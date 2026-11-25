#!/usr/bin/env python3
"""
strip_planner.py — Proof-stripping blueprint & verification planner built on `import_index.py`.

Zero-dependency helper for planning high-confidence Lean proof-stripping PRs:
  1. `bundle-field`: Map all same-file forwarders, downstream readers, destructuring hazards,
     constructor assignment sites, removable imports, exact self-certified orphan deletion list,
     and union reverse-cone compile order for dropping structure fields (#975 / #398 / #96 pattern).
  2. `subtree-replace`: Given a duplicate subtree prefix or module list (and optional canonical
     replacement prefix), map all external boundary importers, cascading orphans outside the subtree,
     cycle checks, and topological compile order (#916 / G2 pattern).
  3. `unused-imports`: Inspect modified `.lean` files (from diff or `--files`) for candidate unused
     imports, flagging instance/notation exports and computing any bonus orphan `peel` cascade.
"""
from __future__ import annotations

import argparse
import collections
import json
import re
import subprocess
import sys
import time
from pathlib import Path
from typing import Any

sys.path.insert(0, str(Path(__file__).resolve().parent))
import big_pr_hunter as bph  # noqa: E402
import import_index as idx  # noqa: E402


def _normalize_prefix(raw: str) -> str:
    s = raw.strip().replace("\\", "/")
    if s.startswith("src/"):
        s = s[4:]
    if s.endswith(".lean"):
        s = s[:-5]
    return s.replace("/", ".").strip(".")


def _rev_cone_set(seeds: set[str], rev: dict[str, set[str]]) -> set[str]:
    cone = set(seeds)
    q = list(seeds)
    while q:
        cur = q.pop()
        for imp in rev.get(cur, ()):
            if imp not in cone:
                cone.add(imp)
                q.append(imp)
    return cone


def _topo_compile_order(
    targets: set[str],
    mods: dict[str, tuple[str, int]],
    fwd: dict[str, set[str]],
) -> list[str]:
    """Return `targets` ordered bottom-up (dependencies before dependents)."""
    in_deg: dict[str, int] = {m: 0 for m in targets if m in mods}
    dependents: dict[str, list[str]] = collections.defaultdict(list)
    for m in in_deg:
        for dep in fwd.get(m, ()):
            if dep in in_deg:
                in_deg[m] += 1
                dependents[dep].append(m)
    ready = sorted(m for m, deg in in_deg.items() if deg == 0)
    q = collections.deque(ready)
    order: list[str] = []
    while q:
        cur = q.popleft()
        order.append(cur)
        for nxt in sorted(dependents.get(cur, ())):
            in_deg[nxt] -= 1
            if in_deg[nxt] == 0:
                q.append(nxt)
    if len(order) < len(in_deg):
        remaining = sorted(set(in_deg) - set(order))
        order.extend(remaining)
    return order


def _collect_clump_header_cleanups(
    raw_by_path: dict[str, str],
    mods: dict[str, tuple[str, int]],
    check_mods: set[str] | list[str],
    stale_mods: set[str],
) -> list[dict[str, Any]]:
    """Find surviving modules whose `-- clump-header:` metadata still imports any module in `stale_mods`."""
    if not stale_mods:
        return []
    out: list[dict[str, Any]] = []
    for hm in sorted(check_mods):
        if hm not in mods:
            continue
        hp = mods[hm][0]
        raw = raw_by_path.get(hp, "")
        for hit in idx.find_clump_header_stale_imports(raw, stale_mods):
            out.append({"mod": hm, "path": hp, **hit})
    return out


def _norm_field_type(ty: str) -> str:
    return " ".join(re.sub(r"\b_root_\.", "", ty).split())


def _field_types_compatible(t1: str, t2: str) -> bool:
    n1, n2 = _norm_field_type(t1), _norm_field_type(t2)
    if not n1 or not n2:
        return False
    if n1 == n2:
        return True
    if " " not in n1 and " " not in n2:
        return n1.endswith("." + n2) or n2.endswith("." + n1)
    return False


def _ere_escape(tok: str) -> str:
    return "".join("\\" + ch if ch in r".^$*+?{}[]\|()" else ch for ch in tok)


def _find_sibling_field_structures(
    repo: Path,
    ref: str,
    mods: dict[str, tuple[str, int]],
    def_mod: str,
    sname: str,
    req_fields: list[str],
    field_map: dict[str, str],
) -> list[dict[str, Any]]:
    """
    Discover other `structure` definitions across the repository that declare any of
    `req_fields` with a compatible field type (e.g. wrapper/adapter structures like
    `Hypotheses''`, `Hypotheses2`, `Hypotheses₂` sharing `p2 : VolGe`).
    """
    if not req_fields:
        return []
    alt = "|".join(_ere_escape(f) for f in req_fields)
    pat = f"^[[:space:]]+({alt})[[:space:]]*:"
    p_grep = subprocess.run(
        ["git", "-c", "core.quotepath=false", "grep", "-l", "-E", pat, ref, "--", "*.lean"],
        cwd=str(repo),
        capture_output=True,
        text=True,
        encoding="utf-8",
        errors="replace",
    )
    if p_grep.returncode not in (0, 1):
        return []
    cand_paths = sorted(
        {
            p
            for p in (bph.parse_git_grep_path(ln, ref) for ln in p_grep.stdout.splitlines())
            if p.endswith(".lean") and idx.path_to_mod(p) in mods
        }
    )
    if not cand_paths:
        return []
    blobs = bph._read_git_blobs(repo, ref, cand_paths)
    req_set = set(req_fields)
    siblings: list[dict[str, Any]] = []
    for cp in cand_paths:
        cm = idx.path_to_mod(cp)
        clean = bph.strip_lean_comments(blobs.get(cp, ""))
        for st in bph.parse_lean_structures(clean):
            if cm == def_mod and st["name"] == sname:
                continue
            matched = []
            for fn, ft in st["fields"]:
                if fn in req_set and _field_types_compatible(field_map[fn], ft):
                    matched.append({"field": fn, "type": ft})
            if matched:
                siblings.append(
                    {
                        "structure": st["name"],
                        "mod": cm,
                        "path": cp,
                        "line": st["start_idx"] + 1,
                        "matched_fields_count": len(matched),
                        "matched_fields": matched,
                    }
                )
    siblings.sort(key=lambda x: (-x["matched_fields_count"], x["path"], x["structure"]))
    return siblings[:20]


def cmd_bundle_field(args: argparse.Namespace) -> int:
    t0 = time.monotonic()
    repo = idx.resolve_repo(args.repo, args.db)
    conn = idx.init_db(args.db)
    mods, fwd, rev = idx.load_graph(conn)

    sname = args.struct.strip()
    if args.module:
        mod = idx.normalize_mod(args.module)
        if mod not in mods:
            print(json.dumps({"error": "MISSING_MODULE", "module": mod}, indent=2), file=sys.stderr)
            return 2
    else:
        p_grep = subprocess.run(
            ["git", "-c", "core.quotepath=false", "grep", "-l", "-F", f"structure {sname}", args.ref, "--", "src/"],
            cwd=str(repo),
            capture_output=True,
            text=True,
            encoding="utf-8",
            errors="replace",
        )
        cand_hits = [
            idx.path_to_mod(p)
            for p in (bph.parse_git_grep_path(ln, args.ref) for ln in p_grep.stdout.splitlines())
            if p.endswith(".lean")
        ]
        cand_hits = [h for h in cand_hits if h in mods]
        cand_blobs = bph._read_git_blobs(repo, args.ref, [mods[h][0] for h in cand_hits])
        hits = [
            h
            for h in cand_hits
            if any(s["name"] == sname for s in bph.parse_lean_structures(bph.strip_lean_comments(cand_blobs.get(mods[h][0], ""))))
        ]
        if len(hits) != 1:
            print(
                json.dumps(
                    {
                        "error": "AMBIGUOUS_OR_MISSING_STRUCT",
                        "structure": sname,
                        "matching_modules": hits[:20],
                        "hint": "Pass --module explicitly to disambiguate.",
                    },
                    indent=2,
                ),
                file=sys.stderr,
            )
            return 2
        mod = hits[0]

    def_path = mods[mod][0]
    rc = _rev_cone_set({mod}, rev)
    rc_paths = sorted({mods[rm][0] for rm in rc if rm in mods})
    rc_raw = bph._read_git_blobs(repo, args.ref, rc_paths)
    rc_clean = {p: bph.strip_lean_comments(txt) for p, txt in rc_raw.items()}

    structs = [s for s in bph.parse_lean_structures(rc_clean.get(def_path, "")) if s["name"] == sname]
    if not structs:
        print(json.dumps({"error": "STRUCTURE_NOT_FOUND", "structure": sname, "module": mod}, indent=2), file=sys.stderr)
        return 2
    st = structs[0]
    field_map = dict(st["fields"])

    req_fields = [f.strip() for f in args.fields.split(",") if f.strip()]
    missing_fields = [f for f in req_fields if f not in field_map]
    if missing_fields:
        print(
            json.dumps(
                {
                    "error": "MISSING_FIELDS",
                    "structure": sname,
                    "missing_fields": missing_fields,
                    "available_fields": [f for f, _ in st["fields"]],
                },
                indent=2,
            ),
            file=sys.stderr,
        )
        return 2

    def_lines = rc_clean.get(def_path, "").splitlines()
    masked_def_lines = [("" if st["start_idx"] <= i < st["end_idx"] else ln) for i, ln in enumerate(def_lines)]

    destr_warnings: list[str] = []
    destr_details: list[dict[str, Any]] = []
    for rmod in sorted(rc):
        rp = mods[rmod][0]
        txt = rc_clean.get(rp, "")
        skip_rng = (st["start_idx"], st["end_idx"]) if rp == def_path else None
        hits = bph.find_struct_destructuring_hits(txt, sname, skip_range=skip_rng)
        if hits:
            destr_warnings.append(rmod)
            for h in hits:
                if len(destr_details) < 15:
                    destr_details.append({"mod": rmod, **h})

    # Collect exclusive direct dependencies of rc modules for constructor peel resolution
    excl_deps_by_host: dict[str, list[str]] = collections.defaultdict(list)
    excl_dep_paths: list[str] = []
    for cmod in rc:
        for dep in fwd.get(cmod, ()):
            if dep != mod and len(rev.get(dep, ())) == 1 and dep in mods:
                excl_deps_by_host[cmod].append(dep)
                excl_dep_paths.append(mods[dep][0])
    excl_dep_blobs = bph._read_git_blobs(repo, args.ref, excl_dep_paths)
    dep_blobs_cache: dict[str, str] = dict(excl_dep_blobs)
    dep_export_shorts: dict[str, set[str]] = {}
    for dp, dtxt in excl_dep_blobs.items():
        if dtxt:
            decls, _ = idx.extract_exported_decls(bph.strip_lean_comments(dtxt))
            dep_export_shorts[dp] = {d["short_name"] for d in decls if len(d["short_name"]) >= 6}

    fields_analysis: list[dict[str, Any]] = []
    all_cuts: list[tuple[str, str]] = []
    seen_cuts: set[tuple[str, str]] = set()
    edited_mods: set[str] = {mod}
    host_decls_cache: dict[str, list[dict[str, Any]]] = {}
    dropped_assign_lines_by_edge: dict[tuple[str, str], set[int]] = collections.defaultdict(set)
    dropped_rhs_by_edge: dict[tuple[str, str], list[str]] = collections.defaultdict(list)

    for fname in req_fields:
        ftype = field_map[fname]
        proj_re = re.compile(rf"(?:\.{re.escape(fname)}{idx.LEAN_ID_END}|{re.escape(sname)}\.{re.escape(fname)}{idx.LEAN_ID_END})")
        assign_re = re.compile(rf"^(?![ \t]*(?:have|let|obtain|show|suffices)\b)[^\n]*(?:^|[\s{{,])[ \t]*{re.escape(fname)}[ \t]*:=[ \t]*\(?[ \t]*({idx.LEAN_QUAL_IDENT})")

        reader_sites: list[dict[str, Any]] = []
        ctor_sites: list[dict[str, Any]] = []
        t_tokens = re.findall(r"[A-Za-z_][A-Za-z0-9_'₀₁₂₃₄₅₆₇₈₉]{4,}", ftype)
        short_type = t_tokens[-1] if t_tokens else ""

        for rmod in sorted(rc):
            rp = mods[rmod][0]
            txt_full = rc_clean.get(rp, "")
            lines = masked_def_lines if rp == def_path else txt_full.splitlines()
            hit_idxs = [idx_ln for idx_ln, ln in enumerate(lines) if proj_re.search(ln)]
            if hit_idxs:
                edited_mods.add(rmod)
                site: dict[str, Any] = {
                    "mod": rmod,
                    "lines": [i + 1 for i in hit_idxs[:10]],
                    "sample": lines[hit_idxs[0]].strip()[:120],
                }
                if rp == def_path:
                    site["same_file_decls"] = bph._find_enclosing_decls(def_lines, hit_idxs)
                reader_sites.append(site)

            if not (sname in txt_full or mod in txt_full or mod in fwd.get(rmod, ())):
                continue
            for idx_ln, ln in enumerate(lines):
                ma = assign_re.search(ln)
                if ma:
                    edited_mods.add(rmod)
                    rhs = ma.group(1)
                    rhs_short = rhs.rsplit(".", 1)[-1]
                    ctor_sites.append(
                        {
                            "mod": rmod,
                            "line": idx_ln + 1,
                            "rhs": rhs,
                            "snippet": ln.strip()[:120],
                        }
                    )
                    w_tokens: set[str] = set()
                    if rmod not in host_decls_cache:
                        host_decls_cache[rmod] = bph._extract_top_decls(txt_full)
                    w_decl = bph._match_local_wrapper(rhs, host_decls_cache[rmod])
                    if w_decl:
                        w_tokens = {
                            tok
                            for tok in re.findall(r"[A-Za-z_][A-Za-z0-9_'₀₁₂₃₄₅₆₇₈₉]{5,}", w_decl["body"])
                            if tok not in {"GlobalTheory", "UpperTheory", "PositivityTheory", "CompanionTheory", "ReciprocityTheory", "Published"}
                        }
                    for dep in excl_deps_by_host.get(rmod, ()):
                        dp = mods[dep][0]
                        dblob = excl_dep_blobs.get(dp, "")
                        exp_shorts = dep_export_shorts.get(dp, set())
                        if (
                            (short_type and (short_type in dblob or short_type.lower() in dep.lower()))
                            or (len(rhs_short) >= 5 and rhs_short in dblob)
                            or bool(w_tokens & exp_shorts)
                        ):
                            edge = (rmod, dep)
                            dropped_assign_lines_by_edge[edge].add(idx_ln)
                            dropped_rhs_by_edge[edge].append(rhs)
                            if edge not in seen_cuts:
                                seen_cuts.add(edge)
                                all_cuts.append(edge)

        fields_analysis.append(
            {
                "field": fname,
                "type": ftype,
                "reader_sites_count": len(reader_sites),
                "reader_sites": reader_sites[:20],
                "constructor_sites_count": len(ctor_sites),
                "constructor_sites": ctor_sites[:20],
            }
        )

    safe_cuts: list[tuple[str, str]] = []
    blocked_cuts: list[dict[str, Any]] = []
    required_wrapper_removals: list[dict[str, Any]] = []
    seen_wrappers: set[tuple[str, str]] = set()
    if args.check_symbols and all_cuts:
        for h, d in all_cuts:
            edge = (h, d)
            guard = bph.check_bundle_cut_safety(
                h,
                d,
                dropped_assign_lines_by_edge.get(edge, set()),
                dropped_rhs_by_edge.get(edge, []),
                mods,
                fwd,
                rev,
                rc_clean,
                repo,
                args.ref,
                dep_blobs_cache,
                host_decls_cache=host_decls_cache,
            )
            if guard["safe"]:
                safe_cuts.append((h, d))
                for witem in guard.get("masked_unused_wrappers", []):
                    wkey = (witem["host"], witem["wrapper"])
                    if wkey not in seen_wrappers:
                        seen_wrappers.add(wkey)
                        required_wrapper_removals.append(witem)
            else:
                blocked_cuts.append(
                    {
                        "host": h,
                        "dep": d,
                        "avoided_false_peel_files": guard["peel_files"],
                        "avoided_false_peel_lines": guard["peel_lines"],
                        "wrapper_reuse_blockers": guard["wrapper_reuse_blockers"],
                        "secondary_symbol_blockers": guard["secondary_symbol_blockers"],
                        "has_instances_or_notations": guard["has_instances_or_notations"],
                    }
                )
    else:
        safe_cuts = list(all_cuts)

    peel_res = idx.compute_multi_peel(mods, fwd, rev, safe_cuts, mode="zero-indegree") if safe_cuts else {
        "dead": set(),
        "survivor_dangling": [],
        "non_main_blocker_mods": [],
    }
    dead: set[str] = peel_res["dead"]
    dead_lines = sum(mods[m][1] for m in dead)
    surviving_compile = _topo_compile_order(_rev_cone_set(edited_mods, rev) - dead, mods, fwd)
    stale_mods = set(dead) | {d for _, d in safe_cuts}
    clump_cleanups = _collect_clump_header_cleanups(
        rc_raw,
        mods,
        ({h for h, _ in safe_cuts} | edited_mods) - dead,
        stale_mods,
    )
    sibling_structs = _find_sibling_field_structures(repo, args.ref, mods, mod, sname, req_fields, field_map)

    if args.emit_delete_list:
        args.emit_delete_list.write_text("\n".join(mods[m][0] for m in sorted(dead)) + ("\n" if dead else ""), encoding="utf-8")

    out: dict[str, Any] = {
        "indexed_commit": idx.get_meta(conn, "commit")[:10],
        "ref": args.ref,
        "elapsed_s": round(time.monotonic() - t0, 2),
        "structure": sname,
        "defining_module": mod,
        "defining_path": def_path,
        "rev_cone_size": len(rc),
        "destructuring_warning_count": len(destr_warnings),
        "destructuring_warning_modules": destr_warnings[:10],
        "destructuring_warning_details": destr_details,
        "sibling_field_structures_count": len(sibling_structs),
        "sibling_field_structures": sibling_structs,
        "fields_analysis": fields_analysis,
        "candidate_import_cuts": [[h, d] for h, d in safe_cuts],
        "required_host_wrapper_removals": required_wrapper_removals,
        "clump_header_cleanups": clump_cleanups,
        "precondition_note": (
            "candidate_import_cuts and orphan_files assume all fields_analysis edits "
            "(removing listed fields, downstream forwarders/readers, constructor assignments, "
            "required_host_wrapper_removals, import lines, and any clump_header_cleanups) are "
            "applied first; bare `import_index.py peel --check-symbols` blocks raw import drops "
            "without those host edits."
        ),
        "blocked_import_cuts_count": len(blocked_cuts),
        "blocked_import_cuts": blocked_cuts,
        "blocked_false_peel_lines_avoided": sum(b["avoided_false_peel_lines"] for b in blocked_cuts),
        "orphan_module_count": len(dead),
        "orphan_total_lines": dead_lines,
        "survivor_dangling_edges": len(peel_res["survivor_dangling"]),
        "orphan_files": [mods[m][0] for m in sorted(dead)],
        "compile_order_count": len(surviving_compile),
        "compile_order": surviving_compile[:200],
    }
    if args.emit_delete_list:
        out["written_delete_list"] = str(args.emit_delete_list)
    print(json.dumps(out, indent=2))
    return 2 if peel_res["survivor_dangling"] else 0


def cmd_subtree_replace(args: argparse.Namespace) -> int:
    t0 = time.monotonic()
    repo = idx.resolve_repo(args.repo, args.db)
    conn = idx.init_db(args.db)
    mods, fwd, rev = idx.load_graph(conn)

    target_mods: set[str] = set()
    if args.drop_prefix:
        pref = _normalize_prefix(args.drop_prefix)
        for m in mods:
            if m == pref or m.startswith(pref + "."):
                target_mods.add(m)
    if args.drop_mods:
        for raw_m in args.drop_mods.split(","):
            if raw_m.strip():
                nm = idx.normalize_mod(raw_m)
                if nm in mods:
                    target_mods.add(nm)
    if args.exclude_mods:
        for raw_m in args.exclude_mods.split(","):
            if raw_m.strip():
                target_mods.discard(idx.normalize_mod(raw_m))

    if not target_mods:
        print(json.dumps({"error": "NO_TARGET_MODULES", "drop_prefix": args.drop_prefix, "drop_mods": args.drop_mods}, indent=2), file=sys.stderr)
        return 2

    boundary_map: dict[str, list[str]] = collections.defaultdict(list)
    all_cuts: list[tuple[str, str]] = []
    for tm in sorted(target_mods):
        for imp in sorted(rev.get(tm, ())):
            if imp not in target_mods:
                boundary_map[imp].append(tm)
                all_cuts.append((imp, tm))

    ext_importers = sorted(boundary_map)
    ext_blobs = bph._read_git_blobs(repo, args.ref, [mods[e][0] for e in ext_importers])
    target_stems = {tm.rsplit(".", 1)[-1] for tm in target_mods}
    boundary_details = []
    for e in ext_importers:
        ep = mods[e][0]
        elines = ext_blobs.get(ep, "").splitlines()
        imp_t = sorted(boundary_map[e])
        t_stem_re = re.compile(r"\b(" + "|".join(re.escape(s) for s in sorted({x.rsplit(".", 1)[-1] for x in imp_t} | target_stems, key=len, reverse=True)) + r")\b")
        ref_lines = [i + 1 for i, ln in enumerate(elines) if not ln.strip().startswith("import ") and t_stem_re.search(ln)]
        boundary_details.append(
            {
                "importer_mod": e,
                "path": ep,
                "imported_target_mods": imp_t,
                "reference_lines_count": len(ref_lines),
                "sample_reference_lines": ref_lines[:15],
            }
        )

    peel_res = idx.compute_multi_peel(mods, fwd, rev, all_cuts, drop_mods=target_mods, mode="zero-indegree")
    dead: set[str] = peel_res["dead"]
    cascading_outside = sorted(dead - target_mods)

    canonical_cycles: list[dict[str, str]] = []
    canonical_mods: set[str] = set()
    if args.canonical_prefix:
        cpref = _normalize_prefix(args.canonical_prefix)
        canonical_mods = {m for m in mods if m == cpref or m.startswith(cpref + ".")}
        # Adding edge e -> c creates a cycle iff e is reachable from c in fwd (outside target_mods)
        c_reach = idx.reachable_from(canonical_mods, mods, fwd, set(all_cuts))
        for e in ext_importers:
            if e in c_reach:
                canonical_cycles.append({"importer": e, "canonical_prefix": cpref})

    compile_seeds = set(ext_importers)
    surviving_compile = _topo_compile_order(_rev_cone_set(compile_seeds, rev) - dead, mods, fwd)
    clump_cleanups = _collect_clump_header_cleanups(ext_blobs, mods, set(ext_importers) - dead, dead | target_mods)

    if args.emit_delete_list:
        args.emit_delete_list.write_text("\n".join(mods[m][0] for m in sorted(dead)) + ("\n" if dead else ""), encoding="utf-8")

    out: dict[str, Any] = {
        "indexed_commit": idx.get_meta(conn, "commit")[:10],
        "ref": args.ref,
        "elapsed_s": round(time.monotonic() - t0, 2),
        "target_subtree_files": len(target_mods),
        "target_subtree_lines": sum(mods[m][1] for m in target_mods),
        "external_boundary_importers_count": len(ext_importers),
        "external_boundary_importers": boundary_details,
        "total_orphan_files": len(dead),
        "total_orphan_lines": sum(mods[m][1] for m in dead),
        "cascading_outside_files_count": len(cascading_outside),
        "cascading_outside_files": [mods[m][0] for m in cascading_outside[:40]],
        "survivor_dangling_edges": len(peel_res["survivor_dangling"]),
        "clump_header_cleanups": clump_cleanups,
        "canonical_cycle_risks": canonical_cycles,
        "compile_order_count": len(surviving_compile),
        "compile_order": surviving_compile[:200],
    }
    if args.emit_delete_list:
        out["written_delete_list"] = str(args.emit_delete_list)
    print(json.dumps(out, indent=2))
    return 2 if peel_res["survivor_dangling"] else 0


def _extract_exported_symbols_and_attrs(clean_txt: str) -> tuple[set[str], set[str], bool]:
    """Return (decl_short_names, namespaces, has_instances_or_notations)."""
    decls, has_implicit = idx.extract_exported_decls(clean_txt)
    names = {d["short_name"] for d in decls}
    namespaces: set[str] = set()
    ns_re = idx._NS_DECL_RE
    for ln in clean_txt.splitlines():
        mn = ns_re.match(ln)
        if mn:
            ns = mn.group(1)
            namespaces.add(ns)
            namespaces.add(ns.rsplit(".", 1)[-1])
    return names, namespaces, has_implicit


def cmd_unused_imports(args: argparse.Namespace) -> int:
    t0 = time.monotonic()
    repo = idx.resolve_repo(args.repo, args.db)
    conn = idx.init_db(args.db)
    mods, fwd, rev = idx.load_graph(conn)

    ref = args.head if args.base else args.ref
    target_paths: list[str] = []
    if args.files:
        for f in args.files.split(","):
            if f.strip():
                nm = idx.normalize_mod(f)
                target_paths.append(mods[nm][0] if nm in mods else idx.mod_to_path(nm))
    elif args.base:
        base_sha = idx.git_run(repo, ["rev-parse", args.base]).strip()
        head_sha = idx.git_run(repo, ["rev-parse", args.head]).strip()
        ns_lines = idx.git_run(repo, ["diff", "--name-status", f"{base_sha}...{head_sha}"]).splitlines()
        for ln in ns_lines:
            parts = ln.split("\t")
            if parts[0] in ("M", "A") and parts[1].endswith(".lean"):
                target_paths.append(parts[1])
            elif parts[0].startswith("R") and parts[2].endswith(".lean"):
                target_paths.append(parts[2])
    else:
        print(json.dumps({"error": "MISSING_TARGET_FILES", "hint": "Pass --files or --base <ref>"}, indent=2), file=sys.stderr)
        return 2

    target_paths = sorted(set(target_paths))
    host_blobs = bph._read_git_blobs(repo, ref, target_paths)

    # Parse imports from live ref blobs and collect all imported project modules
    host_imports: dict[str, list[str]] = {}
    all_imp_paths: set[str] = set()
    for p in target_paths:
        raw = host_blobs.get(p, "")
        _, imps = idx.parse_lean_imports(raw.encode("utf-8"))
        proj_imps = [d for d, _ in imps if d in mods]
        host_imports[p] = proj_imps
        for d in proj_imps:
            all_imp_paths.add(mods[d][0])

    imp_blobs = bph._read_git_blobs(repo, ref, sorted(all_imp_paths))
    imp_meta = {
        idx.path_to_mod(p): _extract_exported_symbols_and_attrs(bph.strip_lean_comments(txt))
        for p, txt in imp_blobs.items()
    }

    report = []
    for p in target_paths:
        hmod = idx.path_to_mod(p)
        clean_body_lines = []
        past_header = False
        for ln in bph.strip_lean_comments(host_blobs.get(p, "")).splitlines():
            s = ln.strip()
            if not past_header:
                if not s or s == "module" or s.startswith("prelude") or idx.IMPORT_RE.match(s):
                    continue
                past_header = True
            clean_body_lines.append(ln)
        body_text = "\n".join(clean_body_lines)
        body_tokens = set(idx._LEAN_IDENT_RE.findall(body_text))

        candidates = []
        for dep in host_imports.get(p, []):
            names, namespaces, has_implicit = imp_meta.get(dep, (set(), set(), False))
            dep_stem = dep.rsplit(".", 1)[-1]
            sym_hits = sorted((names | namespaces | {dep_stem}) & body_tokens)
            peel_files, peel_lines = bph.compute_exclusive_peel(hmod, dep, mods, fwd, rev)
            if not sym_hits:
                candidates.append(
                    {
                        "imported_mod": dep,
                        "status": "needs_instance_or_macro_check" if has_implicit else "likely_unused",
                        "has_instances_or_notations": has_implicit,
                        "bonus_peel_files": peel_files,
                        "bonus_peel_lines": peel_lines,
                    }
                )
        report.append(
            {
                "mod": hmod,
                "path": p,
                "total_project_imports": len(host_imports.get(p, [])),
                "candidate_unused_imports": candidates,
            }
        )

    print(
        json.dumps(
            {
                "indexed_commit": idx.get_meta(conn, "commit")[:10],
                "ref": ref,
                "elapsed_s": round(time.monotonic() - t0, 2),
                "files": report,
            },
            indent=2,
        )
    )
    return 0


def main() -> int:
    idx.ensure_utf8_stdio()
    ap = argparse.ArgumentParser(description="Proof-stripping blueprint & verification planner.")
    ap.add_argument("--repo", type=Path, default=None, help="Path to local riemann-hypothesis git checkout")
    ap.add_argument("--db", type=Path, default=Path.home() / ".cache" / "rh-import-index" / "import_index.db")
    ap.add_argument("--ref", default="origin/main")
    sub = ap.add_subparsers(dest="cmd", required=True)

    p_bf = sub.add_parser("bundle-field", help="Plan dropping fields from a bundle structure")
    p_bf.add_argument("--struct", required=True, help="Structure name (e.g. PublishedHodgeBundleTheorems)")
    p_bf.add_argument("--module", default="", help="Optional defining module (auto-located if omitted)")
    p_bf.add_argument("--fields", required=True, help="Comma-separated field names to drop")
    p_bf.add_argument("--check-symbols", action=argparse.BooleanOptionalAction, default=True, help="Verify host wrapper-reuse & secondary-symbol safety before counting peels")
    p_bf.add_argument("--emit-delete-list", type=Path, help="Optional output file for orphan file paths")

    p_sr = sub.add_parser("subtree-replace", help="Plan replacing a duplicate module subtree")
    p_sr.add_argument("--drop-prefix", default="", help="Module/path prefix of duplicate subtree to remove")
    p_sr.add_argument("--drop-mods", default="", help="Comma-separated additional target modules to drop")
    p_sr.add_argument("--exclude-mods", default="", help="Comma-separated modules to keep out of target drop set")
    p_sr.add_argument("--canonical-prefix", default="", help="Optional canonical replacement prefix for cycle check")
    p_sr.add_argument("--emit-delete-list", type=Path, help="Optional output file for all orphan file paths")

    p_ui = sub.add_parser("unused-imports", help="Detect candidate unused imports and bonus orphan peels")
    p_ui.add_argument("--base", default="", help="Base ref for git diff mode")
    p_ui.add_argument("--head", default="HEAD", help="Head ref for git diff mode")
    p_ui.add_argument("--files", default="", help="Comma-separated file paths or module names")

    args = ap.parse_args()
    return {
        "bundle-field": cmd_bundle_field,
        "subtree-replace": cmd_subtree_replace,
        "unused-imports": cmd_unused_imports,
    }[args.cmd](args)


if __name__ == "__main__":
    raise SystemExit(main())
