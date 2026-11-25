#!/usr/bin/env python3
"""
big_pr_hunter.py — Fast SQLite-backed Big-PR opportunity scanner for continuous local search.

Reads the local `import_index.db` built by `import_index.py` to discover high-ROI
structural/mathematical Big-PR candidates across 11 axes:
  1. `chokepoints`: Modules whose removal/delegation unlocks the largest exclusive subtrees.
  2. `published-dups`: Multiply-proved `GlobalTheory.Published.*` (or custom regex) theorems,
     filtered to top-level declarations and distinguishing real proofs from forwarder wrappers.
  3. `neg-instances`: Files using `attribute [-instance]` (#599 architectural root-cause scan).
  4. `duplicate-stems`: Pure SQLite (<1.5s) twin-directory & duplicate-module-basename radar.
  5. `heavy-pillars`: >=10kL exclusive single-edge proof pillars feeding Main-close hosts.
  6. `unused-fields`: Scan Main-reaching bundle `structure`s (incl. multi-line headers,
     parameterized fields, same-file forwarders, comment stripping, destructuring & cut guards).
  7. `dom-pillars`: Exact Cooper-Harvey-Kennedy Dominator-Tree scanner over Main-reachable nodes
     that surfaces hidden multi-edge / diamond proof pillars missed by single-edge `heavy-pillars`.
  8. `decl-dups`: Declaration-level alpha-normalized signature & proof-body fingerprint dedup
     (catches post-clump and cross-filename duplicates).
  9. `ignored-bundle-args`: Flag 1-to-N-reader bundle fields & direct `Published` parameters
     whose consumers immediately discard them via `fun _ ... =>`, `by intro _`, or unused binders.
 10. `vacuous-defs`: Fast whole-repo syntactic scan (#466) for trivial `Prop` defs (`:= True` /
     `fun _ => True` / `trivial`), vacuous `Prop` structures, 0-field placeholder structures,
     unused callers, and params instantiated only with trivial seeds.
 11. `unreferenced-decls`: Fast whole-project syntactic scanner (#466) for declarations and
     non-instance modules with 0 external or same-file references.

Zero third-party dependencies (Python 3.9+ stdlib + sqlite3 + git).
"""
from __future__ import annotations

import argparse
import collections
import hashlib
import itertools
import json
import re
import subprocess
import sys
import time
from pathlib import Path
from typing import Any

sys.path.insert(0, str(Path(__file__).resolve().parent))
import import_index as idx  # noqa: E402

DEFAULT_STRUCT_FILTER = "Hypotheses,Inputs,Literature,Published,Context,Statement,Bundle,Theorems,Data,Params"

_LS_TREE_CACHE: dict[tuple[str, str], dict[str, str]] = {}

GENERIC_STEMS = {
    "Imports",
    "Basic",
    "Defs",
    "Definitions",
    "Lemmas",
    "Lemma",
    "Helper",
    "Helpers",
    "Statement",
    "Statements",
    "Main",
    "Core",
    "Aux",
    "Utils",
    "Common",
    "Types",
    "Setup",
    "Prelude",
    "All",
    "Index",
    "Proof",
    "Proofs",
    "Bridge",
    "API",
    "Interface",
    "Data",
    "Spec",
}


def compute_exclusive_peel(
    host: str,
    dropped_imp: str,
    mods: dict[str, tuple[str, int]],
    fwd: dict[str, set[str]],
    rev: dict[str, set[str]],
) -> tuple[int, int]:
    """Return (orphan_count, orphan_lines) if edge host -> dropped_imp is removed."""
    if len(rev.get(dropped_imp, ())) != 1 or host not in rev.get(dropped_imp, ()):
        return 0, 0
    dead: set[str] = set()
    q = [dropped_imp]
    dec: dict[str, int] = {dropped_imp: 1}
    while q:
        m = q.pop()
        if m in dead or m not in mods:
            continue
        if len(rev.get(m, ())) - dec.get(m, 0) <= 0:
            dead.add(m)
            for dep in fwd.get(m, ()):
                dec[dep] = dec.get(dep, 0) + 1
                if len(rev.get(dep, ())) - dec[dep] <= 0 and dep in mods and dep not in dead:
                    q.append(dep)
    return len(dead), sum(mods[m][1] for m in dead)


def compute_rev_cone_capped(mod: str, rev: dict[str, set[str]], cap: int = 500) -> int:
    cone = {mod}
    q = [mod]
    while q and len(cone) <= cap:
        cur = q.pop()
        for p in rev.get(cur, ()):
            if p not in cone:
                cone.add(p)
                q.append(p)
    return len(cone)


strip_lean_comments = idx.strip_lean_comments


def parse_git_grep_path(ln: str, ref: str) -> str:
    prefix = f"{ref}:"
    rest = ln[len(prefix) :] if ln.startswith(prefix) else ln
    return rest.strip()


def parse_git_grep_line(ln: str, ref: str) -> tuple[str, int, str] | None:
    prefix = f"{ref}:"
    rest = ln[len(prefix) :] if ln.startswith(prefix) else ln
    m_loc = re.match(r"^([^:]+):(\d+):(.*)$", rest)
    if not m_loc:
        return None
    return m_loc.group(1), int(m_loc.group(2)), m_loc.group(3)


def cmd_chokepoints(args: argparse.Namespace) -> int:
    t0 = time.monotonic()
    conn = idx.init_db(args.db)
    mods, fwd, rev = idx.load_graph(conn)

    results: list[tuple[int, int, str, str, int]] = []
    for mod, importers in rev.items():
        if len(importers) != 1 or mod not in mods:
            continue
        host = next(iter(importers))
        cnt, lines = compute_exclusive_peel(host, mod, mods, fwd, rev)
        if lines >= args.min_lines and cnt >= args.min_files:
            cone_sz = compute_rev_cone_capped(host, rev, cap=500)
            if args.max_cone > 0 and cone_sz > args.max_cone:
                continue
            results.append((lines, cnt, host, mod, cone_sz))

    results.sort(reverse=True)
    seen_hosts: set[str] = set()
    top = []
    for lines, cnt, host, seed, cone_sz in results:
        if host in seen_hosts:
            continue
        seen_hosts.add(host)
        top.append(
            {
                "orphan_lines": lines,
                "orphan_files": cnt,
                "host_mod": host,
                "exclusive_seed": seed,
                "host_rev_cone": cone_sz if cone_sz <= 500 else ">500",
            }
        )
        if len(top) >= args.limit:
            break

    print(
        json.dumps(
            {
                "indexed_commit": idx.get_meta(conn, "commit")[:10],
                "elapsed_s": round(time.monotonic() - t0, 2),
                "candidates": top,
            },
            indent=2,
        )
    )
    return 0


def _extract_attr_names(lines: list[str], decl_line_idx: int) -> list[str]:
    attrs: list[str] = []
    attr_chunks = re.findall(r"@\[([^\]]+)\]", lines[decl_line_idx])
    seen_nonblank = 0
    k = decl_line_idx - 1
    while k >= 0 and seen_nonblank < 3:
        st = lines[k].strip()
        if not st:
            k -= 1
            continue
        seen_nonblank += 1
        if st.startswith("@["):
            attr_chunks.extend(re.findall(r"@\[([^\]]+)\]", st))
            k -= 1
        else:
            break
    for ch in attr_chunks:
        for item in ch.split(","):
            head = item.strip().lstrip("-").split(None, 1)[0] if item.strip() else ""
            if head:
                attrs.append(head)
    return attrs


def _extract_top_decls(clean_text: str) -> list[dict[str, Any]]:
    """
    Extract top-level (indent <= 2) theorem/lemma/def/abbrev/instance declarations
    with bracket-depth-aware signature split and body lines from comment-stripped Lean text.
    """
    decl_start_re = re.compile(
        rf"^(\s{{0,2}})(?:@\[[^\]]*\]\s*)*"
        rf"((?:(?:public|private|protected|noncomputable|unsafe|partial|scoped|local|meta)\s+)*)"
        rf"(theorem|lemma|def|abbrev|instance)\s+({idx.LEAN_QUAL_IDENT}){idx.LEAN_ID_END}(.*)$"
    )
    boundary_re = re.compile(
        r"^\s{0,2}(?:@\[[^\]]*\]\s*)*(?:(?:public|private|protected|noncomputable|unsafe|partial|scoped|local|meta)\s+)*"
        r"(?:theorem|lemma|def|abbrev|instance|structure|inductive|class|opaque|axiom|alias|section|end|namespace|variable|open|set_option|attribute)\b"
    )
    lines = clean_text.splitlines()
    n = len(lines)
    decls: list[dict[str, Any]] = []
    i = 0
    while i < n:
        m = decl_start_re.match(lines[i])
        if not m:
            i += 1
            continue
        mods_kw = m.group(2)
        kind = m.group(3)
        name = m.group(4)
        start_line = i + 1
        is_private = bool(re.search(r"\bprivate\b", mods_kw))
        attrs = _extract_attr_names(lines, i)
        # Collect declaration lines up to next top-level boundary
        j = i + 1
        while j < n:
            ln = lines[j]
            if ln.strip() and boundary_re.match(ln):
                break
            j += 1
        chunk = "\n".join(lines[i:j])
        # Scan `chunk` tracking ()[]{} depth to find top-level `:=` or `where` separating signature from body
        depth = 0
        split_pos = -1
        split_tok_len = 0
        clen = len(chunk)
        # Skip past the declaration keyword + name
        hdr_off = m.start(4) - m.start(0) + len(name)
        k = hdr_off
        while k < clen:
            ch = chunk[k]
            if ch in "([{":
                depth += 1
            elif ch in ")]}":
                if depth > 0:
                    depth -= 1
            elif depth == 0:
                if chunk[k : k + 2] == ":=":
                    split_pos = k
                    split_tok_len = 2
                    break
                if chunk[k : k + 5] == "where" and (k == 0 or chunk[k - 1].isspace()) and (k + 5 == clen or chunk[k + 5].isspace()):
                    split_pos = k
                    split_tok_len = 5
                    break
            k += 1

        if split_pos == -1:
            i = j
            continue

        sig_raw = chunk[hdr_off:split_pos]
        body_raw = chunk[split_pos + split_tok_len :]

        # Find the top-level `:` separating parameters from return type (last `:` at depth 0)
        depth = 0
        colon_pos = -1
        for pos, ch in enumerate(sig_raw):
            if ch in "([{":
                depth += 1
            elif ch in ")]}":
                if depth > 0:
                    depth -= 1
            elif ch == ":" and depth == 0:
                colon_pos = pos

        if colon_pos != -1:
            params_part = sig_raw[:colon_pos].strip()
            ret_part = sig_raw[colon_pos + 1 :].strip()
        else:
            params_part = ""
            ret_part = ""

        decls.append(
            {
                "kind": kind,
                "name": name,
                "line": start_line,
                "start_idx": i,
                "end_idx": j,
                "is_private": is_private,
                "attrs": attrs,
                "params": params_part,
                "ret": ret_part,
                "body": body_raw,
                "sig_raw": sig_raw.strip(),
            }
        )
        i = j
    return decls


def cmd_published_dups(args: argparse.Namespace) -> int:
    """Find top-level theorems/defs proving the same `GlobalTheory.Published.<X>` (or custom regex) type in multiple modules."""
    t0 = time.monotonic()
    repo = idx.resolve_repo(args.repo, args.db)
    ref = args.ref
    pat = args.pattern
    p = subprocess.run(
        ["git", "-c", "core.quotepath=false", "grep", "-l", "-E", pat, ref, "--", "src/"],
        cwd=str(repo),
        capture_output=True,
        text=True,
        encoding="utf-8",
        errors="replace",
    )
    cand_paths = [p for p in (parse_git_grep_path(ln, ref) for ln in p.stdout.splitlines()) if p.endswith(".lean")]
    blobs = _read_git_blobs(repo, ref, cand_paths)

    ret_type_re = re.compile(rf"^(?:_root_\.)?({pat}[A-Za-z0-9_.'₀₁₂₃₄₅₆₇₈₉]+)\s*$")
    by_type: dict[str, list[dict[str, Any]]] = collections.defaultdict(list)
    for path in cand_paths:
        txt = blobs.get(path, "")
        if not txt:
            continue
        clean = strip_lean_comments(txt)
        for d in _extract_top_decls(clean):
            ret = " ".join(d["ret"].split())
            if not ret or "→" in ret or "->" in ret:
                continue
            mr = ret_type_re.match(ret)
            if not mr:
                continue
            tname = mr.group(1)
            body_stripped = " ".join(d["body"].split())
            body_lines = [ln for ln in d["body"].splitlines() if ln.strip()]
            is_proj_body = bool(re.match(r"^(?:by\s+(?:exact|apply)\s+)?[A-Za-z_][A-Za-z0-9_']*\.[A-Za-z0-9_.'₀₁₂₃₄₅₆₇₈₉]+$", body_stripped))
            if tname in d["params"] or (d["params"] and is_proj_body):
                role = "hypothesis_forwarder"
            elif len(body_lines) <= 1 and not body_stripped.startswith("by "):
                role = "short_alias"
            else:
                role = "proof"
            by_type[tname].append(
                {
                    "path": path,
                    "line": d["line"],
                    "role": role,
                    "decl": f"{d['kind']} {d['name']} : {ret}"[:120],
                }
            )

    conn = idx.init_db(args.db)
    mods, fwd, rev = idx.load_graph(conn)

    dups = []
    for tname, locs in by_type.items():
        if not args.include_wrappers:
            filtered_locs = [x for x in locs if x["role"] != "hypothesis_forwarder"]
        else:
            filtered_locs = locs
        unique_paths = {x["path"] for x in filtered_locs}
        if len(unique_paths) < 2:
            continue
        proof_count = len({x["path"] for x in filtered_locs if x["role"] == "proof"})
        wrapper_count = sum(1 for x in locs if x["role"] == "hypothesis_forwarder")
        if not args.include_wrappers and proof_count == 0:
            continue
        # Keep first hit per path
        seen_p: set[str] = set()
        enriched = []
        max_peel_lines = 0
        for x in filtered_locs:
            if x["path"] in seen_p:
                continue
            seen_p.add(x["path"])
            mod = idx.path_to_mod(x["path"])
            importers = rev.get(mod, set())
            peel_cnt, peel_lines = 0, 0
            if len(importers) == 1:
                host = next(iter(importers))
                peel_cnt, peel_lines = compute_exclusive_peel(host, mod, mods, fwd, rev)
            mlines = mods[mod][1] if mod in mods else 0
            max_peel_lines = max(max_peel_lines, peel_lines, mlines)
            cone_sz = compute_rev_cone_capped(mod, rev, cap=500)
            enriched.append(
                {
                    "mod": mod,
                    "line": x["line"],
                    "role": x["role"],
                    "rev_direct": len(importers),
                    "rev_cone": cone_sz if cone_sz <= 500 else ">500",
                    "mod_lines": mlines,
                    "exclusive_peel_files": peel_cnt,
                    "exclusive_peel_lines": peel_lines,
                    "decl": x["decl"],
                }
            )
        dups.append(
            {
                "published_type": tname,
                "occurrences": len(unique_paths),
                "proof_occurrences": proof_count,
                "filtered_forwarder_count": wrapper_count,
                "max_impact_lines": max_peel_lines,
                "providers": enriched,
            }
        )

    dups.sort(key=lambda d: (-d["max_impact_lines"], -d["proof_occurrences"], -d["occurrences"], d["published_type"]))
    print(
        json.dumps(
            {
                "indexed_commit": idx.get_meta(conn, "commit")[:10],
                "ref": ref,
                "elapsed_s": round(time.monotonic() - t0, 2),
                "duplicate_published_types": dups[: args.limit],
            },
            indent=2,
        )
    )
    return 0


def cmd_neg_instances(args: argparse.Namespace) -> int:
    """Scan `attribute [-instance]` workarounds (#599) grouped by disabled instance name."""
    t0 = time.monotonic()
    repo = idx.resolve_repo(args.repo, args.db)
    p = subprocess.run(
        ["git", "-c", "core.quotepath=false", "grep", "-n", "-F", "attribute [-instance]", args.ref, "--", "src/"],
        cwd=str(repo),
        capture_output=True,
        text=True,
        encoding="utf-8",
        errors="replace",
    )
    counts: collections.Counter[str] = collections.Counter()
    files_per_inst: dict[str, set[str]] = collections.defaultdict(set)
    samples: dict[str, list[str]] = collections.defaultdict(list)
    all_files: set[str] = set()
    for ln in p.stdout.splitlines():
        parsed = parse_git_grep_line(ln, args.ref)
        if not parsed:
            continue
        path, lno, text = parsed
        # Ignore comment lines mentioning `attribute [-instance]`
        stripped = text.strip()
        if stripped.startswith("--") or stripped.startswith("/-"):
            continue
        m = re.search(r"attribute\s+\[-instance\]\s+(.+)", text)
        if not m:
            continue
        payload = m.group(1).split("--", 1)[0]
        for tok in payload.split():
            tok = tok.strip(",;")
            if not tok:
                continue
            # Lean 4 scoped syntax: `attribute [-instance] Foo Bar in <decl>`
            if tok == "in":
                break
            counts[tok] += 1
            files_per_inst[tok].add(path)
            all_files.add(path)
            if len(samples[tok]) < 5:
                samples[tok].append(f"{path}:{lno}")
    top = [
        {
            "instance": k,
            "count": v,
            "file_count": len(files_per_inst[k]),
            "sample_files": samples[k],
        }
        for k, v in counts.most_common(args.limit)
    ]
    print(
        json.dumps(
            {
                "ref": args.ref,
                "elapsed_s": round(time.monotonic() - t0, 2),
                "total_hits": sum(counts.values()),
                "unique_files": len(all_files),
                "top_disabled_instances": top,
            },
            indent=2,
        )
    )
    return 0


def cmd_duplicate_stems(args: argparse.Namespace) -> int:
    """
    Pure SQLite (<1.5s) cross-subtree duplicate radar:
      - Twin directories sharing >= min_shared non-generic module basenames, ranked by lines & low external importers.
      - Duplicate module basenames whose copy has large lines or exclusive peel.
    """
    t0 = time.monotonic()
    conn = idx.init_db(args.db)
    mods, fwd, rev = idx.load_graph(conn)

    by_stem: dict[str, list[str]] = collections.defaultdict(list)
    by_dir: dict[str, list[str]] = collections.defaultdict(list)
    for mod in mods:
        if "." in mod:
            parent, stem = mod.rsplit(".", 1)
        else:
            parent, stem = "", mod
        by_dir[parent].append(mod)
        if stem not in GENERIC_STEMS and not stem.startswith("Imports") and len(stem) >= 4:
            by_stem[stem].append(mod)

    # Part A: Twin directories sharing >= min_shared non-generic stems
    pair_stems: dict[tuple[str, str], list[str]] = collections.defaultdict(list)
    for stem, mlist in by_stem.items():
        if len(mlist) < 2 or len(mlist) > 12:
            continue
        dirs = sorted({m.rsplit(".", 1)[0] for m in mlist if "." in m})
        for d1, d2 in itertools.combinations(dirs, 2):
            pair_stems[(d1, d2)].append(stem)

    dir_stats_cache: dict[str, tuple[int, int, int]] = {}

    def get_dir_stats(d: str) -> tuple[int, int, int]:
        if d in dir_stats_cache:
            return dir_stats_cache[d]
        d_mods = set(by_dir.get(d, ()))
        d_lines = sum(mods[m][1] for m in d_mods)
        ext_imps: set[str] = set()
        for m in d_mods:
            for imp in rev.get(m, ()):
                if imp not in d_mods:
                    ext_imps.add(imp)
        res = (len(d_mods), d_lines, len(ext_imps))
        dir_stats_cache[d] = res
        return res

    twins = []
    for (d1, d2), stems in pair_stems.items():
        if len(stems) < args.min_shared:
            continue
        f1, l1, ext1 = get_dir_stats(d1)
        f2, l2, ext2 = get_dir_stats(d2)
        min_lines_pair = min(l1, l2)
        if max(l1, l2) < args.min_lines:
            continue
        twins.append(
            {
                "shared_stems": len(stems),
                "sample_stems": sorted(stems)[:8],
                "min_dir_lines": min_lines_pair,
                "dir_a": {"dir": d1, "files": f1, "lines": l1, "external_importers": ext1},
                "dir_b": {"dir": d2, "files": f2, "lines": l2, "external_importers": ext2},
            }
        )
    twins.sort(key=lambda x: (-x["shared_stems"], -x["min_dir_lines"]))

    # Part B: High-impact individual duplicate module basenames (with exclusive peel!)
    dup_mods = []
    for stem, mlist in by_stem.items():
        if len(mlist) < 2 or len(mlist) > 8:
            continue
        copies = []
        best_impact = 0
        for m in sorted(mlist):
            mlines = mods[m][1]
            importers = rev.get(m, set())
            peel_cnt, peel_lines = 0, 0
            if len(importers) == 1:
                host = next(iter(importers))
                peel_cnt, peel_lines = compute_exclusive_peel(host, m, mods, fwd, rev)
            impact = max(mlines, peel_lines)
            if impact > best_impact:
                best_impact = impact
            cone_sz = compute_rev_cone_capped(m, rev, cap=500)
            copies.append(
                {
                    "mod": m,
                    "lines": mlines,
                    "rev_direct": len(importers),
                    "rev_cone": cone_sz if cone_sz <= 500 else ">500",
                    "exclusive_peel_files": peel_cnt,
                    "exclusive_peel_lines": peel_lines,
                }
            )
        if best_impact >= args.min_lines:
            dup_mods.append({"stem": stem, "copies_count": len(copies), "max_impact_lines": best_impact, "copies": copies})
    dup_mods.sort(key=lambda x: (-x["max_impact_lines"], x["stem"]))

    print(
        json.dumps(
            {
                "indexed_commit": idx.get_meta(conn, "commit")[:10],
                "elapsed_s": round(time.monotonic() - t0, 2),
                "twin_directories": twins[: args.limit],
                "high_impact_duplicate_modules": dup_mods[: args.limit],
            },
            indent=2,
        )
    )
    return 0


def _get_tree_map(repo: Path, ref: str) -> dict[str, str]:
    key = (str(repo), ref)
    cached = _LS_TREE_CACHE.get(key)
    if cached is not None:
        return cached
    tree_out = idx.git_run(repo, ["ls-tree", "-r", ref, "--", "src/"])
    path_to_sha: dict[str, str] = {}
    for ln in tree_out.splitlines():
        if "\t" not in ln:
            continue
        meta, p = ln.split("\t", 1)
        path_to_sha[p] = meta.split()[2]
    _LS_TREE_CACHE[key] = path_to_sha
    return path_to_sha


def _read_git_blobs(repo: Path, ref: str, paths: list[str]) -> dict[str, str]:
    """Read many files from `ref` in one `git cat-file --batch` pass."""
    if not paths:
        return {}
    uniq_paths = sorted(set(paths))
    key = (str(repo), ref)
    if key in _LS_TREE_CACHE or len(uniq_paths) > 150:
        path_to_sha = _get_tree_map(repo, ref)
    else:
        path_to_sha = {}
        for i in range(0, len(uniq_paths), 100):
            chunk = uniq_paths[i : i + 100]
            tree_out = idx.git_run(repo, ["ls-tree", "-r", ref, "--"] + chunk)
            for ln in tree_out.splitlines():
                if "\t" not in ln:
                    continue
                meta, p = ln.split("\t", 1)
                path_to_sha[p] = meta.split()[2]
    specs = [(p, path_to_sha[p]) for p in uniq_paths if p in path_to_sha]
    return {p: raw.decode("utf-8", errors="replace") for p, raw in idx.stream_git_blobs(repo, specs)}


def cmd_heavy_pillars(args: argparse.Namespace) -> int:
    """
    #975-pattern surgical scalpel:
    Find heavy exclusive proof pillars (`exclusive_peel >= min_lines`, `host_rev_cone <= max_host_cone`)
    feeding Main-close hosts, extract their exported Published/Literature/theorem names, and rank them
    so deep researchers can inspect 1-to-3-reader clauses for 30k-150kL narrowing cuts.
    """
    t0 = time.monotonic()
    repo = idx.resolve_repo(args.repo, args.db)
    conn = idx.init_db(args.db)
    mods, fwd, rev = idx.load_graph(conn)

    pillars: list[tuple[int, int, int, str, str]] = []
    for seed, imps in rev.items():
        if len(imps) != 1 or seed not in mods:
            continue
        host = next(iter(imps))
        cnt, lines = compute_exclusive_peel(host, seed, mods, fwd, rev)
        if lines >= args.min_lines and cnt >= args.min_files:
            hrc = compute_rev_cone_capped(host, rev, cap=max(args.max_host_cone + 1, 100))
            if hrc <= args.max_host_cone:
                pillars.append((lines, cnt, hrc, host, seed))

    pillars.sort(reverse=True)
    top_slice = pillars[: args.limit]
    seed_paths = [mods[seed][0] for _, _, _, _, seed in top_slice]
    blobs = _read_git_blobs(repo, args.ref, seed_paths)

    pub_re = re.compile(
        r"((?:GlobalTheory|PositivityTheory|CompanionTheory|ReciprocityTheory|UpperTheory)\.[A-Za-z0-9_.'₀₁₂₃₄₅₆₇₈₉]*Published[A-Za-z0-9_.'₀₁₂₃₄₅₆₇₈₉]*\.[A-Za-z0-9_.'₀₁₂₃₄₅₆₇₈₉]+)"
    )
    thm_re = re.compile(r"^\s*(?:theorem|def)\s+([A-Za-z0-9_.'₀₁₂₃₄₅₆₇₈₉]+)\b[^\n]*", re.MULTILINE)

    items = []
    for lines, cnt, hrc, host, seed in top_slice:
        txt = blobs.get(mods[seed][0], "")
        pubs = sorted(set(pub_re.findall(txt)))[:5]
        thms = [m.group(0).strip()[:110] for m in thm_re.finditer(txt)][-2:]
        items.append(
            {
                "peel_files": cnt,
                "peel_lines": lines,
                "host_rev_cone": hrc,
                "host_mod": host,
                "seed_mod": seed,
                "published_refs": pubs,
                "tail_decls": thms,
            }
        )

    print(
        json.dumps(
            {
                "indexed_commit": idx.get_meta(conn, "commit")[:10],
                "ref": args.ref,
                "elapsed_s": round(time.monotonic() - t0, 2),
                "total_matching_pillars": len(pillars),
                "pillars": items,
            },
            indent=2,
        )
    )
    return 0


def _struct_hdr_flags(hdr_after_name: str) -> tuple[bool, bool]:
    """Return (has_extends, is_prop) ignoring `: ...` inside parameter binders."""
    top_chars: list[str] = []
    depth = 0
    for ch in hdr_after_name:
        if ch in "([{":
            depth += 1
        elif ch in ")]}":
            if depth > 0:
                depth -= 1
        elif depth == 0:
            top_chars.append(ch)
    top_s = "".join(top_chars)
    return bool(re.search(r"\bextends\b", top_s)), bool(re.search(r":\s*Prop\b", top_s))


def parse_lean_structures(clean_text: str, include_empty: bool = False) -> list[dict[str, Any]]:
    """
    Parse Lean 4 `structure` blocks (including multi-line headers/extends, blank lines,
    arbitrary indentation, parameterized fields, and optionally header-only empty structs)
    from comment-stripped text.
    """
    hdr_re = re.compile(
        rf"^(\s*)(?:@\[[^\]]*\]\s*)*"
        rf"((?:(?:public|private|protected|noncomputable|meta)\s+)*)"
        rf"structure\s+({idx.LEAN_QUAL_IDENT}){idx.LEAN_ID_END}(.*)$"
    )
    top_stop_re = re.compile(
        r"^(?:@\[[^\]]*\]\s*)*(?:(?:public|private|protected|noncomputable|unsafe|partial|scoped|local|meta)\s+)*"
        r"(?:theorem|lemma|def|abbrev|instance|structure|inductive|class|opaque|axiom|alias|section|end|namespace|variable|open|set_option|attribute)\b"
    )
    kw_skip = {"where", "extends", "deriving", "public", "private", "protected", "with"}
    lines = clean_text.splitlines()
    n = len(lines)
    out: list[dict[str, Any]] = []
    i = 0
    while i < n:
        ms = hdr_re.match(lines[i])
        if not ms:
            i += 1
            continue
        hdr_indent = len(ms.group(1))
        mods_kw = ms.group(2)
        sname = ms.group(3)
        is_private = bool(re.search(r"\bprivate\b", mods_kw))
        attrs = _extract_attr_names(lines, i)

        # Locate `where` on this line or up to 15 header continuation lines
        where_idx = -1
        saw_assign = False
        last_hdr_idx = i
        for k in range(i, min(i + 16, n)):
            ln = lines[k]
            st = ln.strip()
            if k > i and st:
                ind = len(ln) - len(ln.lstrip(" "))
                if ind <= hdr_indent and (
                    top_stop_re.match(st) or not re.match(r"^(?:extends|where|deriving)\b", st)
                ):
                    break
            if st:
                last_hdr_idx = k
            mw = re.search(r"\bwhere\b", ln)
            ma = ln.find(":=")
            if ma != -1 and (not mw or ma < mw.start()):
                saw_assign = True
                break
            if mw:
                where_idx = k
                break
        if where_idx == -1:
            if include_empty and not saw_assign:
                hdr_tail_parts = [ms.group(4)] + [lines[k] for k in range(i + 1, last_hdr_idx + 1)]
                has_extends, is_prop = _struct_hdr_flags(" ".join(hdr_tail_parts))
                out.append(
                    {
                        "name": sname,
                        "fields": [],
                        "start_idx": i,
                        "end_idx": last_hdr_idx + 1,
                        "extends": has_extends,
                        "is_prop": is_prop,
                        "is_private": is_private,
                        "attrs": attrs,
                    }
                )
                i = last_hdr_idx + 1
            else:
                i += 1
            continue

        hdr_tail_parts = [ms.group(4)] + [lines[k] for k in range(i + 1, where_idx + 1)]
        has_extends, is_prop = _struct_hdr_flags(" ".join(hdr_tail_parts))

        # Collect body lines until indentation drops to <= hdr_indent (or deriving)
        j = where_idx + 1
        while j < n:
            ln = lines[j]
            st = ln.strip()
            if st:
                ind = len(ln) - len(ln.lstrip(" "))
                if ind <= hdr_indent or st.startswith("deriving "):
                    break
            j += 1

        # Determine field indentation dynamically from first actual field line
        field_indent: int | None = None
        for p_idx in range(where_idx + 1, j):
            st = lines[p_idx].strip()
            if not st or st.startswith("@[") or st.startswith("|") or st.endswith("::"):
                continue
            field_indent = len(lines[p_idx]) - len(lines[p_idx].lstrip(" "))
            break

        fields: list[tuple[str, str]] = []
        if field_indent is not None and field_indent > hdr_indent:
            p_idx = where_idx + 1
            while p_idx < j:
                ln = lines[p_idx]
                st = ln.strip()
                if not st or st.startswith("@[") or st.startswith("|") or st.endswith("::"):
                    p_idx += 1
                    continue
                ind = len(ln) - len(ln.lstrip(" "))
                if ind == field_indent:
                    mf = re.match(rf"^(?:(?:public|private|protected)\s+)?({idx.LEAN_IDENT}){idx.LEAN_ID_END}(.*)$", st)
                    if mf and mf.group(1) not in kw_skip:
                        fname = mf.group(1)
                        sig_parts = [mf.group(2)]
                        q_idx = p_idx + 1
                        while q_idx < j and len(sig_parts) < 6:
                            q_ln = lines[q_idx]
                            q_st = q_ln.strip()
                            if not q_st:
                                q_idx += 1
                                continue
                            q_ind = len(q_ln) - len(q_ln.lstrip(" "))
                            if q_ind <= field_indent:
                                break
                            sig_parts.append(q_st)
                            q_idx += 1
                        sig_text = " ".join(sig_parts)
                        depth = 0
                        colon_pos = -1
                        for pos, ch in enumerate(sig_text):
                            if ch in "([{":
                                depth += 1
                            elif ch in ")]}":
                                if depth > 0:
                                    depth -= 1
                            elif ch == ":" and depth == 0 and sig_text[pos : pos + 2] != ":=":
                                colon_pos = pos
                                break
                        if colon_pos != -1:
                            ftype = sig_text[colon_pos + 1 :].strip()
                            # Trim trailing default value `:= ...` at depth 0 if present
                            d2 = 0
                            for pos in range(len(ftype)):
                                ch = ftype[pos]
                                if ch in "([{":
                                    d2 += 1
                                elif ch in ")]}":
                                    if d2 > 0:
                                        d2 -= 1
                                elif d2 == 0 and ftype[pos : pos + 2] == ":=":
                                    ftype = ftype[:pos].strip()
                                    break
                            fields.append((fname, " ".join(ftype.split())[:100]))
                p_idx += 1

        out.append(
            {
                "name": sname,
                "fields": fields,
                "start_idx": i,
                "end_idx": j,
                "extends": has_extends,
                "is_prop": is_prop,
                "is_private": is_private,
                "attrs": attrs,
            }
        )
        i = j
    return out


def _find_enclosing_decls(clean_lines: list[str], match_line_indices: list[int]) -> list[str]:
    decl_re = re.compile(
        rf"^\s*(?:@\[[^\]]*\]\s*)*(?:(?:public|private|protected|noncomputable|unsafe|partial|scoped|local|meta)\s+)*"
        rf"(?:theorem|lemma|def|abbrev|instance|structure)\s+({idx.LEAN_QUAL_IDENT}){idx.LEAN_ID_END}"
    )
    found: list[str] = []
    seen: set[str] = set()
    for l_idx in match_line_indices:
        name = "(top-level)"
        for k in range(l_idx, -1, -1):
            m = decl_re.match(clean_lines[k])
            if m:
                name = m.group(1)
                break
        if name not in seen:
            seen.add(name)
            found.append(name)
    return found


def _match_local_wrapper(rhs_expr: str, host_decls: list[dict[str, Any]]) -> dict[str, Any] | None:
    rclean = rhs_expr.strip().lstrip("(")
    if rclean.startswith("_root_."):
        rclean = rclean[len("_root_.") :]
    rshort = rclean.rsplit(".", 1)[-1]
    if not rshort:
        return None
    for d in host_decls:
        dclean = d["name"][len("_root_.") :] if d["name"].startswith("_root_.") else d["name"]
        if dclean == rclean or dclean.endswith("." + rclean) or dclean.rsplit(".", 1)[-1] == rshort:
            return d
    return None


def check_bundle_cut_safety(
    host_mod: str,
    dep_mod: str,
    dropped_assign_lines: set[int],
    dropped_rhs_exprs: list[str],
    mods: dict[str, tuple[str, int]],
    fwd: dict[str, set[str]],
    rev: dict[str, set[str]],
    rc_clean_blobs: dict[str, str],
    repo: Path,
    ref: str,
    dep_blobs_cache: dict[str, str],
    host_decls_cache: dict[str, list[dict[str, Any]]] | None = None,
) -> dict[str, Any]:
    """
    Host secondary-symbol & wrapper-reuse guard for candidate bundle-field cuts:
      1. Verifies whether local wrappers used by dropped field assignments still have other
         callers in `host_mod` or its direct importers (`rev[host_mod]`).
      2. Checks whether `host_mod`'s remaining body still references ANY secondary exported
         symbol from `dep_mod` (or its peeled exclusive subtree).
    """
    host_path = mods[host_mod][0]
    host_clean = rc_clean_blobs.get(host_path, "")
    if not host_clean:
        raw_h = _read_git_blobs(repo, ref, [host_path])
        host_clean = strip_lean_comments(raw_h.get(host_path, ""))
        rc_clean_blobs[host_path] = host_clean

    if host_decls_cache is None:
        host_decls_cache = {}
    if host_mod not in host_decls_cache:
        host_decls_cache[host_mod] = _extract_top_decls(host_clean)
    host_decls = host_decls_cache[host_mod]

    # Ensure direct importers of host_mod are present in rc_clean_blobs
    rev_hosts = sorted(rev.get(host_mod, ()))
    miss_rev = [mods[im][0] for im in rev_hosts if im in mods and mods[im][0] not in rc_clean_blobs]
    if miss_rev:
        for mp, mtxt in _read_git_blobs(repo, ref, miss_rev).items():
            rc_clean_blobs[mp] = strip_lean_comments(mtxt)

    host_lines = host_clean.splitlines()
    # Identify header line indices to exclude when searching wrapper references
    header_end = 0
    for li, ln in enumerate(host_lines):
        st = ln.strip()
        if not st or st == "module" or st.startswith("prelude") or idx.IMPORT_RE.match(st):
            header_end = li + 1
        else:
            break

    excluded_lines: set[int] = set(dropped_assign_lines)
    wrapper_reuse_blockers: list[dict[str, Any]] = []
    masked_unused_wrappers: list[dict[str, Any]] = []
    seen_wrappers: set[str] = set()

    for rhs_expr in dropped_rhs_exprs:
        w = _match_local_wrapper(rhs_expr, host_decls)
        if not w or w["name"] in seen_wrappers:
            continue
        seen_wrappers.add(w["name"])
        wshort = w["name"].rsplit(".", 1)[-1]
        w_pat = re.compile(rf"{idx.LEAN_ID_PREV}{re.escape(wshort)}{idx.LEAN_ID_END}")

        rem_host_lines: list[int] = []
        for li in range(header_end, len(host_lines)):
            if w["start_idx"] <= li < w["end_idx"] or li in dropped_assign_lines:
                continue
            if wshort in host_lines[li] and w_pat.search(host_lines[li]):
                rem_host_lines.append(li + 1)

        rem_rev_mods: list[str] = []
        for im in rev_hosts:
            if im not in mods:
                continue
            im_txt = rc_clean_blobs.get(mods[im][0], "")
            if wshort not in im_txt:
                continue
            im_lines = im_txt.splitlines()
            past_hdr = False
            for rln in im_lines:
                rst = rln.strip()
                if not past_hdr:
                    if not rst or rst == "module" or rst.startswith("prelude") or idx.IMPORT_RE.match(rst):
                        continue
                    past_hdr = True
                if wshort in rln and w_pat.search(rln):
                    rem_rev_mods.append(im)
                    break

        if rem_host_lines or rem_rev_mods:
            wrapper_reuse_blockers.append(
                {
                    "wrapper": w["name"],
                    "remaining_host_lines": rem_host_lines[:10],
                    "remaining_rev_mods": rem_rev_mods[:10],
                }
            )
        else:
            masked_unused_wrappers.append(
                {
                    "host": host_mod,
                    "wrapper": w["name"],
                    "lines": [w["start_idx"] + 1, w["end_idx"]],
                }
            )
            for li in range(w["start_idx"], w["end_idx"]):
                excluded_lines.add(li)

    peel_res = idx.compute_multi_peel(mods, fwd, rev, [(host_mod, dep_mod)], mode="zero-indegree")
    dead_set: set[str] = peel_res["dead"]
    check_mods = [dep_mod] + sorted(dead_set - {dep_mod})[:299]
    miss_deps = [mods[cm][0] for cm in check_mods if cm in mods and mods[cm][0] not in dep_blobs_cache]
    if miss_deps:
        dep_blobs_cache.update(_read_git_blobs(repo, ref, miss_deps))

    dep_clean_map = {
        cm: strip_lean_comments(dep_blobs_cache.get(mods[cm][0], ""))
        for cm in check_mods
        if cm in mods
    }
    sym_res = idx.check_host_secondary_symbols(host_clean, dep_clean_map, excluded_line_indices=excluded_lines)
    safe = (not wrapper_reuse_blockers) and (not sym_res["blocked"])
    return {
        "safe": safe,
        "wrapper_reuse_blockers": wrapper_reuse_blockers,
        "masked_unused_wrappers": masked_unused_wrappers,
        "secondary_symbol_blockers": sym_res["secondary_symbol_blockers"],
        "total_blocker_symbols": sym_res["total_blocker_symbols"],
        "has_instances_or_notations": sym_res["has_instances_or_notations"],
        "checked_dep_modules": sym_res["checked_dep_modules"],
        "peel_files": len(dead_set),
        "peel_lines": sum(mods[m][1] for m in dead_set),
    }


def _estimate_field_peels(
    fields_list: list[dict[str, Any]],
    struct_mod: str,
    struct_name: str,
    rc: set[str],
    mods: dict[str, tuple[str, int]],
    fwd: dict[str, set[str]],
    rev: dict[str, set[str]],
    rc_clean_blobs: dict[str, str],
    repo: Path,
    ref: str,
    dep_blobs_cache: dict[str, str] | None = None,
) -> None:
    """Attach estimated exclusive peel impact to low-reader fields, verifying host secondary-symbol safety."""
    excl_candidates: list[tuple[str, str]] = []
    dep_paths_needed: list[str] = []
    for cmod in rc:
        cp = mods[cmod][0]
        ctext = rc_clean_blobs.get(cp, "")
        if not (struct_name in ctext or struct_mod in ctext or struct_mod in fwd.get(cmod, ())):
            continue
        for dep in fwd.get(cmod, ()):
            if len(rev.get(dep, ())) == 1 and dep in mods:
                excl_candidates.append((cmod, dep))
                dp = mods[dep][0]
                if dep_blobs_cache is None or dp not in dep_blobs_cache:
                    dep_paths_needed.append(dp)
    if not excl_candidates:
        return

    peel_cache: dict[tuple[str, str], tuple[int, int]] = {}
    if dep_blobs_cache is None:
        dep_blobs_cache = {}
    if dep_paths_needed:
        dep_blobs_cache.update(_read_git_blobs(repo, ref, dep_paths_needed))

    host_decls_cache: dict[str, list[dict[str, Any]]] = {}

    for fld in fields_list:
        fname = fld["field"]
        ftype = fld["type"]
        t_tokens = re.findall(r"[A-Za-z_][A-Za-z0-9_'₀₁₂₃₄₅₆₇₈₉]{4,}", ftype)
        short_type = t_tokens[-1] if t_tokens else ""
        assign_re = re.compile(
            rf"^(?![ \t]*(?:have|let|obtain|show|suffices)\b)[^\n]*(?:^|[\s{{,])[ \t]*{re.escape(fname)}[ \t]*:=[ \t]*\(?[ \t]*([A-Za-z0-9_.'₀₁₂₃₄₅₆₇₈₉]+)"
        )
        best_peel = (0, 0, "", "")
        best_blocked: tuple[int, int, str, str, str] = (0, 0, "", "", "")
        for cmod, dep in excl_candidates:
            cp = mods[cmod][0]
            ctext = rc_clean_blobs.get(cp, "")
            if fname not in ctext:
                continue
            ctext_lines = ctext.splitlines()
            matches: list[tuple[int, str]] = []
            for li_c, cln in enumerate(ctext_lines):
                if fname not in cln:
                    continue
                rm = assign_re.search(cln)
                if rm:
                    matches.append((li_c, rm.group(1)))
            if not matches:
                continue
            matched = False
            drop_line_idxs: set[int] = set()
            rhs_exprs: list[str] = []
            dblob = dep_blobs_cache.get(mods[dep][0], "")
            for li_c, rhs_full in matches:
                rhs_ident = rhs_full.rsplit(".", 1)[-1]
                if not short_type and len(rhs_ident) < 5:
                    continue
                if (short_type and (short_type in dblob or short_type.lower() in dep.lower())) or (
                    rhs_ident and len(rhs_ident) >= 5 and rhs_ident in dblob
                ):
                    matched = True
                    drop_line_idxs.add(li_c)
                    rhs_exprs.append(rhs_full)
            if not matched:
                continue
            if (cmod, dep) not in peel_cache:
                peel_cache[(cmod, dep)] = compute_exclusive_peel(cmod, dep, mods, fwd, rev)
            pc, pl = peel_cache[(cmod, dep)]
            if pl <= 0:
                continue
            guard = check_bundle_cut_safety(
                cmod,
                dep,
                drop_line_idxs,
                rhs_exprs,
                mods,
                fwd,
                rev,
                rc_clean_blobs,
                repo,
                ref,
                dep_blobs_cache,
                host_decls_cache=host_decls_cache,
            )
            if guard["safe"]:
                if pl > best_peel[1]:
                    best_peel = (pc, pl, cmod, dep)
            else:
                reasons: list[str] = []
                if guard["wrapper_reuse_blockers"]:
                    reasons.append("wrapper_reused:" + ",".join(b["wrapper"].rsplit(".", 1)[-1] for b in guard["wrapper_reuse_blockers"][:2]))
                if guard["secondary_symbol_blockers"]:
                    reasons.append("secondary_symbols:" + ",".join(b["short_name"] for b in guard["secondary_symbol_blockers"][:3]))
                if pl > best_blocked[1]:
                    best_blocked = (pc, pl, cmod, dep, "; ".join(reasons))

        if best_peel[1] > 0:
            fld["estimated_peel_files"] = best_peel[0]
            fld["estimated_peel_lines"] = best_peel[1]
            fld["estimated_peel_host"] = best_peel[2].rsplit(".", 1)[-1]
            fld["estimated_peel_seed"] = best_peel[3].rsplit(".", 1)[-1]
        elif best_blocked[1] > 0:
            fld["blocked_peel_files"] = best_blocked[0]
            fld["blocked_peel_lines"] = best_blocked[1]
            fld["blocked_peel_host"] = best_blocked[2].rsplit(".", 1)[-1]
            fld["blocked_peel_seed"] = best_blocked[3].rsplit(".", 1)[-1]
            fld["blocked_peel_reason"] = best_blocked[4]


def _collect_bundle_structures(
    args: argparse.Namespace,
    repo: Path,
    mods: dict[str, tuple[str, int]],
    rev: dict[str, set[str]],
) -> tuple[list[tuple[str, str, dict[str, Any], set[str]]], dict[str, str]]:
    """Shared structure discovery & comment-stripped reverse-cone blob loader for bundle scans."""
    pg = subprocess.run(
        ["git", "-c", "core.quotepath=false", "grep", "-l", "-E", r"^[[:space:]]*((public|private|protected|noncomputable|meta)[[:space:]]+)*structure[[:space:]]+", args.ref, "--", "src/"],
        cwd=str(repo),
        capture_output=True,
        text=True,
        encoding="utf-8",
        errors="replace",
    )
    struct_paths = {p for p in (parse_git_grep_path(ln, args.ref) for ln in pg.stdout.splitlines()) if p.endswith(".lean")}
    path_to_mod = {p: m for m, (p, _) in mods.items()}

    def rev_cone_set(m: str) -> set[str]:
        c = {m}
        q = [m]
        while q:
            cur = q.pop()
            for p in rev.get(cur, ()):
                if p not in c:
                    c.add(p)
                    q.append(p)
        return c

    name_kws = tuple(k.strip().lower() for k in args.name_filter.split(",") if k.strip())
    struct_kws = tuple(k.strip().lower() for k in args.struct_filter.split(",") if k.strip())
    use_struct_filter = struct_kws and not (name_kws and args.struct_filter == DEFAULT_STRUCT_FILTER)

    cand_mods: list[tuple[str, str, set[str]]] = []
    for sp in sorted(struct_paths):
        m = path_to_mod.get(sp)
        if not m:
            continue
        if name_kws and not any(k in m.lower() for k in name_kws):
            continue
        if not rev.get(m):
            continue
        rc = rev_cone_set(m)
        if args.main_only and "Main" not in rc:
            continue
        if len(rc) <= args.max_cone:
            cand_mods.append((m, sp, rc))

    cand_blobs = _read_git_blobs(repo, args.ref, [p for _, p, _ in cand_mods])
    structs: list[tuple[str, str, dict[str, Any], set[str]]] = []
    for m, p, rc in cand_mods:
        raw_txt = cand_blobs.get(p, "")
        if not raw_txt:
            continue
        clean_txt = strip_lean_comments(raw_txt)
        for st in parse_lean_structures(clean_txt):
            sname = st["name"]
            if use_struct_filter and not any(k in sname.lower() or k in m.lower() for k in struct_kws):
                continue
            if len(st["fields"]) >= args.min_fields:
                structs.append((m, p, st, rc))

    all_rc_paths = sorted({mods[rm][0] for _, _, _, rc in structs for rm in rc if rm in mods})
    rc_raw_blobs = _read_git_blobs(repo, args.ref, all_rc_paths)
    rc_clean_blobs = {rp: strip_lean_comments(txt) for rp, txt in rc_raw_blobs.items()}
    return structs, rc_clean_blobs


def _split_top_arrows(type_str: str) -> list[str]:
    """Split a Lean type expression at depth-0 `→` or `->` arrows."""
    parts: list[str] = []
    cur: list[str] = []
    depth = 0
    i = 0
    n = len(type_str)
    while i < n:
        ch = type_str[i]
        if ch in "([{⟨":
            depth += 1
            cur.append(ch)
            i += 1
        elif ch in ")]}⟩":
            if depth > 0:
                depth -= 1
            cur.append(ch)
            i += 1
        elif depth == 0 and ch == "→":
            parts.append("".join(cur).strip())
            cur = []
            i += 1
        elif depth == 0 and type_str[i : i + 2] == "->":
            parts.append("".join(cur).strip())
            cur = []
            i += 2
        else:
            cur.append(ch)
            i += 1
    tail = "".join(cur).strip()
    if tail or parts:
        parts.append(tail)
    return [p for p in parts if p] or [type_str.strip()]


def _split_top_commas(expr: str) -> list[str]:
    """Split an expression by commas at nesting depth 0."""
    parts: list[str] = []
    cur: list[str] = []
    depth = 0
    for ch in expr:
        if ch in "([{⟨":
            depth += 1
            cur.append(ch)
        elif ch in ")]}⟩":
            if depth > 0:
                depth -= 1
            cur.append(ch)
        elif ch == "," and depth == 0:
            item = "".join(cur).strip()
            if item:
                parts.append(item)
            cur = []
        else:
            cur.append(ch)
    tail = "".join(cur).strip()
    if tail:
        parts.append(tail)
    return parts


def _strip_parens_and_ascription(expr: str) -> str:
    """Strip outer `(...)` and top-level `: Type` ascription from a Lean scrutinee/RHS."""
    s = _strip_outer_parens(expr.strip())
    depth = 0
    for i, ch in enumerate(s):
        if ch in "([{⟨":
            depth += 1
        elif ch in ")]}⟩":
            if depth > 0:
                depth -= 1
        elif ch == ":" and depth == 0 and (i + 1 >= len(s) or s[i + 1] != "="):
            s = _strip_outer_parens(s[:i].strip())
            break
    return s.strip()


def _split_binder_colon(inner: str) -> tuple[str, str] | None:
    """Split `lhs : ty` inside a binder at the first depth-0 colon."""
    depth = 0
    for i, ch in enumerate(inner):
        if ch in "([{⟨":
            depth += 1
        elif ch in ")]}⟩":
            if depth > 0:
                depth -= 1
        elif ch == ":" and depth == 0 and (i + 1 >= len(inner) or inner[i + 1] != "="):
            return inner[:i].strip(), inner[i + 1 :].strip()
    return None


def _type_head_is_struct(type_str: str, sname: str) -> bool:
    """Return True if a Lean type expression's outermost head symbol is `sname`."""
    t = _strip_outer_parens(type_str.strip())
    if not t or t[0] in ("{", "[", "⟨"):
        return False
    if len(_split_top_arrows(t)) > 1:
        return False
    toks = _split_top_tokens(t)
    if not toks:
        return False
    head = toks[0].lstrip("@")
    if head in ("∀", "forall", "∃", "exists", "fun", "λ", "Π", "¬"):
        return False
    if any(tok in {"=", "≠", "∧", "∨", "↔", "→", "->", "×", "⊕", "≤", "<", "≥", ">"} for tok in toks[1:]):
        return False
    return head == sname or head.endswith("." + sname)


def _ingest_binder_str(
    binder_str: str,
    sname: str,
    struct_vars: set[str],
    ident_re: re.Pattern[str],
    allow_bare: bool = False,
) -> tuple[list[str], bool]:
    """
    Update `struct_vars` from a binder list `(a : T) {b : U} ...`.
    Returns `(explicit_domain_types, has_positional_binder_pattern)` where
    each explicit/instance variable slot contributes its type in intro order
    (skipping `{...}` / `⦃...⦄` implicit curly binders not consumed by bare `intro`/`rintro`).
    """
    domains: list[str] = []
    has_pos_pat = False
    toks = _split_top_tokens(binder_str.strip())
    if allow_bare and toks and toks[0][0] not in "({⦃[" and ":" in binder_str:
        toks = [f"({binder_str.strip()})"]
    for tok in toks:
        if len(tok) < 2 or not (
            (tok[0] == "(" and tok[-1] == ")")
            or (tok[0] == "{" and tok[-1] == "}")
            or (tok[0] == "⦃" and tok[-1] == "⦄")
            or (tok[0] == "[" and tok[-1] == "]")
        ):
            continue
        is_curly_implicit = tok[0] in "{⦃"
        parsed = _split_binder_colon(tok[1:-1].strip())
        if not parsed:
            if tok[0] == "[":
                # Anonymous typeclass instance `[Field E]` may still consume an `intro _` slot
                domains.append(tok[1:-1].strip())
            continue
        lhs, ty = parsed
        lhs_toks = _split_top_tokens(lhs)
        if not is_curly_implicit:
            n_slots = max(1, len(lhs_toks))
            domains.extend([ty] * n_slots)
        is_s = _type_head_is_struct(ty, sname)
        for pat in lhs_toks:
            if is_s and ("⟨" in pat or pat == ".mk" or pat.endswith(".mk")):
                has_pos_pat = True
            elif ident_re.match(pat):
                if is_s and pat != "_":
                    struct_vars.add(pat)
                else:
                    struct_vars.discard(pat)
    return domains, has_pos_pat


def _analyze_decl_sig_for_struct(
    params_str: str,
    ret_str: str,
    sname: str,
    base_vars: set[str],
    ident_re: re.Pattern[str],
) -> tuple[set[str], bool, list[str], bool]:
    """
    Analyze a declaration signature for bindings and goal types related to `sname`.
    Returns `(struct_vars, has_binder_pos_pat, ordered_goal_domains, ret_is_struct)`.
    """
    struct_vars = set(base_vars)
    _, has_pos_pat = _ingest_binder_str(params_str, sname, struct_vars, ident_re, allow_bare=False)

    domains: list[str] = []
    cur = ret_str.strip()
    while cur:
        if cur.startswith("∀") or cur.startswith("forall "):
            depth = 0
            comma_pos = -1
            start = 1 if cur.startswith("∀") else 7
            for pos in range(start, len(cur)):
                ch = cur[pos]
                if ch in "([{⟨":
                    depth += 1
                elif ch in ")]}⟩":
                    if depth > 0:
                        depth -= 1
                elif ch == "," and depth == 0:
                    comma_pos = pos
                    break
            if comma_pos != -1:
                binders = cur[start:comma_pos].strip()
                rest = cur[comma_pos + 1 :].strip()
                # Do not pre-add ∀ binder names to struct_vars before tactic `intro` introduces them,
                # so track domain types in `domains` via a scratch set.
                doms, pat_hit = _ingest_binder_str(binders, sname, set(), ident_re, allow_bare=True)
                domains.extend(doms)
                if pat_hit:
                    has_pos_pat = True
                cur = rest
                continue
        arrows = _split_top_arrows(cur)
        if len(arrows) > 1:
            domains.append(arrows[0])
            cur = " → ".join(arrows[1:]) if len(arrows) > 2 else arrows[1]
            continue
        break

    ret_is_struct = _type_head_is_struct(cur, sname) if cur else False
    return struct_vars, has_pos_pat, domains, ret_is_struct


def find_struct_destructuring_hits(
    clean_text: str,
    sname: str,
    skip_range: tuple[int, int] | None = None,
) -> list[dict[str, Any]]:
    """
    Scoped detector for positional destructuring / construction of structure `sname`
    inside comment-stripped Lean source `clean_text`.

    Tracks `variable`, parameter, `∀`/`→` goal-domain, and local `have`/`let` bindings
    of head type `sname` per declaration so unrelated `⟨...⟩` / `.1` expressions (e.g.
    `obtain ⟨...⟩ := lem hP2`, `hT.pins.2.1.1`, or subgoal `rintro ⟨...⟩`) do not
    false-positive.
    """
    if not clean_text or sname not in clean_text:
        return []

    ident_re = re.compile(rf"^{idx.LEAN_IDENT}$")
    mk_re = re.compile(rf"{idx.LEAN_ID_PREV_NODOT}(?:{idx.LEAN_QUAL_IDENT}\.)?{re.escape(sname)}\.mk{idx.LEAN_ID_END}")
    typed_pat_re = re.compile(r"\b(?:let|obtain)\s+⟨[^⟩\n]*⟩\s*:\s*([^\n:=]+):=")
    typed_tup_re = re.compile(r"⟨[^⟩\n]*⟩\s*:\s*([^,\)\]\n=>]+)")
    typed_fun_re = re.compile(r"\bfun\s*\(?\s*⟨[^⟩\n]*⟩\s*:\s*([^)\n=>]+)")
    typed_ctor_re = re.compile(r"^\s*(?:have|let)\b[^\n:]*:\s*([^\n:=]+):=\s*(?:by\s+)?(?:refine|exact|return)?\s*⟨")
    local_bind_re = re.compile(rf"^\s*(?:have|let)\s+({idx.LEAN_IDENT})\s*:\s*([^\n:=]+):=")
    local_alias_re = re.compile(rf"^\s*(?:have|let)\s+({idx.LEAN_IDENT})\s*:=\s*(.+)$")
    subgoal_re = re.compile(r"^(\s*)(?:have|suffices)\b[^\n:]*:\s*([^\n:=]+?)(?:\s*:=\s*by|\s+by)\s*(?:--.*)?$")
    rcases_re = re.compile(r"\brcases\s+(.+?)\s+with\b")
    obtain_let_re = re.compile(r"\b(?:obtain|let)\s+⟨[^\n]*?:=\s*(.*)$")
    cases_re = re.compile(r"\bcases\s+(?:[A-Za-z_][\w']*\s*:\s*)?([^\n]+)")
    match_re = re.compile(r"\bmatch\s+(.+?)\s+with\b")
    main_goal_ctor_re = re.compile(r"^\s*(?:exact|refine|return)\s*⟨")
    goal_change_re = re.compile(r"^(?:refine|apply|exact|cases|induction|constructor|convert|rcases|·)\b")

    # Collect active `variable` struct bindings active at each line index.
    raw_lines = clean_text.splitlines()
    var_scopes: list[set[str]] = [set()]
    active_vars_by_line: list[set[str]] = []
    for ln in raw_lines:
        stripped = ln.strip()
        if re.match(r"^(?:section|namespace)\b", stripped):
            var_scopes.append(set())
        elif re.match(r"^end\b", stripped):
            if len(var_scopes) > 1:
                var_scopes.pop()
        elif stripped.startswith("variable "):
            _ingest_binder_str(stripped[len("variable ") :], sname, var_scopes[-1], ident_re, allow_bare=False)
        active_vars_by_line.append(set().union(*var_scopes))

    decls = _extract_top_decls(clean_text)
    hits: list[dict[str, Any]] = []
    seen_line_kind: set[tuple[int, str]] = set()

    def add_hit(line_no: int, kind: str, decl_name: str) -> None:
        if skip_range and skip_range[0] < line_no <= skip_range[1]:
            return
        key = (line_no, kind)
        if key not in seen_line_kind:
            seen_line_kind.add(key)
            hits.append({"line": line_no, "kind": kind, "decl": decl_name})

    for d in decls:
        if skip_range and d["start_idx"] < skip_range[1] and d["end_idx"] > skip_range[0]:
            continue
        d_name = d["name"]
        d_line = d["line"]
        base_vars = active_vars_by_line[d["start_idx"]] if 0 <= d["start_idx"] < len(active_vars_by_line) else set()
        struct_vars, has_binder_pat, rem_domains, ret_is_struct = _analyze_decl_sig_for_struct(
            d["params"], d["ret"], sname, base_vars, ident_re
        )
        if has_binder_pat:
            add_hit(d_line, "binder_destructure", d_name)

        body_str = d["body"]
        body_start_line = d_line + d["sig_raw"].count("\n")
        body_lines = body_str.splitlines()
        skip_subgoal_indent: int | None = None

        # Direct positional term constructor immediately after `:=`
        if ret_is_struct and body_str.lstrip().startswith("⟨"):
            for rel_i, bln in enumerate(body_lines):
                if bln.strip():
                    add_hit(body_start_line + rel_i, "positional_constructor", d_name)
                    break

        proj_var_re: re.Pattern[str] | None = None
        proj_vars_key: tuple[str, ...] = ()

        for rel_i, bln in enumerate(body_lines):
            cur_line = body_start_line + rel_i
            s_ln = bln.strip()
            if not s_ln:
                continue

            indent = len(bln) - len(bln.lstrip())
            if skip_subgoal_indent is not None and indent <= skip_subgoal_indent:
                skip_subgoal_indent = None

            # Enter subgoal `have/suffices h : T := by` for non-struct types
            m_sub = subgoal_re.match(bln)
            if m_sub and not _type_head_is_struct(m_sub.group(2), sname):
                skip_subgoal_indent = len(m_sub.group(1))

            # Explicit `sname.mk` positional constructor or pattern
            if mk_re.search(bln):
                add_hit(cur_line, "explicit_mk", d_name)

            # Typed destructures / anonymous positional tuples
            for m_tp in typed_pat_re.finditer(bln):
                if _type_head_is_struct(m_tp.group(1), sname):
                    add_hit(cur_line, "typed_destructure", d_name)
            for m_tt in typed_tup_re.finditer(bln):
                if _type_head_is_struct(m_tt.group(1), sname):
                    add_hit(cur_line, "typed_anonymous_tuple", d_name)
            for m_tf in typed_fun_re.finditer(bln):
                if _type_head_is_struct(m_tf.group(1), sname):
                    add_hit(cur_line, "typed_fun_destructure", d_name)

            # Positional constructor on local `have/let h : S := ... ⟨`
            m_tc = typed_ctor_re.match(bln)
            if m_tc and _type_head_is_struct(m_tc.group(1), sname):
                add_hit(cur_line, "positional_constructor", d_name)

            # Return-type goal positional constructor `refine ⟨...⟩` / `exact ⟨...⟩` / `return ⟨...⟩`
            if ret_is_struct and skip_subgoal_indent is None and main_goal_ctor_re.match(bln):
                add_hit(cur_line, "positional_constructor", d_name)

            # Pair top-level `intro` / `rintro` / leading `fun` with ordered `rem_domains`
            if rem_domains and skip_subgoal_indent is None:
                tac = s_ln[2:].strip() if (s_ln == "by" or s_ln.startswith("by ")) else s_ln
                for seg in [p.strip() for p in tac.split(";") if p.strip()]:
                    if not rem_domains:
                        break
                    if seg.startswith("intro ") or seg == "intro":
                        toks = _split_top_tokens(seg[len("intro") :].strip()) if len(seg) > 5 else ["_"]
                        for dom, pat in zip(rem_domains, toks):
                            if _type_head_is_struct(dom, sname):
                                if "⟨" in pat or pat == ".mk" or pat.endswith(".mk"):
                                    add_hit(cur_line, "domain_rintro_destructure", d_name)
                                elif ident_re.match(pat) and pat != "_":
                                    struct_vars.add(pat)
                        rem_domains = rem_domains[len(toks) :]
                    elif seg.startswith("rintro "):
                        toks = _split_top_tokens(seg[len("rintro") :].strip())
                        for dom, pat in zip(rem_domains, toks):
                            if _type_head_is_struct(dom, sname):
                                if "⟨" in pat or ".mk" in pat:
                                    add_hit(cur_line, "domain_rintro_destructure", d_name)
                                elif ident_re.match(pat) and pat != "_":
                                    struct_vars.add(pat)
                        rem_domains = rem_domains[len(toks) :]
                    elif rel_i == 0 and seg.startswith("fun ") and "=>" in seg:
                        binders_s = seg[len("fun") : seg.index("=>")].strip()
                        toks = _split_top_tokens(binders_s)
                        for dom, pat in zip(rem_domains, toks):
                            if _type_head_is_struct(dom, sname):
                                if "⟨" in pat or ".mk" in pat:
                                    add_hit(cur_line, "domain_fun_destructure", d_name)
                                elif ident_re.match(pat) and pat != "_":
                                    struct_vars.add(pat)
                        rem_domains = []
                        break
                    elif goal_change_re.match(seg):
                        # Subsequent tactics split/rewrite the goal; remaining arrow domains no longer match `rintro`
                        rem_domains = []
                        break

            # Track local `have`/`let` type bindings and aliases (handles shadowing)
            m_lb = local_bind_re.match(bln)
            if m_lb:
                vname, vty = m_lb.group(1), m_lb.group(2)
                if _type_head_is_struct(vty, sname):
                    if vname != "_":
                        struct_vars.add(vname)
                else:
                    struct_vars.discard(vname)
            else:
                m_la = local_alias_re.match(bln)
                if m_la:
                    vname, vrhs = m_la.group(1), m_la.group(2).strip()
                    rhs_clean = _strip_parens_and_ascription(vrhs)
                    if rhs_clean in struct_vars and vname != "_":
                        struct_vars.add(vname)
                    else:
                        struct_vars.discard(vname)

            if not struct_vars:
                continue

            # Scoped numeric projection: `v.1`, `(v).2` for `v in struct_vars`
            cur_vars_key = tuple(sorted(struct_vars, key=len, reverse=True))
            if cur_vars_key != proj_vars_key:
                proj_vars_key = cur_vars_key
                v_alt = "|".join(re.escape(v) for v in cur_vars_key)
                proj_var_re = re.compile(
                    rf"{idx.LEAN_ID_PREV_NODOT}(?:(?:{v_alt})|\(\s*(?:{v_alt})\s*\))\.\d+{idx.LEAN_ID_END}"
                )
            if proj_var_re is not None and proj_var_re.search(bln):
                add_hit(cur_line, "positional_projection", d_name)

            # Scoped `rcases` on `v in struct_vars`
            for m_rc in rcases_re.finditer(bln):
                for scr in _split_top_commas(m_rc.group(1)):
                    if _strip_parens_and_ascription(scr) in struct_vars:
                        add_hit(cur_line, "rcases_destructure", d_name)
                        break

            # Scoped `obtain ⟨...⟩ := v` / `let ⟨...⟩ := v`
            for m_ol in obtain_let_re.finditer(bln):
                rhs = m_ol.group(1).strip()
                if not rhs and rel_i + 1 < len(body_lines):
                    rhs = body_lines[rel_i + 1].strip()
                if _strip_parens_and_ascription(rhs) in struct_vars:
                    add_hit(cur_line, "obtain_let_destructure", d_name)

            # Scoped `cases v`
            m_ca = cases_re.search(bln)
            if m_ca:
                scr = re.split(r"\s+(?:with|using)\b", m_ca.group(1), maxsplit=1)[0]
                if _strip_parens_and_ascription(scr) in struct_vars:
                    add_hit(cur_line, "cases_destructure", d_name)

            # Scoped `match ... v ... with` when followed by `⟨` or `.mk`
            for m_ma in match_re.finditer(bln):
                for scr in _split_top_commas(m_ma.group(1)):
                    if _strip_parens_and_ascription(scr) in struct_vars:
                        window = "\n".join(body_lines[rel_i : rel_i + 12])
                        if "⟨" in window or re.search(rf"\.mk{idx.LEAN_ID_END}", window):
                            add_hit(cur_line, "match_destructure", d_name)
                        break

    return hits


def cmd_unused_fields(args: argparse.Namespace) -> int:
    """
    Scan Main-reaching bundle `structure` definitions (`>= min_fields` fields, `rev_cone <= max_cone`)
    and count projection reads (`.field` / `Struct.field`) across each structure's entire reverse cone
    (including same-file declarations outside the structure body!).
    """
    t0 = time.monotonic()
    repo = idx.resolve_repo(args.repo, args.db)
    conn = idx.init_db(args.db)
    mods, fwd, rev = idx.load_graph(conn)

    structs, rc_clean_blobs = _collect_bundle_structures(args, repo, mods, rev)

    results = []
    for m, p, st, rc in structs:
        sname = st["name"]
        fields = st["fields"]
        start_idx = st["start_idx"]
        end_idx = st["end_idx"]

        # Mask ONLY the structure's own definition block when scanning the defining file `p`
        p_raw = rc_clean_blobs.get(p, "")
        p_lines = p_raw.splitlines()
        masked_lines = [("" if start_idx <= idx_ln < end_idx else ln) for idx_ln, ln in enumerate(p_lines)]
        masked_str = "\n".join(masked_lines)

        destr_files: list[str] = []
        for rmod in rc:
            rp = mods[rmod][0]
            rtxt = rc_clean_blobs.get(rp, "")
            skip_rng = (start_idx, end_idx) if rp == p else None
            if find_struct_destructuring_hits(rtxt, sname, skip_range=skip_rng):
                destr_files.append(rmod.rsplit(".", 1)[-1])

        low_read = []
        zero_count = 0
        for fname, ftype in fields:
            dot_fname = "." + fname
            proj_re = re.compile(rf"(?:\.{re.escape(fname)}{idx.LEAN_ID_END}|{re.escape(sname)}\.{re.escape(fname)}{idx.LEAN_ID_END})")
            readers: list[str] = []
            same_file_readers: list[str] = []
            for rmod in rc:
                rp = mods[rmod][0]
                if rp == p:
                    if dot_fname in masked_str:
                        hit_lines = [idx_ln for idx_ln, ln in enumerate(masked_lines) if dot_fname in ln and proj_re.search(ln)]
                        if hit_lines:
                            readers.append(rmod.rsplit(".", 1)[-1])
                            same_file_readers = _find_enclosing_decls(p_lines, hit_lines)
                else:
                    rtxt = rc_clean_blobs.get(rp, "")
                    if dot_fname in rtxt and proj_re.search(rtxt):
                        readers.append(rmod.rsplit(".", 1)[-1])
            if len(readers) <= args.max_readers:
                if not readers:
                    zero_count += 1
                entry: dict[str, Any] = {
                    "field": fname,
                    "type": ftype,
                    "readers_count": len(readers),
                    "sample_readers": sorted(readers)[:3],
                }
                if same_file_readers:
                    entry["same_file_readers"] = same_file_readers[:3]
                low_read.append(entry)
        if low_read:
            res_item: dict[str, Any] = {
                "structure": sname,
                "mod": m,
                "rev_cone": len(rc),
                "total_fields": len(fields),
                "zero_reader_fields": zero_count,
                "low_reader_fields_count": len(low_read),
                "destructuring_warning_count": len(destr_files),
                "low_reader_fields": low_read[:20],
                "_rc": rc,
            }
            if destr_files:
                res_item["destructuring_warning_files"] = sorted(destr_files)[:5]
            results.append(res_item)

    results.sort(key=lambda r: (-r["zero_reader_fields"], -r["low_reader_fields_count"], r["rev_cone"]))
    top_results = results[: args.limit]
    dep_blobs_cache: dict[str, str] = {}
    for res_item in top_results:
        rc_val = res_item.pop("_rc")
        if args.with_peel:
            _estimate_field_peels(
                res_item["low_reader_fields"],
                res_item["mod"],
                res_item["structure"],
                rc_val,
                mods,
                fwd,
                rev,
                rc_clean_blobs,
                repo,
                args.ref,
                dep_blobs_cache=dep_blobs_cache,
            )
    print(
        json.dumps(
            {
                "indexed_commit": idx.get_meta(conn, "commit")[:10],
                "ref": args.ref,
                "elapsed_s": round(time.monotonic() - t0, 2),
                "scanned_structures": len(structs),
                "structures": top_results,
            },
            indent=2,
        )
    )
    return 0


def cmd_dom_pillars(args: argparse.Namespace) -> int:
    """
    Cooper-Harvey-Kennedy Dominator Tree over Main-reachable modules:
    Surfaces BOTH single-edge pillars AND hidden multi-edge / diamond proof pillars
    dominated by a Main-close host (`host_rev_cone <= max_host_cone`).
    """
    t0 = time.monotonic()
    conn = idx.init_db(args.db)
    mods, fwd, rev = idx.load_graph(conn)

    if "Main" not in mods:
        print(json.dumps({"error": "MISSING_MAIN", "hint": "Main module not in indexed DB"}, indent=2), file=sys.stderr)
        return 2

    # Iterative DFS postorder from Main
    visited: set[str] = {"Main"}
    postorder: list[str] = []
    stack: list[tuple[str, list[str], int]] = [("Main", sorted(d for d in fwd.get("Main", ()) if d in mods), 0)]
    while stack:
        node, nbrs, idx_i = stack[-1]
        if idx_i < len(nbrs):
            nxt = nbrs[idx_i]
            stack[-1] = (node, nbrs, idx_i + 1)
            if nxt not in visited:
                visited.add(nxt)
                stack.append((nxt, sorted(d for d in fwd.get(nxt, ()) if d in mods), 0))
        else:
            postorder.append(node)
            stack.pop()

    rpo_nodes = postorder[::-1]
    n = len(rpo_nodes)
    rpo_idx = {m: i for i, m in enumerate(rpo_nodes)}

    preds: list[list[int]] = [[] for _ in range(n)]
    for i, m in enumerate(rpo_nodes):
        if i == 0:
            continue
        preds[i] = [rpo_idx[p] for p in rev.get(m, ()) if p in rpo_idx]

    idom = [-1] * n
    idom[0] = 0

    def intersect(b1: int, b2: int) -> int:
        f1, f2 = b1, b2
        while f1 != f2:
            while f1 > f2:
                f1 = idom[f1]
            while f2 > f1:
                f2 = idom[f2]
        return f1

    changed = True
    while changed:
        changed = False
        for b in range(1, n):
            processed = [p for p in preds[b] if idom[p] != -1]
            if not processed:
                continue
            new_idom = processed[0]
            for p in processed[1:]:
                new_idom = intersect(p, new_idom)
            if idom[b] != new_idom:
                idom[b] = new_idom
                changed = True

    dom_children: list[list[int]] = [[] for _ in range(n)]
    sub_files = [1] * n
    sub_lines = [mods[m][1] for m in rpo_nodes]
    for i in range(1, n):
        p = idom[i]
        if p >= 0:
            dom_children[p].append(i)
    for i in range(n - 1, 0, -1):
        p = idom[i]
        if p >= 0:
            sub_files[p] += sub_files[i]
            sub_lines[p] += sub_lines[i]

    def dom_subtree_set(root_i: int) -> set[str]:
        s: set[str] = set()
        q = list(dom_children[root_i])
        while q:
            cur = q.pop()
            s.add(rpo_nodes[cur])
            q.extend(dom_children[cur])
        return s

    pillars = []
    for i, host in enumerate(rpo_nodes):
        if i == 0:
            continue
        d_files = sub_files[i] - 1
        d_lines = sub_lines[i] - mods[host][1]
        if d_files < args.min_files or d_lines < args.min_lines:
            continue
        hrc = compute_rev_cone_capped(host, rev, cap=max(args.max_host_cone + 1, 100))
        if hrc > args.max_host_cone:
            continue
        dom_set = dom_subtree_set(i)
        cut_edges = sorted(dep for dep in fwd.get(host, ()) if dep in dom_set)
        best_single_files = 0
        best_single_lines = 0
        for dep in cut_edges:
            sf, sl = compute_exclusive_peel(host, dep, mods, fwd, rev)
            if sl > best_single_lines:
                best_single_lines = sl
                best_single_files = sf
        multi_gain = d_lines - best_single_lines
        if args.only_multi_edge and multi_gain < args.min_multi_gain:
            continue
        pillars.append(
            {
                "host_mod": host,
                "host_rev_cone": hrc,
                "dom_files": d_files,
                "dom_lines": d_lines,
                "cut_edges_count": len(cut_edges),
                "cut_edges_sample": [d.rsplit(".", 1)[-1] for d in cut_edges[:8]],
                "best_single_edge_files": best_single_files,
                "best_single_edge_lines": best_single_lines,
                "multi_edge_gain_lines": multi_gain,
            }
        )

    if args.only_multi_edge:
        pillars.sort(key=lambda x: (-x["multi_edge_gain_lines"], -x["dom_lines"]))
    else:
        pillars.sort(key=lambda x: (-x["dom_lines"], -x["multi_edge_gain_lines"]))

    print(
        json.dumps(
            {
                "indexed_commit": idx.get_meta(conn, "commit")[:10],
                "elapsed_s": round(time.monotonic() - t0, 2),
                "main_reachable_modules": n,
                "total_matching_pillars": len(pillars),
                "pillars": pillars[: args.limit],
            },
            indent=2,
        )
    )
    return 0


def alpha_normalize_sig(params: str, ret: str) -> str:
    """Alpha-normalize binder variable names across parameter binders and return type."""
    p_clean = params.replace("_root_.", "")
    r_clean = ret.replace("_root_.", "")
    # Extract declared binder names from `(a b : T)`, `{a b : T}`, `⦃a : T⦄`, `[inst : C]`
    var_map: dict[str, str] = {}
    counter = 0
    for grp in re.finditer(r"[\(\{⦃\[]([^:\)\}\]]+?):[^)\}\]]+[\)\}⦄\]]", p_clean):
        lhs = grp.group(1).strip()
        for tok in lhs.split():
            if tok and tok != "_" and re.match(r"^[A-Za-z_][A-Za-z0-9_'₀₁₂₃₄₅₆₇₈₉]*$", tok):
                if tok not in var_map:
                    var_map[tok] = f"_v{counter}"
                    counter += 1
    combined = f"{p_clean} : {r_clean}".strip()
    if var_map:
        pat = re.compile(r"\b(" + "|".join(re.escape(k) for k in sorted(var_map, key=len, reverse=True)) + r")\b")
        combined = pat.sub(lambda m: var_map[m.group(1)], combined)
    return " ".join(combined.split())


def cmd_decl_dups(args: argparse.Namespace) -> int:
    """
    Scan declarations across src/ (or --prefix) for alpha-equivalent theorem signatures
    and copy-pasted non-trivial proof bodies across distinct modules.
    """
    t0 = time.monotonic()
    repo = idx.resolve_repo(args.repo, args.db)
    conn = idx.init_db(args.db)
    mods, fwd, rev = idx.load_graph(conn)

    cand_paths: list[str] = []
    for m, (p, lcnt) in mods.items():
        if lcnt < args.min_mod_lines:
            continue
        if args.prefix and not (m.startswith(args.prefix) or p.startswith(args.prefix)):
            continue
        if args.max_cone > 0 and compute_rev_cone_capped(m, rev, cap=args.max_cone) > args.max_cone:
            continue
        cand_paths.append(p)

    blobs = _read_git_blobs(repo, args.ref, cand_paths)
    by_sig: dict[str, list[dict[str, Any]]] = collections.defaultdict(list)
    by_body: dict[str, list[dict[str, Any]]] = collections.defaultdict(list)

    for p in cand_paths:
        txt = blobs.get(p, "")
        if not txt:
            continue
        clean = strip_lean_comments(txt)
        mod = idx.path_to_mod(p)
        for d in _extract_top_decls(clean):
            if d["kind"] not in ("theorem", "lemma", "def"):
                continue
            body_lines = [ln for ln in d["body"].splitlines() if ln.strip()]
            body_norm = " ".join(d["body"].split())
            sig_norm = alpha_normalize_sig(d["params"], d["ret"]) if d["ret"] else ""
            rec = {
                "mod": mod,
                "name": d["name"],
                "kind": d["kind"],
                "line": d["line"],
                "body_lines": len(body_lines),
                "sig_preview": sig_norm[:140],
            }
            if sig_norm and len(sig_norm) >= args.min_sig_len and d["kind"] in ("theorem", "lemma"):
                by_sig[sig_norm].append(rec)
            if len(body_lines) >= args.min_body_lines:
                bhash = hashlib.sha1(body_norm.encode("utf-8")).hexdigest()[:12]
                by_body[bhash].append(rec)

    clusters: list[dict[str, Any]] = []
    seen_mod_sets: set[tuple[str, tuple[str, ...]]] = set()

    def enrich_cluster(match_type: str, key_label: str, items: list[dict[str, Any]]) -> None:
        unique_mods = sorted({x["mod"] for x in items})
        if len(unique_mods) < 2:
            return
        sig_key = (match_type, tuple(unique_mods))
        if sig_key in seen_mod_sets:
            return
        seen_mod_sets.add(sig_key)
        stems = {m.rsplit(".", 1)[-1] for m in unique_mods}
        first_by_mod: dict[str, dict[str, Any]] = {}
        for x in items:
            first_by_mod.setdefault(x["mod"], x)
        copies = []
        max_impact = 0
        for m in unique_mods:
            x = first_by_mod[m]
            importers = rev.get(m, set())
            peel_cnt, peel_lines = 0, 0
            if len(importers) == 1:
                host = next(iter(importers))
                peel_cnt, peel_lines = compute_exclusive_peel(host, m, mods, fwd, rev)
            mlines = mods[m][1] if m in mods else 0
            max_impact = max(max_impact, peel_lines, mlines)
            cone_sz = compute_rev_cone_capped(m, rev, cap=500)
            copies.append(
                {
                    "mod": m,
                    "decl": x["name"],
                    "line": x["line"],
                    "body_lines": x["body_lines"],
                    "rev_direct": len(importers),
                    "rev_cone": cone_sz if cone_sz <= 500 else ">500",
                    "mod_lines": mlines,
                    "exclusive_peel_files": peel_cnt,
                    "exclusive_peel_lines": peel_lines,
                }
            )
        clusters.append(
            {
                "match_type": match_type,
                "key": key_label[:140],
                "module_count": len(unique_mods),
                "different_stems": len(stems) > 1,
                "max_impact_lines": max_impact,
                "copies": copies,
            }
        )

    for sig_norm, items in by_sig.items():
        if len({x["mod"] for x in items}) >= 2:
            enrich_cluster("alpha_sig", sig_norm, items)
    for bhash, items in by_body.items():
        if len({x["mod"] for x in items}) >= 2:
            enrich_cluster("body_hash", f"sha1:{bhash} | {items[0]['sig_preview']}", items)

    clusters.sort(key=lambda c: (-c["max_impact_lines"], -c["module_count"], c["key"]))
    print(
        json.dumps(
            {
                "indexed_commit": idx.get_meta(conn, "commit")[:10],
                "ref": args.ref,
                "scanned_files": len(cand_paths),
                "elapsed_s": round(time.monotonic() - t0, 2),
                "total_clusters": len(clusters),
                "clusters": clusters[: args.limit],
            },
            indent=2,
        )
    )
    return 0


def _split_top_tokens(expr: str) -> list[str]:
    """Split expression by whitespace respecting ()[]{}⟨⟩ nesting."""
    tokens: list[str] = []
    cur: list[str] = []
    depth = 0
    for ch in expr:
        if ch in "([{⟨":
            depth += 1
            cur.append(ch)
        elif ch in ")]}⟩":
            if depth > 0:
                depth -= 1
            cur.append(ch)
        elif ch.isspace() and depth == 0:
            if cur:
                tokens.append("".join(cur))
                cur = []
        else:
            cur.append(ch)
    if cur:
        tokens.append("".join(cur))
    return tokens


def _find_call_arg_occurrences(line: str, proj_re: re.Pattern[str]) -> list[tuple[str, int]]:
    """
    Find `(callee_tok, arg_idx_0_based)` pairs where `proj_re` is passed as an argument
    in a call on `line` (handles `:= fn a b.f`, `exact fn b.f`, and nested `(fn a b.f)`).
    """
    hits: list[tuple[str, int]] = []
    lead_skip = {"have", "let", "obtain", "show", "suffices", "exact", "refine", "apply", "return", "by", "from"}
    op_skip = {"=", "==", ":=", "→", "->", "|", "∧", "∨", "↔", "+", "-", "*", "/"}

    def scan_expr(expr: str) -> None:
        toks = _split_top_tokens(expr.strip())
        while toks and toks[0] in lead_skip:
            toks.pop(0)
        if len(toks) >= 2:
            head = toks[0]
            if head not in op_skip and re.match(r"^@?[A-Za-z_][A-Za-z0-9_.'₀₁₂₃₄₅₆₇₈₉]*$", head):
                for idx_arg, arg in enumerate(toks[1:]):
                    if proj_re.search(arg):
                        hits.append((head, idx_arg))
        for tok in toks:
            if len(tok) >= 2 and ((tok[0] == "(" and tok[-1] == ")") or (tok[0] == "⟨" and tok[-1] == "⟩")):
                inner = tok[1:-1]
                for part in inner.split(",") if tok[0] == "⟨" else [inner]:
                    if proj_re.search(part):
                        scan_expr(part)

    if ":=" in line:
        scan_expr(line.split(":=", 1)[1])
    else:
        scan_expr(line)
    return hits


def _parse_binder_slots(binder_str: str, include_implicit: bool = False) -> list[str]:
    """Expand `(a b : T) {c : U} [inst : C] _ x` into ordered binder variable slots."""
    slots: list[str] = []
    for tok in _split_top_tokens(binder_str.strip()):
        if not tok:
            continue
        if tok.startswith("{") or tok.startswith("⦃") or tok.startswith("["):
            if not include_implicit:
                continue
            inner = tok[1:-1].strip()
            lhs = inner.split(":", 1)[0].strip() if ":" in inner else "_"
            for v in lhs.split():
                if v:
                    slots.append(v)
        elif tok.startswith("("):
            inner = tok[1:-1].strip()
            lhs = inner.split(":", 1)[0].strip() if ":" in inner else inner
            for v in lhs.split():
                if v:
                    slots.append(v)
        else:
            slots.append(tok)
    return slots


def _analyze_callee_discard(callee_decl: dict[str, Any], arg_idx: int, is_at_explicit: bool) -> str | None:
    """Return discard reason if `arg_idx` in `callee_decl` is bound to `_` or unused in its body."""
    explicit_slots = _parse_binder_slots(callee_decl["params"], include_implicit=is_at_explicit)
    body = callee_decl["body"].strip()
    if arg_idx < len(explicit_slots):
        bname = explicit_slots[arg_idx]
        if bname == "_" or bname.startswith("_"):
            return "param_wildcard"
        if re.match(rf"^{idx.LEAN_IDENT}$", bname) and not re.search(rf"{idx.LEAN_ID_PREV}{re.escape(bname)}{idx.LEAN_ID_END}", body):
            return "param_unused"
        return None

    rem_idx = arg_idx - len(explicit_slots)
    # Pattern A: `fun ... => rest`
    mf = re.match(r"^fun\s+(.*?)\s*=>\s*(.*)$", body, re.DOTALL)
    if mf:
        lam_slots = _parse_binder_slots(mf.group(1), include_implicit=is_at_explicit)
        if rem_idx < len(lam_slots):
            bname = lam_slots[rem_idx]
            if bname == "_" or bname.startswith("_"):
                return "fun_wildcard"
            if re.match(rf"^{idx.LEAN_IDENT}$", bname) and not re.search(rf"{idx.LEAN_ID_PREV}{re.escape(bname)}{idx.LEAN_ID_END}", mf.group(2)):
                return "fun_unused"
        return None

    # Pattern B: `by intro ...` / `by\n  intro ...`
    body_lines = [ln.strip() for ln in body.splitlines() if ln.strip()]
    intro_args = ""
    rest_start = 1
    if body_lines:
        mb = re.match(r"^by\s+(?:r?intro)\s+(.+)$", body_lines[0])
        if mb:
            intro_args = mb.group(1)
        elif body_lines[0] == "by" and len(body_lines) >= 2:
            mb2 = re.match(r"^(?:r?intro)\s+(.+)$", body_lines[1])
            if mb2:
                intro_args = mb2.group(1)
                rest_start = 2
    if intro_args:
        # Stop at `;` or `<;>` if inline tactics follow on same line
        intro_head = re.split(r"(?:;|<;>)", intro_args, maxsplit=1)[0]
        intro_slots = _parse_binder_slots(intro_head, include_implicit=True)
        rest_body = "\n".join(body_lines[rest_start:])
        if ";" in intro_args:
            rest_body = intro_args.split(";", 1)[1] + "\n" + rest_body
        if rem_idx < len(intro_slots):
            bname = intro_slots[rem_idx]
            if bname == "_" or bname.startswith("_"):
                return "intro_wildcard"
            if re.match(rf"^{idx.LEAN_IDENT}$", bname) and not re.search(rf"{idx.LEAN_ID_PREV}{re.escape(bname)}{idx.LEAN_ID_END}", rest_body):
                return "intro_unused"
    return None


def cmd_ignored_bundle_args(args: argparse.Namespace) -> int:
    """
    #975/#151 surgical scalpel:
    Find 1-to-N-reader bundle structure fields (plus Main-close direct Published arguments)
    whose consumers immediately discard them via `fun _ ... =>`, `by intro _ ...`, `_` binders,
    or unused named parameters (the exact `flat_tensor_swap_isIso := fun _ _ _` q4 pattern).
    """
    t0 = time.monotonic()
    repo = idx.resolve_repo(args.repo, args.db)
    conn = idx.init_db(args.db)
    mods, fwd, rev = idx.load_graph(conn)

    structs, rc_clean_blobs = _collect_bundle_structures(args, repo, mods, rev)

    # First identify 1..max_readers fields
    candidate_fields: list[dict[str, Any]] = []
    reader_mods_needed: set[str] = set()
    for m, p, st, rc in structs:
        sname = st["name"]
        fields = st["fields"]
        start_idx = st["start_idx"]
        end_idx = st["end_idx"]
        p_lines = rc_clean_blobs.get(p, "").splitlines()
        masked_lines = [("" if start_idx <= idx_ln < end_idx else ln) for idx_ln, ln in enumerate(p_lines)]
        masked_str = "\n".join(masked_lines)

        for fname, ftype in fields:
            dot_fname = "." + fname
            proj_re = re.compile(rf"(?:\.{re.escape(fname)}{idx.LEAN_ID_END}|{re.escape(sname)}\.{re.escape(fname)}{idx.LEAN_ID_END})")
            readers: list[str] = []
            for rmod in rc:
                rp = mods[rmod][0]
                if rp == p:
                    if dot_fname in masked_str and proj_re.search(masked_str):
                        readers.append(rmod)
                else:
                    rtxt = rc_clean_blobs.get(rp, "")
                    if dot_fname in rtxt and proj_re.search(rtxt):
                        readers.append(rmod)
            if 1 <= len(readers) <= args.max_readers:
                reader_mods_needed.update(readers)
                candidate_fields.append(
                    {
                        "structure": sname,
                        "mod": m,
                        "path": p,
                        "rc": rc,
                        "field": fname,
                        "type": ftype,
                        "readers": readers,
                        "masked_lines": masked_lines,
                        "proj_re": proj_re,
                    }
                )

    # Preload 1-hop dependency blobs of reader modules (2-hop loaded lazily only on miss)
    dep_mods_to_load: set[str] = set(reader_mods_needed)
    for rm in reader_mods_needed:
        dep_mods_to_load.update(fwd.get(rm, ()))
    extra_paths = sorted({mods[dm][0] for dm in dep_mods_to_load if dm in mods and mods[dm][0] not in rc_clean_blobs})
    if extra_paths:
        extra_raw = _read_git_blobs(repo, args.ref, extra_paths)
        for ep, etxt in extra_raw.items():
            rc_clean_blobs[ep] = strip_lean_comments(etxt)

    decl_cache: dict[str, list[dict[str, Any]]] = {}

    def get_decls(path: str) -> list[dict[str, Any]]:
        if path not in decl_cache:
            decl_cache[path] = _extract_top_decls(rc_clean_blobs.get(path, ""))
        return decl_cache[path]

    def resolve_callee(rmod: str, callee_tok: str) -> tuple[str, dict[str, Any]] | None:
        cname = callee_tok.lstrip("@").replace("_root_.", "")
        cshort = cname.rsplit(".", 1)[-1]
        search_1 = [rmod] + sorted(fwd.get(rmod, ()))
        for smod in search_1:
            if smod not in mods:
                continue
            sp = mods[smod][0]
            for d in get_decls(sp):
                d_clean = d["name"].replace("_root_.", "")
                if d_clean == cname or d_clean.endswith("." + cname) or d_clean.rsplit(".", 1)[-1] == cshort:
                    return smod, d
        # Lazy 2-hop fallback only when callee not found in 0-hop or 1-hop
        visited_s = set(search_1)
        hop2 = []
        for d1 in fwd.get(rmod, ()):
            for d2 in fwd.get(d1, ()):
                if d2 not in visited_s and d2 in mods:
                    visited_s.add(d2)
                    hop2.append(d2)
        miss_paths = [mods[d2][0] for d2 in hop2 if mods[d2][0] not in rc_clean_blobs]
        if miss_paths:
            for mp, mtxt in _read_git_blobs(repo, args.ref, miss_paths).items():
                rc_clean_blobs[mp] = strip_lean_comments(mtxt)
        for smod in hop2:
            sp = mods[smod][0]
            for d in get_decls(sp):
                d_clean = d["name"].replace("_root_.", "")
                if d_clean == cname or d_clean.endswith("." + cname) or d_clean.rsplit(".", 1)[-1] == cshort:
                    return smod, d
        return None

    local_discard_re = re.compile(r"^(?:have|let)\s+_\s*(?::[^=]*)?:=")
    flagged_fields: list[dict[str, Any]] = []
    by_struct_peel: dict[tuple[str, str], list[dict[str, Any]]] = collections.defaultdict(list)

    for item in candidate_fields:
        proj_re = item["proj_re"]
        p = item["path"]
        total_reads = 0
        discarded_reads: list[dict[str, Any]] = []
        for rmod in item["readers"]:
            rp = mods[rmod][0]
            lines = item["masked_lines"] if rp == p else rc_clean_blobs.get(rp, "").splitlines()
            for idx_ln, ln in enumerate(lines):
                if not proj_re.search(ln):
                    continue
                total_reads += 1
                st_ln = ln.strip()
                if local_discard_re.match(st_ln):
                    discarded_reads.append(
                        {
                            "reader_mod": rmod,
                            "line": idx_ln + 1,
                            "discard_kind": "local_wildcard_bind",
                            "callee": None,
                        }
                    )
                    continue
                for callee_tok, arg_idx in _find_call_arg_occurrences(ln, proj_re):
                    is_at = callee_tok.startswith("@")
                    resolved = resolve_callee(rmod, callee_tok)
                    if not resolved:
                        continue
                    cmod, cdecl = resolved
                    reason = _analyze_callee_discard(cdecl, arg_idx, is_at)
                    if reason:
                        discarded_reads.append(
                            {
                                "reader_mod": rmod,
                                "line": idx_ln + 1,
                                "discard_kind": reason,
                                "callee": cdecl["name"],
                                "callee_mod": cmod.rsplit(".", 1)[-1],
                                "arg_idx": arg_idx,
                            }
                        )
                        break

        if discarded_reads:
            rec = {
                "structure": item["structure"],
                "mod": item["mod"],
                "rev_cone": len(item["rc"]),
                "field": item["field"],
                "type": item["type"],
                "readers_count": len(item["readers"]),
                "total_read_sites": total_reads,
                "discarded_read_sites": len(discarded_reads),
                "all_reads_discarded": len(discarded_reads) >= total_reads,
                "sample_discards": discarded_reads[:5],
            }
            flagged_fields.append(rec)
            by_struct_peel[(item["mod"], item["structure"])].append(rec)

    if args.with_peel and flagged_fields:
        struct_rc_map = {(m, st["name"]): rc for m, _, st, rc in structs}
        dep_blobs_cache: dict[str, str] = {}
        # Estimate peel across unique (mod, structure) for candidates up to max(limit*2, 40)
        by_struct_top: dict[tuple[str, str], list[dict[str, Any]]] = collections.defaultdict(list)
        for r in flagged_fields[: max(args.limit * 3, 60)]:
            by_struct_top[(r["mod"], r["structure"])].append(r)
        for (m, sname_k), flist in by_struct_top.items():
            rc = struct_rc_map[(m, sname_k)]
            _estimate_field_peels(
                flist, m, sname_k, rc, mods, fwd, rev, rc_clean_blobs, repo, args.ref, dep_blobs_cache=dep_blobs_cache
            )

    flagged_fields.sort(
        key=lambda r: (
            not r["all_reads_discarded"],
            -r.get("estimated_peel_lines", 0),
            r["readers_count"],
            r["rev_cone"],
        )
    )

    # Also find Main-close direct Published/Hypotheses wildcard/unused binders (`fun _` / `intro _`)
    direct_discarded: list[dict[str, Any]] = []
    pg_dir = subprocess.run(
        ["git", "-c", "core.quotepath=false", "grep", "-l", "-E", r"(fun|intro)[[:space:]]+_|[(]_[[:space:]]*:", args.ref, "--", "src/"],
        cwd=str(repo),
        capture_output=True,
        text=True,
        encoding="utf-8",
        errors="replace",
    )
    path_to_mod = {p_it: m_it for m_it, (p_it, _) in mods.items()}
    close_paths: list[str] = []
    for ln in pg_dir.stdout.splitlines():
        sp = parse_git_grep_path(ln, args.ref)
        m_it = path_to_mod.get(sp)
        if not m_it:
            continue
        if compute_rev_cone_capped(m_it, rev, cap=41) <= 40:
            close_paths.append(sp)
    close_blobs = _read_git_blobs(repo, args.ref, close_paths)
    pub_arg_re = re.compile(r"(GlobalTheory\.Published\.[A-Za-z0-9_.'₀₁₂₃₄₅₆₇₈₉]+|[A-Za-z0-9_.'₀₁₂₃₄₅₆₇₈₉]*Hypotheses[A-Za-z0-9_.'₀₁₂₃₄₅₆₇₈₉]*)")
    for sp in sorted(close_paths):
        raw_txt = close_blobs.get(sp, "")
        if not raw_txt:
            continue
        for d in _extract_top_decls(strip_lean_comments(raw_txt)):
            if "Published." not in d["sig_raw"] and "Hypotheses" not in d["sig_raw"]:
                continue
            explicit_slots = _parse_binder_slots(d["params"], include_implicit=False)
            # Check explicit binders of form `(_ : Pub)` or unused `(h : Pub)`
            checked = False
            for idx_b, btok in enumerate(explicit_slots):
                if btok == "_" or btok.startswith("_"):
                    # Verify binder actually sits near a Published/Hypotheses type
                    if pub_arg_re.search(d["params"]):
                        direct_discarded.append(
                            {
                                "mod": path_to_mod[sp],
                                "decl": d["name"],
                                "line": d["line"],
                                "discard_kind": "explicit_wildcard_binder",
                                "arg_idx": idx_b,
                            }
                        )
                        checked = True
                        break
            if checked:
                continue
            # Check arrow `Pub → ...` with `fun _ ...` or `by intro _ ...`
            if "→" in d["ret"] or "->" in d["ret"]:
                arrows = re.split(r"(?:→|->)", d["ret"])
                for idx_a, part in enumerate(arrows[:-1]):
                    if pub_arg_re.search(part):
                        reason = _analyze_callee_discard(d, len(explicit_slots) + idx_a, is_at_explicit=False)
                        if reason:
                            direct_discarded.append(
                                {
                                    "mod": path_to_mod[sp],
                                    "decl": d["name"],
                                    "line": d["line"],
                                    "discard_kind": reason,
                                    "arg_idx": len(explicit_slots) + idx_a,
                                    "arg_type": part.strip()[:80],
                                }
                            )
                            break

    print(
        json.dumps(
            {
                "indexed_commit": idx.get_meta(conn, "commit")[:10],
                "ref": args.ref,
                "elapsed_s": round(time.monotonic() - t0, 2),
                "scanned_structures": len(structs),
                "ignored_bundle_fields_count": len(flagged_fields),
                "ignored_bundle_fields": flagged_fields[: args.limit],
                "direct_discarded_decls_count": len(direct_discarded),
                "direct_discarded_decls": direct_discarded[: args.limit],
            },
            indent=2,
        )
    )
    return 0


def _strip_outer_parens(s: str) -> str:
    cur = s.strip()
    while len(cur) >= 2 and cur[0] == "(" and cur[-1] == ")":
        depth = 0
        matched = True
        for idx_c, ch in enumerate(cur):
            if ch in "([{":
                depth += 1
            elif ch in ")]}":
                depth -= 1
                if depth == 0 and idx_c < len(cur) - 1:
                    matched = False
                    break
        if matched and depth == 0:
            cur = cur[1:-1].strip()
        else:
            break
    return cur


def _is_syntactic_trivial_body(body_raw: str) -> bool:
    """Return True if a Lean def/abbrev body reduces syntactically through fun/forall to True/trivial."""
    cur = _strip_outer_parens(" ".join(body_raw.split()))
    for _ in range(10):
        if cur in ("True", "trivial", "by trivial", "by exact trivial"):
            return True
        if re.fullmatch(r"True(?:\s*∧\s*True)+", cur):
            return True
        if re.match(r"^fun(?:\s|\(|{|\[|⦃)", cur):
            depth = 0
            split_at = -1
            for k in range(3, len(cur) - 1):
                ch = cur[k]
                if ch in "([{":
                    depth += 1
                elif ch in ")]}":
                    if depth > 0:
                        depth -= 1
                elif depth == 0 and cur[k : k + 2] == "=>":
                    split_at = k + 2
                    break
            if split_at != -1:
                cur = _strip_outer_parens(cur[split_at:].strip())
                continue
        if cur.startswith("∀"):
            depth = 0
            split_at = -1
            for k in range(1, len(cur)):
                ch = cur[k]
                if ch in "([{":
                    depth += 1
                elif ch in ")]}":
                    if depth > 0:
                        depth -= 1
                elif depth == 0 and cur[k] == ",":
                    split_at = k + 1
                    break
            if split_at != -1:
                cur = _strip_outer_parens(cur[split_at:].strip())
                continue
        break
    return False


def _find_unused_seed_binders(params: str, body: str, seed_short: str) -> list[str]:
    """Return binder names of type mentioning `seed_short` that are wildcards or unused in `body`."""
    if not params or not seed_short or not re.search(rf"{idx.LEAN_ID_PREV}{re.escape(seed_short)}{idx.LEAN_ID_END}", params):
        return []
    body_tokens = set(idx._LEAN_IDENT_RE.findall(body))
    unused: list[str] = []
    n = len(params)
    i = 0
    pairs = {"(": ")", "{": "}", "⦃": "⦄", "[": "]"}
    while i < n:
        ch = params[i]
        if ch in pairs:
            close_ch = pairs[ch]
            depth = 1
            j = i + 1
            while j < n and depth > 0:
                if params[j] == ch:
                    depth += 1
                elif params[j] == close_ch:
                    depth -= 1
                j += 1
            grp = params[i + 1 : j - 1].strip() if depth == 0 else params[i + 1 :].strip()
            # Find top-level ':' inside grp
            d2 = 0
            cpos = -1
            for pos, gch in enumerate(grp):
                if gch in "([{⦃":
                    d2 += 1
                elif gch in ")]}⦄":
                    if d2 > 0:
                        d2 -= 1
                elif gch == ":" and d2 == 0 and grp[pos : pos + 2] != ":=":
                    cpos = pos
                    break
            if cpos != -1:
                lhs = grp[:cpos].strip()
                rhs = grp[cpos + 1 :].strip()
                if re.search(rf"{idx.LEAN_ID_PREV}{re.escape(seed_short)}{idx.LEAN_ID_END}", rhs):
                    vars_toks = [t for t in lhs.split() if re.match(rf"^{idx.LEAN_IDENT}$", t)]
                    if not vars_toks:
                        unused.append(f"anon:{rhs[:40]}")
                    else:
                        for vt in vars_toks:
                            if vt == "_" or vt.startswith("_") or vt not in body_tokens:
                                unused.append(vt)
            i = j
        else:
            i += 1
    return unused


def _body_without_header(clean_txt: str) -> tuple[list[str], int]:
    lines = clean_txt.splitlines()
    hdr_end = 0
    for li, ln in enumerate(lines):
        st = ln.strip()
        if not st or st == "module" or st.startswith("prelude") or idx.IMPORT_RE.match(st):
            hdr_end = li + 1
        else:
            break
    return lines, hdr_end


def _rev_cone_full(seed: str, rev: dict[str, set[str]]) -> set[str]:
    cone = {seed}
    q = [seed]
    while q:
        cur = q.pop()
        for imp in rev.get(cur, ()):
            if imp not in cone:
                cone.add(imp)
                q.append(imp)
    return cone


def cmd_vacuous_defs(args: argparse.Namespace) -> int:
    """
    Axis #10 (#466): Fast whole-repo syntactic scan for vacuous Prop definitions (`:= True` /
    `fun _ => True` / `trivial`), vacuous Prop structures, and 0-field non-Prop placeholders,
    plus syntactic downstream unused-binder and only-trivial-instantiation checks.
    """
    t0 = time.monotonic()
    repo = idx.resolve_repo(args.repo, args.db)
    conn = idx.init_db(args.db)
    mods, fwd, rev = idx.load_graph(conn)
    path_to_mod = {p: m for m, (p, _) in mods.items()}
    main_reach = idx.reachable_from(["Main"], mods, fwd, set()) if args.main_only and "Main" in mods else None

    grep_patterns = [
        r"(def|abbrev)[[:space:]].*:=[[:space:]]*(fun[[:space:]].*=>[[:space:]]*)?(True|trivial|∀.*True|True[[:space:]]*∧)([[:space:]]|$)",
        r"^[[:space:]]*((fun[[:space:]].*=>[[:space:]]*)?(True|trivial)|∀.*True|True[[:space:]]*∧)[[:space:]]*$",
        r"^[[:space:]]*((public|private|protected|noncomputable|meta)[[:space:]]+)*structure[[:space:]]+",
    ]
    cand_paths_set: set[str] = set()
    for pat in grep_patterns:
        pg = subprocess.run(
            ["git", "-c", "core.quotepath=false", "grep", "-l", "-E", pat, args.ref, "--", "src/"],
            cwd=str(repo),
            capture_output=True,
            text=True,
            encoding="utf-8",
            errors="replace",
        )
        for ln in pg.stdout.splitlines():
            sp = parse_git_grep_path(ln, args.ref)
            if sp.endswith(".lean"):
                cand_paths_set.add(sp)

    filtered_paths: list[str] = []
    for sp in sorted(cand_paths_set):
        m = path_to_mod.get(sp)
        if not m:
            continue
        if main_reach is not None and m not in main_reach:
            continue
        if args.max_cone > 0 and compute_rev_cone_capped(m, rev, cap=args.max_cone + 1) > args.max_cone:
            continue
        filtered_paths.append(sp)

    cand_blobs = _read_git_blobs(repo, args.ref, filtered_paths)
    clean_cache: dict[str, str] = {}
    decls_cache: dict[str, list[dict[str, Any]]] = {}

    raw_hits: list[dict[str, Any]] = []
    for sp in filtered_paths:
        raw_txt = cand_blobs.get(sp, "")
        if not raw_txt:
            continue
        clean = strip_lean_comments(raw_txt)
        clean_cache[sp] = clean
        m = path_to_mod[sp]

        decls = _extract_top_decls(clean)
        decls_cache[sp] = decls
        for d in decls:
            if d["kind"] not in ("def", "abbrev") or d["name"] == "_":
                continue
            if _is_syntactic_trivial_body(d["body"]):
                raw_hits.append(
                    {
                        "category": "trivial_prop_def",
                        "kind": d["kind"],
                        "mod": m,
                        "path": sp,
                        "name": d["name"],
                        "short_name": d["name"].rsplit(".", 1)[-1],
                        "line": d["line"],
                        "start_idx": d["start_idx"],
                        "end_idx": d["end_idx"],
                        "signature": f"{d['kind']} {d['name']} {d['sig_raw']}"[:140],
                    }
                )

        for st in parse_lean_structures(clean, include_empty=True):
            if st["extends"]:
                continue
            sname = st["name"]
            if st["is_prop"] and all(_is_syntactic_trivial_body(ft) for _, ft in st["fields"]):
                raw_hits.append(
                    {
                        "category": "vacuous_prop_struct",
                        "kind": "structure",
                        "mod": m,
                        "path": sp,
                        "name": sname,
                        "short_name": sname.rsplit(".", 1)[-1],
                        "line": st["start_idx"] + 1,
                        "start_idx": st["start_idx"],
                        "end_idx": st["end_idx"],
                        "field_count": len(st["fields"]),
                        "signature": f"structure {sname} : Prop ({len(st['fields'])} trivial fields)",
                    }
                )
            elif (not st["is_prop"]) and len(st["fields"]) == 0:
                raw_hits.append(
                    {
                        "category": "zero_field_placeholder",
                        "kind": "structure",
                        "mod": m,
                        "path": sp,
                        "name": sname,
                        "short_name": sname.rsplit(".", 1)[-1],
                        "line": st["start_idx"] + 1,
                        "start_idx": st["start_idx"],
                        "end_idx": st["end_idx"],
                        "field_count": 0,
                        "signature": f"structure {sname} (0 fields, non-Prop)",
                    }
                )

    # Gather downstream scan blobs for hits (up to cone size 2500 cleanly; larger falls back to direct rev importers)
    rc_by_mod: dict[str, set[str]] = {}
    scan_mods_needed: set[str] = set()
    for h in raw_hits:
        hm = h["mod"]
        if hm not in rc_by_mod:
            rc = _rev_cone_full(hm, rev)
            rc_by_mod[hm] = rc
        rc = rc_by_mod[hm]
        h["rev_cone"] = len(rc)
        if len(rc) <= 2500:
            scan_mods_needed.update(rc)
        else:
            scan_mods_needed.add(hm)
            scan_mods_needed.update(rev.get(hm, ()))

    miss_scan = sorted({mods[sm][0] for sm in scan_mods_needed if sm in mods and mods[sm][0] not in clean_cache})
    if miss_scan:
        for mp, mtxt in _read_git_blobs(repo, args.ref, miss_scan).items():
            clean_cache[mp] = strip_lean_comments(mtxt)

    all_trivial_seeds = {h["short_name"] for h in raw_hits if h["category"] == "trivial_prop_def" and len(h["short_name"]) >= 3}
    kw_non_callee = {"def", "theorem", "lemma", "abbrev", "structure", "inductive", "class", "by", "exact", "apply", "refine", "fun", "∀", "return", "show", "have", "let", "if", "then", "else", "match", "with"}

    results: list[dict[str, Any]] = []
    for h in raw_hits:
        hm = h["mod"]
        hp = h["path"]
        short = h["short_name"]
        rc = rc_by_mod[hm]
        truncated = len(rc) > 2500
        scan_set = ({hm} | set(rev.get(hm, ()))) if truncated else rc
        tok_re = re.compile(rf"{idx.LEAN_ID_PREV}{re.escape(short)}{idx.LEAN_ID_END}")

        ref_mods: list[str] = []
        unused_callers: list[dict[str, Any]] = []
        callee_candidates: dict[str, str] = {}

        for rm in sorted(scan_set):
            if rm not in mods:
                continue
            rp = mods[rm][0]
            rtxt = clean_cache.get(rp, "")
            if short not in rtxt:
                continue
            rlines, hdr_end = _body_without_header(rtxt)
            hit_idxs: list[int] = []
            for li in range(hdr_end, len(rlines)):
                if rp == hp and h["start_idx"] <= li < h["end_idx"]:
                    continue
                if short in rlines[li] and tok_re.search(rlines[li]):
                    hit_idxs.append(li)
            if not hit_idxs:
                continue
            ref_mods.append(rm)
            if rp not in decls_cache:
                decls_cache[rp] = _extract_top_decls(rtxt)
            for d in decls_cache[rp]:
                ub = _find_unused_seed_binders(d["params"], d["body"], short)
                if ub:
                    unused_callers.append({"mod": rm.rsplit(".", 1)[-1], "decl": d["name"], "line": d["line"], "unused_binders": ub[:3]})
            if h["category"] == "trivial_prop_def" and len(scan_set) <= 250 and len(ref_mods) <= 80:
                for li in hit_idxs[:10]:
                    ln = rlines[li]
                    for m_call in re.finditer(rf"(?=({idx.LEAN_QUAL_IDENT})\s+(?:(?![:=]).)*?{idx.LEAN_ID_PREV}{re.escape(short)}{idx.LEAN_ID_END})", ln):
                        ctok = m_call.group(1).rsplit(".", 1)[-1]
                        if ctok not in kw_non_callee and ctok != short and len(ctok) >= 4:
                            callee_candidates.setdefault(ctok, rm)

        only_trivial_params: list[dict[str, Any]] = []
        if callee_candidates and all_trivial_seeds:
            seed_alt = "|".join(re.escape(s) for s in sorted(all_trivial_seeds, key=len, reverse=True))
            trivial_arg_re = re.compile(rf"(?:{idx.LEAN_ID_PREV}(?:{seed_alt}|trivial){idx.LEAN_ID_END}|fun\s+[^\n]*=>\s*True)")
            for ctok, host_rm in list(callee_candidates.items())[:8]:
                c_mod = ""
                for cand_m in [host_rm] + sorted(fwd.get(host_rm, ())):
                    if cand_m not in mods:
                        continue
                    cp = mods[cand_m][0]
                    if cp not in clean_cache:
                        raw_c = _read_git_blobs(repo, args.ref, [cp])
                        clean_cache[cp] = strip_lean_comments(raw_c.get(cp, ""))
                    c_txt = clean_cache[cp]
                    if re.search(rf"^\s{{0,2}}(?:def|abbrev|inductive|structure)\s+(?:{idx.LEAN_QUAL_IDENT}\.)?{re.escape(ctok)}{idx.LEAN_ID_END}", c_txt, re.MULTILINE):
                        c_mod = cand_m
                        break
                if not c_mod:
                    continue
                c_rc = _rev_cone_full(c_mod, rev)
                if len(c_rc) > 150:
                    continue
                c_miss = [mods[x][0] for x in c_rc if x in mods and mods[x][0] not in clean_cache]
                if c_miss:
                    for mp, mtxt in _read_git_blobs(repo, args.ref, c_miss).items():
                        clean_cache[mp] = strip_lean_comments(mtxt)
                c_pat = re.compile(rf"{idx.LEAN_ID_PREV}{re.escape(ctok)}{idx.LEAN_ID_END}")
                call_lines: list[str] = []
                all_triv = True
                c_def_re = re.compile(
                    rf"^\s{{0,2}}(?:@\[[^\]]*\]\s*)*(?:(?:public|private|protected|noncomputable|unsafe|partial|scoped|local|meta)\s+)*"
                    rf"(?:def|abbrev|inductive|structure|class|theorem|lemma)\s+(?:{idx.LEAN_QUAL_IDENT}\.)?{re.escape(ctok)}{idx.LEAN_ID_END}"
                )
                for x in c_rc:
                    if x not in mods:
                        continue
                    xlines, xhdr = _body_without_header(clean_cache.get(mods[x][0], ""))
                    for xli in range(xhdr, len(xlines)):
                        xln = xlines[xli]
                        if ctok in xln and c_pat.search(xln):
                            if c_def_re.match(xln):
                                continue
                            check_part = xln.split(":=", 1)[1] if (":=" in xln and re.match(r"^\s*(?:theorem|lemma|def|abbrev)\b", xln)) else xln
                            if not c_pat.search(check_part):
                                continue
                            call_lines.append(check_part)
                            if not trivial_arg_re.search(check_part):
                                all_triv = False
                                break
                    if not all_triv:
                        break
                if all_triv and call_lines:
                    only_trivial_params.append({"callee_mod": c_mod.rsplit(".", 1)[-1], "callee": ctok, "call_sites_checked": len(call_lines)})
                    if len(only_trivial_params) >= 5:
                        break

        entry: dict[str, Any] = {
            "category": h["category"],
            "kind": h["kind"],
            "mod": hm,
            "path": hp,
            "name": h["name"],
            "line": h["line"],
            "rev_cone": h["rev_cone"],
            "ref_files_count": len(ref_mods),
            "is_unreferenced": len(ref_mods) == 0,
            "unused_binder_callers_count": len(unused_callers),
            "signature": h["signature"],
        }
        if truncated:
            entry["ref_scan_note"] = "rev_cone > 2500; scanned same-file + direct importers only"
        if unused_callers:
            entry["unused_binder_callers_sample"] = unused_callers[:8]
        if only_trivial_params:
            entry["only_trivial_param_candidates"] = only_trivial_params
        results.append(entry)

    results.sort(key=lambda r: (not r["is_unreferenced"], -r["unused_binder_callers_count"], r["ref_files_count"], r["rev_cone"], r["path"]))
    summary = collections.Counter(r["category"] for r in results)
    unreferenced_cnt = sum(1 for r in results if r["is_unreferenced"])

    print(
        json.dumps(
            {
                "indexed_commit": idx.get_meta(conn, "commit")[:10],
                "ref": args.ref,
                "elapsed_s": round(time.monotonic() - t0, 2),
                "total_hits": len(results),
                "unreferenced_count": unreferenced_cnt,
                "summary_by_category": dict(sorted(summary.items())),
                "hits": results[: args.limit],
                "syntactic_caveat": "Purely syntactic shape check: misses multi-hop whnf-reducible Props and provably-true Props not literally reducing to True/trivial.",
            },
            indent=2,
        )
    )
    return 0


_SKIP_IMPLICIT_ATTRS = {
    "simp", "ext", "coe", "norm_cast", "aesop", "fun_prop", "measurability",
    "continuity", "gcongr", "positivity", "instance", "reducible", "scoped",
    "macro", "elab", "syntax", "match_pattern", "refl", "symm", "trans",
}


def _extract_other_top_decls(clean_text: str) -> list[dict[str, Any]]:
    """Extract top-level inductive/class/opaque/axiom/alias declarations with line spans."""
    hdr_re = re.compile(
        rf"^(\s{{0,2}})(?:@\[[^\]]*\]\s*)*"
        rf"((?:(?:public|private|protected|noncomputable|unsafe|partial|scoped|local|meta)\s+)*)"
        rf"(inductive|class|opaque|axiom|alias)\s+({idx.LEAN_QUAL_IDENT}){idx.LEAN_ID_END}"
    )
    stop_re = re.compile(
        r"^\s{0,2}(?:@\[[^\]]*\]\s*)*(?:(?:public|private|protected|noncomputable|unsafe|partial|scoped|local|meta)\s+)*"
        r"(?:theorem|lemma|def|abbrev|instance|structure|inductive|class|opaque|axiom|alias|section|end|namespace|variable|open|set_option|attribute)\b"
    )
    lines = clean_text.splitlines()
    n = len(lines)
    out: list[dict[str, Any]] = []
    i = 0
    while i < n:
        m = hdr_re.match(lines[i])
        if not m:
            i += 1
            continue
        hdr_indent = len(m.group(1))
        mods_kw, kind, name = m.group(2), m.group(3), m.group(4)
        j = i + 1
        while j < n:
            ln = lines[j]
            st = ln.strip()
            if st and (len(ln) - len(ln.lstrip(" "))) <= hdr_indent and stop_re.match(st):
                break
            j += 1
        out.append(
            {
                "kind": kind,
                "name": name,
                "line": i + 1,
                "start_idx": i,
                "end_idx": j,
                "is_private": bool(re.search(r"\bprivate\b", mods_kw)),
                "attrs": _extract_attr_names(lines, i),
            }
        )
        i = j
    return out


def cmd_unreferenced_decls(args: argparse.Namespace) -> int:
    """
    Axis #11 (#466): Fast whole-project syntactic scanner for top-level declarations and
    non-instance modules with 0 external AND 0 same-file references.
    """
    t0 = time.monotonic()
    repo = idx.resolve_repo(args.repo, args.db)
    conn = idx.init_db(args.db)
    mods, fwd, rev = idx.load_graph(conn)

    pref = args.prefix.strip().replace("\\", "/")
    pref_mod = idx.path_to_mod(pref) if (pref.startswith("src/") or "/" in pref or pref.endswith(".lean")) else pref.strip(".")
    max_cone = (10 if not pref_mod else 0) if args.max_cone < 0 else args.max_cone
    main_reach = idx.reachable_from(["Main"], mods, fwd, set()) if args.main_only and "Main" in mods else None
    protected_mods = {"Main"} | {
        r.strip() for r in getattr(args, "keep_roots", "").split(",") if r.strip()
    }

    targets: list[str] = []
    for m, (p, _) in mods.items():
        if m in protected_mods:
            continue
        if main_reach is not None and m not in main_reach:
            continue
        if pref_mod and not (m == pref_mod or m.startswith(pref_mod + ".") or p.startswith(pref)):
            continue
        if max_cone > 0 and compute_rev_cone_capped(m, rev, cap=max_cone + 1) > max_cone:
            continue
        targets.append(m)

    targets.sort()
    rc_by_target: dict[str, set[str]] = {}
    all_needed_mods: set[str] = set(targets)
    for m in targets:
        rc = _rev_cone_full(m, rev)
        rc_by_target[m] = rc
        all_needed_mods.update(rc)

    needed_paths = sorted({mods[m][0] for m in all_needed_mods if m in mods})
    raw_blobs = _read_git_blobs(repo, args.ref, needed_paths)
    clean_by_mod: dict[str, str] = {}
    body_lines_by_mod: dict[str, tuple[list[str], int]] = {}
    tokens_by_mod: dict[str, set[str]] = {}

    for m in all_needed_mods:
        if m not in mods:
            continue
        raw = raw_blobs.get(mods[m][0], "")
        if not raw:
            continue
        clean = strip_lean_comments(raw)
        clean_by_mod[m] = clean
        lines, hdr_end = _body_without_header(clean)
        body_lines_by_mod[m] = (lines, hdr_end)
        tokens_by_mod[m] = set(idx._LEAN_IDENT_RE.findall("\n".join(lines[hdr_end:])))

    unreferenced_decls: list[dict[str, Any]] = []
    dead_module_candidates: list[dict[str, Any]] = []

    for m in targets:
        clean = clean_by_mod.get(m, "")
        if not clean:
            continue
        lines, hdr_end = body_lines_by_mod[m]
        rc = rc_by_target[m]
        ext_mods = [im for im in rc if im != m and im in tokens_by_mod]

        cands: list[dict[str, Any]] = []
        for d in _extract_top_decls(clean):
            if d["kind"] in ("theorem", "lemma", "def", "abbrev"):
                cands.append(d)
        for st in parse_lean_structures(clean, include_empty=True):
            cands.append(
                {
                    "kind": "structure",
                    "name": st["name"],
                    "line": st["start_idx"] + 1,
                    "start_idx": st["start_idx"],
                    "end_idx": st["end_idx"],
                    "is_private": st["is_private"],
                    "attrs": st["attrs"],
                }
            )
        cands.extend(_extract_other_top_decls(clean))

        exported_count = 0
        ext_live_count = 0
        for d in cands:
            name = d["name"]
            short = name.rsplit(".", 1)[-1]
            if not name or name == "_" or len(short) < 2:
                continue
            attrs_set = set(d.get("attrs", ()))
            if not d.get("is_private"):
                exported_count += 1
            has_ext = any(short in tokens_by_mod[im] for im in ext_mods)
            if not d.get("is_private") and has_ext:
                ext_live_count += 1

            if d.get("is_private") and not args.include_private:
                continue
            if attrs_set & _SKIP_IMPLICIT_ATTRS:
                continue
            if has_ext:
                continue

            start_idx, end_idx = d["start_idx"], d["end_idx"]
            body_span = max(1, end_idx - start_idx)
            if body_span < args.min_body_lines:
                continue

            same_file_hit = False
            pat = re.compile(rf"{idx.LEAN_ID_PREV}{re.escape(short)}{idx.LEAN_ID_END}")
            for li in range(hdr_end, len(lines)):
                if start_idx <= li < end_idx:
                    continue
                if short in lines[li] and pat.search(lines[li]):
                    same_file_hit = True
                    break
            if not same_file_hit:
                unreferenced_decls.append(
                    {
                        "mod": m,
                        "path": mods[m][0],
                        "kind": d["kind"],
                        "name": name,
                        "line": d["line"],
                        "body_lines": body_span,
                        "rev_cone": len(rc),
                    }
                )

        if exported_count >= 1 and ext_live_count == 0 and m not in redline_mods:
            _, has_implicit = idx.extract_exported_decls(clean)
            if not has_implicit:
                dead_module_candidates.append(
                    {
                        "mod": m,
                        "path": mods[m][0],
                        "lines": mods[m][1],
                        "direct_importers": sorted(rev.get(m, ()))[:10],
                        "direct_importers_count": len(rev.get(m, ())),
                        "exported_decls": exported_count,
                    }
                )

    unreferenced_decls.sort(key=lambda r: (-r["body_lines"], r["rev_cone"], r["mod"], r["line"]))
    dead_module_candidates.sort(key=lambda r: (-r["lines"], r["direct_importers_count"], r["mod"]))

    print(
        json.dumps(
            {
                "indexed_commit": idx.get_meta(conn, "commit")[:10],
                "ref": args.ref,
                "elapsed_s": round(time.monotonic() - t0, 2),
                "scanned_modules": len(targets),
                "unreferenced_decls_count": len(unreferenced_decls),
                "dead_module_candidates_count": len(dead_module_candidates),
                "dead_module_candidates": dead_module_candidates[:20],
                "unreferenced_decls": unreferenced_decls[: args.limit],
                "syntactic_caveat": "Purely syntactic token check: always verify with `lake build` before deleting (handles coercions, macros, typeclasses, or shadowed names).",
            },
            indent=2,
        )
    )
    return 0


def main() -> int:
    idx.ensure_utf8_stdio()
    ap = argparse.ArgumentParser(description="SQLite-backed Big-PR opportunity hunter for continuous local search.")
    ap.add_argument("--repo", type=Path, default=None, help="Path to local Lean 4 git repository (defaults to indexed repo_root or cwd)")
    ap.add_argument("--db", type=Path, default=Path.home() / ".cache" / "lean-import-index" / "import_index.db")
    ap.add_argument("--ref", default="origin/main")
    sub = ap.add_subparsers(dest="cmd", required=True)

    p_cp = sub.add_parser("chokepoints", help="Find hosts guarding giant exclusive subtrees")
    p_cp.add_argument("--min-lines", type=int, default=3000)
    p_cp.add_argument("--min-files", type=int, default=5)
    p_cp.add_argument("--max-cone", type=int, default=0, help="Optional max host reverse cone size (0 = unlimited)")
    p_cp.add_argument("--limit", type=int, default=30)

    p_pd = sub.add_parser("published-dups", help="Find multiply-proved GlobalTheory.Published.* theorems")
    p_pd.add_argument("--pattern", default=r"GlobalTheory\.Published\.")
    p_pd.add_argument("--include-wrappers", action="store_true", help="Also include hypothesis-forwarding wrappers")
    p_pd.add_argument("--limit", type=int, default=40)

    p_ni = sub.add_parser("neg-instances", help="Rank attribute [-instance] workarounds (#599)")
    p_ni.add_argument("--limit", type=int, default=30)

    p_ds = sub.add_parser("duplicate-stems", help="Pure-SQLite twin-directory & duplicate-module-basename radar")
    p_ds.add_argument("--min-shared", type=int, default=2, help="Min shared stems for twin directories")
    p_ds.add_argument("--min-lines", type=int, default=1500, help="Min lines or peel impact to report")
    p_ds.add_argument("--limit", type=int, default=25)

    p_hp = sub.add_parser("heavy-pillars", help="#975 scalpel: rank >=10kL exclusive proof pillars feeding Main-close hosts")
    p_hp.add_argument("--min-lines", type=int, default=10000)
    p_hp.add_argument("--min-files", type=int, default=15)
    p_hp.add_argument("--max-host-cone", type=int, default=35)
    p_hp.add_argument("--limit", type=int, default=40)

    p_uf = sub.add_parser("unused-fields", help="#398/#975 scalpel: find 0-reader or 1-reader fields in Main-reaching bundle structures")
    p_uf.add_argument("--min-fields", type=int, default=5)
    p_uf.add_argument("--max-cone", type=int, default=400)
    p_uf.add_argument("--max-readers", type=int, default=0, help="Report fields with <= N downstream readers (0 or 1)")
    p_uf.add_argument("--struct-filter", default=DEFAULT_STRUCT_FILTER, help="Comma-separated substrings matched against structure OR module name (empty = all)")
    p_uf.add_argument("--name-filter", default="", help="Optional comma-separated module-name substrings")
    p_uf.add_argument("--main-only", action=argparse.BooleanOptionalAction, default=True, help="Restrict to Main-reaching structures")
    p_uf.add_argument("--with-peel", action=argparse.BooleanOptionalAction, default=True, help="Estimate exclusive peel impact for low-reader fields")
    p_uf.add_argument("--limit", type=int, default=25)

    p_dp = sub.add_parser("dom-pillars", help="Exact CHK Dominator-Tree multi-edge/diamond pillars feeding Main-close hosts")
    p_dp.add_argument("--min-lines", type=int, default=10000)
    p_dp.add_argument("--min-files", type=int, default=15)
    p_dp.add_argument("--max-host-cone", type=int, default=35)
    p_dp.add_argument("--only-multi-edge", action="store_true", help="Keep only pillars where multi-edge dominance beats best single edge")
    p_dp.add_argument("--min-multi-gain", type=int, default=1000, help="Min multi_edge_gain_lines when --only-multi-edge is set")
    p_dp.add_argument("--limit", type=int, default=30)

    p_dd = sub.add_parser("decl-dups", help="Declaration-level alpha-normalized signature & proof-body dedup")
    p_dd.add_argument("--prefix", default="", help="Optional module or path prefix filter (e.g. Development.WeilBound)")
    p_dd.add_argument("--max-cone", type=int, default=0, help="Optional max reverse cone filter (0 = unlimited)")
    p_dd.add_argument("--min-mod-lines", type=int, default=20, help="Skip modules smaller than N lines")
    p_dd.add_argument("--min-body-lines", type=int, default=15, help="Min non-blank body lines for proof-body hash matching")
    p_dd.add_argument("--min-sig-len", type=int, default=30, help="Min normalized signature length for alpha-sig matching")
    p_dd.add_argument("--limit", type=int, default=30)

    p_iba = sub.add_parser("ignored-bundle-args", help="#975/#151 scalpel: find bundle fields & Published args discarded via `fun _`/`intro _`")
    p_iba.add_argument("--min-fields", type=int, default=3)
    p_iba.add_argument("--max-cone", type=int, default=400)
    p_iba.add_argument("--max-readers", type=int, default=2, help="Inspect bundle fields with 1..N readers")
    p_iba.add_argument("--struct-filter", default=DEFAULT_STRUCT_FILTER, help="Comma-separated substrings matched against structure OR module name (empty = all)")
    p_iba.add_argument("--name-filter", default="", help="Optional comma-separated module-name substrings")
    p_iba.add_argument("--main-only", action=argparse.BooleanOptionalAction, default=True, help="Restrict to Main-reaching structures")
    p_iba.add_argument("--with-peel", action=argparse.BooleanOptionalAction, default=True, help="Estimate exclusive peel impact for flagged fields")
    p_iba.add_argument("--limit", type=int, default=30)

    p_vd = sub.add_parser("vacuous-defs", help="Axis #10 (#466): Fast whole-repo syntactic scan for vacuous Prop defs & 0-field placeholders")
    p_vd.add_argument("--main-only", action=argparse.BooleanOptionalAction, default=True, help="Restrict to Main-reaching modules")
    p_vd.add_argument("--max-cone", type=int, default=0, help="Optional max reverse cone filter (0 = unlimited)")
    p_vd.add_argument("--limit", type=int, default=40)

    p_ud = sub.add_parser("unreferenced-decls", help="Axis #11 (#466): Syntactic scan for declarations & modules with 0 external/same-file refs")
    p_ud.add_argument("--prefix", default="", help="Optional module or path prefix filter")
    p_ud.add_argument("--max-cone", type=int, default=-1, help="Max reverse cone filter (-1 => 10 when --prefix omitted, 0 unlimited when --prefix set)")
    p_ud.add_argument("--min-body-lines", type=int, default=1, help="Min declaration line span")
    p_ud.add_argument("--include-private", action="store_true", help="Also scan private declarations")
    p_ud.add_argument("--main-only", action=argparse.BooleanOptionalAction, default=True, help="Restrict to Main-reaching modules")
    p_ud.add_argument("--limit", type=int, default=50)

    args = ap.parse_args()
    return {
        "chokepoints": cmd_chokepoints,
        "published-dups": cmd_published_dups,
        "neg-instances": cmd_neg_instances,
        "duplicate-stems": cmd_duplicate_stems,
        "heavy-pillars": cmd_heavy_pillars,
        "unused-fields": cmd_unused_fields,
        "dom-pillars": cmd_dom_pillars,
        "decl-dups": cmd_decl_dups,
        "ignored-bundle-args": cmd_ignored_bundle_args,
        "vacuous-defs": cmd_vacuous_defs,
        "unreferenced-decls": cmd_unreferenced_decls,
    }[args.cmd](args)


if __name__ == "__main__":
    raise SystemExit(main())
