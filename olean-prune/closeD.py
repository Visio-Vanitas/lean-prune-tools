#!/usr/bin/env python3
"""Fixpoint closure over hard constant edges, text-refs, open/export clauses, and zero-const imports."""
from __future__ import annotations

import argparse
import collections
import json
import re
import sqlite3
from pathlib import Path

import relax_policy as RP
from lean_syntax import (
    IDENT_RE,
    IMPORT_LINE_PREFIX_RE,
    OPEN_EXPORT_LINE_RE,
    OPEN_TOK_RE,
    mod_to_relpath,
    parse_import_line,
    parse_lakefile_roots,
    read_nonempty_lines,
    strip_lean_comments,
    write_lines,
)

EXPORT_CMD_RE = re.compile(r"^\s*(?:@\[[^\]]*\]\s*)?export\b", re.MULTILINE)
SCOPED_DECL_RE = re.compile(r"^(?!\s*(?:@\[[^\]]*\]\s*)?(?:open|export)\b).*\bscoped\b", re.MULTILINE)
INERT_LINE_RE = re.compile(
    r"^\s*($|module\b|(?:public\s+|private\s+)?(?:meta\s+)?import\b|open\b|namespace\b|end\b|"
    r"section\b|noncomputable\s+section\b|set_option\b|@\[expose\]\s*public\s+section|public\s+section)"
)
CLAUSE_WITH_LIST_RE = re.compile(
    r"([A-Za-z_\u0370-\u03ff][\w.'!?\u2080-\u2089\u0370-\u03ff]*)\s*"
    r"(?:\(([^)]*)\)|\b(renaming|hiding)\b([^\n]*))"
)


def _read_mod_source(repo: Path, mod: str) -> str:
    p = repo / mod_to_relpath(mod)
    if not p.is_file():
        return ""
    return p.read_text(encoding="utf-8", errors="replace")


def extract_opened_namespaces(clean_src: str) -> set[str]:
    """Return opened/exported namespace tokens from a comment-stripped Lean source."""
    out: set[str] = set()
    for line in clean_src.splitlines():
        mm = OPEN_EXPORT_LINE_RE.match(line)
        if not mm:
            continue
        rest = re.sub(r"\(.*?\)|\bhiding\b.*|\bin\b.*|\brenaming\b.*", "", mm.group(1))
        for tok in rest.split():
            if OPEN_TOK_RE.match(tok):
                out.add(tok)
    return out


def extract_open_item_refs(line_rest: str) -> list[str]:
    """Extract qualified candidate references from selective `(a b)`, `hiding a b`, and `renaming a → b`."""
    rest = re.sub(r"\s+in\b.*$", "", line_rest)
    refs: list[str] = []
    for match in CLAUSE_WITH_LIST_RE.finditer(rest):
        ns = match.group(1)
        paren_items = match.group(2)
        kw = match.group(3)
        kw_body = match.group(4)
        if paren_items is not None:
            for item in IDENT_RE.findall(paren_items):
                refs.append(f"{ns}.{item.rstrip('.')}")
        elif kw == "hiding" and kw_body is not None:
            for item in IDENT_RE.findall(kw_body):
                if item not in ("hiding", "renaming"):
                    refs.append(f"{ns}.{item.rstrip('.')}")
        elif kw == "renaming" and kw_body is not None:
            for entry in kw_body.split(","):
                lhs = re.split(r"→|->", entry, maxsplit=1)[0]
                for item in IDENT_RE.findall(lhs):
                    if item not in ("hiding", "renaming"):
                        refs.append(f"{ns}.{item.rstrip('.')}")
    return refs


def is_inert_module(clean_src: str) -> bool:
    return all(INERT_LINE_RE.match(line) for line in clean_src.splitlines())


def run_close_d(
    repo: Path,
    work_dir: Path,
    cand_file: Path,
    out_set: Path,
    out_relax: Path,
    *,
    policy_name: str | None = None,
    keep_roots: set[str] | None = None,
    hard_file: Path | None = None,
    no_relax_file: Path | None = None,
    debug_mods: list[str] | None = None,
) -> tuple[list[str], dict[str, list[str]]]:
    db_path = work_dir / "olean" / "decl_graph.db"
    B = set(read_nonempty_lines(cand_file))

    if hard_file and hard_file.is_file():
        B -= set(read_nonempty_lines(hard_file))
    no_relax = set(read_nonempty_lines(no_relax_file)) if (no_relax_file and no_relax_file.is_file()) else set()

    protected = parse_lakefile_roots(repo)
    if keep_roots:
        protected |= keep_roots
    B -= protected

    clean_cache: dict[str, str] = {}

    def get_clean(mod: str) -> str:
        if mod not in clean_cache:
            clean_cache[mod] = strip_lean_comments(_read_mod_source(repo, mod))
        return clean_cache[mod]

    # Modules containing `export` or declaring anything `scoped` produce non-constant effects
    # (export aliases, scoped notations/instances/attributes) and are kept conservatively.
    exp_or_scoped = {
        m
        for m in B
        if EXPORT_CMD_RE.search(get_clean(m)) or SCOPED_DECL_RE.search(get_clean(m))
    }
    print(f"kept: modules with export or scoped declarations: {len(exp_or_scoped)}", flush=True)
    B -= exp_or_scoped

    pname, policy_fn = RP.get(policy_name)
    print(f"relax policy: {pname}", flush=True)

    G: dict[str, list[str]] = json.loads((work_dir / "G_before.json").read_text(encoding="utf-8"))
    mod_set = set(G)

    con = sqlite3.connect(str(db_path))
    try:
        mod_of_id = {i: m for i, _, m in con.execute("SELECT id, name, mod FROM decls")}
        uses = con.execute("SELECT src, dst FROM uses").fetchall()
    finally:
        con.close()

    # Read public declaration names (only public .olean constants register namespaces for importers)
    names_files = [work_dir / "names.txt"] if (work_dir / "names.txt").is_file() else sorted(work_dir.glob("names*.txt"))
    bsuf: dict[str, set[str]] = collections.defaultdict(set)
    nbsuf: dict[str, set[str]] = collections.defaultdict(set)
    nb_rows: list[tuple[str, list[str]]] = []
    nsmods: dict[str, set[str]] = collections.defaultdict(set)
    suffix: dict[str, set[str]] = collections.defaultdict(set)

    for nf in names_files:
        with nf.open(encoding="utf-8") as fh:
            for line in fh:
                parts = line.rstrip("\n").split("\t")
                if len(parts) < 3:
                    continue
                mod, name = parts[0], parts[2]
                segs = name.split(".")
                for k in range(1, len(segs)):
                    nsmods[".".join(segs[:k])].add(mod)
                if any(c.startswith(("_", "proof_", "match_", "eq_")) for c in segs):
                    continue
                if mod not in B:
                    nb_rows.append((mod, segs))
                    continue
                for k in range(len(segs)):
                    bsuf[".".join(segs[k:])].add(mod)

    # Public import adjacency (reuses cached comment-stripped source)
    GP: dict[str, list[str]] = collections.defaultdict(list)
    for mod in G:
        for line in get_clean(mod).splitlines():
            spec = parse_import_line(line)
            if spec is not None and spec.is_public:
                GP[mod].extend(t for t in spec.targets if t in mod_set)

    for ns in nsmods:
        segs = ns.split(".")
        for k in range(len(segs)):
            suffix[".".join(segs[k:])].add(ns)

    ext_file = work_dir / "ext_ns.txt"
    EXT = set(read_nonempty_lines(ext_file)) if ext_file.is_file() else set()
    EXTSUF: set[str] = set()
    for ns in EXT:
        segs = ns.split(".")
        for k in range(len(segs)):
            EXTSUF.add(".".join(segs[k:]))
    print(f"external namespaces: {len(EXT)}", flush=True)

    RG: dict[str, list[str]] = collections.defaultdict(list)
    RGP: dict[str, list[str]] = collections.defaultdict(list)
    for a, bs in GP.items():
        for b in bs:
            RGP[b].append(a)
    for a, bs in G.items():
        for b in bs:
            RG[b].append(a)

    nconst = collections.Counter(mod_of_id.values())

    for mod_nb, segs in nb_rows:
        for k in range(len(segs)):
            tok = ".".join(segs[k:])
            if tok in bsuf:
                nbsuf[tok].add(mod_nb)
    del nb_rows
    print(f"B-only name suffixes: {len(bsuf)}", flush=True)

    def extract_textrefs(mod: str) -> dict[str, set[str]]:
        hit: dict[str, set[str]] = collections.defaultdict(set)
        for line in get_clean(mod).splitlines():
            if IMPORT_LINE_PREFIX_RE.match(line):
                continue
            mo = OPEN_EXPORT_LINE_RE.match(line)
            if mo:
                toks = extract_open_item_refs(mo.group(1))
            else:
                toks = IDENT_RE.findall(line)
            for tok in toks:
                tok = tok.rstrip(".")
                segs = tok.split(".")
                for k in range(len(segs), 0, -1):
                    prefix = ".".join(segs[:k])
                    if prefix in bsuf:
                        hit[prefix] |= bsuf[prefix]
        return hit

    closure_cache: dict[str, set[str]] = {}

    def importers(x: str) -> set[str]:
        if x in closure_cache:
            return closure_cache[x]
        q = {x}
        st = [x]
        while st:
            y = st.pop()
            for z in RG.get(y, ()):
                if z not in q:
                    q.add(z)
                    st.append(z)
        closure_cache[x] = q
        return q

    TR: dict[str, dict[str, set[str]]] = {}
    OP: dict[str, set[str]] = {}
    it = 0
    relax: dict[str, set[str]] = collections.defaultdict(set)

    while True:
        it += 1
        drop: set[str] = set()
        relax = collections.defaultdict(set)
        drop |= {mod_of_id[d] for s, d in uses if mod_of_id.get(d) in B and mod_of_id.get(s) not in B}

        nrel = 0
        reach_cache: dict[tuple[str, str], set[str]] = {}

        def reach(tag: str, ns_key: str, providers: list[str] | set[str]) -> set[str]:
            ck = (tag, ns_key)
            if ck in reach_cache:
                return reach_cache[ck]
            q = set(providers)
            st = list(providers)
            while st:
                x = st.pop()
                for y in RGP.get(x, ()):
                    if y not in q:
                        q.add(y)
                        st.append(y)
            reach_cache[ck] = q
            return q

        def can_see(tag: str, ns_key: str, providers: list[str] | set[str], mod_name: str) -> bool:
            q = reach(tag, ns_key, providers)
            return (mod_name in q) or any(dep in q for dep in G.get(mod_name, ()))

        for mod in G:
            if mod in B:
                continue
            if mod not in OP:
                OP[mod] = extract_opened_namespaces(get_clean(mod))
            for tok in OP[mod]:
                cands = suffix.get(tok)
                if not cands or not any(nsmods[c] & B for c in cands):
                    continue
                ext = tok in EXTSUF
                after = ext or any(can_see("k", c, [x for x in nsmods[c] if x not in B], mod) for c in cands)
                before = (not after) and any(can_see("a", c, nsmods[c], mod) for c in cands)
                prov_b = set().union(*(nsmods[c] & B for c in cands))
                edge = RP.Edge(
                    "open-namespace",
                    mod,
                    token=tok,
                    providers_in_B=prov_b,
                    visible_before=before,
                    visible_after=after,
                    external=ext,
                    failed_before=mod in no_relax,
                )
                act = policy_fn(edge)
                if act == RP.RELAX:
                    relax[mod].add(tok)
                    nrel += 1
                elif act == RP.KEEP:
                    drop |= prov_b

        ntr = 0
        for mod in G:
            if mod in B:
                continue
            if mod not in TR:
                TR[mod] = extract_textrefs(mod)
            for tok, prov in TR[mod].items():
                prov_b = {x for x in prov if x in B and mod in importers(x)}
                if not prov_b:
                    continue
                if any(mod in importers(y) or y == mod for y in nbsuf.get(tok, ()) if y not in B):
                    continue
                edge = RP.Edge("text-ref", mod, token=tok, providers_in_B=prov_b, failed_before=mod in no_relax)
                if policy_fn(edge) == RP.KEEP:
                    drop |= prov_b
                    ntr += 1

        zrel = 0
        zkeep = 0
        for mod in G:
            if mod in B:
                continue
            for dep in G[mod]:
                if dep in B and nconst[dep] == 0:
                    edge = RP.Edge(
                        "zero-const-import",
                        mod,
                        target=dep,
                        providers_in_B={dep},
                        inert=is_inert_module(get_clean(dep)),
                        failed_before=mod in no_relax,
                    )
                    if policy_fn(edge) == RP.KEEP:
                        drop.add(dep)
                        zkeep += 1
                    else:
                        zrel += 1

        drop &= B
        print(
            f"iter {it}: text-ref_keeps={ntr} drop={len(drop)} relaxed_opens={nrel} zero_const_relaxed={zrel} zero_const_kept={zkeep}",
            flush=True,
        )
        if not drop:
            break
        B -= drop

    final_set = sorted(B)
    relax_dict = {m: sorted(v) for m, v in sorted(relax.items()) if v}
    print(f"final: {len(final_set)} modules to delete, {len(relax_dict)} files with relaxed opens", flush=True)

    write_lines(out_set, final_set)
    out_relax.parent.mkdir(parents=True, exist_ok=True)
    out_relax.write_text(json.dumps(relax_dict, indent=1), encoding="utf-8")

    if debug_mods:
        for mod in debug_mods:
            print("DBG", mod, "in_B=", mod in B, "opened=", OP.get(mod), "relax=", relax_dict.get(mod, []))

    return final_set, relax_dict


def main() -> int:
    ap = argparse.ArgumentParser(description="Compute fixpoint closed dead-module set and open-line relaxations.")
    ap.add_argument("--repo", type=Path, required=True, help="Path to Lean project repository")
    ap.add_argument("--work-dir", type=Path, default=Path("work"), help="Working directory (default: ./work)")
    ap.add_argument("--cand", type=Path, default=None, help="Input candidate module list (default: <work-dir>/cand.txt)")
    ap.add_argument("--out-set", type=Path, default=None, help="Output dead module list (default: <work-dir>/v3b_set.txt)")
    ap.add_argument("--out-relax", type=Path, default=None, help="Output relax JSON (default: <work-dir>/v3b_relax.json)")
    ap.add_argument("--policy", default=None, help="Relax policy name (conservative or aggressive)")
    ap.add_argument("--keep-roots", default="", help="Extra comma-separated modules never deleted")
    ap.add_argument("--hard", type=Path, default=None, help="Optional file of module names that must be kept")
    ap.add_argument("--no-relax", type=Path, default=None, help="Optional file of kept modules whose opens must not be relaxed")
    ap.add_argument("--debug-mods", default="", help="Comma-separated module names to trace")
    args = ap.parse_args()

    work = args.work_dir.resolve()
    cand_file = (args.cand or (work / "cand.txt")).resolve()
    out_set = (args.out_set or (work / "v3b_set.txt")).resolve()
    out_relax = (args.out_relax or (work / "v3b_relax.json")).resolve()
    keep_roots = {r.strip() for r in args.keep_roots.split(",") if r.strip()} if args.keep_roots else None
    debug_mods = [m.strip() for m in args.debug_mods.split(",") if m.strip()] or None

    run_close_d(
        repo=args.repo.resolve(),
        work_dir=work,
        cand_file=cand_file,
        out_set=out_set,
        out_relax=out_relax,
        policy_name=args.policy,
        keep_roots=keep_roots,
        hard_file=args.hard.resolve() if args.hard else None,
        no_relax_file=args.no_relax.resolve() if args.no_relax else None,
        debug_mods=debug_mods,
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
