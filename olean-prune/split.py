#!/usr/bin/env python3
"""Split a closed dead-module set into independent, directory-coherent chunks."""
from __future__ import annotations

import argparse
import collections
import json
import sqlite3
from pathlib import Path

from lean_syntax import (
    IDENT_RE,
    IMPORT_LINE_PREFIX_RE,
    OPEN_EXPORT_LINE_RE,
    mod_to_relpath,
    read_nonempty_lines,
    strip_lean_comments,
    write_lines,
)


def _comp_area(mods: list[str], depth: int) -> str:
    counts = collections.Counter(".".join(m.split(".")[:depth]) for m in mods)
    return counts.most_common(1)[0][0]


def split_dead_set(
    repo: Path,
    work_dir: Path,
    set_file: Path,
    relax_file: Path | None,
    out_dir: Path,
    *,
    max_chunk: int = 40,
    area_depth: int = 1,
    adaptive_depth: bool = False,
) -> dict[str, object]:
    B = read_nonempty_lines(set_file)
    BS = set(B)
    relax: dict[str, list[str]] = (
        json.loads(relax_file.read_text(encoding="utf-8"))
        if (relax_file is not None and relax_file.is_file())
        else {}
    )

    db_path = work_dir / "olean" / "decl_graph.db"
    con = sqlite3.connect(str(db_path))
    try:
        mod_of_id: dict[int, str] = {}
        names: dict[str, list[str]] = collections.defaultdict(list)
        for i, name, mod in con.execute("SELECT id, name, mod FROM decls"):
            mod_of_id[i] = mod
            if mod in BS:
                names[mod].append(name)
        uses = con.execute("SELECT src, dst FROM uses").fetchall()
    finally:
        con.close()

    parent = {m: m for m in B}

    def find(x: str) -> str:
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x

    def union(a: str, b: str) -> None:
        ra, rb = find(a), find(b)
        if ra != rb:
            parent[ra] = rb

    ne: collections.Counter[str] = collections.Counter()
    for src, dst in uses:
        ms, md = mod_of_id.get(src), mod_of_id.get(dst)
        if ms in BS and md in BS and ms != md:
            union(ms, md)
            ne["const"] += 1

    suf: dict[str, set[str]] = collections.defaultdict(set)
    pre: dict[str, set[str]] = collections.defaultdict(set)
    for mod, decls in names.items():
        for name in decls:
            segs = name.split(".")
            if any(c.startswith(("_", "proof_", "match_", "eq_")) for c in segs):
                continue
            for k in range(len(segs)):
                suf[".".join(segs[k:])].add(mod)
            for k in range(1, len(segs)):
                pre[".".join(segs[:k])].add(mod)

    for u in B:
        p = repo / mod_to_relpath(u)
        if not p.is_file():
            continue
        clean = strip_lean_comments(p.read_text(encoding="utf-8", errors="replace"))
        for line in clean.splitlines():
            if IMPORT_LINE_PREFIX_RE.match(line):
                continue
            mo = OPEN_EXPORT_LINE_RE.match(line)
            toks = IDENT_RE.findall(mo.group(1) if mo else line)
            for tok in toks:
                tok = tok.rstrip(".")
                hits = (pre.get(tok, set()) | suf.get(tok, set())) if mo else suf.get(tok, set())
                for v in hits:
                    if v != u:
                        union(u, v)
                        ne["open" if mo else "text"] += 1

    # Co-locate all candidate providers in B referenced by the same relaxed (file, token),
    # guaranteeing that each open-line token relaxation maps to a single unique chunk.
    for _, toks in relax.items():
        for tok in toks:
            providers = sorted(v for v in (pre.get(tok, set()) | suf.get(tok, set())) if v in BS)
            if len(providers) >= 2:
                first = providers[0]
                for nxt in providers[1:]:
                    union(first, nxt)
                    ne["relax_coloc"] += 1

    comps: dict[str, list[str]] = collections.defaultdict(list)
    for mod in B:
        comps[find(mod)].append(mod)
    comp_list = [sorted(c) for c in comps.values()]
    largest = max((len(c) for c in comp_list), default=0)
    print(f"modules={len(B)} edges={dict(ne)} components={len(comp_list)} largest={largest}", flush=True)

    # Group components by directory prefix, refining deep areas when --adaptive-depth is set.
    def group_components(items: list[list[str]], depth: int) -> dict[str, list[list[str]]]:
        grouped: dict[str, list[list[str]]] = collections.defaultdict(list)
        for comp in items:
            grouped[_comp_area(comp, depth)].append(comp)
        if not adaptive_depth:
            return grouped
        refined: dict[str, list[list[str]]] = collections.defaultdict(list)
        for area, area_comps in grouped.items():
            total = sum(len(c) for c in area_comps)
            max_seg_len = max((len(m.split(".")) for c in area_comps for m in c), default=depth)
            if total > max_chunk and depth < max_seg_len:
                sub = group_components(area_comps, depth + 1)
                for k, v in sub.items():
                    refined[k].extend(v)
            else:
                refined[area].extend(area_comps)
        return refined

    by_area = group_components(comp_list, area_depth)
    chunks: list[tuple[str, list[str]]] = []
    for area in sorted(by_area):
        cur: list[str] = []
        for comp in sorted(by_area[area], key=lambda c: (-len(c), c[0])):
            if cur and len(cur) + len(comp) > max_chunk:
                chunks.append((area, cur))
                cur = []
            cur.extend(comp)
        if cur:
            chunks.append((area, cur))

    where = {mod: idx for idx, (_, ms) in enumerate(chunks, 1) for mod in ms}
    rbc: dict[int, dict[str, list[str]]] = collections.defaultdict(dict)
    if chunks:
        for fname, toks in relax.items():
            for tok in toks:
                ks = {where[v] for v in (pre.get(tok, set()) | suf.get(tok, set())) if v in where}
                # Singleton after relax_coloc; fall back to chunk 1 only if no B-decl matched.
                target_k = next(iter(ks)) if ks else 1
                rbc[target_k].setdefault(fname, []).append(tok)

    out_dir.mkdir(parents=True, exist_ok=True)
    for idx, rdict in rbc.items():
        (out_dir / f"relax{idx:02d}.json").write_text(json.dumps(rdict, indent=1), encoding="utf-8")

    manifest_chunks = []
    for idx, (area, ms) in enumerate(chunks, 1):
        mods_sorted = sorted(ms)
        write_lines(out_dir / f"chunk{idx:02d}.txt", mods_sorted)
        print(f"chunk{idx:02d} area={area} modules={len(mods_sorted)}", flush=True)
        manifest_chunks.append({"id": idx, "area": area, "modules": mods_sorted})

    manifest = {"chunks": manifest_chunks, "relax": relax}
    (out_dir / "chunks.json").write_text(json.dumps(manifest, indent=1), encoding="utf-8")
    return manifest


def main() -> int:
    ap = argparse.ArgumentParser(description="Split a closed dead-module set into independent chunks.")
    ap.add_argument("--repo", type=Path, required=True, help="Path to Lean project repository")
    ap.add_argument("--work-dir", type=Path, default=Path("work"), help="Working directory (default: ./work)")
    ap.add_argument("--set", dest="set_file", type=Path, default=None, help="Dead-module set (default: <work-dir>/v3b_set.txt)")
    ap.add_argument("--relax", dest="relax_file", type=Path, default=None, help="Relax JSON (default: <work-dir>/v3b_relax.json)")
    ap.add_argument("--out-dir", type=Path, default=None, help="Output chunks directory (default: <work-dir>/chunks)")
    ap.add_argument("--max-chunk", type=int, default=40, help="Target max modules per chunk (default: 40)")
    ap.add_argument("--area-depth", type=int, default=1, help="Module dot-prefix depth for grouping (default: 1)")
    ap.add_argument("--adaptive-depth", action="store_true", help="Refine areas exceeding --max-chunk by deeper directory prefixes")
    args = ap.parse_args()

    work = args.work_dir.resolve()
    set_file = (args.set_file or (work / "v3b_set.txt")).resolve()
    relax_file = (args.relax_file or (work / "v3b_relax.json")).resolve()
    out_dir = (args.out_dir or (work / "chunks")).resolve()

    split_dead_set(
        repo=args.repo.resolve(),
        work_dir=work,
        set_file=set_file,
        relax_file=relax_file,
        out_dir=out_dir,
        max_chunk=args.max_chunk,
        area_depth=args.area_depth,
        adaptive_depth=args.adaptive_depth,
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
