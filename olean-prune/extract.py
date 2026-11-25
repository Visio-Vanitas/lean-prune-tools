#!/usr/bin/env python3
"""Extract exact constant graph from .olean/.olean.server/.olean.private and mark live reachability."""
from __future__ import annotations

import argparse
import collections
import concurrent.futures as cf
import json
import sqlite3
import subprocess
import sys
import tempfile
from pathlib import Path

from ext_ns import find_lean_exe
from lean_syntax import discover_src_modules, parse_lakefile_roots, parse_lean_imports, resolve_roots, write_lines
from load import load_tsv_to_db
from reach import compute_reach
from seed_cache import _hh, olean_cache_key


def build_import_graph(mods: dict[str, Path]) -> dict[str, list[str]]:
    graph: dict[str, list[str]] = {}
    mod_set = set(mods)
    for mod, path in mods.items():
        text = path.read_text(encoding="utf-8", errors="replace")
        imps: list[str] = []
        for spec in parse_lean_imports(text):
            for tgt in spec.targets:
                if tgt in mod_set:
                    imps.append(tgt)
        graph[mod] = imps
    return graph


def compute_module_closure(graph: dict[str, list[str]], roots: set[str]) -> set[str]:
    seen = set(roots)
    stack = list(roots)
    while stack:
        cur = stack.pop()
        for dep in graph.get(cur, ()):
            if dep not in seen:
                seen.add(dep)
                stack.append(dep)
    return seen


def run_extract(
    repo: Path,
    work_dir: Path,
    dump_lean: Path,
    roots: set[str],
    keep_roots: set[str],
    jobs: int = 8,
    force: bool = False,
) -> int:
    work_dir.mkdir(parents=True, exist_ok=True)
    cache_dir = work_dir / "cache"
    deps_dir = work_dir / "olean" / "deps"
    cache_dir.mkdir(parents=True, exist_ok=True)
    deps_dir.mkdir(parents=True, exist_ok=True)

    mods = discover_src_modules(repo)
    graph = build_import_graph(mods)
    (work_dir / "G_before.json").write_text(json.dumps(graph), encoding="utf-8")
    print(f"modules: {len(mods)}", flush=True)

    active_roots = {m for m in mods if m in roots}
    main_clos = compute_module_closure(graph, active_roots)
    print(f"roots={sorted(active_roots)} main_closure={len(main_clos)}", flush=True)

    olean_root = repo / ".lake" / "build" / "lib" / "lean"
    lst: list[tuple[str, Path]] = []
    for mod in sorted(mods):
        base = olean_root / Path(mod.replace(".", "/"))
        if Path(f"{base}.olean").exists():
            lst.append((mod, base))
    print(f"modules with .olean: {len(lst)}", flush=True)

    missing_olean = [m for m in sorted(main_clos) if not (olean_root / f"{m.replace('.', '/')}.olean").exists()]
    print(f"closure modules without .olean: {len(missing_olean)} {missing_olean[:5]}", flush=True)

    keys = {mod: olean_cache_key(base) for mod, base in lst}

    def cache_path(mod: str, kind: str) -> Path:
        k = keys[mod]
        if k:
            return cache_dir / f"{_hh(mod)}.{_hh(k)}.{kind}"
        return cache_dir / f"{_hh(mod)}.nokey.{kind}"

    todo = [
        (mod, base)
        for mod, base in lst
        if not (keys[mod] and cache_path(mod, "names").is_file() and cache_path(mod, "deps").is_file())
    ]
    print(f"incremental cache: cached={len(lst) - len(todo)} to_extract={len(todo)}", flush=True)

    lean_exe = find_lean_exe() if todo else ""

    with tempfile.TemporaryDirectory() as td_str:
        td = Path(td_str)

        def run_stage(mode: str, known_file: Path | None = None) -> None:
            chunks = [todo[i::jobs] for i in range(jobs)]

            def worker(idx: int, items: list[tuple[str, Path]]) -> tuple[Path, Path]:
                list_p = td / f"b{idx}.list"
                out_p = td / f"{mode}_out{idx}.txt"
                err_p = td / f"{mode}_{idx}.err"
                list_p.write_text("".join(f"{m}\t{b}\n" for m, b in items), encoding="utf-8")
                if not items:
                    out_p.write_text("", encoding="utf-8")
                    err_p.write_text("", encoding="utf-8")
                    return out_p, err_p
                cmd = (
                    [lean_exe, "--run", str(dump_lean), "names", str(out_p), str(list_p)]
                    if mode == "names"
                    else [lean_exe, "--run", str(dump_lean), "deps", str(out_p), str(known_file), str(list_p)]
                )
                r = subprocess.run(cmd, capture_output=True, text=True)
                err_p.write_text(r.stderr, encoding="utf-8")
                if r.returncode != 0:
                    raise RuntimeError(f"Dump.lean {mode} worker {idx} failed ({r.returncode}): {r.stderr[:240]}")
                return out_p, err_p

            rows: dict[str, list[str]] = collections.defaultdict(list)
            err_lines = 0
            with cf.ThreadPoolExecutor(max_workers=jobs) as ex:
                for out_p, err_p in ex.map(lambda p: worker(*p), enumerate(chunks)):
                    with out_p.open(encoding="utf-8") as fh:
                        for line in fh:
                            rows[line.split("\t", 1)[0]].append(line)
                    err_txt = err_p.read_text(encoding="utf-8", errors="replace")
                    err_lines += sum(1 for ln in err_txt.splitlines() if "ERR " in ln)

            for mod, _ in todo:
                cache_path(mod, mode).write_text("".join(rows.get(mod, ())), encoding="utf-8")
            if mode == "deps":
                print(f"deps errs: {err_lines}", flush=True)

        if todo:
            run_stage("names")

        names_out = work_dir / "names.txt"
        known_out = work_dir / "known.txt"
        known_count = 0
        with names_out.open("w", encoding="utf-8") as nf, known_out.open("w", encoding="utf-8") as kf:
            for mod, _ in lst:
                with cache_path(mod, "names").open(encoding="utf-8") as cfh:
                    for line in cfh:
                        nf.write(line)
                        parts = line.rstrip("\n").split("\t")
                        if len(parts) >= 3:
                            kf.write(parts[2] + "\n")
                            known_count += 1
        print(f"known constants: {known_count}", flush=True)

        if todo:
            run_stage("deps", known_file=known_out)

    for old_tsv in deps_dir.glob("*.tsv"):
        old_tsv.unlink()
    merged_tsv = deps_dir / "r0000.tsv"
    with merged_tsv.open("w", encoding="utf-8") as out_fh:
        for mod, _ in lst:
            out_fh.write(cache_path(mod, "deps").read_text(encoding="utf-8"))

    db_path = work_dir / "olean" / "decl_graph.db"
    load_tsv_to_db(deps_dir, db_path)
    compute_reach(db_path, active_roots or roots)

    con = sqlite3.connect(str(db_path))
    try:
        with_rows = {m for (m,) in con.execute("SELECT DISTINCT mod FROM decls")}
        tags = collections.Counter(t for (t,) in con.execute("SELECT src FROM decls"))
        live_mods = {
            m for (m,) in con.execute("SELECT DISTINCT d.mod FROM decls d JOIN live l ON l.id = d.id")
        }
    finally:
        con.close()

    print(f"src tags: {dict(tags)}", flush=True)
    missing_rows = sorted(m for m in main_clos if m not in with_rows)
    print(f"main-closure modules with no DB rows: {len(missing_rows)} {missing_rows[:10]}", flush=True)
    write_lines(work_dir / "closure_norows.txt", missing_rows)

    if missing_rows and not force:
        print("ABORT: main-closure modules missing from DB (pass --force to continue)", file=sys.stderr)
        return 2

    candidates = sorted(m for m in mods if m not in live_mods and m not in keep_roots)
    cand_file = work_dir / "cand.txt"
    write_lines(cand_file, candidates)
    print(f"candidates: {len(candidates)} -> {cand_file}", flush=True)
    return 0


def main() -> int:
    ap = argparse.ArgumentParser(description="Extract Lean .olean constant graph and compute initial dead-module candidates.")
    ap.add_argument("--repo", type=Path, required=True, help="Path to Lean project repository")
    ap.add_argument("--work-dir", type=Path, default=Path("work"), help="Working directory (default: ./work)")
    ap.add_argument(
        "--dump-lean",
        type=Path,
        default=Path(__file__).resolve().parent / "Dump.lean",
        help="Path to Dump.lean",
    )
    ap.add_argument("--roots", default="", help="Comma-separated reachability roots (default: auto-detect from lakefile)")
    ap.add_argument("--keep-roots", default="", help="Extra comma-separated modules never deleted")
    ap.add_argument("--jobs", type=int, default=8, help="Parallel extractor workers (default: 8)")
    ap.add_argument("--force", action="store_true", help="Continue even if some closure modules lack DB rows")
    args = ap.parse_args()

    repo = args.repo.resolve()
    roots = resolve_roots(repo, args.roots)
    keep_roots = parse_lakefile_roots(repo) | roots
    if args.keep_roots:
        keep_roots |= {r.strip() for r in args.keep_roots.split(",") if r.strip()}

    return run_extract(
        repo=repo,
        work_dir=args.work_dir.resolve(),
        dump_lean=args.dump_lean.resolve(),
        roots=roots,
        keep_roots=keep_roots,
        jobs=args.jobs,
        force=args.force,
    )


if __name__ == "__main__":
    raise SystemExit(main())
