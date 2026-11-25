#!/usr/bin/env python3
"""Collect namespaces exported by external packages (Mathlib, Batteries, Lean core)."""
from __future__ import annotations

import argparse
import concurrent.futures as cf
import shutil
import subprocess
import tempfile
from pathlib import Path


def find_lean_exe() -> str:
    lean = shutil.which("lean")
    if lean:
        return lean
    fallback = Path.home() / ".elan" / "bin" / "lean"
    if fallback.is_file():
        return str(fallback)
    raise FileNotFoundError("Could not find `lean` executable on PATH or ~/.elan/bin/lean")


def discover_external_olean_roots(repo: Path, lean_exe: str) -> list[Path]:
    roots: list[Path] = []
    pkg_dir = repo / ".lake" / "packages"
    if pkg_dir.is_dir():
        for lib_dir in sorted(pkg_dir.glob("*/.lake/build/lib/lean")):
            if lib_dir.is_dir():
                roots.append(lib_dir)

    r = subprocess.run([lean_exe, "--print-prefix"], capture_output=True, text=True, check=True)
    tc_lib = Path(r.stdout.strip()) / "lib" / "lean"
    if tc_lib.is_dir():
        roots.append(tc_lib)
    return roots


def extract_external_namespaces(
    repo: Path,
    out_file: Path,
    dump_lean: Path,
    jobs: int = 8,
) -> int:
    lean_exe = find_lean_exe()
    roots = discover_external_olean_roots(repo, lean_exe)
    mod_stems: list[tuple[str, str]] = []
    for root in roots:
        for olean in root.rglob("*.olean"):
            rel = olean.relative_to(root).as_posix()
            stem = str(olean)[: -len(".olean")]
            mod = rel[: -len(".olean")].replace("/", ".")
            mod_stems.append((mod, stem))

    print(f"external modules: {len(mod_stems)}", flush=True)
    out_file.parent.mkdir(parents=True, exist_ok=True)
    ns: set[str] = set()

    with tempfile.TemporaryDirectory() as td_str:
        td = Path(td_str)
        chunks = [mod_stems[i::jobs] for i in range(jobs)]

        def worker(idx: int, items: list[tuple[str, str]]) -> Path:
            list_p = td / f"x{idx}.list"
            out_p = td / f"x{idx}.out"
            list_p.write_text("".join(f"{m}\t{s}\n" for m, s in items), encoding="utf-8")
            if items:
                subprocess.run(
                    [lean_exe, "--run", str(dump_lean), "names", str(out_p), str(list_p)],
                    capture_output=True,
                    text=True,
                    check=True,
                )
            else:
                out_p.write_text("", encoding="utf-8")
            return out_p

        with cf.ThreadPoolExecutor(max_workers=jobs) as ex:
            for out_p in ex.map(lambda p: worker(*p), enumerate(chunks)):
                with out_p.open(encoding="utf-8", errors="replace") as fh:
                    for line in fh:
                        parts = line.rstrip("\n").split("\t")
                        if len(parts) < 3:
                            continue
                        segs = parts[2].split(".")
                        for k in range(1, len(segs)):
                            ns.add(".".join(segs[:k]))

    out_file.write_text("\n".join(sorted(ns)) + ("\n" if ns else ""), encoding="utf-8")
    print(f"external namespaces: {len(ns)} -> {out_file}", flush=True)
    return len(ns)


def main() -> int:
    ap = argparse.ArgumentParser(description="Extract external Lean namespaces so closeD never strips them.")
    ap.add_argument("--repo", type=Path, required=True, help="Path to Lean project repository")
    ap.add_argument("--work-dir", type=Path, default=Path("work"), help="Working directory (default: ./work)")
    ap.add_argument(
        "--dump-lean",
        type=Path,
        default=Path(__file__).resolve().parent / "Dump.lean",
        help="Path to Dump.lean",
    )
    ap.add_argument("--jobs", type=int, default=8, help="Parallel extractor workers (default: 8)")
    args = ap.parse_args()

    extract_external_namespaces(
        repo=args.repo.resolve(),
        out_file=(args.work_dir / "ext_ns.txt").resolve(),
        dump_lean=args.dump_lean.resolve(),
        jobs=args.jobs,
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
