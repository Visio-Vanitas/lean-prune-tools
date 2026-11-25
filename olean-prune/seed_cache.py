#!/usr/bin/env python3
"""Seed the incremental per-module extraction cache from existing names/deps outputs."""
from __future__ import annotations

import argparse
import collections
import glob
import hashlib
from pathlib import Path

from lean_syntax import discover_src_modules


def _hh(val: str) -> str:
    return hashlib.sha1(val.encode("utf-8")).hexdigest()[:24]


def olean_cache_key(base: Path) -> str | None:
    parts: list[str] = []
    for ext in (".olean", ".olean.server", ".olean.private"):
        art = Path(f"{base}{ext}")
        if art.exists():
            h_file = Path(f"{base}{ext}.hash")
            if not h_file.is_file() or art.stat().st_size == 0:
                return None
            parts.append(h_file.read_text(encoding="utf-8").strip())
    return "-".join(parts) if parts else None


def seed_cache(repo: Path, work_dir: Path, names_glob: str, deps_glob: str) -> dict[str, int]:
    olean_root = repo / ".lake" / "build" / "lib" / "lean"
    cache_dir = work_dir / "cache"
    cache_dir.mkdir(parents=True, exist_ok=True)
    mods = discover_src_modules(repo)
    counts: dict[str, int] = {}

    for mode, pattern in (("names", names_glob), ("deps", deps_glob)):
        rows: dict[str, list[str]] = collections.defaultdict(list)
        for path_str in sorted(glob.glob(pattern)):
            with open(path_str, encoding="utf-8") as fh:
                for line in fh:
                    rows[line.split("\t", 1)[0]].append(line)

        seeded = 0
        for mod in mods:
            base = olean_root / Path(mod.replace(".", "/"))
            if not Path(f"{base}.olean").exists():
                continue
            key = olean_cache_key(base)
            if key:
                out_p = cache_dir / f"{_hh(mod)}.{_hh(key)}.{mode}"
                out_p.write_text("".join(rows.get(mod, ())), encoding="utf-8")
                seeded += 1
        counts[mode] = seeded
        print(f"{mode}: seeded {seeded}", flush=True)

    return counts


def main() -> int:
    ap = argparse.ArgumentParser(description="Seed incremental extraction cache from existing TSV/TXT outputs.")
    ap.add_argument("--repo", type=Path, required=True, help="Path to Lean project repository")
    ap.add_argument("--work-dir", type=Path, default=Path("work"), help="Working directory (default: ./work)")
    ap.add_argument("--names-glob", default="", help="Glob for existing names*.txt files")
    ap.add_argument("--deps-glob", default="", help="Glob for existing deps *.tsv files")
    args = ap.parse_args()

    work = args.work_dir.resolve()
    names_glob = args.names_glob or str(work / "names*.txt")
    deps_glob = args.deps_glob or str(work / "olean" / "deps" / "*.tsv")
    seed_cache(args.repo.resolve(), work, names_glob, deps_glob)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
