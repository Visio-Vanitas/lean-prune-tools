#!/usr/bin/env python3
"""Load extracted declaration/dependency TSV files into a SQLite graph DB."""
from __future__ import annotations

import argparse
import sqlite3
from pathlib import Path


def load_tsv_to_db(deps_dir: Path, db_path: Path) -> tuple[int, int, int]:
    db_path.parent.mkdir(parents=True, exist_ok=True)
    if db_path.exists():
        db_path.unlink()

    files = sorted(deps_dir.glob("*.tsv"))
    con = sqlite3.connect(str(db_path))
    try:
        cur = con.cursor()
        cur.executescript(
            """
            CREATE TABLE decls(
                id INTEGER PRIMARY KEY,
                name TEXT UNIQUE NOT NULL,
                mod TEXT NOT NULL,
                kind TEXT NOT NULL,
                src TEXT NOT NULL
            );
            CREATE TABLE uses(
                src INTEGER NOT NULL,
                dst INTEGER NOT NULL
            );
            """
        )
        ids: dict[str, int] = {}
        rows: list[tuple[int, str, str, str, str]] = []
        pending: list[tuple[int, list[str]]] = []

        for f in files:
            with f.open(encoding="utf-8") as fh:
                for line in fh:
                    parts = line.rstrip("\n").split("\t")
                    if len(parts) < 4:
                        continue
                    mod, tag, kind, name = parts[:4]
                    if name in ids:
                        continue
                    did = len(ids) + 1
                    ids[name] = did
                    rows.append((did, name, mod, kind, tag))
                    dep_list = parts[4].split() if len(parts) > 4 and parts[4] else []
                    pending.append((did, dep_list))

        cur.executemany("INSERT INTO decls VALUES (?,?,?,?,?)", rows)
        edges = [(s, ids[d]) for s, ds in pending for d in ds if d in ids]
        cur.executemany("INSERT INTO uses VALUES (?,?)", edges)
        cur.executescript(
            "CREATE INDEX iu_s ON uses(src); "
            "CREATE INDEX iu_d ON uses(dst); "
            "CREATE INDEX id_m ON decls(mod);"
        )
        con.commit()
    finally:
        con.close()

    return len(rows), len(edges), len(files)


def main() -> int:
    ap = argparse.ArgumentParser(description="Load extracted .olean TSV files into SQLite.")
    ap.add_argument("--work-dir", type=Path, default=Path("work"), help="Working directory (default: ./work)")
    ap.add_argument("--deps-dir", type=Path, default=None, help="Directory with *.tsv (default: <work-dir>/olean/deps)")
    ap.add_argument("--db", type=Path, default=None, help="Output SQLite DB path (default: <work-dir>/olean/decl_graph.db)")
    args = ap.parse_args()

    deps_dir = (args.deps_dir or (args.work_dir / "olean" / "deps")).resolve()
    db_path = (args.db or (args.work_dir / "olean" / "decl_graph.db")).resolve()
    n_decls, n_edges, n_files = load_tsv_to_db(deps_dir, db_path)
    print(f"loaded {n_decls} decls, {n_edges} edges from {n_files} files -> {db_path}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
