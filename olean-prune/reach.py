#!/usr/bin/env python3
"""Mark all declarations reachable from the root modules in decl_graph.db."""
from __future__ import annotations

import argparse
import collections
import sqlite3
from pathlib import Path

from lean_syntax import resolve_roots


def compute_reach(db_path: Path, roots: set[str] | None = None) -> tuple[int, int, int]:
    root_mods = roots if roots is not None else {"Main"}
    con = sqlite3.connect(str(db_path))
    try:
        cur = con.cursor()
        names = {i: (n, m, k) for i, n, m, k in cur.execute("SELECT id, name, mod, kind FROM decls")}
        adj: dict[int, list[int]] = collections.defaultdict(list)
        for src, dst in cur.execute("SELECT src, dst FROM uses"):
            adj[src].append(dst)

        root_ids = [i for i, (_, m, _) in names.items() if m in root_mods]
        seen = set(root_ids)
        stack = list(root_ids)
        while stack:
            cur_id = stack.pop()
            for nxt in adj.get(cur_id, ()):
                if nxt not in seen:
                    seen.add(nxt)
                    stack.append(nxt)

        cur.execute("CREATE TABLE IF NOT EXISTS live(id INTEGER PRIMARY KEY)")
        cur.execute("DELETE FROM live")
        cur.executemany("INSERT INTO live VALUES (?)", [(i,) for i in seen])
        con.commit()
    finally:
        con.close()

    return len(root_ids), len(seen), len(names)


def main() -> int:
    ap = argparse.ArgumentParser(description="Compute forward reachability from root modules in decl_graph.db.")
    ap.add_argument("--db", type=Path, required=True, help="Path to decl_graph.db")
    ap.add_argument("--repo", type=Path, default=None, help="Optional repo path to auto-detect lakefile roots")
    ap.add_argument("--roots", default="", help="Comma-separated root modules (default: lakefile roots or Main)")
    args = ap.parse_args()

    if args.roots.strip():
        roots = {r.strip() for r in args.roots.split(",") if r.strip()}
    elif args.repo is not None:
        roots = resolve_roots(args.repo.resolve(), "")
    else:
        roots = {"Main"}
    n_roots, n_seen, n_total = compute_reach(args.db.resolve(), roots)
    print(f"roots={n_roots} reached={n_seen} of total={n_total}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
