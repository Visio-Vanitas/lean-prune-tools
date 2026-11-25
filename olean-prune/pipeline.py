#!/usr/bin/env python3
"""Cross-platform orchestrator for extraction, closeD, application, chunk splitting, and patch generation."""
from __future__ import annotations

import argparse
import json
import subprocess
from pathlib import Path

from apply_relax import apply_relaxations
from closeD import run_close_d
from del_dead2 import apply_dead_deletions
from ext_ns import extract_external_namespaces
from extract import run_extract
from lean_syntax import parse_lakefile_roots
from quickcheck import run_quickcheck
from split import split_dead_set


def _ensure_clean_repo(repo: Path, allow_reset: bool) -> None:
    st = subprocess.run(["git", "status", "--porcelain"], cwd=str(repo), capture_output=True, text=True, check=True)
    if st.stdout.strip():
        if not allow_reset:
            raise RuntimeError(
                f"Repository {repo} has uncommitted changes; commit/stash them or pass --allow-reset."
            )
        subprocess.run(["git", "checkout", "-q", "--", "."], cwd=str(repo), check=True)
        subprocess.run(["git", "clean", "-qfd", "src", "scripts"], cwd=str(repo), check=True)


def main() -> int:
    ap = argparse.ArgumentParser(description="End-to-end orchestrator for compiled-graph dead-module removal.")
    ap.add_argument("--repo", type=Path, required=True, help="Path to Lean project repository")
    ap.add_argument("--work-dir", type=Path, default=Path("work"), help="Working directory (default: ./work)")
    sub = ap.add_subparsers(dest="cmd", required=True)

    p_ext = sub.add_parser("extract", help="Extract external namespaces and constant graph DB")
    p_ext.add_argument("--roots", default="Main,Statements")
    p_ext.add_argument("--jobs", type=int, default=8)
    p_ext.add_argument("--force", action="store_true")
    p_ext.add_argument("--skip-ext-ns", action="store_true")

    p_cls = sub.add_parser("close", help="Run closeD fixpoint")
    p_cls.add_argument("--policy", default=None)
    p_cls.add_argument("--hard", type=Path, default=None)
    p_cls.add_argument("--no-relax", type=Path, default=None)

    p_app = sub.add_parser("apply", help="Apply deletion set and relaxations to repo working tree")
    p_app.add_argument("--set", dest="set_file", type=Path, default=None)
    p_app.add_argument("--relax", dest="relax_file", type=Path, default=None)

    p_spl = sub.add_parser("split", help="Split closed set into independent chunks")
    p_spl.add_argument("--max-chunk", type=int, default=40)
    p_spl.add_argument("--area-depth", type=int, default=1)
    p_spl.add_argument("--adaptive-depth", action="store_true")
    p_spl.add_argument("--out-dir", type=Path, default=None)

    p_chk = sub.add_parser("chunks", help="Split and materialize clean per-chunk .diff patches")
    p_chk.add_argument("--max-chunk", type=int, default=40)
    p_chk.add_argument("--area-depth", type=int, default=1)
    p_chk.add_argument("--adaptive-depth", action="store_true")
    p_chk.add_argument("--out-dir", type=Path, default=None)
    p_chk.add_argument("--quickcheck-sample", type=int, default=0, help="Run selective quickcheck N files per chunk (0=skip)")
    p_chk.add_argument("--jobs", type=int, default=6)
    p_chk.add_argument("--allow-reset", action="store_true", help="Allow resetting working tree between chunks")

    args = ap.parse_args()
    repo = args.repo.resolve()
    work = args.work_dir.resolve()
    dump_lean = Path(__file__).resolve().parent / "Dump.lean"

    if args.cmd == "extract":
        roots = {r.strip() for r in args.roots.split(",") if r.strip()}
        keep_roots = parse_lakefile_roots(repo) | roots | {"Main", "Statements", "Challenge"}
        if not args.skip_ext_ns:
            extract_external_namespaces(repo, work / "ext_ns.txt", dump_lean, jobs=args.jobs)
        return run_extract(repo, work, dump_lean, roots, keep_roots, jobs=args.jobs, force=args.force)

    if args.cmd == "close":
        run_close_d(
            repo=repo,
            work_dir=work,
            cand_file=work / "cand.txt",
            out_set=work / "v3b_set.txt",
            out_relax=work / "v3b_relax.json",
            policy_name=args.policy,
            hard_file=args.hard.resolve() if args.hard else None,
            no_relax_file=args.no_relax.resolve() if args.no_relax else None,
        )
        return 0

    if args.cmd == "apply":
        set_p = (args.set_file or (work / "v3b_set.txt")).resolve()
        rel_p = (args.relax_file or (work / "v3b_relax.json")).resolve()
        dead = {ln.strip() for ln in set_p.read_text(encoding="utf-8").splitlines() if ln.strip()}
        apply_dead_deletions(repo, dead)
        if rel_p.is_file():
            apply_relaxations(repo, json.loads(rel_p.read_text(encoding="utf-8")))
        return 0

    if args.cmd == "split":
        out_dir = (args.out_dir or (work / "chunks")).resolve()
        split_dead_set(
            repo,
            work,
            work / "v3b_set.txt",
            work / "v3b_relax.json",
            out_dir,
            max_chunk=args.max_chunk,
            area_depth=args.area_depth,
            adaptive_depth=args.adaptive_depth,
        )
        return 0

    if args.cmd == "chunks":
        _ensure_clean_repo(repo, args.allow_reset)
        out_dir = (args.out_dir or (work / "chunks")).resolve()
        manifest = split_dead_set(
            repo,
            work,
            work / "v3b_set.txt",
            work / "v3b_relax.json",
            out_dir,
            max_chunk=args.max_chunk,
            area_depth=args.area_depth,
            adaptive_depth=args.adaptive_depth,
        )
        for chunk in manifest["chunks"]:
            cid = chunk["id"]
            dead = set(chunk["modules"])
            _ensure_clean_repo(repo, allow_reset=True)
            apply_dead_deletions(repo, dead)
            rel_p = out_dir / f"relax{cid:02d}.json"
            if rel_p.is_file():
                apply_relaxations(repo, json.loads(rel_p.read_text(encoding="utf-8")))
            diff_res = subprocess.run(["git", "diff"], cwd=str(repo), capture_output=True, text=True, check=True)
            (out_dir / f"chunk{cid:02d}.diff").write_text(diff_res.stdout, encoding="utf-8")
            if args.quickcheck_sample > 0:
                run_quickcheck(
                    repo,
                    sample_size=args.quickcheck_sample,
                    jobs=args.jobs,
                    out_json=out_dir / f"qc{cid:02d}.json",
                )
        _ensure_clean_repo(repo, allow_reset=True)
        return 0

    return 1


if __name__ == "__main__":
    raise SystemExit(main())
