#!/usr/bin/env python3
"""Compare quickcheck failures against unpatched HEAD to isolate patch-caused errors."""
from __future__ import annotations

import argparse
import concurrent.futures as cf
import json
import os
import subprocess
import tempfile
import time
from pathlib import Path

from quickcheck import DEFAULT_LEAN_OPTS, lean_opts_for_file


def _fails_from_qc_json(qc_json: Path) -> list[str]:
    data = json.loads(qc_json.read_text(encoding="utf-8"))
    results = data.get("results", data if isinstance(data, list) else [])
    return sorted({item["file"] for item in results if item.get("status") != "ok"})


def _fails_from_qc_log(qc_log: Path) -> list[str]:
    return sorted(
        {
            ln.split()[1]
            for ln in qc_log.read_text(encoding="utf-8").splitlines()
            if ln.startswith("FAIL ") and len(ln.split()) >= 2
        }
    )


def run_basecheck(
    repo: Path,
    fails: list[str],
    *,
    base_dir: Path | None = None,
    jobs: int = 4,
    timeout: int = 1800,
    out_json: Path | None = None,
    base_ref: str = "HEAD",
) -> list[dict[str, object]]:
    env = dict(os.environ)
    lp = subprocess.run(
        ["lake", "env", "printenv", "LEAN_PATH"],
        cwd=str(repo),
        capture_output=True,
        text=True,
        env=env,
        check=True,
    )
    env["LEAN_PATH"] = lp.stdout.strip()

    def eval_one(rel: str, target_path: str) -> tuple[str, list[str]]:
        try:
            r = subprocess.run(
                ["lean"] + lean_opts_for_file(rel, DEFAULT_LEAN_OPTS) + [target_path],
                cwd=str(repo),
                capture_output=True,
                text=True,
                env=env,
                timeout=timeout,
            )
        except subprocess.TimeoutExpired:
            return "timeout", []
        errs = [ln for ln in (r.stdout + r.stderr).splitlines() if ": error" in ln]
        return ("ok" if r.returncode == 0 else "fail"), errs[:3]

    with tempfile.TemporaryDirectory() as td_str:
        stage_dir = base_dir if base_dir is not None else Path(td_str)
        stage_dir.mkdir(parents=True, exist_ok=True)

        def job(rel: str) -> dict[str, object]:
            orig_copy = stage_dir / rel.replace("/", "__")
            show = subprocess.run(
                ["git", "show", f"{base_ref}:{rel}"],
                cwd=str(repo),
                capture_output=True,
                text=True,
                check=True,
            )
            orig_copy.write_text(show.stdout, encoding="utf-8")
            patched_st, patched_err = eval_one(rel, rel)
            orig_st, orig_err = eval_one(rel, str(orig_copy))
            return {
                "file": rel,
                "patched": patched_st,
                "orig": orig_st,
                "perr": patched_err,
                "oerr": orig_err,
            }

        out: list[dict[str, object]] = []
        t0 = time.time()
        with cf.ThreadPoolExecutor(max_workers=jobs) as ex:
            for item in ex.map(job, fails):
                out.append(item)
                print(f"BC patched={item['patched']} orig={item['orig']} {item['file']}", flush=True)

    if out_json is not None:
        out_json.parent.mkdir(parents=True, exist_ok=True)
        out_json.write_text(json.dumps(out, indent=1), encoding="utf-8")

    caused = sum(1 for d in out if d["patched"] != "ok" and d["orig"] == "ok")
    print(
        f"BC_SUMMARY n={len(out)} patched_fail={sum(d['patched'] != 'ok' for d in out)} "
        f"orig_fail={sum(d['orig'] != 'ok' for d in out)} caused_by_patch={caused} secs={int(time.time() - t0)}",
        flush=True,
    )
    return out


def main() -> int:
    ap = argparse.ArgumentParser(description="Compare failed quickcheck files against unpatched HEAD.")
    ap.add_argument("--repo", type=Path, required=True, help="Path to Lean project repository")
    ap.add_argument("--qc-json", type=Path, default=None, help="Path to quickcheck JSON output")
    ap.add_argument("--qc-log", type=Path, default=None, help="Path to quickcheck text log")
    ap.add_argument("--base-dir", type=Path, default=None, help="Optional staging dir for baseline copies")
    ap.add_argument("--base-ref", default="HEAD", help="Git ref for baseline file content (default: HEAD)")
    ap.add_argument("--jobs", type=int, default=4, help="Parallel Lean workers (default: 4)")
    ap.add_argument("--timeout", type=int, default=1800, help="Per-file timeout seconds (default: 1800)")
    ap.add_argument("--out-json", type=Path, default=None, help="Output basecheck JSON path")
    args = ap.parse_args()

    if args.qc_json:
        fails = _fails_from_qc_json(args.qc_json.resolve())
    elif args.qc_log:
        fails = _fails_from_qc_log(args.qc_log.resolve())
    else:
        ap.error("Provide --qc-json or --qc-log")

    out_json = args.out_json.resolve() if args.out_json else Path("basecheck.json").resolve()
    run_basecheck(
        args.repo.resolve(),
        fails,
        base_dir=args.base_dir.resolve() if args.base_dir else None,
        jobs=args.jobs,
        timeout=args.timeout,
        out_json=out_json,
        base_ref=args.base_ref,
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
