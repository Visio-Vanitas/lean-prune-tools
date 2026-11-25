#!/usr/bin/env python3
"""Selective elaboration check of modified Lean files with exact Clopper-Pearson confidence bounds."""
from __future__ import annotations

import argparse
import concurrent.futures as cf
import json
import math
import os
import random
import subprocess
import time
from pathlib import Path

DEFAULT_LEAN_OPTS = [
    "--tstack=400000",
    "-DautoImplicit=false",
    "-DrelaxedAutoImplicit=false",
    "-DmaxSynthPendingDepth=3",
    "-Dpp.unicode.fun=true",
    "-DmaxHeartbeats=4000000",
]
EXTRA_SYNTH_PREFIXES = (
    "src/GroundTheory/LocalFields/",
    "src/GroundTheory/GlobalFields/",
)


def _binom_cdf_le(x: int, n: int, p: float) -> float:
    """P(Binomial(n, p) <= x) computed stably in log-space."""
    if p <= 0.0:
        return 1.0
    if p >= 1.0:
        return 1.0 if x >= n else 0.0
    log_p = math.log(p)
    log_q = math.log1p(-p)
    lg_n1 = math.lgamma(n + 1)
    total = 0.0
    for k in range(x + 1):
        lp = lg_n1 - math.lgamma(k + 1) - math.lgamma(n - k + 1) + k * log_p + (n - k) * log_q
        total += math.exp(lp)
    return min(1.0, max(0.0, total))


def clopper_pearson_ci(x: int, n: int, alpha: float = 0.05) -> tuple[float, float]:
    """Exact two-sided (1 - alpha) Clopper-Pearson binomial confidence interval (stdlib only)."""
    if n <= 0:
        return 0.0, 1.0
    half = alpha / 2.0

    if x <= 0:
        lo = 0.0
    elif x >= n:
        lo = half ** (1.0 / n)
    else:
        a, b = 0.0, 1.0
        for _ in range(60):
            mid = 0.5 * (a + b)
            # P(X >= x) = 1 - P(X <= x - 1)
            tail = 1.0 - _binom_cdf_le(x - 1, n, mid)
            if tail < half:
                a = mid
            else:
                b = mid
        lo = 0.5 * (a + b)

    if x >= n:
        hi = 1.0
    elif x <= 0:
        hi = 1.0 - half ** (1.0 / n)
    else:
        a, b = 0.0, 1.0
        for _ in range(60):
            mid = 0.5 * (a + b)
            tail = _binom_cdf_le(x, n, mid)
            if tail > half:
                a = mid
            else:
                b = mid
        hi = 0.5 * (a + b)

    return lo, hi


def lean_opts_for_file(rel_path: str, base_opts: list[str]) -> list[str]:
    if rel_path.startswith(EXTRA_SYNTH_PREFIXES):
        return base_opts + ["-DsynthInstance.maxHeartbeats=400000"]
    return list(base_opts)


def run_quickcheck(
    repo: Path,
    *,
    sample_size: int = 400,
    seed: int = 20261125,
    jobs: int = 6,
    timeout: int = 1200,
    out_json: Path | None = None,
    files: list[str] | None = None,
    lean_opts: list[str] | None = None,
) -> dict[str, object]:
    if files is None:
        r = subprocess.run(
            ["git", "diff", "--name-only", "--diff-filter=M", "--", "src"],
            cwd=str(repo),
            capture_output=True,
            text=True,
            check=True,
        )
        all_files = sorted(f for f in r.stdout.split() if f.endswith(".lean"))
    else:
        all_files = sorted(files)

    rnd = random.Random(seed)
    sample = all_files if len(all_files) <= sample_size else rnd.sample(all_files, sample_size)

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
    base_opts = lean_opts if lean_opts is not None else DEFAULT_LEAN_OPTS

    def check_one(rel: str) -> tuple[str, str, list[str]]:
        try:
            r = subprocess.run(
                ["lean"] + lean_opts_for_file(rel, base_opts) + [rel],
                cwd=str(repo),
                capture_output=True,
                text=True,
                env=env,
                timeout=timeout,
            )
        except subprocess.TimeoutExpired:
            return rel, "timeout", []
        errs = [ln for ln in (r.stdout + r.stderr).splitlines() if ": error" in ln]
        return rel, ("ok" if r.returncode == 0 else "fail"), errs[:5]

    results = []
    t0 = time.time()
    with cf.ThreadPoolExecutor(max_workers=jobs) as ex:
        for idx, (rel, status, errs) in enumerate(ex.map(check_one, sample), 1):
            results.append({"file": rel, "status": status, "errors": errs})
            if status != "ok":
                print(f"FAIL {rel} {errs[:2]}", flush=True)
            if idx % 50 == 0:
                print(f"progress {idx}/{len(sample)} ({int(time.time() - t0)}s)", flush=True)

    n = len(results)
    x = sum(1 for item in results if item["status"] != "ok")
    lo, hi = clopper_pearson_ci(x, n, alpha=0.05)
    summary = {
        "population": len(all_files),
        "sample": n,
        "seed": seed,
        "fails": x,
        "rate": (x / n) if n else 0.0,
        "ci95": [lo, hi],
        "expected_failing_files": [lo * len(all_files), hi * len(all_files)],
        "secs": int(time.time() - t0),
    }
    payload = {"summary": summary, "results": results}
    if out_json is not None:
        out_json.parent.mkdir(parents=True, exist_ok=True)
        out_json.write_text(json.dumps(payload, indent=1), encoding="utf-8")
    print("QC_RESULT", json.dumps(summary), flush=True)
    return payload


def main() -> int:
    ap = argparse.ArgumentParser(description="Sampled Lean elaboration check on modified files.")
    ap.add_argument("--repo", type=Path, required=True, help="Path to Lean project repository")
    ap.add_argument("--sample", type=int, default=400, help="Max sample size (default: 400)")
    ap.add_argument("--seed", type=int, default=20261125, help="RNG seed (default: 20261125)")
    ap.add_argument("--jobs", type=int, default=6, help="Parallel Lean workers (default: 6)")
    ap.add_argument("--timeout", type=int, default=1200, help="Per-file timeout seconds (default: 1200)")
    ap.add_argument("--out-json", type=Path, default=None, help="Output JSON report path")
    ap.add_argument("--lean-opt", action="append", default=None, help="Override base Lean flags (repeatable)")
    args = ap.parse_args()

    out_json = args.out_json.resolve() if args.out_json else Path("qc_sample.json").resolve()
    run_quickcheck(
        args.repo.resolve(),
        sample_size=args.sample,
        seed=args.seed,
        jobs=args.jobs,
        timeout=args.timeout,
        out_json=out_json,
        lean_opts=args.lean_opt,
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
