# lean-prune-tools

Zero-dependency Python 3.9+ standard-library tools (plus Lean 4 extractors and machine-checked soundness proofs) for analyzing, pruning, and splitting dead code in large Lean 4 repositories.

## Packages

- **[`olean-prune/`](olean-prune/README.md)** — Compiled `.olean`/`.olean.private` constant-graph dead-module pruner:
  - Extracts declaration-level constant dependencies (`Dump.lean`, `extract.py`, `load.py`, `reach.py`) with incremental per-module hashing.
  - Computes the dependency-closed fixpoint [`closeD.py`](olean-prune/closeD.py) over hard edges, source `text-ref` identifiers, `open`/`export` clauses (`NS (a b)`, `hiding`, `renaming`), `scoped` declarations, and zero-constant modules.
  - Splices transitive `public import`s ([`del_dead2.py`](olean-prune/del_dead2.py)) while filtering modules already deleted upstream and verifying zero dangling project imports, safely strips dead `open` tokens ([`apply_relax.py`](olean-prune/apply_relax.py)), and splits into dependency-closed chunks ([`split.py`](olean-prune/split.py), [`pipeline.py`](olean-prune/pipeline.py)) with stdlib Clopper-Pearson selective checks ([`quickcheck.py`](olean-prune/quickcheck.py)).
  - Includes the written derivation & 10-item review ([`olean-prune/DERIVATION_AND_REVIEW.md`](olean-prune/DERIVATION_AND_REVIEW.md)) and core-Lean-only formalization ([`olean-prune/Soundness.lean`](olean-prune/Soundness.lean), `Init`-only, zero `sorry`).

- **[`import-index/`](import-index/README.md)** — Fast source-level SQLite module import-graph index & refactor planner:
  - Streams `src/**/*.lean` via `git cat-file --batch` into SQLite (~61k files in seconds, `<0.5s` incremental `sync`) for millisecond reverse-cone (`rev`), cycle (`cycle`), fixed-point orphan cascade (`peel --check-symbols`), and branch diff audits (`audit-diff`, catching both PR-deleted modules and spliced imports absent on `base`).
  - Includes structural cleanup scanners ([`big_pr_hunter.py`](import-index/big_pr_hunter.py)) and refactor planners ([`strip_planner.py`](import-index/strip_planner.py)).

## Running Unit Tests

```bash
python3 -m unittest discover -s olean-prune -v
python3 -m unittest discover -s import-index -v
```

## License

Released under the [Apache License 2.0](LICENSE).
