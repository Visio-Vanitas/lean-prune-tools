# `import-index`

Zero-dependency Python 3.9+ tools for maintaining a fast, incremental SQLite module import-graph index over large Lean 4 repositories (~61k+ `.lean` files under `src/`) without building `.olean` artifacts. (See [root README](../README.md) and [MIT License](../LICENSE).)

## What Problem This Solves
- **Incremental SQLite module index (`import_index.py`)**: Streams all `src/**/*.lean` blobs through `git cat-file --batch` (~4–10s full build, <0.5s incremental `sync`), handling nested `/- ... -/` block comments and `public`/`private`/`meta`/`import all` syntax.
- **Millisecond structural queries (`import_index.py`)**:
  - `rev`: direct importers and transitive reverse cone (all the way to `Main` / `Statements` / `Challenge`).
  - `cycle`: cycle check before adding `src -> dst`.
  - `peel`: fixed-point orphan cascade computation when severing imports or dropping subtrees (`--check-symbols` inspects Lean sources for secondary exported symbol references).
  - `audit-diff`: `<1s` branch diff verification checking dangling imports across untouched files, import cycles, `git merge-tree` cleanliness, protected files, `sorry`/`admit`/`axiom`, and optional `--forbid-pattern` / `--forbid-file` rules.
- **Cleanup discovery (`big_pr_hunter.py`)**: Structural scanners over source syntax and the import graph (`duplicate-stems`, `chokepoints`, `dom-pillars`, `published-dups`, `neg-instances`, `heavy-pillars`, `unused-fields`, `decl-dups`, `ignored-bundle-args`, `vacuous-defs`, `unreferenced-decls`).
- **Refactor planning (`strip_planner.py`)**: Plans bundle-field pruning (`bundle-field`), duplicate-subtree replacement (`subtree-replace`), and unused-import checks (`unused-imports`).

## What This Does **Not** Do
- It operates on **module-level syntax and imports**, not elaborated Lean terms or compiled `.olean` constant graphs.
- Syntactic scans cannot detect semantic dependencies carried solely via elaborated typeclasses, `simp` lemmas, macros, or `open`/`export` namespaces without running `lean` / `lake build`. Always verify candidate edits with `lake build` before submitting changes.
- Distinct from [`olean-prune`](../olean-prune/README.md) (the compiled constant-graph reachability and `closeD` fixpoint pipeline).

## Quickstart

```bash
# 1. Build or incrementally sync the SQLite import index (stored at ~/.cache/rh-import-index/import_index.db by default)
python3 import_index.py --repo /path/to/riemann-hypothesis sync --ref origin/main

# 2. Check index metadata and remote freshness
python3 import_index.py stats --check-remote

# 3. Query reverse cone or cycle risk
python3 import_index.py rev My.Module.Name
python3 import_index.py cycle Src.Module Dst.Module

# 4. Compute fixed-point orphan cascade for edge cuts or module drops
python3 import_index.py peel HostModule --drop DepA,DepB --check-symbols
python3 import_index.py peel --drop-modules Mod1,Mod2 --mode reach-main

# 5. Audit a branch diff before opening or updating a PR
python3 import_index.py --repo /path/to/riemann-hypothesis audit-diff origin/main HEAD
```

## Cleanup Scanners & Planners

`--repo`, `--db`, and `--ref` are top-level options placed **before** the subcommand (`--repo` reuses the stored `repo_root` when omitted after `sync`):

```bash
python3 big_pr_hunter.py duplicate-stems --min-lines 1500 --limit 25
python3 big_pr_hunter.py chokepoints --min-lines 3000 --max-cone 25 --limit 30
python3 big_pr_hunter.py dom-pillars --min-lines 10000 --max-host-cone 35 --only-multi-edge
python3 big_pr_hunter.py unused-fields --max-readers 0 --limit 25
python3 big_pr_hunter.py decl-dups --prefix Development.WeilBound
python3 big_pr_hunter.py unreferenced-decls --max-cone 10 --limit 50

python3 strip_planner.py bundle-field --struct MyBundle --fields f1,f2
python3 strip_planner.py subtree-replace --drop-prefix My.Duplicate.Subtree
python3 strip_planner.py unused-imports --base origin/main --head HEAD
```

## Running Unit Tests

```bash
python3 -m unittest discover -v
```

## Design & Static Invariants
- **Exact fixed-point orphan peel (`peel`)**: Removes cut edges `(Host, Dep)` and iteratively prunes only modules whose remaining incoming project import count reaches `0` (or loses all paths to `Main` under `--mode reach-main`), verifying `survivor_dangling_edges == 0` on the surviving subgraph.
- **Branch diff verification (`audit-diff`)**: Verifies `merge-tree` cleanliness, zero introduced import cycles (`cycle_free == True`), zero edits to protected files, and zero dangling imports—covering both PR-deleted modules and imports targeting project-directory modules already absent on `base` (without false positives on external packages such as `Mathlib.*`).
