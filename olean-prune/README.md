# `olean-prune`

Compiled constant-graph dead-module detection, dependency-closed fixpoint refinement (`closeD`), public-import splicing (`del_dead2`), and chunk-independent splitting (`split`) for large Lean 4 repositories. (See [root README](../README.md) and [Apache License 2.0](../LICENSE).)

## What Problem This Solves
1. **Exact constant-graph reachability (`Dump.lean`, `extract.py`, `load.py`, `reach.py`)**:
   Reads `.olean`, `.olean.server`, and `.olean.private` (including proof terms and private declarations) via `Lean.readModuleDataParts`, and marks everything reachable from the configured root modules (`--roots`, auto-detected from `lakefile.toml` / `lakefile.lean` by default).
2. **Dependency-closed fixpoint (`closeD.py`)**:
   Refines candidates over dependencies invisible to plain constant reachability:
   - hard constant edges originating from dead code inside kept modules;
   - `export` commands and `scoped` declarations;
   - source text references (e.g. `variable (E : T)`, `open NS (a b)`, `open NS hiding x`, `open NS renaming a → b`);
   - non-inert zero-constant modules (e.g. `attribute [...]` modules);
   - namespace `open` / `export` lines (kept or conservatively relaxed via `apply_relax.py` + `ext_ns.py`).
3. **Module deletion and `public import` splicing (`del_dead2.py`)**:
   Replaces every removed `import Dead` in kept files with `Dead`'s transitive `public import` closure while preserving `meta`/`all` modifiers and upgrading `private` imports when required by `public import`.
4. **Independent chunk splitting (`split.py`, `pipeline.py`)**:
   Partitions the closed deletion set into weakly connected components (including co-located relaxed namespace providers) grouped by directory prefix so chunks can merge independently in any order.
5. **Selective elaboration check (`quickcheck.py`, `basecheck.py`)**:
   Zero-dependency Python 3.9+ elaboration sampler with exact two-sided Clopper-Pearson confidence intervals and unpatched-`HEAD` baseline comparison.

## Explicit Limitations (What Is Not Modeled)
- Downstream unedited files are not rebuilt automatically; typeclass synthesis changes, global `@[simp]`/`@[ext]` priority shifts, or macro/elaborator side effects can only be ruled out by a full `lake build Main`.
- Always run a full `lake build` before marking a generated cleanup PR ready for review.
- Distinct from [`import-index`](../import-index/README.md) (which builds a fast source-level syntactic import index without `.olean` artifacts).

## Prerequisites
- Python 3.9+ (pure standard library — no `scipy` or third-party packages required)
- Lean 4 toolchain (`lean` + `lake` matching the target repository's `lean-toolchain`)
- A built Lean project cache/build (e.g. `lake exe cache get && lake build Main`) for `.olean`/`.olean.private` extraction

## Quickstart

```bash
# 1. Extract external namespaces + exact .olean constant graph into ./work (roots auto-detected from lakefile)
python3 pipeline.py --repo /path/to/lean-project --work-dir ./work extract --jobs 8 --force

# 2. Compute fixpoint-closed deletion set and open-line relaxations
python3 pipeline.py --repo /path/to/lean-project --work-dir ./work close

# 3. Apply the full patch OR split into independent per-directory chunk diffs
python3 pipeline.py --repo /path/to/lean-project --work-dir ./work split --max-chunk 40 --adaptive-depth
python3 pipeline.py --repo /path/to/lean-project --work-dir ./work chunks --max-chunk 40 --adaptive-depth --allow-reset

# 4. Run selective elaboration checks on modified files (stdlib-only Clopper-Pearson CI)
python3 quickcheck.py --repo /path/to/lean-project --sample 400 --jobs 6 --out-json ./work/qc.json
python3 basecheck.py --repo /path/to/lean-project --qc-json ./work/qc.json --out-json ./work/basecheck.json
```

See [DERIVATION_AND_REVIEW.md](DERIVATION_AND_REVIEW.md) for the mathematical soundness derivation and code review notes.

## Mathematical Soundness & Formal Verification
- **Written Derivation & Code Review**: [DERIVATION_AND_REVIEW.md](DERIVATION_AND_REVIEW.md) — covers [reachability vs. `closeD` fixpoint soundness](DERIVATION_AND_REVIEW.md#2-soundness-of-the-closed-fixpoint-iteration), [`public import` splicing preservation](DERIVATION_AND_REVIEW.md#3-lean-4-public-import-splicing-invariant-del_dead2py), [chunk-independence & co-location](DERIVATION_AND_REVIEW.md#4-chunk-independence--co-location-theorem-splitpy), and the [10-item engineering review log](DERIVATION_AND_REVIEW.md#5-comprehensive-code-review--fixes-applied).
- **Lean 4 Formalization (`Init` only, zero `sorry`)**: [Soundness.lean](Soundness.lean) — machine-checked proofs of:
  - `DeadModuleSoundness.closeFix_sound`: finite termination and `Dep`-closure of the fixpoint contraction;
  - `DeadModuleSoundness.splice_preserves_reach` & `DeadModuleSoundness.splice_preserves_acyclic`: `public import` splicing preserves external reachability and cannot introduce cycles;
  - `DeadModuleSoundness.chunk_subset_closed` & `DeadModuleSoundness.relax_coloc_unique_owner`: arbitrary-order merge safety across WCC chunks and unique chunk ownership for co-located relaxed providers.

## Interoperability with Read-Only Analyzers
Read-only Lean `MetaM` analyzers (such as `lake exe deadWeight`) report plain unreachable modules/declarations/fields from a single in-memory `Environment` pass. `olean-prune` supplies the downstream streaming `.olean`/`.olean.private` extraction, `closeD` fixpoint closure (catching dead-code-in-live-modules, `text-ref`, `open`/`export`/`scoped`), `public import` splicing with missing-module guards, and dependency-closed chunk splitting required to produce merge-ready cleanup PRs.

## Running Unit Tests

```bash
python3 -m unittest discover -v
```
