# Mathematical Derivation & Code Review (`olean-prune`)

## 1. Why Reachability Alone Over-Counts (and Fails to Compile)

Let $G_{\text{const}} = (V_{\text{decl}}, E_{\text{const}})$ be the exact project constant dependency graph extracted from `.olean`, `.olean.server`, and `.olean.private`, where $(u, v) \in E_{\text{const}}$ holds iff constant $v$ appears in the type, value, constructor list, or recursor rules of constant $u$. Let $R_{\text{decl}} \subseteq V_{\text{decl}}$ be the declarations of the root modules (`Main`, `Statements`), and let $\text{Reach}(R_{\text{decl}})$ be the set of constants reachable from $R_{\text{decl}}$ in $G_{\text{const}}$.

Define the initial unreachable candidate modules:
$$B_0 = \{ m \in M \mid m \notin M_{\text{protected}} \;\land\; \forall c \in \text{Decl}(m),\ c \notin \text{Reach}(R_{\text{decl}}) \}.$$

Deleting $B_0$ directly (even after splicing `public import`s) **fails to compile** because module compilation requires elaborating **all** code inside kept modules $K = M \setminus B$, including:

1. **Dead declarations inside live modules**: A kept module $m \in K$ may contain a declaration $d \notin \text{Reach}(R_{\text{decl}})$ whose proof or body depends on $c \in \text{Decl}(b)$ for $b \in B_0$. When Lean elaborates $m$, removing $b$ breaks $d$.
2. **Type/binder-only source references (`text-ref`)**: A kept file $m \in K$ may reference a constant $c \in \text{Decl}(b)$ in `variable (x : c)` or unused notation without creating any kept constant edge.
3. **Selective / renamed / hidden namespace items**: `open NS (a b)`, `open NS hiding a`, or `open NS renaming a → b` require `NS.a` and `NS.b` to exist in the environment even when `NS` itself remains provided by another module in $K$.
4. **Non-constant command effects (`export`, `scoped`, attributes)**: `export NS (a)` creates alias names without constant graph nodes; `scoped` declarations register scoped notations, instances, macros, or attributes; and zero-constant modules can still run `attribute [...]` commands.

---

## 2. Soundness of the `closeD` Fixpoint Iteration

Starting from $B^{(0)} = B_0 \setminus M_{\text{export/scoped}}$, `closeD` computes a monotone descending chain $B^{(0)} \supseteq B^{(1)} \supseteq \dots \supseteq B^*$ inside the finite module set $M$. At step $t$, let $K^{(t)} = M \setminus B^{(t)}$, and collect the drop set $\Delta^{(t)} \subseteq B^{(t)}$ from four conditions:

1. **Constant boundary crossing**:
   $$\exists (s, d) \in E_{\text{const}} : \text{mod}(s) \in K^{(t)} \;\land\; \text{mod}(d) \in B^{(t)} \implies \text{mod}(d) \in \Delta^{(t)}.$$
2. **`open`/`export` namespace edges**: For each $m \in K^{(t)}$ and namespace token $\tau$ opened in $m$, if every provider of a matching namespace in $m$'s strict `public import` visibility closure lies in $B^{(t)}$ (and $\tau$ is not external), then policy either **relaxes** $(m, \tau)$ (`apply_relax.py` removes dead token $\tau$) or **keeps** all providers in $\Delta^{(t)}$ (e.g. when the token's visibility path wasn't modeled).
3. **Source `text-ref` edges**: For each $m \in K^{(t)}$ and source identifier or selective `open`/`export` item `(NS.x)` whose visible candidate providers in $m$'s transitive import closure lie in $B^{(t)}$, if no visible module in $K^{(t)}$ also provides the same suffix, all candidate providers in $B^{(t)}$ are added to $\Delta^{(t)}$.
4. **Zero-constant imports**: For each $m \in K^{(t)}$ importing $x \in B^{(t)}$ with $|\text{Decl}(x)| = 0$, if $x$ is not syntactically inert (only `module`, `import`, `open`, `namespace`/`section`/`end`, `set_option`), $x \in \Delta^{(t)}$.

**Termination & Monotonicity**: Because $M$ is finite and $B^{(t+1)} = B^{(t)} \setminus \Delta^{(t)}$ shrinks strictly until $\Delta^{(t)} = \emptyset$, termination is guaranteed in at most $|B_0|$ iterations (typically 2–4 iterations in practice). Every module removed from $B$ moves to $K$, strictly enlarging visible kept providers; therefore re-evaluating `text-ref` and `open-namespace` at each step ensures the final $(B^*, \text{relax}^*)$ has zero modeled unresolved constant edges, zero unresolved `text-ref` identifiers, and zero unrelaxed dead `open` namespaces across all $K^* = M \setminus B^*$. Mechanized in [`DeadModuleSoundness.closeFix_sound`](Soundness.lean).

---

## 3. Lean 4 `public import` Splicing Invariant (`del_dead2.py`)

Under Lean 4's module system, a kept file $m$ importing $d \in B^*$ directly sees constants transitively exported by $d$ via **`public import` edges** (`import_pub`). A private import inside $d$ is not re-exported to $m$.

Let $I_{\text{pub}}(d)$ denote the transitive closure of `public import` paths starting at $d$ that terminate in $K^*$ (avoiding cycles via `seen`). Replacing every `import d` in $m$ by $I_{\text{pub}}(d)$:
- preserves visibility of every declaration in $K^*$ transitively visible to $m$ prior to deleting $d$,
- preserves `public` / `meta` / `all` visibility attributes (and upgrades an existing `private import x` in $m$ when `public import d` brings in `x` publicly), and
- cannot introduce cycles into $G[K^*]$ because any path $m \to_{\text{imp}} x$ added by splicing already existed as $m \to d \to_{\text{pub}}^* x$ in $G_{\text{before}}$, which was acyclic.

Mechanized for abstract graphs in [`DeadModuleSoundness.splice_preserves_reach`](Soundness.lean) and [`DeadModuleSoundness.splice_preserves_acyclic`](Soundness.lean).

---

## 4. Chunk Independence & Co-Location Theorem (`split.py`)

To split $B^*$ into chunks $C_1, \dots, C_k$ such that **any subset** of chunks can be merged independently in **any order** without compile breakage:

Suppose chunk $C_i$ is merged while $C_j$ ($j \neq i$) has not yet merged (so modules in $C_j$ remain in the repository and must still elaborate cleanly). A conflict occurs if either:
1. $u \in C_j$ has a constant, `text-ref`, or `open` dependency on $v \in C_i$ (which `split.py` prevents by placing all weakly connected components of intra-$B^*$ constant/text-ref/`open` edges into the **same** chunk), OR
2. a kept file $f \in K^*$ has an `open` token $\tau \in \text{relax}^*(f)$ with providers in multiple modules $v_1, v_2 \in B^*$: if $v_1 \in C_1$ and $v_2 \in C_2$ ($C_1 \neq C_2$), then stripping $\tau$ in $C_1$ breaks $f$'s use of $v_2$ while $C_2$ is unmerged, or stripping $\tau$ in both chunks creates a duplicate edit/conflict.

**Fix implemented in `split.py`**: `split.py` unions all candidate providers $\{v \in B^* \mid v \text{ provides } \tau\}$ into one WCC **before** packing chunks. Consequently, every $(f, \tau)$ in `relax*` maps to a **unique** chunk $C_k$, guaranteeing zero cross-chunk `open`-line conflicts and safe arbitrary-order merging. Mechanized in [`DeadModuleSoundness.chunk_subset_closed`](Soundness.lean) and [`DeadModuleSoundness.relax_coloc_unique_owner`](Soundness.lean).

---

## 5. Comprehensive Code Review & Fixes Applied

| # | File | Issue Found in Prototype | Fix Applied in Release Version |
|---|---|---|---|
| 1 | `Dump.lean` | `deps` mode called `readModuleDataParts` without calling `region.free`, leaking `CompactedRegion` mmaps across ~60k modules. | Added `for (_, region) in res.reverse do region.free` after reading constants in `deps` mode. |
| 2 | `load.py` | Hardcoded fixed scratch-directory glob for `.tsv` files, silently loading 0 rows when `--work-dir` differed. | Parameterized `--deps-dir`, `--work-dir`, and `--db` with explicit error-free loading. |
| 3 | `extract.py` | Hardcoded fixed container paths, wrote scratch files into tools dir, invoked non-existent `closeB.py`, and parsed imports without block-comment awareness. | Fully parameterized CLI, `TemporaryDirectory` for scratch files, nested-comment-safe `parse_lean_imports`, and removed broken `closeB.py` call. |
| 4 | `closeD.py` | Non-nested `re.sub(r'/-.*?-/')` broke nested Lean block comments, hardcoded absolute path for `names*.txt`, and contained internal path/handle notes. | Replaced with stack-based `strip_lean_comments`, resolved `names.txt` via `--work-dir`, and stripped all non-public identifiers. |
| 5 | `closeD.py` | Verified Unicode (`\u0370-\u03ff`, `\u2080-\u2089`), `hiding`, and `renaming` arrow entry parsing in `open`/`export` lists. | Unified Unicode regexes in `OPEN_TOK_RE` / `CLAUSE_WITH_LIST_RE` and split `→`/`->` entries so only source symbols are checked. |
| 6 | `apply_relax.py` | Filtering `'hiding'` unconditionally turned `open A B hiding x` into invalid Lean syntax `open B x` and orphaned hidden identifiers. | Implemented clause-aware `_split_open_clauses` (preserving sibling `hiding`/`renaming`/`(...)` clauses) plus block-comment awareness. |
| 7 | `del_dead2.py` | Loaded unused `G_before.json`, matched commented-out imports inside block comments, dropped `meta`/`all` import flags, and failed if `scripts/clump-exclude.txt` was absent. | Removed dead code, parsed imports after `strip_lean_comments`, preserved `meta`/`all` modifiers, and guarded `clump-exclude.txt`. |
| 8 | `split.py` | Relaxed tokens with multiple providers in $B^*$ could assign identical `(file, token)` relaxations to multiple chunks; `--area-depth` was fixed at `1`. | Added `relax_coloc` union-find edges ensuring single-chunk ownership of every relaxed token, plus `--adaptive-depth` sub-area clustering. |
| 9 | `quickcheck.py`, `basecheck.py`, `ext_ns.py`, shell scripts | Hardcoded fixed absolute workspace paths, Linux `sysctl`, and required third-party `scipy` just for Clopper-Pearson intervals. | Replaced `scipy` with pure-stdlib log-binomial Clopper-Pearson bisection (`clopper_pearson_ci`), replaced wrapper shell scripts with cross-platform `pipeline.py`, and parameterized all CLIs. |
| 10 | `del_dead2.py` | Splicing a deleted module's `public import` blindly copied targets that upstream had already removed since candidate generation (causing `no such file` / `bad import` cascades). | Added `discover_project_dir_roots` + `is_missing_project_module` filtering during splicing plus `verify_no_dangling_project_imports` post-rewrite verification gate. |
