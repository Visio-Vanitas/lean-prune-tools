/-
Copyright (c) 2026
Released under the MIT license as described in the file LICENSE.

Machine-checked formalization of the core graph-theoretic soundness invariants
for `lean-dead-modules` in pure Lean 4 (`Init` only; zero Mathlib imports, zero `sorry`):
1. `closeFix_sound`: Fixpoint closure terminates and leaves no kept node with an edge into `B*`.
2. `splice_preserves_reach` & `splice_preserves_acyclic`: Splicing transitive `public import`
   edges across deleted nodes preserves external reachability and acyclicity.
3. `chunk_subset_closed` & `relax_coloc_unique_owner`: Weakly-connected component splitting and
   provider co-location make any subset of chunks independently mergeable in arbitrary order.
-/

namespace DeadModuleSoundness

section GraphClosures

variable {α : Type u}

/-- Reflexive-transitive closure of a directed edge relation `R`. -/
inductive Reach (R : α → α → Prop) : α → α → Prop
  | refl (x : α) : Reach R x x
  | step {x y z : α} : R x y → Reach R y z → Reach R x z

/-- Non-empty transitive closure of `R`. -/
inductive ReachPlus (R : α → α → Prop) : α → α → Prop
  | single {x y : α} : R x y → ReachPlus R x y
  | step {x y z : α} : R x y → ReachPlus R y z → ReachPlus R x z

theorem Reach.trans {R : α → α → Prop} {x y z : α}
    (h₁ : Reach R x y) (h₂ : Reach R y z) : Reach R x z := by
  induction h₁ with
  | refl => exact h₂
  | step r _ ih => exact .step r (ih h₂)

theorem ReachPlus.trans {R : α → α → Prop} {x y z : α}
    (h₁ : ReachPlus R x y) (h₂ : ReachPlus R y z) : ReachPlus R x z := by
  induction h₁ with
  | single r => exact .step r h₂
  | step r _ ih => exact .step r (ih h₂)

theorem ReachPlus.toReach {R : α → α → Prop} {x y : α}
    (h : ReachPlus R x y) : Reach R x y := by
  induction h with
  | single r => exact .step r (.refl _)
  | step r _ ih => exact .step r ih

/-- A candidate set `B` is `Dep`-closed when no kept node (`¬ B u`) depends on any node in `B`. -/
def IsClosed (Dep : α → α → Prop) (B : α → Prop) : Prop :=
  ∀ u v, ¬ B u → Dep u v → ¬ B v

end GraphClosures

section CloseFix

private theorem filter_length_eq {α : Type u} {p : α → Bool} :
    ∀ {l : List α}, (l.filter p).length = l.length → ∀ x ∈ l, p x = true
  | [], _, _, h => nomatch h
  | a :: as, hlen, x, hx => by
    cases hpa : p a
    · rw [List.filter_cons_of_neg (by simp [hpa])] at hlen
      have hle : (as.filter p).length ≤ as.length := List.length_filter_le p as
      simp only [List.length_cons] at hlen
      omega
    · rw [List.filter_cons_of_pos hpa] at hlen
      simp only [List.length_cons] at hlen
      have hsub := filter_length_eq (Nat.succ.inj hlen)
      cases hx with
      | head => exact hpa
      | tail _ hmem => exact hsub x hmem

variable {α : Type u} [DecidableEq α] (Dep : α → α → Bool)

/-- `true` iff some node outside `cur` (a kept node) has a `Dep` edge into `v`. -/
def hasKeptDep (allNodes cur : List α) (v : α) : Bool :=
  allNodes.any fun u => !(cur.contains u) && Dep u v

/-- One fixpoint contraction step removing every candidate referenced by a kept node. -/
def closeStep (allNodes cur : List α) : List α :=
  cur.filter fun v => !hasKeptDep Dep allNodes cur v

/-- Finite fixpoint iteration converging in at most `cur.length` steps. -/
def closeFix (allNodes cur : List α) : List α :=
  if _h : (closeStep Dep allNodes cur).length < cur.length then
    closeFix allNodes (closeStep Dep allNodes cur)
  else
    cur
termination_by cur.length

theorem closeFix_subset (allNodes cur : List α) {v : α} :
    v ∈ closeFix Dep allNodes cur → v ∈ cur := by
  unfold closeFix
  split
  · intro hv
    have hv' := closeFix_subset allNodes (closeStep Dep allNodes cur) hv
    exact (List.mem_filter.mp hv').1
  · exact id
termination_by cur.length

theorem closeFix_sound (allNodes : List α) (h_univ : ∀ u, u ∈ allNodes) (cur : List α) :
    IsClosed (fun u v => Dep u v = true) (fun v => v ∈ closeFix Dep allNodes cur) := by
  unfold closeFix
  split
  · exact closeFix_sound allNodes h_univ (closeStep Dep allNodes cur)
  · rename_i hnot
    have hle : (closeStep Dep allNodes cur).length ≤ cur.length :=
      List.length_filter_le _ _
    have heq : (closeStep Dep allNodes cur).length = cur.length := by omega
    have hall : ∀ v ∈ cur, !(hasKeptDep Dep allNodes cur v) = true :=
      filter_length_eq heq
    intro u v hnu hdep hv
    have hnotkept := hall v hv
    simp only [Bool.not_eq_true'] at hnotkept
    have hany : (allNodes.any fun w => !(cur.contains w) && Dep w v) = false := hnotkept
    have hmem_u := List.any_eq_false.mp hany u (h_univ u)
    simp [hdep] at hmem_u
    exact hnu hmem_u
termination_by cur.length

end CloseFix

section PublicImportSplicing

variable {α : Type u}

/-- Directed paths inside `B` ending at a node in `B` (0 or more steps). -/
inductive ReachInB (B : α → Prop) (R : α → α → Prop) : α → α → Prop
  | refl {d : α} : B d → ReachInB B R d d
  | snoc {d x y : α} : ReachInB B R d x → R x y → B y → ReachInB B R d y

/-- Directed paths starting at `d ∈ B`, walking inside `B`, and exiting to `w ∉ B`. -/
inductive ReachThrough (B : α → Prop) (R : α → α → Prop) : α → α → Prop
  | mk {d y w : α} : B d → ReachInB B R d y → R y w → ¬ B w → ReachThrough B R d w

/-- Spliced graph on kept nodes (`¬ B`): keeps direct edges and replaces `B`-mediated paths. -/
def Splice (B : α → Prop) (R : α → α → Prop) (u w : α) : Prop :=
  ¬ B u ∧ ¬ B w ∧ (R u w ∨ ∃ d, R u d ∧ ReachThrough B R d w)

private theorem reachInB_to_reach {B : α → Prop} {R : α → α → Prop} {d y : α}
    (h : ReachInB B R d y) : Reach R d y := by
  induction h with
  | refl => exact .refl _
  | snoc _ r _ ih => exact ih.trans (.step r (.refl _))

private theorem reach_step_right {R : α → α → Prop} {x y z : α}
    (h : Reach R x y) (r : R y z) : ReachPlus R x z := by
  induction h with
  | refl => exact .single r
  | step rxy _ ih => exact .step rxy (ih r)

private theorem reachThrough_to_reachPlus {B : α → Prop} {R : α → α → Prop} {d w : α}
    (h : ReachThrough B R d w) : ReachPlus R d w := by
  cases h with
  | mk _ hdy ryw _ => exact reach_step_right (reachInB_to_reach hdy) ryw

theorem splice_implies_reachPlus {B : α → Prop} {R : α → α → Prop} {u w : α}
    (h : Splice B R u w) : ReachPlus R u w := by
  rcases h with ⟨_, _, hr | ⟨d, rud, hdw⟩⟩
  · exact .single hr
  · exact .step rud (reachThrough_to_reachPlus hdw)

theorem reachPlus_splice_implies_reachPlus {B : α → Prop} {R : α → α → Prop} {x y : α}
    (h : ReachPlus (Splice B R) x y) : ReachPlus R x y := by
  induction h with
  | single s => exact splice_implies_reachPlus s
  | step s _ ih => exact (splice_implies_reachPlus s).trans ih

theorem reach_splice_implies_reach {B : α → Prop} {R : α → α → Prop} {x y : α}
    (h : Reach (Splice B R) x y) : Reach R x y := by
  induction h with
  | refl => exact .refl _
  | step s _ ih => exact (splice_implies_reachPlus s).toReach.trans ih

private theorem reach_to_splice_aux {B : α → Prop} {R : α → α → Prop} {y w : α}
    (h : Reach R y w) :
    ∀ u, ¬ B u →
      (u = y ∨ ∃ d, B d ∧ R u d ∧ ReachInB B R d y) →
      ¬ B w → Reach (Splice B R) u w := by
  induction h with
  | refl =>
    intro u hnu hpre hnw
    rcases hpre with rfl | ⟨d, _, _, hdd⟩
    · exact .refl _
    · cases hdd with
      | refl bd => exact False.elim (hnw bd)
      | snoc _ _ bu => exact False.elim (hnw bu)
  | @step y z w ryz _ ih =>
    intro u hnu hpre hnw
    by_cases hbz : B z
    · apply ih u hnu _ hnw
      right
      rcases hpre with rfl | ⟨d, bd, rud, hdy⟩
      · exact ⟨z, hbz, ryz, .refl hbz⟩
      · exact ⟨d, bd, rud, .snoc hdy ryz hbz⟩
    · have hs : Splice B R u z := by
        refine ⟨hnu, hbz, ?_⟩
        rcases hpre with rfl | ⟨d, bd, rud, hdy⟩
        · exact Or.inl ryz
        · exact Or.inr ⟨d, rud, .mk bd hdy ryz hbz⟩
      exact .step hs (ih z hbz (Or.inl rfl) hnw)

/-- Exact reachability preservation between kept nodes (`¬ B u` and `¬ B w`). -/
theorem splice_preserves_reach {B : α → Prop} {R : α → α → Prop} {u w : α}
    (hnu : ¬ B u) (hnw : ¬ B w) :
    Reach R u w ↔ Reach (Splice B R) u w :=
  ⟨fun h => reach_to_splice_aux h u hnu (Or.inl rfl) hnw, reach_splice_implies_reach⟩

/-- Splicing cannot introduce an import cycle into an acyclic graph. -/
theorem splice_preserves_acyclic {B : α → Prop} {R : α → α → Prop}
    (hacyc : ∀ x, ¬ ReachPlus R x x) : ∀ x, ¬ ReachPlus (Splice B R) x x :=
  fun x hx => hacyc x (reachPlus_splice_implies_reachPlus hx)

end PublicImportSplicing

section ChunkSplitting

variable {α : Type u}

/-- Weakly-connected component chunking guarantees any arbitrary subset of chunks
(selected by `S : Nat → Prop`) remains `Dep`-closed when merged independently. -/
theorem chunk_subset_closed {Dep : α → α → Prop} {B : α → Prop} {chunk : α → Nat}
    (hclosed : IsClosed Dep B)
    (hwcc : ∀ u v, B u → B v → Dep u v → chunk u = chunk v)
    (S : Nat → Prop) :
    IsClosed Dep (fun m => B m ∧ S (chunk m)) := by
  intro u v hnu hdep ⟨hvb, hvs⟩
  have hbu : B u := Classical.byContradiction fun hnbu => hclosed u v hnbu hdep hvb
  have hnsu : ¬ S (chunk u) := fun hsu => hnu ⟨hbu, hsu⟩
  rw [hwcc u v hbu hvb hdep] at hnsu
  exact hnsu hvs

/-- Co-locating all candidate providers `P` in the same WCC guarantees unique chunk ownership. -/
theorem relax_coloc_unique_owner {P : α → Prop} {chunk : α → Nat}
    (hcoloc : ∀ u v, P u → P v → chunk u = chunk v)
    {u v : α} (hu : P u) (hv : P v) : chunk u = chunk v :=
  hcoloc u v hu hv

end ChunkSplitting

end DeadModuleSoundness

#print axioms DeadModuleSoundness.closeFix_sound
#print axioms DeadModuleSoundness.splice_preserves_reach
#print axioms DeadModuleSoundness.splice_preserves_acyclic
#print axioms DeadModuleSoundness.chunk_subset_closed
#print axioms DeadModuleSoundness.relax_coloc_unique_owner
