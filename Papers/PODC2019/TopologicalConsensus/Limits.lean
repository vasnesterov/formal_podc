import Papers.PODC2019.TopologicalConsensus.Characterization
import Papers.PODC2019.TopologicalConsensus.ProductTopology

/-!
# Limit-based consensus characterization (Section 6)

All topologies here are the ones of `Characterization.lean`: `M.τNU`, `M.τUc`, `M.τU` on the set
`Σ = M.adm` of admissible executions, induced by the (non-metric) distances restricted to `Σ`.

* `lemma_6_3` (Separation Lemma, for finite partitions): all fibres of `lab : X → V` (`V` finite)
  are clopen iff no fibre contains a limit (accumulation) point of another fibre;
  `isClopen_fibers_iff_closure` is the same with closures, `isClopen_iff_separation` the paper's
  two-set version.
* `theorem_6_4_nonUniform` / `theorem_6_4_uniform` (Theorem 6.4, under `LockstepRecall`):
  consensus is solvable iff there is a labelling with validity such that no decision set contains a
  limit point of another (w.r.t. `τNU`, resp. the corrected uniform topology `τUc`;
  `theorem_6_4_uniform_faultFree` gives the paper's `τU` version for fault-free models).
* `SetDistZero d A B`: the set distance `d(A, B) = inf {d(α, β) | α ∈ A, β ∈ B}` (Definition 6.1)
  is `0`, in the junk-free form `∀ ε > 0, ∃ α ∈ A, β ∈ B, d(α, β) < ε` (for empty `A` or `B` it is
  false, matching `inf ∅ = +∞`); `setDistZero_iff_sInf` relates it to `sInf`.
* `corollary_6_5_nonUniform` / `corollary_6_5_uniform` (Corollary 6.5, second sentence): if for a
  labelling with validity all decision sets have positive pairwise distance, consensus is solvable.
* `theorem_6_4_setDist_nonUniform` / `..._uniform` (last sentence of Theorem 6.4): if consensus is
  not solvable, then for *every* labelling with validity there are `v ≠ w` with
  `d(Σ_v, Σ_w) = 0`.
* `ClosureCounterexample.closure_not_setDistZero`: for a non-metric distance, a point in the closure
  of `B` can have positive distance to `B`, so the paper's sequence argument for the last sentence
  of Theorem 6.4 (via Lemma 6.2) does not apply; we prove it via the contrapositive instead.
-/

namespace TopoConsensus

open Set Filter Topology

set_option linter.unusedSectionVars false

/-! ### Lemma 6.3 (Separation Lemma) -/

section Separation

variable {X V : Type*} [TopologicalSpace X]

/-- For a point outside `s`, being in the closure of `s` is being a limit point of `s`. -/
theorem mem_closure_iff_accPt_of_notMem {x : X} {s : Set X} (hx : x ∉ s) :
    x ∈ closure s ↔ AccPt x (𝓟 s) := by
  rw [mem_closure_iff_clusterPt, accPt_principal_iff_clusterPt, sdiff_singleton_eq_self hx]

/-- Lemma 6.3 for finite partitions, closure form: all fibres of `lab` are clopen iff every point
in the closure of a fibre `lab⁻¹{w}` has label `w`. -/
theorem isClopen_fibers_iff_closure [Finite V] (lab : X → V) :
    (∀ w, IsClopen (lab ⁻¹' {w})) ↔ ∀ x w, x ∈ closure (lab ⁻¹' {w}) → lab x = w := by
  constructor
  · intro h x w hx
    rw [(h w).1.closure_eq] at hx
    exact hx
  · intro h
    have hcl : ∀ w, IsClosed (lab ⁻¹' {w}) := fun w =>
      closure_subset_iff_isClosed.1 fun x hx => h x w hx
    intro w
    refine ⟨hcl w, ?_⟩
    rw [← isClosed_compl_iff]
    have : (lab ⁻¹' {w})ᶜ = ⋃ u ∈ ({w}ᶜ : Set V), lab ⁻¹' {u} := by
      ext x; simp [eq_comm]
    rw [this]
    exact (Set.toFinite _).isClosed_biUnion fun u _ => hcl u

/-- **Lemma 6.3** (Separation Lemma, for a partition into finitely many parts): all parts
`lab⁻¹{w}` are clopen iff no part contains a limit point of another part. -/
theorem lemma_6_3 [Finite V] (lab : X → V) :
    (∀ w, IsClopen (lab ⁻¹' {w})) ↔ ∀ x w, lab x ≠ w → ¬ AccPt x (𝓟 (lab ⁻¹' {w})) := by
  rw [isClopen_fibers_iff_closure]
  refine forall₂_congr fun x w => ?_
  by_cases h : lab x = w
  · simp [h]
  · rw [mem_closure_iff_accPt_of_notMem (s := lab ⁻¹' {w}) h]
    simp [h]

/-- **Lemma 6.3** in the paper's two-set form: `A` and `Aᶜ` are clopen iff neither contains a limit
point of the other. -/
theorem isClopen_iff_separation (A : Set X) :
    IsClopen A ↔ (∀ x ∈ A, ¬ AccPt x (𝓟 Aᶜ)) ∧ ∀ x ∈ Aᶜ, ¬ AccPt x (𝓟 A) := by
  have key : ∀ B : Set X, (∀ x ∈ Bᶜ, ¬ AccPt x (𝓟 B)) ↔ IsClosed B := by
    intro B
    rw [← closure_subset_iff_isClosed]
    constructor
    · intro h x hx
      by_contra hxB
      exact h x hxB ((mem_closure_iff_accPt_of_notMem hxB).1 hx)
    · intro h x hx hacc
      exact hx (h ((mem_closure_iff_accPt_of_notMem hx).2 hacc))
  have h1 := key Aᶜ
  rw [compl_compl] at h1
  rw [h1, key A, isClosed_compl_iff, IsClopen, and_comm]

end Separation

/-! ### Set distances (Definition 6.1) -/

/-- `d(A, B) = 0` for the set distance `d(A, B) = inf {d(α, β) | α ∈ A, β ∈ B}` of
Definition 6.1, stated without junk values: for every `ε > 0` there are `α ∈ A`, `β ∈ B` with
`d(α, β) < ε`. (If `A` or `B` is empty this is false, matching `inf ∅ = +∞`.) -/
def SetDistZero {X : Type*} (d : X → X → ℝ) (A B : Set X) : Prop :=
  ∀ ε > 0, ∃ α ∈ A, ∃ β ∈ B, d α β < ε

/-- For a nonnegative distance and nonempty sets, `SetDistZero` is `inf = 0`. -/
theorem setDistZero_iff_sInf {X : Type*} {d : X → X → ℝ} (hd : ∀ x y, 0 ≤ d x y)
    {A B : Set X} (hA : A.Nonempty) (hB : B.Nonempty) :
    SetDistZero d A B ↔ sInf (image2 d A B) = 0 := by
  have hne : (image2 d A B).Nonempty := hA.image2 hB
  have hbdd : BddBelow (image2 d A B) := ⟨0, by rintro _ ⟨a, -, b, -, rfl⟩; exact hd a b⟩
  have hnn : 0 ≤ sInf (image2 d A B) := le_csInf hne (by rintro _ ⟨a, -, b, -, rfl⟩; exact hd a b)
  constructor
  · intro h
    refine le_antisymm (not_lt.1 fun hpos => ?_) hnn
    obtain ⟨α, hα, β, hβ, hlt⟩ := h _ hpos
    exact (not_lt.2 (csInf_le hbdd (mem_image2_of_mem hα hβ))) hlt
  · intro h ε hε
    obtain ⟨_, ⟨α, hα, β, hβ, rfl⟩, hlt⟩ := exists_lt_of_csInf_lt hne (h ▸ hε)
    exact ⟨α, hα, β, hβ, hlt⟩

/-- If the decision sets of a labelling into a finite type have pairwise positive set distances,
then they are all open in the topology induced by the distance. -/
theorem isOpen_fibers_of_not_setDistZero {X V : Type*} [Finite V] (d : X → X → ℝ)
    (lab : X → V) (h : ∀ v w, v ≠ w → ¬ SetDistZero d (lab ⁻¹' {v}) (lab ⁻¹' {w})) (v : V) :
    IsOpen[distTopology d] (lab ⁻¹' {v}) := by
  classical
  intro γ hγ
  have : ∀ w, ∃ ε > 0, w ≠ v → ∀ δ, d γ δ < ε → lab δ ≠ w := by
    intro w
    by_cases hw : w = v
    · exact ⟨1, one_pos, fun h => absurd hw h⟩
    · have := h v w (Ne.symm hw)
      unfold SetDistZero at this
      push Not at this
      obtain ⟨ε, hε, hε'⟩ := this
      exact ⟨ε, hε, fun _ δ hδ hδw => absurd (hε' γ hγ δ hδw) (not_le.2 hδ)⟩
  choose ε hε hε' using this
  have : Nonempty V := ⟨v⟩
  cases nonempty_fintype V
  refine ⟨Finset.univ.inf' Finset.univ_nonempty ε,
    (Finset.lt_inf'_iff _).2 fun w _ => hε w, fun δ hδ => ?_⟩
  by_contra hne
  exact hε' (lab δ) hne δ (lt_of_lt_of_le hδ (Finset.inf'_le _ (Finset.mem_univ _))) rfl

namespace Model

variable {P C V : Type*} (M : Model P C V) [Fintype P] [Nonempty P]

/-! ### Theorem 6.4: non-uniform consensus -/

/-- **Theorem 6.4** (non-uniform case, closure form), under `LockstepRecall`: non-uniform
consensus is solvable iff there is a partition of `Σ` into decision sets `Σ_v = lab⁻¹{v}` such that
(1) every execution in the `τNU`-closure of `Σ_w` lies in `Σ_w`, and (2) every `v`-valent
execution lies in `Σ_v`. -/
theorem theorem_6_4_nonUniform [Finite V] (hM : M.LockstepRecall) :
    NonUniformSolvable M ↔
      ∃ lab : M.adm → V, (∀ γ w, γ ∈ closure[M.τNU] (lab ⁻¹' {w}) → lab γ = w) ∧
        ∀ γ : M.adm, ∀ v, M.Valent γ v → lab γ = v := by
  rw [M.theorem_5_3 hM]
  exact exists_congr fun lab => and_congr_left' (@isClopen_fibers_iff_closure _ _ M.τNU _ lab)

/-- **Theorem 6.4** (non-uniform case, as stated): no decision set `Σ_v` contains a limit point
(w.r.t. `τNU`) of another decision set `Σ_w`. -/
theorem theorem_6_4_nonUniform' [Finite V] (hM : M.LockstepRecall) :
    NonUniformSolvable M ↔
      ∃ lab : M.adm → V, (∀ γ w, lab γ ≠ w → ¬ @AccPt _ M.τNU γ (𝓟 (lab ⁻¹' {w}))) ∧
        ∀ γ : M.adm, ∀ v, M.Valent γ v → lab γ = v := by
  rw [M.theorem_5_3 hM]
  exact exists_congr fun lab => and_congr_left' (@lemma_6_3 _ _ M.τNU _ lab)

/-- **Corollary 6.5** (non-uniform case, second sentence), under `LockstepRecall`: if for some
labelling with validity all decision sets have pairwise positive `d_nu`-distance, then
non-uniform consensus is solvable. -/
theorem corollary_6_5_nonUniform [Finite V] (hM : M.LockstepRecall) (lab : M.adm → V)
    (hval : ∀ γ : M.adm, ∀ v, M.Valent γ v → lab γ = v)
    (hpos : ∀ v w, v ≠ w →
      ¬ SetDistZero (fun γ δ : M.adm => M.dNU γ δ) (lab ⁻¹' {v}) (lab ⁻¹' {w})) :
    NonUniformSolvable M :=
  (M.theorem_5_3 hM).2 ⟨lab, @isClopen_fibers _ _ M.τNU lab
    (isOpen_fibers_of_not_setDistZero _ lab hpos), hval⟩

/-- **Theorem 6.4**, last sentence (non-uniform case), under `LockstepRecall`: if non-uniform
consensus is not solvable, then for every partition into decision sets satisfying validity there
are `v ≠ w` with `d_nu(Σ_v, Σ_w) = 0`. -/
theorem theorem_6_4_setDist_nonUniform [Finite V] (hM : M.LockstepRecall)
    (h : ¬ NonUniformSolvable M) (lab : M.adm → V)
    (hval : ∀ γ : M.adm, ∀ v, M.Valent γ v → lab γ = v) :
    ∃ v w, v ≠ w ∧ SetDistZero (fun γ δ : M.adm => M.dNU γ δ) (lab ⁻¹' {v}) (lab ⁻¹' {w}) := by
  by_contra hne
  push Not at hne
  exact h (M.corollary_6_5_nonUniform hM lab hval fun v w hvw => hne v w hvw)

/-! ### Theorem 6.4: uniform consensus (corrected uniform topology) -/

/-- **Theorem 6.4** (uniform case, closure form), with the corrected uniform topology `τUc` and
under `LockstepRecall`. -/
theorem theorem_6_4_uniform [Finite V] (hM : M.LockstepRecall) :
    UniformSolvable M ↔
      ∃ lab : M.adm → V, (∀ γ w, γ ∈ closure[M.τUc] (lab ⁻¹' {w}) → lab γ = w) ∧
        ∀ γ : M.adm, ∀ v, M.Valent γ v → lab γ = v := by
  rw [M.theorem_5_2c hM]
  exact exists_congr fun lab => and_congr_left' (@isClopen_fibers_iff_closure _ _ M.τUc _ lab)

/-- **Theorem 6.4** (uniform case, as stated in the paper with `d_u`), for fault-free models
(e.g. dynamic networks under message adversaries) under `LockstepRecall`. -/
theorem theorem_6_4_uniform_faultFree [Finite V] (hM : M.LockstepRecall) (hF : M.FaultFree) :
    UniformSolvable M ↔
      ∃ lab : M.adm → V, (∀ γ w, γ ∈ closure[M.τU] (lab ⁻¹' {w}) → lab γ = w) ∧
        ∀ γ : M.adm, ∀ v, M.Valent γ v → lab γ = v := by
  rw [← M.τUc_eq_τU hF]
  exact M.theorem_6_4_uniform hM

/-- **Corollary 6.5** (uniform case, second sentence) for the corrected distance `d_uc`. -/
theorem corollary_6_5_uniform [Finite V] (hM : M.LockstepRecall) (lab : M.adm → V)
    (hval : ∀ γ : M.adm, ∀ v, M.Valent γ v → lab γ = v)
    (hpos : ∀ v w, v ≠ w →
      ¬ SetDistZero (fun γ δ : M.adm => M.dUc γ δ) (lab ⁻¹' {v}) (lab ⁻¹' {w})) :
    UniformSolvable M :=
  (M.theorem_5_2c hM).2 ⟨lab, @isClopen_fibers _ _ M.τUc lab
    (isOpen_fibers_of_not_setDistZero _ lab hpos), hval⟩

/-- **Theorem 6.4**, last sentence (uniform case) for the corrected distance `d_uc`. -/
theorem theorem_6_4_setDist_uniform [Finite V] (hM : M.LockstepRecall)
    (h : ¬ UniformSolvable M) (lab : M.adm → V)
    (hval : ∀ γ : M.adm, ∀ v, M.Valent γ v → lab γ = v) :
    ∃ v w, v ≠ w ∧ SetDistZero (fun γ δ : M.adm => M.dUc γ δ) (lab ⁻¹' {v}) (lab ⁻¹' {w}) := by
  by_contra hne
  push Not at hne
  exact h (M.corollary_6_5_uniform hM lab hval fun v w hvw => hne v w hvw)

end Model

/-! ### Closure points need not be at distance zero -/

namespace ClosureCounterexample

open BallCounterexample

/-- For the reflexive `0/1`-valued distance `dChain` on `Fin 3` (zero relation `0 → 1 → 2`, not
transitive), `0` lies in the closure of `{2}`, but `d({0}, {2}) = 1 > 0`. Hence "`α ∈ A` is a limit
point of `B`" does not imply `d(A, B) = 0` for the non-metric distances of the paper. -/
theorem closure_not_setDistZero :
    (0 : Fin 3) ∈ closure[distTopology dChain] {2} ∧ ¬ SetDistZero dChain {0} {2} := by
  constructor
  · rw [@mem_closure_iff _ (distTopology dChain)]
    intro o ho h0
    obtain ⟨ε, hε, h⟩ := (isOpen_distTopology_iff dChain o).1 ho 0 h0
    have h1 : (1 : Fin 3) ∈ o := h 1 (by simp [dChain]; exact hε)
    obtain ⟨ε', hε', h'⟩ := (isOpen_distTopology_iff dChain o).1 ho 1 h1
    exact ⟨2, h' 2 (by simp [dChain]; exact hε'), rfl⟩
  · intro h
    obtain ⟨α, hα, β, hβ, hlt⟩ := h (1 / 2) (by norm_num)
    rw [mem_singleton_iff] at hα hβ
    subst hα hβ
    norm_num [dChain] at hlt

end ClosureCounterexample

end TopoConsensus
