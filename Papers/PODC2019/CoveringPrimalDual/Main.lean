import Papers.PODC2019.CoveringPrimalDual.Rounds

/-!
# Main result: Algorithm MWHVC is an `(f+ε)`-approximation in `O(log_α Δ + f z α)` iterations

`mwhvc_main` combines Corollary 4.3 and Theorem 4.8 for the algorithm of Section 3 (`κ = 1`,
`c₀ = 1/2`); `mwhvc_appendixC` does the same for the variant of Appendix C (`κ = 1/2`), which in
addition raises every level by at most one per iteration (Corollary C.1). `Params.std` shows that the
hypotheses are satisfiable for every instance, every `ε > 0` and every `α > 1`.
-/

set_option linter.unusedSectionVars false

namespace Podc.CoveringPrimalDual

open Finset Cslib.Hypergraph

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable {I : Inst V E} {P : Params}

/-- Algorithm MWHVC (Section 3: `κ = 1`, `c₀ = 1/2`) with `α ≥ 2`, on a hypergraph of rank `≤ f`
and maximum degree `≤ Δ`: after `N = iterBound P Δ ≤ log_α Δ + f·z·(α + 2) + 1` iterations every
edge is covered, and the output `C` is a vertex cover with `w(C) ≤ (f + ε)·OPT_LP` (Corollary 4.3,
Theorem 4.8). -/
theorem mwhvc_main (hP : P.Valid I) (hκ : P.κ = 1) (hc : P.c₀ = 1 / 2) (hα : 2 ≤ P.α) {Δ : ℕ}
    (hΔ : ∀ v, I.deg v ≤ Δ) (hΔ1 : 1 ≤ Δ) :
    Terminated I P (iterBound P Δ) ∧ IsCover I.inc (run I P (iterBound P Δ)).C ∧
      (∀ x, IsFracCover I.inc x →
        ∑ v ∈ (run I P (iterBound P Δ)).C, I.w v ≤ (P.f + P.ε) * ∑ v, I.w v * x v) ∧
      (iterBound P Δ : ℝ) ≤ Real.logb P.α Δ + P.f * P.z * (P.α + 2) + 1 := by
  have hT := theorem_4_8 hP hΔ
  refine ⟨hT, (corollary_4_3 hP hT).1, (corollary_4_3 hP hT).2, ?_⟩
  have := iterBound_le hP hc hα hΔ1
  rwa [hκ, div_one] at this

/-- The variant of Appendix C (`δ(e) ← δ(e) + deal(e)/2`): same guarantees with `2α` in place of
`α` in the iteration bound, and levels grow by at most one per iteration (Corollary C.1). -/
theorem mwhvc_appendixC (hP : P.Valid I) (hκ : P.κ = 1 / 2) (hc : P.c₀ = 1 / 2) (hα : 2 ≤ P.α)
    {Δ : ℕ} (hΔ : ∀ v, I.deg v ≤ Δ) (hΔ1 : 1 ≤ Δ) :
    Terminated I P (iterBound P Δ) ∧ IsCover I.inc (run I P (iterBound P Δ)).C ∧
      (∀ x, IsFracCover I.inc x →
        ∑ v ∈ (run I P (iterBound P Δ)).C, I.w v ≤ (P.f + P.ε) * ∑ v, I.w v * x v) ∧
      (iterBound P Δ : ℝ) ≤ Real.logb P.α Δ + P.f * P.z * (2 * P.α + 2) + 1 ∧
      ∀ i, 1 ≤ i → ∀ v, (run I P i).level v ≤ (run I P (i - 1)).level v + 1 := by
  have hT := theorem_4_8 hP hΔ
  refine ⟨hT, (corollary_4_3 hP hT).1, (corollary_4_3 hP hT).2, ?_,
    fun i hi v => corollary_C_1 hP hκ hi v⟩
  have := iterBound_le hP hc hα hΔ1
  rwa [hκ, div_div_eq_mul_div, div_one, mul_comm P.α 2] at this

/-- The rank of the hypergraph (at least `1`). -/
def Inst.rank (I : Inst V E) : ℕ := max 1 (univ.sup fun e => (I.inc e).card)

/-- The paper's parameters: `f` = rank, `κ = 1`, `c₀ = 1/2`. -/
noncomputable def Params.std (I : Inst V E) (ε α : ℝ) : Params := ⟨I.rank, ε, α, 1, 1 / 2⟩

/-- Non-vacuity: the paper's parameters are valid for every instance, `ε > 0` and `α > 1`. -/
theorem Params.std_valid (I : Inst V E) {ε α : ℝ} (hε : 0 < ε) (hα : 1 < α) :
    (Params.std I ε α).Valid I where
  f_pos := lt_of_lt_of_le one_pos (le_max_left _ _)
  rank_le e := (le_sup (f := fun e => (I.inc e).card) (mem_univ e)).trans (le_max_right _ _)
  ε_pos := hε
  one_lt_α := hα
  κ_pos := one_pos
  κ_le := le_rfl
  c₀_pos := by norm_num [Params.std]
  c₀_le := le_rfl

/-- Every instance has a degree bound. -/
theorem exists_deg_bound (I : Inst V E) : ∃ Δ, 1 ≤ Δ ∧ ∀ v, I.deg v ≤ Δ :=
  ⟨max 1 (univ.sup I.deg), le_max_left _ _,
    fun v => (le_sup (f := I.deg) (mem_univ v)).trans (le_max_right _ _)⟩

/-- Non-vacuity of `mwhvc_main`: for every instance and every `ε > 0`, Algorithm MWHVC with `α = 2`
terminates with an `(f+ε)`-approximate vertex cover. -/
example (I : Inst V E) {ε : ℝ} (hε : 0 < ε) : ∃ N, Terminated I (Params.std I ε 2) N ∧
    ∀ x, IsFracCover I.inc x → ∑ v ∈ (run I (Params.std I ε 2) N).C, I.w v ≤
      (I.rank + ε) * ∑ v, I.w v * x v := by
  obtain ⟨Δ, hΔ1, hΔ⟩ := exists_deg_bound I
  have h := mwhvc_main (Params.std_valid I hε (by norm_num : (1 : ℝ) < 2)) rfl rfl le_rfl hΔ hΔ1
  exact ⟨_, h.1, h.2.2.1⟩

end Podc.CoveringPrimalDual
