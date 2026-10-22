import Papers.PODC2019.CoveringPrimalDual.Invariants

/-!
# Feasibility and approximation ratio (Section 4.1, Claim 4.4, Appendices A and C)

* `claim_4_1`, `claim_4_2`, `claim_4_2_feasible`: the invariants of Section 4.1.
* `claim_A_1`: the `β`-tight vertices of an edge packing weigh at most `(f+ε)·OPT_LP`.
* `corollary_4_3`: upon termination, `C` is a vertex cover of weight `≤ (f+ε)·OPT_LP`.
* `claim_4_4`: levels stay below `z = ⌈log₂(1/β)⌉`.
* `corollary_C_1`: with `κ = 1/2` (Appendix C), levels grow by at most one per iteration.
-/

set_option linter.unusedSectionVars false

namespace Podc.CoveringPrimalDual

open Finset Cslib.Hypergraph

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable {I : Inst V E} {P : Params}

/-- Claim 4.1 of [Ben-Basat–Even–Kawarabayashi–Schwartzman, PODC'19]: if `v ∉ C` at the end of
iteration `i`, then `∑_{e ∈ E'(v)} deal_i(e) ≤ 2^{-(ℓ_i(v)+1)} · w(v)`. -/
theorem claim_4_1 (hP : P.Valid I) (i : ℕ) {v : V} (hv : v ∉ (run I P i).C) :
    ∑ e ∈ I.uncov (run I P i).C v, (run I P i).deal e ≤
      (1 / 2 : ℝ) ^ ((run I P i).level v + 1) * I.w v :=
  (inv_run hP i).claim41 v hv

/-- Claim 4.2, Eq. (1): for every iteration `i ≥ 1` and every vertex `v` that is still active in
iteration `i`, `w(v)(1 - 2^{-ℓ_i(v)}) ≤ ∑_{e ∈ E(v)} δ_{i-1}(e) ≤ (1 - 2^{-(ℓ_i(v)+1)}) w(v)`. -/
theorem claim_4_2 (hP : P.Valid I) {i : ℕ} (hi : 1 ≤ i) {v : V}
    (hv : I.Active (run I P i).C v) :
    I.w v * (1 - (1 / 2 : ℝ) ^ (run I P i).level v) ≤ I.load (run I P (i - 1)).δ v ∧
      I.load (run I P (i - 1)).δ v ≤ (1 - (1 / 2 : ℝ) ^ ((run I P i).level v + 1)) * I.w v := by
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  change I.Active (joinC I P (run I P j)) v at hv
  change I.w v * (1 - (1 / 2 : ℝ) ^ lvl1 I P (run I P j) v) ≤ _ ∧
    _ ≤ (1 - (1 / 2 : ℝ) ^ (lvl1 I P (run I P j) v + 1)) * I.w v
  have hs := inv_run hP j
  refine ⟨?_, by rw [mul_comm]; exact load_le_lvl1 hP hv⟩
  by_cases hlt : (run I P j).level v < lvl1 I P (run I P j) v
  · rw [lvl1_of_active I P hv] at hlt ⊢
    exact (lvlUp_lower hlt).le
  · have : lvl1 I P (run I P j) v = (run I P j).level v :=
      le_antisymm (by omega) (le_lvl1 I P _ v)
    rw [this]; exact hs.lower v

/-- Claim 4.2, feasibility: the dual variables `δ_i` form an edge packing. -/
theorem claim_4_2_feasible (hP : P.Valid I) (i : ℕ) : IsPacking I.inc I.w (run I P i).δ :=
  ⟨(inv_run hP i).δ_nonneg, (inv_run hP i).feasible⟩

/-- Claim A.1: for a feasible edge packing `δ` and `β = ε/(f+ε)`, the set `T_ε` of `β`-tight
vertices satisfies `w(T_ε) ≤ (f+ε)·opt`; we prove it against every fractional vertex cover `x`
(in particular an optimal one). -/
theorem claim_A_1 {inc : E → Finset V} {w : V → ℝ} {δ : E → ℝ} {f : ℕ} {ε : ℝ} (hε : 0 < ε)
    (hf0 : 0 < f) (hf : ∀ e, (inc e).card ≤ f) (hδ : IsPacking inc w δ) {x : V → ℝ}
    (hx : IsFracCover inc x) :
    ∑ v ∈ univ.filter (fun v => (1 - ε / (f + ε)) * w v ≤ load inc δ v), w v ≤
      (f + ε) * ∑ v, w v * x v :=
  sum_tight_le_of_isPacking hε hf0 hf hδ (fun _ hv => (mem_filter.1 hv).2) hx

/-- Throughout the algorithm, `C` consists of `β`-tight vertices. -/
theorem tight_of_mem_C (hP : P.Valid I) (i : ℕ) {v : V} (hv : v ∈ (run I P i).C) :
    (1 - P.β) * I.w v ≤ I.load (run I P i).δ v :=
  (inv_run hP i).tight v hv

/-- At every iteration, `w(C) ≤ (f+ε)·opt` (against every fractional vertex cover). -/
theorem weight_C_le (hP : P.Valid I) (i : ℕ) {x : V → ℝ} (hx : IsFracCover I.inc x) :
    ∑ v ∈ (run I P i).C, I.w v ≤ (P.f + P.ε) * ∑ v, I.w v * x v :=
  sum_tight_le_of_isPacking hP.ε_pos hP.f_pos hP.rank_le (claim_4_2_feasible hP i)
    (fun _ hv => tight_of_mem_C hP i hv) hx

/-- Corollary 4.3: upon termination, `C` is a vertex cover and `w(C) ≤ (f+ε)·opt`, where `opt` is
the cost of an optimal fractional vertex cover (we prove the bound against every fractional
vertex cover `x`). -/
theorem corollary_4_3 (hP : P.Valid I) {i : ℕ} (hT : Terminated I P i) :
    IsCover I.inc (run I P i).C ∧
      ∀ x, IsFracCover I.inc x → ∑ v ∈ (run I P i).C, I.w v ≤ (P.f + P.ε) * ∑ v, I.w v * x v :=
  ⟨hT, fun _ hx => weight_C_le hP i hx⟩

/-- Corollary 4.3 against integral covers: `w(C) ≤ (f+ε)·w(C*)` for every vertex cover `C*`. -/
theorem corollary_4_3_integral (hP : P.Valid I) {i : ℕ} (hT : Terminated I P i) {C' : Finset V}
    (hC' : IsCover I.inc C') :
    ∑ v ∈ (run I P i).C, I.w v ≤ (P.f + P.ε) * ∑ v ∈ C', I.w v := by
  have := (corollary_4_3 hP hT).2 _ hC'.isFracCover
  rwa [sum_mul_indicator] at this

/-- Claim 4.4: the level of every vertex is always less than `z = ⌈log₂(1/β)⌉`. -/
theorem claim_4_4 (hP : P.Valid I) (i : ℕ) (v : V) : (run I P i).level v < P.z :=
  (inv_run hP i).level_lt v

/-- Corollary C.1: in the variant of Appendix C (`δ(e) ← δ(e) + deal(e)/2`), for every iteration
`i ≥ 1` and vertex `v`, `ℓ_i(v) ≤ ℓ_{i-1}(v) + 1`. -/
theorem corollary_C_1 (hP : P.Valid I) (hκ : P.κ = 1 / 2) {i : ℕ} (hi : 1 ≤ i) (v : V) :
    (run I P i).level v ≤ (run I P (i - 1)).level v + 1 := by
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  change lvl1 I P (run I P j) v ≤ _
  by_cases hact : I.Active (joinC I P (run I P j)) v
  · rw [lvl1_of_active I P hact]
    apply lvlUp_le (by omega)
    have h := (inv_run hP j).activeLoad v (I.active_anti (C_subset_joinC I P _) hact)
    rw [hκ] at h
    have : (1 / 2 : ℝ) ^ ((run I P j).level v + 1 + 1) =
        (1 - 1 / 2) * (1 / 2 : ℝ) ^ ((run I P j).level v + 1) := by ring
    rw [this, mul_comm]; exact h
  · rw [lvl1_of_not_active I P hact]; omega

end Podc.CoveringPrimalDual
