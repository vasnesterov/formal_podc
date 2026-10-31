import Papers.PODC2012.ByzantineLinearCoding.Examples

/-!
# Two small issues in Appendix C, with Lean witnesses

1. **Lemma 1 is false for small fields.** Lemma 1 claims, "for any `ρ_k ≤ U_k/2`", that `M̃_H` is
   invertible with probability `≥ (1 - (n-f-1)/2^{L/ρ_k})^{ρ_k}`. When `2^{L/ρ_k} < (n-f-1)/2` and
   `ρ_k` is even, the right-hand side is `> 1`; when it equals `1` the claim says `M̃_H` is *always*
   invertible, which fails for the all-zero coding. Instance: `n = 7`, `f = 2` (so `n - f - 1 = 4`),
   `H = K_5` with all link capacities `2` (`U_k = 16`), `ρ_k = 2`, `L = 2`, so the field is
   `GF(2^{L/ρ_k}) = GF(2)` and the bound is `(1 - 4/2)^2 = 1`. The induction in the paper multiplies
   inequalities whose factors `1 - (n-f-1)/2^{L/ρ_k}` may be negative. With `n - f - 1 ≤ |F|` the
   lemma holds (`TreePacking.lemma_1`).

2. **The argument of Appendix C.3 does not prove that `A_q` is invertible.** It only uses that some
   column has a single nonzero entry, that every row has a nonzero entry and that no two columns
   have the same support; these properties hold for the incidence matrix of the edges
   `(1,5), (2,3), (3,4), (4,2)` on the nodes `1..4` (root `5`), which is singular (a cycle, no tree).
   The claim itself is true (`TreePacking.det_A_ne_zero`, proved from connectivity).
-/

namespace Podc.ByzantineLinearCoding

open Finset Cslib.Probability

/-- An event that fails at some outcome has probability `< 1`. -/
theorem uprob_lt_one_of_not {Ω : Type*} [Fintype Ω] {E : Ω → Prop} (ω : Ω) (h : ¬ E ω) :
    uprob E < 1 := by
  classical
  have : Nonempty Ω := ⟨ω⟩
  have hpos : 0 < uprob (fun ω => ¬ E ω) := by
    rw [uprob_eq_card_filter]
    apply div_pos _ (by exact_mod_cast Fintype.card_pos)
    exact_mod_cast card_pos.2 ⟨ω, by simpa using h⟩
  have := uprob_not E
  have h2 := uprob_not (fun ω => ¬ E ω)
  simp only [not_not] at h2
  linarith

/-- Capacities of the complete network on `5` nodes with all link capacities `2`. -/
abbrev z5 : Fin 5 → Fin 5 → ℕ := fun _ _ => 2

/-- Two edge-disjoint spanning stars of `K_5` with capacities `2`. -/
noncomputable abbrev P5 : TreePacking z5 univ 2 :=
  TreePacking.star z5 univ 2 univ_nonempty fun _ _ _ _ _ => le_rfl

theorem P5_w : P5.w = 4 := rfl

/-- **Lemma 1 (Appendix C.1) is false as stated for small fields**: with `n - f - 1 = 4`,
`ρ_k = 2` and the field `GF(2)` (`L = 2`), the claimed lower bound `(1 - 4/2)^2 = 1` exceeds the
probability that `M̃_H` is invertible (the all-zero coding makes it singular). -/
theorem lemma_1_false_small_field :
    ¬ ((1 - (P5.w : ℝ) / Fintype.card (ZMod 2)) ^ 2 ≤
      uprob (fun c : Coding z5 2 (ZMod 2) => (P5.M c).det ≠ 0)) := by
  have hw : (P5.w : ℝ) = 4 := by rw [P5_w]; norm_num
  rw [hw, ZMod.card]
  intro h
  have hlt : uprob (fun c : Coding z5 2 (ZMod 2) => (P5.M c).det ≠ 0) < 1 := by
    refine uprob_lt_one_of_not 0 ?_
    have hM : P5.M (0 : Coding z5 2 (ZMod 2)) = 0 := by
      ext ip rq; simp [TreePacking.M]
    simp only [ne_eq, not_not, hM]
    have : Nonempty (Fin P5.w × Fin 2) := ⟨(⟨0, by rw [P5_w]; norm_num⟩, 0)⟩
    exact Matrix.det_zero
  norm_num at h
  linarith

/-- The incidence matrix of the edges `(1,5), (2,3), (3,4), (4,2)` (rows: nodes `1..4`; node `5`
is the paper's node `n - f`; columns: edges). -/
def cycleA : Matrix (Fin 4) (Fin 4) ℚ :=
  !![1, 0, 0, 0;
     0, 1, 0, -1;
     0, -1, 1, 0;
     0, 0, -1, 1]

/-- **The argument of Appendix C.3 is insufficient**: `cycleA` has every property that the
argument uses (a column with a single nonzero entry, a nonzero entry in every row, pairwise
different column supports), yet it is singular. -/
theorem c3_argument_insufficient :
    (∃ r, ∃ i, cycleA i r ≠ 0 ∧ ∀ i', i' ≠ i → cycleA i' r = 0) ∧
    (∀ i, ∃ r, cycleA i r ≠ 0) ∧
    (∀ r r', r ≠ r' → ∃ i, (cycleA i r = 0) ≠ (cycleA i r' = 0)) ∧
    cycleA.det = 0 := by
  refine ⟨⟨0, 0, by simp [cycleA], ?_⟩, ?_, ?_, ?_⟩
  · intro i' hi'; fin_cases i' <;> simp_all [cycleA]
  · intro i; fin_cases i
    · exact ⟨0, by simp [cycleA]⟩
    · exact ⟨1, by simp [cycleA]⟩
    · exact ⟨1, by simp [cycleA]⟩
    · exact ⟨2, by simp [cycleA]⟩
  · intro r r' h
    fin_cases r <;> fin_cases r' <;> first
      | exact absurd rfl h
      | (refine ⟨1, ?_⟩; simp [cycleA]; done)
      | (refine ⟨2, ?_⟩; simp [cycleA])
  · rw [← Matrix.exists_vecMul_eq_zero_iff]
    refine ⟨![0, 1, 1, 1], by decide, ?_⟩
    ext r; fin_cases r <;> simp [cycleA, Matrix.vecMul, dotProduct, Fin.sum_univ_four]

end Podc.ByzantineLinearCoding
