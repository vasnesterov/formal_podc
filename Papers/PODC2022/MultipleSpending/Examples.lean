import Papers.PODC2022.MultipleSpending.Trust

/-!
# Examples 3.1 and 3.5

Four processes `p₁, …, p₄` (here `0, …, 3`), only `p₃` may fail. The paper writes the fault model
as `{{p₃}}`; with the standing assumption that fault models are inclusion-closed it is
`{∅, {p₃}}` (`example_3_1`); the literal `{{p₃}}` gives the same answer
(`example_3_5_literal`). Note that the paper's `Q(p₃) = {{p₁, p₂, p₄}}` violates the standing
assumption `p ∈ Q` for `Q ∈ Q(p)` (`example_3_1_not_selfMem`); this does not affect the claim.
-/

namespace Podc.MultipleSpending

/-- The quorum map of Example 3.1. -/
def ex31Q : Fin 4 → Set (Finset (Fin 4))
  | 0 => {{0, 1, 2}}
  | 1 => {{0, 1}, {1, 3}}
  | 2 => {{0, 1, 3}}
  | 3 => {{1, 3}, {2, 3}}

/-- The trust model of Example 3.1 (fault model closed under subsets). -/
def example_3_1 : TrustModel (Fin 4) := ⟨ex31Q, {∅, {2}}⟩

/-- The trust model of Example 3.1 with the fault model `{{p₃}}` taken literally. -/
def example_3_1_literal : TrustModel (Fin 4) := ⟨ex31Q, {{2}}⟩

theorem example_3_1_not_selfMem : ¬ example_3_1.SelfMem := by
  intro h
  have := h 2 {0, 1, 3} rfl
  revert this; decide

/-- The finite check behind Example 3.5: for both faulty sets and all four quorum maps, every
independent set has at most two members. -/
private theorem ex35_check : ∀ a ∈ ({{0, 1}, {1, 3}} : Finset (Finset (Fin 4))),
    ∀ b ∈ ({{1, 3}, {2, 3}} : Finset (Finset (Fin 4))),
    ∀ F ∈ ({∅, {2}} : Finset (Finset (Fin 4))), ∀ C : Finset (Fin 4),
    (Disjoint C F ∧ ∀ p ∈ C, ∀ q ∈ C, p ≠ q →
      (![{0, 1, 2}, a, {0, 1, 3}, b] p) ∩ (![{0, 1, 2}, a, {0, 1, 3}, b] q) ⊆ F) →
    C.card ≤ 2 := by
  decide

private theorem ex35_le (F : Finset (Fin 4)) (hF : F = ∅ ∨ F = {2}) (S : Fin 4 → Finset (Fin 4))
    (hS : ∀ p, S p ∈ ex31Q p) (C : Finset (Fin 4)) (hC : IsIndep F S C) : C.card ≤ 2 := by
  have h0 : S 0 = {0, 1, 2} := hS 0
  have h2 : S 2 = {0, 1, 3} := hS 2
  have h1 : S 1 ∈ ({{0, 1}, {1, 3}} : Finset (Finset (Fin 4))) := by
    have := hS 1
    simp only [ex31Q, Set.mem_insert_iff, Set.mem_singleton_iff] at this
    rcases this with h | h <;> simp [h]
  have h3 : S 3 ∈ ({{1, 3}, {2, 3}} : Finset (Finset (Fin 4))) := by
    have := hS 3
    simp only [ex31Q, Set.mem_insert_iff, Set.mem_singleton_iff] at this
    rcases this with h | h <;> simp [h]
  have hSeq : S = ![{0, 1, 2}, S 1, {0, 1, 3}, S 3] := by
    funext p; fin_cases p <;> simp [h0, h2]
  refine ex35_check (S 1) h1 (S 3) h3 F (by rcases hF with rfl | rfl <;> simp) C ?_
  rw [← hSeq]; exact hC

private theorem ex35_ge (T : TrustModel (Fin 4)) (hT : T.Q = ex31Q) (hF : {2} ∈ T.F) :
    2 ≤ inconsistencyNumber T := by
  let S : Fin 4 → Finset (Fin 4) := ![{0, 1, 2}, {1, 3}, {0, 1, 3}, {2, 3}]
  have hS : S ∈ T.QuorumMaps := by
    intro p; rw [hT]; fin_cases p <;> simp [S, ex31Q]
  have := T.card_le_inconsistencyNumber hF hS (C := {0, 3}) (by
    refine ⟨by decide, ?_⟩
    decide)
  simpa using this

/-- **Example 3.5**: the inconsistency number of the trust model of Example 3.1 is `2`. -/
theorem example_3_5 : inconsistencyNumber example_3_1 = 2 := by
  apply le_antisymm
  · apply TrustModel.inconsistencyNumber_le
    intro F hF S hS C hC
    exact ex35_le F hF S hS C hC
  · exact ex35_ge _ rfl (Or.inr rfl)

theorem example_3_5_literal : inconsistencyNumber example_3_1_literal = 2 := by
  apply le_antisymm
  · apply TrustModel.inconsistencyNumber_le
    intro F hF S hS C hC
    exact ex35_le F (Or.inr hF) S hS C hC
  · exact ex35_ge _ rfl rfl

end Podc.MultipleSpending
