import Papers.PODC2020.BinaryLabelingClassification.Basic

/-!
# The global problem families V and VI (Table 2)

In the bit-vector notation of §3.4 (bit `i` of `W` is `1` iff `i ∈ W`):

* V.a: `W = 10⁺1`, `B = 010` (so `δ = 2`, `W = {0, d}`, `B = {1}`); V.b: the colour swap.
* VI.a: `W = 0⁺1∗`, `B = ∗10⁺`; VI.b: `W = ∗10⁺`, `B = 0⁺1∗` (the colour swap of VI.a).

We also define the extreme members of VI.b used in §8: the hardest one
`W = 010⁺, B = 0⁺10` (`viHard`) and the easiest one `W = 110⁺, B = 0⁺11` (`viEasy`).
-/

namespace Podc.BinaryLabeling

open SimpleGraph

namespace Problem

/-- Family V.a: `W = 10⁺1`, `B = 010`. -/
def IsVa (P : Problem) : Prop := P.δ = 2 ∧ P.W = {0, P.d} ∧ P.B = {1}

/-- Family V.b: `W = 010`, `B = 10⁺1`. -/
def IsVb (P : Problem) : Prop := P.swap.IsVa

/-- Family VI.a: `W = 0⁺1∗`, `B = ∗10⁺`. -/
def IsVIa (P : Problem) : Prop :=
  (P.d - 1 ∈ P.W ∧ ∀ i < P.d - 1, i ∉ P.W) ∧ (1 ∈ P.B ∧ ∀ i, 2 ≤ i → i ∉ P.B)

/-- Family VI.b: `W = ∗10⁺`, `B = 0⁺1∗`. -/
def IsVIb (P : Problem) : Prop := P.swap.IsVIa

end Problem

/-- The hardest problem of VI.b: `W = 010⁺`, `B = 0⁺10` (proof of Theorem 8.3). -/
def viHard (d δ : ℕ) (hd : 2 ≤ d) (hδ : 2 ≤ δ) : Problem where
  d := d
  δ := δ
  W := {1}
  B := {δ - 1}
  two_le_d := hd
  two_le_δ := hδ
  W_le := by rintro x rfl; omega
  B_le := by rintro x rfl; omega

/-- The easiest problem of VI.b: `W = 110⁺`, `B = 0⁺11` (proof of Theorem 8.2). -/
def viEasy (d δ : ℕ) (hd : 2 ≤ d) (hδ : 2 ≤ δ) : Problem where
  d := d
  δ := δ
  W := {0, 1}
  B := {δ - 1, δ}
  two_le_d := hd
  two_le_δ := hδ
  W_le := by rintro x (rfl | rfl) <;> omega
  B_le := by rintro x (rfl | rfl) <;> omega

namespace Problem

variable {P : Problem}

lemma IsVIb.iff : P.IsVIb ↔
    (1 ∈ P.W ∧ ∀ i, 2 ≤ i → i ∉ P.W) ∧ (P.δ - 1 ∈ P.B ∧ ∀ i < P.δ - 1, i ∉ P.B) := by
  simp only [IsVIb, IsVIa, swap]; tauto

/-- `viHard` is a restriction of every problem of VI.b. -/
lemma IsVIb.viHard_le (h : P.IsVIb) : (viHard P.d P.δ P.two_le_d P.two_le_δ).IsRestriction P := by
  rw [IsVIb.iff] at h
  refine ⟨rfl, rfl, ?_, ?_⟩
  · rintro x rfl; exact h.1.1
  · rintro x rfl; exact h.2.1

/-- Every problem of VI.b is a restriction of `viEasy`. -/
lemma IsVIb.le_viEasy (h : P.IsVIb) : P.IsRestriction (viEasy P.d P.δ P.two_le_d P.two_le_δ) := by
  rw [IsVIb.iff] at h
  refine ⟨rfl, rfl, fun x hx => ?_, fun x hx => ?_⟩
  · by_contra hc
    simp only [viEasy, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hc
    exact h.1.2 x (by omega) hx
  · by_contra hc
    simp only [viEasy, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hc
    have := P.B_le x hx
    exact h.2.2 x (by omega) hx

/-- The complement of a VI.a problem is a VI.b problem (Observation 3.2). -/
lemma IsVIa.compl (h : P.IsVIa) : P.compl.IsVIb := by
  rw [IsVIb.iff]
  obtain ⟨⟨hW1, hW2⟩, ⟨hB1, hB2⟩⟩ := h
  have hd := P.two_le_d
  have hδ := P.two_le_δ
  refine ⟨⟨?_, fun i hi hmem => ?_⟩, ⟨?_, fun i hi hmem => ?_⟩⟩
  · exact ⟨P.d - 1, hW1, by simp only [compl_d]; omega⟩
  · obtain ⟨x, hx, hxi⟩ := hmem
    have := P.W_le x hx
    exact hW2 x (by simp only [compl_d] at hxi hi; omega) hx
  · exact ⟨1, hB1, by simp only [compl_δ]⟩
  · obtain ⟨x, hx, hxi⟩ := hmem
    have := P.B_le x hx
    simp only [compl_δ] at hxi hi
    by_cases hx0 : x = 0
    · subst hx0; omega
    · by_cases hx1 : x = 1
      · subst hx1; omega
      · exact hB2 x (by omega) hx

end Problem

end Podc.BinaryLabeling
