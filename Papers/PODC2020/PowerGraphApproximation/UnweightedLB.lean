import Papers.PODC2020.PowerGraphApproximation.WeightedLB

/-!
# Theorem 22: exact (unweighted) `G²`-MVC needs `Ω̃(n²)` CONGEST rounds

Bar-Yehuda, Censor-Hillel, Maus, Pai, Pemmaraju, *Distributed Approximation on Power Graphs*,
PODC 2020 (arXiv:2006.03746), Section 5.3.

Model: synchronous deterministic CONGEST with `B`-bit messages on `H_{x,y}` (gadgets are dangling
paths of three vertices, `H x y 3`); nodes know their IDs and neighbourhoods. With `k = 2^L` and
`g = 2k + 4k log k + 8 log k` gadgets, `n = |V(H)| = 10k + 12k log k + 32 log k` (`card_HV`), the
cut has `4 log k` edges, and the predicate is "`H²` has a vertex cover of size at most
`W + 2g`" with `W = 4(k - 1) + 4 log k`. Theorem 19 with `CC(DISJ_{k²}) ≥ k²` gives
`k² ≤ 8 T B log k + 2` (`theorem_22`), i.e. `n² ≤ 2916 log² n · (8 T B log n + 2)`
(`theorem_22_n`).
-/

namespace Podc.PowerGraphApproximation.LowerBound

open Finset SimpleGraph Cslib.Congest Cslib.CommunicationComplexity

variable {L : ℕ}

/-- The predicate `P_H` of Theorem 22: `H²` has a vertex cover of size at most
`W + 2(2k + 4k log k + 8 log k)`, `W = 4(k - 1) + 4 log k`. -/
def UnweightedPred (x y : Idx L × Idx L → Bool) : Prop :=
  ∃ C : Finset (HV L 3), ((H x y 3).power 2).IsVertexCover ↑C ∧
    C.card ≤ 4 * (2 ^ L - 1) + 4 * L + 2 * (2 * 2 ^ L + 4 * 2 ^ L * L + 8 * L)

lemma unweightedPred_iff (x y : Idx L × Idx L → Bool) :
    UnweightedPred x y ↔ Protocol.disj x y = false := by
  rw [UnweightedPred, lemma_24, ckp17]
  simp [Protocol.disj]

/-- **Theorem 22 of [BCMPP20]** (deterministic, decision version). Let `A` be a deterministic
CONGEST algorithm with `B`-bit messages that, in `T` rounds, decides on every graph `H_{x,y}`
(nodes know their neighbourhoods) whether `H²_{x,y}` has a vertex cover of size at most
`W + 2(2k + 4k log k + 8 log k)`, `W = 4(k - 1) + 4 log k`. Then `k² ≤ 8 T B log k + 2`. -/
theorem theorem_22 {σ : Type*} {B : ℕ} (A : Algorithm (HV L 3) (HV L 3 → Bool) σ B) (T : ℕ)
    (hA : ∀ x y : Idx L × Idx L → Bool,
      A.Accepts (H x y 3) (fun v w => decide ((H x y 3).Adj v w)) T ↔
        ∃ C : Finset (HV L 3), ((H x y 3).power 2).IsVertexCover ↑C ∧
          C.card ≤ 4 * (2 ^ L - 1) + 4 * L + 2 * (2 * 2 ^ L + 4 * 2 ^ L * L + 8 * L)) :
    4 ^ L ≤ T * (8 * L * B) + 2 := by
  have h := (hFamily L 3).not_disj_lowerBound A T fun x y => by
    change A.Accepts (H x y 3) (fun v w => decide ((H x y 3).Adj v w)) T ↔ _
    rw [hA x y]
    exact unweightedPred_iff x y
  rw [hFamily_Ecut, card_hCut] at h
  have hc : Fintype.card (Idx L × Idx L) = 4 ^ L := by
    simp [Fintype.card_prod, ← mul_pow]
  rw [hc] at h
  calc 4 ^ L ≤ T * (2 * (4 * L * B)) + 2 := h
    _ = T * (8 * L * B) + 2 := by ring

/-- **Theorem 22 of [BCMPP20]**, in terms of `n = |V(H_{x,y})|` (for `k ≥ 2`):
`n² ≤ 2916 log² n · (8 T B log n + 2)`, i.e. `T = Ω(n² / (B log³ n)) = Ω̃(n²)`. -/
theorem theorem_22_n (hL : 1 ≤ L) {σ : Type*} {B : ℕ}
    (A : Algorithm (HV L 3) (HV L 3 → Bool) σ B) (T : ℕ)
    (hA : ∀ x y : Idx L × Idx L → Bool,
      A.Accepts (H x y 3) (fun v w => decide ((H x y 3).Adj v w)) T ↔
        ∃ C : Finset (HV L 3), ((H x y 3).power 2).IsVertexCover ↑C ∧
          C.card ≤ 4 * (2 ^ L - 1) + 4 * L + 2 * (2 * 2 ^ L + 4 * 2 ^ L * L + 8 * L)) :
    Fintype.card (HV L 3) ^ 2 ≤
      2916 * Nat.log 2 (Fintype.card (HV L 3)) ^ 2 *
        (T * (8 * Nat.log 2 (Fintype.card (HV L 3)) * B) + 2) := by
  have hk : 1 ≤ 2 ^ L := Nat.one_le_two_pow
  have := sq_le_of_card_le (c := 54) (n := Fintype.card (HV L 3)) ?_ ?_ (theorem_22 A T hA)
  · simpa using this
  · rw [card_HV]; nlinarith
  · rw [card_HV]; nlinarith

open Classical in
/-- **Theorem 22 of [BCMPP20]** (randomized, conditional on `CC^R(DISJ_K) ≥ κ·K` with a real
constant `κ` and nonempty coin spaces, see `theorem_20_randomized`). -/
theorem theorem_22_randomized {σ ρ : Type} [Fintype ρ] [Nonempty ρ] {B : ℕ}
    (A : Algorithm (HV L 3) ((HV L 3 → Bool) × ρ) σ B) (T : ℕ) (ε κ : ℝ)
    (hCC : ∀ (RA RB : Type) [Fintype RA] [Fintype RB] [Nonempty RA] [Nonempty RB]
      (P : Protocol ((Idx L × Idx L → Bool) × RA) ((Idx L × Idx L → Bool) × RB) Bool) (b : ℕ),
      P.RandComputes (fun x y => !Protocol.disj x y) ε → P.CostLE b → κ * 4 ^ L ≤ b)
    (hA : ∀ x y : Idx L × Idx L → Bool,
      (LBFamily.Algorithm.randErr A (H x y 3) (fun v w => decide ((H x y 3).Adj v w)) T
        (decide (∃ C : Finset (HV L 3), ((H x y 3).power 2).IsVertexCover ↑C ∧
          C.card ≤ 4 * (2 ^ L - 1) + 4 * L + 2 * (2 * 2 ^ L + 4 * 2 ^ L * L + 8 * L))) : ℝ) ≤
        ε * Fintype.card (HV L 3 → ρ)) :
    κ * 4 ^ L ≤ T * (8 * L * B) + 2 := by
  have h := (hFamily L 3).rand_lowerBound A T (fun x y => !Protocol.disj x y) ε (fun x y => by
    have e : (!Protocol.disj x y) = decide (∃ C : Finset (HV L 3),
        ((H x y 3).power 2).IsVertexCover ↑C ∧
          C.card ≤ 4 * (2 ^ L - 1) + 4 * L + 2 * (2 * 2 ^ L + 4 * 2 ^ L * L + 8 * L)) := by
      rw [Bool.eq_iff_iff, decide_eq_true_iff]
      exact ((unweightedPred_iff x y).trans (by simp)).symm
    rw [e]
    exact hA x y) ⌈κ * 4 ^ L⌉₊ (fun P b hP hb => Nat.ceil_le.2 (hCC _ _ P b hP hb))
  rw [hFamily_Ecut, card_hCut] at h
  calc κ * 4 ^ L ≤ (⌈κ * 4 ^ L⌉₊ : ℝ) := Nat.le_ceil _
    _ ≤ ((T * (2 * (4 * L * B)) + 2 : ℕ) : ℝ) := by exact_mod_cast h
    _ = T * (8 * L * B) + 2 := by push_cast; ring

end Podc.PowerGraphApproximation.LowerBound
