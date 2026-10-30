import Papers.PODC2019.HardnessOptimization.MDSTheorem
import Cslib.Computability.Distributed.Congest.Randomized
import Mathlib

/-!
# Theorem 2.1, randomized version (conditional on `CC^R(DISJ_K) = Ω(K)`)
-/

namespace HardnessOptimization

open Cslib.Congest Cslib.CommunicationComplexity Protocol

variable {L : ℕ}

open Classical in
/-- **Theorem 2.1 (randomized).** Assume the randomized communication complexity bound for
(the complement of) set disjointness: every private-coin protocol computing "the inputs intersect"
on `K = k²` bits with error `≤ ε` sends at least `κ · K` bits (`hCC`; Kalyanasundaram–Schnitger /
Razborov: true for `ε = 1/3` and some real constant `κ > 0`, not formalized). The constant `κ` is
real: a natural-number constant would make the hypothesis false for large `k` whenever it is `≥ 1`
(the randomized complexity of disjointness is about `0.49 K`), leaving only the vacuous value `0`.
The statement holds for every real `κ`, so no positivity assumption is needed. The coin spaces `RA`,
`RB` must be nonempty: without that, `hCC` would force `κ ≤ 0` (`hCC_without_nonempty_degenerate`).
If a randomized CONGEST algorithm (private random strings `r v : ρ`) decides on every `G_{x,y}`, with
error probability `≤ ε`, whether there is a dominating set of size `≤ 4 log k + 2`, then
`κ · k² ≤ 8 T B log k + 2`. -/
theorem theorem_2_1_randomized {σ ρ : Type} [Fintype ρ] [Nonempty ρ] {B : ℕ}
    (A : Algorithm (MV L) ((MV L → Bool) × ρ) σ B) (T : ℕ) (ε κ : ℝ)
    (hCC : ∀ (RA RB : Type) [Fintype RA] [Fintype RB] [Nonempty RA] [Nonempty RB]
      (P : Protocol ((Idx L × Idx L → Bool) × RA) ((Idx L × Idx L → Bool) × RB) Bool) (b : ℕ),
      P.RandComputes (fun x y => !disj x y) ε → P.CostLE b → κ * 4 ^ L ≤ b)
    (hA : ∀ x y : Idx L × Idx L → Bool,
      (LBFamily.Algorithm.randErr A (mdsG x y) (fun v w => decide ((mdsG x y).Adj v w)) T
        (decide (∃ D : Finset (MV L), IsDominating (mdsG x y) D ∧ D.card ≤ 4 * L + 2)) : ℝ) ≤
        ε * Fintype.card (MV L → ρ)) :
    κ * 4 ^ L ≤ T * (8 * L * B) + 2 := by
  have h := (mdsFamily L).rand_lowerBound A T (fun x y => !disj x y) ε (fun x y => by
    have e : (!disj x y) = decide (∃ D : Finset (MV L), IsDominating (mdsG x y) D ∧
        D.card ≤ 4 * L + 2) := by
      rw [Bool.eq_iff_iff, decide_eq_true_iff,
        show mdsG x y = mdsGraph (fun i j => x (i, j)) (fun i j => y (i, j)) from rfl, lemma_2_1_le]
      simp [disj]
    rw [e]
    exact hA x y) ⌈κ * 4 ^ L⌉₊ (fun P b hP hb => Nat.ceil_le.2 (hCC _ _ P b hP hb))
  rw [mdsFamily_Ecut, card_mdsCut] at h
  calc κ * 4 ^ L ≤ (⌈κ * 4 ^ L⌉₊ : ℝ) := Nat.le_ceil _
    _ ≤ ((T * (2 * (4 * L * B)) + 2 : ℕ) : ℝ) := by exact_mod_cast h
    _ = T * (8 * L * B) + 2 := by push_cast; ring

/-- Why `hCC` in `theorem_2_1_randomized` requires nonempty coin spaces: with an empty coin space
every protocol has error count `0`, so the constant protocol "computes" `¬DISJ` at cost `0`, and the
hypothesis would force `κ ≤ 0`, making the theorem vacuous. -/
lemma hCC_without_nonempty_degenerate {ε κ : ℝ}
    (hCC : ∀ (RA RB : Type) [Fintype RA] [Fintype RB]
      (P : Protocol ((Idx L × Idx L → Bool) × RA) ((Idx L × Idx L → Bool) × RB) Bool) (b : ℕ),
      P.RandComputes (fun x y => !disj x y) ε → P.CostLE b → κ * 4 ^ L ≤ b) :
    κ ≤ 0 := by
  have := hCC Empty Unit (Protocol.ret true) 0 (fun x y => by simp [errCount]) trivial
  rw [Nat.cast_zero] at this
  exact nonpos_of_mul_nonpos_left this (by positivity)

end HardnessOptimization
