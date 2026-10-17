import Papers.PODC2019.HardnessOptimization.MDSTheorem
import Podc.CongestLB.Randomized

/-!
# Theorem 2.1, randomized version (conditional on `CC^R(DISJ_K) = Ω(K)`)
-/

namespace HardnessOptimization

open Podc.CongestLB Protocol

variable {L : ℕ}

open Classical in
/-- **Theorem 2.1 (randomized).** Assume the randomized communication complexity bound for
(the complement of) set disjointness: every private-coin protocol computing "the inputs intersect"
on `K = k²` bits with error `≤ ε` sends at least `c · K` bits (`hCC`; Kalyanasundaram–Schnitger /
Razborov, not formalized). If a randomized CONGEST algorithm (private random strings `r v : ρ`)
decides on every `G_{x,y}`, with error probability `≤ ε`, whether there is a dominating set of size
`≤ 4 log k + 2`, then `c · k² ≤ 8 T B log k + 2`. -/
theorem theorem_2_1_randomized {σ ρ : Type} [Fintype ρ] [Nonempty ρ] {B : ℕ}
    (A : Algorithm (MV L) ((MV L → Bool) × ρ) σ B) (T : ℕ) (ε : ℝ) (c : ℕ)
    (hCC : ∀ (RA RB : Type) [Fintype RA] [Fintype RB]
      (P : Protocol ((Idx L × Idx L → Bool) × RA) ((Idx L × Idx L → Bool) × RB) Bool) (b : ℕ),
      P.RandComputes (fun x y => !disj x y) ε → P.CostLE b → c * 4 ^ L ≤ b)
    (hA : ∀ x y : Idx L × Idx L → Bool,
      (LBFamily.Algorithm.randErr A (mdsG x y) (fun v w => decide ((mdsG x y).Adj v w)) T
        (decide (∃ D : Finset (MV L), IsDominating (mdsG x y) D ∧ D.card ≤ 4 * L + 2)) : ℝ) ≤
        ε * Fintype.card (MV L → ρ)) :
    c * 4 ^ L ≤ T * (8 * L * B) + 2 := by
  have h := (mdsFamily L).rand_lowerBound A T (fun x y => !disj x y) ε (fun x y => by
    have e : (!disj x y) = decide (∃ D : Finset (MV L), IsDominating (mdsG x y) D ∧
        D.card ≤ 4 * L + 2) := by
      rw [Bool.eq_iff_iff, decide_eq_true_iff,
        show mdsG x y = mdsGraph (fun i j => x (i, j)) (fun i j => y (i, j)) from rfl, lemma_2_1_le]
      simp [disj]
    rw [e]
    exact hA x y) (c * 4 ^ L) (fun P b hP hb => hCC _ _ P b hP hb)
  rw [mdsFamily_Ecut, card_mdsCut] at h
  calc c * 4 ^ L ≤ T * (2 * (4 * L * B)) + 2 := h
    _ = T * (8 * L * B) + 2 := by ring

end HardnessOptimization
