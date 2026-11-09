import Papers.PODC2010.MobileDataSearch.TwoRounds

/-!
# Lemma 4: the merging step of the paper's proof fails

Bar-Noy, Cheilaris, Feng, Levin, *Finding mobile data under delay constraints with searching costs*,
PODC 2010, Lemma 4.

The paper merges the boxes of an instance `I_N` into four boxes `C_A, C_B, C_C, C_D`
(`A = X ∩ X'`, `B = X' \ X`, `C = Y' \ Y`, `D = Y ∩ Y'` for `OPT_N = ⟨X, Y⟩`, `FRO_N = ⟨X', Y'⟩`)
and claims that FRO on the merged instance `I_4` outputs `⟨{C_A, C_B}, {C_C, C_D}⟩`, hence
`cost(FRO_4) ≥ cost(FRO_N)` and `cost(FRO_N)/cost(OPT_N) ≤ cost(FRO_4)/cost(OPT_4)`.
FRO on `I_4` minimises over *all* prefixes of the ratio order of `I_4`, and these need not be
prefixes of `I_N`, so FRO can do strictly better on `I_4`. Counterexample with `N = 5`
(boxes in strict ratio order `8 > 1 > 6/7 > 5/6 > 1/4`):
`p = (8, 1, 6, 5, 1)`, `w = (1, 1, 7, 6, 4)`. `FRO_N = ⟨{0,1}, {2,3,4}⟩` with cost `246`,
`OPT_N = ⟨{0,3}, {1,2,4}⟩` with cost `243`; `A = {0}`, `B = {1}`, `C = {3}`, `D = {2,4}`; the merged
instance `p = (8, 1, 5, 7)`, `w = (1, 1, 6, 11)` (already in strict ratio order) has
`FRO_4 = ⟨{C_A,C_B,C_C}, {C_D}⟩` with cost `245 < 246`, and `OPT_4` costs `243`.
So the ratio drops from `246/243` to `245/243`.
-/

namespace Podc.MobileDataSearch

open Finset

variable {N : ℕ}

/-- Gain over `ℕ`, for `decide`. -/
def gainN (pN wN : Fin N → ℕ) (S : Finset (Fin N)) : ℕ :=
  (∑ i ∈ S, pN i) * ∑ i ∈ Sᶜ, wN i

lemma gain_cast (pN wN : Fin N → ℕ) (S : Finset (Fin N)) :
    gain (fun i => (pN i : ℝ)) (fun i => (wN i : ℝ)) S = (gainN pN wN S : ℝ) := by
  simp [gain, gainN]

lemma cost_cast (pN wN : Fin N → ℕ) (A : Strategy N 2) :
    cost (fun i => (pN i : ℝ)) (fun i => (wN i : ℝ)) A =
      ((∑ i, pN i) * (∑ i, wN i) : ℕ) - (gainN pN wN (firstRound A) : ℝ) := by
  rw [cost_two, gain_cast]; push_cast; rfl

lemma ratioSorted_cast (pN wN : Fin N → ℕ) (h : ∀ i j : Fin N, i ≤ j → pN j * wN i ≤ pN i * wN j) :
    RatioSorted (fun i => (pN i : ℝ)) (fun i => (wN i : ℝ)) := fun i j hij => by
  simp only; exact_mod_cast h i j hij

/-- FRO cost from a `decide`-checked table of prefix gains. -/
lemma fro_cost_nat (pN wN : Fin N → ℕ) (g k0 : ℕ) (hk0 : gainN pN wN (pref N k0) = g)
    (hmax : ∀ k : Fin (N + 1), gainN pN wN (pref N k) ≤ g) {A : Strategy N 2}
    (hA : IsFRO (fun i => (pN i : ℝ)) (fun i => (wN i : ℝ)) A) :
    cost (fun i => (pN i : ℝ)) (fun i => (wN i : ℝ)) A =
      ((∑ i, pN i) * (∑ i, wN i) : ℕ) - (g : ℝ) := by
  obtain ⟨k, hk, rfl⟩ := monotone_eq_prefixStrategy A hA.1
  have h1 := hA.2 (prefixStrategy k0) (prefixStrategy_monotone k0)
  rw [cost_cast, cost_cast, firstRound_prefixStrategy, firstRound_prefixStrategy, hk0] at h1
  rw [cost_cast, firstRound_prefixStrategy]
  have := hmax ⟨k, Nat.lt_succ_of_le hk⟩
  have : (gainN pN wN (pref N k) : ℝ) ≤ g := by exact_mod_cast this
  linarith

/-- Optimal cost from a `decide`-checked bound on all gains. -/
lemma opt_cost_nat (pN wN : Fin N → ℕ) (g : ℕ) (S0 : Finset (Fin N))
    (hS0 : gainN pN wN S0 = g) (hmax : ∀ S, gainN pN wN S ≤ g) {B : Strategy N 2}
    (hB : IsOptimal (fun i => (pN i : ℝ)) (fun i => (wN i : ℝ)) B) :
    cost (fun i => (pN i : ℝ)) (fun i => (wN i : ℝ)) B =
      ((∑ i, pN i) * (∑ i, wN i) : ℕ) - (g : ℝ) := by
  have h1 := hB (ofFirstRound S0)
  rw [cost_cast, cost_cast, firstRound_ofFirstRound, hS0] at h1
  rw [cost_cast]
  have : (gainN pN wN (firstRound B) : ℝ) ≤ g := by exact_mod_cast hmax _
  linarith

/-- The five-box instance. -/
def p5 : Fin 5 → ℕ := ![8, 1, 6, 5, 1]
/-- The five-box instance. -/
def w5 : Fin 5 → ℕ := ![1, 1, 7, 6, 4]
/-- The merged instance `(C_A, C_B, C_C, C_D)` for `A = {0}`, `B = {1}`, `C = {3}`,
`D = {2, 4}`. -/
def p4 : Fin 4 → ℕ := ![p5 0, p5 1, p5 3, p5 2 + p5 4]
/-- The merged instance. -/
def w4 : Fin 4 → ℕ := ![w5 0, w5 1, w5 3, w5 2 + w5 4]

/-- **Lemma 4's proof step fails.** On the five-box instance (strict ratio order) FRO costs
`246` and the optimum `{0,3}` costs `243`; FRO's first round is `X' = {0,1}` and the optimal one
`X = {0,3}`, so `A = {0}`, `B = {1}`, `C = {3}`, `D = {2,4}`. On the merged instance (strict ratio
order) the optimum still costs `243`, but FRO costs `245 < 246`: `cost(FRO_4) ≥ cost(FRO_N)` and
`cost(FRO_N)/cost(OPT_N) ≤ cost(FRO_4)/cost(OPT_4)` are both false. -/
theorem lemma4_proof_step_fails :
    RatioSorted (fun i => (p5 i : ℝ)) (fun i => (w5 i : ℝ)) ∧
    RatioSorted (fun i => (p4 i : ℝ)) (fun i => (w4 i : ℝ)) ∧
    -- `FRO_N = ⟨{0,1}, {2,3,4}⟩` (unique optimal prefix) and `OPT_N = ⟨{0,3}, {1,2,4}⟩` (unique)
    (∀ k : Fin 6, k.val ≠ 2 → gainN p5 w5 (pref 5 k) < gainN p5 w5 (pref 5 2)) ∧
    (∀ S, S ≠ {0, 3} → gainN p5 w5 S < gainN p5 w5 {0, 3}) ∧
    (∀ A : Strategy 5 2, IsFRO (fun i => (p5 i : ℝ)) (fun i => (w5 i : ℝ)) A →
      cost (fun i => (p5 i : ℝ)) (fun i => (w5 i : ℝ)) A = 246) ∧
    (∀ B : Strategy 5 2, IsOptimal (fun i => (p5 i : ℝ)) (fun i => (w5 i : ℝ)) B →
      cost (fun i => (p5 i : ℝ)) (fun i => (w5 i : ℝ)) B = 243) ∧
    (∀ A : Strategy 4 2, IsFRO (fun i => (p4 i : ℝ)) (fun i => (w4 i : ℝ)) A →
      cost (fun i => (p4 i : ℝ)) (fun i => (w4 i : ℝ)) A = 245) ∧
    (∀ B : Strategy 4 2, IsOptimal (fun i => (p4 i : ℝ)) (fun i => (w4 i : ℝ)) B →
      cost (fun i => (p4 i : ℝ)) (fun i => (w4 i : ℝ)) B = 243) := by
  refine ⟨ratioSorted_cast _ _ (by decide), ratioSorted_cast _ _ (by decide), by decide,
    by decide, fun A hA => ?_, fun B hB => ?_, fun A hA => ?_, fun B hB => ?_⟩
  · rw [fro_cost_nat p5 w5 153 2 (by decide) (by decide) hA]; norm_num [p5, w5, Fin.sum_univ_five]
  · rw [opt_cost_nat p5 w5 156 {0, 3} (by decide) (by decide) hB]
    norm_num [p5, w5, Fin.sum_univ_five]
  · rw [fro_cost_nat p4 w4 154 3 (by decide) (by decide) hA]
    norm_num [p4, w4, p5, w5, Fin.sum_univ_four]
  · rw [opt_cost_nat p4 w4 156 {0, 2} (by decide) (by decide) hB]
    norm_num [p4, w4, p5, w5, Fin.sum_univ_four]

end Podc.MobileDataSearch
