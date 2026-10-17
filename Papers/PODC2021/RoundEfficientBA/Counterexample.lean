import Papers.PODC2021.RoundEfficientBA.Protocol

/-!
# The paper's `t < n/3` protocol fails for `n = 5`, `t = 1` (Corollaries 3.3 and 3.8)

With the paper's threshold `n - 2t` (here `3`), `n = 5` parties and one Byzantine party, the
3-round protocol `Prox_9` violates consistency, and the resulting BA protocol (Corollary 3.8 with
`κ = 3`: 3 Proxcensus rounds + one coin uniform in `[1, 8]`) fails with probability `3/8` instead of
the claimed `2^{-3} = 1/8`.

Run (found by exhaustive search): inputs `0, 0, 0, 1` for the honest parties `0, 1, 2, 3`; party
`4` is Byzantine and echoes, to the receivers `0, 1, 2, 3`,
* round 1: `(1,0), (0,0), (0,0), (0,0)`,
* round 2: `(0,1), (0,0), (0,0), (0,1)`,
* round 3: `(0,1), (0,1), (0,2), (0,0)`.
The honest `Prox_9` outputs are `(0,2), (0,2), (0,3), (0,0)`, i.e. grades `3` and `0`, in the slots
`2, 2, 1, 4` of Figure 1, so the three coins `c ∈ {2, 3, 4}` split the honest parties
(`cex_badCoins`, `c = i + 1`).
-/

namespace RoundEfficientBA

open Cslib.Byzantine.LockStep

/-- The Byzantine echoes of party `4` in round `k` to receiver `p`. -/
def cexAdv : ℕ → Fin 5 → Option (Bool × ℕ)
  | 0, p => some (![(true, 0), (false, 0), (false, 0), (false, 0), (false, 0)] p)
  | 1, p => some (![(false, 1), (false, 0), (false, 0), (false, 1), (false, 0)] p)
  | 2, p => some (![(false, 1), (false, 1), (false, 2), (false, 0), (false, 0)] p)
  | _, _ => none

/-- The honest inputs `0, 0, 0, 1` (party `4` is Byzantine). -/
def cexIn : Fin 5 → Bool := ![false, false, false, true, false]

/-- The run: party `4` is Byzantine. -/
def cexSc : Scenario (Fin 5) Bool (Bool × ℕ) where
  byz := {4}
  input := cexIn
  adv k q p := if q = 4 then cexAdv k p else none

/-- The outputs, computed round by round (only the honest entries `0, …, 3` matter). -/
def cexSt : ℕ → Fin 5 → Bool × ℕ
  | 0, p => (cexIn p, 0)
  | k + 1, p => expandOut (2 ^ k + 1) 5 1 3 (cexSt k p)
      (viewCnt fun q => if q = 4 then cexAdv k p else some (cexSt k q))

lemma cexSc_byz (q : Fin 5) : q ∈ cexSc.byz ↔ q = 4 := by simp [cexSc]

lemma cex_roundOut (k : ℕ) (p : Fin 5) (hp : p ≠ 4) :
    roundOut 1 3 3 cexSc k p = cexSt k p := by
  induction k generalizing p with
  | zero => rw [roundOut_zero]; rfl
  | succ k ih =>
    classical
    rw [roundOut_succ _ _ _ _ (fun _ _ _ => id) k p (by rwa [cexSc_byz])]
    simp only [Fintype.card_fin, cexSt]
    rw [ih p hp]
    congr 2
    funext q
    by_cases hq : q = 4
    · simp [hq, cexSc]
    · rw [if_neg (by rwa [cexSc_byz]), if_neg hq, ih q hq]

lemma cex_final : (cexSt 3 0, cexSt 3 1, cexSt 3 2, cexSt 3 3) =
    ((false, 2), (false, 2), (false, 3), (false, 0)) := by decide

/-- **Corollary 3.3 fails for the paper's threshold** (`n = 5`, `t = 1`, `r = 3`): the honest outputs
of `Prox_9` have grades `3` and `0`. -/
theorem paper_cor33_counterexample :
    cexSc.byz.ncard ≤ 1 ∧ cexSc.Reliable ∧ 3 * 1 < Fintype.card (Fin 5) ∧
      ¬ ProxSpec (2 ^ 3 + 1) cexSc.input cexSc.honest
        (Decides ⊤ (proxProtocol 1 (Fintype.card (Fin 5) - 2 * 1) 3) cexSc) := by
  rw [show Fintype.card (Fin 5) - 2 * 1 = 3 by simp]
  refine ⟨by simp [cexSc], fun _ _ _ => id, by simp, fun h => ?_⟩
  have h2 : (2 : Fin 5) ∈ cexSc.honest := by simp [Scenario.honest, cexSc]
  have h3 : (3 : Fin 5) ∈ cexSc.honest := by simp [Scenario.honest, cexSc]
  have := (h.2 _ (fun p _ => (decides_proxProtocol_iff _ _ _ _ p _).2 rfl)).consistency
    2 h2 3 h3
  rw [cex_roundOut 3 2 (by decide), cex_roundOut 3 3 (by decide)] at this
  have e := cex_final
  simp only [Prod.mk.injEq] at e
  rw [e.2.2.1, e.2.2.2] at this
  exact absurd this.1 (by decide)

/-- The coins `c = i + 1 ∈ [1, 8]` that split the honest parties of the run. -/
lemma cex_badCoins :
    {i : Fin (2 ^ 3) | ∃ p ∈ cexSc.honest, ∃ q ∈ cexSc.honest,
      extract (2 ^ 3 + 1) (roundOut 1 3 3 cexSc 3 p) (i + 1) ≠
        extract (2 ^ 3 + 1) (roundOut 1 3 3 cexSc 3 q) (i + 1)} =
      {i | i = 1 ∨ i = 2 ∨ i = 3} := by
  have hh : ∀ p : Fin 5, p ∈ cexSc.honest ↔ p ≠ 4 := fun p => by
    simp [Scenario.honest, cexSc]
  ext i
  simp only [Set.mem_setOf_eq, hh]
  constructor
  · rintro ⟨p, hp, q, hq, hne⟩
    rw [cex_roundOut 3 p hp, cex_roundOut 3 q hq] at hne
    revert hne
    revert p q
    decide +revert
  · intro hi
    refine ⟨2, by decide, 3, by decide, ?_⟩
    rw [cex_roundOut 3 2 (by decide), cex_roundOut 3 3 (by decide)]
    revert hi; revert i
    decide

/-- **Corollary 3.8 (`t < n/3`) fails for the paper's threshold**: with `n = 5`, `t = 1`, `κ = 3`
(three Proxcensus rounds and a uniform coin in `[1, 8]`), the honest parties disagree with
probability `3/8`, not at most `2^{-3} = 1/8`. -/
theorem paper_cor38_counterexample :
    cexSc.byz.ncard ≤ 1 ∧ cexSc.Reliable ∧ 3 * 1 < Fintype.card (Fin 5) ∧
      (PMF.uniformOfFintype (Fin (2 ^ 3))).toOuterMeasure
        {i | ∃ p ∈ cexSc.honest, ∃ q ∈ cexSc.honest,
          extract (2 ^ 3 + 1) (roundOut 1 (Fintype.card (Fin 5) - 2 * 1) 3 cexSc 3 p) (i + 1) ≠
            extract (2 ^ 3 + 1) (roundOut 1 (Fintype.card (Fin 5) - 2 * 1) 3 cexSc 3 q) (i + 1)}
        = 3 / 8 := by
  rw [show Fintype.card (Fin 5) - 2 * 1 = 3 by simp]
  refine ⟨by simp [cexSc], fun _ _ _ => id, by simp, ?_⟩
  rw [cex_badCoins, PMF.toOuterMeasure_uniformOfFintype_apply]
  have : Fintype.card {i : Fin (2 ^ 3) | i = 1 ∨ i = 2 ∨ i = 3} = 3 := by decide
  rw [this]
  simp

end RoundEfficientBA
