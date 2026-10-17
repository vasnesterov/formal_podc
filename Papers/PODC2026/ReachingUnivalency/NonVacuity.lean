import Papers.PODC2026.ReachingUnivalency.Corrected

/-!
# Reaching Univalency — non-vacuity of the corrected Lemma 6

A concrete instance satisfying all hypotheses of `lemma6_corrected_sampling` with an actual
Byzantine processor: `n = k = 8`, `ε = 1/12`, `f = 1` (`F = {7}`), committees `{0..3}` and `{4..7}`,
exactly uniform samples (every processor samples everybody once in steps 1, 2 and every member of
its committee twice in step 3), ideal committee instances. For **every** input vector and **every**
behaviour of the Byzantine processor the corrected protocol achieves ε-BA (`nonvacuous`).
-/

namespace ReachingUnivalency.RPK.NonVacuity

open Finset

/-- Committees `{0..3}` and `{4..7}`. -/
def C : Fin 2 → Finset (Fin 8) := fun r => univ.filter fun p => decide (p.val < 4) = decide (r = 0)

/-- Exactly uniform samples. -/
def σ : Sampling 8 8 where
  val _ _ j := j
  resp _ _ j := j
  comm r _ j := ⟨4 * r.val + j.val % 4, by omega⟩

lemma l1_univ : ∑ i ∈ (univ : Finset (Fin 8)),
    |(mult (fun j : Fin 8 => j) i : ℚ) / 8 - 1 / (univ : Finset (Fin 8)).card| = 0 := by
  decide +kernel

lemma l1_comm (r : Fin 2) : ∑ i ∈ C r,
    |(mult (fun j : Fin 8 => (⟨4 * r.val + j.val % 4, by omega⟩ : Fin 8)) i : ℚ) / 8 -
      1 / (C r).card| = 0 := by
  revert r; decide +kernel

lemma comm_mem (r : Fin 2) (p j : Fin 8) : σ.comm r p j ∈ C r := by
  revert r p j; decide +kernel

/-- Exactly uniform samples are `(δ, 0)`-good for every `δ > 0`. -/
lemma samplingGood {δ : ℚ} (hδ : 0 < δ) : SamplingGood δ 0 σ C := by
  have key : ∀ (smp : Fin 8 → Fin 8 → Fin 8) (R : Finset (Fin 8)),
      (∀ p S, |dev (smp p) R S| ≤ 0) → SamplerGood δ 0 smp R := by
    intro smp R h S
    rw [filter_false_of_mem fun p _ h' => absurd ((h p S).trans_lt hδ) (not_lt.mpr h')]
    simp
  intro r
  refine ⟨key _ _ fun p S => ?_, key _ _ fun p S => ?_, key _ _ fun p S => ?_⟩
  · exact (abs_dev_le _ _ _ fun _ => mem_univ _).trans (by simpa [σ] using l1_univ.le)
  · exact (abs_dev_le _ _ _ fun _ => mem_univ _).trans (by simpa [σ] using l1_univ.le)
  · exact (abs_dev_le _ _ _ fun j => comm_mem r p j).trans (by simpa [σ] using (l1_comm r).le)

/-- The adversary: arbitrary Byzantine behaviour of processor `7`, ideal committees. -/
def adv (byzVal byzResp byzComm : Fin 2 → Fin 8 → Fin 8 → Option Bool)
    (tie : Fin 2 → Fin 8 → Bool) : Adversary 8 :=
  ⟨{7}, byzVal, byzResp, byzComm, tie, fun r vals => majorityOracle (C r) {7} vals⟩

/-- **Non-vacuity.** For every input and every behaviour of the Byzantine processor `7`, one level
of the corrected ε-RPK with ideal committees achieves ε-BA. -/
theorem nonvacuous (byzVal byzResp byzComm : Fin 2 → Fin 8 → Fin 8 → Option Bool)
    (tie : Fin 2 → Fin 8 → Bool) (inp : Fin 8 → Bool) :
    EpsBA (1/12) {7} inp (output (T1c (1/12)) σ (adv byzVal byzResp byzComm tie) inp) := by
  refine lemma6_corrected_sampling (ε := 1/12) (δ := 1/96) (M := 0)
    (adv := adv byzVal byzResp byzComm tie) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by simp [adv]; norm_num)
    (by unfold CommitteeSplit; decide)
    (fun r => ?_) (by norm_num) (fun r vals hb => majorityOracle_epsBA (by norm_num) hb vals)
    (samplingGood (by norm_num)) inp
  have : (C r).card = 4 := by revert r; decide
  rw [this]; norm_num

end ReachingUnivalency.RPK.NonVacuity
