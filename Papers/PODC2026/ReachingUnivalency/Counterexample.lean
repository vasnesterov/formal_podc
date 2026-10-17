import Papers.PODC2026.ReachingUnivalency.RPK

/-!
# Reaching Univalency — Lemma 6 is false

A concrete execution of one level of ε-RPK (`n = 38`, `f = 5`, `ε = 1/5`, `k = 37`) in which

* the sampling choice is not bad in the strongest sense: for every step, every processor and
  *every* set of processors, the sample deviates from the response set by at most `1/19 < ε/2`
  (`sampling_accurate`); in particular no processor is bad and `NotBad` holds;
* both committee instances behave like an ideal BA functionality (every member outputs the
  majority of the correct members' inputs, `majorityOracle`), which is a valid ε-BA outcome
  whenever the committee is within its fault bound (`commOK`);
* yet 14 correct processors output `1` and 19 correct processors output `0`, so ε-Agreement fails
  (`nε = 7.6`).

Scenario. `C₁ = {0..18}` contains the 5 Byzantine processors `{14..18}`; `C₂ = {19..37}` is
fault-free (the "sufficiently honest" committee). Every processor samples the 37 processors other
than `13` (steps 1, 2) and the round's committee `C_r` cyclically (step 3). With `f = 5` close to `n(1/3 - ε)`,
the step-1 threshold `k(2/3 - ε/2)` can be reached for *both* values: with 16 correct zeros and 16
correct ones among the samples, the 5 Byzantine samples push a processor to `0` or to `1` as they
wish. In step 5 the 14 correct members of `C₁` see `20 + 5 = 25 ≥ 2k/3` responses `1` and keep `1`
with grade 2, while all members of `C₂` see two values above `k/3` (grade 0) and adopt the output
`0` of `C₂`, whose inputs are 16 zeros and 3 ones.
-/

namespace ReachingUnivalency.RPK.Counterexample

open Finset

/-- The committees `C₁ = {0..18}`, `C₂ = {19..37}`. -/
def C : Fin 2 → Finset (Fin 38) := fun r => univ.filter fun p => decide (p.val < 19) = decide (r = 0)

/-- The Byzantine processors `{14..18}`. -/
def F : Finset (Fin 38) := univ.filter fun p => 14 ≤ p.val ∧ p.val < 19

/-- Steps 1, 2: sample everybody except processor `13`, once. Step 3: sample the committee
cyclically (`j ↦ j mod 19`). -/
def σ : Sampling 38 37 where
  val _ _ j := (13 : Fin 38).succAbove j
  resp _ _ j := (13 : Fin 38).succAbove j
  comm r _ j := ⟨19 * r.val + j.val % 19, by omega⟩

/-- Inputs: `1` on `{0..13} ∪ {35,36,37}`, `0` on `{19..34}`. -/
def inp : Fin 38 → Bool := fun p => decide (p.val ≤ 13 ∨ 35 ≤ p.val)

/-- The adversary. -/
def adv : Adversary 38 where
  F := F
  byzVal r _ p :=
    if r = 0 then
      (if (19 ≤ p.val ∧ p.val ≤ 34) ∨ p.val ≤ 3 then some false
       else if (4 ≤ p.val ∧ p.val ≤ 12) ∨ 35 ≤ p.val then some true else none)
    else
      (if 26 ≤ p.val then some false
       else if p.val ≤ 12 ∨ (19 ≤ p.val ∧ p.val ≤ 25) then some true else none)
  byzResp r _ p :=
    if r = 0 then (if 19 ≤ p.val ∧ p.val ≤ 34 then some false else some true)
    else (if p.val ≤ 13 then some true else some false)
  byzComm _ _ _ := some false
  tie _ _ := false
  comm r vals := majorityOracle (C r) F vals

/-- The paper's step-1 threshold for `ε = 1/5`. -/
abbrev T1 : ℚ := 2/3 - (1/5 : ℚ)/2

lemma resp0 : respAt T1 σ adv inp 0 = fun p =>
    if (19 ≤ p.val ∧ p.val ≤ 34) ∨ p.val ≤ 3 then some false
    else if (4 ≤ p.val ∧ p.val ≤ 12) ∨ 35 ≤ p.val then some true else none := by
  funext p; revert p; decide +kernel

lemma vg0 : vgAt T1 σ adv inp 0 = fun p =>
    if 19 ≤ p.val ∧ p.val ≤ 34 then (false, 2) else (inp p, 0) := by
  unfold vgAt
  rw [resp0]
  funext p; revert p; decide +kernel

lemma vals1 : valsAt T1 σ adv inp 1 = fun p => decide (¬ (19 ≤ p.val ∧ p.val ≤ 34)) := by
  show step3 σ adv 0 (vgAt T1 σ adv inp 0) = _
  rw [vg0]
  funext p; revert p; decide +kernel

lemma resp1 : respAt T1 σ adv inp 1 = fun p =>
    if 26 ≤ p.val then some false
    else if p.val ≤ 12 ∨ (19 ≤ p.val ∧ p.val ≤ 25) then some true else none := by
  unfold respAt
  rw [vals1]
  funext p; revert p; decide +kernel

lemma vg1 : vgAt T1 σ adv inp 1 = fun p =>
    if p.val ≤ 13 then (true, 2) else (decide (¬ (19 ≤ p.val ∧ p.val ≤ 34)), 0) := by
  unfold vgAt
  rw [resp1, vals1]
  funext p; revert p; decide +kernel

/-- The outputs: `1` exactly on `{0..13}` (and `0` on all of `C₂`). -/
lemma output_eq : output T1 σ adv inp = fun p => decide (p.val ≤ 13) := by
  show step3 σ adv 1 (vgAt T1 σ adv inp 1) = _
  rw [vg1]
  funext p; revert p; decide +kernel

/-- ε-Agreement fails: 14 correct processors output `1`, 19 output `0`, and `nε = 7.6`. -/
theorem not_epsBA : ¬ EpsBA (1/5) F inp (output T1 σ adv inp) := by
  rw [output_eq]
  rintro ⟨X, v, hX, hXc, hagr, -⟩
  simp only [card_univ, Fintype.card_fin] at hXc
  have key : ∀ (G : Finset (Fin 38)), (∀ p ∈ G, p ∉ F ∧ decide (p.val ≤ 13) ≠ v) →
      (G.card : ℚ) < 38 * (1/5) := by
    intro G hG
    refine lt_of_le_of_lt ?_ hXc
    refine Nat.cast_le.mpr (card_le_card fun p hp => ?_)
    by_contra hpX
    exact (hG p hp).2 (hagr p (by simp [(hG p hp).1]) hpX)
  cases v
  · have := key (univ.filter fun p : Fin 38 => p.val ≤ 13) (by decide)
    rw [show (univ.filter fun p : Fin 38 => p.val ≤ 13).card = 14 by decide] at this
    norm_num at this
  · have := key (univ.filter fun p : Fin 38 => 19 ≤ p.val) (by decide)
    rw [show (univ.filter fun p : Fin 38 => 19 ≤ p.val).card = 19 by decide] at this
    norm_num at this

/-! ### The hypotheses of Lemma 6 hold -/

lemma l1_val : ∑ i ∈ (univ : Finset (Fin 38)),
    |(mult (fun j : Fin 37 => (13 : Fin 38).succAbove j) i : ℚ) / 37 - 1 / (univ : Finset (Fin 38)).card|
      < 1/10 := by
  decide +kernel

lemma l1_comm (r : Fin 2) : ∑ i ∈ C r,
    |(mult (fun j : Fin 37 => (⟨19 * r.val + j.val % 19, by omega⟩ : Fin 38)) i : ℚ) / 37 -
      1 / (C r).card| < 1/10 := by
  revert r; decide +kernel

lemma samplesInCommittee : SamplesInCommittee σ C := by
  unfold SamplesInCommittee; decide +kernel

/-- The sampling choice is accurate to within `ε/2 = 1/10` on **every** set, for every processor
and every step (deviation `≤ 1/19` in steps 1, 2 and `≤ 36/703` in step 3). -/
theorem sampling_accurate : Accurate σ (1/10) C := by
  intro r p S
  refine ⟨?_, ?_, ?_⟩
  · exact lt_of_le_of_lt (abs_dev_le _ _ _ fun _ => mem_univ _) (by simpa [σ] using l1_val)
  · exact lt_of_le_of_lt (abs_dev_le _ _ _ fun _ => mem_univ _) (by simpa [σ] using l1_val)
  · exact lt_of_le_of_lt (abs_dev_le _ _ _ fun j => samplesInCommittee r p j)
      (by simpa [σ] using l1_comm r)

/-- Hence no processor is bad, and the sampling is not bad. -/
theorem notBad : NotBad T1 σ adv (1/5) C inp :=
  notBad_of_accurate T1 σ adv inp
    ((show (1 : ℚ)/5/2 = 1/10 by norm_num) ▸ sampling_accurate) (by norm_num)

lemma committeeSplit : CommitteeSplit C := by
  unfold CommitteeSplit; decide +kernel

lemma card_F : F.card = 5 := by decide

/-- The committee instances are ideal: valid ε-BA outcomes whenever within the fault bound. -/
lemma commOK : CommOK adv (1/5) C := fun r vals hb =>
  majorityOracle_epsBA (by norm_num) hb vals

/-- **Lemma 6 is false**, even for samplings that are not bad in the strongest sense
(`sampling_accurate`) and committees that behave as an ideal agreement functionality. -/
theorem lemma6_false : ¬ Lemma6Claim := by
  intro h
  refine not_epsBA (h 38 37 (1/5) C σ adv inp (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) ?_ committeeSplit samplesInCommittee commOK notBad)
  show ((F.card : ℕ) : ℚ) < 38 * (1/3 - 1/5)
  rw [card_F]; norm_num

end ReachingUnivalency.RPK.Counterexample
