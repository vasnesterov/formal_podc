import Papers.PODC2020.DetectableSpace.Alg1StepLocal
import Papers.PODC2020.DetectableSpace.Alg1StepRec
import Papers.PODC2020.DetectableSpace.Alg1StepA
import Papers.PODC2020.DetectableSpace.Alg1StepEv
import Papers.PODC2020.DetectableSpace.Alg1StepCrash

/-!
# Lemma 1 for the corrected Algorithm 1

With `R` initially `⟨v_init, 0, 1⟩` (the initial value is attributed to a fictitious write of
process `0` with toggle index `1`, while `T_0` is initially `0`), Algorithm 1 is durably
linearizable and detectable (`alg1fix_durLinDet`) and wait-free (`alg1_boundedSteps`), for every
number of processes `n ≥ 1` and every value domain `V`.
-/

set_option linter.unusedSectionVars false

namespace Papers.PODC2020.DetectableSpace

open Cslib.SharedMemory

namespace Alg1

variable {V : Type} [DecidableEq V] {n : ℕ} [NeZero n] {v₀ : V}

/-- Every event preserves the invariant. -/
theorem step_ok {C : Cfg1 V v₀ n} {g : Ghost V n} {h : Hist V n} {L : LinL V}
    (hI : Inv v₀ C g h L) (e : Ev (Fin n) (RWOp V)) : StepOK C h e := by
  match e with
  | .inv r o => exact step_inv hI r o
  | .crash => exact step_crash hI
  | .step r =>
    cases hr : C.ps r with
    | idle =>
      rw [StepOK]
      refine ⟨g, L, ?_⟩
      simp only [RImpl.step1, hr, List.append_nil]
      exact hI
    | run a o b l =>
      cases l with
      | w1 v => exact step_w1 hI hr
      | w2 v tr => exact step_w2 hI hr
      | w3 v tr => exact step_w3 hI hr
      | w4 v tr mt => exact step_w4 hI hr
      | w5 v tr mt => exact step_w5 hI hr
      | w6 v tr mt => exact step_w6 hI hr
      | w7 v tr mt => exact step_w7 hI hr
      | w8 v tr mt => exact step_w8 hI hr
      | w9 v tr mt i => exact step_w9 hI hr
      | w11 v tr mt => exact step_w11 hI hr
      | w12 v tr mt => exact step_w12 hI hr
      | r14 v => exact step_r14 hI hr
      | r15 v tr mt => exact step_r15 hI hr
      | r17 v tr mt => exact step_r17 hI hr
      | r19 v tr mt => exact step_r19 hI hr
      | r20 v tr mt => exact step_r20 hI hr
      | r20b v tr mt => exact step_r20b hI hr
      | d1 => exact step_d1 hI hr
      | d2 x => exact step_d2 hI hr
      | dr => exact step_dr hI hr
      | ret x => exact step_ret hI hr

end Alg1

open Alg1

/-- **Lemma 1 (corrected).** Algorithm 1 with `R` initially `⟨v_init, 0, 1⟩` satisfies durable
linearizability and detectability, for any number `n ≥ 1` of processes and any value domain. -/
theorem alg1fix_durLinDet {V : Type} [DecidableEq V] (v₀ : V) (n : ℕ) [NeZero n] :
    (alg1 V v₀ n true).DurLinDet := by
  apply RImpl.durLinDet_of_inv (alg1 V v₀ n true) (fun C h L => ∃ g, Inv v₀ C g h L)
  · exact ⟨g₀ v₀, inv_init v₀⟩
  · rintro C h L e - ⟨g, hI⟩
    obtain ⟨g', L', h'⟩ := step_ok hI e
    exact ⟨L', g', h'⟩
  · rintro C h L ⟨g, hI⟩
    exact hI.dlin
  · rintro C h L ⟨g, hI⟩
    exact hI.nf

/-- **Lemma 1 (corrected), progress.** The corrected Algorithm 1 is wait-free (bounded number
of own steps per operation and recovery function), hence obstruction-free. -/
theorem alg1fix_obstructionFree {V : Type} [DecidableEq V] (v₀ : V) (n : ℕ) [NeZero n] :
    (alg1 V v₀ n true).ObstructionFree :=
  alg1_obstructionFree v₀ n true

end Papers.PODC2020.DetectableSpace
