import Cslib.Computability.Distributed.Byzantine.PartialSync.Sync

/-!
# Two generic tools for concrete PSync runs (CSLib candidates)

* `Run.st_map`: **equivariance**. If an algorithm `A'` is the image of `A` under maps of messages,
  states and inputs (commuting with `init`, `step`, `send`), then in runs with the same faulty set and
  delivery times and mapped inputs / Byzantine messages, the states are the images. Used to transfer a
  run computed with Boolean values to the same run with real values.
* `Run.st_eq_simStates`: in a run with zero delays on `Fin n`, the states are computed by the
  **memoised** iteration `simStates` (one list of `n` states per tick), which the kernel evaluates
  quickly; so concrete finite runs can be checked by `decide`.
-/

open Cslib.Byzantine.PartialSync

namespace HybridApproxAgreement

section Map

variable {P M M' S S' VI VI' VO VO' : Type*} [DecidableEq P]

-- CSLib candidate
/-- **Equivariance of runs** under maps of messages, states and inputs. -/
theorem Run.st_map {A : Algorithm P M S VI VO} {A' : Algorithm P M' S' VI' VO'}
    (fm : M → M') (fs : S → S') (fi : VI → VI')
    (hinit : ∀ p v, A'.init p (fi v) = fs (A.init p v))
    (hstep : ∀ p s ib, A'.step p (fs s) (fun q => (ib q).map fm) = fs (A.step p s ib))
    (hsend : ∀ p s q, A'.send p (fs s) q = (A.send p s q).map fm)
    {R : Run P M VI} {R' : Run P M' VI'} (hf : R'.faulty = R.faulty)
    (hi : ∀ p, R'.inp p = fi (R.inp p)) (hb : ∀ q τ p, R'.byz q τ p = (R.byz q τ p).map fm)
    (hdl : R'.dl = R.dl) : ∀ τ p, R'.st A' τ p = fs (R.st A τ p) := by
  intro τ
  induction τ using Nat.strong_induction_on with
  | _ τ ih =>
    intro p
    rcases τ with _ | τ
    · simp [hi, hinit]
    · rw [Run.st_succ, Run.st_succ, ih τ (by omega)]
      have hout : ∀ σ ≤ τ, ∀ q r, R'.out A' q σ r = (R.out A q σ r).map fm := by
        intro σ hσ q r
        by_cases hq : q ∈ R.faulty
        · rw [Run.out_of_faulty _ _ (hf ▸ hq), Run.out_of_faulty _ _ hq, hb]
        · rw [Run.out_of_correct _ _ (hf ▸ hq), Run.out_of_correct _ _ hq, ih σ (by omega), hsend]
      have hin : R'.inbox A' p τ = fun q => (R.inbox A p τ q).map fm := by
        funext q
        rw [Run.inbox_eq_flatMap, Run.inbox_eq_flatMap, List.map_flatMap]
        refine List.flatMap_congr fun σ hσ => ?_
        simp only [List.mem_range] at hσ
        simp only [Run.dlv, hdl]
        split_ifs
        · exact hout σ (by omega) q p
        · rfl
      rw [hin, hstep]

end Map

section Sim

variable {n : ℕ} {M S VI VO : Type*}

/-- Memoised computation of the states of a zero-delay run on `Fin n` (faulty parties `bad`,
Byzantine messages `byz`); `d` is a dummy state for out-of-range indices. -/
def simStates (A : Algorithm (Fin n) M S VI VO) (inp : Fin n → VI) (bad : Fin n → Bool)
    (byz : Fin n → ℕ → Fin n → List M) (d : S) : ℕ → List S
  | 0 => List.ofFn fun p => A.init p (inp p)
  | τ + 1 =>
    let v := simStates A inp bad byz d τ
    List.ofFn fun p => A.step p (v.getD p d) fun q => if bad q then byz q τ p else A.send q (v.getD q d) p

theorem getD_ofFn {α : Type*} (f : Fin n → α) (p : Fin n) (d : α) :
    (List.ofFn f).getD p d = f p := by
  simp [List.getD_eq_getElem?_getD]

-- CSLib candidate
theorem Run.st_eq_simStates (A : Algorithm (Fin n) M S VI VO) {R : Run (Fin n) M VI}
    (hdl : ∀ q τ p, R.dl q τ p = τ) {bad : Fin n → Bool} (hbad : ∀ q, bad q = true ↔ q ∈ R.faulty)
    (d : S) : ∀ τ (p : Fin n), R.st A τ p = (simStates A R.inp bad R.byz d τ).getD p d := by
  intro τ
  induction τ with
  | zero => intro p; simp [simStates]
  | succ τ ih =>
    intro p
    rw [Run.st_succ]
    simp only [simStates, getD_ofFn]
    rw [← ih p]
    congr 1
    funext q
    rw [Run.inbox_of_dl_eq _ hdl]
    by_cases hq : q ∈ R.faulty
    · rw [Run.out_of_faulty _ _ hq, ite_eq_left ((hbad q).2 hq)]
    · rw [Run.out_of_correct _ _ hq, ite_eq_right (fun h => hq ((hbad q).1 h)), ih q]

end Sim

end HybridApproxAgreement
