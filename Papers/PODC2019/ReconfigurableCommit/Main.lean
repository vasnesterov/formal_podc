/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Papers.PODC2019.ReconfigurableCommit.Init
import Papers.PODC2019.ReconfigurableCommit.Steps1
import Papers.PODC2019.ReconfigurableCommit.Steps2
import Papers.PODC2019.ReconfigurableCommit.StepsProbe
import Papers.PODC2019.ReconfigurableCommit.StepsRecon
import Papers.PODC2019.ReconfigurableCommit.StepsCAS
import Papers.PODC2019.ReconfigurableCommit.StepsPrep
import Papers.PODC2019.ReconfigurableCommit.StepsNC
import Papers.PODC2019.ReconfigurableCommit.Safety

/-!
# Theorem 4.1 for the corrected protocol

The invariant `Inv` is inductive (`Inv.step`), hence holds in every reachable state
(`inv_reachable`), and it implies TCS-LL (Lemma A.1, `Inv.tcsll`) and correctness (`theorem_4_1`).
-/

namespace Podc.ReconfigurableCommit

variable {T Pl S P : Type} [DecidableEq T] [DecidableEq Pl] [DecidableEq S] [DecidableEq P]
  [Fintype S]

variable {Pa : Params T Pl S P} {st st' : State T Pl S P}

/-- Every step of the corrected protocol preserves the invariant. -/
theorem Inv.step (hfix : Pa.fixNewConfig = true) (hsh : ∀ t, (Pa.σ.shards t).Nonempty)
    (hI : Inv Pa st) {a : Action T Pl S P} (h : step Pa st a = some st') : Inv Pa st' := by
  cases a with
  | certify p t l => exact hI.step_certify h
  | decide p t ks ds => exact hI.step_decide hsh h
  | reconfigure p s => exact hI.step_reconfigure h
  | probeDone p q M => exact hI.step_probeDone h
  | probeSkip p q => exact hI.step_probeSkip h
  | configChange p s e => exact hI.step_configChange h
  | retry p k => exact hI.step_retry h
  | deliver src dst i =>
    obtain ⟨m, hm, h⟩ := step_deliver h
    have hI₁ := hI.erase src dst i
    have hmS : m ∈ (st.erase src dst i).sent src dst :=
      (hI.net_sub src dst).subset (List.mem_of_getElem? hm)
    cases m with
    | prepare t lo => exact hI₁.deliver_prepare hmS h
    | prepareAck e s k t l d => exact hI₁.deliver_prepareAck hmS h
    | accept e k t l d => exact hI₁.deliver_accept hmS h
    | acceptAck s e k t d => exact hI₁.deliver_acceptAck hmS h
    | decision e k d => exact hI₁.deliver_decision hmS h
    | probe e => exact hI₁.deliver_probe hmS h
    | probeAck b e s => exact hI₁.deliver_probeAck hmS h
    | newConfig e M => exact hI.deliver_newConfig hfix hm h
    | newState e M a =>
      exact hI₁.deliver_newState hmS (hI.ns_flight _ _ _ _ _ (List.mem_of_getElem? hm))
        (fun p M' a' => hI.ns_gone hm p M' a') h

/-- The invariant holds in every reachable state of the corrected protocol. -/
theorem inv_reachable (hfix : Pa.fixNewConfig = true) (hinit : ValidInit Pa)
    (hsh : ∀ t, (Pa.σ.shards t).Nonempty) (hr : Reachable Pa st) : Inv Pa st := by
  induction hr with
  | refl => exact inv_init Pa hinit
  | tail _ hstep ih =>
    obtain ⟨a, ha⟩ := hstep
    exact ih.step hfix hsh ha

/-- **Lemma A.1 of [Bravo–Gotsman 2019]** (without constraint (12)): the histories of the
corrected protocol satisfy TCS-LL. -/
theorem lemma_A_1 (hfix : Pa.fixNewConfig = true) (hinit : ValidInit Pa)
    (hsh : ∀ t, (Pa.σ.shards t).Nonempty) (hfs : ∀ s, Distributive (Pa.fs s))
    (hgs : ∀ s, Distributive (Pa.gs s)) (hr : Reachable Pa st) :
    TCSLL Pa.σ Pa.fs Pa.gs st.hist :=
  (inv_reachable hfix hinit hsh hr).tcsll hfs hgs

/-- **Theorem 4.1 of [Bravo–Gotsman 2019]**, for the protocol of Figure 1 with the check
`e ≥ new_epoch` in the `NEW_CONFIG` handler (line 56; the paper's pattern
`NEW_CONFIG(new_epoch, M)` checks `e = new_epoch`, so its executions are executions of this model): every history of the transaction
certification service is well-formed and correct w.r.t. a certification function `f` matched by the
shard-local functions `fₛ`, `gₛ` (conditions (1), (3)–(5)), provided `fₛ({ε}, l) = commit`
(`EpsNeutral`), every configuration has at least one follower (`ValidInit` and line 48) and every
transaction accesses at least one shard. -/
theorem theorem_4_1 (hfix : Pa.fixNewConfig = true) (hinit : ValidInit Pa)
    (hsh : ∀ t, (Pa.σ.shards t).Nonempty) {f : Finset Pl → Pl → Dec}
    (hm : Matching Pa.σ f Pa.fs Pa.gs) (heps : EpsNeutral Pa.σ Pa.fs) (hr : Reachable Pa st) :
    WellFormed st.hist ∧ Correct f st.hist :=
  ⟨(inv_reachable hfix hinit hsh hr).wellFormed, (inv_reachable hfix hinit hsh hr).correct hm heps⟩

end Podc.ReconfigurableCommit
