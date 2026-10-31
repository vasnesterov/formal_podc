import Papers.PODC2018.NestingSafeRecoverable.Alg1Cases
import Papers.PODC2018.NestingSafeRecoverable.Alg1Events
import Papers.PODC2018.NestingSafeRecoverable.Alg1Write

/-!
# Lemma 2 of [ABH18]: Algorithm 1 satisfies NRL

Under the environment assumption `Env1 v₀` (all written values are distinct and differ from the
initial value `v₀`), every history of Algorithm 1 is recoverable well-formed (Lemma 1, for any
algorithm of the model) and its crash-free projection `N(H)` is linearizable with respect to the
register specification `register V v₀`. The proof maintains the invariant `Inv` along every
execution (see `Alg1Inv.lean`).
-/

set_option linter.unusedSectionVars false

namespace Podc.NestingSafeRecoverable

open Cslib.SharedMemory Cslib.SharedMemory.NRL

variable {P V : Type} [DecidableEq P] [DecidableEq V] {v₀ : V}

namespace Alg1

/-- The invariant is preserved by every event (whose resulting history obeys `Env1`). -/
theorem Inv.ev {C : (alg1 P V v₀).Cfg} {L : List (OpId P × RWOp V)} {G : Set V}
    (hI : Inv C L G) (e : Ev P (register V v₀)) (henv : Env1 v₀ (N (C.ev e).hist)) :
    ∃ L' G', Inv (C.ev e) L' G' := by
  rcases e with ⟨p, o⟩ | p | p
  · obtain ⟨L', h⟩ := hI.ev_inv henv; exact ⟨L', G, h⟩
  · rcases hs : C.st p with _ | ⟨o, pc, v⟩
    · rw [Alg.ev_step_of_none C hs]; exact ⟨L, G, hI⟩
    · rcases o with _ | val
      · obtain ⟨L', h⟩ := hI.step_read hs; exact ⟨L', G, h⟩
      · by_cases hpc : pc = .w4
        · subst hpc
          obtain ⟨h', he⟩ := Alg.ev_hist C (.step p)
          rw [he, N_append] at henv
          exact hI.step_w4 henv.of_append hs
        · obtain ⟨L', h⟩ := hI.step_write hs hpc; exact ⟨L', G, h⟩
  · obtain ⟨L', h⟩ := hI.ev_crash p; exact ⟨L', G, h⟩

/-- Every execution whose history obeys `Env1` satisfies the invariant. -/
theorem inv_run (es : List (Ev P (register V v₀)))
    (henv : Env1 v₀ (N ((alg1 P V v₀).init.run es).hist)) :
    ∃ L G, Inv ((alg1 P V v₀).init.run es) L G := by
  induction es using List.reverseRecOn with
  | nil => exact ⟨[], {v₀}, inv_init⟩
  | append_singleton es e ih =>
    rw [Alg.Cfg.run_concat] at henv ⊢
    obtain ⟨h', he⟩ := Alg.ev_hist ((alg1 P V v₀).init.run es) e
    obtain ⟨L, G, hI⟩ := ih (by rw [he, N_append] at henv; exact henv.of_append)
    exact hI.ev e henv

end Alg1

open Alg1 in
/-- **Lemma 2** of [ABH18]: Algorithm 1 satisfies NRL (for histories in which all written values
are distinct and differ from the initial value). -/
theorem lemma2 : (alg1 P V v₀).NRL (Env1 v₀) :=
  (Alg.nrl_iff _).2 fun es he =>
    let ⟨L, _, hI⟩ := inv_run es he
    ⟨L, hI.lin⟩

end Podc.NestingSafeRecoverable
