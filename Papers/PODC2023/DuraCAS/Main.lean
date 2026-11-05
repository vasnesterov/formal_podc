import Papers.PODC2023.DuraCAS.ADurLin
import Papers.PODC2023.DuraCAS.Refinement
import Papers.PODC2023.DuraCAS.WaitFree
import Papers.PODC2023.DuraCAS.Counterexample

/-!
# Main results for DuraCAS (PODC 2023, brief announcement)

* `theorem_4_1_1` — Theorem 4.1(1), repaired: under the **per-process** recovery discipline, every
  history of DuraCAS (with the DurEC code inlined, over hardware CAS, any number of processes and
  objects, individual crashes) is durably linearizable w.r.t. writable CAS and detectable.
* `theorem_4_1_1_false` — Theorem 4.1(1) as stated is false: under the brief announcement's
  **per-object** recovery discipline a history is not durably linearizable.
* `waitFree` (in `WaitFree.lean`) — Theorem 4.1(2): every operation and `RECOVER` completes within
  `54` steps of its process.
-/

namespace Podc.DuraCAS

variable {P K V : Type} [DecidableEq P] [DecidableEq K] [DecidableEq V]

/-- **Theorem 4.1(1) of the brief announcement (= Theorem 6.1(1) of the full version), under the
per-process recovery discipline.** Every reachable history of DuraCAS is durably linearizable (w.r.t.
the sequential specification of writable CAS objects with initial values `init`) and detectable. -/
theorem theorem_4_1_1 {init : K → V} {hv0 : Hd P → V × Bool} {s : St P K V}
    (h : Reach init hv0 s) : DurLinDet init s.hist := by
  obtain ⟨a, ha, hh⟩ := reach_aReach h
  rw [← hh]
  exact aReach_durLinDet ha

/-- **Theorem 4.1(1) is false as stated**: with the per-object recovery discipline of the brief
announcement ("execute `O.Recover()` before invoking any other operation on `O`"), two processes and
two DuraCAS objects suffice to produce a history that is not durably linearizable. -/
theorem theorem_4_1_1_false :
    ∃ s : St (Fin 2) (Fin 2) ℕ, ReachPO (fun _ => 0) (fun _ => (0, false)) s ∧
      ¬ DurLinearizable (fun _ => (0 : ℕ)) s.hist :=
  perObject_counterexample

end Podc.DuraCAS
