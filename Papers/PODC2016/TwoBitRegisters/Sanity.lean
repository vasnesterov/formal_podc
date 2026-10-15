import Papers.PODC2016.TwoBitRegisters.Liveness
import Papers.PODC2016.TwoBitRegisters.Safety
import Cslib.Computability.Distributed.MessagePassing.FairExec

/-!
# Sanity checks: the hypotheses of the main theorems are not vacuous

A concrete execution of `alg 0 1 0` with `n = 3` processes (`Fin 3`), writer `0`, `t = 1`,
values in `ℕ` (initial value `0`): `p₀` writes `5`, then `p₁` reads `5`; all messages are then
delivered and the system becomes quiescent. Extending it by stuttering gives an infinite **fair**,
`1`-resilient execution (`fair_exec_exists`), to which the liveness theorem applies. So neither
the safety theorem (the history has completed operations) nor the liveness theorem (fair
executions with operations exist) is vacuous.
-/

namespace Podc.TwoBit.Sanity

open Cslib.SharedMemory Cslib.AsyncMP

/-- The algorithm for `n = 3`, writer `0`, `t = 1`, values `ℕ` with initial value `0`. -/
abbrev A3 := alg (0 : Fin 3) 1 (0 : ℕ)

/-- `p₀` writes `5`; `p₁` reads; all messages delivered. -/
def run : List (Step (Fin 3) (register ℕ 0) (Msg ℕ) (Act (Fin 3))) :=
  [.inv 0 (.write 5), .recv 0 1 (.write true 5), .recv 1 0 (.write true 5), .internal 0 .wret,
   .inv 1 .read, .recv 1 0 .read, .internal 0 (.proceed 1 1), .recv 0 1 .proceed,
   .internal 1 .r8, .internal 1 .rret,
   .recv 0 2 (.write true 5), .recv 1 2 (.write true 5), .recv 2 0 (.write true 5),
   .recv 2 1 (.write true 5), .recv 1 2 .read, .internal 2 (.proceed 1 1), .recv 2 1 .proceed]

/-- The history of `run`: the write of `5` completes, then a read returns `5`. -/
def runHist : List (Label (Fin 3) (register ℕ 0)) :=
  [.inv 0 (.write 5), .ret 0 5, .inv 1 .read, .ret 1 5]

set_option maxRecDepth 100000 in
theorem run_spec : ∃ C, A3.runFrom A3.initCfg run = some (C, runHist) ∧ C.net = 0 ∧
    C.crashed = ∅ ∧ ∀ p, (C.loc p).phase = .idle ∧ (C.loc p).tasks = 0 :=
  ⟨_, rfl, rfl, rfl, by decide⟩

theorem run_quiescent {C : Cfg (Fin 3) ℕ} (hnet : C.net = 0)
    (hidle : ∀ p, (C.loc p).phase = .idle ∧ (C.loc p).tasks = 0)
    (s : Step (Fin 3) (register ℕ 0) (Msg ℕ) (Act (Fin 3))) (p : Fin 3) (hs : s.owner = some p) :
    ¬ A3.Enabled C s := by
  cases s with
  | internal q a =>
    obtain ⟨h1, h2⟩ := hidle q
    simp only [Protocol.Enabled, Protocol.step, alg]
    split_ifs
    · simp
    · cases a <;> simp [internal, h1, h2]
  | recv src dst m =>
    simp [Protocol.Enabled, Protocol.step, hnet]
  | inv => simp [Step.owner] at hs
  | drop => simp [Step.owner] at hs
  | crash => simp [Step.owner] at hs
  | skip => simp [Step.owner] at hs

/-- There is a fair, `1`-resilient infinite execution of `A3` whose history contains a completed
write and a completed read. -/
theorem fair_exec_exists :
    ∃ e : A3.Exec, e.Fair ∧ e.Resilient 1 ∧ e.hist run.length = runHist := by
  obtain ⟨C, hrun, hnet, hcr, hidle⟩ := run_spec
  obtain ⟨e, hf, hh, -, hc⟩ := Protocol.exists_fair_exec_of_quiescent hrun
    (run_quiescent hnet hidle)
  refine ⟨e, hf, fun t => ?_, hh⟩
  have := hc t
  rw [hcr] at this
  rw [Finset.subset_empty.1 this]; simp

/-- The liveness theorem applies to it (`2 * 1 < 3`). -/
example : ∃ e : A3.Exec, e.Fair ∧ e.Resilient 1 ∧ e.OpsTerminate := by
  obtain ⟨e, hf, hr, -⟩ := fair_exec_exists
  exact ⟨e, hf, hr, live (by decide) e hf hr⟩

/-- The safety theorem applies to the history of `run`. -/
example : ∃ L, IsLinearization runHist L := by
  obtain ⟨C, hrun, -⟩ := run_spec
  exact linearizable (w := (0 : Fin 3)) (t := 1) (by decide) C runHist
    (by simpa using Protocol.runFrom_reach Protocol.Reach.init hrun)

end Podc.TwoBit.Sanity
