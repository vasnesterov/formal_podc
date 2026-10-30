import Papers.PODC2020.RecoverableMutexRMR.InvQuiet
import Papers.PODC2020.RecoverableMutexRMR.InvWrite
import Papers.PODC2020.RecoverableMutexRMR.InvGhost
import Papers.PODC2020.RecoverableMutexRMR.InvToken

/-!
# The invariant holds in every reachable configuration
-/

set_option linter.unusedSectionVars false

namespace Podc.RecoverableMutexRMR

variable {P : Type} [DecidableEq P] [Fintype P]

theorem inv_step {s : Cfg P} {g : Ghost P} (hI : Inv s g) (p : P) :
    Inv (s.step p) (g.next s (.step p)) := by
  cases hpc : s.pc p with
  | rem => exact inv_step_rem hI hpc
  | l3 => exact inv_step_l3 hI hpc
  | l4 => exact inv_step_l4 hI hpc
  | l5 c => exact inv_step_l5 hI hpc
  | w23 => exact inv_step_w23 hI hpc
  | w24 w => exact inv_step_w24 hI hpc
  | w25 w => exact inv_step_w25 hI hpc
  | w26 => exact inv_step_w26 hI hpc
  | w28 w => exact inv_step_w28 hI hpc
  | w31 w => exact inv_step_w31 hI hpc
  | cs => exact inv_step_cs hI hpc
  | x9 => exact inv_step_x9 hI hpc
  | x10 => exact inv_step_x10 hI hpc
  | x12 => exact inv_step_x12 hI hpc
  | r15 => exact inv_step_r15 hI hpc
  | r16 => exact inv_step_r16 hI hpc
  | r18 => exact inv_step_r18 hI hpc
  | m34 r => exact inv_step_m34 hI hpc
  | m35 r ℓ => exact inv_step_m35 hI hpc
  | m36 r ℓ d => exact inv_step_m36 hI hpc
  | m38 r ℓ c d => exact inv_step_m38 hI hpc
  | m40 r ℓ q => exact inv_step_m40 hI hpc
  | m41 r ℓ q => exact inv_step_m41 hI hpc
  | m42 r ℓ => exact inv_step_m42 hI hpc
  | m46 r ℓ => exact inv_step_m46 hI hpc
  | m47 r ℓ => exact inv_step_m47 hI hpc
  | m48 r ℓ => exact inv_step_m48 hI hpc

theorem inv_next {s : Cfg P} {g : Ghost P} (hI : Inv s g) (ev : Ev P) :
    Inv (s.next ev) (g.next s ev) := by
  cases ev with
  | step p => exact inv_step hI p
  | crash p => exact inv_crash hI p

/-- The invariant holds along every execution. -/
theorem inv_exec (e : ℕ → Ev P) (t : ℕ) : Inv (exec e t) (ghost e t) := by
  induction t with
  | zero => exact inv_init
  | succ t ih => exact inv_next ih (e t)

end Podc.RecoverableMutexRMR
