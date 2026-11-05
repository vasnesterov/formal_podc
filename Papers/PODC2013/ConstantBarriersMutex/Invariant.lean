import Papers.PODC2013.ConstantBarriersMutex.InvStep

/-!
# The invariant holds in every reachable configuration
-/

namespace Podc.ConstantBarriersMutex

variable {h : ℕ}

theorem inv_reachable {s : Cfg h} (hs : Reachable s) : Inv s := by
  induction hs with
  | init => exact inv_init
  | next e _ ih => exact inv_next ih e

theorem Run.reachable (r : Run h) (t : ℕ) : Reachable (r.s t) := by
  induction t with
  | zero => rw [r.init]; exact Reachable.init
  | succ t ih => rw [r.step t]; exact Reachable.next _ ih

theorem Run.inv (r : Run h) (t : ℕ) : Inv (r.s t) := inv_reachable (r.reachable t)

end Podc.ConstantBarriersMutex
