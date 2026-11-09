/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Papers.PODC2019.ReconfigurableCommit.SendProbeAck
import Papers.PODC2019.ReconfigurableCommit.Raise

/-!
# Preservation of the invariant: delivering `PROBE` (lines 40–44)
-/

namespace Podc.ReconfigurableCommit

variable {T Pl S P : Type} [DecidableEq T] [DecidableEq Pl] [DecidableEq S] [DecidableEq P]
  [Fintype S]

variable {Pa : Params T Pl S P} {st st' : State T Pl S P}

theorem Inv.deliver_probe (hI : Inv Pa st) {src dst : P} {e : ℕ}
    (hm : Msg.probe e ∈ st.sent src dst)
    (h : handle Pa st src dst (.probe e) = some st') : Inv Pa st' := by
  simp only [handle] at h
  split_ifs at h with hle
  cases h
  rw [State.setLoc_eq_setRaise]
  refine (hI.setRaise hle).send_probeAck dst _ fun b m hb => ?_
  split_ifs at hb with hbq
  cases hb
  subst hbq
  simp [PAOK, hm]

end Podc.ReconfigurableCommit
