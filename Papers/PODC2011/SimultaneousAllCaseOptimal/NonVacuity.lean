import Papers.PODC2011.SimultaneousAllCaseOptimal.Flood
import Papers.PODC2011.SimultaneousAllCaseOptimal.Chain

/-!
# Non-vacuity of Theorem 6: an instance with `t = 1`

For `n ≥ 3` processes, `t = 1`, and consensus on a set with two distinct values, every hypothesis
of `theorem6` holds: `floodCC` has the ConCon properties, Lemma 5 holds (`lemma5_t1`), `2` is a
worst-case lower bound (`consensus_lb_two`) and `floodSet 2` solves consensus within `2` rounds.
Hence `Opt(floodSet 2, 2) = Delay(floodSet 2, 2) else ConCon(floodSet 2)` is all-case optimal.
-/

namespace Podc.SimultaneousAllCaseOptimal

open Cslib.SyncCrash Cslib.Byzantine.LockStep

variable {P I : Type} [Fintype P] [DecidableEq P] [DecidableEq I] [LinearOrder I]

/-- **Theorem 6, instance with all hypotheses discharged** (`n ≥ 3`, `t = 1`, consensus). -/
theorem theorem6_instance (hn : 3 ≤ Fintype.card P) {a b : I} (hab : a ≠ b) :
    AllCaseOptimal (Opt floodCC (floodSet 2) (consensus P I) 2) (consensus P I) 1 :=
  haveI : Nonempty P := Fintype.card_pos_iff.1 (by omega)
  theorem6 (by omega) (floodCC_isConCon _) (lemma5_t1 rfl hn)
    (consensus_lb_two hn le_rfl (by omega) hab)
    { toSolves := (floodSet_solvesSim (t := 1) (R := 2) (Or.inl (by norm_num))).toSolves
      within := fun _ _ p hp => ⟨2, le_rfl, _, floodSet_decides (Run.alive_of_not_faulty hp 2)⟩ }

end Podc.SimultaneousAllCaseOptimal
