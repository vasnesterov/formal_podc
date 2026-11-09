import Papers.PODC2026.RandomizedWaitFreeLocks.Alg1Model

/-!
# Algorithm 1: non-vacuity — concrete executions

With one process and one descriptor: if the coin of line 6 is `true`, the descriptor is
promoted in the first `HelpAndPromote()`, its thunk is executed and `TryLock` returns `True`;
if the coin is `false`, the call returns `False`.  So both outcomes of the probabilistic
theorems are possible, and thunks are really executed (the safety theorems are not vacuous).
-/

namespace Podc.RandomizedWaitFreeLocks.Alg1

/-- The schedule: invoke, then 16 steps of the only process, with coin `w` at line 6. -/
def soloRun (w : Bool) : List (Act Unit Unit × Bool) :=
  (.invoke () (), false) :: (.sched (), w) :: List.replicate 16 (.sched (), false)

example : (run (init : Cfg Unit Unit) (step (fun _ => ())) (soloRun true)).2 =
    [.inv () (), .tau, .tau, .tau, .tau, .tau, .tau, .tau, .exS (), .exE (), .tau, .tau, .tau,
      .exS (), .exE (), .tau, .resp () () true, .tau] := by
  decide

example : (run (init : Cfg Unit Unit) (step (fun _ => ())) (soloRun false)).2 =
    [.inv () (), .tau, .tau, .tau, .tau, .tau, .tau, .tau, .tau, .tau, .tau, .tau, .tau,
      .tau, .resp () () false, .tau, .tau, .tau] := by
  decide

end Podc.RandomizedWaitFreeLocks.Alg1
