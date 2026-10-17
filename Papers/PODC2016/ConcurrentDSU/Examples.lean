import Papers.PODC2016.ConcurrentDSU.Main

/-!
# Concrete executions

## Non-vacuity: a sequential execution

`seqDemo`: process `0` runs `Unite(0, 1)` (one-try splitting) and then `SameSet(1, 0)`, which
returns `true`; the execution is valid (`seqDemo_valid`), i.e. the implementation really returns
these responses. (`seqDemo_false`: before the `Unite`, `SameSet(1, 0)` returns `false`.)

## A `Find` can issue `Cas(u.parent, u, w)` (proof of Lemma 3.1)

The proof of Lemma 3.1 says that "each `Cas(u.parent, v, w)` done in a `Find` is such that
`u`, `v` and `w` are distinct". This is not true: with splitting, `Find(u)` may read
`v ← u.parent = u` while `u` is still a root, then another process links `u`, and the `Find`
reads `w ← v.parent ≠ v` and executes `Cas(u.parent, u, w)` with `u = v`. Such a `Cas` always
fails (`u` is no longer a root), so the lemma is not affected (our proof of `fRes_spec` handles
this case).

Execution (one-try splitting, two elements `0 < 1`, two processes): process `0` starts
`SameSet(0, 0)` and reads `0.parent = 0`; process `1` runs `Unite(0, 1)` up to its successful
link `0.parent ← 1`; process `0` reads `0.parent = 1` and is now about to execute
`Cas(0.parent, 0, 1)`.
-/

namespace Podc.ConcurrentDSU

open Cslib.SharedMemory

/-- The execution described above. -/
def casSameNodeExec : List (Label (Fin 2) (dsu (Fin 2))) :=
  [.inv 0 (.sameSet 0 0), .tau 0,
   .inv 1 (.unite 0 1), .tau 1, .tau 1, .tau 1, .tau 1, .tau 1,
   .tau 0]

theorem cas_same_node :
    ((dsuImpl FindKind.oneTry (fun a : Fin 2 => a.val) (Fin 2)).run casSameNodeExec).map
      (fun C => C.loc 0) = some (.fu false (.cas 0 0 1 0) 0) := by
  simp [casSameNodeExec, Impl.run, Impl.runFrom, Impl.step, Impl.initCfg, dsuImpl, act, liftF,
    FS.next, invoke, FS.start, contU, contV, val, Function.update, FindKind.tries]

/-- `Unite(0, 1)` followed by `SameSet(1, 0)`, sequentially by process `0`. -/
def seqDemo : List (Label (Fin 1) (dsu (Fin 2))) :=
  [.inv 0 (.unite 0 1), .tau 0, .tau 0, .tau 0, .tau 0, .tau 0, .ret 0 true,
   .inv 0 (.sameSet 1 0), .tau 0, .tau 0, .tau 0, .tau 0, .ret 0 true]

theorem seqDemo_valid :
    (dsuImpl FindKind.oneTry (fun a : Fin 2 => a.val) (Fin 1)).Valid seqDemo := by
  refine Option.isSome_iff_exists.1 ?_
  simp [seqDemo, Impl.run, Impl.runFrom, Impl.step, Impl.initCfg, dsuImpl, act, liftF,
    FS.next, invoke, FS.start, contU, contV, val, Function.update, FindKind.tries]

/-- Without the `Unite`, `SameSet(1, 0)` returns `false`. -/
theorem seqDemo_false :
    (dsuImpl FindKind.oneTry (fun a : Fin 2 => a.val) (Fin 1)).Valid
      [.inv 0 (.sameSet 1 0), .tau 0, .tau 0, .tau 0, .tau 0, .tau 0, .ret 0 false] := by
  refine Option.isSome_iff_exists.1 ?_
  simp [Impl.run, Impl.runFrom, Impl.step, Impl.initCfg, dsuImpl, act, liftF,
    FS.next, invoke, FS.start, contU, contV, val, Function.update, FindKind.tries]

end Podc.ConcurrentDSU
