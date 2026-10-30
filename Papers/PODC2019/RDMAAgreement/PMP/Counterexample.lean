import Papers.PODC2019.RDMAAgreement.PMP.Exec

/-!
# Algorithm 7 as written violates agreement (Theorem D.2 is false)

Line 21 of Algorithm 7 writes `(propNr, ⊥, ⊥)` into the process's own slot, erasing the
`(accProp, value)` that the same process accepted there in an earlier attempt; since the main
loop is `repeat forever`, a process that has decided starts new attempts.

Execution with `n = 2` processes (`p1 = 0` with input `false`, `p2 = 1` with input `true`) and
`m = 1` memory (majority = 1), no crashes:

1. `p1` starts its first attempt (ballot 1, no phase 1) and invokes its line-35 write; the write
   is slow.
2. `p2` (ballot 2) acquires the permission, writes `(2,⊥,⊥)`, reads (no value), passes the
   barrier, writes `(2,2,true)` and **decides `true`**.
3. `p1`'s write takes effect without permission (`nak`): `p1` aborts.
4. `p2` starts a new attempt (ballot 4): `getPermission`, line-21 write `(4,⊥,⊥)` takes effect —
   the accepted value `true` is erased from memory.
5. `p1` starts a new attempt (ballot 5): `getPermission`, writes `(5,⊥,⊥)`, reads
   `{(5,⊥,⊥), (4,⊥,⊥)}`: no `minProp > 5`, no value, so `CurrentVal = false`; passes the
   barrier, its line-35 write succeeds and **`p1` decides `false`**.

All ballots are unique, increase per process and `p1`'s first ballot is the smallest.
-/

namespace Podc.RDMAAgreement.PMP

namespace Counterexample

/-- Inputs: `p1 = 0` proposes `false`, `p2 = 1` proposes `true`. -/
def inp (p : Fin 2) : Bool := decide (p = 1)

/-- The schedule described in the module docstring. -/
def schedule : List (Act (Fin 2) (Fin 1)) :=
  [ -- 1. p1's first attempt, slow line-35 write
    .startFirst 0, .issue 0 0,
    -- 2. p2 decides `true` with ballot 2
    .startNext 1 2, .invPerm 1 0, .eff 1 0, .dlv 1 0, .eff 1 0, .dlv 1 0, .eff 1 0, .dlv 1 0,
    .pass 1 0, .eff 1 0, .dlv 1 0,
    -- 3. p1's write fails, p1 aborts
    .eff 0 0, .dlv 0 0,
    -- 4. p2's new attempt erases its accepted value
    .startNext 1 4, .invPerm 1 0, .eff 1 0, .dlv 1 0, .eff 1 0,
    -- 5. p1 decides `false` with ballot 5
    .startNext 0 5, .invPerm 0 0, .eff 0 0, .dlv 0 0, .eff 0 0, .dlv 0 0, .eff 0 0, .dlv 0 0,
    .pass 0 0, .eff 0 0, .dlv 0 0 ]

/-- The final state's decisions, if the schedule is executable. -/
def finalDecs (var : Variant) : Option (List Bool) :=
  (run (0 : Fin 2) inp var schedule (initState 0 inp)).map State.decs

theorem finalDecs_literal : finalDecs .literal = some [false, true] := by decide +kernel

end Counterexample

open Counterexample in
/-- **Theorem D.2 (agreement) fails for Algorithm 7 as written**: with two processes and one
memory there is an execution of the literal algorithm (line 21 writes `(propNr, ⊥, ⊥)`) in which
`p2` decides `true` and later `p1` decides `false`. -/
theorem theorem_D2_false :
    ∃ s : State (Fin 2) (Fin 1) Bool, Reachable (0 : Fin 2) inp .literal s ∧
      true ∈ s.decs ∧ false ∈ s.decs := by
  have h := finalDecs_literal
  simp only [finalDecs, Option.map_eq_some_iff] at h
  obtain ⟨s, hs, hd⟩ := h
  exact ⟨s, run_sound _ _ _ _ _ _ hs, by simp [hd], by simp [hd]⟩

end Podc.RDMAAgreement.PMP
