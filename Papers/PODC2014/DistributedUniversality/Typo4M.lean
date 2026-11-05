import Papers.PODC2014.DistributedUniversality.Model

/-!
# Line 4M as written in Section 4.3 breaks safety

Section 4.3 of [Raynal–Stainer–Taubenfeld, PODC 2014] describes the contention-aware wait-free
`(k, ℓ)`-universal construction as Figure 2 with modified lines 2M–4M, and states line 4M as
"`AC[2rᵢ][m].propose(operᵢ[m])` is invoked only for the remaining objects", whereas Figure 2's line 4M
proposes `ac_opᵢ[m]` (the value obtained at line N1).  The mode flag `typo4M := true` models the
literal text.

We exhibit an execution (`n = 2`, `k = 2`, `ℓ = 1`, no helping; the adopt-commit and SC responses
satisfy the specifications, even the strong reading of the no-conflict property) in which two
processes return, as the *first* operation on object `0`, two different operations: process 0
returns `(0,0)` computed from the local history `[(0,0)]`, process 1 returns `(1,0)` computed from
`[(1,0)]`.  The two local histories are not prefix-comparable, so the object is not linearizable.

Schedule: process 0 commits `(0,0)` at line N1 on both objects (it skips the SC object); process 1
gets `adopt (0,0)` on object 0 at line N1 (it invoked `AC[1][0]` concurrently with process 0) and
`commit (0,0)` on object 1, so it goes to `SC[1]`, which decides object 1.  At line 4M it proposes
its own `oper[0] = (1,0)` (instead of `ac_op[0] = (0,0)`) to the fresh `AC[2][0]`, alone, and
commits it.  With Figure 2's line 4M (`typo4M := false`) the same schedule is not executable
(`sched_not_executable_fig2`).
-/

namespace Podc.DistributedUniversality.Typo4M

open Podc.DistributedUniversality

/-- Section 4.3 with the literal line 4M, `ℓ = 1`, no helping, strong reading of adopt-commit. -/
def M : Mode := { ℓ := 1, ca := true, help := false, strongAC := true, typo4M := true }

/-- The `s`-th operation of process `i`. -/
abbrev o (i : Fin 2) (s : ℕ) : Op 2 := (i, s)

/-- The decision of `SC[1]` for process 1: object `1`, operation `(0,0)`. -/
def d : Fin 2 → Option (Op 2) := ![none, some (o 0 0)]

/-- `c` local steps of process `i`. -/
def g (i : Fin 2) (c : ℕ) : List (Act 2 2) := List.replicate c (.go i)

/-- The schedule (28 steps). -/
def sched : List (Act 2 2) :=
  -- both processes start; 0 and 1 invoke `AC[1][0]`; 0 commits `(0,0)` on both objects at N1
  [.go 0, .go 0, .go 1, .go 1, .ac 0 true (o 0 0), .go 0, .ac 0 true (o 0 0)] ++
  -- process 0: lines 5–28 (collect, local computation, append `(0,0)` to both histories)
  g 0 5 ++
  -- process 1: adopt `(0,0)` on object 0 and commit `(0,0)` on object 1 at N1; `SC[1]` decides
  -- object 1; line 3M on object 1; line 4M on object 0 with its own `oper[0] = (1,0)`
  [.ac 1 false (o 0 0), .go 1, .ac 1 true (o 0 0), .go 1, .sc 1 d, .go 1, .ac 1 true (o 0 0),
   .go 1, .ac 1 true (o 1 0)] ++
  -- process 1: lines 5–31 (it returns `(1,0)`); then process 0 executes line 30–31
  g 1 6 ++ [.go 0]

/-- **Line 4M of Section 4.3, taken literally, breaks linearizability.** In the above execution of
the construction of Section 4.3 with line 4M proposing `operᵢ[m]`, processes 0 and 1 both return
their own operation on object `0`, computed from the local histories `[(0,0)]` and `[(1,0)]`,
which are not prefix-comparable. -/
theorem section_4_3_line_4M_unsafe :
    ∃ s : St 2 2, run M init sched = some s ∧
      s.retH 0 0 0 = some [(0, 0)] ∧ s.retH 1 0 0 = some [(1, 0)] ∧
      (s.retAt 0 0 0).isSome ∧ (s.retAt 1 0 0).isSome ∧
      ¬ ([((0 : Fin 2), 0)] <+: [((1 : Fin 2), 0)]) ∧ ¬ ([((1 : Fin 2), 0)] <+: [((0 : Fin 2), 0)]) := by
  refine ⟨(run M init sched).get (by decide), by simp, by decide, by decide, by decide, by decide,
    by decide, by decide⟩

/-- The schedule is also valid for the weak (standard) reading of the adopt-commit
no-conflict property. -/
theorem sched_executable_weakAC : (run { M with strongAC := false } init sched).isSome := by
  decide

/-- With Figure 2's line 4M (proposing `ac_opᵢ[m]`), the schedule is not executable: process 1
proposes `(0,0)` to `AC[2][0]` and cannot obtain `(1,0)`. -/
theorem sched_not_executable_fig2 : run { M with typo4M := false } init sched = none := by
  decide

end Podc.DistributedUniversality.Typo4M
