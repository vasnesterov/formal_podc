import Papers.PODC2025.StrangerFreeTasks.BoundedLA

/-!
# Algorithm 1 of the paper: `k`-bounded lattice agreement with `k + 1` registers

```
1: shared A[r] ← ⟨0, 0, ∅⟩ for all r ∈ 1..k+1
2: local output ← ∅
3: local seen ← {p}
4: local seq ← 0
5: local i ← 1
6: local snapshot ← true
7: local collect[r] ← ⊥ for all r ∈ 1..k+1
8: while output = ∅ do
9:    A[i] ← ⟨p, seq, seen⟩
10:   i ← if (i ≤ k) then i + 1 else 1
11:   seq ← seq + 1
12:   for j = 1 to k+1 do
13:     collect[j] ← A[j]
14:     seen ← seen ∪ collect[j][3]
15:   end for
16:   snapshot ← true
17:   for j = 1 to k+1 do
18:     if A[j] ≠ collect[j] then
19:       snapshot ← false
20:     end if
21:     seen ← seen ∪ collect[j][3]
22:   end for
23:   if |seen| > k then
24:     output ← seen
25:   else if snapshot ∧ ∀ r ∈ 1..k+1 : seen = collect[r][3] then
26:     output ← seen
27:   end if
28: end while
```

Modelling choices (see `differencies.md`):
* registers are indexed by `Fin (k + 1)` (`0..k` instead of `1..k+1`); the initial value
  `⟨0, 0, ∅⟩` is `Triple.init` (writer `none`);
* every shared-memory access (line 9, line 13, line 18) is one atomic step; local computation is
  folded into the step that precedes it; the decision of lines 23–27 is taken in the step of the
  last read of the second collect; `⊥` initial values of `collect` are modelled by `Triple.init`
  (they are overwritten before being used);
* line 21 is taken literally (`seen ∪ collect[j][3]`, a no-op after line 14);
* a process that has output and is invoked again returns the same output immediately (one-shot
  tasks only constrain one-shot executions; this makes the algorithm a total `Impl`).
-/

namespace Cslib.SharedMemory.StrangerFree

open Cslib.SharedMemory

variable {P : Type} [DecidableEq P]

/-- Contents of a register: writer (`none` for the initial value), sequence number, seen set. -/
structure Triple (P : Type) where
  /-- The writer (`none` = the initial value `⟨0, 0, ∅⟩`). -/
  id : Option P
  /-- Sequence number of the write. -/
  seq : ℕ
  /-- The writer's `seen` set. -/
  seen : Finset P
  deriving DecidableEq

/-- The initial register value `⟨0, 0, ∅⟩`. -/
def Triple.init : Triple P := ⟨none, 0, ∅⟩

/-- Phases of Algorithm 1. -/
inductive Phase where
  /-- Not invoked yet. -/
  | idle
  /-- About to write (line 9). -/
  | wr
  /-- First collect (lines 12–15), about to read `A[j]`. -/
  | col1
  /-- Second collect (lines 17–22), about to read `A[j]`. -/
  | col2
  /-- Output produced. -/
  | done
  deriving DecidableEq

/-- Local state of a process running Algorithm 1. -/
structure Loc (P : Type) (k : ℕ) where
  phase : Phase
  /-- Loop index `j` of the current collect. -/
  j : Fin (k + 1)
  /-- Next register to write. -/
  i : Fin (k + 1)
  seq : ℕ
  seen : Finset P
  collect : Fin (k + 1) → Triple P
  snap : Bool
  out : Finset P

/-- The base objects: `k + 1` registers holding triples. -/
abbrev Regs (P : Type) (k : ℕ) : Fin (k + 1) → ObjSpec := fun _ => register (Triple P) Triple.init

variable (k : ℕ)

/-- The decision of lines 23–27 after the second collect, with the final `seen` and `snapshot`. -/
def decision (l : Loc P k) : Loc P k :=
  if k < l.seen.card then { l with phase := .done, out := l.seen }
  else if l.snap = true ∧ ∀ r, l.seen = (l.collect r).seen then { l with phase := .done, out := l.seen }
  else { l with phase := .wr }

/-- Step of the first collect after reading value `v` from `A[l.j]` (lines 13–14). -/
def afterCol1 (l : Loc P k) (v : Triple P) : Loc P k :=
  let l' := { l with collect := Function.update l.collect l.j v, seen := l.seen ∪ v.seen }
  if l.j.val = k then { l' with phase := .col2, j := 0, snap := true }
  else { l' with j := l.j + 1 }

/-- Step of the second collect after reading value `v` from `A[l.j]` (lines 18–21), followed by
the decision (lines 23–27) after the last read. -/
def afterCol2 (l : Loc P k) (v : Triple P) : Loc P k :=
  let l' := { l with snap := l.snap && decide (v = l.collect l.j),
                     seen := l.seen ∪ (l.collect l.j).seen }
  if l.j.val = k then decision k l' else { l' with j := l.j + 1 }

/-- The initial local state of `p` (lines 2–7). -/
def locInit (p : P) : Loc P k :=
  ⟨.idle, 0, 0, 0, {p}, fun _ => Triple.init, true, ∅⟩

/-- Algorithm 1 as an implementation of the `k`-bounded lattice-agreement task from `k + 1`
read/write registers. -/
noncomputable def alg1 : Impl (laObj P) (Regs P k) P (Loc P k) where
  memInit _ := Triple.init
  locInit := locInit k
  invoke _ l _ := if l.phase = .idle then { l with phase := .wr } else l
  act p l :=
    match l.phase with
    | .wr => .access l.i (.write ⟨some p, l.seq, l.seen⟩)
        (fun _ => { l with phase := .col1, j := 0, i := l.i + 1, seq := l.seq + 1 })
    | .col1 => .access l.j .read (fun v => afterCol1 k l v)
    | .col2 => .access l.j .read (fun v => afterCol2 k l v)
    | .done => .ret l.out l
    | .idle => .ret (∅ : Finset P) l

end Cslib.SharedMemory.StrangerFree
