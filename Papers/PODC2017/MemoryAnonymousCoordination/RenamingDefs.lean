import Podc.Computability.Distributed.SharedMemory.Unnamed
import Papers.PODC2017.MemoryAnonymousCoordination.ImpRenaming

/-!
# Figure 3 of Taubenfeld, *Coordination Without Prior Agreement* (PODC 2017): the algorithm

A memory-anonymous symmetric obstruction-free adaptive perfect renaming algorithm with `2n − 1`
registers:

```
Code of process i
Shared: p.i[1..2n-1]: registers (id, val, round, history), initially (0, 0, 0, ∅)
myround := 1; myhistory := ∅
1  repeat
2    mypref := i
3    repeat
4      for j = 1 to 2n-1 do myview[j] := p.i[j] od
5      if ∃ j ∃ v : (i, v) ∈ myview[j].history
6        then return(v) fi
7      mytemp := max_j myview[j].round
8      if mytemp > myround then
9        j := an arbitrary index k with myview[k].round = mytemp
10       mypref := myview[j].val
11       myhistory := myview[j].history
12       myround := myview[j].round fi
13     if ∃ v ≠ 0 appearing in at least n of the val fields of the entries of myview whose
         round field equals myround
14       then mypref := v fi
15     j := an arbitrary index k with myview[k] ≠ (i, mypref, myround, myhistory)
16     p.i[j] := (i, mypref, myround, myhistory)
17   until ∀ j : myview[j] = (i, mypref, myround, myhistory)
18   if mypref = i then return(myround) fi
19   myhistory := myhistory ∪ {(mypref, myround)}
20   myround := myround + 1
21 until myround = n
22 return(n)
```

## Modelling

* `m` registers (the paper: `m = 2n − 1`). A register value is `Option (P × St P)`: `none` is the
  initial value `(0, 0, 0, ∅)`, `some (q, s)` is the record `(id, val, round, history) =
  (q, s.val, s.rd, s.hist)`. Identifiers are arbitrary (`P` is any type with decidable equality);
  rounds are natural numbers (the initial round field `0` is never a real round).
* Local state: the triple `St` `(mypref, myround, myhistory)` and a program counter (`Loc`).
* Granularity: each read of the collect (line 4) is one atomic step, the write (line 16) is one
  step, the returns (lines 6, 18, 22) are the response of the renaming operation; the local
  computations of lines 5–15 are folded into the last read (`finish`), lines 17–21 and 2 into the
  write (`afterWrite`).
* Line 5: the name `v` is chosen by classical choice (it is unique in every execution).
* Lines 9 and 15 are parameters (`Sel`); the correctness proofs only assume `Sel.OK`: line 9
  picks an entry whose round is the maximum, line 15 an entry different from the own record
  whenever one exists. In the iteration that exits the loop all entries equal the own record and
  no such entry exists; the write of line 16 is still performed (it rewrites the own record).
* Process code is written in local register names; the memory-anonymous execution is
  `(alg n S).unnamed π` for an arbitrary adversarial numbering `π`.
-/

set_option linter.unusedSectionVars false

namespace Podc.MemoryAnonymousCoordination.Renaming

open Cslib.SharedMemory

/-- The local variables `(mypref, myround, myhistory)`, also the fields `(val, round, history)`
of a register. -/
structure St (P : Type) where
  /-- Preference (`mypref` / `val`). -/
  val : P
  /-- Round (`myround` / `round`). -/
  rd : ℕ
  /-- History: pairs (identifier, round) of the processes elected in earlier rounds. -/
  hist : Finset (P × ℕ)
deriving DecidableEq

variable {P : Type} {m : ℕ}

/-- Local state of a process. -/
inductive Loc (P : Type) (m : ℕ) where
  /-- Not participating (before invocation or after returning). -/
  | idle
  /-- In the collect of line 4 with local variables `s`, about to read local register `k`;
  `view` holds the entries read so far (meaningful below `k`). -/
  | collect (s : St P) (k : Fin m) (view : Fin m → Option (P × St P))
  /-- About to write the record `(i, s)` to local register `j` (line 16); `last` is the result
  of the test of line 17. -/
  | write (s : St P) (j : Fin m) (last : Bool)
  /-- About to return the new name `a`. -/
  | done (a : ℕ)

/-- The round field of a register value (`0` for the initial value). -/
def rdOf : Option (P × St P) → ℕ
  | none => 0
  | some (_, s) => s.rd

/-- The history field of a register value. -/
def histOf : Option (P × St P) → Finset (P × ℕ)
  | none => ∅
  | some (_, s) => s.hist

/-- The `(val, round)` fields of a register value (`none` for the initial value). -/
def rvOf (e : Option (P × St P)) : Option (P × ℕ) := e.map fun e => (e.2.val, e.2.rd)

@[simp] lemma rdOf_none : rdOf (none : Option (P × St P)) = 0 := rfl
@[simp] lemma rdOf_some (q : P) (s : St P) : rdOf (some (q, s)) = s.rd := rfl
@[simp] lemma histOf_none : histOf (none : Option (P × St P)) = ∅ := rfl
@[simp] lemma histOf_some (q : P) (s : St P) : histOf (some (q, s)) = s.hist := rfl
@[simp] lemma rvOf_none : rvOf (none : Option (P × St P)) = none := rfl
@[simp] lemma rvOf_some (q : P) (s : St P) : rvOf (some (q, s)) = some (s.val, s.rd) := rfl

/-- Line 7: the maximal round field of a view. -/
def maxRd (V : Fin m → Option (P × St P)) : ℕ := Finset.univ.sup fun j => rdOf (V j)

variable [DecidableEq P]

/-- Number of entries of `V` with round `t` and val `u`. -/
def cnt (V : Fin m → Option (P × St P)) (t : ℕ) (u : P) : ℕ :=
  (Finset.univ.filter fun j => rvOf (V j) = some (u, t)).card

/-- The choices of lines 9 and 15, made by a process `p` with local variables `s` after
collecting the view `V`. -/
structure Sel (P : Type) (m : ℕ) where
  /-- Line 9: the entry to copy when catching up. -/
  up : P → St P → (Fin m → Option (P × St P)) → Fin m
  /-- Line 15: the register to write. -/
  tgt : P → St P → (Fin m → Option (P × St P)) → Fin m

/-- The hypotheses on lines 9 and 15: line 9 picks an entry with the maximal round (when the
process is lagging behind), line 15 an entry different from the own record whenever one
exists. -/
structure Sel.OK (S : Sel P m) : Prop where
  up : ∀ p s V, s.rd < maxRd V → rdOf (V (S.up p s V)) = maxRd V
  tgt : ∀ p s (V : Fin m → Option (P × St P)), (∃ k, V k ≠ some (p, s)) →
    V (S.tgt p s V) ≠ some (p, s)

open Classical in
/-- Lines 5–6: the name `v` with `(i, v)` in some history of the view, if any. -/
noncomputable def retName (p : P) (V : Fin m → Option (P × St P)) : Option ℕ :=
  if h : ∃ v j, (p, v) ∈ histOf (V j) then some h.choose else none

/-- Lines 7–12: catching up. -/
def catchUp (S : Sel P m) (p : P) (s : St P) (V : Fin m → Option (P × St P)) : St P :=
  if s.rd < maxRd V then
    match V (S.up p s V) with
    | some (_, e) => e
    | none => s
  else s

open Classical in
/-- Lines 13–14: adopt a value occurring at least `n` times among the entries of round `s.rd`. -/
noncomputable def adopt (n : ℕ) (V : Fin m → Option (P × St P)) (s : St P) : St P :=
  if h : ∃ u, n ≤ cnt V s.rd u then { s with val := h.choose } else s

/-- Start a new collect (line 4). (With no registers, return at once.) -/
def startCollect (s : St P) : Loc P m :=
  if h : 0 < m then .collect s ⟨0, h⟩ (fun _ => none) else .done 0

/-- Lines 5–15 and the test of line 17, after a complete collect `V` with local variables `s`. -/
noncomputable def finish (n : ℕ) (S : Sel P m) (p : P) (s : St P)
    (V : Fin m → Option (P × St P)) : Loc P m :=
  match retName p V with
  | some v => .done v
  | none =>
    let s₂ := adopt n V (catchUp S p s V)
    .write s₂ (S.tgt p s₂ V) (decide (∀ j, V j = some (p, s₂)))

/-- Continuation of the read of local register `k` returning `r`. -/
noncomputable def afterRead (n : ℕ) (S : Sel P m) (p : P) (s : St P) (k : Fin m)
    (view : Fin m → Option (P × St P)) (r : Option (P × St P)) : Loc P m :=
  if h : k.val + 1 < m then .collect s ⟨k.val + 1, h⟩ (Function.update view k r)
  else finish n S p s (Function.update view k r)

/-- The local variables at the start of round `s.rd + 1` after losing round `s.rd` (lines 19,
20, 2). -/
def nextRound (p : P) (s : St P) : St P := ⟨p, s.rd + 1, insert (s.val, s.rd) s.hist⟩

/-- Continuation of the write (lines 17–22 and 2). -/
def afterWrite (n : ℕ) (p : P) (s : St P) (last : Bool) : Loc P m :=
  if last then
    if s.val = p then .done s.rd
    else if s.rd + 1 = n then .done n
    else startCollect (nextRound p s)
  else startCollect s

/-- **Figure 3** (in local register names), for `n` processes, `m` registers (the paper:
`m = 2n − 1`) and the choices `S` of lines 9 and 15. -/
noncomputable def alg (n : ℕ) (S : Sel P m) :
    Impl RenObj (RegFamily (Fin m) (Option (P × St P)) none) P (Loc P m) where
  memInit _ := none
  locInit _ := .idle
  invoke p _ _ := startCollect ⟨p, 1, ∅⟩
  act p
    | .idle => .ret (default : ℕ) .idle
    | .collect s k view => .access k .read (afterRead n S p s k view)
    | .write s j b => .access j (.write (some (p, s))) (fun _ => afterWrite n p s b)
    | .done a => .ret a .idle

/-- Configurations of the algorithm. -/
abbrev Cfg (P : Type) (m : ℕ) :=
  Config RenObj (RegFamily (Fin m) (Option (P × St P)) none) P (Loc P m)

/-- The local variables of a process inside the inner loop. -/
def stOf : Loc P m → Option (St P)
  | .collect s _ _ => some s
  | .write s _ _ => some s
  | _ => none

@[simp] lemma stOf_collect (s : St P) (k : Fin m) (view : Fin m → Option (P × St P)) :
    stOf (Loc.collect s k view) = some s := rfl
@[simp] lemma stOf_write (s : St P) (j : Fin m) (b : Bool) :
    stOf (Loc.write s j b) = some s := rfl
@[simp] lemma stOf_idle : stOf (Loc.idle : Loc P m) = none := rfl
@[simp] lemma stOf_done (a : ℕ) : stOf (Loc.done a : Loc P m) = none := rfl

end Podc.MemoryAnonymousCoordination.Renaming
