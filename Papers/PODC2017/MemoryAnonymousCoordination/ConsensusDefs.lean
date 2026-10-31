import Podc.Computability.Distributed.SharedMemory.Unnamed
import Cslib.Computability.Distributed.SharedMemory.Consensus

/-!
# Figure 2 of Taubenfeld, *Coordination Without Prior Agreement* (PODC 2017): the algorithm

A memory-anonymous symmetric obstruction-free consensus algorithm with `2n − 1` registers:

```
Code of process i with input in_i
Shared: p.i[1..2n-1]: registers (id, val), initially all fields 0
1 mypref := in_i
2 repeat
3   for j = 1 to 2n-1 do myview[j] := p.i[j] od
4   if ∃ value ≠ 0 which appears in at least n of the val fields of myview
5     then mypref := value fi
6   j := an arbitrary index k with myview[k] ≠ (i, mypref)
7   p.i[j] := (i, mypref)
8 until ∀ j : myview[j] = (i, mypref)
9 decide(mypref)
```

## Modelling

* `m` registers (the paper: `m = 2n − 1`), register values `Option (P × V)`; `none` is the
  initial value "`(0, 0)`", `some (q, v)` the record `(id, val) = (q, v)`. Inputs range over `V`,
  so no process can have the input `0` (with an input equal to the initial `val`, agreement fails).
* Granularity: each read of the collect (line 3) is one atomic step, the write (line 7) is one
  step, the decision (line 9) is the response of the consensus operation; lines 4–6 and the test
  of line 8 are local and folded into the continuation of the last read / of the write.
* Line 4 is `adopt n view mypref`: a value occurring in at least `n` val fields (unique when
  `m < 2n`), if any.
* Line 6 is a parameter `sel p mypref myview : Fin m`; the correctness proofs only assume that it
  returns an entry different from `(p, mypref)` whenever one exists. In the last iteration all
  entries equal `(p, mypref)` and no such index exists (contrary to "Clearly, such an arbitrary
  entry exists"); we still perform the write of line 7 to the register `sel …` (it rewrites
  `(p, mypref)` there, which is harmless).
* Process code is written in local register names; the memory-anonymous execution is
  `(alg n sel).unnamed π` for an arbitrary adversarial numbering `π`.
-/

namespace Podc.MemoryAnonymousCoordination.Consensus

open Cslib.SharedMemory

variable {P V : Type} {m : ℕ}

/-- Local state of a process. -/
inductive Loc (P V : Type) (m : ℕ) where
  /-- Not participating (before invocation or after deciding). -/
  | idle
  /-- In the collect of line 3: preference `pref`, about to read local register `k`; `view`
  holds the entries read so far (meaningful below `k`). -/
  | collect (pref : V) (k : Fin m) (view : Fin m → Option (P × V))
  /-- About to write `(i, pref)` to local register `j` (line 7); `last` is the result of the
  test of line 8 (on the view just collected). -/
  | write (pref : V) (j : Fin m) (last : Bool)
  /-- About to decide `v` (line 9). -/
  | done (v : V)

/-- The `val` field of a register value (`none` for the initial value `(0, 0)`). -/
def val (e : Option (P × V)) : Option V := e.map Prod.snd

@[simp] lemma val_none : val (none : Option (P × V)) = none := rfl
@[simp] lemma val_some (q : P) (v : V) : val (some (q, v)) = some v := rfl

variable [DecidableEq V]

/-- Number of entries whose `val` field is `v`. -/
def cnt (view : Fin m → Option (P × V)) (v : V) : ℕ :=
  (Finset.univ.filter fun j => val (view j) = some v).card

/-- Number of entries whose `val` field is not `w` (including initial entries). -/
def nonW (view : Fin m → Option (P × V)) (w : V) : ℕ :=
  (Finset.univ.filter fun j => val (view j) ≠ some w).card

open Classical in
/-- Lines 4–5: adopt a value occurring in at least `n` val fields of `view`, if any. -/
noncomputable def adopt (n : ℕ) (view : Fin m → Option (P × V)) (pref : V) : V :=
  if h : ∃ v, n ≤ cnt view v then h.choose else pref

/-- Start a new collect (line 3) with preference `x`. (With no registers, decide at once.) -/
def startCollect (x : V) : Loc P V m :=
  if h : 0 < m then .collect x ⟨0, h⟩ (fun _ => none) else .done x

variable [DecidableEq P]

/-- Lines 4–6 and the test of line 8, after a complete collect `view` with preference `x`. -/
noncomputable def finish (n : ℕ) (sel : P → V → (Fin m → Option (P × V)) → Fin m) (p : P) (x : V)
    (view : Fin m → Option (P × V)) : Loc P V m :=
  .write (adopt n view x) (sel p (adopt n view x) view)
    (decide (∀ j, view j = some (p, adopt n view x)))

/-- Continuation of the read of local register `k` returning `r`. -/
noncomputable def afterRead (n : ℕ) (sel : P → V → (Fin m → Option (P × V)) → Fin m) (p : P)
    (x : V) (k : Fin m) (view : Fin m → Option (P × V)) (r : Option (P × V)) : Loc P V m :=
  if h : k.val + 1 < m then .collect x ⟨k.val + 1, h⟩ (Function.update view k r)
  else finish n sel p x (Function.update view k r)

/-- Continuation of the write (line 8: decide, or repeat the loop). -/
def afterWrite (x : V) (last : Bool) : Loc P V m :=
  if last then .done x else startCollect x

variable [Inhabited V]

/-- **Figure 2** (in local register names), for `n` processes, `m` registers (the paper: `m = 2n − 1`)
and the choice `sel` of line 6. -/
noncomputable def alg (n : ℕ) (sel : P → V → (Fin m → Option (P × V)) → Fin m) :
    Impl (taskObj V V) (RegFamily (Fin m) (Option (P × V)) none) P (Loc P V m) where
  memInit _ := none
  locInit _ := .idle
  invoke _ _ x := startCollect x
  act p
    | .idle => .ret (default : V) .idle
    | .collect x k view => .access k .read (afterRead n sel p x k view)
    | .write x j b => .access j (.write (some (p, x))) (fun _ => afterWrite x b)
    | .done v => .ret v .idle

/-- Configurations of the algorithm. -/
abbrev Cfg (P V : Type) (m : ℕ) [Inhabited V] :=
  Config (taskObj V V) (RegFamily (Fin m) (Option (P × V)) none) P (Loc P V m)

/-- The hypothesis on line 6: if some entry differs from `(p, x)`, the selected one does. -/
def SelOK (sel : P → V → (Fin m → Option (P × V)) → Fin m) : Prop :=
  ∀ (p : P) (x : V) (view : Fin m → Option (P × V)), (∃ k, view k ≠ some (p, x)) → view (sel p x view) ≠ some (p, x)

end Podc.MemoryAnonymousCoordination.Consensus
