import Podc.SharedMemory.Objects.LLSC
import Cslib.Computability.Distributed.SharedMemory.Model
import Mathlib

/-!
# Algorithm 5: a universal implementation from R-LLSC objects

Section 6.1 of Attiya, Bender, Farach-Colton, Oshman, Schiller, *History-Independent Concurrent
Objects*, PODC 2024.

`n` processes `Fin n` implement an arbitrary abstract object `A` from atomic R-LLSC base objects
`head` and `announce[0..n-1]` (`Obj.head`, `Obj.ann j`).

* `head` holds a value in `A.State × Option (A.Resp × Fin n)`: `(q, none)` is the paper's
  `⟨q, ⊥⟩`, `(q, some (r, j))` is `⟨q, ⟨r, j⟩⟩`.
* `announce[j]` holds a value in `Option (A.Op ⊕ A.Resp)`: `none` is `⊥`, `some (inl o)` an
  announced operation, `some (inr r)` a response. (The paper assumes `R ∩ O = ∅` and `⊥ ∉ R ∪ O`;
  the sum/option type makes this automatic.)

Read-only operations are recognized with a decidable instance for `A.ReadOnly`.

## The program

Every program counter (`PC`) performs exactly one access to a base object (or returns), and the
local computation between accesses is folded into the continuation. Line numbers refer to the
paper's Algorithm 5:

| `PC`              | line(s) | access                                 |
|-------------------|---------|----------------------------------------|
| `ro o`            | 1–2     | `Load(head)`                           |
| `roRet r`         | 3       | return `r`                             |
| `ann o`           | 4       | `Store(announce[i], o)`                |
| `loop`            | 5       | `Load(announce[i])`, exit to 24 if `∈ R` |
| `llHead`          | 6L, 7   | `LL(head)`                             |
| `help`            | 8–9     | `Load(announce[priority])`             |
| `own`             | 10–12   | `Load(announce[i])`                    |
| `scApply j o`     | 13–15   | `SC(head, ⟨Δ(q,o), ⟨rsp, j⟩⟩)`          |
| `llAnn`           | 17–18L  | `LL(announce[j])`                      |
| `vl`              | 19      | `VL(head)`                             |
| `scAnn`           | 20      | `SC(announce[j], rsp)`                 |
| `scHead`          | 21      | `SC(head, ⟨q, ⊥⟩)`                      |
| `rlAnn`           | 22      | `RL(announce[j])`                      |
| `resp`            | 24      | `Load(announce[i])`                    |
| `llHead2 r`       | 25L     | `LL(head)`                             |
| `clear r`         | 26      | `SC(head, ⟨q, ⊥⟩)`                      |
| `rlHead r`        | 27      | `RL(head)`                             |
| `storeBot r`      | 28      | `Store(announce[i], ⊥)`                |
| `retSC r`         | 29      | return `r`                             |

**The blue right-hand sides of `∥` (lines 6R, 18R, 25R) are omitted.** They only matter when an
`LL` on the left-hand side can block, which happens with the lock-free R-LLSC implementation of
Algorithm 6. Here the base objects are atomic, so each `LL` is a single step, and the paper's
`∥` allows any finite number of steps on either side: executing the left side to completion
(zero steps on the right) is one of the allowed schedules of the paper's program.

Line 12 (`apply-op ← op`) uses the value just loaded from `announce[i]` in line 11 (which is
`op` itself whenever it is an operation, see `Universal.Inv`): this avoids storing `op` in the
local state.

Lines 20–21 are executed only when the `VL` of line 19 succeeds; line 22 is executed in both
cases (when the `VL` succeeds and `a = ⊥`, which never happens, it is harmless).
-/

namespace Cslib.SharedMemory

namespace Universal

variable (A : ObjSpec) (n : ℕ)

/-- The base objects: `head` and `announce[j]`. -/
inductive Obj (n : ℕ) where
  | head
  | ann (j : Fin n)
  deriving DecidableEq

/-- Values of `head`. -/
abbrev HeadVal := A.State × Option (A.Resp × Fin n)

/-- Values of `announce[j]` (`none` is `⊥`). -/
abbrev AnnVal := Option (A.Op ⊕ A.Resp)

/-- The base objects' specifications. -/
@[reducible] def B : Obj n → ObjSpec
  | .head => rllsc (Fin n) (HeadVal A n) (A.init, none)
  | .ann _ => rllsc (Fin n) (AnnVal A) none

/-- Program counters (see the table in the module docstring). -/
inductive PC where
  | idle
  | ro (o : A.Op)
  | roRet (r : A.Resp)
  | ann (o : A.Op)
  | loop
  | llHead
  | help
  | own
  | scApply (j : Fin n) (o : A.Op)
  | llAnn
  | vl
  | scAnn
  | scHead
  | rlAnn
  | resp
  | llHead2 (r : A.Resp)
  | clear (r : A.Resp)
  | rlHead (r : A.Resp)
  | storeBot (r : A.Resp)
  | retSC (r : A.Resp)
  /-- Line 18R.2: `RL(announce[j])`, then go to line 24. Unreachable in `alg5` (which omits the
  right-hand sides of `∥`); used by the flattened implementation (`UniversalFlat`). -/
  | rl18 (j : Fin n)

/-- Local state of a process: program counter, `priority`, the value `⟨q, r⟩` returned by the
last `LL(head)`, and the value `a` returned by the last `LL(announce[aj])`. -/
structure Loc where
  pc : PC A n
  prio : Fin n
  hd : HeadVal A n
  a : AnnVal A
  aj : Fin n

variable {A n}

/-- `priority + 1 mod n`. -/
def nextP (i : Fin n) : Fin n := ⟨(i.val + 1) % n, Nat.mod_lt _ (by have := i.isLt; omega)⟩

/-- `a ∈ O`. -/
def isOp : AnnVal A → Bool
  | some (.inl _) => true
  | _ => false

/-- `r = ⟨_, p⟩` (line 26). -/
def ownerIs (p : Fin n) : Option (A.Resp × Fin n) → Bool
  | some (_, j) => decide (j = p)
  | none => false

/-- Access `head`. -/
abbrev accH (o : RLLSCOp (Fin n) (HeadVal A n)) (k : HeadVal A n ⊕ Bool → Loc A n) :
    Action A (B A n) (Loc A n) := .access .head o k

/-- Access `announce[j]`. -/
abbrev accA (j : Fin n) (o : RLLSCOp (Fin n) (AnnVal A)) (k : AnnVal A ⊕ Bool → Loc A n) :
    Action A (B A n) (Loc A n) := .access (.ann j) o k

/-- The code of process `p` (Algorithm 5, left-hand sides of `∥`). -/
def act (p : Fin n) (l : Loc A n) : Action A (B A n) (Loc A n) :=
  match l.pc with
  | .idle => accH .load fun _ => l
  | .ro o => accH .load fun
      | .inl v => { l with pc := .roRet (A.δ v.1 o).2 }
      | .inr _ => l
  | .roRet r => .ret r { l with pc := .idle }
  | .ann o => accA p (.store (some (.inl o))) fun _ => { l with pc := .loop }
  | .loop => accA p .load fun
      | .inl (some (.inr _)) => { l with pc := .resp }
      | _ => { l with pc := .llHead }
  | .llHead => accH (.ll p) fun
      | .inl v => { l with hd := v, pc := if v.2.isNone then .help else .llAnn }
      | .inr _ => l
  | .help => accA l.prio .load fun
      | .inl (some (.inl o)) => { l with pc := .scApply l.prio o }
      | _ => { l with pc := .own }
  | .own => accA p .load fun
      | .inl (some (.inl o)) => { l with pc := .scApply p o }
      | _ => { l with pc := .loop }
  | .scApply j o => accH (.sc p ((A.δ l.hd.1 o).1, some ((A.δ l.hd.1 o).2, j))) fun
      | .inr true => { l with pc := .loop, prio := nextP l.prio }
      | _ => { l with pc := .loop }
  | .llAnn => match l.hd.2 with
      | some (_, j) => accA j (.ll p) fun
          | .inl v => { l with a := v, aj := j, pc := .vl }
          | .inr _ => l
      | none => accH .load fun _ => { l with pc := .loop }
  | .vl => accH (.vl p) fun
      | .inr true => { l with pc := if isOp l.a then .scAnn else .scHead }
      | _ => { l with pc := if l.a.isNone then .rlAnn else .loop }
  | .scAnn => match l.hd.2 with
      | some (rsp, _) => accA l.aj (.sc p (some (.inr rsp))) fun _ => { l with pc := .scHead }
      | none => accH .load fun _ => { l with pc := .scHead }
  | .scHead => accH (.sc p (l.hd.1, none)) fun _ =>
      { l with pc := if l.a.isNone then .rlAnn else .loop }
  | .rlAnn => accA l.aj (.rl p) fun _ => { l with pc := .loop }
  | .resp => accA p .load fun
      | .inl (some (.inr x)) => { l with pc := .llHead2 x }
      | _ => l
  | .llHead2 x => accH (.ll p) fun
      | .inl v =>
        { l with hd := v, pc := if ownerIs p v.2 then .clear x else .rlHead x }
      | .inr _ => l
  | .clear x => accH (.sc p (l.hd.1, none)) fun _ => { l with pc := .storeBot x }
  | .rlHead x => accH (.rl p) fun _ => { l with pc := .storeBot x }
  | .storeBot x => accA p (.store none) fun _ => { l with pc := .retSC x }
  | .retSC x => .ret x { l with pc := .idle }
  | .rl18 j => accA j (.rl p) fun _ => { l with pc := .resp }

variable (A n) in
/-- **Algorithm 5** with atomic R-LLSC base objects. -/
def alg5 [DecidablePred A.ReadOnly] : Impl A (B A n) (Fin n) (Loc A n) where
  memInit
    | .head => ((A.init, none), ∅)
    | .ann _ => (none, ∅)
  locInit p := ⟨.idle, p, (A.init, none), none, p⟩
  invoke _ l o := { l with pc := if A.ReadOnly o then .ro o else .ann o }
  act := act

end Universal

end Cslib.SharedMemory
