import Mathlib
import Cslib.Computability.Distributed.SharedMemory.Model
import Cslib.Computability.Distributed.SharedMemory.LinPoints
import Cslib.Computability.Distributed.SharedMemory.Objects.FetchAdd
import Podc.Computability.Distributed.SharedMemory.Objects.GCAS

/-!
# Hadzilacos–Thiessen–Toueg, *Generalized Compare-and-Swap and Space-Efficient Universal
Constructions for the Infinite-Arrival Model* (PODC 2026): Algorithm 1

Algorithm 1 is a universal construction: given the sequential specification `T` (an `ObjSpec`,
i.e. a deterministic `applyT`), it implements an object of type `T` for an arbitrary (possibly
infinite) set of processes `P` from

* `C` — a fetch&increment object, initially `1` (timestamps);
* `A` — a GCAS object holding a triple `(time, operation, pointer)`, initially
  `(0, Noop, ptrNoop)`, compared lexicographically (footnote 2 of the paper);
* `S` — a CAS object holding `(time, state, response, pointer)`, initially
  `(0, s₀, ⊥, ptrNoop)`;
* dynamically allocated *cells*, one CAS object `(time, response)` each, obtained from a memory
  manager (`MM`).

## Modelling choices

* Pointers are `Ptr = WithBot ℕ`: `⊥` is `ptrNoop` (the dummy cell, initially `(0, ⊥)`), `↑n` is
  the `n`-th cell handed out by the memory manager. The memory manager is a base object whose
  `AllocateCell` returns the cells `0, 1, 2, …` in order (`mmObj`): since Algorithm 1 never frees
  cells, any allocation order is of this form up to renaming of cells.
* The initial contents of the cells are arbitrary (`cellInit`).
* `Noop` is `⊥ : WithBot T.Op`; responses stored in cells and in `S` are `RVal T.Resp`
  (`null` = `Null`, `bot` = `⊥`, `val r`). Comparing triples in `A` lexicographically needs a
  linear order on operations (`[LinearOrder T.Op]`, e.g. their bit-string encodings).
* Each line of the pseudocode that accesses a shared object is one step; local computations are
  merged into these steps. Line 2 is a step only when the process allocates; line 16 is the
  response step (it returns the response read on line 5).
-/

namespace Podc.GeneralizedCAS

open Cslib.SharedMemory

/-- Pointers to cells: `⊥` is `ptrNoop`, `↑n` the `n`-th allocated cell. -/
abbrev Ptr := WithBot ℕ

/-- Responses stored in shared objects: `Null`, `⊥` or a response of the type. -/
inductive RVal (R : Type) where
  | null
  | bot
  | val (r : R)
  deriving DecidableEq

/-- The contents of `A`: `(time, operation, pointer)`. -/
@[ext] structure AVal (Op : Type) where
  time : ℕ
  op : WithBot Op
  ptr : Ptr
  deriving DecidableEq

/-- Lexicographic key of an `AVal`. -/
def AVal.key {Op : Type} (a : AVal Op) : ℕ ×ₗ (WithBot Op ×ₗ Ptr) := toLex (a.time, toLex (a.op, a.ptr))

lemma AVal.key_injective {Op : Type} : Function.Injective (AVal.key (Op := Op)) := by
  intro a b h
  simp only [AVal.key, toLex_inj, Prod.mk.injEq] at h
  ext <;> simp [h]

instance {Op : Type} [LinearOrder Op] : LinearOrder (AVal Op) :=
  LinearOrder.lift' AVal.key AVal.key_injective

lemma AVal.lt_iff {Op : Type} [LinearOrder Op] (a b : AVal Op) : a < b ↔ a.key < b.key := Iff.rfl

lemma AVal.time_le_of_lt {Op : Type} [LinearOrder Op] {a b : AVal Op} (h : a < b) :
    a.time ≤ b.time := by
  rw [AVal.lt_iff, AVal.key, AVal.key, Prod.Lex.toLex_lt_toLex] at h
  rcases h with h | ⟨h, -⟩
  · exact h.le
  · exact h.le

lemma AVal.time_le_of_not_lt {Op : Type} [LinearOrder Op] {a b : AVal Op} (h : ¬ b < a) :
    a.time ≤ b.time := by
  rcases lt_or_eq_of_le (not_lt.1 h) with h | h
  · exact AVal.time_le_of_lt h
  · rw [h]

lemma AVal.lt_of_time_lt {Op : Type} [LinearOrder Op] {a b : AVal Op} (h : a.time < b.time) :
    a < b := by
  rw [AVal.lt_iff, AVal.key, AVal.key, Prod.Lex.toLex_lt_toLex]
  exact Or.inl h

/-- The contents of `S`: `(time, state, response, pointer)`. -/
@[ext] structure SVal (St R : Type) where
  time : ℕ
  state : St
  resp : RVal R
  ptr : Ptr

/-- The contents of a cell: `(time, response)`. -/
@[ext] structure CellVal (R : Type) where
  time : ℕ
  resp : RVal R
  deriving DecidableEq

/-- The memory manager: `AllocateCell` returns the cells `0, 1, 2, …` in order; its state is the
number of cells allocated so far. -/
abbrev mmObj : ObjSpec where
  State := ℕ
  Op := Unit
  Resp := ℕ
  init := 0
  δ n _ := (n + 1, n)

/-- The base objects of Algorithm 1. -/
inductive Obj where
  | C
  | A
  | S
  | MM
  | cell (x : Ptr)
  deriving DecidableEq

variable (T : ObjSpec) [LinearOrder T.Op]

open Classical in
/-- The sequential specifications of the base objects. -/
noncomputable abbrev base : Obj → ObjSpec
  | .C => rfaiObj
  | .A => gcasObject (AVal T.Op) ⟨0, ⊥, ⊥⟩
  | .S => casObject (SVal T.State T.Resp) ⟨0, T.init, .bot, ⊥⟩
  | .MM => mmObj
  | .cell _ => casObject (CellVal T.Resp) ⟨0, .bot⟩

/-- Program counter: the next line to execute (`l16 r`: return `r`). -/
inductive PC (R : Type) where
  | l2 | l3 | l4 | l5 | l6 | l7 | l8 | l9 | l10 | l13 | l15
  | l16 (r : R)

/-- Local state of a process. `ptr` (persistent, initially `Null = none`) points to the
process's cell; `t` is the timestamp of the current operation; `snap = (t*, s*, r*, ptr*)` is the
value read from `S` on line 6; `ann = (t', o', ptr')` the value read from `A` on line 9. -/
structure Loc where
  pc : PC T.Resp
  op : WithBot T.Op
  ptr : Option Ptr
  t : ℕ
  snap : SVal T.State T.Resp
  ann : AVal T.Op

variable {T}

/-- The pointer to the own cell (`ptrNoop` if not yet allocated, which never happens when it is
used). -/
def Loc.me (l : Loc T) : Ptr := l.ptr.getD ⊥

/-- `applyT` extended to `Noop` (never used on `Noop`). -/
def applyT (o : WithBot T.Op) (s : T.State) : T.State × RVal T.Resp :=
  match o with
  | ⊥ => (s, .bot)
  | (o : T.Op) => ((T.δ s o).1, .val (T.δ s o).2)

/-- The new value of `S` tried on line 13 (computed on line 12). -/
def Loc.newS (l : Loc T) : SVal T.State T.Resp :=
  ⟨l.ann.time, (applyT l.ann.op l.snap.state).1, (applyT l.ann.op l.snap.state).2, l.ann.ptr⟩

/-- The triple `(t, o, ptr)` of the current operation. -/
def Loc.mine (l : Loc T) : AVal T.Op := ⟨l.t, l.op, l.me⟩

/-- The local state after an invocation of `o`. -/
def Loc.invoke (l : Loc T) (o : T.Op) : Loc T :=
  { l with op := (o : WithBot T.Op), pc := if l.ptr = none then .l2 else .l3 }

variable (T)

open Classical in
/-- The next action of a process (lines 2–16 of Algorithm 1). -/
noncomputable def act (l : Loc T) : Action T (base T) (Loc T) :=
  match l.pc with
  | .l2 => .access .MM () (fun n => { l with ptr := some (n : Ptr), pc := .l3 })
  | .l3 => .access .C .fai (fun τ => { l with t := τ, pc := .l4 })
  | .l4 => .access (.cell l.me) (.write ⟨l.t, .null⟩) (fun _ => { l with pc := .l5 })
  | .l5 => .access (.cell l.me) .read (fun v =>
      match v with
      | .inl c =>
        if c = ⟨l.t, .null⟩ then { l with pc := .l6 } else
        match c.resp with
        | .val r => { l with pc := .l16 r }
        | _ => { l with pc := .l5 }
      | .inr _ => l)
  | .l6 => .access .S .read (fun v =>
      match v with
      | .inl s => { l with snap := s, pc := .l7 }
      | .inr _ => l)
  | .l7 => .access (.cell l.snap.ptr) (.cas ⟨l.snap.time, .null⟩ ⟨l.snap.time, l.snap.resp⟩)
      (fun _ => { l with pc := .l8 })
  | .l8 => .access .A (.gcas .gt l.mine l.mine) (fun _ => { l with pc := .l9 })
  | .l9 => .access .A .read (fun v =>
      match v with
      | .inl a => { l with ann := a, pc := .l10 }
      | .inr _ => l)
  | .l10 => .access (.cell l.ann.ptr) .read (fun v =>
      match v with
      | .inl c => if c = ⟨l.ann.time, .null⟩ then { l with pc := .l13 } else { l with pc := .l15 }
      | .inr _ => l)
  | .l13 => .access .S (.cas l.snap l.newS) (fun _ => { l with pc := .l5 })
  | .l15 => .access .A (.gcas .eq l.ann l.mine) (fun _ => { l with pc := .l5 })
  | .l16 r => .ret r { l with pc := .l2 }

variable (P : Type)

/-- **Algorithm 1** for processes `P`, with initial cell contents `cellInit`. -/
noncomputable def alg (cellInit : ℕ → CellVal T.Resp) : Impl T (base T) P (Loc T) where
  memInit
    | .C => (1 : ℕ)
    | .A => (⟨0, ⊥, ⊥⟩ : AVal T.Op)
    | .S => (⟨0, T.init, .bot, ⊥⟩ : SVal T.State T.Resp)
    | .MM => (0 : ℕ)
    | .cell x => (match x with
        | ⊥ => (⟨0, .bot⟩ : CellVal T.Resp)
        | (n : ℕ) => cellInit n)
  locInit _ := ⟨.l2, ⊥, none, 0, ⟨0, T.init, .bot, ⊥⟩, ⟨0, ⊥, ⊥⟩⟩
  invoke _ l o := l.invoke o
  act _ l := act T l

end Podc.GeneralizedCAS
