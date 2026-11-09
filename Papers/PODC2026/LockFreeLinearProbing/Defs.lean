import Cslib.Computability.Distributed.SharedMemory.Model
import Cslib.Computability.Distributed.SharedMemory.Objects.LLSC
import Mathlib

/-!
# The LL/SC lock-free linear-probing hash table (Algorithms 1–5)

Attiya, Oshman, Schiller, *Space-Efficient Lock-Free Linear-Probing Hash Table*,
arXiv 2606.17315v1 (full version of the PODC 2026 brief announcement).

The table `table[0..m-1]` is modelled in CSLib's asynchronous shared-memory model
(`Cslib.SharedMemory.Impl`): base object `i : Fin m` is an LL/SC object (`llscObj`) holding a
`Cell`. Following Algorithm 5, `Read` is `LL`, `Modify(loc, old, new)` is `SC(loc, new)` and the
plain reads `table[i]` of lines 94, 102 and 105 are `VL` (which returns the current value and
does not touch any link). Indices are `Fin m`, so `i + 1` and `i - 1` wrap around (the paper:
"we use modular arithmetic that wraps at the m-th cell"); the comparison `i − h(v) < j − h(v)`
of line 51 is `dist v i < dist v j` with `dist v i = (i - h v).val ∈ [0, m)`.

Each process runs the pseudocode as a state machine: the program counter `PC` names the next
shared-memory access (one primitive per step, as in Section 3); the local computation between
two accesses (control flow of Algorithms 1–4, including the `goto`s and the returns of the helper
functions) is done by the functions `fsBody`, `vcRet`, `dsBody`, … below.

The dictionary (Section 4) is the nondeterministic specification `dictSpec`: `insert` may also
return `ABORT` at any time without changing the state.
-/

namespace Podc.LockFreeLinearProbing

open Cslib.SharedMemory

/-! ## Cells, operations, responses -/

/-- The tag of a stored key: `tentative`, `final` or `revalidate`. -/
inductive Tag where
  | tent
  | fin
  | reval
  deriving DecidableEq, Repr

/-- The content of a table cell (LL/SC version): `EMPTY`, `TOMBSTONE`, the cleanup states
`DELETED`, `COLLIDED`, or a tagged key `⟨v, tag⟩`. -/
inductive Cell (K : Type) where
  | empty
  | tomb
  | deleted
  | collided
  | key (v : K) (t : Tag)
  deriving DecidableEq, Repr

/-- The key stored in a cell (`val(x)` of the paper), if any. -/
def Cell.key? {K : Type} : Cell K → Option K
  | .key v _ => some v
  | _ => none

@[simp] lemma Cell.key?_key {K : Type} (v : K) (t : Tag) : (Cell.key v t).key? = some v := rfl
@[simp] lemma Cell.key?_empty {K : Type} : (Cell.empty : Cell K).key? = none := rfl
@[simp] lemma Cell.key?_tomb {K : Type} : (Cell.tomb : Cell K).key? = none := rfl
@[simp] lemma Cell.key?_deleted {K : Type} : (Cell.deleted : Cell K).key? = none := rfl
@[simp] lemma Cell.key?_collided {K : Type} : (Cell.collided : Cell K).key? = none := rfl

/-- Dictionary operations. -/
inductive DOp (K : Type) where
  | insert (v : K)
  | delete (v : K)
  | lookup (v : K)
  deriving DecidableEq, Repr

/-- The key of an operation. -/
def DOp.key {K : Type} : DOp K → K
  | .insert v | .delete v | .lookup v => v

/-- Responses: `true`, `false`, or `ABORT` (only for `insert`). -/
inductive Res where
  | ok (b : Bool)
  | abort
  deriving DecidableEq, Repr

/-- The dictionary as a deterministic object (no aborts); the state says which keys are in the
set. Used for the operation and response types of the implementation. -/
def dict (K : Type) [DecidableEq K] : ObjSpec where
  State := K → Bool
  Op := DOp K
  Resp := Res
  init := fun _ => false
  δ s
    | .insert v => (Function.update s v true, .ok (!s v))
    | .delete v => (Function.update s v false, .ok (s v))
    | .lookup v => (s, .ok (s v))

instance (K : Type) [DecidableEq K] : DecidableEq (dict K).Resp := inferInstanceAs (DecidableEq Res)
instance (K : Type) [DecidableEq K] : DecidableEq (dict K).Op := inferInstanceAs (DecidableEq (DOp K))

/-- The sequential specification of Section 4: the dictionary, where an `insert` may in
addition return `ABORT` at any point without modifying the set. -/
def dictSpec (K : Type) [DecidableEq K] : NSpec (dict K).Op (dict K).Resp where
  State := K → Bool
  init := fun _ => false
  Step s o r s' := ((dict K).δ s o = (s', r)) ∨ (∃ v, o = .insert v ∧ r = .abort ∧ s' = s)

/-! ## Local states -/

/-- Program counters: the next shared-memory access of a process (named after the pseudocode
line), `ret` (about to return `rsp`) and `idle` (no pending operation). -/
inductive PC where
  | idle
  /-- line 2/11: `LL(table[i])` in the forward scan -/
  | fsLL
  /-- line 16: `LL(table[i])` in the backward scan -/
  | bsLL
  /-- line 93: `SC(table[i], ⟨v, revalidate⟩)` -/
  | vcSC
  /-- line 94: plain read of `table[i]` -/
  | vcRD
  /-- line 86: `SC(table[i], TOMBSTONE)` -/
  | tdSCF
  /-- line 88: `SC(table[i], DELETED)` -/
  | tdSCD
  /-- line 89: `LL(table[i])` -/
  | tdLL
  /-- line 41/47: `LL(table[j])` while looking for a free cell -/
  | iLL
  /-- line 43: `SC(table[j], ⟨v, tentative⟩)` -/
  | iSC
  /-- line 48/65: `LL(table[i])` in the duplicate scan -/
  | dsLL
  /-- line 102: plain read of `table[j]` (in `del_other_copy`) -/
  | docRD
  /-- line 104: `SC(table[i], COLLIDED)` -/
  | docSC
  /-- line 105: plain read of `table[i]` -/
  | docRD2
  /-- line 57: `LL(table[j])` -/
  | l57LL
  /-- line 58: `SC(table[j], ⟨v, tentative⟩)` -/
  | l58SC
  /-- line 66: `LL(table[j])` -/
  | l66LL
  /-- line 67: `SC(table[j], ⟨v, final⟩)` -/
  | l67SC
  /-- line 69: `SC(table[j], ⟨v, tentative⟩)` -/
  | l69SC
  /-- line 76: `LL(table[j])` in `del_copy` -/
  | dcLL76
  /-- line 78: `SC(table[j], ⟨v, tentative⟩)` -/
  | dcSC78
  /-- line 79: `LL(table[j])` -/
  | dcLL79
  /-- line 80: `SC(table[j], TOMBSTONE)` -/
  | dcSC80
  /-- about to return `rsp` -/
  | ret
  deriving DecidableEq, Repr

/-- The local state of a process: current operation, program counter and the local variables of
the pseudocode (`i`, `j`, `val`, `cur val`, and `fwd` = whether the current helper call
`validate_copy`/`try_delete` was made from the forward scan). -/
structure Loc (K : Type) (m : ℕ) where
  op : DOp K
  pc : PC
  i : Fin m
  j : Fin m
  val : Cell K
  cur : Cell K
  fwd : Bool
  rsp : Res

/-- Results of the scans: `true`, `false`, an index, or `⊥`. -/
inductive SR (m : ℕ) where
  | tt
  | ff
  | idx (i : Fin m)
  | bot

section Program

variable {K : Type} [DecidableEq K] {m : ℕ} [NeZero m] (h : K → Fin m)

/-- The probe distance `i − h(v) (mod m)` of cell `i` for key `v`. -/
def dist (v : K) (i : Fin m) : ℕ := ((i - h v : Fin m) : ℕ)

/-- Return `r`. -/
def retL (l : Loc K m) (r : Res) : Loc K m := { l with pc := .ret, rsp := r }

/-- Lines 25–26, 31–32, 37–38: what an operation does with the result of `forward_scan`. -/
def fsReturn (l : Loc K m) (r : SR m) : Loc K m :=
  match l.op, r with
  | .delete _, .tt => retL l (.ok true)
  | .delete _, .ff => retL l (.ok false)
  | .lookup _, .tt => retL l (.ok true)
  | .insert _, .tt => retL l (.ok false)
  | _, .idx i => { l with i := i, pc := .bsLL }
  | _, _ => retL l (.ok false)

/-- Lines 12–13: end of the forward scan. -/
def fsEnd (l : Loc K m) : Loc K m :=
  if l.i = h l.op.key ∧ l.val = .empty then fsReturn l (.idx l.i)
  else fsReturn l (.idx (l.i - 1))

/-- Lines 9–11: advance the forward scan. -/
def fsNext (l : Loc K m) : Loc K m :=
  if l.i + 1 = h l.op.key then fsEnd h { l with i := l.i + 1 }
  else { l with i := l.i + 1, pc := .fsLL }

/-- Lines 27–29, 33–35, 39–41: what an operation does with the result of `backward_scan`. -/
def bsReturn (l : Loc K m) (r : SR m) : Loc K m :=
  match l.op, r with
  | .delete _, .tt => retL l (.ok true)
  | .delete _, _ => retL l (.ok false)
  | .lookup _, .tt => retL l (.ok true)
  | .lookup _, _ => retL l (.ok false)
  | .insert _, .tt => retL l (.ok false)
  | .insert v, _ => { l with j := h v, pc := .iLL }

/-- Lines 22–23: advance the backward scan. -/
def bsCheck (l : Loc K m) : Loc K m :=
  if l.i = h l.op.key then bsReturn h l .bot else { l with i := l.i - 1, pc := .bsLL }

/-- Return of `validate_copy` with result `b` (lines 5, 18). -/
def vcRet (l : Loc K m) (b : Bool) : Loc K m :=
  if l.fwd then (if b then fsReturn l .tt else fsNext h l)
  else (if b then bsReturn h l .tt else bsCheck h l)

/-- Line 92 (`validate_copy`, local part). -/
def vcStart (l : Loc K m) : Loc K m :=
  if l.val = .key l.op.key .fin ∨ l.val = .key l.op.key .reval then vcRet h l true
  else { l with pc := .vcSC }

/-- Return of `try_delete` with result `r` (lines 7–8, 20–21). -/
def tdRet (l : Loc K m) (r : SR m) : Loc K m :=
  match r with
  | .bot => if l.fwd then fsNext h l else bsCheck h l
  | r => if l.fwd then fsReturn l r else bsReturn h l r

/-- Lines 84–85, 87, 90 (`try_delete`, local part). -/
def tdBody (l : Loc K m) : Loc K m :=
  if l.val.key? = some l.op.key then
    (if l.val = .key l.op.key .fin then { l with pc := .tdSCF } else { l with pc := .tdSCD })
  else tdRet h l .bot

/-- Is the operation an `insert` or a `lookup`? -/
def DOp.isInsLook : DOp K → Bool
  | .delete _ => false
  | _ => true

/-- Lines 3–8 (`forward_scan`, after reading `val`). -/
def fsBody (l : Loc K m) : Loc K m :=
  if l.val = .empty then fsEnd h l
  else if l.val.key? = some l.op.key then
    (if l.op.isInsLook then vcStart h { l with fwd := true } else tdBody h { l with fwd := true })
  else fsNext h l

/-- Lines 17–21 (`backward_scan`, after reading `val`). -/
def bsBody (l : Loc K m) : Loc K m :=
  if l.val.key? = some l.op.key then
    (if l.op.isInsLook then vcStart h { l with fwd := false } else tdBody h { l with fwd := false })
  else bsCheck h l

/-- Lines 45–47: try the next cell for the tentative copy (`ABORT` after a full cycle). -/
def iNext (l : Loc K m) : Loc K m :=
  if l.j + 1 = h l.op.key then retL l .abort else { l with j := l.j + 1, pc := .iLL }

/-- Line 43 (local part): try to write the tentative copy into an available cell. -/
def iBody (l : Loc K m) : Loc K m :=
  if l.val = .empty ∨ l.val = .tomb then { l with pc := .iSC } else iNext h l

/-- Line 48 (`goto 48`): restart the duplicate scan at `h(v)`. -/
def ds48 (l : Loc K m) : Loc K m := { l with i := h l.op.key, pc := .dsLL }

/-- Lines 63–65: advance the duplicate scan. -/
def dsNext (l : Loc K m) : Loc K m :=
  if l.i + 1 = h l.op.key then { l with i := l.i + 1, pc := .l66LL }
  else { l with i := l.i + 1, pc := .dsLL }

/-- Lines 49–56 (duplicate scan, after reading `val`). -/
def dsBody (l : Loc K m) : Loc K m :=
  if l.val = .empty then { l with pc := .l66LL }
  else if l.i ≠ l.j ∧ l.val.key? = some l.op.key then
    (if dist h l.op.key l.i < dist h l.op.key l.j ∨ l.val = .key l.op.key .fin then
      { l with pc := .dcLL76 }
    else if l.val ≠ .key l.op.key .reval then { l with pc := .docRD }
    else dsNext h l)
  else dsNext h l

/-- Return of `del_other_copy` with result `b` (line 56). -/
def docRet (l : Loc K m) (b : Bool) : Loc K m :=
  if b then dsNext h l else { l with pc := .l57LL }

/-- The initial local state of an operation (lines 2, 25, 31, 37). -/
def start (o : DOp K) : Loc K m :=
  { op := o, pc := .fsLL, i := h o.key, j := h o.key, val := .empty, cur := .empty, fwd := true,
    rsp := .abort }

/-- The base objects: an LL/SC cell per index. -/
abbrev Mem (K : Type) (m : ℕ) (P : Type) [DecidableEq P] : Fin m → ObjSpec :=
  fun _ => llscObj (Cell K) P .empty

variable {P : Type} [DecidableEq P]

/-- One step of process `p` in local state `l` (Algorithms 1–5). -/
def act (p : P) (l : Loc K m) : Action (dict K) (Mem K m P) (Loc K m) :=
  let v := l.op.key
  match l.pc with
  | .fsLL => .access l.i (.ll p) fun r => fsBody h { l with val := r.1 }
  | .bsLL => .access l.i (.ll p) fun r => bsBody h { l with val := r.1 }
  | .vcSC => .access l.i (.sc p (.key v .reval)) fun r =>
      if r.2 then vcRet h l true else { l with pc := .vcRD }
  | .vcRD => .access l.i (.vl p) fun r => vcRet h { l with val := r.1 } (r.1.key? = some v)
  | .tdSCF => .access l.i (.sc p .tomb) fun r => tdRet h l (if r.2 then .tt else .ff)
  | .tdSCD => .access l.i (.sc p .deleted) fun r =>
      if r.2 then tdRet h l .tt else { l with pc := .tdLL }
  | .tdLL => .access l.i (.ll p) fun r => tdBody h { l with val := r.1 }
  | .iLL => .access l.j (.ll p) fun r => iBody h { l with val := r.1 }
  | .iSC => .access l.j (.sc p (.key v .tent)) fun r => if r.2 then ds48 h l else iNext h l
  | .dsLL => .access l.i (.ll p) fun r => dsBody h { l with val := r.1 }
  | .docRD => .access l.j (.vl p) fun r =>
      if r.1 = .key v .tent then { l with cur := r.1, pc := .docSC }
      else docRet h { l with cur := r.1 } false
  | .docSC => .access l.i (.sc p .collided) fun r =>
      if r.2 then docRet h l true else { l with pc := .docRD2 }
  | .docRD2 => .access l.i (.vl p) fun r => docRet h l (r.1 ≠ .key v .fin)
  | .l57LL => .access l.j (.ll p) fun r =>
      if r.1 = .key v .reval then { l with cur := r.1, pc := .l58SC }
      else { l with cur := r.1, pc := .dcLL76 }
  | .l58SC => .access l.j (.sc p (.key v .tent)) fun r =>
      if r.2 then ds48 h l else { l with pc := .dcLL76 }
  | .l66LL => .access l.j (.ll p) fun r =>
      if r.1 = .key v .tent then { l with cur := r.1, pc := .l67SC }
      else if r.1 = .key v .reval then { l with cur := r.1, pc := .l69SC }
      else { l with cur := r.1, pc := .dcLL76 }
  | .l67SC => .access l.j (.sc p (.key v .fin)) fun r =>
      if r.2 then retL l (.ok true) else { l with pc := .dcLL76 }
  | .l69SC => .access l.j (.sc p (.key v .tent)) fun r =>
      if r.2 then ds48 h l else { l with pc := .dcLL76 }
  | .dcLL76 => .access l.j (.ll p) fun r =>
      if r.1 = .key v .reval then { l with val := r.1, pc := .dcSC78 }
      else { l with val := r.1, pc := .dcSC80 }
  | .dcSC78 => .access l.j (.sc p (.key v .tent)) fun r =>
      if r.2 then ds48 h l else { l with pc := .dcLL79 }
  | .dcLL79 => .access l.j (.ll p) fun r => { l with val := r.1, pc := .dcSC80 }
  | .dcSC80 => .access l.j (.sc p .tomb) fun r =>
      if r.2 then retL l (.ok (decide (l.val = .deleted))) else { l with pc := .dcLL76 }
  | .ret => .ret l.rsp { l with pc := .idle }
  | .idle => .ret .abort l

/-- The hash table of Algorithms 1–5 (LL/SC version) for `n` processes `P`, keys `K`, a table
of `m` cells and hash function `h`, starting from the empty table. -/
def impl [Inhabited K] : Impl (dict K) (Mem K m P) P (Loc K m) where
  memInit _ := (.empty, [])
  locInit _ := { start h (.lookup default) with pc := .idle }
  invoke _ _ o := start h o
  act := act h

end Program

end Podc.LockFreeLinearProbing
