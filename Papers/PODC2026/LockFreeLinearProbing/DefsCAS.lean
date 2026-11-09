import Papers.PODC2026.LockFreeLinearProbing.Defs

/-!
# The CAS version of the hash table (Algorithms 1–4 with Algorithm 6)

The same program as `Defs.lean`, with `Read` = atomic read and `Modify(loc, old, new)` =
`CAS(loc, old, new)` (base objects: CSLib's `casObject`), cells that may additionally hold the
marked state `⟨⟨v, j⟩, marked⟩` (`j` the cell of the marking insert), `restart(x)` true for
`⟨v, revalidate⟩` and for marked values of `v`, and `del_other_copy` of Algorithm 6
(lines 113–124).
-/

namespace Podc.LockFreeLinearProbing.CAS

open Cslib.SharedMemory

/-- Cells of the CAS version. -/
inductive CCell (K : Type) (m : ℕ) where
  | empty
  | tomb
  | deleted
  | collided
  | key (v : K) (t : Tag)
  /-- `⟨⟨v, j⟩, marked⟩`: a copy of `v` reserved by the insert owning cell `j`. -/
  | marked (v : K) (j : Fin m)
  deriving DecidableEq, Repr

/-- `val(x)`: the key a cell contains (marked values contain their key, Section 5.1). -/
def CCell.key? {K : Type} {m : ℕ} : CCell K m → Option K
  | .key v _ => some v
  | .marked v _ => some v
  | _ => none

/-- `restart(x)`: `⟨v, revalidate⟩` or a marked copy of `v`. -/
def restart {K : Type} [DecidableEq K] {m : ℕ} (v : K) : CCell K m → Bool
  | .key w .reval => decide (w = v)
  | .marked w _ => decide (w = v)
  | _ => false

/-- Program counters (as in `PC`; `del_other_copy` has its own lines 116–122). -/
inductive PCc where
  | idle | fsLL | bsLL | vcSC | vcRD | tdSCF | tdSCD | tdLL | iLL | iSC | dsLL
  /-- line 116: `CAS(table[i], val, ⟨⟨v, j⟩, marked⟩)` -/
  | docM
  /-- line 117: read `table[i]` -/
  | docMR
  /-- line 120: read `table[j]` -/
  | docRD
  /-- line 122: `CAS(table[i], ⟨⟨v, j⟩, marked⟩, COLLIDED)` -/
  | docC
  | l57LL | l58SC | l66LL | l67SC | l69SC | dcLL76 | dcSC78 | dcLL79 | dcSC80 | ret
  deriving DecidableEq, Repr

/-- Local states. -/
structure LocC (K : Type) (m : ℕ) where
  op : DOp K
  pc : PCc
  i : Fin m
  j : Fin m
  val : CCell K m
  cur : CCell K m
  fwd : Bool
  rsp : Res

section Program

variable {K : Type} [DecidableEq K] {m : ℕ} [NeZero m] (h : K → Fin m)

def retL (l : LocC K m) (r : Res) : LocC K m := { l with pc := .ret, rsp := r }

def fsReturn (l : LocC K m) (r : SR m) : LocC K m :=
  match l.op, r with
  | .delete _, .tt => retL l (.ok true)
  | .delete _, .ff => retL l (.ok false)
  | .lookup _, .tt => retL l (.ok true)
  | .insert _, .tt => retL l (.ok false)
  | _, .idx i => { l with i := i, pc := .bsLL }
  | _, _ => retL l (.ok false)

def fsEnd (l : LocC K m) : LocC K m :=
  if l.i = h l.op.key ∧ l.val = .empty then fsReturn l (.idx l.i)
  else fsReturn l (.idx (l.i - 1))

def fsNext (l : LocC K m) : LocC K m :=
  if l.i + 1 = h l.op.key then fsEnd h { l with i := l.i + 1 }
  else { l with i := l.i + 1, pc := .fsLL }

def bsReturn (l : LocC K m) (r : SR m) : LocC K m :=
  match l.op, r with
  | .delete _, .tt => retL l (.ok true)
  | .delete _, _ => retL l (.ok false)
  | .lookup _, .tt => retL l (.ok true)
  | .lookup _, _ => retL l (.ok false)
  | .insert _, .tt => retL l (.ok false)
  | .insert v, _ => { l with j := h v, pc := .iLL }

def bsCheck (l : LocC K m) : LocC K m :=
  if l.i = h l.op.key then bsReturn h l .bot else { l with i := l.i - 1, pc := .bsLL }

def vcRet (l : LocC K m) (b : Bool) : LocC K m :=
  if l.fwd then (if b then fsReturn l .tt else fsNext h l)
  else (if b then bsReturn h l .tt else bsCheck h l)

def vcStart (l : LocC K m) : LocC K m :=
  if l.val = .key l.op.key .fin ∨ l.val = .key l.op.key .reval then vcRet h l true
  else { l with pc := .vcSC }

def tdRet (l : LocC K m) (r : SR m) : LocC K m :=
  match r with
  | .bot => if l.fwd then fsNext h l else bsCheck h l
  | r => if l.fwd then fsReturn l r else bsReturn h l r

def tdBody (l : LocC K m) : LocC K m :=
  if l.val.key? = some l.op.key then
    (if l.val = .key l.op.key .fin then { l with pc := .tdSCF } else { l with pc := .tdSCD })
  else tdRet h l .bot

def fsBody (l : LocC K m) : LocC K m :=
  if l.val = .empty then fsEnd h l
  else if l.val.key? = some l.op.key then
    (if l.op.isInsLook then vcStart h { l with fwd := true } else tdBody h { l with fwd := true })
  else fsNext h l

def bsBody (l : LocC K m) : LocC K m :=
  if l.val.key? = some l.op.key then
    (if l.op.isInsLook then vcStart h { l with fwd := false } else tdBody h { l with fwd := false })
  else bsCheck h l

def iNext (l : LocC K m) : LocC K m :=
  if l.j + 1 = h l.op.key then retL l .abort else { l with j := l.j + 1, pc := .iLL }

def iBody (l : LocC K m) : LocC K m :=
  if l.val = .empty ∨ l.val = .tomb then { l with pc := .iSC } else iNext h l

def ds48 (l : LocC K m) : LocC K m := { l with i := h l.op.key, pc := .dsLL }

def dsNext (l : LocC K m) : LocC K m :=
  if l.i + 1 = h l.op.key then { l with i := l.i + 1, pc := .l66LL }
  else { l with i := l.i + 1, pc := .dsLL }

/-- Line 114–115 (local part of `del_other_copy`, Algorithm 6). -/
def docStart (l : LocC K m) : LocC K m :=
  if (∃ k, l.val = .marked l.op.key k ∧ k ≠ l.j) then dsNext h l          -- line 114
  else if l.val ≠ .marked l.op.key l.j then { l with pc := .docM }         -- line 115
  else { l with pc := .docRD }                                            -- line 120

def dsBody (l : LocC K m) : LocC K m :=
  if l.val = .empty then { l with pc := .l66LL }
  else if l.i ≠ l.j ∧ l.val.key? = some l.op.key then
    (if dist h l.op.key l.i < dist h l.op.key l.j ∨ l.val = .key l.op.key .fin then
      { l with pc := .dcLL76 }
    else if l.val ≠ .key l.op.key .reval then docStart h l
    else dsNext h l)
  else dsNext h l

def docRet (l : LocC K m) (b : Bool) : LocC K m :=
  if b then dsNext h l else { l with pc := .l57LL }

def start (o : DOp K) : LocC K m :=
  { op := o, pc := .fsLL, i := h o.key, j := h o.key, val := .empty, cur := .empty, fwd := true,
    rsp := .abort }

/-- The base objects: a CAS register per cell. -/
abbrev MemC (K : Type) (m : ℕ) [DecidableEq K] : Fin m → ObjSpec :=
  fun _ => casObject (CCell K m) .empty

/-- The value of a `read` response. -/
def rv : CCell K m ⊕ Bool → CCell K m
  | .inl x => x
  | .inr _ => .empty

/-- The success flag of a `CAS` response. -/
def rb : CCell K m ⊕ Bool → Bool
  | .inl _ => false
  | .inr b => b

variable {P : Type}

/-- One step of a process (Algorithms 1–4 and 6). -/
def act (_p : P) (l : LocC K m) : Action (dict K) (MemC K m) (LocC K m) :=
  let v := l.op.key
  match l.pc with
  | .fsLL => .access l.i .read fun r => fsBody h { l with val := rv r }
  | .bsLL => .access l.i .read fun r => bsBody h { l with val := rv r }
  | .vcSC => .access l.i (.cas l.val (.key v .reval)) fun r =>
      if rb r then vcRet h l true else { l with pc := .vcRD }
  | .vcRD => .access l.i .read fun r => vcRet h { l with val := rv r } ((rv r).key? = some v)
  | .tdSCF => .access l.i (.cas l.val .tomb) fun r => tdRet h l (if rb r then .tt else .ff)
  | .tdSCD => .access l.i (.cas l.val .deleted) fun r =>
      if rb r then tdRet h l .tt else { l with pc := .tdLL }
  | .tdLL => .access l.i .read fun r => tdBody h { l with val := rv r }
  | .iLL => .access l.j .read fun r => iBody h { l with val := rv r }
  | .iSC => .access l.j (.cas l.val (.key v .tent)) fun r => if rb r then ds48 h l else iNext h l
  | .dsLL => .access l.i .read fun r => dsBody h { l with val := rv r }
  | .docM => .access l.i (.cas l.val (.marked v l.j)) fun r =>
      if rb r then { l with pc := .docRD } else { l with pc := .docMR }
  | .docMR => .access l.i .read fun r =>
      docRet h { l with val := rv r } (rv r ≠ .key v .fin)
  | .docRD => .access l.j .read fun r =>
      if rv r = .key v .tent then { l with cur := rv r, pc := .docC }
      else docRet h { l with cur := rv r } false
  | .docC => .access l.i (.cas (.marked v l.j) .collided) fun _ => docRet h l true
  | .l57LL => .access l.j .read fun r =>
      if restart v (rv r) then { l with cur := rv r, pc := .l58SC }
      else { l with cur := rv r, pc := .dcLL76 }
  | .l58SC => .access l.j (.cas l.cur (.key v .tent)) fun r =>
      if rb r then ds48 h l else { l with pc := .dcLL76 }
  | .l66LL => .access l.j .read fun r =>
      if rv r = .key v .tent then { l with cur := rv r, pc := .l67SC }
      else if restart v (rv r) then { l with cur := rv r, pc := .l69SC }
      else { l with cur := rv r, pc := .dcLL76 }
  | .l67SC => .access l.j (.cas l.cur (.key v .fin)) fun r =>
      if rb r then retL l (.ok true)
      else if restart v l.cur then { l with pc := .l69SC } else { l with pc := .dcLL76 }
  | .l69SC => .access l.j (.cas l.cur (.key v .tent)) fun r =>
      if rb r then ds48 h l else { l with pc := .dcLL76 }
  | .dcLL76 => .access l.j .read fun r =>
      if rv r = .key v .reval then { l with val := rv r, pc := .dcSC78 }
      else { l with val := rv r, pc := .dcSC80 }
  | .dcSC78 => .access l.j (.cas l.val (.key v .tent)) fun r =>
      if rb r then ds48 h l else { l with pc := .dcLL79 }
  | .dcLL79 => .access l.j .read fun r => { l with val := rv r, pc := .dcSC80 }
  | .dcSC80 => .access l.j (.cas l.val .tomb) fun r =>
      if rb r then retL l (.ok (decide (l.val = .deleted))) else { l with pc := .dcLL76 }
  | .ret => .ret l.rsp { l with pc := .idle }
  | .idle => .ret .abort l

/-- The CAS version of the hash table, starting from the empty table. -/
def implC [Inhabited K] : Impl (dict K) (MemC K m) P (LocC K m) where
  memInit _ := .empty
  locInit _ := { start h (.lookup default) with pc := .idle }
  invoke _ _ o := start h o
  act := act h

end Program

end Podc.LockFreeLinearProbing.CAS
