import Cslib.Computability.Distributed.SharedMemory.Model
import Podc.Computability.Distributed.SharedMemory.View
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.List.FinRange

/-!
# Algorithm 1: a multi-writer, `m`-reader auditable register

Attiya, Fernández Anta, Milani, Rapetti, Travers, *Auditing without Leaks Despite Curiosity*,
PODC 2025, Section 3, Algorithm 1, in CSLib's asynchronous shared-memory model
(`Cslib.SharedMemory.Impl`).

* Processes: readers `rd j` (`j : Fin m`), writers `wr w` (`w : W`), auditors `au a` (`a : Au`).
* The implemented object `auditReg m V v₀`: a register over `V` whose `read j` (the reader's
  identity is part of the operation, since sequential specifications cannot see the caller) also
  records the pair `(j, v)`; `audit` returns the set of recorded pairs.
* Base objects: `R` (a triple `(seq, val, bits)` supporting read, fetch&xor on one tracking bit,
  and compare&swap), `SN` (a compare&swap register over `ℕ`), `V[s]` (registers over `Option V`)
  and `B[s][j]` (Boolean registers).
* The one-time pads `rnd : ℕ → Fin m → Bool` are a parameter of the implementation (known to
  writers and auditors, not to readers): the algorithm is the family `alg1 m W Au V v₀ rnd`.

Each step of a process applies exactly one primitive; the `for each` loops of lines 13, 18–20 are
unfolded into one step per register access.
-/

namespace Podc.AuditingWithoutLeaks

open Cslib.SharedMemory

variable (m : ℕ) (W Au V : Type)

/-- Processes: `m` readers, writers, auditors. -/
inductive Proc where
  | rd (j : Fin m)
  | wr (w : W)
  | au (a : Au)
  deriving DecidableEq

/-- Operations of an auditable register. The reader's identity is an argument of `read`. -/
inductive AOp where
  | read (j : Fin m)
  | write (v : V)
  | audit

/-- Responses of an auditable register. -/
inductive AResp where
  | val (v : V)
  | ack
  | set (S : Set (Fin m × V))

/-- Sequential specification of an auditable register: a read by `j` returns the current value `v`
and records `(j, v)`; an audit returns the set of recorded pairs (exactly the pairs of preceding
reads: accuracy and completeness). -/
abbrev auditReg (v₀ : V) : ObjSpec where
  State := V × Set (Fin m × V)
  Op := AOp m V
  Resp := AResp m V
  init := (v₀, ∅)
  δ q o := match o with
    | .read j => ((q.1, insert (j, q.1) q.2), .val q.1)
    | .write w => ((w, q.2), .ack)
    | .audit => (q, .set q.2)

/-- Contents of `R`: sequence number, value, tracking bits. -/
structure RVal where
  seq : ℕ
  val : V
  bits : Fin m → Bool
  deriving DecidableEq

/-- Primitives on `R`. -/
inductive ROp where
  | read
  /-- `fetch&xor(2^j)`: flip tracking bit `j`, return the old contents. -/
  | fx (j : Fin m)
  | cas (old new : RVal m V)

variable {m V} in
/-- Flip bit `j` of a bit string. -/
def flip (b : Fin m → Bool) (j : Fin m) : Fin m → Bool := Function.update b j (!b j)

/-- The base object `R`. Read and fetch&xor return the old contents (`inl`); compare&swap returns
its success flag (`inr`). -/
abbrev rObj [DecidableEq V] (r₀ : RVal m V) : ObjSpec where
  State := RVal m V
  Op := ROp m V
  Resp := RVal m V ⊕ Bool
  init := r₀
  δ q o := match o with
    | .read => (q, .inl q)
    | .fx j => ({ q with bits := flip q.bits j }, .inl q)
    | .cas old new => if q = old then (new, .inr true) else (q, .inr false)

/-- Names of base objects. -/
inductive Obj where
  | R
  | SN
  | V (s : ℕ)
  | B (s : ℕ) (j : Fin m)
  deriving DecidableEq

/-- Specifications of the base objects (`ObjSpec.init` is ignored by CSLib; the initial memory is
`Impl.memInit`). -/
abbrev BO [DecidableEq V] (v₀ : V) : Obj m → ObjSpec
  | .R => rObj m V ⟨0, v₀, fun _ => false⟩
  | .SN => casObject ℕ 0
  | .V _ => register (Option V) none
  | .B _ _ => register Bool false

/-- Local states (program counters with the local variables in use). -/
inductive Loc where
  /-- Reader, idle; `prev` = `(prev_sn, prev_val)` (`none` initially). -/
  | rIdle (prev : Option (ℕ × V))
  /-- Reader, line 2: about to read `SN`. -/
  | rSN (prev : Option (ℕ × V))
  /-- Reader, line 4: has read `y ≠ prev_sn` from `SN`, about to apply fetch&xor to `R`. -/
  | rFX (prev : Option (ℕ × V)) (y : ℕ)
  /-- Reader, line 5: fetched `(sn, val, _)`, about to apply `SN.compare&swap(sn-1, sn)`. -/
  | rCAS (prev : Option (ℕ × V)) (sn : ℕ) (val : V)
  /-- Reader, about to return `val` (with `prev` already updated). -/
  | rRet (prev : Option (ℕ × V)) (val : V)
  /-- Writer, idle. -/
  | wIdle
  /-- Writer, line 8: about to read `SN`. -/
  | wSN (v : V)
  /-- Writer, line 10: about to read `R`. -/
  | wR (v : V) (sn : ℕ)
  /-- Writer, line 12: read `r` from `R` with `r.seq < sn`, about to write `V[r.seq]`. -/
  | wV (v : V) (sn : ℕ) (r : RVal m V)
  /-- Writer, line 13: about to write `true` to `B[r.seq][j]` for the first `j` of `todo`. -/
  | wB (v : V) (sn : ℕ) (r : RVal m V) (todo : List (Fin m))
  /-- Writer, line 14: about to apply `R.compare&swap(r, (sn, v, rand_sn))`. -/
  | wCAS (v : V) (sn : ℕ) (r : RVal m V)
  /-- Writer, line 15: about to apply `SN.compare&swap(sn-1, sn)`. -/
  | wHelp (sn : ℕ)
  /-- Writer, about to return. -/
  | wRet
  /-- Auditor, idle: audit set `A` and `lsa`. -/
  | aIdle (A : Set (Fin m × V)) (lsa : ℕ)
  /-- Auditor, line 17: about to read `R`. -/
  | aR (A : Set (Fin m × V)) (lsa : ℕ)
  /-- Auditor, line 19: read `r` from `R`, about to read `V[s]` (`lsa ≤ s < r.seq`). -/
  | aV (A : Set (Fin m × V)) (r : RVal m V) (s : ℕ)
  /-- Auditor, line 20: read `val` from `V[s]`, about to read `B[s][j]`. -/
  | aB (A : Set (Fin m × V)) (r : RVal m V) (s : ℕ) (val : Option V) (j : Fin m)
  /-- Auditor, line 22: about to apply `SN.compare&swap(r.seq-1, r.seq)`. -/
  | aCAS (A : Set (Fin m × V)) (r : RVal m V)
  /-- Auditor, about to return `A`; then `lsa = r.seq`. -/
  | aRet (A : Set (Fin m × V)) (lsa : ℕ)

variable {m W Au V}

section Defs

variable [DecidableEq V] (rnd : ℕ → Fin m → Bool)

/-- The readers recorded in `r.bits` (deciphered with `rand_{r.seq}`). -/
def readersOf (r : RVal m V) (j : Fin m) : Prop := r.bits j ≠ rnd r.seq j

/-- Line 13: the readers to be recorded in `B[r.seq]`. -/
def todoOf (r : RVal m V) : List (Fin m) :=
  (List.finRange m).filter (fun j => r.bits j ≠ rnd r.seq j)

/-- Line 21: the pairs contributed by the tracking bits. -/
def bitPairs (r : RVal m V) : Set (Fin m × V) := {x | r.bits x.1 ≠ rnd r.seq x.1 ∧ x.2 = r.val}

/-- Next writer state in the loop of line 13. -/
def wBnext (v : V) (sn : ℕ) (r : RVal m V) : List (Fin m) → Loc m V
  | [] => .wCAS v sn r
  | todo => .wB v sn r todo

/-- Next auditor state in the loop of line 18. -/
def aNext (A : Set (Fin m × V)) (r : RVal m V) (s : ℕ) : Loc m V :=
  if s < r.seq then .aV A r s else .aCAS (A ∪ bitPairs rnd r) r

/-- Add `(j, val)` to `A` if `b` (line 20). -/
def addPair (A : Set (Fin m × V)) (j : Fin m) (val : Option V) (b : Bool) : Set (Fin m × V) :=
  match b, val with
  | true, some v => insert (j, v) A
  | _, _ => A

/-- Next auditor state after reading `B[s][j]`. -/
def aBnext (A : Set (Fin m × V)) (r : RVal m V) (s : ℕ) (val : Option V) (j : Fin m) :
    Loc m V :=
  if h : j.val + 1 < m then .aB A r s val ⟨j.val + 1, h⟩ else aNext rnd A r (s + 1)

/-- Next auditor state after reading `V[s]`. -/
def aVnext (A : Set (Fin m × V)) (r : RVal m V) (s : ℕ) (val : Option V) : Loc m V :=
  if h : 0 < m then .aB A r s val ⟨0, h⟩ else aNext rnd A r (s + 1)

variable (v₀ : V)

/-- The actions of a reader (lines 1–6). -/
def readerAct (j : Fin m) : Loc m V → Action (auditReg m V v₀) (BO m V v₀) (Loc m V)
  | .rSN prev => .access Obj.SN CASOp.read (fun x => match x with
      | .inl y => if prev.map Prod.fst = some y then
          (match prev with | some (_, pv) => .rRet prev pv | none => .rFX prev y)
        else .rFX prev y
      | .inr _ => .rFX prev 0)
  | .rFX prev _ => .access Obj.R (ROp.fx j) (fun x => match x with
      | .inl r => .rCAS prev r.seq r.val
      | .inr _ => .rIdle prev)
  | .rCAS _ sn val => .access Obj.SN (CASOp.cas (sn - 1) sn) (fun _ => .rRet (some (sn, val)) val)
  | .rRet prev val => .ret (.val val) (.rIdle prev)
  | l => .ret .ack l

/-- The actions of a writer (lines 7–15). -/
def writerAct : Loc m V → Action (auditReg m V v₀) (BO m V v₀) (Loc m V)
  | .wSN v => .access Obj.SN CASOp.read (fun x => match x with
      | .inl y => .wR v (y + 1)
      | .inr _ => .wR v 0)
  | .wR v sn => .access Obj.R ROp.read (fun x => match x with
      | .inl r => if sn ≤ r.seq then .wHelp sn else .wV v sn r
      | .inr _ => .wR v sn)
  | .wV v sn r => .access (Obj.V r.seq) (RWOp.write (some r.val))
      (fun _ => wBnext v sn r (todoOf rnd r))
  | .wB v sn r todo => match todo with
      | j :: rest => .access (Obj.B r.seq j) (RWOp.write true) (fun _ => wBnext v sn r rest)
      | [] => .ret .ack (.wCAS v sn r)
  | .wCAS v sn r => .access Obj.R (ROp.cas r ⟨sn, v, rnd sn⟩) (fun x => match x with
      | .inr true => .wHelp sn
      | _ => .wR v sn)
  | .wHelp sn => .access Obj.SN (CASOp.cas (sn - 1) sn) (fun _ => .wRet)
  | .wRet => .ret .ack .wIdle
  | l => .ret .ack l

/-- The actions of an auditor (lines 16–22). -/
def auditorAct : Loc m V → Action (auditReg m V v₀) (BO m V v₀) (Loc m V)
  | .aR A lsa => .access Obj.R ROp.read (fun x => match x with
      | .inl r => aNext rnd A r lsa
      | .inr _ => .aR A lsa)
  | .aV A r s => .access (Obj.V s) RWOp.read (fun val => aVnext rnd A r s val)
  | .aB A r s val j => .access (Obj.B s j) RWOp.read
      (fun b => aBnext rnd (addPair A j val b) r s val j)
  | .aCAS A r => .access Obj.SN (CASOp.cas (r.seq - 1) r.seq) (fun _ => .aRet A r.seq)
  | .aRet A lsa => .ret (.set A) (.aIdle A lsa)
  | l => .ret .ack l

/-- Initial local states. -/
def locInit : Proc m W Au → Loc m V
  | .rd _ => .rIdle none
  | .wr _ => .wIdle
  | .au _ => .aIdle ∅ 0

/-- Invocations. -/
def invoke : Proc m W Au → Loc m V → AOp m V → Loc m V
  | .rd _, .rIdle prev, .read _ => .rSN prev
  | .wr _, .wIdle, .write v => .wSN v
  | .au _, .aIdle A lsa, .audit => .aR A lsa
  | _, l, _ => l

/-- Which operations a process may invoke. -/
def allowed : Proc m W Au → AOp m V → Prop
  | .rd j, .read j' => j' = j
  | .wr _, .write _ => True
  | .au _, .audit => True
  | _, _ => False

/-- Algorithm 1 with one-time pads `rnd`. -/
def alg1 : Impl (auditReg m V v₀) (BO m V v₀) (Proc m W Au) (Loc m V) where
  memInit
    | .R => (⟨0, v₀, rnd 0⟩ : RVal m V)
    | .SN => (0 : ℕ)
    | .V _ => (none : Option V)
    | .B _ _ => false
  locInit := locInit
  invoke := invoke
  act
    | .rd j, l => readerAct v₀ j l
    | .wr _, l => writerAct rnd v₀ l
    | .au _, l => auditorAct rnd v₀ l
  allowed := allowed

end Defs

end Podc.AuditingWithoutLeaks
