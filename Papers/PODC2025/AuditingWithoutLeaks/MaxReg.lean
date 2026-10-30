import Papers.PODC2025.AuditingWithoutLeaks.Alg1
import Mathlib.Order.Prod.Lex.Basic

/-!
# Algorithm 2: an auditable max register

Attiya, Fernández Anta, Milani, Rapetti, Travers, *Auditing without Leaks Despite Curiosity*,
PODC 2025, Section 4, Algorithm 2, in CSLib's asynchronous shared-memory model
(`Cslib.SharedMemory.Impl`), following the model of Algorithm 1 in `Alg1.lean`.

* Values are natural numbers, nonces are natural numbers, and a *pair* `(w, N)` is an element of
  `ℕ ×ₗ ℕ` (lexicographic order, as in the paper). The initial pair is `v₀ = (w₀, N₀) = (0, 0)`
  (`= ⊥`), stored initially in `R` and in `M`.
* Processes: readers `rd j` (`j : Fin m`), writers `wr x` (`x : W`), auditors `au a` (`a : Au`).
* The implemented object `amaxReg m`: a max register over `ℕ` whose `read j` also records the pair
  `(j, value)` and whose `audit` returns the recorded pairs.
* Base objects: `R` (triples `(seq, pair, bits)`, as in Alg. 1), `SN`, `V[s]` (registers over
  `Option ℕ`: line 32 stores the value component), `B[s][j]`, and the max register `M` of pairs.
* Randomness (`Coins`): the one-time pads `rnd : ℕ → Fin m → Bool` (known to writers and auditors)
  and the nonces `nc : W → ℕ → ℕ` (`nc x k` = nonce drawn by writer `x` in its `k`-th
  `writeMax`, line 23). The algorithm is the family `alg2 θ`, `θ : Coins m W`.
* Read and audit are the code of Alg. 1 (line 21), with values replaced by pairs and the nonce
  dropped when a value is returned or recorded. Audit sets are `Finset`s (so that executions can be
  evaluated by `decide`).
* `continue` at line 30 restarts the loop body at line 26 (the evident intent: the `until`
  condition at line 34 refers to `mval`, which is not yet defined in the first iteration).

Each step of a process applies exactly one primitive; the `for each` loops (lines 33, 18–20) are
unfolded into one step per register access.
-/

namespace Podc.AuditingWithoutLeaks.MaxReg

open Cslib.SharedMemory

/-- Pairs `(value, nonce)` ordered lexicographically. -/
abbrev Pr := ℕ ×ₗ ℕ

/-- The initial pair `v₀ = (w₀, N₀) = (0, 0)`. -/
abbrev v₀ : Pr := toLex (0, 0)

/-- The value component of a pair. -/
abbrev Pr.val (v : Pr) : ℕ := (ofLex v).1

/-- The nonce component of a pair. -/
abbrev Pr.nonce (v : Pr) : ℕ := (ofLex v).2

variable (m : ℕ) (W Au : Type)

/-- Operations of an auditable max register (the reader's identity is an argument of `read`). -/
inductive MOp where
  | read (j : Fin m)
  | writeMax (w : ℕ)
  | audit
  deriving DecidableEq

/-- Responses of an auditable max register. -/
inductive MResp where
  | val (w : ℕ)
  | ack
  | set (S : Finset (Fin m × ℕ))
  deriving DecidableEq

/-- Sequential specification of an auditable max register (initial value `w₀ = 0`): a read by
`j` returns the largest value written so far and records `(j, value)`; an audit returns the
recorded pairs. -/
abbrev amaxReg : ObjSpec where
  State := ℕ × Finset (Fin m × ℕ)
  Op := MOp m
  Resp := MResp m
  init := (0, ∅)
  δ q o := match o with
    | .read j => ((q.1, insert (j, q.1) q.2), .val q.1)
    | .writeMax w => ((max q.1 w, q.2), .ack)
    | .audit => (q, .set q.2)

instance : DecidableEq (amaxReg m).Resp := inferInstanceAs (DecidableEq (MResp m))

instance : DecidableEq (amaxReg m).Op := inferInstanceAs (DecidableEq (MOp m))

/-- Primitives of the (non-auditable) max register `M` of pairs. -/
inductive MaxOp where
  | read
  | writeMax (v : Pr)

/-- The base max register `M` over pairs; `writeMax` returns a dummy response. -/
abbrev maxRegPr : ObjSpec where
  State := Pr
  Op := MaxOp
  Resp := Pr
  init := v₀
  δ q o := match o with
    | .read => (q, q)
    | .writeMax v => (max q v, v)

/-- Names of base objects. -/
inductive MObj where
  | R
  | SN
  | V (s : ℕ)
  | B (s : ℕ) (j : Fin m)
  | M
  deriving DecidableEq

/-- Specifications of the base objects (`ObjSpec.init` is ignored by CSLib; the initial memory is
`Impl.memInit`). -/
abbrev MBO : MObj m → ObjSpec
  | .R => rObj m Pr ⟨0, v₀, fun _ => false⟩
  | .SN => casObject ℕ 0
  | .V _ => register (Option ℕ) none
  | .B _ _ => register Bool false
  | .M => maxRegPr

/-- Local states (program counters with the local variables in use). Writers carry the number
`k` of their completed `writeMax` operations (to index their nonces). -/
inductive MLoc where
  /-- Reader, idle; `prev` = `(prev_sn, prev_val)` (`none` initially). -/
  | rIdle (prev : Option (ℕ × ℕ))
  /-- Reader, line 2: about to read `SN`. -/
  | rSN (prev : Option (ℕ × ℕ))
  /-- Reader, line 4: has read `y ≠ prev_sn` from `SN`, about to apply fetch&xor to `R`. -/
  | rFX (prev : Option (ℕ × ℕ)) (y : ℕ)
  /-- Reader, line 5: fetched `(sn, val, _)`, about to apply `SN.compare&swap(sn-1, sn)`. -/
  | rCAS (prev : Option (ℕ × ℕ)) (sn : ℕ) (val : ℕ)
  /-- Reader, about to return `val`. -/
  | rRet (prev : Option (ℕ × ℕ)) (val : ℕ)
  /-- Writer, idle. -/
  | wIdle (k : ℕ)
  /-- Writer, line 24: about to apply `M.writeMax(v)`. -/
  | wM (k : ℕ) (v : Pr)
  /-- Writer, lines 24 and 30: about to read `SN` (then `sn ← SN.read() + 1`). -/
  | wSN (k : ℕ) (v : Pr)
  /-- Writer, line 26: about to read `R`. -/
  | wR (k : ℕ) (v : Pr) (sn : ℕ)
  /-- Writer, line 29: about to apply `SN.compare&swap(sn-1, sn)`, then line 30. -/
  | wHelpL (k : ℕ) (v : Pr) (sn : ℕ)
  /-- Writer, line 31: read `r` from `R`, about to read `M`. -/
  | wMR (k : ℕ) (v : Pr) (sn : ℕ) (r : RVal m Pr)
  /-- Writer, line 32: about to write `V[r.seq]`. -/
  | wV (k : ℕ) (v : Pr) (sn : ℕ) (r : RVal m Pr) (mval : Pr)
  /-- Writer, line 33: about to write `true` to `B[r.seq][j]` for the first `j` of `todo`. -/
  | wB (k : ℕ) (v : Pr) (sn : ℕ) (r : RVal m Pr) (mval : Pr) (todo : List (Fin m))
  /-- Writer, line 34: about to apply `R.compare&swap(r, (sn, mval, rand_sn))`. -/
  | wCAS (k : ℕ) (v : Pr) (sn : ℕ) (r : RVal m Pr) (mval : Pr)
  /-- Writer, line 35: about to apply `SN.compare&swap(sn-1, sn)`. -/
  | wHelp (k : ℕ) (sn : ℕ)
  /-- Writer, about to return. -/
  | wRet (k : ℕ)
  /-- Auditor, idle: audit set `A` and `lsa`. -/
  | aIdle (A : Finset (Fin m × ℕ)) (lsa : ℕ)
  /-- Auditor, line 17: about to read `R`. -/
  | aR (A : Finset (Fin m × ℕ)) (lsa : ℕ)
  /-- Auditor, line 19: read `r` from `R`, about to read `V[s]`. -/
  | aV (A : Finset (Fin m × ℕ)) (r : RVal m Pr) (s : ℕ)
  /-- Auditor, line 20: read `val` from `V[s]`, about to read `B[s][j]`. -/
  | aB (A : Finset (Fin m × ℕ)) (r : RVal m Pr) (s : ℕ) (val : Option ℕ) (j : Fin m)
  /-- Auditor, line 22: about to apply `SN.compare&swap(r.seq-1, r.seq)`. -/
  | aCAS (A : Finset (Fin m × ℕ)) (r : RVal m Pr)
  /-- Auditor, about to return `A`. -/
  | aRet (A : Finset (Fin m × ℕ)) (lsa : ℕ)
  deriving DecidableEq

/-- The random choices of Algorithm 2: one-time pads and nonces. -/
structure Coins where
  /-- `rnd s` = the pad `rand_s`. -/
  rnd : ℕ → Fin m → Bool
  /-- `nc x k` = the nonce `N` drawn by writer `x` in its `k`-th `writeMax` (line 23). -/
  nc : W → ℕ → ℕ

variable {m W Au}

section Defs

variable (rnd : ℕ → Fin m → Bool)

/-- Line 21 (Alg. 1, line 21): the pairs contributed by the tracking bits (nonce dropped). -/
def bitPairs (r : RVal m Pr) : Finset (Fin m × ℕ) :=
  (Finset.univ.filter (fun j => r.bits j ≠ rnd r.seq j)).image (fun j => (j, r.val.val))

/-- Next writer state in the loop of line 33. -/
def wBnext (k : ℕ) (v : Pr) (sn : ℕ) (r : RVal m Pr) (mval : Pr) : List (Fin m) → MLoc m
  | [] => .wCAS k v sn r mval
  | todo => .wB k v sn r mval todo

/-- Next auditor state in the loop of line 18. -/
def aNext (A : Finset (Fin m × ℕ)) (r : RVal m Pr) (s : ℕ) : MLoc m :=
  if s < r.seq then .aV A r s else .aCAS (A ∪ bitPairs rnd r) r

/-- Add `(j, val)` to `A` if `b` (line 20). -/
def addPair (A : Finset (Fin m × ℕ)) (j : Fin m) (val : Option ℕ) (b : Bool) :
    Finset (Fin m × ℕ) :=
  match b, val with
  | true, some v => insert (j, v) A
  | _, _ => A

/-- Next auditor state after reading `B[s][j]`. -/
def aBnext (A : Finset (Fin m × ℕ)) (r : RVal m Pr) (s : ℕ) (val : Option ℕ) (j : Fin m) :
    MLoc m :=
  if h : j.val + 1 < m then .aB A r s val ⟨j.val + 1, h⟩ else aNext rnd A r (s + 1)

/-- Next auditor state after reading `V[s]`. -/
def aVnext (A : Finset (Fin m × ℕ)) (r : RVal m Pr) (s : ℕ) (val : Option ℕ) : MLoc m :=
  if h : 0 < m then .aB A r s val ⟨0, h⟩ else aNext rnd A r (s + 1)

/-- The actions of a reader (Alg. 1, lines 1–6; the nonce is dropped from the fetched pair). -/
def readerAct (j : Fin m) : MLoc m → Action (amaxReg m) (MBO m) (MLoc m)
  | .rSN prev => .access MObj.SN CASOp.read (fun x => match x with
      | .inl y => if prev.map Prod.fst = some y then
          (match prev with | some (_, pv) => .rRet prev pv | none => .rFX prev y)
        else .rFX prev y
      | .inr _ => .rFX prev 0)
  | .rFX prev _ => .access MObj.R (ROp.fx j) (fun x => match x with
      | .inl r => .rCAS prev r.seq r.val.val
      | .inr _ => .rIdle prev)
  | .rCAS _ sn val => .access MObj.SN (CASOp.cas (sn - 1) sn)
      (fun _ => .rRet (some (sn, val)) val)
  | .rRet prev val => .ret (.val val) (.rIdle prev)
  | l => .ret .ack l

/-- The actions of a writer (Alg. 2, lines 22–35). -/
def writerAct : MLoc m → Action (amaxReg m) (MBO m) (MLoc m)
  | .wM k v => .access MObj.M (MaxOp.writeMax v) (fun _ => .wSN k v)
  | .wSN k v => .access MObj.SN CASOp.read (fun x => match x with
      | .inl y => .wR k v (y + 1)
      | .inr _ => .wR k v 0)
  | .wR k v sn => .access MObj.R ROp.read (fun x => match x with
      | .inl r => if v ≤ r.val then .wHelp k r.seq
        else if sn ≤ r.seq then .wHelpL k v sn
        else .wMR k v sn r
      | .inr _ => .wR k v sn)
  | .wHelpL k v sn => .access MObj.SN (CASOp.cas (sn - 1) sn) (fun _ => .wSN k v)
  | .wMR k v sn r => .access MObj.M MaxOp.read (fun mval => .wV k v sn r mval)
  | .wV k v sn r mval => .access (MObj.V r.seq) (RWOp.write (some r.val.val))
      (fun _ => wBnext k v sn r mval (todoOf rnd r))
  | .wB k v sn r mval todo => match todo with
      | j :: rest => .access (MObj.B r.seq j) (RWOp.write true)
          (fun _ => wBnext k v sn r mval rest)
      | [] => .ret .ack (.wCAS k v sn r mval)
  | .wCAS k v sn r mval => .access MObj.R (ROp.cas r ⟨sn, mval, rnd sn⟩) (fun x => match x with
      | .inr true => .wHelp k sn
      | _ => .wR k v sn)
  | .wHelp k sn => .access MObj.SN (CASOp.cas (sn - 1) sn) (fun _ => .wRet k)
  | .wRet k => .ret .ack (.wIdle (k + 1))
  | l => .ret .ack l

/-- The actions of an auditor (Alg. 1, lines 16–22). -/
def auditorAct : MLoc m → Action (amaxReg m) (MBO m) (MLoc m)
  | .aR A lsa => .access MObj.R ROp.read (fun x => match x with
      | .inl r => aNext rnd A r lsa
      | .inr _ => .aR A lsa)
  | .aV A r s => .access (MObj.V s) RWOp.read (fun val => aVnext rnd A r s val)
  | .aB A r s val j => .access (MObj.B s j) RWOp.read
      (fun b => aBnext rnd (addPair A j val b) r s val j)
  | .aCAS A r => .access MObj.SN (CASOp.cas (r.seq - 1) r.seq) (fun _ => .aRet A r.seq)
  | .aRet A lsa => .ret (.set A) (.aIdle A lsa)
  | l => .ret .ack l

end Defs

/-- Initial local states. -/
def locInit : Proc m W Au → MLoc m
  | .rd _ => .rIdle none
  | .wr _ => .wIdle 0
  | .au _ => .aIdle ∅ 0

/-- Invocations; a writer draws its nonce at invocation (line 23). -/
def invoke (nc : W → ℕ → ℕ) : Proc m W Au → MLoc m → MOp m → MLoc m
  | .rd _, .rIdle prev, .read _ => .rSN prev
  | .wr x, .wIdle k, .writeMax w => .wM k (toLex (w, nc x k))
  | .au _, .aIdle A lsa, .audit => .aR A lsa
  | _, l, _ => l

/-- Which operations a process may invoke. -/
def allowed : Proc m W Au → MOp m → Prop
  | .rd j, .read j' => j' = j
  | .wr _, .writeMax _ => True
  | .au _, .audit => True
  | _, _ => False

instance decAllowed (p : Proc m W Au) (o : MOp m) : Decidable (allowed p o) := by
  cases p <;> cases o <;> simp only [allowed] <;> infer_instance

/-- Algorithm 2 with random choices `θ` (pads and nonces). -/
def alg2 (θ : Coins m W) : Impl (amaxReg m) (MBO m) (Proc m W Au) (MLoc m) where
  memInit
    | .R => (⟨0, v₀, θ.rnd 0⟩ : RVal m Pr)
    | .SN => (0 : ℕ)
    | .V _ => (none : Option ℕ)
    | .B _ _ => false
    | .M => v₀
  locInit := locInit
  invoke := invoke θ.nc
  act
    | .rd j, l => readerAct j l
    | .wr _, l => writerAct θ.rnd l
    | .au _, l => auditorAct θ.rnd l
  allowed := allowed

instance (θ : Coins m W) (p : Proc m W Au) (o : (amaxReg m).Op) :
    Decidable ((alg2 θ).allowed p o) := decAllowed p o

end Podc.AuditingWithoutLeaks.MaxReg
