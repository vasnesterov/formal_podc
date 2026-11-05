import Papers.PODC2020.StoreCollectChurn.Spec
import Cslib.Computability.Distributed.SharedMemory.History

/-!
# Algorithm 7 (atomic snapshot from store-collect), Section 6.2 of the paper

We model Algorithm 7 on top of an **abstract** store-collect object: the only assumption on the
object is that the schedule of its invocations and responses satisfies `Regular` (Section 2,
`Spec.lean`).  This is exactly what the paper's proof uses ("The regularity of store-collect
ensures …").

* Nodes `P` (any type: under churn there may be infinitely many), snapshot values `V`.
* A store-collect value (`SCVal`) is the 5-tuple `⟨val, usqno, ssqno, sview, scounts⟩` of the
  paper (`ValSC = Val_AS × ℕ × ℕ × 𝒫(Π × Val_AS) × 𝒫(Π × ℕ)`); a snapshot view and the set
  `scounts` (pairs without duplicate node ids) are partial functions.
* An execution is a list of events `Ev`: high-level invocations/responses of `SCAN`/`UPDATE` and
  low-level store-collect events.  Every node runs the code of Algorithm 7 as a deterministic
  automaton (`lstep`); the environment chooses the interleaving and the views returned by
  collects.  The choice of `q` at Line 77 ("if ∃ q such that …") is an arbitrary choice
  function `Pick` (any rule is allowed).
* Line 71 stores `⟨−, −, ssqno, −, −⟩`, "with all the other components unchanged": we read the
  `−` components as those of the value the node stored last (`stored`).  With the other reading
  (the current local variables, where `scounts` was already overwritten at Line 79 of an
  enclosing `UPDATE`) the algorithm is not linearizable: see `differencies.md`.
-/

namespace Podc.StoreCollectChurn.Snap

open Cslib.SharedMemory

variable (P V : Type)

/-- Values stored in the store-collect object (`Val_SC` of Section 6.2). -/
structure SCVal where
  /-- argument of the most recent update (`⊥` = `none`) -/
  val : Option V
  /-- number of updates performed -/
  usqno : ℕ
  /-- number of scans performed -/
  ssqno : ℕ
  /-- snapshot view of a recent (embedded) scan -/
  sview : P → Option V
  /-- scan counts of other nodes as observed (pairs `⟨q, n⟩` ↦ `scounts q = some n`) -/
  scounts : P → Option ℕ

/-- Store-collect views. -/
abbrev SCView := P → Option (SCVal P V)

/-- High-level operations of node `p`. -/
inductive HOp where
  | scan
  | update (v : V)

/-- Events of an execution of Algorithm 7. -/
inductive Ev where
  /-- invocation of `SCAN()` / `UPDATE(v)` at `p` -/
  | hinv (p : P) (o : HOp V)
  /-- response at `p` (a snapshot view; `UPDATE` answers the empty view as `ACK`) -/
  | hret (p : P) (r : P → Option V)
  /-- an invocation or response of the underlying store-collect object -/
  | sc (e : SCEv P (SCVal P V))

variable {P V}

/-- The node of an event. -/
def Ev.proc : Ev P V → P
  | .hinv p _ => p
  | .hret p _ => p
  | .sc e => e.proc

/-- The store-collect part of an event. -/
def Ev.scOf : Ev P V → Option (SCEv P (SCVal P V))
  | .sc e => some e
  | _ => none

/-! ## Notation of Section 6.2 -/

/-- `r(V).usqno`: update sequence numbers of the entries with a real value. -/
def rU (W : SCView P V) (r : P) : Option ℕ := (W r).bind fun x => x.val.map fun _ => x.usqno

/-- `r(V).val`: the snapshot view made of the real values of a store-collect view. -/
def rVal (W : SCView P V) (r : P) : Option V := (W r).bind (·.val)

/-- `V.ssqno`: the scan sequence numbers of a store-collect view (Line 79). -/
def ssqVec (W : SCView P V) : P → Option ℕ := fun r => (W r).map (·.ssqno)

/-- The borrowed view `V₁(q).sview` (Line 78). -/
def sviewOf (W : SCView P V) (q : P) : P → Option V := ((W q).map (·.sview)).getD fun _ => none

/-! ## The automaton of a node -/

/-- Program counter of Algorithm 7.  `emb = some v`: the scan is embedded in `UPDATE(v)`. -/
inductive PC where
  /-- no pending operation -/
  | idle
  /-- next: Line 71 `STORE` -/
  | scStore (emb : Option V)
  /-- waiting for the `ACK` of Line 71 -/
  | scStoreW (emb : Option V)
  /-- next: Line 72 `COLLECT` -/
  | scCol1 (emb : Option V)
  /-- waiting for a collect of Line 72 (`first`) or Line 74 -/
  | scColW (emb : Option V) (first : Bool)
  /-- next: Line 74 `COLLECT` -/
  | scColN (emb : Option V)
  /-- a free-standing scan has decided `W`; next: return it -/
  | scRet (W : P → Option V)
  /-- next: Line 79 `COLLECT` of `UPDATE(v)` -/
  | upCol (v : V)
  /-- waiting for the collect of Line 79 -/
  | upColW (v : V)
  /-- next: Line 83 `STORE` -/
  | upStore
  /-- waiting for the `ACK` of Line 83 -/
  | upStoreW
  /-- next: return `ACK` (Line 84) -/
  | upRet

/-- Local state of a node (the local variables of Algorithm 7 plus `stored`, the value it stored
last, whose components the `−` of Line 71 refers to). -/
structure LState (P V : Type) where
  pc : PC (P := P) (V := V)
  ssqno : ℕ
  scounts : P → Option ℕ
  val : Option V
  usqno : ℕ
  sview : P → Option V
  V1 : SCView P V
  stored : SCVal P V

/-- Initial local state. -/
def LState.init : LState P V where
  pc := .idle
  ssqno := 0
  scounts := fun _ => none
  val := none
  usqno := 0
  sview := fun _ => none
  V1 := fun _ => none
  stored := ⟨none, 0, 0, fun _ => none, fun _ => none⟩

/-- The choice at Line 77: any rule returning some `q` with `⟨p, ssqno⟩ ∈ V₁(q).scounts`
whenever such a `q` exists. -/
structure Pick (P V : Type) where
  f : SCView P V → P → ℕ → Option P
  spec : ∀ W p s q, f W p s = some q → ∃ x, W q = some x ∧ x.scounts p = some s
  total : ∀ W p s q x, W q = some x → x.scounts p = some s → f W p s ≠ none

/-- End of a scan returning `W`: a free-standing scan returns it (Line 76/78); an embedded scan
continues with Lines 80–82 (`sview = W; val = v; usqno++`). -/
def finishScan (s : LState P V) (emb : Option V) (W : P → Option V) : LState P V :=
  match emb with
  | none => { s with pc := .scRet W }
  | some v => { s with pc := .upStore, sview := W, val := some v, usqno := s.usqno + 1 }

open Classical in
/-- One step of node `p` on its event `e` (`none` = the event is not allowed by the code). -/
noncomputable def lstep (pk : Pick P V) (p : P) (s : LState P V) (e : Ev P V) :
    Option (LState P V) :=
  match s.pc, e with
  -- Line 70
  | .idle, .hinv _ .scan => some { s with pc := .scStore none, ssqno := s.ssqno + 1 }
  | .idle, .hinv _ (.update v) => some { s with pc := .upCol v }
  -- Line 71: `STORE_p(⟨−, −, ssqno, −, −⟩)`
  | .scStore emb, .sc (.stInv _ x) =>
      if x = { s.stored with ssqno := s.ssqno } then some { s with pc := .scStoreW emb, stored := x }
      else none
  -- Line 83: `STORE_p(⟨val, usqno, −, sview, scounts⟩)`
  | .upStore, .sc (.stInv _ x) =>
      if x = ⟨s.val, s.usqno, s.ssqno, s.sview, s.scounts⟩ then
        some { s with pc := .upStoreW, stored := x }
      else none
  | .scStoreW emb, .sc (.ack _) => some { s with pc := .scCol1 emb }
  | .upStoreW, .sc (.ack _) => some { s with pc := .upRet }
  -- Lines 72, 74, 79: invocations of `COLLECT`
  | .scCol1 emb, .sc (.colInv _) => some { s with pc := .scColW emb true }
  | .scColN emb, .sc (.colInv _) => some { s with pc := .scColW emb false }
  | .upCol v, .sc (.colInv _) => some { s with pc := .upColW v }
  -- Line 79 returns, then Line 80 starts the embedded scan (Line 70)
  | .upColW v, .sc (.ret _ W) =>
      some { s with pc := .scStore (some v), scounts := ssqVec W, ssqno := s.ssqno + 1 }
  -- Line 72 returns
  | .scColW emb true, .sc (.ret _ W) => some { s with pc := .scColN emb, V1 := W }
  -- Line 74 returns; Lines 75–78
  | .scColW emb false, .sc (.ret _ W) =>
      if ∀ r, rU W r = rU s.V1 r then some (finishScan { s with V1 := W } emb (rVal W))
      else match pk.f W p s.ssqno with
        | some q => some (finishScan { s with V1 := W } emb (sviewOf W q))
        | none => some { s with pc := .scColN emb, V1 := W }
  | .scRet W, .hret _ r => if r = W then some { s with pc := .idle } else none
  | .upRet, .hret _ r => if r = (fun _ => none) then some { s with pc := .idle } else none
  | _, _ => none

variable [DecidableEq P]

/-- Configurations: the local states of all nodes. -/
abbrev Cfg (P V : Type) := P → LState P V

/-- One global step: the node of the event takes its local step. -/
noncomputable def gstep (pk : Pick P V) (c : Cfg P V) (e : Ev P V) : Option (Cfg P V) :=
  (lstep pk e.proc (c e.proc) e).map (Function.update c e.proc)

/-- Run an execution from the initial configuration (`none` if some event is not allowed). -/
noncomputable def run (pk : Pick P V) (E : List (Ev P V)) : Option (Cfg P V) :=
  E.foldl (fun c e => c.bind (gstep pk · e)) (some fun _ => LState.init)

/-- The schedule of the underlying store-collect object. -/
def scSched (E : List (Ev P V)) : List (SCEv P (SCVal P V)) := E.filterMap Ev.scOf

/-! ## The implemented object: an atomic snapshot -/

/-- Snapshot operations as seen by the sequential specification (the updating node is part of
the operation, since a sequential specification does not see the caller). -/
inductive SnapOp (P V : Type) where
  | scan
  | update (p : P) (v : V)

instance : Inhabited (SnapOp P V) := ⟨.scan⟩

/-- Sequential specification of an atomic snapshot over nodes `P` (Section 6.2): a scan returns,
for each node, the value of its last preceding update (`none` if there is none). -/
abbrev snapSpec (P V : Type) [DecidableEq P] : ObjSpec where
  State := P → Option V
  Op := SnapOp P V
  Resp := P → Option V
  init := fun _ => none
  δ q o := match o with
    | .scan => (q, q)
    | .update p v => (Function.update q p (some v), fun _ => none)

/-- The high-level history of an execution (store-collect events become internal steps). -/
def Ev.toLabel : Ev P V → Label P (snapSpec P V)
  | .hinv p .scan => .inv p .scan
  | .hinv p (.update v) => .inv p (.update p v)
  | .hret p r => .ret p r
  | .sc e => .tau e.proc

/-- The high-level history of an execution. -/
def hist (E : List (Ev P V)) : List (Label P (snapSpec P V)) := E.map Ev.toLabel

end Podc.StoreCollectChurn.Snap
