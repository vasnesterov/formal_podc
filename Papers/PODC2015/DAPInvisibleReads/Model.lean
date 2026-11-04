import Cslib.Computability.Distributed.SharedMemory.Covering
import Mathlib.Logic.Relation
import Mathlib.Data.Set.Basic

-- CSLib candidate: Cslib/Computability/Distributed/SharedMemory/Transactional/Basic.lean

/-!
# Transactional memory on top of the asynchronous shared-memory model

Peluso, Palmieri, Romano, Ravindran, Quaglia. *Disjoint-Access Parallelism: Impossibility,
Possibility, and Cost of Transactional Memory Implementations.* PODC 2015 (technical report,
Virginia Tech, May 2015), Section 2.

A **TM implementation** is an implementation (`Cslib.SharedMemory.Impl`) of the transactional
interface `tmSpec X V` from arbitrary base objects `B : ι → ObjSpec`: processes are deterministic
programs, every step applies one primitive to one base object, the environment chooses the
invocations, and the scheduler is arbitrary (finite executions model crashes: a crashed process
simply takes no more steps).

* **Interface.** Operations `read x`, `write x v`, `tryC` (`TOp`). A response is an `Option V`:
  `none` is the abort event, `some v` a successful response (the value read for a read; the value
  is ignored for writes and `tryC`). As in Guerraoui–Kapałka, a transaction begins implicitly with
  its first invocation (the paper's `begin` operation would only add a step that does nothing).
* **Transactions** are computed per process from the history (`pstate`): an operation that is
  aborted, or a `tryC` that returns successfully, ends the current transaction; `(p, k)` is the
  `k`-th transaction of `p` (`TxId`). `txRec h T` is its record (completed operations with their
  responses, and the pending operation).
* **Histories and the DSG** (Section 2): versions of `x` are the initial version (`none`, value
  `v₀ x`) and the versions of the committed transactions that wrote `x`, ordered by commit time;
  direct read-, write- and anti-dependence edges (`wr`, `ww`, `rw`); the real-time order `RTO` and
  the *witnessable* real-time order `WRTO` (RTO between transactions joined by a direct edge), and
  the paper's notions "`H` preserves RTO / WRTO".
* **Properties of TM implementations** used in Section 3: weak disjoint-access parallelism
  (`WDAP`), obstruction-free write transactions (`ObstructionFreeWrites`), write transactions that
  commit when run in isolation (`IsolatedWritesCommit`, implied by weak progressiveness),
  wait-free read-only transactions (`WaitFreeReadOnly`), invisible read-only transactions
  (`InvisibleReads`) and the standing assumption that a read returns the initial value or a value
  some write has written (`LegalReads`).
-/

namespace Podc.DAPInvisibleReads

open Cslib.SharedMemory

/-! ### The transactional interface -/

/-- Transactional operations. -/
inductive TOp (X V : Type) where
  | read (x : X)
  | write (x : X) (v : V)
  | tryC
  deriving DecidableEq

namespace TOp

variable {X V : Type}

/-- The transactional object accessed by an operation. -/
def obj : TOp X V → Option X
  | read x => some x
  | write x _ => some x
  | tryC => none

/-- Whether the operation is a write. -/
def IsWrite : TOp X V → Prop
  | write _ _ => True
  | _ => False

end TOp

/-- The transactional interface as an `ObjSpec`. Only `Op` and `Resp` matter: TM correctness is
not linearizability, so the sequential specification is a dummy. A response `none` is an abort
event; `some v` is a successful response (`v` is the value read by a read). -/
abbrev tmSpec (X V : Type) : ObjSpec where
  State := Unit
  Op := TOp X V
  Resp := Option V
  init := ()
  δ := fun _ _ => ((), none)

variable {X V P : Type}

/-- Labels of executions of a TM. -/
abbrev Lbl (P X V : Type) := Label P (tmSpec X V)

/-! ### Transactions of a history -/

/-- The record of one transaction: its completed operations (with responses), in order, and its
pending operation. -/
structure TxRec (X V : Type) where
  ops : List (TOp X V × Option V)
  pend : Option (TOp X V)
  deriving DecidableEq

/-- The empty record. -/
def TxRec.empty : TxRec X V := ⟨[], none⟩

/-- An operation with this response ends the transaction: an abort, or a successful `tryC`. -/
def endsTx : TOp X V → Option V → Bool
  | _, none => true
  | .tryC, some _ => true
  | _, _ => false

/-- Per-process bookkeeping: the finished transactions and the current one. -/
structure PState (X V : Type) where
  done : List (TxRec X V)
  cur : TxRec X V

/-- The initial per-process state. -/
def PState.init : PState X V := ⟨[], TxRec.empty⟩

/-- Processing one label of the process. -/
def PState.step (s : PState X V) : Lbl P X V → PState X V
  | .inv _ o => ⟨s.done, ⟨s.cur.ops, some o⟩⟩
  | .ret _ r =>
    match s.cur.pend with
    | none => s
    | some o =>
      if endsTx o r then ⟨s.done ++ [⟨s.cur.ops ++ [(o, r)], none⟩], TxRec.empty⟩
      else ⟨s.done, ⟨s.cur.ops ++ [(o, r)], none⟩⟩
  | .tau _ => s

variable [DecidableEq P]

/-- The labels of process `p`. -/
def projP (h : List (Lbl P X V)) (p : P) : List (Lbl P X V) := h.filter (fun ℓ => ℓ.proc = p)

/-- The transactional bookkeeping of process `p` after the history `h`. -/
def pstate (h : List (Lbl P X V)) (p : P) : PState X V :=
  (projP h p).foldl PState.step PState.init

/-- Transaction identifiers: `(p, k)` is the `k`-th transaction of process `p` (from `0`). -/
abbrev TxId (P : Type) := P × ℕ

/-- The record of transaction `T` in `h` (empty if `T` has not begun). -/
def txRec (h : List (Lbl P X V)) (T : TxId P) : TxRec X V :=
  ((pstate h T.1).done ++ [(pstate h T.1).cur]).getD T.2 TxRec.empty

/-- The current transaction of `p` (the one its next invocation belongs to). -/
def cur (h : List (Lbl P X V)) (p : P) : TxId P := (p, (pstate h p).done.length)

/-- `T` has begun in `h` (some operation of `T` has been invoked). -/
def Began (h : List (Lbl P X V)) (T : TxId P) : Prop :=
  (txRec h T).ops ≠ [] ∨ (txRec h T).pend ≠ none

instance [DecidableEq X] [DecidableEq V] (h : List (Lbl P X V)) (T : TxId P) :
    Decidable (Began h T) := by
  unfold Began; infer_instance

/-- `T` is committed in `h`. -/
def Committed (h : List (Lbl P X V)) (T : TxId P) : Prop :=
  ∃ v, (TOp.tryC, some v) ∈ (txRec h T).ops

/-- `T` has a write operation (invoked, possibly pending or aborted). -/
def HasWrite (h : List (Lbl P X V)) (T : TxId P) : Prop :=
  (∃ x v r, (TOp.write x v, r) ∈ (txRec h T).ops) ∨ ∃ x v, (txRec h T).pend = some (.write x v)

/-- `T` read value `v` from `x` (a completed read). -/
def Reads (h : List (Lbl P X V)) (T : TxId P) (x : X) (v : V) : Prop :=
  (TOp.read x, some v) ∈ (txRec h T).ops

/-- The successful writes `(x, v)` of a list of completed operations. -/
def writesOf : List (TOp X V × Option V) → List (X × V)
  | [] => []
  | (.write x v, some _) :: l => (x, v) :: writesOf l
  | _ :: l => writesOf l

/-- The value written by `T` to `x` (its last successful write to `x`), if any. -/
def wval [DecidableEq X] (h : List (Lbl P X V)) (T : TxId P) (x : X) : Option V :=
  (((writesOf (txRec h T).ops).filter (fun w => w.1 = x)).map Prod.snd).getLast?

/-- The data set of `T`: the transactional objects of its invoked operations. -/
def DSet (h : List (Lbl P X V)) (T : TxId P) : Set X :=
  {x | (∃ q ∈ (txRec h T).ops, q.1.obj = some x) ∨ ∃ o, (txRec h T).pend = some o ∧ o.obj = some x}

/-- The object and value of a write invocation. -/
def writeInv : Lbl P X V → Option (X × V)
  | .inv _ (.write x v) => some (x, v)
  | _ => none

/-! ### Versions and the direct serialization graph -/

section DSG

variable [DecidableEq X] (v₀ : X → V)

/-- `T` is a committed transaction that wrote `x`: it created a version of `x`. -/
def CWriter (h : List (Lbl P X V)) (x : X) (T : TxId P) : Prop :=
  Committed h T ∧ (wval h T x).isSome

/-- The version order on `x`: committed writers of `x`, ordered by commit time. -/
def VOrd (h : List (Lbl P X V)) (x : X) (T T' : TxId P) : Prop :=
  CWriter h x T ∧ CWriter h x T' ∧ ∃ h₁ h₂, h = h₁ ++ h₂ ∧ Committed h₁ T ∧ ¬ Committed h₁ T'

/-- `T'` is the version of `x` immediately following version `u` (`none` = initial version). -/
def NextV (h : List (Lbl P X V)) (x : X) : Option (TxId P) → TxId P → Prop
  | none, T' => CWriter h x T' ∧ ¬ ∃ T'', VOrd h x T'' T'
  | some T, T' => VOrd h x T T' ∧ ¬ ∃ T'', VOrd h x T T'' ∧ VOrd h x T'' T'

/-- The value of version `u` of `x`. -/
def vval (h : List (Lbl P X V)) (x : X) : Option (TxId P) → Option V
  | none => some (v₀ x)
  | some T => wval h T x

/-- Direct read-dependence `T →wr T'`: `T'` read the version of some `x` committed by `T`.
Read-from is determined by values; this is exact on histories with unique written values
(`UniqueWrites`), the only ones `EnsuresRTO` / `EnsuresWRTO` quantify over. -/
def WR (h : List (Lbl P X V)) (T T' : TxId P) : Prop :=
  T ≠ T' ∧ Committed h T ∧ ∃ x v, Reads h T' x v ∧ wval h T x = some v

/-- Direct write-dependence `T →ww T'`: `T'` wrote the version of some `x` following `T`'s. -/
def WW (h : List (Lbl P X V)) (T T' : TxId P) : Prop :=
  ∃ x, NextV h x (some T) T'

/-- Direct anti-dependence `T →rw T'`: `T` read a version of `x` (written by a transaction other
than `T`, or initial) and `T'` wrote the next version of `x`. -/
def RW (h : List (Lbl P X V)) (T T' : TxId P) : Prop :=
  T ≠ T' ∧ ∃ x v u, Reads h T x v ∧ vval v₀ h x u = some v ∧ u ≠ some T ∧ NextV h x u T'

/-- The direct serialization graph `DSG(H)`. -/
def DSG (h : List (Lbl P X V)) (T T' : TxId P) : Prop :=
  WR h T T' ∨ WW h T T' ∨ RW v₀ h T T'

/-- Real-time order `Tq ≺RTO Tk`: `Tq` committed before `Tk` began. -/
def RTO (h : List (Lbl P X V)) (T T' : TxId P) : Prop :=
  Began h T' ∧ ∃ h₁ h₂, h = h₁ ++ h₂ ∧ Committed h₁ T ∧ ¬ Began h₁ T'

/-- Witnessable real-time order: RTO between transactions joined by a direct DSG edge. -/
def WRTO (h : List (Lbl P X V)) (T T' : TxId P) : Prop :=
  RTO h T T' ∧ (DSG v₀ h T T' ∨ DSG v₀ h T' T)

/-- `H` preserves RTO: adding an edge `Tq → Tk` for every `Tq ≺RTO Tk` to `DSG(H)` creates no
cycle through `Tq` and `Tk`. -/
def PreservesRTO (h : List (Lbl P X V)) : Prop :=
  ∀ T T', RTO h T T' → ¬ Relation.TransGen (DSG v₀ h ⊔ RTO h) T' T

/-- `H` preserves WRTO. -/
def PreservesWRTO (h : List (Lbl P X V)) : Prop :=
  ∀ T T', WRTO v₀ h T T' → ¬ Relation.TransGen (DSG v₀ h ⊔ WRTO v₀ h) T' T

/-- RTO is stronger than WRTO. -/
theorem PreservesRTO.preservesWRTO {h : List (Lbl P X V)} (H : PreservesRTO v₀ h) :
    PreservesWRTO v₀ h := by
  intro T T' hw hc
  refine H T T' hw.1 (Relation.TransGen.mono (fun a b hab => ?_) _ _ hc)
  rcases hab with hab | hab
  · exact Or.inl hab
  · exact Or.inr hab.1

/-- Every write invoked in `h` writes a value different from the initial value of its object and
from the values of all other writes to that object. The paper's histories name versions
(`Rᵢ(xⱼ)`); with read-from determined by values, this is the standard "unique values" convention
that makes read-from unambiguous. -/
def UniqueWrites (h : List (Lbl P X V)) : Prop :=
  (h.filterMap writeInv).Nodup ∧ ∀ z ∈ h.filterMap writeInv, z.2 ≠ v₀ z.1

end DSG

/-! ### Properties of TM implementations -/

section Props

variable {ι : Type} {B : ι → ObjSpec} {L : Type} [DecidableEq ι]
variable (I : Impl (tmSpec X V) B P L)

/-- A primitive is trivial if it never changes the state of the base object. -/
def Trivial {i : ι} (o : (B i).Op) : Prop := ∀ s, ((B i).δ s o).1 = s

/-- Two transactions are *not disjoint-access* in `h`: they are joined by a path in the conflict
graph of `h`, whose vertices are the transactions that have begun and whose edges join
transactions with intersecting data sets. -/
def Connected (h : List (Lbl P X V)) : TxId P → TxId P → Prop :=
  Relation.ReflTransGen (fun T T' => Began h T ∧ Began h T' ∧ (DSet h T ∩ DSet h T').Nonempty)

/-- **Weak disjoint-access parallelism** (WDAP, Attiya–Hillel–Milani). Two transactions
concurrently contend on a base object (in some reachable configuration, both have a pending step
on that base object, and at least one of the two primitives is non-trivial) only if they are not
disjoint-access. -/
def WDAP : Prop :=
  ∀ (α : List (Lbl P X V)) (C : Config (tmSpec X V) B P L), I.run α = some C →
    ∀ a b, a ≠ b → C.pend a ≠ none → C.pend b ≠ none →
    ∀ (i : ι) (o o' : (B i).Op) k k', I.act a (C.loc a) = .access i o k →
      I.act b (C.loc b) = .access i o' k' → (¬ Trivial o ∨ ¬ Trivial o') →
      Connected α (cur α a) (cur α b)

/-- Process `p` completes the operation `o` invoked in configuration `C`, running solo, with the
successful response `some v`. -/
def SoloCompletes (C : Config (tmSpec X V) B P L) (p : P) (o : TOp X V) (v : V) : Prop :=
  ∃ β : List (Lbl P X V), (∀ ℓ ∈ β, ℓ = .tau p) ∧
    (I.runFrom C (.inv p o :: β ++ [.ret p (some v)])).isSome

/-- **Obstruction-free write transactions.** An operation of a write transaction (one that has
invoked a write) that encounters no step contention (no other process has taken a step since the
transaction began) completes when run solo, and is not aborted. -/
def ObstructionFreeWrites : Prop :=
  ∀ (α₁ α₂ : List (Lbl P X V)) C p (o : TOp X V), I.run (α₁ ++ α₂) = some C →
    ¬ Began α₁ (cur α₁ p) → (∀ ℓ ∈ α₂, ℓ.proc = p) → C.pend p = none →
    (o.IsWrite ∨ HasWrite (α₁ ++ α₂) (cur (α₁ ++ α₂) p)) →
    ∃ v, SoloCompletes I C p o v

/-- **Write transactions run in isolation commit.** An operation of a write transaction that
runs with no concurrent transaction at all (when it began, no transaction was live, and no other
process has taken a step since) completes when run solo and is not aborted. Weak progressiveness
(a transaction is aborted only if it conflicts with a concurrent transaction), together with
termination of solo operations, implies it, and so does `ObstructionFreeWrites`. -/
def IsolatedWritesCommit : Prop :=
  ∀ (α₁ α₂ : List (Lbl P X V)) C p (o : TOp X V), I.run (α₁ ++ α₂) = some C →
    (∀ q, ¬ Began α₁ (cur α₁ q)) → (∀ ℓ ∈ α₂, ℓ.proc = p) → C.pend p = none →
    (o.IsWrite ∨ HasWrite (α₁ ++ α₂) (cur (α₁ ++ α₂) p)) →
    ∃ v, SoloCompletes I C p o v

/-- **Wait-free read-only transactions** (WFRO). A read or `tryC` of a transaction that has not
invoked a write completes (in particular, when run solo) and is not aborted: such a transaction
may turn out to be read-only, and a read-only transaction commits in a finite number of its own
steps. -/
def WaitFreeReadOnly : Prop :=
  ∀ (α : List (Lbl P X V)) C p (o : TOp X V), I.run α = some C → C.pend p = none →
    ¬ o.IsWrite → ¬ HasWrite α (cur α p) → ∃ v, SoloCompletes I C p o v

/-- **Invisible read-only transactions** (IRO). The steps of a read of a transaction that has not
invoked a write apply only trivial primitives. -/
def InvisibleReads : Prop :=
  ∀ (α : List (Lbl P X V)) C p x, I.run α = some C → C.pend p = some (.read x) →
    ¬ HasWrite α (cur α p) → ∀ (i : ι) (o : (B i).Op) k, I.act p (C.loc p) = .access i o k →
      Trivial o

/-- **Legal reads** (implicit in the paper, where a read always returns a version): a read of `x`
returns the initial value `v₀ x` or a value that some invoked operation writes to `x`. -/
def LegalReads (v₀ : X → V) : Prop :=
  ∀ (α : List (Lbl P X V)) C p x v l, I.run α = some C → C.pend p = some (.read x) →
    I.act p (C.loc p) = .ret (some v) l → v = v₀ x ∨ ∃ q, .inv q (.write x v) ∈ α

/-- The TM *ensures RTO*: every history it produces (with unique written values, so that
read-from is unambiguous) preserves RTO. Without `UniqueWrites`, a serial history in which a
transaction writes the initial value of `x` and a later one reads it would count as a violation
(`Figure1.serial_repeated_value_not_preservesRTO`). -/
def EnsuresRTO [DecidableEq X] (v₀ : X → V) : Prop :=
  ∀ α : List (Lbl P X V), I.Valid α → UniqueWrites v₀ α → PreservesRTO v₀ α

/-- The TM *ensures WRTO* (on histories with unique written values). -/
def EnsuresWRTO [DecidableEq X] (v₀ : X → V) : Prop :=
  ∀ α : List (Lbl P X V), I.Valid α → UniqueWrites v₀ α → PreservesWRTO v₀ α

/-- `ObstructionFreeWrites` implies `IsolatedWritesCommit`. -/
theorem ObstructionFreeWrites.isolated (h : ObstructionFreeWrites I) : IsolatedWritesCommit I :=
  fun α₁ α₂ C p o hC hq h₂ hp hw => h α₁ α₂ C p o hC (hq p) h₂ hp hw

end Props

end Podc.DAPInvisibleReads
