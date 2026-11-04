import Cslib.Computability.Distributed.SharedMemory.Covering
import Podc.Computability.Distributed.SharedMemory.Contention

/-!
# Universal constructions, feeble disjoint-access parallelism, value-obliviousness

Ellen, Fatourou, Kosmas, Milani, Travers. *Universal Constructions that Ensure Disjoint-Access
Parallelism and Wait-Freedom.* PODC 2012 (full version: HAL research report hal-00697198v2),
Sections 3 and 4.

**Model.** Asynchronous shared memory (`Cslib.SharedMemory`): processes are deterministic
programs (`Impl`), each step applies one primitive to one base object (arbitrary sequential
objects `B i`, e.g. registers, LL/SC, CAS), the scheduler is arbitrary, crashes are modelled by
processes that stop taking steps (wait-freedom quantifies over all infinite executions).

**Data structures.** A sequential data structure (`SeqDS`) is given by its sequential
specification together with the *data items* each operation accesses when it is executed by
itself from a given state (`SeqDS.dataSet`), as determined by its sequential code (which accesses
data items only through `CreateDI`, `ReadDI`, `WriteDI`). A universal construction maps every
data structure to an implementation (`UniversalConstruction`).

**Definitions of the paper formalized here.**
* trivial / non-trivial primitives (`ObjSpec.ReadOnly`: never changes the state of the object);
  *contention* of two executions on a base object (`Contend`);
* the state represented by a quiescent configuration (`RepresentsState`);
* **Definition 1** — feeble disjoint-access parallelism (`FeeblyDAP`, `UniversalConstruction.FeeblyDAP`);
* value-oblivious operations of a data structure (`SeqDS.ValueOblivious`), and
  **Assumption 3** — the value-obliviousness assumption on universal constructions
  (`ImplValueOblivious`, `UniversalConstruction.ValueObliviousAssumption`).
-/

namespace Podc.DAPUniversalConstruction

open Cslib.SharedMemory

/-! ### Sequential data structures -/

/-- A sequential data structure: a sequential specification together with the data items that
each operation accesses when executed by itself from a given state. -/
structure SeqDS where
  /-- The sequential specification (states, operations, responses, transition function). -/
  spec : ObjSpec
  /-- The data items. -/
  Item : Type
  /-- `dataSet s o`: the data items accessed by the sequential code of `o` run from state `s`. -/
  dataSet : spec.State → spec.Op → Set Item

namespace SeqDS

/-- The operation `op` (with input parameters in `V`) is *value oblivious* (Section 3): in every
sequential execution (from every reachable state `s`), the set of data items accessed by each
instance in a sequence of consecutive instances of `op` does not depend on the input parameters
of these instances. The `n`-th instance (from `0`) has parameter `f n`. -/
def ValueOblivious (S : SeqDS) {V : Type} (op : V → S.spec.Op) : Prop :=
  ∀ (os : List S.spec.Op) (f g : ℕ → V) (n : ℕ),
    S.dataSet (S.spec.runOps (S.spec.runOps S.spec.init os) ((List.range n).map (op ∘ f)))
        (op (f n)) =
      S.dataSet (S.spec.runOps (S.spec.runOps S.spec.init os) ((List.range n).map (op ∘ g)))
        (op (g n))

end SeqDS

/-! ### Solo executions, contention, represented states -/

variable {A : ObjSpec} {ι : Type} {B : ι → ObjSpec} {P L : Type} [DecidableEq P] [DecidableEq ι]

/-- The first `n` steps of the solo execution of an invocation of `o` by `p` from `C`
(the invocation label followed by at most `n` steps; empty if `p` cannot invoke `o` in `C`). -/
noncomputable def soloPrefix (I : Impl A B P L) (p : P) (o : A.Op) (C : Config A B P L)
    (n : ℕ) : List (Label P A) :=
  match I.step C (.inv p o) with
  | some C₁ => .inv p o :: I.soloLabels p C₁ n
  | none => []

/-- Two execution fragments from `C` *contend* on some base object: both apply a primitive to it
and at least one of these primitives is non-trivial. -/
def Contend (I : Impl A B P L) (C : Config A B P L) (α β : List (Label P A)) : Prop :=
  ∃ b, b ∈ I.accessed C α ∧ b ∈ I.accessed C β ∧ (b ∈ I.written C α ∨ b ∈ I.written C β)

/-- The execution `α` represents the state `s` of the data structure: `α` is linearizable, and
every linearization of `α` ends in `s` (Section 3: "every quiescent configuration of an execution
… defines a state"). Requiring *every* linearization to agree makes `FeeblyDAP` weaker, hence the
impossibility result stronger. -/
def RepresentsState (α : List (Label P A)) (s : A.State) : Prop :=
  (∃ Lz, IsLinearization α Lz) ∧ ∀ Lz, IsLinearization α Lz → linState Lz = s

/-- **Definition 1 (feeble disjoint-access parallelism).** For every quiescent configuration `C`
(reached by an execution `α` representing state `s`), every solo execution of an operation `o₁`
by `p₁` and every solo execution of `o₂` by `p₂ ≠ p₁`, both from `C`: if the sequential code of
`o₁` and `o₂` access disjoint sets of data items from `s`, the two executions contend on no base
object. Solo executions may be partial (any number `n₁`, `n₂` of steps). -/
def FeeblyDAP {D : Type} (I : Impl A B P L) (DS : A.State → A.Op → Set D) : Prop :=
  ∀ (α : List (Label P A)) (C : Config A B P L) (s : A.State), I.run α = some C →
    C.Quiescent → RepresentsState α s →
    ∀ (p₁ p₂ : P) (o₁ o₂ : A.Op) (n₁ n₂ : ℕ), p₁ ≠ p₂ → Disjoint (DS s o₁) (DS s o₂) →
      ¬ Contend I C (soloPrefix I p₁ o₁ C n₁) (soloPrefix I p₂ o₂ C n₂)

/-! ### Consecutive instances of an operation, run solo -/

section Instances

variable (I : Impl A B P L) (C : Config A B P L) (r : P) {V : Type} (op : V → A.Op)
  (f : ℕ → V)

/-- `instCfg I C r op f n`: the configuration after `r` performs, solo from `C`, the instances
`op (f 0)`, …, `op (f (n-1))`, one after the other, each until it returns. -/
noncomputable def instCfg : ℕ → Config A B P L
  | 0 => C
  | n + 1 => (I.runFrom (instCfg n) (I.soloOp r (op (f n)) (instCfg n))).getD (instCfg n)

/-- The steps of the `n`-th instance `op (f n)` (from `0`), run solo from `instCfg … n`. -/
noncomputable def instSeg (n : ℕ) : List (Label P A) :=
  I.soloOp r (op (f n)) (instCfg I C r op f n)

end Instances

/-- **Assumption 3 (value-obliviousness assumption)**, for one implementation and one operation
`op`: the sets of base objects read from (accessed) and written to (non-trivially accessed)
during each instance of a solo execution of a sequence of consecutive instances of `op`,
starting from a reachable quiescent configuration, do not depend on the input parameters. -/
def ImplValueOblivious (I : Impl A B P L) {V : Type} (op : V → A.Op) : Prop :=
  ∀ (C : Config A B P L) (r : P), I.Reachable C → C.Quiescent → ∀ (f g : ℕ → V) (n : ℕ),
    I.accessed (instCfg I C r op f n) (instSeg I C r op f n) =
        I.accessed (instCfg I C r op g n) (instSeg I C r op g n) ∧
      I.written (instCfg I C r op f n) (instSeg I C r op f n) =
        I.written (instCfg I C r op g n) (instSeg I C r op g n)

/-! ### Universal constructions -/

/-- An implementation of a data structure from some base objects (with its own types of base
objects and local states). -/
structure Implementation (S : SeqDS) (P : Type) where
  /-- Base object names. -/
  ι : Type
  /-- Base objects. -/
  B : ι → ObjSpec
  /-- Local states. -/
  L : Type
  /-- Base objects have decidable equality. -/
  decι : DecidableEq ι
  /-- The implementation. -/
  impl : Impl S.spec B P L

/-- A universal construction for the processes `P`: a mechanism that produces, for every
sequential data structure, a concurrent implementation of it. -/
def UniversalConstruction (P : Type) : Type 1 := (S : SeqDS) → Implementation S P

namespace UniversalConstruction

variable (U : UniversalConstruction P)

/-- Every process may invoke every operation (no access discipline). -/
def AllowsAll : Prop := ∀ (S : SeqDS) (p : P) (o : S.spec.Op), (U S).impl.allowed p o

/-- The universal construction produces linearizable implementations. -/
def Linearizable : Prop :=
  ∀ S : SeqDS, letI := (U S).decι; (U S).impl.Linearizable

/-- The universal construction produces wait-free implementations. -/
def WaitFree : Prop :=
  ∀ S : SeqDS, letI := (U S).decι; (U S).impl.WaitFree

/-- **Definition 1.** A universal construction is feebly disjoint-access parallel if all
implementations resulting from it are. -/
def FeeblyDAP : Prop :=
  ∀ S : SeqDS, letI := (U S).decι; DAPUniversalConstruction.FeeblyDAP (U S).impl S.dataSet

/-- **Assumption 3.** If an operation of a data structure is value oblivious, then the sets of
base objects read from and written to during any solo execution of a sequence of consecutive
instances of this operation from a quiescent configuration do not depend on the input
parameters. -/
def ValueObliviousAssumption : Prop :=
  ∀ (S : SeqDS) (V : Type) (op : V → S.spec.Op), S.ValueOblivious op →
    letI := (U S).decι; ImplValueOblivious (U S).impl op

end UniversalConstruction

end Podc.DAPUniversalConstruction
