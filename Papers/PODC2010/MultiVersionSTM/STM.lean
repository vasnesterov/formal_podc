import Papers.PODC2010.MultiVersionSTM.Model

/-!
# STM algorithms on base objects

Section 3 of Perelman–Fan–Keidar (PODC 2010). An STM is run by threads `P` that communicate
through shared base objects `B` (holding values in `M`) and have private memory `L`. To run a
transactional operation, the thread `thr T` takes the invocation as input, performs a sequence of
base steps determined by the input and the memory (a `Prog`: a finite decision tree of
read-modify-write accesses), and returns a response. The base steps of one transactional step are
atomic. The algorithm is deterministic; the environment chooses the invocations (a schedule
`σ : List (Inv Tx O)`).

* `STM.exec`, `STM.hist`, `STM.conf`, `STM.resp`: the execution, history, final configuration
  and responses of a schedule.
* `STM.Correct` (strict serializability), `STM.MVPermissive` (Definition 2),
  `STM.ReadsWritten`: properties of all well-formed histories of the STM.
* **Versions kept.** The paper does not define which versions an STM "keeps". We let an STM come
  with a declared set `kept C` of versions kept in configuration `C`, with the two properties that
  give the notion its meaning: a read returns a kept version (`KeepsReads`), and a version that is
  not kept (garbage collected) is never kept again (`GCFinal`). `keptOld` counts the kept versions
  that are overwritten (the counts 6 and 7 in the proof of Theorem 1).
* Definition 1 (`WDAP`), Definition 3 (`OnlineSpaceOptimal`), Definition 4 (`UPGC`, literal
  reading, and `UPGCPrec`, the potential-reader reading of Section 7), and "the configuration
  external to a solo read-only transaction is unchanged" (`NoTrace`, Theorem 3).
-/

namespace Podc.MultiVersionSTM

open scoped Classical

/-- A program for one transactional step: return a result, or access base object `b` with the
read-modify-write primitive `f` (which writes `f x` and returns the old value `x`) and continue. -/
inductive Prog (B M α : Type) where
  | ret (a : α)
  | access (b : B) (f : M → M) (k : M → Prog B M α)

/-- One base-object access: object, old value, new value. -/
structure Access (B M : Type) where
  b : B
  old : M
  new : M

/-- Running a program on the shared memory: result, new memory, trace of accesses. -/
noncomputable def Prog.run {B M α : Type} : Prog B M α → (B → M) → α × (B → M) × List (Access B M)
  | .ret a, m => (a, m, [])
  | .access b f k, m =>
    let r := (k (m b)).run (Function.update m b (f (m b)))
    (r.1, r.2.1, ⟨b, m b, f (m b)⟩ :: r.2.2)

variable {Tx O P : Type}

/-- An STM algorithm: base objects `B` with values `M`, private states `L`, initial
configuration, and the program each thread runs for each invocation. -/
structure STM (Tx O P : Type) where
  B : Type
  M : Type
  L : Type
  mem₀ : B → M
  loc₀ : P → L
  prog : P → L → Inv Tx O → Prog B M (L × Resp Tx)

/-- A configuration: shared memory and private states. -/
structure Config (X : STM Tx O P) where
  mem : X.B → X.M
  loc : P → X.L

namespace STM

variable (X : STM Tx O P)

/-- The initial configuration. -/
def init : Config X := ⟨X.mem₀, X.loc₀⟩

/-- The trace of one transactional step. -/
abbrev Trace := List (Access X.B X.M)

variable [TxSys Tx P]

/-- One (atomic) transactional step: thread `thr i.tx` runs its program for `i`. -/
noncomputable def step (C : Config X) (i : Inv Tx O) : Config X × Resp Tx × X.Trace :=
  let r := (X.prog (thr i.tx) (C.loc (thr i.tx)) i).run C.mem
  (⟨r.2.1, Function.update C.loc (thr i.tx) r.1.1⟩, r.1.2, r.2.2)

/-- Running a schedule from a configuration: final configuration and the steps (events with
their base-step traces). -/
noncomputable def run (C : Config X) (σ : List (Inv Tx O)) :
    Config X × List (Event Tx O × X.Trace) :=
  σ.foldl (fun s i => let r := X.step s.1 i; (r.1, s.2 ++ [(⟨i, r.2.1⟩, r.2.2)])) (C, [])

/-- The execution of a schedule from the initial configuration. -/
noncomputable def exec (σ : List (Inv Tx O)) : Config X × List (Event Tx O × X.Trace) :=
  X.run X.init σ

/-- The history of a schedule. -/
noncomputable def hist (σ : List (Inv Tx O)) : Hist Tx O := (X.exec σ).2.map Prod.fst

/-- The configuration after a schedule. -/
noncomputable def conf (σ : List (Inv Tx O)) : Config X := (X.exec σ).1

/-- The response to invocation `i` after schedule `σ`. -/
noncomputable def resp (σ : List (Inv Tx O)) (i : Inv Tx O) : Resp Tx :=
  (X.step (X.conf σ) i).2.1

/-! ### Correctness and permissiveness -/

/-- The STM is strictly serializable: all its well-formed histories are. -/
def Correct : Prop := ∀ σ, WF (X.hist σ) → StrictSer (X.hist σ)

/-- The STM is MV-permissive (Definition 2). -/
def MVPermissive : Prop := ∀ σ, WF (X.hist σ) → MVPerm (X.hist σ)

/-- Reads of the STM return written versions. -/
def ReadsWrittenOnly : Prop := ∀ σ, WF (X.hist σ) → ReadsWritten (X.hist σ)

/-! ### Versions kept -/

/-- A read (not following an own write) returns a version kept just before it. -/
def KeepsReads (kept : Config X → Set (Version Tx O)) : Prop :=
  ∀ σ T o v, WF (X.hist (σ ++ [.read T o])) → X.resp σ (.read T o) = some v →
    ¬ Writes (X.hist σ) T o → (o, v) ∈ kept (X.conf σ)

/-- Garbage collection is final: an existing version that is not kept is never kept again. -/
def GCFinal (kept : Config X → Set (Version Tx O)) : Prop :=
  ∀ σ τ v, WF (X.hist (σ ++ τ)) → VExists (X.hist σ) v → v ∉ kept (X.conf σ) →
    v ∉ kept (X.conf (σ ++ τ))

/-- A correct, MV-permissive STM with a declared set of kept versions. -/
structure Valid (kept : Config X → Set (Version Tx O)) : Prop where
  correct : X.Correct
  mvPermissive : X.MVPermissive
  readsWritten : X.ReadsWrittenOnly
  keepsReads : X.KeepsReads kept
  gcFinal : X.GCFinal kept

/-- The number of kept overwritten versions after schedule `σ`. -/
noncomputable def keptOld (kept : Config X → Set (Version Tx O)) (σ : List (Inv Tx O)) : ℕ∞ :=
  (kept (X.conf σ) ∩ {v | Old (X.hist σ) v}).encard

/-- **Definition 3.** `X` is online space optimal if at every point of every (well-formed)
history it keeps at most as many (overwritten) versions as any other MV-permissive STM. -/
def OnlineSpaceOptimal (kept : Config X → Set (Version Tx O)) : Prop :=
  ∀ (Y : STM Tx O P) (keptY : Config Y → Set (Version Tx O)), Y.Valid keptY →
    ∀ σ, WF (X.hist σ) → WF (Y.hist σ) → X.keptOld kept σ ≤ Y.keptOld keptY σ

/-- `T` can read version `v` after `h` without violating correctness: the history in which `T`
then reads `v` and commits is strictly serializable. -/
def CanRead (h : Hist Tx O) (T : Tx) (v : Version Tx O) : Prop :=
  StrictSer (h ++ [⟨.read T v.1, some v.2⟩, ⟨.commit T, some none⟩])

/-- **Definition 4 (UP GC), literal reading.** A version is kept only if some extension of the
execution has a live transaction that can read it and cannot read any version written after it. -/
def UPGC (kept : Config X → Set (Version Tx O)) : Prop :=
  ∀ σ v, WF (X.hist σ) → v ∈ kept (X.conf σ) →
    ∃ τ T, WF (X.hist (σ ++ τ)) ∧ Live (X.hist (σ ++ τ)) T ∧ CanRead (X.hist (σ ++ τ)) T v ∧
      ∀ w, WrittenAfter (X.hist (σ ++ τ)) v w → ¬ CanRead (X.hist (σ ++ τ)) T w

/-- **UP GC, potential-reader reading** (Section 7, Design Principle 5): an overwritten version
is kept only if some live transaction precedes the transaction that overwrote it (only the
"precedes `oʲ⁺¹.writer`" half of "potential reader" is required, which makes this weaker). -/
def UPGCPrec (kept : Config X → Set (Version Tx O)) : Prop :=
  ∀ σ o v, WF (X.hist σ) → (o, v) ∈ kept (X.conf σ) → Old (X.hist σ) (o, v) →
    ∃ T W', Live (X.hist σ) T ∧ NextWriter (X.hist σ) o v W' ∧ Prec (X.hist σ) T W'

/-! ### Read visibility (Theorem 3) -/

/-- Two configurations agree outside thread `p`: same shared memory, same private states of the
other threads ("the configuration external to the transaction"). -/
def ExtEq (p : P) (C C' : Config X) : Prop := C.mem = C'.mem ∧ ∀ q, q ≠ p → C.loc q = C'.loc q

/-- Read-only transactions leave no trace: whenever a read-only transaction runs from its first
to its last step with no step of another transaction in between, the configurations external to
it before and after are the same. -/
def NoTrace : Prop :=
  ∀ σ τ T, WF (X.hist (σ ++ τ)) → ro T = true → (∀ i ∈ τ, Inv.tx i = T) →
    ¬ Began (X.hist σ) T → Committed (X.hist (σ ++ τ)) T →
    ExtEq X (thr T) (X.conf σ) (X.conf (σ ++ τ))

/-! ### Weak disjoint-access parallelism (Definition 1) -/

/-- Some base step of transaction `T` in the execution of `σ` accesses base object `b`. -/
def Touches (σ : List (Inv Tx O)) (T : Tx) (b : X.B) : Prop :=
  ∃ s ∈ (X.exec σ).2, s.1.inv.tx = T ∧ ∃ a ∈ s.2, a.b = b

/-- Some base step of transaction `T` in the execution of `σ` changes base object `b`. -/
def Changes (σ : List (Inv Tx O)) (T : Tx) (b : X.B) : Prop :=
  ∃ s ∈ (X.exec σ).2, s.1.inv.tx = T ∧ ∃ a ∈ s.2, a.b = b ∧ a.old ≠ a.new

/-- The base steps of `T₁` and `T₂` contend: some base object is accessed by both, and changed by
one of them. -/
def Contend (σ : List (Inv Tx O)) (T₁ T₂ : Tx) : Prop :=
  ∃ b, X.Touches σ T₁ b ∧ X.Touches σ T₂ b ∧ (X.Changes σ T₁ b ∨ X.Changes σ T₂ b)

end STM

/-- The `i`-th event of `h` belongs to a transaction satisfying `S`. -/
def EvAt (h : Hist Tx O) (i : ℕ) (S : Tx → Prop) : Prop := ∃ e, h[i]? = some e ∧ S e.inv.tx

/-- The execution interval of `T` overlaps that of `{T₁, T₂}`. -/
def Overlaps (h : Hist Tx O) (T₁ T₂ T : Tx) : Prop :=
  (∃ i j, i ≤ j ∧ EvAt h i (· = T) ∧ EvAt h j (fun x => x = T₁ ∨ x = T₂)) ∧
  (∃ i j, i ≤ j ∧ EvAt h i (fun x => x = T₁ ∨ x = T₂) ∧ EvAt h j (· = T))

/-- `T₁` and `T₂` are disjoint-access in `h`: in the graph on transactional objects joining two
objects accessed by a common transaction whose interval overlaps that of `{T₁, T₂}`, no object
accessed by `T₁` is connected to an object accessed by `T₂`. -/
def DisjointAccess (h : Hist Tx O) (T₁ T₂ : Tx) : Prop :=
  ¬ ∃ x y, Accesses h T₁ x ∧ Accesses h T₂ y ∧
    Relation.ReflTransGen (fun x y => ∃ T, Overlaps h T₁ T₂ T ∧ Accesses h T x ∧ Accesses h T y)
      x y

namespace STM

variable (X : STM Tx O P) [TxSys Tx P]

/-- **Definition 1.** Weak disjoint-access parallelism: in every execution, the base steps of two
disjoint-access transactions do not contend. -/
def WDAP : Prop :=
  ∀ σ, WF (X.hist σ) → ∀ T₁ T₂, T₁ ≠ T₂ → DisjointAccess (X.hist σ) T₁ T₂ → ¬ X.Contend σ T₁ T₂

end STM

end Podc.MultiVersionSTM
