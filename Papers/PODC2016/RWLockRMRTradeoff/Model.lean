import Cslib.Computability.Distributed.SharedMemory.Mutex
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Finset.Lattice.Fold

/-!
# The model of Hendler, *On the Complexity of Reader-Writer Locks* (PODC 2016)

* **Shared memory.** Asynchronous shared memory; processes are deterministic and communicate
  through registers supporting `read`, `write` and `CAS` (`rwcas`): `CAS(v, a, b)` sets `v` to
  `b` iff its value is `a`, and (as in the paper) returns the value of `v` before the step.
  Reader-writer lock algorithms are CSLib implementations (`Impl`) of the lock object
  `mutexObj` (operations `lock` / `unlock`) from such registers. Region bookkeeping (remainder,
  entry = `trying`, critical section, exit = `exiting`) is CSLib's `regionOf`.
* **Processes.** `Proc n m = Fin n ⊕ Fin m`: readers `Sum.inl i`, writers `Sum.inr j`.
* **Knowledge** (`Know`, `kstep`): the awareness sets `AW(p, C ↪ E)` and familiarity sets
  `F(v, C ↪ E)` of Definitions 1–2 of the paper, computed forward along an execution fragment
  (a *trivial* step, i.e. one that does not change the value of its register, never changes a
  familiarity set).
* **Cache-coherent RMRs** (`CacheModel`): an abstract CC cache with three axioms; the write-back
  (`writeBack`) and write-through (`writeThrough`) protocols quoted in the paper are instances.
* **Augmented runs** (`Ext`, `xrun`): configuration, knowledge and cache state together; `xcount`
  counts labels with a given property along a run.
-/

namespace Podc.RWLockRMRTradeoff

open Cslib.SharedMemory

/-! ### Registers -/

/-- A read/write/CAS register with values in `V`. `read` and `CAS` return the value before the
step; `write` returns an acknowledgement (`none`). -/
abbrev rwcas (V : Type) [DecidableEq V] (v₀ : V) : ObjSpec where
  State := V
  Op := CASOp V
  Resp := Option V
  init := v₀
  δ q
    | .read => (q, some q)
    | .write v => (v, none)
    | .cas a b => (if q = a then b else q, some q)

/-- The shared variables: registers indexed by `ι`. -/
abbrev Regs (ι V : Type) [DecidableEq V] (v₀ : V) : ι → ObjSpec := fun _ => rwcas V v₀

/-- The processes: `n` readers `Sum.inl i` and `m` writers `Sum.inr j`. -/
abbrev Proc (n m : ℕ) := Fin n ⊕ Fin m

/-- A reader-writer lock algorithm for `n` readers and `m` writers from read/write/CAS registers:
an implementation of `lock`/`unlock` (entry and exit section) with local states `L`. -/
abbrev RWAlg (n m : ℕ) (ι V : Type) [DecidableEq V] (v₀ : V) (L : Type) :=
  Impl mutexObj (Regs ι V v₀) (Proc n m) L

/-! ### Knowledge: awareness and familiarity sets (Definitions 1 and 2) -/

/-- Awareness sets of processes and familiarity sets of variables. -/
structure Know (P ι : Type) where
  /-- `AW(p, ·)`. -/
  aw : P → Finset P
  /-- `F(v, ·)`. -/
  fam : ι → Finset P

/-- Knowledge at the beginning of an execution fragment: `AW(p, C ↪ ⊥) = {p}`,
`F(v, C ↪ ⊥) = ∅`. -/
def Know.init {P ι : Type} : Know P ι := ⟨fun p => {p}, fun _ => ∅⟩

section Steps

variable {A : ObjSpec} {ι V P L : Type} [DecidableEq ι] [DecidableEq V] [DecidableEq P] {v₀ : V}
variable (I : Impl A (Regs ι V v₀) P L)

/-- The effect of a label on the knowledge (Definitions 1 and 2, read forward): a reading step
(read or CAS) of `p` on `v` adds `F(v)` to `AW(p)`; a non-trivial write sets `F(v) := AW(p)`; a
non-trivial CAS sets `F(v) := AW(p) ∪ F(v)` (which is the new `AW(p)`). Trivial steps (writes of
the current value, failed CAS, CAS with `new = expected`) leave `F(v)` unchanged. -/
def kstep (C : Config A (Regs ι V v₀) P L) (K : Know P ι) : Label P A → Know P ι
  | .tau p =>
    match I.act p (C.loc p) with
    | .access i o _ =>
      match (o : CASOp V) with
      | .read => { K with aw := Function.update K.aw p (K.aw p ∪ K.fam i) }
      | .write v => if C.mem i = v then K else { K with fam := Function.update K.fam i (K.aw p) }
      | .cas a b =>
        { aw := Function.update K.aw p (K.aw p ∪ K.fam i)
          fam := if C.mem i = a ∧ b ≠ a then Function.update K.fam i (K.aw p ∪ K.fam i)
            else K.fam }
    | .ret _ _ => K
  | _ => K

end Steps

/-! ### Cache-coherent RMR model -/

/-- A memory access as seen by the cache: a read, a write (and whether it changes the value), a
CAS (whether it succeeds, and whether it changes the value). -/
inductive Access
  | read
  | write (changes : Bool)
  | cas (success changes : Bool)

/-- Whether an access changes the value of its variable. -/
def Access.changes : Access → Bool
  | .read => false
  | .write c => c
  | .cas _ c => c

-- CSLib candidate: Cslib/Computability/Distributed/SharedMemory/CacheCoherent.lean
/-- An abstract cache-coherent (CC) memory: per-process caches, a predicate `rmr` telling whether
an access is a remote memory reference, and a predicate `valid s p v` (process `p` holds a valid
cached copy of `v`). Axioms:
* an access to a variable without a valid cached copy is an RMR;
* a step only creates valid copies for the stepping process and the accessed variable;
* a step that changes the value of `v` invalidates the copies of `v` held by other processes. -/
structure CacheModel (P ι : Type) where
  /-- Cache states. -/
  σ : Type
  /-- Initial cache state. -/
  init : σ
  /-- Effect of an access by `p` to `v`. -/
  step : σ → P → ι → Access → σ
  /-- The access is a remote memory reference. -/
  rmr : σ → P → ι → Access → Prop
  /-- `p` holds a valid copy of `v`. -/
  valid : σ → P → ι → Prop
  rmr_of_not_valid : ∀ s p i a, ¬ valid s p i → rmr s p i a
  valid_of_step : ∀ s q j a p i, valid (step s q j a) p i → q ≠ p ∨ j ≠ i → valid s p i
  not_valid_step : ∀ s q i a p, a.changes = true → q ≠ p → ¬ valid (step s q i a) p i

/-- Modes of a cached copy in the write-back protocol. -/
inductive Mode
  | inv
  | sh
  | ex
  deriving DecidableEq

section Protocols

variable {P ι : Type} [DecidableEq P] [DecidableEq ι]

/-- The **write-back** protocol, as quoted in the paper from Golab et al.: a read needs a copy in
shared or exclusive mode (otherwise an RMR downgrades exclusive copies and creates a shared one);
a write or CAS needs an exclusive copy (otherwise an RMR invalidates all other copies and creates
an exclusive one). -/
def writeBack : CacheModel P ι where
  σ := P → ι → Mode
  init := fun _ _ => .inv
  step s p i a :=
    match a with
    | .read =>
      if s p i = .inv then
        fun q j => if j = i then (if q = p then .sh else if s q j = .ex then .sh else s q j)
          else s q j
      else s
    | _ => fun q j => if j = i then (if q = p then .ex else .inv) else s q j
  rmr s p i a :=
    match a with
    | .read => s p i = .inv
    | _ => s p i ≠ .ex
  valid s p i := s p i ≠ .inv
  rmr_of_not_valid s p i a h := by
    push Not at h
    cases a <;> simp [h]
  valid_of_step s q j a p i h hne := by
    cases a with
    | read =>
      simp only at h
      split_ifs at h with h1
      · by_cases hj : i = j
        · subst hj
          have hqp : q ≠ p := by tauto
          simp only [ite_true, Ne.symm hqp, ite_false] at h
          split_ifs at h with h2
          · simp [h2]
          · exact h
        · simpa [hj] using h
      · exact h
    | write c =>
      by_cases hj : i = j
      · subst hj
        have hqp : q ≠ p := by tauto
        simp [Ne.symm hqp] at h
      · simpa [hj] using h
    | cas b c =>
      by_cases hj : i = j
      · subst hj
        have hqp : q ≠ p := by tauto
        simp [Ne.symm hqp] at h
      · simpa [hj] using h
  not_valid_step s q i a p ha hqp := by
    cases a with
    | read => simp [Access.changes] at ha
    | write c => simp [Ne.symm hqp]
    | cas b c => simp [Ne.symm hqp]

/-- The **write-through** protocol: a read without a valid copy is an RMR that creates one; every
write or CAS is an RMR that invalidates all other copies (the writer keeps a valid copy). -/
def writeThrough : CacheModel P ι where
  σ := P → ι → Bool
  init := fun _ _ => false
  step s p i a :=
    match a with
    | .read => Function.update s p (Function.update (s p) i true)
    | _ => fun q j => if j = i then decide (q = p) else s q j
  rmr s p i a :=
    match a with
    | .read => s p i = false
    | _ => True
  valid s p i := s p i = true
  rmr_of_not_valid s p i a h := by cases a <;> simp_all
  valid_of_step s q j a p i h hne := by
    cases a with
    | read =>
      simp only at h
      by_cases hq : q = p
      · subst hq
        have hj : j ≠ i := by tauto
        simpa [Function.update_of_ne (Ne.symm hj)] using h
      · simpa [Function.update_of_ne (Ne.symm hq)] using h
    | write c =>
      by_cases hj : i = j
      · subst hj
        have hqp : q ≠ p := by tauto
        simp [Ne.symm hqp] at h
      · simpa [hj] using h
    | cas b c =>
      by_cases hj : i = j
      · subst hj
        have hqp : q ≠ p := by tauto
        simp [Ne.symm hqp] at h
      · simpa [hj] using h
  not_valid_step s q i a p ha hqp := by
    cases a with
    | read => simp [Access.changes] at ha
    | write c => simp [Ne.symm hqp]
    | cas b c => simp [Ne.symm hqp]

end Protocols

/-! ### Augmented runs: configuration, knowledge, cache -/

section Runs

variable {A : ObjSpec} {ι V P L : Type} [DecidableEq ι] [DecidableEq V] [DecidableEq P] {v₀ : V}
variable (I : Impl A (Regs ι V v₀) P L) (cm : CacheModel P ι)

/-- The cache view of an operation applied to a register holding `x`. -/
def accessOf (x : V) : CASOp V → Access
  | .read => .read
  | .write v => .write (decide (x ≠ v))
  | .cas a b => .cas (decide (x = a)) (decide (x = a ∧ b ≠ a))

/-- The variable accessed by a label and the kind of access (`none` for invocations, responses). -/
def accessAt (C : Config A (Regs ι V v₀) P L) : Label P A → Option (ι × Access)
  | .tau p =>
    match I.act p (C.loc p) with
    | .access i o _ => some (i, accessOf (C.mem i) (o : CASOp V))
    | .ret _ _ => none
  | _ => none

/-- Effect of a label on the cache. -/
def cacheStep (C : Config A (Regs ι V v₀) P L) (s : cm.σ) (ℓ : Label P A) : cm.σ :=
  match accessAt I C ℓ with
  | some (i, a) => cm.step s ℓ.proc i a
  | none => s

/-- The label is a remote memory reference. -/
def IsRMR (C : Config A (Regs ι V v₀) P L) (s : cm.σ) (ℓ : Label P A) : Prop :=
  match accessAt I C ℓ with
  | some (i, a) => cm.rmr s ℓ.proc i a
  | none => False

/-- An augmented configuration: configuration, knowledge (relative to the beginning of the current
execution fragment) and cache state. -/
structure Ext (I : Impl A (Regs ι V v₀) P L) (cm : CacheModel P ι) where
  /-- The configuration. -/
  cfg : Config A (Regs ι V v₀) P L
  /-- Awareness and familiarity sets. -/
  kn : Know P ι
  /-- The cache. -/
  cache : cm.σ

variable {I cm}

/-- Augmented step. -/
noncomputable def xstep (X : Ext I cm) (ℓ : Label P A) : Option (Ext I cm) :=
  (I.step X.cfg ℓ).map fun C' => ⟨C', kstep I X.cfg X.kn ℓ, cacheStep I cm X.cfg X.cache ℓ⟩

/-- Augmented run. -/
noncomputable def xrun : Ext I cm → List (Label P A) → Option (Ext I cm)
  | X, [] => some X
  | X, ℓ :: β => (xstep X ℓ).bind fun Y => xrun Y β

/-- The same configuration and cache with fresh knowledge: the beginning of a fragment `C ↪ ·`. -/
def Ext.fresh (X : Ext I cm) : Ext I cm := ⟨X.cfg, Know.init, X.cache⟩

variable (I cm) in
/-- The initial augmented configuration. -/
def Ext.init : Ext I cm := ⟨I.initCfg, Know.init, cm.init⟩

open Classical in
/-- Number of labels of `β`, run from `X`, satisfying `f` (evaluated before the label). -/
noncomputable def xcount (f : Ext I cm → Label P A → Prop) :
    Ext I cm → List (Label P A) → ℕ
  | _, [] => 0
  | X, ℓ :: β =>
    match xstep X ℓ with
    | none => 0
    | some Y => (if f X ℓ then 1 else 0) + xcount f Y β

/-- `ℓ` is a remote memory reference by `p`. -/
def RMRBy (p : P) (X : Ext I cm) (ℓ : Label P A) : Prop :=
  ℓ.proc = p ∧ IsRMR I cm X.cfg X.cache ℓ

/-- **Definition 3.** A step is *expanding* (w.r.t. the current fragment) if it increases the size
of some awareness set. -/
def Expanding (X : Ext I cm) (ℓ : Label P A) : Prop :=
  ∃ q, (X.kn.aw q).card < ((kstep I X.cfg X.kn ℓ).aw q).card

/-- `ℓ` is an expanding step of `p`. -/
def ExpBy (p : P) (X : Ext I cm) (ℓ : Label P A) : Prop :=
  ℓ.proc = p ∧ Expanding X ℓ

@[simp] lemma xrun_nil (X : Ext I cm) : xrun X [] = some X := rfl

lemma xrun_cons (X : Ext I cm) (ℓ : Label P A) (β : List (Label P A)) :
    xrun X (ℓ :: β) = (xstep X ℓ).bind fun Y => xrun Y β := rfl

lemma xrun_append (X : Ext I cm) (α β : List (Label P A)) :
    xrun X (α ++ β) = (xrun X α).bind fun Y => xrun Y β := by
  induction α generalizing X with
  | nil => simp
  | cons ℓ α ih =>
    simp only [List.cons_append, xrun_cons, ih]
    cases xstep X ℓ <;> simp

lemma xrun_append_of_eq {X Y : Ext I cm} {α : List (Label P A)} (h : xrun X α = some Y)
    (β : List (Label P A)) : xrun X (α ++ β) = xrun Y β := by
  rw [xrun_append, h]; rfl

lemma xstep_eq_some {X Y : Ext I cm} {ℓ : Label P A} :
    xstep X ℓ = some Y ↔ I.step X.cfg ℓ = some Y.cfg ∧ Y.kn = kstep I X.cfg X.kn ℓ ∧
      Y.cache = cacheStep I cm X.cfg X.cache ℓ := by
  unfold xstep
  constructor
  · intro h
    obtain ⟨C', h1, rfl⟩ := Option.map_eq_some_iff.1 h
    exact ⟨h1, rfl, rfl⟩
  · rintro ⟨h1, h2, h3⟩
    rw [h1]; cases Y; simp_all

lemma xrun_cfg {X Y : Ext I cm} {α : List (Label P A)} (h : xrun X α = some Y) :
    I.runFrom X.cfg α = some Y.cfg := by
  induction α generalizing X with
  | nil => simp only [xrun_nil, Option.some.injEq] at h; subst h; rfl
  | cons ℓ α ih =>
    simp only [xrun_cons] at h
    cases hs : xstep X ℓ with
    | none => simp [hs] at h
    | some Z =>
      simp only [hs, Option.bind_some] at h
      simp [Impl.runFrom_cons, (xstep_eq_some.1 hs).1, ih h]

lemma exists_xrun {X : Ext I cm} {α : List (Label P A)} {C : Config A (Regs ι V v₀) P L}
    (h : I.runFrom X.cfg α = some C) : ∃ Y, xrun X α = some Y ∧ Y.cfg = C := by
  induction α generalizing X with
  | nil => simp only [Impl.runFrom_nil, Option.some.injEq] at h; exact ⟨X, rfl, h⟩
  | cons ℓ α ih =>
    simp only [Impl.runFrom_cons] at h
    cases hs : I.step X.cfg ℓ with
    | none => simp [hs] at h
    | some C₁ =>
      simp only [hs, Option.bind_some] at h
      obtain ⟨Y, h1, h2⟩ := ih (X := ⟨C₁, kstep I X.cfg X.kn ℓ, cacheStep I cm X.cfg X.cache ℓ⟩) h
      refine ⟨Y, ?_, h2⟩
      rw [xrun_cons, show xstep X ℓ = some ⟨C₁, _, _⟩ from xstep_eq_some.2 ⟨hs, rfl, rfl⟩]
      exact h1

lemma xcount_append (f : Ext I cm → Label P A → Prop) {X Y : Ext I cm}
    {α : List (Label P A)} (h : xrun X α = some Y) (β : List (Label P A)) :
    xcount f X (α ++ β) = xcount f X α + xcount f Y β := by
  induction α generalizing X with
  | nil => simp only [xrun_nil, Option.some.injEq] at h; subst h; simp [xcount]
  | cons ℓ α ih =>
    simp only [xrun_cons] at h
    cases hs : xstep X ℓ with
    | none => simp [hs] at h
    | some Z =>
      simp only [hs, Option.bind_some] at h
      simp only [List.cons_append, xcount, hs, ih h]
      omega

lemma xcount_mono {f g : Ext I cm → Label P A → Prop} (hfg : ∀ X ℓ, f X ℓ → g X ℓ)
    (X : Ext I cm) (β : List (Label P A)) : xcount f X β ≤ xcount g X β := by
  induction β generalizing X with
  | nil => simp [xcount]
  | cons ℓ β ih =>
    simp only [xcount]
    split
    · exact le_rfl
    · rename_i Y _
      have := ih Y
      split_ifs with h1 h2 <;> first | omega | exact absurd (hfg _ _ h1) h2

lemma xcount_le_length (f : Ext I cm → Label P A → Prop) (X : Ext I cm)
    (β : List (Label P A)) : xcount f X β ≤ β.length := by
  induction β generalizing X with
  | nil => simp [xcount]
  | cons ℓ β ih =>
    simp only [xcount, List.length_cons]
    split
    · omega
    · rename_i Y _; have := ih Y; split_ifs <;> omega

end Runs

end Podc.RWLockRMRTradeoff
