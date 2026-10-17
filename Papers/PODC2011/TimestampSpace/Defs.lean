import Mathlib
import Cslib.Computability.Distributed.SharedMemory.Covering
import Cslib.Computability.Distributed.SharedMemory.Mutex
import Cslib.Computability.Distributed.SharedMemory.ObjClasses
import Cslib.Computability.Distributed.SharedMemory.Task
import Cslib.Foundations.Data.Nat.Descent

/-!
# Timestamp objects: definitions

Model of Helmi, Higham, Pacheco, Woelfel, *The space complexity of long-lived and one-shot
timestamp implementations*, PODC 2011 (full version arXiv:1103.5794v2).

* **System.** Asynchronous shared memory (CSLib `Cslib.SharedMemory.Impl`): processes `P`,
  base objects `B i`, `i : ι`, deterministic processes, executions are lists of labels
  (invocation / internal step / response).
* **Base objects.** For the lower bounds the base objects are *read/write-like*
  (`RWLike B`, from the shared object-class library): every primitive is either read-only or a
  blind overwrite. Registers (`register V v₀`, of arbitrary — also unbounded — value types) are
  the main example (`rwLike_register`).
* **Implemented object.** `tsObj T`: operations `getTS` and `compare t₁ t₂` over an arbitrary
  timestamp universe `T`; responses `Sum.inl t` (a timestamp) or `Sum.inr b` (a Boolean).
  The specification is not sequential: `TSCorrect α` says that whenever a `getTS` instance
  `g₁` returning `t₁` happens before a `getTS` instance `g₂` returning `t₂`, then every
  `compare(t₁, t₂)` invoked after `g₂` returned returns `true` and every such
  `compare(t₂, t₁)` returns `false`.
* **Long-lived vs one-shot.** `Adm oneShot α`: if `oneShot` then every process invokes `getTS`
  at most once in `α` (`compare` is unrestricted).
* **Progress.** `SoloTerm I oneShot`: from every configuration reached by an admissible
  execution, a pending process running solo returns (for deterministic processes this is the
  paper's "non-deterministic solo-termination", i.e. obstruction-freedom). It is the library's
  `Impl.ObstructionFreeOn (Adm oneShot)` (`soloTerm_iff`).
-/

set_option linter.unusedSectionVars false

namespace Cslib.SharedMemory.Timestamp

open Cslib.SharedMemory

/-- Operations of a timestamp object over the universe `T`. -/
inductive TSOp (T : Type) where
  /-- `getTS()`. -/
  | getTS
  /-- `compare(t₁, t₂)`. -/
  | compare (t₁ t₂ : T)

/-- Is the operation a `getTS`? -/
def TSOp.isGetTS {T : Type} : TSOp T → Bool
  | .getTS => true
  | .compare _ _ => false

/-- The interface of a timestamp object. The sequential "specification" is a dummy: timestamp
objects are specified by the history property `TSCorrect`. -/
abbrev tsObj (T : Type) : ObjSpec where
  State := Unit
  Op := TSOp T
  Resp := T ⊕ Bool
  init := ()
  δ _ _ := ((), .inr false)

variable {P : Type} [DecidableEq P] {T : Type}

/-- **Correctness of a timestamp object** on the history of an execution `α`:
* every completed `getTS` returns a timestamp (`Sum.inl t`), and
* if a `getTS` instance `g₁` returning `t₁` happens before a `getTS` instance `g₂` returning `t₂`,
  then a `compare(t₁, t₂)` invoked after `g₂` returned returns `true` and a `compare(t₂, t₁)`
  invoked after `g₂` returned returns `false`. -/
structure TSCorrect (α : List (Label P (tsObj T))) : Prop where
  getTS_ts : ∀ (g : OpId P) (r : T ⊕ Bool), opOf α g = some .getTS → respOf α g = some r →
    ∃ t, r = .inl t
  order : ∀ (g₁ g₂ c : OpId P) (t₁ t₂ : T) (o : TSOp T) (r : T ⊕ Bool),
    opOf α g₁ = some .getTS → respOf α g₁ = some (.inl t₁) →
    opOf α g₂ = some .getTS → respOf α g₂ = some (.inl t₂) →
    Precedes α g₁ g₂ → Precedes α g₂ c → opOf α c = some o → respOf α c = some r →
    (o = .compare t₁ t₂ → r = .inr true) ∧ (o = .compare t₂ t₁ → r = .inr false)

/-- Number of `getTS` invocations of `p` in `α`. -/
def getTSCount (α : List (Label P (tsObj T))) (p : P) : ℕ :=
  (opsOf α p).countP TSOp.isGetTS

/-- Admissible executions: all executions (long-lived) or, if `oneShot`, the executions in which
every process invokes `getTS` at most once. -/
def Adm (oneShot : Bool) (α : List (Label P (tsObj T))) : Prop :=
  oneShot = true → ∀ p, getTSCount α p ≤ 1

variable {ι : Type} {B : ι → ObjSpec} {L : Type}

variable [DecidableEq ι]

/-- Solo termination (obstruction-freedom) on admissible executions. -/
abbrev SoloTerm (I : Impl (tsObj T) B P L) (oneShot : Bool) : Prop :=
  I.ObstructionFreeOn (Adm oneShot)

/-- `SoloTerm`, unfolded: from every configuration reached by an admissible execution, a pending
process running solo returns. -/
lemma soloTerm_iff (I : Impl (tsObj T) B P L) (oneShot : Bool) :
    SoloTerm I oneShot ↔ ∀ α C p, I.run α = some C → Adm oneShot α → C.pend p ≠ none →
      ∃ k, ((I.soloStep p)^[k] C).pend p = none := Iff.rfl

/-- `I` is a timestamp implementation (long-lived if `oneShot = false`, one-shot otherwise)
satisfying non-deterministic solo termination: all operations may be invoked by all processes,
every admissible execution satisfies `TSCorrect`, and solo runs from admissible configurations
terminate. -/
structure IsTS (I : Impl (tsObj T) B P L) (oneShot : Bool) : Prop where
  allowed : ∀ p o, I.allowed p o
  correct : ∀ α, I.Valid α → Adm oneShot α → TSCorrect α
  progress : SoloTerm I oneShot

/-! ### Basic facts about admissibility -/

@[simp] lemma getTSCount_append (α β : List (Label P (tsObj T))) (p : P) :
    getTSCount (α ++ β) p = getTSCount α p + getTSCount β p := by
  simp [getTSCount, List.countP_append]

lemma getTSCount_eq_zero_of_opsOf {α : List (Label P (tsObj T))} {p : P}
    (h : ∀ o ∈ opsOf α p, o.isGetTS = false) : getTSCount α p = 0 := by
  simp only [getTSCount, List.countP_eq_zero]
  intro o ho; simp [h o ho]

lemma getTSCount_of_proc_ne {α : List (Label P (tsObj T))} {p : P} (h : ∀ ℓ ∈ α, ℓ.proc ≠ p) :
    getTSCount α p = 0 := by
  simp [getTSCount, opsOf_eq_nil_of_proc_ne h]

lemma getTSCount_le_length (α : List (Label P (tsObj T))) (p : P) :
    getTSCount α p ≤ (opsOf α p).length := List.countP_le_length

lemma Adm.of_append {os : Bool} {α β : List (Label P (tsObj T))} (h : Adm os (α ++ β)) :
    Adm os α := fun hos p => by
  have := h hos p; simp only [getTSCount_append] at this; omega

/-- Admissibility only depends on the per-process `getTS` counts. -/
lemma Adm.of_count {os : Bool} {α β : List (Label P (tsObj T))} (h : Adm os α)
    (hc : ∀ p, getTSCount β p ≤ getTSCount α p) : Adm os β := fun hos p =>
  (hc p).trans (h hos p)

lemma Adm.append_of_zero {os : Bool} {α β : List (Label P (tsObj T))} (h : Adm os α)
    (hβ : ∀ p, getTSCount β p = 0) : Adm os (α ++ β) :=
  h.of_count (fun p => by simp [hβ p])

lemma adm_false (α : List (Label P (tsObj T))) : Adm false α := fun h => by simp at h

/-- In a long-lived implementation, `IsTS` progress is CSLib obstruction-freedom. -/
lemma soloTerm_false_iff (I : Impl (tsObj T) B P L) :
    SoloTerm I false ↔ I.ObstructionFree := by
  constructor
  · intro h C p ⟨α, hα⟩ hp; exact h α C p hα (adm_false α) hp
  · intro h α C p hα _ hp; exact h C p ⟨α, hα⟩ hp

end Cslib.SharedMemory.Timestamp
