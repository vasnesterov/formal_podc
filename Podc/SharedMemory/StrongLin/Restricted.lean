import Podc.SharedMemory.StrongLin.Basic
import Podc.SharedMemory.Progress

-- CSLib candidate: Cslib/Computability/Distributed/SharedMemory/StrongLin.lean

/-!
# Strong linearizability restricted to a class of executions

Objects with a *usage discipline* (one-shot objects, objects whose operations may only be invoked
by designated processes, objects that may be used only after some event) need correctness only
on the executions that respect the discipline. For a set `E` of finite executions (intended to be
`PrefixClosed`):

* `Impl.StrongLinOn E` — a linearization function on the executions of `E`, prefix-closed
  within `E`;
* `Impl.NStrongLinOn S E` — the same for a nondeterministic specification `S`.

Each is implied by its unrestricted version (and equivalent to it for `E = fun _ => True`), so
impossibility results proved for the restricted notions are stronger. The corresponding
restricted progress conditions `Impl.WaitFreeOn`, `Impl.LockFreeOn`, `Impl.ObstructionFreeOn`
are in `Podc.SharedMemory.Progress`.
-/

set_option linter.unusedSectionVars false

namespace Cslib.SharedMemory

variable {A : ObjSpec} {ι : Type} {B : ι → ObjSpec} {P L : Type}

namespace Impl

variable [DecidableEq P] [DecidableEq ι] (I : Impl A B P L)

/-- Strong linearizability on the executions of `E`. -/
def StrongLinOn (E : List (Label P A) → Prop) : Prop :=
  ∃ h : List (Label P A) → List (OpId P × A.Op),
    (∀ α, I.Valid α → E α → IsLinearization α (h α)) ∧
    ∀ α β, I.Valid β → E β → α <+: β → h α <+: h β

/-- Strong linearizability with respect to a nondeterministic specification, on the executions
of `E`. -/
def NStrongLinOn (S : NSpec A.Op A.Resp) (E : List (Label P A) → Prop) : Prop :=
  ∃ h : List (Label P A) → List (OpId P × A.Op × A.Resp),
    (∀ α, I.Valid α → E α → IsNLinearization S α (h α)) ∧
    ∀ α β, I.Valid β → E β → α <+: β → h α <+: h β

variable {I}

lemma StronglyLinearizable.strongLinOn (h : I.StronglyLinearizable) (E : List (Label P A) → Prop) :
    I.StrongLinOn E := by
  obtain ⟨f, hf, hp⟩ := h
  exact ⟨f, fun α hα _ => hf α hα, fun α β hβ _ hαβ => hp α β hβ hαβ⟩

lemma NStronglyLinearizable.nStrongLinOn {S : NSpec A.Op A.Resp} (h : I.NStronglyLinearizable S)
    (E : List (Label P A) → Prop) : I.NStrongLinOn S E := by
  obtain ⟨f, hf, hp⟩ := h
  exact ⟨f, fun α hα _ => hf α hα, fun α β hβ _ hαβ => hp α β hβ hαβ⟩

lemma strongLinOn_true_iff : I.StrongLinOn (fun _ => True) ↔ I.StronglyLinearizable :=
  ⟨fun ⟨f, hf, hp⟩ => ⟨f, fun α hα => hf α hα trivial, fun α β hβ => hp α β hβ trivial⟩,
    fun h => h.strongLinOn _⟩

lemma nStrongLinOn_true_iff {S : NSpec A.Op A.Resp} :
    I.NStrongLinOn S (fun _ => True) ↔ I.NStronglyLinearizable S :=
  ⟨fun ⟨f, hf, hp⟩ => ⟨f, fun α hα => hf α hα trivial, fun α β hβ => hp α β hβ trivial⟩,
    fun h => h.nStrongLinOn _⟩

lemma StrongLinOn.mono {E E' : List (Label P A) → Prop} (h : I.StrongLinOn E)
    (hE : ∀ α, E' α → E α) : I.StrongLinOn E' := by
  obtain ⟨f, hf, hp⟩ := h
  exact ⟨f, fun α hα h' => hf α hα (hE α h'), fun α β hβ h' hαβ => hp α β hβ (hE β h') hαβ⟩

lemma NStrongLinOn.mono {S : NSpec A.Op A.Resp} {E E' : List (Label P A) → Prop}
    (h : I.NStrongLinOn S E) (hE : ∀ α, E' α → E α) : I.NStrongLinOn S E' := by
  obtain ⟨f, hf, hp⟩ := h
  exact ⟨f, fun α hα h' => hf α hα (hE α h'), fun α β hβ h' hαβ => hp α β hβ (hE β h') hαβ⟩

end Impl

end Cslib.SharedMemory
