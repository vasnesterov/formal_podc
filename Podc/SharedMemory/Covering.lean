import Cslib.Computability.Distributed.SharedMemory.Covering

-- CSLib candidate: Cslib/Computability/Distributed/SharedMemory/Covering.lean

/-!
# Agreement of configurations

`Impl.AgreeOn Q C D` (CSLib, `Covering.lean`: same memory, same local states and pending operations
on `Q`) is an equivalence relation (`AgreeOn.refl`, `AgreeOn.symm`, `AgreeOn.trans`), and
agreement on all processes is equality (`AgreeOn.univ_eq`).
-/

namespace Cslib.SharedMemory

variable {A : ObjSpec} {ι : Type} {B : ι → ObjSpec} {P L : Type}

namespace Impl

@[refl] lemma AgreeOn.refl (Q : Set P) (C : Config A B P L) : AgreeOn Q C C :=
  ⟨rfl, fun _ _ => rfl, fun _ _ => rfl⟩

lemma AgreeOn.trans {Q : Set P} {C D E : Config A B P L} (h₁ : AgreeOn Q C D)
    (h₂ : AgreeOn Q D E) : AgreeOn Q C E :=
  ⟨h₁.mem.trans h₂.mem, fun q hq => (h₁.loc q hq).trans (h₂.loc q hq),
    fun q hq => (h₁.pend q hq).trans (h₂.pend q hq)⟩

/-- Configurations that agree on all processes are equal. -/
lemma AgreeOn.univ_eq {C D : Config A B P L} (h : AgreeOn Set.univ C D) : C = D := by
  cases C; cases D
  simp only [Config.mk.injEq]
  exact ⟨funext fun q => h.loc q trivial, funext fun q => h.pend q trivial, h.mem⟩

lemma agreeOn_univ_iff {C D : Config A B P L} : AgreeOn Set.univ C D ↔ C = D :=
  ⟨AgreeOn.univ_eq, fun h => h ▸ AgreeOn.refl _ _⟩

end Impl

end Cslib.SharedMemory
