import Papers.PODC2012.WeakModelsModalLogic.Model

/-!
# Existence of port numberings

Every finite graph has a port numbering, in fact a consistent one
(`exists_consistent_portNumbering`, `exists_portNumbering`): identify the ports of `v` with its
neighbours and connect port `(v, w)` with port `(w, v)`.
-/

namespace Podc.WeakModelsModalLogic

open Function

variable {V : Type*}

/-- Every finite graph has a port numbering, and in fact a consistent one: identify the ports of
`v` with its neighbours and connect port `(v, w)` with port `(w, v)`. -/
theorem exists_consistent_portNumbering [Finite V] (G : SimpleGraph V) :
    ∃ P : PortNumbering G, P.Consistent := by
  let N := Σ v, G.neighborSet v
  let σ : N → N := fun x => ⟨x.2.1, ⟨x.1, x.2.2.symm⟩⟩
  have hσ : Involutive σ := fun _ => rfl
  let E : Port G ≃ N := Equiv.sigmaCongrRight fun v => (Finite.equivFin (G.neighborSet v)).symm
  have hE : ∀ x, (E x).1 = x.1 := fun _ => rfl
  have hE' : ∀ y, (E.symm y).1 = y.1 := fun _ => rfl
  refine ⟨⟨E.trans (hσ.toPerm.trans E.symm), fun x => ?_, fun u v h => ?_⟩, fun x => ?_⟩
  · simp only [Equiv.trans_apply, hE', Involutive.coe_toPerm]
    exact (E x).2.2
  · refine ⟨E.symm ⟨u, ⟨v, h⟩⟩, rfl, ?_⟩
    simp only [Equiv.trans_apply, Equiv.apply_symm_apply, hE', Involutive.coe_toPerm]
    rfl
  · simp [Involutive.coe_toPerm, hσ (E x)]

/-- Every finite graph has a port numbering. -/
theorem exists_portNumbering [Finite V] (G : SimpleGraph V) : Nonempty (PortNumbering G) :=
  let ⟨P, _⟩ := exists_consistent_portNumbering G; ⟨P⟩

end Podc.WeakModelsModalLogic
