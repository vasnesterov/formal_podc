import Papers.PODC2020.UndoableCRDTs.Counters

/-!
# The Only Undoable CRDTs are Counters (Dolan, PODC 2020) — main results

* `UndoableCRDTs.theorem_main`: every undoable CRDT is equivalent to a (finite) tuple of counter
  and modulo-counter CRDTs (Section 2.3, Theorem).
* Section 3 consequences: `all_operations_valid`, `negative_states`, `finite_states_periodic`
  and the trade-off `tradeoff`.

The definitions are in `Defs.lean`, Propositions 1–2 and Facts 1–6 in `Actions.lean`, the
group of actions and Proposition 3 in `Group.lean`, counters and tuples in `Counters.lean`.
-/

namespace UndoableCRDTs

open OpSystem UndoableCRDT

/-- **Section 2.5.** In an undoable CRDT, the actions available from any state form a finitely
generated abelian group `G_s`. -/
theorem groupOfActions_fg (C : UndoableCRDT.{u, v}) (s : C.S) : AddGroup.FG (C.G s) :=
  inferInstance

/-- The direct sum `ℤⁿ ⊕ ⨁ᵢ ℤ/pᵢ^{eᵢ}` is the group `∀ j, ZMod (m j)` for the moduli
`m = (0, …, 0, p₁^{e₁}, …)`. -/
noncomputable def directSumEquivPi (n : ℕ) {ι : Type} [Fintype ι] (p e : ι → ℕ) :
    ((Fin n →₀ ℤ) × DirectSum ι fun i => ZMod (p i ^ e i)) ≃+
      ∀ j : Fin n ⊕ ι, ZMod (Sum.elim (fun _ => 0) (fun i => p i ^ e i) j) :=
  let sumPi : (∀ j : Fin n ⊕ ι, ZMod (Sum.elim (fun _ => 0) (fun i => p i ^ e i) j)) ≃+
      ((Fin n → ℤ) × ∀ i, ZMod (p i ^ e i)) :=
    { Equiv.sumPiEquivProdPi (fun j => ZMod (Sum.elim (fun _ => 0) (fun i => p i ^ e i) j)) with
      map_add' := fun _ _ => rfl }
  (AddEquiv.prodCongr (Finsupp.linearEquivFunOnFinite ℤ ℤ (Fin n)).toAddEquiv
    (DirectSum.linearEquivFunOnFintype ℤ ι fun i => ZMod (p i ^ e i)).toAddEquiv).trans
    sumPi.symm

/-- **Theorem (Section 2.3).** Every undoable CRDT is equivalent to a tuple of counter and
modulo counter CRDTs: there are finitely many moduli `m i` (`m i = 0` is the unbounded counter
on `ℤ`; the others are prime powers) such that the CRDT is equivalent (Section 2.2) to the tuple
of the counters modulo `m i`. -/
theorem theorem_main (C : UndoableCRDT.{u, v}) :
    ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι) (m : ι → ℕ),
      (∀ i, m i = 0 ∨ ∃ p k, Nat.Prime p ∧ m i = p ^ k) ∧
      Nonempty (CRDTEquiv C.toOpSystem (counters m).toOpSystem) := by
  classical
  obtain ⟨n, ι, _, p, hp, e, ⟨f⟩⟩ := AddCommGroup.equiv_free_prod_directSum_zmod (C.G C.s0)
  refine ⟨Fin n ⊕ ι, inferInstance, inferInstance, Sum.elim (fun _ => 0) (fun i => p i ^ e i),
    ?_, ?_⟩
  · rintro (a | i)
    · exact Or.inl rfl
    · exact Or.inr ⟨p i, e i, hp i, rfl⟩
  · exact prop3 ((f.trans (directSumEquivPi n p e)).trans (countersGroupEquiv _).symm)

/-! ### Section 3: consequences -/

/-- **Section 3, "All operations are always valid".** In an undoable CRDT, an action that is
well defined in some state is well defined in every state. (Operations that are well defined
in *no* state are allowed by the definitions; see `Counterexamples.lean`.) -/
theorem all_operations_valid (C : UndoableCRDT.{u, v}) {s : C.S} {a : List C.P}
    (h : C.toOpSystem.Ok s a) (t : C.S) : C.toOpSystem.Ok t a :=
  ok_of_ok C.comm C.undo C.reachable h t

/-- **Section 3, "Negative states always exist".** For any action `a` (that applies somewhere),
there is a state `s` in which applying `a` brings us back to `s₀`. -/
theorem negative_states (C : UndoableCRDT.{u, v}) {s : C.S} {a : List C.P}
    (h : C.toOpSystem.Ok s a) : ∃ s', C.toOpSystem.act s' a = some C.s0 := by
  have h0 := ok_s0_of_ok C.comm C.undo C.reachable h
  obtain ⟨a', ha'⟩ := prop2 C.undo h0
  obtain ⟨s', hs'⟩ := fact4 C.comm h0 ha'
  refine ⟨s', ?_⟩
  rw [← act_append_of _ hs', fact5 C.comm h0 ha']

/-- Repeating an action `k` times adds `k • [a]` in the group of actions. -/
lemma act_eval_repeat (C : UndoableCRDT.{u, v}) {s : C.S} (x : C.G s) (a : List C.P)
    (ha : C.toOpSystem.Ok s a) (k : ℕ) :
    C.toOpSystem.act (eval s x) (List.replicate k a).flatten =
      some (eval s (x + k • G.mk a ha)) := by
  induction k generalizing x with
  | zero => simp
  | succ k ih =>
    rw [List.replicate_succ, List.flatten_cons, act_append_of _ (act_eval x a ha), ih,
      succ_nsmul', add_assoc]

/-- **Section 3 (trade-off), periodicity.** In an undoable CRDT with finitely many states there is
`k ≥ 1` such that every action is undone by performing it `k - 1` more times:
`s · aᵏ = s` whenever `s · a ok`. -/
theorem finite_states_periodic (C : UndoableCRDT.{u, v}) [Finite C.S] :
    ∃ k, 0 < k ∧ ∀ (s : C.S) (a : List C.P), C.toOpSystem.Ok s a →
      C.toOpSystem.act s (List.replicate k a).flatten = some s := by
  have : Finite (C.G C.s0) := Finite.of_equiv _ C.stateEquiv.symm
  refine ⟨AddMonoid.exponent (C.G C.s0),
    Nat.pos_of_ne_zero AddMonoid.exponent_ne_zero_of_finite, fun s a ha => ?_⟩
  have ha0 := ok_s0_of_ok C.comm C.undo C.reachable ha
  have hs : eval C.s0 (C.stateEquiv.symm s) = s := by
    rw [← stateEquiv_apply, Equiv.apply_symm_apply]
  rw [← hs, act_eval_repeat C _ a ha0, AddMonoid.exponent_nsmul_eq_zero, add_zero]

/-- **Section 3, the trade-off.** For any CRDT, one of the following holds: some operation is
not undoable; there are infinitely many states; or all operations are cyclic, undoing themselves
after `k` iterations for a common `k ≥ 1`. -/
theorem tradeoff (C : CRDT.{u, v}) :
    ¬ C.toOpSystem.Undoable ∨ Infinite C.toOpSystem.S ∨
      ∃ k, 0 < k ∧ ∀ s p, C.toOpSystem.Ok s [p] →
        C.toOpSystem.act s (List.replicate k p) = some s := by
  by_cases hu : C.toOpSystem.Undoable
  · rcases finite_or_infinite C.toOpSystem.S with hfin | hinf
    · right; right
      obtain ⟨k, hk, h⟩ := finite_states_periodic (C := ⟨C, hu⟩)
      refine ⟨k, hk, fun s p hp => ?_⟩
      have := h s [p] hp
      rwa [List.flatten_replicate_singleton] at this
    · exact Or.inr (Or.inl hinf)
  · exact Or.inl hu

end UndoableCRDTs
