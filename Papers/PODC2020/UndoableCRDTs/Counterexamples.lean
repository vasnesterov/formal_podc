import Papers.PODC2020.UndoableCRDTs.Main

/-!
# Sharpness remarks (Dolan, PODC 2020)

1. **Axiom 1 must include `p = q`.** The paper applies Commutativity with `p = q` ("any valid
   action can be done twice", Fact 2). This is essential: the nonnegative counter `nnCounter`
   (states `ℕ`, `dec` only applies in nonzero states) satisfies Axiom 1 for all *distinct*
   `p ≠ q`, Axiom 2, finiteness and reachability, but it is not equivalent to *any* undoable
   CRDT (in particular, to no tuple of counters): `nnCounter_not_equiv`. Under the paper's
   Axiom 1 it is not a CRDT at all (`nnCounter_not_commutative`).
2. **Dead operations.** The definitions allow a primitive operation that applies in no state.
   Section 3 says "all operations are always valid"; this holds only for operations that apply
   in *some* state (`all_operations_valid`). `deadOp` is an undoable CRDT with an operation that
   never applies (`deadOp_not_valid`).
-/

namespace UndoableCRDTs

open OpSystem UndoableCRDT

/-- The nonnegative counter: states `ℕ`; `inc` always applies, `dec` only in nonzero states. -/
abbrev nnCounter : OpSystem.{0, 0} where
  S := ℕ
  P := CounterOp
  s0 := 0
  app
    | .inc, n => some (n + 1)
    | .dec, 0 => none
    | .dec, n + 1 => some n

/-- Axiom 1 restricted to distinct operations. -/
def OpSystem.CommutativeDistinct (C : OpSystem.{u, v}) : Prop :=
  ∀ s p q, p ≠ q → C.Ok s [p] → C.Ok s [q] →
    C.Ok s [p, q] ∧ C.Ok s [q, p] ∧ C.act s [p, q] = C.act s [q, p]

lemma nnCounter_finite : Finite nnCounter.P := inferInstanceAs (Finite CounterOp)

lemma nnCounter_reachable : nnCounter.Reachable := by
  intro n
  refine ⟨List.replicate n .inc, ?_⟩
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.replicate_succ', act_append_of _ ih]
    rfl

lemma nnCounter_commutativeDistinct : nnCounter.CommutativeDistinct := by
  rintro s (_ | _) (_ | _) hpq hp hq
  · exact absurd rfl hpq
  · cases s with
    | zero => obtain ⟨t, ht⟩ := hq; cases ht
    | succ n => exact ⟨⟨n + 1, rfl⟩, ⟨n + 1, rfl⟩, rfl⟩
  · cases s with
    | zero => obtain ⟨t, ht⟩ := hp; cases ht
    | succ n => exact ⟨⟨n + 1, rfl⟩, ⟨n + 1, rfl⟩, rfl⟩
  · exact absurd rfl hpq

lemma nnCounter_undoable : nnCounter.Undoable := by
  rintro s (_ | _) hp
  · exact ⟨[.dec], rfl⟩
  · cases s with
    | zero => obtain ⟨t, ht⟩ := hp; cases ht
    | succ n => exact ⟨[.inc], rfl⟩

/-- The nonnegative counter violates Axiom 1 with `p = q = dec` in state `1`. -/
lemma nnCounter_not_commutative : ¬ nnCounter.Commutative := by
  intro h
  obtain ⟨⟨t, ht⟩, -⟩ := h 1 .dec .dec ⟨0, rfl⟩ ⟨0, rfl⟩
  cases ht

/-- Net displacement of a counter action. -/
def disp (w : List CounterOp) : ℤ := (w.map (CounterOp.val (A := ℤ))).sum

lemma nnCounter_act (w : List CounterOp) (n k : ℕ) (h : nnCounter.act n w = some k) :
    (k : ℤ) = n + disp w := by
  induction w generalizing n with
  | nil => cases h; simp [disp]
  | cons p w ih =>
    rcases p with _ | _
    · have := ih (n + 1) (by rwa [act_cons_of (t := n + 1) _ rfl] at h)
      simp only [disp, List.map_cons, List.sum_cons] at this ⊢
      rw [this]; simp only [CounterOp.val]; push_cast; ring
    · cases n with
      | zero => cases h
      | succ n =>
        have := ih n (by rwa [act_cons_of (t := n) _ rfl] at h)
        simp only [disp, List.map_cons, List.sum_cons] at this ⊢
        rw [this]; simp only [CounterOp.val]; push_cast; ring

/-- **The `p = q` case of Axiom 1 is essential.** The nonnegative counter satisfies Axiom 1 for
distinct operations and Axiom 2, but it is not equivalent to any undoable CRDT; in particular it
is not equivalent to a tuple of counters. -/
theorem nnCounter_not_equiv (T : UndoableCRDT.{u, v}) :
    IsEmpty (CRDTEquiv nnCounter T.toOpSystem) := by
  refine ⟨fun E => ?_⟩
  have hφ0 : E.φ.symm T.s0 = 0 := E.φ.symm_apply_eq.2 E.map_s0.symm
  -- every operation of `T` that applies somewhere has nonnegative displacement under `ψ'`
  have step : ∀ s' p' t', T.toOpSystem.app p' s' = some t' →
      E.φ.symm s' ≤ E.φ.symm t' := by
    intro s' p' t' h
    obtain ⟨u, hu⟩ := ok_s0_of_ok T.comm T.undo T.reachable (s := s') (a := [p'])
      ⟨t', by simpa using h⟩
    rw [act_singleton] at hu
    have h0 := nnCounter_act _ _ _ (E.map_app' _ _ _ hu)
    have h1 := nnCounter_act _ _ _ (E.map_app' _ _ _ h)
    rw [hφ0] at h0
    have : (0 : ℤ) ≤ disp (E.ψ' p') := by have := (E.φ.symm u).cast_nonneg (α := ℤ); omega
    have h2 : ((E.φ.symm s' : ℕ) : ℤ) ≤ ((E.φ.symm t' : ℕ) : ℤ) := by omega
    exact_mod_cast h2
  have steps : ∀ (w : List T.P) (s' t' : T.S), T.toOpSystem.act s' w = some t' →
      E.φ.symm s' ≤ E.φ.symm t' := by
    intro w
    induction w with
    | nil => intro s' t' h; cases h; exact le_rfl
    | cons p w ih =>
      intro s' t' h
      rw [act_cons] at h
      cases hp : T.toOpSystem.app p s' with
      | none => rw [hp] at h; cases h
      | some r =>
        rw [hp] at h
        exact (step _ _ _ hp).trans (ih _ _ h)
  -- hence every operation leaves `φ⁻¹` unchanged (it can be undone)
  have stepEq : ∀ s' p' t', T.toOpSystem.app p' s' = some t' → E.φ.symm t' = E.φ.symm s' := by
    intro s' p' t' h
    obtain ⟨qs, hqs⟩ := T.undo s' p' ⟨t', by simpa using h⟩
    rw [act_cons_of _ h] at hqs
    exact le_antisymm (steps _ _ _ hqs) (step _ _ _ h)
  have stepsEq : ∀ (w : List T.P) (s' t' : T.S), T.toOpSystem.act s' w = some t' →
      E.φ.symm t' = E.φ.symm s' := by
    intro w
    induction w with
    | nil => intro s' t' h; cases h; rfl
    | cons p w ih =>
      intro s' t' h
      rw [act_cons] at h
      cases hp : T.toOpSystem.app p s' with
      | none => rw [hp] at h; cases h
      | some r =>
        rw [hp] at h
        exact (ih _ _ h).trans (stepEq _ _ _ hp)
  obtain ⟨w, hw⟩ := T.reachable (E.φ (1 : ℕ))
  have := stepsEq w _ _ hw
  rw [Equiv.symm_apply_apply, hφ0] at this
  exact absurd this one_ne_zero

/-- An undoable CRDT with one state and one primitive operation that never applies. -/
def deadOp : UndoableCRDT.{0, 0} where
  toOpSystem := { S := Unit, P := Unit, s0 := (), app := fun _ _ => none }
  finite := inferInstanceAs (Finite Unit)
  reachable := fun _ => ⟨[], rfl⟩
  comm := fun _ _ _ ⟨_, h⟩ _ => by cases h
  undo := fun _ _ ⟨_, h⟩ => by cases h

/-- "All operations are always valid" (Section 3) fails literally for operations that never
apply. -/
theorem deadOp_not_valid : ¬ deadOp.toOpSystem.Ok () [()] := by
  rintro ⟨_, h⟩
  cases h

end UndoableCRDTs
