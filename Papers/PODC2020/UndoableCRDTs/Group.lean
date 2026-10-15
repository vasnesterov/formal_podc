import Papers.PODC2020.UndoableCRDTs.Actions

/-!
# The group of actions (Dolan, PODC 2020, Sections 2.4–2.6)

For an undoable CRDT and a state `s`, `G s = P*/≡ₛ` is the set of actions applicable in `s`,
modulo `a ≡ₛ b :↔ s · a = s · b`. It is an abelian group under concatenation (Section 2.4),
finitely generated (Section 2.5). We write it additively.

* `UndoableCRDT.eval s : G s → S`, `[a] ↦ s · a`, is injective; for `s = s₀` it is a bijection
  (`stateEquiv`), because all states are reachable.
* **Proposition 3** (`prop3`): CRDTs with isomorphic groups of actions at `s₀` are equivalent.
-/

namespace UndoableCRDTs

namespace OpSystem

variable (C : OpSystem.{u, v})

/-- Actions that apply in state `s`. -/
def OkAction (s : C.S) : Type v := {a : List C.P // C.Ok s a}

/-- The partial equivalence `≡ₛ`, restricted to the actions applicable in `s`. -/
def actSetoid (s : C.S) : Setoid (C.OkAction s) where
  r a b := C.act s a.1 = C.act s b.1
  iseqv := ⟨fun _ => rfl, Eq.symm, Eq.trans⟩

end OpSystem

namespace UndoableCRDT

open OpSystem

variable (C : UndoableCRDT.{u, v})

/-- States of an undoable CRDT. -/
abbrev S : Type u := C.toOpSystem.S
/-- Primitive operations of an undoable CRDT. -/
abbrev P : Type v := C.toOpSystem.P
/-- Initial state of an undoable CRDT. -/
abbrev s0 : C.S := C.toOpSystem.s0

/-- **The group of actions** `G_s = P*/≡ₛ` (Section 2.4). -/
def G (s : C.S) : Type v := Quotient (C.toOpSystem.actSetoid s)

variable {C}

/-- The class `[a] ∈ G_s` of an action `a` with `s · a ok`. -/
def G.mk {s : C.S} (a : List C.P) (h : C.toOpSystem.Ok s a) : C.G s :=
  Quotient.mk _ ⟨a, h⟩

lemma G.ind {s : C.S} {motive : C.G s → Prop} (h : ∀ a ha, motive (G.mk a ha)) (x : C.G s) :
    motive x :=
  Quotient.ind (fun a => h a.1 a.2) x

lemma G.mk_eq_mk {s : C.S} {a b : List C.P} {ha : C.toOpSystem.Ok s a}
    {hb : C.toOpSystem.Ok s b} : G.mk a ha = G.mk b hb ↔ C.toOpSystem.act s a = C.toOpSystem.act s b :=
  Quotient.eq (r := C.toOpSystem.actSetoid s)

variable {s : C.S}

instance : Add (C.G s) :=
  ⟨Quotient.map₂ (fun a b => ⟨a.1 ++ b.1, (prop1 C.comm a.2 b.2).1⟩)
    (fun a₁ b₁ h₁ a₂ b₂ h₂ => fact1 C.comm a₁.2 b₁.2 a₂.2 b₂.2 h₁ h₂)⟩

instance : Zero (C.G s) := ⟨G.mk [] (ok_nil s)⟩

lemma G.mk_add_mk (a b : List C.P) (ha : C.toOpSystem.Ok s a) (hb : C.toOpSystem.Ok s b) :
    G.mk a ha + G.mk b hb = G.mk (a ++ b) (prop1 C.comm ha hb).1 := rfl

lemma G.zero_def : (0 : C.G s) = G.mk [] (ok_nil s) := rfl

instance : AddCommMonoid (C.G s) where
  add_assoc x y z := by
    induction x using G.ind; induction y using G.ind; induction z using G.ind
    simp only [G.mk_add_mk, List.append_assoc]
  zero_add x := by
    induction x using G.ind; rfl
  add_zero x := by
    induction x using G.ind
    simp only [G.zero_def, G.mk_add_mk, List.append_nil]
  add_comm x y := by
    induction x using G.ind with | h a ha => induction y using G.ind with | h b hb =>
    exact G.mk_eq_mk.2 (prop1 C.comm ha hb).2.2
  nsmul := nsmulRec

/-- A chosen undo `a⁻¹ₛ` of an action `a` (Proposition 2). -/
noncomputable def undoAction (a : C.toOpSystem.OkAction s) : List C.P :=
  Classical.choose (prop2 C.undo a.2)

lemma act_undoAction (a : C.toOpSystem.OkAction s) :
    C.toOpSystem.act s (a.1 ++ undoAction a) = some s :=
  Classical.choose_spec (prop2 C.undo a.2)

lemma ok_undoAction (a : C.toOpSystem.OkAction s) : C.toOpSystem.Ok s (undoAction a) :=
  fact4 C.comm a.2 (act_undoAction a)

lemma mk_add_undo (a : C.toOpSystem.OkAction s) :
    G.mk a.1 a.2 + G.mk (undoAction a) (ok_undoAction a) = 0 := by
  rw [G.mk_add_mk, G.zero_def, G.mk_eq_mk, act_undoAction]; rfl

noncomputable instance : Neg (C.G s) :=
  ⟨Quotient.lift (fun a => G.mk (undoAction a) (ok_undoAction a)) (fun a b h => by
    have hab : G.mk a.1 a.2 = G.mk b.1 b.2 := Quotient.sound h
    have ha := mk_add_undo a
    have hb := mk_add_undo b
    calc G.mk (undoAction a) (ok_undoAction a)
        = G.mk (undoAction a) (ok_undoAction a) +
            (G.mk b.1 b.2 + G.mk (undoAction b) (ok_undoAction b)) := by rw [hb, add_zero]
      _ = (G.mk a.1 a.2 + G.mk (undoAction a) (ok_undoAction a)) +
            G.mk (undoAction b) (ok_undoAction b) := by rw [hab]; abel
      _ = _ := by rw [ha, zero_add])⟩

/-- `G_s` is an abelian group (Section 2.4). -/
noncomputable instance : AddCommGroup (C.G s) :=
  { (inferInstance : AddCommMonoid (C.G s)) with
    neg_add_cancel := fun x => by
      induction x using G.ind with | h a ha =>
      rw [add_comm]
      exact mk_add_undo ⟨a, ha⟩
    zsmul := zsmulRec }

/-- **Section 2.5: `G_s` is finitely generated**, by the classes of the primitive operations
that apply in `s`. -/
instance : AddGroup.FG (C.G s) := by
  have := C.finite
  rw [AddGroup.fg_iff]
  refine ⟨Set.range (fun p : {p : C.P // C.toOpSystem.Ok s [p]} => G.mk [p.1] p.2),
    ?_, Set.finite_range _⟩
  rw [eq_top_iff]
  intro x _
  induction x using G.ind with | h a ha =>
  induction a with
  | nil => exact AddSubgroup.zero_mem _
  | cons p b ih =>
    have hp : C.toOpSystem.Ok s [p] := Ok.of_append_left (b := b) ha
    have hb : C.toOpSystem.Ok s b := fact6 C.comm C.undo (a := [p]) ha
    have : G.mk (p :: b) ha = G.mk [p] hp + G.mk b hb := rfl
    rw [this]
    exact AddSubgroup.add_mem _ (AddSubgroup.subset_closure ⟨⟨p, hp⟩, rfl⟩) (ih hb (AddSubgroup.mem_top _))

/-- `[a] ↦ s · a`. -/
noncomputable def eval (s : C.S) : C.G s → C.S :=
  Quotient.lift (fun a => (C.toOpSystem.act s a.1).get (ok_iff_isSome.1 a.2))
    (fun a b h => Option.some_injective _ (by simp only [Option.some_get]; exact h))

lemma act_eq_eval (a : List C.P) (ha : C.toOpSystem.Ok s a) :
    C.toOpSystem.act s a = some (eval s (G.mk a ha)) :=
  (Option.some_get _).symm

lemma eval_zero : eval s (0 : C.G s) = s := by
  apply Option.some_injective
  rw [G.zero_def, ← act_eq_eval]; rfl

lemma eval_injective : Function.Injective (eval s) := by
  intro x y h
  induction x using G.ind with | h a ha => induction y using G.ind with | h b hb =>
  exact G.mk_eq_mk.2 (by rw [act_eq_eval a ha, act_eq_eval b hb, h])

/-- Applying an action `b` to `eval s x` corresponds to adding `[b]` in `G_s`. -/
lemma act_eval (x : C.G s) (b : List C.P) (hb : C.toOpSystem.Ok s b) :
    C.toOpSystem.act (eval s x) b = some (eval s (x + G.mk b hb)) := by
  induction x using G.ind with | h a ha =>
  rw [G.mk_add_mk, ← act_eq_eval, act_append_of _ (act_eq_eval a ha)]

/-- Applying a representative of `y` to `eval s x` gives `eval s (x + y)`. -/
lemma act_eval_out (x y : C.G s) :
    C.toOpSystem.act (eval s x) (Quotient.out y).1 = some (eval s (x + y)) := by
  rw [act_eval x _ (Quotient.out y).2]
  congr 3
  exact Quotient.out_eq y

lemma eval_surjective : Function.Surjective (eval C.s0) := by
  intro t
  obtain ⟨a, ha⟩ := C.reachable t
  exact ⟨G.mk a (ok_of_act ha), Option.some_injective _ (by rw [← act_eq_eval a (ok_of_act ha), ha])⟩

variable (C) in
/-- The states of an undoable CRDT are in bijection with its group of actions at `s₀`. -/
noncomputable def stateEquiv : C.G C.s0 ≃ C.S :=
  Equiv.ofBijective (eval C.s0) ⟨eval_injective, eval_surjective⟩

lemma stateEquiv_apply (x : C.G C.s0) : C.stateEquiv x = eval C.s0 x := rfl

lemma stateEquiv_symm_s0 : C.stateEquiv.symm C.s0 = 0 :=
  C.stateEquiv.symm_apply_eq.2 eval_zero.symm

/-! ### Proposition 3 -/

variable {C₁ : UndoableCRDT.{u₁, v₁}} {C₂ : UndoableCRDT.{u₂, v₂}}

/-- The implementation `ψ : P₁ → P₂*` induced by a group isomorphism (proof of
Proposition 3): `p ↦` a representative of `f [p]` (and `ε` if `p` never applies). -/
noncomputable def transportOp (f : C₁.G C₁.s0 ≃+ C₂.G C₂.s0) (p : C₁.P) : List C₂.P :=
  open Classical in
  if h : C₁.toOpSystem.Ok C₁.s0 [p] then (Quotient.out (f (G.mk [p] h))).1 else []

lemma transport_map_app (f : C₁.G C₁.s0 ≃+ C₂.G C₂.s0) (s : C₁.S) (p : C₁.P) (t : C₁.S)
    (h : C₁.toOpSystem.app p s = some t) :
    C₂.toOpSystem.act (C₂.stateEquiv (f (C₁.stateEquiv.symm s))) (transportOp f p) =
      some (C₂.stateEquiv (f (C₁.stateEquiv.symm t))) := by
  have hp : C₁.toOpSystem.Ok C₁.s0 [p] :=
    ok_s0_of_ok C₁.comm C₁.undo C₁.reachable (s := s) ⟨t, by simpa using h⟩
  set x := C₁.stateEquiv.symm s with hx
  have hs : eval C₁.s0 x = s := by rw [← stateEquiv_apply, hx, Equiv.apply_symm_apply]
  have ht : C₁.stateEquiv.symm t = x + G.mk [p] hp := by
    rw [Equiv.symm_apply_eq, stateEquiv_apply]
    apply Option.some_injective
    rw [← act_eval, hs, act_singleton, h]
  rw [ht, map_add, transportOp, dite_eq_left hp, stateEquiv_apply, stateEquiv_apply, act_eval_out]

/-- **Proposition 3.** If the groups of actions `G_{s₀}` and `G_{s₀'}` of two undoable CRDTs
are isomorphic, then the CRDTs are equivalent. -/
theorem prop3 (f : C₁.G C₁.s0 ≃+ C₂.G C₂.s0) :
    Nonempty (CRDTEquiv C₁.toOpSystem C₂.toOpSystem) :=
  ⟨{ φ := (C₁.stateEquiv.symm.trans f.toEquiv).trans C₂.stateEquiv
     ψ := transportOp f
     ψ' := transportOp f.symm
     map_s0 := by
       simp only [Equiv.trans_apply, stateEquiv_symm_s0, AddEquiv.toEquiv_eq_coe,
         EquivLike.coe_coe, map_zero, stateEquiv_apply, eval_zero]
     map_app := fun s p t h => transport_map_app f s p t h
     map_app' := fun s' p' t' h => transport_map_app f.symm s' p' t' h }⟩

end UndoableCRDT

end UndoableCRDTs
