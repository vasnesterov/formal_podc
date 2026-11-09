import Mathlib

/-!
# Routing algebras (Definitions 4.1–4.3 of Rétvári et al., *Compact policy routing*)

We follow the numbering of Chapter 4 of G. Rétvári's D.Sc. dissertation (2020), which reproduces the PODC 2011
paper *Compact policy routing* (Rétvári, Gulyás, Heszberger, Csernai, Bíró) with proofs.

A routing algebra `(W, φ, ⊕, ⪯)` is a totally ordered commutative semigroup with an absorbing maximal element `φ`
(Definition 4.1).  In Lean the order `⪯` is the ambient `LinearOrder` on `W` (smaller = preferred) and `⊕` is the
field `op`.

The *extended* weights `A.Ext = WithBot W` adjoin a neutral element `1 = ⊥` (the weight of the empty path); this
makes `A.Ext` a commutative monoid, so path weights are list products and `w ^ k` is `Monoid.npow`.

Several properties of Definition 4.3 are unsatisfiable when read literally because they quantify over `φ` too
(`φ ≺ w ⊕ φ = φ` is false); we state them for `w ≠ φ` (`IsStrictlyMonotone`, `IsCancellative`, `IsCondensed`) and
record the literal versions and their degeneracy (`not_isStrictlyMonotoneLit`, ...).
-/

namespace Podc.CompactPolicyRouting

universe u

/-- Definition 4.1. A routing algebra `A = (W, φ, ⊕, ⪯)`: `(W, ⊕)` is a commutative semigroup, `⪯` is the linear
order of `W`, and `φ` is absorptive and maximal. -/
structure RoutingAlgebra (W : Type u) [LinearOrder W] where
  /-- Weight composition `⊕`. -/
  op : W → W → W
  op_assoc : ∀ a b c, op (op a b) c = op a (op b c)
  op_comm : ∀ a b, op a b = op b a
  /-- The infinity weight `φ` (untraversable). -/
  phi : W
  /-- Absorptivity: `w ⊕ φ = φ`. -/
  op_phi : ∀ a, op a phi = phi
  /-- Maximality: `w ⪯ φ` (equivalently `w ≺ φ` for `w ≠ φ`). -/
  le_phi : ∀ a, a ≤ phi

namespace RoutingAlgebra

variable {W : Type u} [LinearOrder W] (A : RoutingAlgebra W)

theorem phi_op (a : W) : A.op A.phi a = A.phi := by rw [A.op_comm, A.op_phi]

theorem lt_phi {a : W} (h : a ≠ A.phi) : a < A.phi := lt_of_le_of_ne (A.le_phi a) h

/-! ### Properties (Definitions 4.2, 4.3) -/

/-- Monotonicity (M): `w₁ ⪯ w₂ ⊕ w₁`. -/
def IsMonotone : Prop := ∀ a b : W, a ≤ A.op b a

/-- Isotonicity (I): `w₁ ⪯ w₂ → w₃ ⊕ w₁ ⪯ w₃ ⊕ w₂`. -/
def IsIsotone : Prop := ∀ a b c : W, a ≤ b → A.op c a ≤ A.op c b

/-- Definition 4.2: regular = monotone and isotone. -/
def IsRegular : Prop := A.IsMonotone ∧ A.IsIsotone

/-- Delimited (D): `w₁ ⊕ w₂ ≠ φ` for finite `w₁, w₂`. -/
def IsDelimited : Prop := ∀ a b : W, a ≠ A.phi → b ≠ A.phi → A.op a b ≠ A.phi

/-- Strictly monotone (SM), for finite `w₁`: `w₁ ≺ w₂ ⊕ w₁`. (Definition 4.3 quantifies over all `w₁`, which is
unsatisfiable, see `not_isStrictlyMonotoneLit`.) -/
def IsStrictlyMonotone : Prop := ∀ a b : W, a ≠ A.phi → a < A.op b a

/-- Selective (S): `w₁ ⊕ w₂ ∈ {w₁, w₂}`. -/
def IsSelective : Prop := ∀ a b : W, A.op a b = a ∨ A.op a b = b

/-- Cancellative (N), for finite `w₁`: `w₁ ⊕ w₂ = w₁ ⊕ w₃ → w₂ = w₃`. -/
def IsCancellative : Prop := ∀ a b c : W, a ≠ A.phi → A.op a b = A.op a c → b = c

/-- Condensed (C), on finite weights: `w₁ ⊕ w₂ = w₁ ⊕ w₃`. -/
def IsCondensed : Prop :=
  ∀ a b c : W, a ≠ A.phi → b ≠ A.phi → c ≠ A.phi → A.op a b = A.op a c

/-- Strict monotonicity exactly as printed in Definition 4.3 (for *all* `w₁`). -/
def IsStrictlyMonotoneLit : Prop := ∀ a b : W, a < A.op b a

/-- Cancellativity exactly as printed in Definition 4.3. -/
def IsCancellativeLit : Prop := ∀ a b c : W, A.op a b = A.op a c → b = c

/-- Condensedness exactly as printed in Definition 4.3. -/
def IsCondensedLit : Prop := ∀ a b c : W, A.op a b = A.op a c

/-- Definition 4.3, (SM) as printed is unsatisfiable: take `w₁ = φ`. -/
theorem not_isStrictlyMonotoneLit : ¬ A.IsStrictlyMonotoneLit := fun h => by
  have := h A.phi A.phi
  rw [A.op_phi] at this
  exact lt_irrefl _ this

/-- Definition 4.3, (N) as printed fails in every algebra with a finite weight: take `w₁ = φ`. -/
theorem not_isCancellativeLit {a : W} (ha : a ≠ A.phi) : ¬ A.IsCancellativeLit := fun h =>
  ha (h A.phi a A.phi (by rw [A.phi_op, A.phi_op]))

/-- Definition 4.3, (C) as printed forces every composition to be `φ`. -/
theorem isCondensedLit_iff : A.IsCondensedLit ↔ ∀ a b : W, A.op a b = A.phi := by
  constructor
  · intro h a b; rw [h a b A.phi, A.op_phi]
  · intro h a b c; rw [h, h]

/-- Footnote 7: selectivity implies delimitedness. -/
theorem IsSelective.isDelimited {A : RoutingAlgebra W} (h : A.IsSelective) : A.IsDelimited := by
  intro a b ha hb hab
  rcases h a b with h' | h' <;> rw [h'] at hab <;> contradiction

theorem IsStrictlyMonotone.isMonotone {A : RoutingAlgebra W} (h : A.IsStrictlyMonotone) :
    A.IsMonotone := by
  intro a b
  by_cases ha : a = A.phi
  · subst ha; rw [A.op_phi]
  · exact (h a b ha).le

/-- In a monotone selective algebra, `⊕` is the maximum. -/
theorem op_eq_max {A : RoutingAlgebra W} (hM : A.IsMonotone) (hS : A.IsSelective) (a b : W) :
    A.op a b = max a b := by
  have h1 : a ≤ A.op a b := by rw [A.op_comm]; exact hM a b
  have h2 : b ≤ A.op a b := hM b a
  rcases hS a b with h | h
  · rw [h] at h2 ⊢; exact (max_eq_left h2).symm
  · rw [h] at h1 ⊢; exact (max_eq_right h1).symm

/-! ### Extended weights: adjoining the weight `1 = ⊥` of the empty path -/

/-- Extended weights `W ∪ {1}`, where `1 = ⊥` is the (most preferred) weight of the empty path. -/
def Ext (_A : RoutingAlgebra W) : Type u := WithBot W

instance : LinearOrder A.Ext := inferInstanceAs (LinearOrder (WithBot W))
instance : OrderBot A.Ext := inferInstanceAs (OrderBot (WithBot W))

/-- Embedding of weights into extended weights. -/
def emb (a : W) : A.Ext := (a : WithBot W)

/-- Composition on extended weights. -/
protected def extMul (x y : A.Ext) : A.Ext := Option.merge A.op x y

instance : CommMonoid A.Ext where
  mul := A.extMul
  one := (⊥ : WithBot W)
  mul_assoc x y z := by
    rcases x with _ | x <;> rcases y with _ | y <;> rcases z with _ | z <;>
      simp [HMul.hMul, Mul.mul, RoutingAlgebra.extMul, Option.merge, A.op_assoc] <;> rfl
  one_mul x := by rcases x with _ | x <;> rfl
  mul_one x := by rcases x with _ | x <;> rfl
  mul_comm x y := by
    rcases x with _ | x <;> rcases y with _ | y <;>
      simp [HMul.hMul, Mul.mul, RoutingAlgebra.extMul, Option.merge, A.op_comm] <;> rfl

variable {A}

@[simp] theorem emb_mul_emb (a b : W) : A.emb a * A.emb b = A.emb (A.op a b) := rfl

theorem one_eq_bot : (1 : A.Ext) = ⊥ := rfl

@[simp] theorem emb_le_emb {a b : W} : A.emb a ≤ A.emb b ↔ a ≤ b := WithBot.coe_le_coe

@[simp] theorem emb_lt_emb {a b : W} : A.emb a < A.emb b ↔ a < b := WithBot.coe_lt_coe

@[simp] theorem emb_inj {a b : W} : A.emb a = A.emb b ↔ a = b := WithBot.coe_inj

@[simp] theorem emb_ne_one (a : W) : A.emb a ≠ 1 := WithBot.coe_ne_bot

theorem one_le (x : A.Ext) : 1 ≤ x := bot_le

theorem one_lt_emb (a : W) : (1 : A.Ext) < A.emb a := WithBot.bot_lt_coe a

/-- Every extended weight is `1` or a weight. -/
theorem Ext.cases (x : A.Ext) : x = 1 ∨ ∃ a, x = A.emb a := by
  rcases x with _ | a
  · exact Or.inl rfl
  · exact Or.inr ⟨a, rfl⟩

theorem emb_mul_ne_one (a : W) (x : A.Ext) : A.emb a * x ≠ 1 := by
  rcases Ext.cases x with rfl | ⟨b, rfl⟩
  · rw [mul_one]; exact emb_ne_one a
  · rw [emb_mul_emb]; exact emb_ne_one _

theorem le_emb_phi (x : A.Ext) : x ≤ A.emb A.phi := by
  rcases Ext.cases x with rfl | ⟨a, rfl⟩
  · exact (one_lt_emb _).le
  · exact emb_le_emb.2 (A.le_phi a)

@[simp] theorem mul_emb_phi (x : A.Ext) : x * A.emb A.phi = A.emb A.phi := by
  rcases Ext.cases x with rfl | ⟨a, rfl⟩
  · exact one_mul _
  · rw [emb_mul_emb, A.op_phi]

/-- Monotonicity on extended weights. -/
theorem IsMonotone.le_mul (hM : A.IsMonotone) (x y : A.Ext) : x ≤ y * x := by
  rcases Ext.cases x with rfl | ⟨a, rfl⟩
  · exact one_le _
  rcases Ext.cases y with rfl | ⟨b, rfl⟩
  · rw [one_mul]
  · rw [emb_mul_emb]; exact emb_le_emb.2 (hM a b)

theorem IsMonotone.le_mul' (hM : A.IsMonotone) (x y : A.Ext) : x ≤ x * y := by
  rw [mul_comm]; exact hM.le_mul x y

/-- Isotonicity on extended weights (needs monotonicity for the new element `1`). -/
theorem IsRegular.mul_le_mul_left (hR : A.IsRegular) {x y : A.Ext} (h : x ≤ y) (z : A.Ext) :
    z * x ≤ z * y := by
  rcases Ext.cases z with rfl | ⟨c, rfl⟩
  · simpa using h
  rcases Ext.cases x with rfl | ⟨a, rfl⟩
  · rw [mul_one]; exact hR.1.le_mul' _ _
  rcases Ext.cases y with rfl | ⟨b, rfl⟩
  · exact absurd h (not_le.2 (one_lt_emb a))
  · rw [emb_mul_emb, emb_mul_emb]; exact emb_le_emb.2 (hR.2 a b c (emb_le_emb.1 h))

theorem IsRegular.mul_le_mul (hR : A.IsRegular) {x y x' y' : A.Ext} (h : x ≤ y) (h' : x' ≤ y') :
    x * x' ≤ y * y' :=
  calc x * x' ≤ x * y' := hR.mul_le_mul_left h' x
    _ = y' * x := mul_comm _ _
    _ ≤ y' * y := hR.mul_le_mul_left h y'
    _ = y * y' := mul_comm _ _

/-- Semigroup powers: `spow a k = a ^ (k + 1)` (the paper's `w^(k+1)`, Lemma 4.12). -/
def spow (A : RoutingAlgebra W) (a : W) : ℕ → W
  | 0 => a
  | k + 1 => A.op (A.spow a k) a

theorem emb_pow_succ (a : W) (k : ℕ) : A.emb a ^ (k + 1) = A.emb (A.spow a k) := by
  induction k with
  | zero => simp [spow]
  | succ k ih => rw [pow_succ, ih, emb_mul_emb]; rfl

theorem spow_ne_phi (hD : A.IsDelimited) {a : W} (ha : a ≠ A.phi) (k : ℕ) : A.spow a k ≠ A.phi := by
  induction k with
  | zero => exact ha
  | succ k ih => exact hD _ _ ih ha

theorem spow_add (a : W) (j k : ℕ) : A.spow a (j + k + 1) = A.op (A.spow a j) (A.spow a k) := by
  have h := congrArg (fun x : A.Ext => x) (pow_add (A.emb a) (j + 1) (k + 1))
  simp only [emb_pow_succ, emb_mul_emb] at h
  rw [show j + 1 + (k + 1) = (j + k + 1) + 1 by omega, emb_pow_succ, emb_inj] at h
  exact h

end RoutingAlgebra

end Podc.CompactPolicyRouting
