import Papers.PODC2020.SSLERegular.EulerDynamics
import Mathlib.GroupTheory.Perm.Cycle.Basic

/-!
# The ring-protocol hypothesis and the legitimate configurations of the repaired SS-EulerCycle

* `RingStepOn R τ`: one interaction of the ring protocol `R` on a **directed ring** given by a
  cyclic permutation `τ` of a finite set `X` (initiator `x`, responder its successor `τ x`).
* `RingSpec R`: `R` solves SSLE on every directed ring with at least three nodes, in the
  reachability ("probability 1 / global fairness") sense: from every ring configuration a ring
  configuration is reachable that has exactly one leader and whose outputs never change. This is
  the property of the Ring-Protocol of [11] that Chen–Chen use as a black box; phrasing it for all
  cyclic permutations `(X, τ)` instead of `Fin N` with `i ↦ i + 1` is equivalent (isomorphism
  invariance) and avoids index arithmetic.
* `Good`: the valid output-stable configurations we construct: coherent skeleton, a single
  virtual ring (an Euler cycle), ring part valid-stable, and a legitimate token configuration of
  SS-Token (one token; bits `b…b ¬b…¬b` from the ring leader on).
-/

set_option linter.unusedSectionVars false

open Finset

namespace SSLERegular

universe u

variable {RS : Type*}

/-- One ring-protocol interaction on the directed ring `(X, τ)`. -/
def RingStepOn (R : RingProtocol RS) {X : Type*} [DecidableEq X] (τ : Equiv.Perm X)
    (c c' : X → RS) : Prop :=
  ∃ x, ∃ o ∈ R.δ (c x) (c (τ x)), c' = Function.update (Function.update c x o.1) (τ x) o.2

/-- Valid output-stable ring configuration. -/
def RingValidOn (R : RingProtocol RS) {X : Type*} [DecidableEq X] (τ : Equiv.Perm X)
    (c : X → RS) : Prop :=
  (∀ c', Relation.ReflTransGen (RingStepOn R τ) c c' → ∀ x, R.lead (c' x) = R.lead (c x)) ∧
    ∃! x, R.lead (c x) = true

/-- **Hypothesis on the Ring-Protocol** (black box of the paper, [11]): SSLE on every directed
ring with at least three nodes. -/
def RingSpec (R : RingProtocol RS) : Prop :=
  ∀ (X : Type u) [Fintype X] [DecidableEq X] (τ : Equiv.Perm X), (∀ x y, τ.SameCycle x y) →
    3 ≤ Fintype.card X → ∀ c : X → RS,
      ∃ c', Relation.ReflTransGen (RingStepOn R τ) c c' ∧ RingValidOn R τ c'

lemma RingValidOn.step {R : RingProtocol RS} {X : Type*} [DecidableEq X] {τ : Equiv.Perm X}
    {c c' : X → RS} (h : RingValidOn R τ c) (hs : RingStepOn R τ c c') : RingValidOn R τ c' := by
  obtain ⟨h1, x, hx, hu⟩ := h
  have hl : ∀ y, R.lead (c' y) = R.lead (c y) := h1 c' (Relation.ReflTransGen.single hs)
  refine ⟨fun c'' h y => ?_, x, by simp only; rw [hl]; exact hx,
    fun y hy => hu y (by simp only at hy ⊢; rw [← hl]; exact hy)⟩
  rw [h1 c'' (Relation.ReflTransGen.head hs h) y, hl]

variable {k : ℕ} {V : Type u} [DecidableEq V] [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The skeleton of a configuration. -/
def skelOf (C : V → EState k RS) : V → Skel k := fun v => skel (C v)

/-- Legitimate SS-Token configuration on the single virtual ring `σ`, counted from the ring
leader `w0`: the token is at position `m` and the bits are `b` up to `m` and `¬b` after. -/
def TokLegit (σ : Equiv.Perm (V × Fin k)) (F : V × Fin k → VNode k RS) (w0 : V × Fin k) : Prop :=
  ∃ m < Fintype.card (V × Fin k), ∃ b : Bool, ∀ t < Fintype.card (V × Fin k),
    (F ((σ ^ t) w0)).token = decide (t = m) ∧ (F ((σ ^ t) w0)).bit = (if t ≤ m then b else !b)

variable (G) in
/-- **Legitimate configurations** of the repaired SS-EulerCycle (Lemma 3.1). -/
def Good (R : RingProtocol RS) (hdeg : ∀ v, G.degree v = 2 * k) (C : V → EState k RS) : Prop :=
  ∃ (hinj : InjCol G (skelOf C)) (hok : EdgeOK G (skelOf C)),
    Base G (skelOf C) C ∧ (∀ w w', (vperm hdeg hinj hok).SameCycle w w') ∧
    RingValidOn R (vperm hdeg hinj hok) (fun w => (vn C w).ringState) ∧
    ∃ w0, R.lead (vn C w0).ringState = true ∧ TokLegit (vperm hdeg hinj hok) (vn C) w0

end SSLERegular
