import Papers.PODC2025.RendezvousLabeledLine.Line
import Cslib.Foundations.Data.Nat.LogStar

/-!
# Early-stopping coloured ruling sets on the line: the interface used by Algorithm 5

Algorithm 5 only uses the *output* of `ES-ColPathRulingSet(R)` (Algorithm 3) and the fact that a
node `u` commits to it within `κ₃ R log* ℓ(u)` rounds (Lemma 3.5). An `R`-round LOCAL algorithm
is the same as a map from `R`-balls to outputs, so we record Lemma 3.5 as a *rule*: a membership
predicate `inS R ℓ` and a colouring `col R ℓ` of the infinite line labelled by `ℓ` such that

* `inS R ℓ` is an `(R, R - 1)`-ruling set of `ℤ` (`packing`, `covering`),
* `col R ℓ` takes values in `[17]` and is proper on `G^{9R-1}[S]` (`proper`),
* (early stopping, Lemma 3.5 (1)–(3)) every node `u` *knows* some ruling-set node within distance
  `R - 1` and its colour (`knows`, `knows_exists`), and what it knows is determined by the labels
  within distance `κ R log* ℓ(u)` of `u` (`local_`); it need not know *all* ruling-set nodes within
  `R - 1` (nodes of larger labels may join the ruling set after `u` committed),
* the rule commutes with the isometries of the line (`inS_frame`, `col_frame`): it is computed
  from the labelled line, which has no orientation and no origin.

Here `log*` is `lstar n = Nat.logStar n + 1`, the paper's convention `log* x ≥ 1` (with the
floor of `log₂` inside, which changes it by at most an additive constant).
-/

namespace Podc.RendezvousLabeledLine

open Function

/-- The paper's `log*` (Section 2.1): at least `1`. -/
def lstar (n : ℕ) : ℕ := Nat.logStar n + 1

lemma one_le_lstar (n : ℕ) : 1 ≤ lstar n := by simp [lstar]

/-- An early-stopping coloured `(R, R-1)`-ruling-set rule with commitment time `κ R log* ℓ(u)`
(the object computed by Algorithm 3, Lemma 3.5). `knows R ℓ u w` means that, when `u` commits to
its output, it knows that `w` is a ruling-set node (within distance `R - 1`), together with its
colour. -/
structure ColRuling (κ : ℕ) where
  /-- membership in the ruling set of parameter `R` -/
  inS : ℕ → (ℤ → ℕ) → ℤ → Prop
  /-- colour of a ruling-set node -/
  col : ℕ → (ℤ → ℕ) → ℤ → ℕ
  /-- ruling-set nodes known to a node when it commits -/
  knows : ℕ → (ℤ → ℕ) → ℤ → ℤ → Prop
  col_lt : ∀ (R : ℕ) ℓ w, col R ℓ w < 17
  inS_frame : ∀ (R : ℕ) ℓ v ε i, inS R (ℓ ∘ frame v ε) i ↔ inS R ℓ (frame v ε i)
  col_frame : ∀ (R : ℕ) ℓ v ε i, col R (ℓ ∘ frame v ε) i = col R ℓ (frame v ε i)
  packing : ∀ R : ℕ, 1 ≤ R → ∀ ℓ, Injective ℓ → ∀ w w', inS R ℓ w → inS R ℓ w' → w ≠ w' →
    (R : ℤ) ≤ |w - w'|
  proper : ∀ R : ℕ, 1 ≤ R → ∀ ℓ, Injective ℓ → ∀ w w', inS R ℓ w → inS R ℓ w' → w ≠ w' →
    |w - w'| ≤ 9 * (R : ℤ) - 1 → col R ℓ w ≠ col R ℓ w'
  knows_spec : ∀ R : ℕ, 1 ≤ R → ∀ ℓ, Injective ℓ → ∀ u w, knows R ℓ u w →
    |w - u| ≤ (R : ℤ) - 1 ∧ inS R ℓ w
  /-- (Lemma 3.5 (3)) every node knows a ruling-set node within distance `R - 1` -/
  knows_exists : ∀ R : ℕ, 1 ≤ R → ∀ ℓ, Injective ℓ → ∀ u, ∃ w, knows R ℓ u w
  /-- (Lemma 3.5 (1)–(2)) what `u` knows is determined by its `κ R log* ℓ(u)`-ball -/
  local_ : ∀ R : ℕ, 1 ≤ R → ∀ ℓ ℓ', Injective ℓ → Injective ℓ' → ∀ u,
    (∀ x, |x - u| ≤ ((κ * R * lstar (ℓ u) : ℕ) : ℤ) → ℓ' x = ℓ x) →
    ∀ w, (knows R ℓ' u w ↔ knows R ℓ u w) ∧ (knows R ℓ u w → col R ℓ' w = col R ℓ w)

namespace ColRuling

variable {κ : ℕ} (Rl : ColRuling κ)

/-- Covering property of the ruling set. -/
lemma covering (R : ℕ) (hR : 1 ≤ R) (ℓ : ℤ → ℕ) (hℓ : Injective ℓ) (u : ℤ) :
    ∃ w, |w - u| ≤ (R : ℤ) - 1 ∧ Rl.inS R ℓ w := by
  obtain ⟨w, hw⟩ := Rl.knows_exists R hR ℓ hℓ u
  exact ⟨w, Rl.knows_spec R hR ℓ hℓ u w hw⟩

end ColRuling

end Podc.RendezvousLabeledLine
