import Papers.PODC2025.RendezvousLabeledLine.Rule

/-!
# Rules on the labelled line: locality and equivariance

A *rule* `F : (ℤ → ℕ) → ℤ → α` assigns a value to every node of the line labelled by `ℓ`. In the
LOCAL model (unbounded messages), a `T`-round deterministic algorithm is the same as a rule whose
value at `v` only depends on the labels within distance `T` of `v` (`IsLocal F T`). Algorithms on
the unoriented labelled line commute with the isometries of `ℤ` (`IsEquivar F`).
-/

namespace Podc.RendezvousLabeledLine

open Function

/-- The value of `F` at `v` is determined by the labels within distance `ρ` of `v`. -/
def IsLocal {α : Sort*} (F : (ℤ → ℕ) → ℤ → α) (ρ : ℕ) : Prop :=
  ∀ ℓ ℓ', Injective ℓ → Injective ℓ' → ∀ v, (∀ x, |x - v| ≤ (ρ : ℤ) → ℓ' x = ℓ x) → F ℓ' v = F ℓ v

/-- `F` commutes with the isometries `i ↦ v + ε i` of the line. -/
def IsEquivar {α : Sort*} (F : (ℤ → ℕ) → ℤ → α) : Prop :=
  ∀ ℓ v ε i, F (ℓ ∘ frame v ε) i = F ℓ (frame v ε i)

lemma IsLocal.mono {α : Sort*} {F : (ℤ → ℕ) → ℤ → α} {ρ ρ' : ℕ} (h : IsLocal F ρ) (hρ : ρ ≤ ρ') :
    IsLocal F ρ' := fun ℓ ℓ' hℓ hℓ' v hv =>
  h ℓ ℓ' hℓ hℓ' v fun x hx => hv x (hx.trans (by exact_mod_cast hρ))

/-- Nodes of `S` are pairwise at distance at least `p`. -/
def Packed (S : ℤ → Prop) (p : ℕ) : Prop := ∀ u w, S u → S w → u ≠ w → (p : ℤ) ≤ |u - w|

end Podc.RendezvousLabeledLine
