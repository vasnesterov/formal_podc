import Mathlib.Order.WellQuasiOrder
import Mathlib.Order.WellFoundedSet

/-!
# Lemma 4.10 is false for infinite subsets (Rado's example)

Lemma 4.10 of the paper (attributed to Higman [20]) states: if `(Q, ≤)` is a well quasi-order,
then `(𝒫(Q), ≤_P)` is a well quasi-order, where `A ≤_P B` iff there is an injective
`φ : A → B` with `a ≤ φ a` for all `a ∈ A`. Higman's result is about *finite* subsets (or finite
sequences); for arbitrary subsets it fails, by Rado's classical example
`Q = {(i, j) | i < j}` with `(i, j) ≤ (k, l)` iff `(i = k ∧ j ≤ l) ∨ j < k`. The paper applies the
lemma to infinite antichains `Xᵢ` in the proof of Theorem 4.12.

Here we prove that Rado's order is a well quasi-order and that the sets
`A k = {(k, l) | k < l}` form an infinite antichain for `≤_P` (even for the weaker Hoare order).
-/

namespace Podc.TVGWaitingExpressivity

/-- `A ≤_P B`: some injection `A → B` dominates the identity. -/
def injDom {Q : Type*} (r : Q → Q → Prop) (A B : Set Q) : Prop :=
  ∃ φ : A → B, Function.Injective φ ∧ ∀ a : A, r a.1 (φ a).1

/-- Rado's quasi-order on pairs `i < j`. -/
def radoLE (x y : {p : ℕ × ℕ // p.1 < p.2}) : Prop :=
  (x.1.1 = y.1.1 ∧ x.1.2 ≤ y.1.2) ∨ x.1.2 < y.1.1

theorem radoLE_refl (x) : radoLE x x := Or.inl ⟨rfl, le_rfl⟩

theorem radoLE_trans {x y z} (h₁ : radoLE x y) (h₂ : radoLE y z) : radoLE x z := by
  have := y.2
  unfold radoLE at *
  omega

theorem radoLE_wqo : WellQuasiOrdered radoLE := by
  intro f
  by_cases h : ∃ m n, m < n ∧ (f m).1.2 < (f n).1.1
  · obtain ⟨m, n, hmn, h⟩ := h
    exact ⟨m, n, hmn, Or.inr h⟩
  · push Not at h
    -- from index 1 on, first coordinates are bounded by `j₀`
    set B := (f 0).1.2
    let g : ℕ → Fin (B + 1) × ℕ := fun m =>
      (⟨(f (m + 1)).1.1, Nat.lt_succ_of_le (h 0 (m + 1) (Nat.succ_pos m))⟩, (f (m + 1)).1.2)
    have hwqo : WellQuasiOrdered fun a b : Fin (B + 1) × ℕ => a.1 = b.1 ∧ a.2 ≤ b.2 :=
      (Finite.wellQuasiOrdered _).prod wellQuasiOrdered_le
    obtain ⟨m, n, hmn, h1, h2⟩ := hwqo g
    exact ⟨m + 1, n + 1, by omega, Or.inl ⟨congrArg Fin.val h1, h2⟩⟩

/-- Rado's antichain: `A k = {(k, l) | k < l}`. -/
def radoSet (k : ℕ) : Set {p : ℕ × ℕ // p.1 < p.2} := {x | x.1.1 = k}

theorem not_injDom_radoSet {k k' : ℕ} (hkk' : k ≠ k') : ¬ injDom radoLE (radoSet k) (radoSet k') := by
  rintro ⟨φ, -, hφ⟩
  let a : radoSet k := ⟨⟨(k, k + k' + 1), by simp only; omega⟩, rfl⟩
  have h := hφ a
  have hk' : (φ a).1.1.1 = k' := (φ a).2
  have ha1 : a.1.1.1 = k := rfl
  have ha2 : a.1.1.2 = k + k' + 1 := rfl
  unfold radoLE at h
  omega

/-- **Lemma 4.10 of [CFGSY'12] is false** (as stated, for arbitrary subsets): Rado's
quasi-order is a well quasi-order, but `≤_P` on its subsets is not (it has an infinite antichain,
so the sequence of its members has no good pair). -/
theorem lemma_4_10_false :
    ∃ (Q : Type) (r : Q → Q → Prop), (∀ x, r x x) ∧ (∀ x y z, r x y → r y z → r x z) ∧
      WellQuasiOrdered r ∧ ¬ WellQuasiOrdered (injDom r) := by
  refine ⟨_, radoLE, radoLE_refl, fun _ _ _ => radoLE_trans, radoLE_wqo, fun h => ?_⟩
  obtain ⟨m, n, hmn, hr⟩ := h radoSet
  exact not_injDom_radoSet hmn.ne hr

end Podc.TVGWaitingExpressivity
