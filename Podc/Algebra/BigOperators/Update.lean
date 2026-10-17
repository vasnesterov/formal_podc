import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Order.BigOperators.Group.Finset

-- CSLib candidate: Mathlib/Algebra/Order/BigOperators/Group/Finset.lean

/-!
# Sums over a finite type after changing one value

Potential-function arguments sum a quantity over all processes and change it at one process per
step. This file provides the corresponding facts about `∑ x, f x` when `f` is changed at a single
point:

* `Fintype.sum_update_add` — `∑ x, update f a b x + f a = ∑ x, f x + b`;
* `Fintype.sum_le_sum_of_eq_off`, `Fintype.sum_lt_sum_of_eq_off` — if `g` agrees with `f` outside
  `a`, then the sums compare as `g a` and `f a`;
* `Fintype.sum_lt_sum_of_update` — decreasing one value decreases the sum;
* `Fintype.sum_lt_sum_of_le_add` — a large drop at one point outweighs bounded increases elsewhere.
-/

open Finset

namespace Fintype

variable {α M : Type*} [Fintype α]

section AddCommMonoid

variable [AddCommMonoid M] [DecidableEq α]

/-- Changing `f` at `a` to `b` changes the sum by replacing `f a` with `b`. -/
theorem sum_update_add (f : α → M) (a : α) (b : M) :
    ∑ x, Function.update f a b x + f a = ∑ x, f x + b := by
  rw [Finset.sum_update_of_mem (Finset.mem_univ a), Finset.sdiff_singleton_eq_erase,
    ← Finset.add_sum_erase _ _ (Finset.mem_univ a)]
  ac_rfl

end AddCommMonoid

section Ordered

variable [AddCommMonoid M] [PartialOrder M] [IsOrderedCancelAddMonoid M]

/-- If `g` agrees with `f` outside `a` and `g a ≤ f a`, then `∑ g ≤ ∑ f`. -/
theorem sum_le_sum_of_eq_off {f g : α → M} (a : α) (h : ∀ x, x ≠ a → g x = f x)
    (ha : g a ≤ f a) : ∑ x, g x ≤ ∑ x, f x :=
  Finset.sum_le_sum fun x _ => by
    by_cases hx : x = a
    · exact hx ▸ ha
    · exact (h x hx).le

/-- If `g` agrees with `f` outside `a` and `g a < f a`, then `∑ g < ∑ f`. -/
theorem sum_lt_sum_of_eq_off {f g : α → M} (a : α) (h : ∀ x, x ≠ a → g x = f x)
    (ha : g a < f a) : ∑ x, g x < ∑ x, f x :=
  Finset.sum_lt_sum (fun x _ => by
    by_cases hx : x = a
    · exact hx ▸ ha.le
    · exact (h x hx).le) ⟨a, Finset.mem_univ _, ha⟩

/-- Decreasing the value at one point decreases the sum. -/
theorem sum_lt_sum_of_update [DecidableEq α] {f : α → M} {a : α} {b : M} (h : b < f a) :
    ∑ x, Function.update f a b x < ∑ x, f x :=
  sum_lt_sum_of_eq_off a (fun _ hx => Function.update_of_ne hx _ _) (by simpa using h)

/-- If `g` exceeds `f` by at most `c` outside `a`, and at `a` drops by more than the total possible
increase `(card α - 1) • c` elsewhere, then `∑ g < ∑ f`. -/
theorem sum_lt_sum_of_le_add {f g : α → M} {c : M} (a : α) (h : ∀ x, x ≠ a → g x ≤ f x + c)
    (ha : g a + (Fintype.card α - 1) • c < f a) : ∑ x, g x < ∑ x, f x := by
  classical
  rw [← Finset.add_sum_erase _ g (Finset.mem_univ a),
    ← Finset.add_sum_erase _ f (Finset.mem_univ a)]
  have h₁ : ∑ x ∈ univ.erase a, g x ≤ ∑ x ∈ univ.erase a, f x + (Fintype.card α - 1) • c := by
    rw [← Finset.card_univ, ← Finset.card_erase_of_mem (Finset.mem_univ a), ← Finset.sum_const,
      ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun x hx => h x (Finset.ne_of_mem_erase hx)
  calc g a + ∑ x ∈ univ.erase a, g x
      ≤ g a + (∑ x ∈ univ.erase a, f x + (Fintype.card α - 1) • c) := by gcongr
    _ = g a + (Fintype.card α - 1) • c + ∑ x ∈ univ.erase a, f x := by ac_rfl
    _ < f a + ∑ x ∈ univ.erase a, f x := add_lt_add_of_lt_of_le ha le_rfl

end Ordered

end Fintype
