import Cslib.Foundations.Data.Finset.SumUpdate

-- CSLib candidate: Cslib/Foundations/Data/Finset/SumUpdate.lean (append to the existing file)

/-!
# Sums and counts after changing one value: the "agrees off one point" forms

Additions to `Cslib/Foundations/Data/Finset/SumUpdate.lean`. A step of a distributed algorithm
changes the local state of one process only, so potentials and counters over all processes change
by the contribution of that process alone. The existing file phrases this through
`Function.update`; here the new function is only known to agree with the old one off a point.

## Main statements

* `Finset.sum_add_eq_sum_add_of_eq_off`, `Fintype.sum_add_eq_sum_add_of_eq_off`: if `g` agrees
  with `f` outside `a`, then `∑ g + f a = ∑ f + g a`;
* `Fintype.card_filter_add_ite_eq_of_eq_off`: the counting form, for two predicates that agree
  outside `a`;
* `Finset.sum_update_self_add`, `Fintype.sum_update_self_add`: increasing the value at one point by
  `b` increases the sum by `b`.
-/

open Finset

namespace Finset

variable {α M : Type*} [AddCommMonoid M]

/-- If `g` agrees with `f` on `s` outside `a ∈ s`, then `∑ g + f a = ∑ f + g a`. -/
theorem sum_add_eq_sum_add_of_eq_off {s : Finset α} {f g : α → M} {a : α} (ha : a ∈ s)
    (h : ∀ x ∈ s, x ≠ a → g x = f x) : ∑ x ∈ s, g x + f a = ∑ x ∈ s, f x + g a := by
  classical
  rw [← add_sum_erase _ g ha, ← add_sum_erase _ f ha,
    sum_congr rfl fun x hx => h x (mem_of_mem_erase hx) (ne_of_mem_erase hx)]
  ac_rfl

/-- Increasing the value of `f` at `a ∈ s` by `b` increases `∑ x ∈ s, f x` by `b`. -/
theorem sum_update_self_add [DecidableEq α] {s : Finset α} {a : α} (ha : a ∈ s) (f : α → M)
    (b : M) : ∑ x ∈ s, Function.update f a (f a + b) x = ∑ x ∈ s, f x + b := by
  rw [sum_update_of_mem ha, sdiff_singleton_eq_erase, ← add_sum_erase _ _ ha]
  ac_rfl

end Finset

namespace Fintype

variable {α M : Type*} [Fintype α] [AddCommMonoid M]

/-- If `g` agrees with `f` outside `a`, then `∑ g + f a = ∑ f + g a`. -/
theorem sum_add_eq_sum_add_of_eq_off {f g : α → M} (a : α) (h : ∀ x, x ≠ a → g x = f x) :
    ∑ x, g x + f a = ∑ x, f x + g a :=
  Finset.sum_add_eq_sum_add_of_eq_off (mem_univ a) fun x _ => h x

/-- Counting form of `Fintype.sum_add_eq_sum_add_of_eq_off`: if the predicates `p` (before) and `q`
(after) agree outside `a`, then `#{x | q x} + [p a] = #{x | p x} + [q a]`. -/
theorem card_filter_add_ite_eq_of_eq_off {p q : α → Prop} [DecidablePred p] [DecidablePred q]
    (a : α) (h : ∀ x, x ≠ a → (q x ↔ p x)) :
    #{x | q x} + (if p a then 1 else 0) = #{x | p x} + (if q a then 1 else 0) := by
  simp only [card_filter]
  exact sum_add_eq_sum_add_of_eq_off a fun x hx => if_congr (h x hx) rfl rfl

/-- Increasing the value of `f` at `a` by `b` increases `∑ x, f x` by `b`. -/
theorem sum_update_self_add [DecidableEq α] (f : α → M) (a : α) (b : M) :
    ∑ x, Function.update f a (f a + b) x = ∑ x, f x + b :=
  Finset.sum_update_self_add (mem_univ a) f b

end Fintype
