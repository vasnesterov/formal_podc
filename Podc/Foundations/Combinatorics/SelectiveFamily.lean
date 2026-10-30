import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Algebra.Field.ZMod

-- CSLib candidate: Cslib/Foundations/Combinatorics/SelectiveFamily.lean

/-!
# Families selecting a single element of every nonempty set

A family `F : ι → Finset α` *selects* every nonempty set if for every nonempty `P ⊆ α` some
member `F i` meets `P` in exactly one element. (In radio-network terminology this is an
`(n, n)`-*selective* family; it is weaker than being `(n, n)`-*strongly* selective, which asks that
*every* element of `P` be isolated by some member.)

We prove that such a family has at least `|α|` members, by a parity argument over `ZMod 2`:
if `|ι| < |α|`, the linear map `z ↦ (∑_{v ∈ F i} z v)_i` from `(ZMod 2)^α` to `(ZMod 2)^ι` has a
nonzero kernel vector `z`; its support `P` meets every `F i` in an even number of elements.

This is the counting core of lower bounds for deterministic contention resolution with advice
(e.g. Gilbert–Newport–Vaidya–Weaver, PODC 2021).

## Main statements

* `Cslib.even_card_inter_of_ker`: the parity step.
* `Cslib.card_le_of_forall_exists_card_inter_eq_one`: `|α| ≤ |ι|`.
-/

namespace Cslib

open Finset

variable {α ι : Type*} [Fintype α] [DecidableEq α] [Fintype ι]

/-- The `ZMod 2`-linear map sending `z` to the parities `∑_{v ∈ F i} z v`. -/
noncomputable def parityMap (F : ι → Finset α) : (α → ZMod 2) →ₗ[ZMod 2] (ι → ZMod 2) where
  toFun z i := ∑ v ∈ F i, z v
  map_add' z w := by ext i; simp [Finset.sum_add_distrib]
  map_smul' c z := by ext i; simp [Finset.mul_sum]

omit [Fintype ι] in
/-- If `z` is in the kernel of `parityMap F`, its support meets each `F i` in an even number of
points. -/
theorem even_card_inter_of_ker (F : ι → Finset α) (z : α → ZMod 2) (hz : parityMap F z = 0)
    (i : ι) : Even (F i ∩ univ.filter (fun v => z v ≠ 0)).card := by
  have h0 : ∑ v ∈ F i, z v = 0 := congrFun hz i
  have hz1 : ∀ v, z v ≠ 0 → z v = 1 := fun v hv => by
    have : ∀ x : ZMod 2, x ≠ 0 → x = 1 := by decide
    exact this _ hv
  have : ∑ v ∈ F i, z v = ((F i ∩ univ.filter (fun v => z v ≠ 0)).card : ZMod 2) := by
    rw [← Finset.sum_filter_ne_zero, Finset.card_eq_sum_ones, Nat.cast_sum]
    refine Finset.sum_congr ?_ ?_
    · ext v; simp
    · intro v hv
      simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and] at hv
      simp [hz1 v hv.2]
  rw [this] at h0
  exact (ZMod.natCast_eq_zero_iff_even).1 h0

/-- **A family selecting one element of every nonempty set has at least `|α|` members.**
If for every nonempty `P ⊆ α` some `F i` satisfies `|F i ∩ P| = 1`, then `|α| ≤ |ι|`. -/
theorem card_le_of_forall_exists_card_inter_eq_one (F : ι → Finset α)
    (h : ∀ P : Finset α, P.Nonempty → ∃ i, (F i ∩ P).card = 1) :
    Fintype.card α ≤ Fintype.card ι := by
  by_contra hlt
  push Not at hlt
  have hker : (parityMap F).ker ≠ ⊥ :=
    LinearMap.ker_ne_bot_of_finrank_lt (K := ZMod 2) (f := parityMap F)
      (by simpa [Module.finrank_fintype_fun_eq_card] using hlt)
  obtain ⟨z, hzk, hz0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  have hne : (univ.filter (fun v => z v ≠ 0)).Nonempty := by
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty, Finset.filter_eq_empty_iff] at hemp
    exact hz0 (funext fun v => by simpa using hemp (mem_univ v))
  obtain ⟨i, hi⟩ := h _ hne
  have := even_card_inter_of_ker F z hzk i
  rw [hi] at this
  exact absurd this (by decide)

end Cslib
