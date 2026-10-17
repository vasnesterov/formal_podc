import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.Group.Units.Equiv

-- CSLib candidate: Cslib/Foundations/Algebra/BigOperators/Translate.lean (Mathlib candidate:
-- `Mathlib/Algebra/BigOperators/Group/Finset/Defs.lean`, next to `Equiv.prod_comp`)

/-!
# Products and sums over a finite group are translation invariant

For a finite group `G` (e.g. the ring positions `ZMod n` or `Fin n`), reindexing by a translation
`x ↦ x * a` does not change a product over all of `G`; additively, `∑ x, f (x + a) = ∑ x, f x`
(sums of per-node quantities around a ring, shifted by one position).

## Main statements

* `Fintype.prod_mul_right_eq_self`, `Fintype.sum_add_right_eq_self`.
-/

namespace Fintype

variable {G M : Type*} [Group G] [Fintype G] [CommMonoid M]

/-- A product over a finite group is invariant under right translation of the index. -/
@[to_additive /-- A sum over a finite additive group is invariant under right translation of the
index. -/]
theorem prod_mul_right_eq_self (f : G → M) (a : G) : ∏ x, f (x * a) = ∏ x, f x :=
  Equiv.prod_comp (Equiv.mulRight a) f

end Fintype
