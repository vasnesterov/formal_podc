import Mathlib
import Papers.PODC2013.ByzantineVectorConsensus.Gamma
import Podc.Foundations.Combinatorics.Convex.Tverberg

/-!
# Tverberg's theorem (Theorem 2 of Vaidya–Garg, PODC 2013)

* `tverberg` — **Tverberg's theorem**: for `r ≥ 1`, any family of at least `(d + 1)(r - 1) + 1`
  points `y : ι → E` of a `d`-dimensional real vector space (repetitions allowed) admits a partition
  `part : ι → Fin r` into `r` nonempty parts whose convex hulls have a common point.
* `tverberg_point_mem_GammaOn`, `GammaOn_nonempty_of_tverberg` — the paper's derivation of Lemma 1
  (`Γ ≠ ∅`) from Tverberg's theorem with `r = f + 1` parts (`Gamma.lean` proves Lemma 1 independently
  via Helly's theorem).

## Proof route

The proof is shared library code (`Podc/Foundations/Combinatorics/Convex/Tverberg.lean`):
Sarkaria's lifting plus the colorful Carathéodory theorem (`exists_colorful_mem_convexHull`),
see `Convex.tverberg_partition`.
-/

open Finset Module

namespace ByzantineVectorConsensus

section Tverberg

variable {ι E : Type*} [Fintype ι] [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]

/-- **Tverberg's theorem** (Tverberg 1966; Theorem 2 of the paper). Any `(d + 1)(r - 1) + 1`
(or more) points `y i` of a `d`-dimensional real vector space, `r ≥ 1`, can be partitioned into
`r` nonempty parts whose convex hulls have a common point. Points may repeat (multiset version).
The proof (Sarkaria's lifting + colorful Carathéodory) is the shared `Convex.tverberg_partition`. -/
theorem tverberg {r : ℕ} (hr : 0 < r) (y : ι → E)
    (hcard : (finrank ℝ E + 1) * (r - 1) < Fintype.card ι) :
    ∃ part : ι → Fin r, (∀ j, ∃ i, part i = j) ∧
      (⋂ j, convexHull ℝ (y '' {i | part i = j})).Nonempty :=
  Convex.tverberg_partition hr y hcard

end Tverberg

section Gamma

variable {ι E : Type*} [Fintype ι] [AddCommGroup E] [Module ℝ E]

/-- A Tverberg point of a partition into `f + 1` parts lies in `Γ`: every sub-multiset of size
`n - f` misses at most `f` indices, hence contains a whole part. (This is how the paper proves
Lemma 1 from Tverberg's theorem.) -/
theorem tverberg_point_mem_GammaOn {f : ℕ} (y : ι → E) (part : ι → Fin (f + 1)) {z : E}
    (hz : ∀ j, z ∈ convexHull ℝ (y '' {i | part i = j})) : z ∈ GammaOn f Finset.univ y := by
  classical
  refine mem_GammaOn.2 fun T _ hT => ?_
  have hTc : (Finset.univ \ T).card ≤ f := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ T), hT]
    omega
  obtain ⟨j, hj⟩ : ∃ j, j ∉ (Finset.univ \ T).image part := by
    by_contra h
    push Not at h
    have := Finset.card_le_card (fun j _ => h j : Finset.univ ⊆ (Finset.univ \ T).image part)
    have := Finset.card_image_le (s := Finset.univ \ T) (f := part)
    simp at *
    omega
  refine convexHull_mono (Set.image_mono fun i (hi : part i = j) => ?_) (hz j)
  by_contra hiT
  exact hj (Finset.mem_image.2 ⟨i, by simpa using hiT, hi⟩)

/-- **Lemma 1** of the paper, derived (as in the paper) from Tverberg's theorem: for at least
`(d + 1) f + 1` points, `Γ` is nonempty. -/
theorem GammaOn_nonempty_of_tverberg [FiniteDimensional ℝ E] {f : ℕ} (y : ι → E)
    (hcard : (finrank ℝ E + 1) * f < Fintype.card ι) : (GammaOn f Finset.univ y).Nonempty := by
  obtain ⟨part, -, z, hz⟩ := tverberg (r := f + 1) (Nat.succ_pos f) y (by simpa using hcard)
  exact ⟨z, tverberg_point_mem_GammaOn y part (Set.mem_iInter.1 hz)⟩

end Gamma

end ByzantineVectorConsensus
