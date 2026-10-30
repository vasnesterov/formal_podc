import Mathlib

/-!
# Lemmas 5 and 6: enumerating a totally ordered set with finite lower sets

Lemma 5 of [Monti–Camaioni–Roman]: if every lower set `X|≤x` of a totally ordered set `X` is finite,
"a strictly increasing sequence `z` exists such that `∀ x ∈ X, ∃ n, z_n = x`".
Lemma 6: two strictly increasing sequences `z, z'` with `∀ x ∈ X, ∃ n, z_n = x` and
`∀ x ∈ X, ∃ n', z'_{n'} = x` are equal.

Read literally (sequences indexed by `ℕ`; only `X ⊆ range z` required), both are false:
* Lemma 5 fails for every finite nonempty `X` (a strictly increasing `ℕ`-indexed sequence of elements
  of `X` would be injective) — `lemma5_literal_false`;
* Lemma 6 fails because nothing forces `z` and `z'` to stay inside `X` — `lemma6_literal_false`.

The intended statements (clear from the proofs: `φ` is "a bijection between `X` and
`{n ≤ |X|}`", and "we have `z_n, z'_n ∈ X`"; in the application, Corollary 3, the sequences do stay
in `X` by Lemma 18) are true: sequences are finite or infinite, and `range z = X`. We prove them
separately for infinite `X` (sequences `ℕ → α`) and finite `X` (sorted lists).
-/

namespace Podc.FastByzantineTOB

open Set

variable {α : Type*} [LinearOrder α]

/-- Lemma 5 of [Monti–Camaioni–Roman], infinite case: an infinite set all of whose lower sets are
finite is the range of a strictly increasing sequence. -/
theorem lemma5_infinite (X : Set α) (hfin : ∀ x ∈ X, (X ∩ Iic x).Finite) (hX : X.Infinite) :
    ∃ z : ℕ → α, StrictMono z ∧ range z = X := by
  -- `φ x = |X|<x|`, as in the paper
  let φ : X → ℕ := fun x => (X ∩ Iio x.1).ncard
  have hφ : StrictMono φ := by
    intro x y hxy
    apply Set.ncard_lt_ncard _ ((hfin y y.2).subset (inter_subset_inter_right _ Iio_subset_Iic_self))
    refine ⟨inter_subset_inter_right _ (Iio_subset_Iio hxy.le), fun h => ?_⟩
    have := h ⟨x.2, (hxy : x.1 < y.1)⟩
    exact lt_irrefl _ this.2
  have : Infinite X := hX.to_subtype
  have : Infinite (range φ) := (Set.infinite_range_of_injective hφ.injective).to_subtype
  let e : X ≃o range φ := hφ.orderIso φ
  let z : ℕ → α := fun n => ((e.symm (Nat.Subtype.orderIsoOfNat (range φ) n)) : α)
  refine ⟨z, ?_, ?_⟩
  · intro m n hmn
    exact Subtype.coe_lt_coe.mpr (e.symm.strictMono ((Nat.Subtype.orderIsoOfNat _).strictMono hmn))
  · ext x
    constructor
    · rintro ⟨n, rfl⟩; exact Subtype.prop _
    · intro hx
      obtain ⟨n, hn⟩ := (Nat.Subtype.orderIsoOfNat (range φ)).surjective (e ⟨x, hx⟩)
      exact ⟨n, by simp [z, hn]⟩

/-- Lemma 5, finite case: a finite set is the set of entries of a strictly increasing list. -/
theorem lemma5_finite (X : Set α) (hX : X.Finite) :
    ∃ l : List α, l.SortedLT ∧ ∀ x, x ∈ l ↔ x ∈ X :=
  ⟨hX.toFinset.sort (· ≤ ·), Finset.sortedLT_sort _, fun x => by simp⟩

/-- Lemma 6 of [Monti–Camaioni–Roman], infinite case: two strictly increasing sequences with the
same range are equal. -/
theorem lemma6_infinite {z z' : ℕ → α} (hz : StrictMono z) (hz' : StrictMono z')
    (h : range z = range z') : z = z' :=
  (hz.range_inj_of_wellFoundedLT hz').mp h

/-- Lemma 6, finite case: two strictly increasing lists with the same entries are equal. -/
theorem lemma6_finite {l l' : List α} (hl : l.SortedLT) (hl' : l'.SortedLT)
    (h : ∀ x, x ∈ l ↔ x ∈ l') : l = l' :=
  hl.eq_of_mem_iff hl' h

/-- Lemma 5 read literally is false: for the one-point set there is no strictly increasing
`ℕ`-indexed sequence of its elements. -/
theorem lemma5_literal_false :
    ¬ ∀ (X : Set Unit), (∀ x ∈ X, (X ∩ Iic x).Finite) →
      ∃ z : ℕ → X, StrictMono z ∧ ∀ x ∈ X, ∃ n, (z n : Unit) = x := by
  intro h
  obtain ⟨z, hz, -⟩ := h univ (fun _ _ => toFinite _)
  exact absurd (hz.injective (Subsingleton.elim (z 0) (z 1))) (by decide)

/-- Lemma 6 read literally is false: `X = {0} ⊆ ℕ`, `z n = n`, `z' n = 2n`. -/
theorem lemma6_literal_false :
    ∃ (X : Set ℕ) (z z' : ℕ → ℕ), StrictMono z ∧ StrictMono z' ∧
      (∀ x ∈ X, ∃ n, z n = x) ∧ (∀ x ∈ X, ∃ n, z' n = x) ∧ z ≠ z' := by
  refine ⟨{0}, id, (2 * ·), strictMono_id, fun a b h => by simp only; omega, ?_, ?_, ?_⟩
  · rintro x rfl; exact ⟨0, rfl⟩
  · rintro x rfl; exact ⟨0, rfl⟩
  · intro h; have := congrFun h 1; simp at this

end Podc.FastByzantineTOB
