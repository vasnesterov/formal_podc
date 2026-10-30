import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset

-- CSLib candidate: Cslib/Foundations/Combinatorics/HypergraphRamsey.lean

/-!
# Finite Ramsey theorem for uniform hypergraphs (two colours)

For every `K` (the uniformity) and every `a`, `b` there is an `N` such that, whenever the
`K`-element subsets of a finite set `S` with `|S| ≥ N` are coloured with two colours (`Bool`), there
is an `a`-element subset of `S` all of whose `K`-subsets have colour `false`, or a `b`-element subset
all of whose `K`-subsets have colour `true`.

Mathlib (checked 2026-10) has neither the finite nor the infinite hypergraph Ramsey theorem; CSLib has
the infinite graph (`K = 2`) version in `Cslib.Foundations.Combinatorics.InfiniteGraphRamsey`.

## Main statements

* `Cslib.IsHomogeneous c K Y i`: every `K`-subset of `Y` has colour `i`.
* `Cslib.hypergraph_ramsey`: the asymmetric two-colour finite Ramsey theorem for `K`-uniform
  hypergraphs.
* `Cslib.exists_homogeneous`: the symmetric form (a monochromatic `M`-subset).
* `Cslib.exists_homogeneous_lt`, `Cslib.exists_homogeneous_finite`: finitely many colours (colours
  `< k` in `ℕ`, or any `Finite` type), by induction on the number of colours.

## Proof

Induction on `K`, then on `a + b`, via the classical bound
`R_{K+1}(a + 1, b + 1) ≤ R_K(R_{K+1}(a, b + 1), R_{K+1}(a + 1, b)) + 1`: remove one point `x` and
colour the `K`-sets `Z` by the colour of `Z ∪ {x}`.
-/

namespace Cslib

open Finset

variable {α : Type*}

/-- `Y` is homogeneous of colour `i` for the colouring `c` of `K`-sets: every `K`-subset of `Y` has
colour `i`. -/
def IsHomogeneous (c : Finset α → Bool) (K : ℕ) (Y : Finset α) (i : Bool) : Prop :=
  ∀ Z ⊆ Y, Z.card = K → c Z = i

lemma IsHomogeneous.mono {c : Finset α → Bool} {K : ℕ} {Y Y' : Finset α} {i : Bool}
    (h : IsHomogeneous c K Y i) (hY : Y' ⊆ Y) : IsHomogeneous c K Y' i :=
  fun Z hZ hc => h Z (hZ.trans hY) hc

variable [DecidableEq α]

/-- The extension step of the Ramsey induction: if all `K`-sets `Z ⊆ A` satisfy
`c (insert x Z) = i` and `Y ⊆ A` is `i`-homogeneous for `(K + 1)`-sets, then so is
`insert x Y`. -/
private lemma isHomogeneous_insert {c : Finset α → Bool} {K : ℕ} {A Y : Finset α} {x : α}
    {i : Bool} (hA : IsHomogeneous (fun Z => c (insert x Z)) K A i) (hYA : Y ⊆ A)
    (hY : IsHomogeneous c (K + 1) Y i) : IsHomogeneous c (K + 1) (insert x Y) i := by
  intro Z hZ hcard
  by_cases hxZ : x ∈ Z
  · have h1 : Z.erase x ⊆ A := by
      intro z hz
      have hzx := Finset.ne_of_mem_erase hz
      have := hZ (Finset.mem_of_mem_erase hz)
      rcases Finset.mem_insert.1 this with h | h
      · exact absurd h hzx
      · exact hYA h
    have h2 : (Z.erase x).card = K := by
      rw [Finset.card_erase_of_mem hxZ, hcard]; rfl
    have := hA _ h1 h2
    simpa [Finset.insert_erase hxZ] using this
  · refine hY Z ?_ hcard
    intro z hz
    rcases Finset.mem_insert.1 (hZ hz) with h | h
    · exact absurd (h ▸ hz) hxZ
    · exact h

/-- **Finite Ramsey theorem** for `K`-uniform hypergraphs, two colours, asymmetric form. -/
theorem hypergraph_ramsey (K a b : ℕ) :
    ∃ N, ∀ {α : Type*} [DecidableEq α] (c : Finset α → Bool) (S : Finset α), N ≤ S.card →
      (∃ Y ⊆ S, Y.card = a ∧ IsHomogeneous c K Y false) ∨
      (∃ Y ⊆ S, Y.card = b ∧ IsHomogeneous c K Y true) := by
  induction K generalizing a b with
  | zero =>
    refine ⟨a + b, fun c S hS => ?_⟩
    cases hc : c ∅
    · obtain ⟨Y, hYS, hY⟩ := Finset.exists_subset_card_eq (show a ≤ S.card by omega)
      exact Or.inl ⟨Y, hYS, hY, fun Z _ hZ => by rw [Finset.card_eq_zero.1 hZ, hc]⟩
    · obtain ⟨Y, hYS, hY⟩ := Finset.exists_subset_card_eq (show b ≤ S.card by omega)
      exact Or.inr ⟨Y, hYS, hY, fun Z _ hZ => by rw [Finset.card_eq_zero.1 hZ, hc]⟩
  | succ K ih =>
    suffices H : ∀ n a b, a + b = n → ∃ N, ∀ {α : Type _} [DecidableEq α] (c : Finset α → Bool)
        (S : Finset α), N ≤ S.card →
        (∃ Y ⊆ S, Y.card = a ∧ IsHomogeneous c (K + 1) Y false) ∨
        (∃ Y ⊆ S, Y.card = b ∧ IsHomogeneous c (K + 1) Y true) from H _ a b rfl
    intro n
    induction n with
    | zero =>
      intro a b hab
      refine ⟨0, fun c S _ => Or.inl ⟨∅, Finset.empty_subset _, by simp; omega, ?_⟩⟩
      intro Z hZ hc
      rw [Finset.subset_empty.1 hZ] at hc
      simp at hc
    | succ n ihn =>
      intro a b hab
      rcases a with _ | a
      · refine ⟨0, fun c S _ => Or.inl ⟨∅, Finset.empty_subset _, rfl, ?_⟩⟩
        intro Z hZ hc
        rw [Finset.subset_empty.1 hZ] at hc
        simp at hc
      rcases b with _ | b
      · refine ⟨0, fun c S _ => Or.inr ⟨∅, Finset.empty_subset _, rfl, ?_⟩⟩
        intro Z hZ hc
        rw [Finset.subset_empty.1 hZ] at hc
        simp at hc
      obtain ⟨N1, hN1⟩ := ihn a (b + 1) (by omega)
      obtain ⟨N2, hN2⟩ := ihn (a + 1) b (by omega)
      obtain ⟨N0, hN0⟩ := ih N1 N2
      refine ⟨N0 + 1, fun {β} _ c S hS => ?_⟩
      obtain ⟨x, hx⟩ : S.Nonempty := Finset.card_pos.1 (by omega)
      have hS' : N0 ≤ (S.erase x).card := by rw [Finset.card_erase_of_mem hx]; omega
      have hxS' : x ∉ S.erase x := Finset.notMem_erase x S
      have hsub : insert x (S.erase x) ⊆ S := by rw [Finset.insert_erase hx]
      rcases hN0 (fun Z => c (insert x Z)) (S.erase x) hS' with
        ⟨A, hAS, hAc, hA⟩ | ⟨B, hBS, hBc, hB⟩
      · rcases hN1 c A hAc.ge with ⟨Y, hYA, hYc, hY⟩ | hright
        · refine Or.inl ⟨insert x Y, ?_, ?_, isHomogeneous_insert hA hYA hY⟩
          · exact (Finset.insert_subset_insert x (hYA.trans hAS)).trans hsub
          · rw [Finset.card_insert_of_notMem (fun h => hxS' (hAS (hYA h))), hYc]
        · obtain ⟨Y, hYA, hYc, hY⟩ := hright
          exact Or.inr ⟨Y, hYA.trans (hAS.trans (Finset.erase_subset x S)), hYc, hY⟩
      · rcases hN2 c B hBc.ge with hleft | ⟨Y, hYB, hYc, hY⟩
        · obtain ⟨Y, hYB, hYc, hY⟩ := hleft
          exact Or.inl ⟨Y, hYB.trans (hBS.trans (Finset.erase_subset x S)), hYc, hY⟩
        · refine Or.inr ⟨insert x Y, ?_, ?_, isHomogeneous_insert hB hYB hY⟩
          · exact (Finset.insert_subset_insert x (hYB.trans hBS)).trans hsub
          · rw [Finset.card_insert_of_notMem (fun h => hxS' (hBS (hYB h))), hYc]

/-- **Finite Ramsey theorem**, symmetric form: for every `K` and `M` there is `N` such that every
two-colouring of the `K`-subsets of a set `S` with `|S| ≥ N` admits a monochromatic `M`-subset. -/
theorem exists_homogeneous (K M : ℕ) :
    ∃ N, ∀ {α : Type*} [DecidableEq α] (c : Finset α → Bool) (S : Finset α), N ≤ S.card →
      ∃ Y ⊆ S, Y.card = M ∧ ∃ i, IsHomogeneous c K Y i := by
  obtain ⟨N, hN⟩ := hypergraph_ramsey K M M
  refine ⟨N, fun c S hS => ?_⟩
  rcases hN c S hS with ⟨Y, h1, h2, h3⟩ | ⟨Y, h1, h2, h3⟩
  · exact ⟨Y, h1, h2, _, h3⟩
  · exact ⟨Y, h1, h2, _, h3⟩

/-- **Finite Ramsey theorem**, `k` colours (colours `< k` in `ℕ`): for every `K`, `M` and `k` there
is `N` such that every colouring of the `K`-subsets of a set `S` with `|S| ≥ N` by colours `< k`
admits an `M`-subset all of whose `K`-subsets have the same colour. Derived from the two-colour
case by induction on `k`. -/
theorem exists_homogeneous_lt (K M k : ℕ) :
    ∃ N, ∀ {α : Type*} [DecidableEq α] (c : Finset α → ℕ) (S : Finset α), N ≤ S.card →
      (∀ Z ⊆ S, Z.card = K → c Z < k) →
      ∃ Y ⊆ S, Y.card = M ∧ ∃ i, ∀ Z ⊆ Y, Z.card = K → c Z = i := by
  induction k with
  | zero =>
    refine ⟨M + K, fun c S hS hc => ?_⟩
    obtain ⟨Z, hZS, hZ⟩ := Finset.exists_subset_card_eq (show K ≤ S.card by omega)
    exact absurd (hc Z hZS hZ) (Nat.not_lt_zero _)
  | succ k ih =>
    obtain ⟨N₁, hN₁⟩ := ih
    obtain ⟨N, hN⟩ := exists_homogeneous K (max N₁ M)
    refine ⟨N, fun {α} _ c S hS hc => ?_⟩
    obtain ⟨Y, hYS, hYc, i, hY⟩ := hN (fun Z => decide (c Z = k)) S hS
    cases i with
    | true =>
      obtain ⟨Y', hY'Y, hY'c⟩ := Finset.exists_subset_card_eq (show M ≤ Y.card by omega)
      exact ⟨Y', hY'Y.trans hYS, hY'c, k, fun Z hZ hZc => by
        simpa using hY Z (hZ.trans hY'Y) hZc⟩
    | false =>
      obtain ⟨Y', hY'Y, hY'c, j, hj⟩ := hN₁ c Y (by omega) fun Z hZ hZc => by
        have h1 := hc Z (hZ.trans hYS) hZc
        have h2 : ¬ c Z = k := by simpa using hY Z hZ hZc
        omega
      exact ⟨Y', hY'Y.trans hYS, hY'c, j, hj⟩

/-- **Finite Ramsey theorem**, finitely many colours: for every `K`, `M` and every finite type `β`
of colours there is `N` such that every colouring `c : Finset α → β` of the `K`-subsets of a set `S`
with `|S| ≥ N` admits an `M`-subset all of whose `K`-subsets have the same colour. -/
theorem exists_homogeneous_finite (K M : ℕ) (β : Type*) [Finite β] :
    ∃ N, ∀ {α : Type*} [DecidableEq α] (c : Finset α → β) (S : Finset α), N ≤ S.card →
      ∃ Y ⊆ S, Y.card = M ∧ ∃ i, ∀ Z ⊆ Y, Z.card = K → c Z = i := by
  obtain ⟨k, ⟨e⟩⟩ := Finite.exists_equiv_fin β
  obtain ⟨N, hN⟩ := exists_homogeneous_lt K M k
  refine ⟨N, fun {α} _ c S hS => ?_⟩
  obtain ⟨Y, hYS, hYc, j, hj⟩ := hN (fun Z => (e (c Z) : ℕ)) S hS fun Z _ _ => (e (c Z)).isLt
  refine ⟨Y, hYS, hYc, ?_⟩
  by_cases h : ∃ Z ⊆ Y, Z.card = K
  · obtain ⟨Z₀, hZ₀, hZ₀c⟩ := h
    refine ⟨c Z₀, fun Z hZ hZc => e.injective (Fin.ext ?_)⟩
    rw [hj Z hZ hZc, hj Z₀ hZ₀ hZ₀c]
  · exact ⟨c ∅, fun Z hZ hZc => absurd ⟨Z, hZ, hZc⟩ h⟩

end Cslib
