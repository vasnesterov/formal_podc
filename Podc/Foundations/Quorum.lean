import Mathlib.Data.Set.Card

-- CSLib candidate: Cslib/Foundations/Data/Finset/Quorum.lean

/-!
# Quorum arithmetic

Fault-tolerant protocols for `n` processes with at most `f` faulty ones argue with *quorums*: sets
of processes large enough that any two of them, or any one of them and the set of correct
processes, share a (correct) member. Every such argument is an instance of the inclusion–exclusion
bound `#s + #t ≤ #(s ∩ t) + n` together with "a set larger than the faulty set has a correct
member". This file states these facts once, over `[Fintype α]` (`n = Fintype.card α`) and a
faulty set `F : Finset α` (or `B : Set α`, for models that keep the Byzantine processes in a set).

## Main statements

* `Finset.card_add_card_le_card_inter_add_card_univ`: `#s + #t ≤ #(s ∩ t) + n`.
* `Finset.exists_mem_notMem_of_card_le_of_lt`: a set with more than `f ≥ #F` members has a member
  outside `F`.
* `Finset.exists_mem_inter_notMem_of_card_le`: two sets with `#s + #t > n + f` share a member
  outside `F`.
* `Set.ncard` variants for a faulty set `B : Set α`: `Finset.card_filter_mem_le_ncard`,
  `Finset.exists_mem_notMem_of_ncard_le_of_lt`, `Finset.exists_mem_inter_notMem_of_ncard_le`.
* Threshold regimes (namespace `Cslib.Quorum`): `exists_mem_inter_notMem_of_quorum`
  (`Q`-quorums, `n + f < 2Q`), `exists_mem_inter_notMem_of_three_mul_lt` (`(n - f)`-quorums,
  `3f < n`), `inter_nonempty_of_two_mul_lt` (`(n - f)`-quorums, `2f < n`),
  `inter_nonempty_of_card_le_four_mul_add_one` (`(2f + 1)`-quorums, `n ≤ 4f + 1`),
  `card_sub_two_mul_le_card_inter` (`(n - f)`-quorums meet in `n - 2f` members).
-/

namespace Finset

variable {α : Type*} [DecidableEq α] {s t u F : Finset α} {f q : ℕ}

/-! ### Inclusion–exclusion -/

/-- Two subsets of `u` exceed `u` by at most their intersection: `#s + #t ≤ #(s ∩ t) + #u`. -/
theorem card_add_card_le_card_inter_add_card_of_subset (hs : s ⊆ u) (ht : t ⊆ u) :
    #s + #t ≤ #(s ∩ t) + #u := by
  have h₁ := card_union_add_card_inter s t
  have h₂ := card_le_card (union_subset hs ht)
  omega

omit [DecidableEq α] in
/-- A set with more than `f` members has a member outside any `F` with `#F ≤ f`. -/
theorem exists_mem_notMem_of_card_le_of_lt (hF : #F ≤ f) (hs : f < #s) : ∃ a ∈ s, a ∉ F :=
  exists_mem_notMem_of_card_lt_card (hF.trans_lt hs)

section Fintype

variable [Fintype α]

/-- **Quorum intersection bound**: `#s + #t ≤ #(s ∩ t) + n` for `n = Fintype.card α`. -/
theorem card_add_card_le_card_inter_add_card_univ (s t : Finset α) :
    #s + #t ≤ #(s ∩ t) + Fintype.card α :=
  card_univ (α := α) ▸ card_add_card_le_card_inter_add_card_of_subset (subset_univ s)
    (subset_univ t)

/-- Two sets of total size `> n` intersect. -/
theorem inter_nonempty_of_card_univ_lt_card_add_card (h : Fintype.card α < #s + #t) :
    (s ∩ t).Nonempty :=
  inter_nonempty_of_card_lt_card_add_card (subset_univ s) (subset_univ t) (by simpa using h)

/-- Two sets with `#s + #t > n + f` share a member outside any `F` with `#F ≤ f`. -/
theorem exists_mem_inter_notMem_of_card_le (hF : #F ≤ f) (h : Fintype.card α + f < #s + #t) :
    ∃ a ∈ s, a ∈ t ∧ a ∉ F := by
  have := card_add_card_le_card_inter_add_card_univ s t
  obtain ⟨a, ha, haF⟩ := exists_mem_notMem_of_card_le_of_lt hF (show f < #(s ∩ t) by omega)
  exact ⟨a, (mem_inter.1 ha).1, (mem_inter.1 ha).2, haF⟩

/-! ### Faulty sets given as `Set`s -/

omit [DecidableEq α] in
/-- The members of `s` in `B` are at most `B.ncard`. -/
theorem card_filter_mem_le_ncard (B : Set α) [DecidablePred (· ∈ B)] (s : Finset α) :
    #{a ∈ s | a ∈ B} ≤ B.ncard := by
  rw [← Set.ncard_coe_finset]
  exact Set.ncard_le_ncard (fun a ha => (mem_filter.1 ha).2)

omit [DecidableEq α] in
/-- A set with more than `f` members has a member outside any `B : Set α` with `B.ncard ≤ f`. -/
theorem exists_mem_notMem_of_ncard_le_of_lt {B : Set α} (hB : B.ncard ≤ f) (hs : f < #s) :
    ∃ a ∈ s, a ∉ B := by
  classical
  have := card_filter_mem_le_ncard B s
  obtain ⟨a, ha, haB⟩ := exists_mem_notMem_of_card_le_of_lt (F := {a ∈ s | a ∈ B}) le_rfl
    (show #{a ∈ s | a ∈ B} < #s by omega)
  exact ⟨a, ha, fun h => haB (mem_filter.2 ⟨ha, h⟩)⟩

/-- Two sets with `#s + #t > n + f` share a member outside any `B : Set α` with `B.ncard ≤ f`. -/
theorem exists_mem_inter_notMem_of_ncard_le {B : Set α} (hB : B.ncard ≤ f)
    (h : Fintype.card α + f < #s + #t) : ∃ a ∈ s, a ∈ t ∧ a ∉ B := by
  have := card_add_card_le_card_inter_add_card_univ s t
  obtain ⟨a, ha, haB⟩ := exists_mem_notMem_of_ncard_le_of_lt hB (show f < #(s ∩ t) by omega)
  exact ⟨a, (mem_inter.1 ha).1, (mem_inter.1 ha).2, haB⟩

end Fintype

end Finset

/-! ### Threshold regimes -/

namespace Cslib.Quorum

open Finset

variable {α : Type*} [DecidableEq α] [Fintype α] {s t F : Finset α} {f q : ℕ}

/-- Two `q`-quorums with `n + f < 2q` share a member outside `F`, `#F ≤ f`. -/
theorem exists_mem_inter_notMem_of_quorum (hn : Fintype.card α + f < 2 * q) (hF : #F ≤ f)
    (hs : q ≤ #s) (ht : q ≤ #t) : ∃ a ∈ s, a ∈ t ∧ a ∉ F :=
  exists_mem_inter_notMem_of_card_le hF (by omega)

/-- Two `(n - f)`-quorums with `3f < n` share a member outside `F`, `#F ≤ f`. -/
theorem exists_mem_inter_notMem_of_three_mul_lt (hn : 3 * f < Fintype.card α) (hF : #F ≤ f)
    (hs : Fintype.card α - f ≤ #s) (ht : Fintype.card α - f ≤ #t) : ∃ a ∈ s, a ∈ t ∧ a ∉ F :=
  exists_mem_inter_notMem_of_card_le hF (by omega)

/-- Two `(n - f)`-quorums meet in at least `n - 2f` members. -/
theorem card_sub_two_mul_le_card_inter (hs : Fintype.card α - f ≤ #s)
    (ht : Fintype.card α - f ≤ #t) : Fintype.card α - 2 * f ≤ #(s ∩ t) := by
  have := card_add_card_le_card_inter_add_card_univ s t
  omega

/-- Two `(n - f)`-quorums intersect when `2f < n`. -/
theorem inter_nonempty_of_two_mul_lt (hn : 2 * f < Fintype.card α)
    (hs : Fintype.card α - f ≤ #s) (ht : Fintype.card α - f ≤ #t) : (s ∩ t).Nonempty :=
  inter_nonempty_of_card_univ_lt_card_add_card (by omega)

/-- Two `(2f + 1)`-quorums intersect when `n ≤ 4f + 1`. -/
theorem inter_nonempty_of_card_le_four_mul_add_one (hn : Fintype.card α ≤ 4 * f + 1)
    (hs : 2 * f + 1 ≤ #s) (ht : 2 * f + 1 ≤ #t) : (s ∩ t).Nonempty :=
  inter_nonempty_of_card_univ_lt_card_add_card (by omega)

end Cslib.Quorum
