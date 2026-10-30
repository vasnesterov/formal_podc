import Mathlib

-- CSLib candidate: logs with prefix compatibility and faithful-tally counting for graded agreement
-- (`Cslib/Computability/Distributed/Byzantine/GradedLogs.lean`).

/-!
# Logs, vote tallies and graded-agreement counting

D'Amato, Losa, Zanolini, *Asynchrony-Resilient Sleepy Total-Order Broadcast Protocols*, PODC 2024
(arXiv:2309.05347v2).

A *log* is a list of blocks (`List α`); `Λ <+: Λ'` means `Λ'` extends `Λ` (Definition 1).
A *vote assignment* `M : P → Option (List α)` records the (at most one) vote that a receiver counts
for each process after discarding equivocations; it is the set `M_r^i` of Figure 3. The tally of
Figures 2/3 outputs `(Λ, 1)` if more than `2m/3` of the `m` counted votes are for extensions of `Λ`,
and `(Λ, 0)` if more than `m/3` (but not more than `2m/3`) are.

This file contains the pure counting arguments behind Lemma 1: an abstract "faithful tally"
(every honest process of `H` is counted with its true vote, every counted process lies in a
universe `U`, `|H| > 2|U|/3`) and the consequences graded consistency, integrity, validity,
uniqueness and bounded divergence.
-/

namespace Podc.SleepyTOB

open Finset

noncomputable section
open Classical

variable {P α : Type*}

/-- Two logs are compatible when one is a prefix of the other (Definition 1). -/
def Compatible (Λ Λ' : List α) : Prop := Λ <+: Λ' ∨ Λ' <+: Λ

/-- Two logs conflict when they are not compatible (Definition 1). -/
def Conflict (Λ Λ' : List α) : Prop := ¬ Compatible Λ Λ'

theorem Compatible.symm {Λ Λ' : List α} (h : Compatible Λ Λ') : Compatible Λ' Λ := Or.symm h

/-- Two prefixes of a common log are compatible. -/
theorem compatible_of_prefix_of_prefix {Λ Λ' l : List α} (h : Λ <+: l) (h' : Λ' <+: l) :
    Compatible Λ Λ' := by
  rcases le_total Λ.length Λ'.length with hl | hl
  · exact Or.inl (List.prefix_of_prefix_length_le h h' hl)
  · exact Or.inr (List.prefix_of_prefix_length_le h' h hl)

/-- If `X ⊑ Z`, `Λ ⊑ Y` and `Y`, `Z` are compatible, then `X` and `Λ` are compatible. -/
theorem compatible_of_prefix_compatible {X Z Λ Y : List α} (hX : X <+: Z) (hΛ : Λ <+: Y)
    (hYZ : Compatible Y Z) : Compatible X Λ := by
  rcases hYZ with h | h
  · exact compatible_of_prefix_of_prefix hX (hΛ.trans h)
  · exact compatible_of_prefix_of_prefix (hX.trans h) hΛ

/-- A compatible log at least as long is an extension. -/
theorem prefix_of_compatible_of_length_le {Λ L : List α} (h : Compatible Λ L)
    (hl : Λ.length ≤ L.length) : Λ <+: L := by
  rcases h with h | h
  · exact h
  · have := h.eq_of_length (le_antisymm h.length_le hl)
    exact this ▸ List.prefix_refl _

/-- A vote assignment: the vote counted from each process (`none`: no vote counted). -/
abbrev Votes (P α : Type*) := P → Option (List α)

variable [Fintype P]

/-- The processes whose vote is counted (`m = #(voters M)`). -/
def voters (M : Votes P α) : Finset P := univ.filter (fun q => M q ≠ none)

/-- The processes whose counted vote is for an extension of `Λ`. -/
def votesFor (M : Votes P α) (Λ : List α) : Finset P :=
  univ.filter (fun q => ∃ l, M q = some l ∧ Λ <+: l)

/-- `Λ` is output with grade 1: voted by more than `2m/3` processes. -/
def Grade1 (M : Votes P α) (Λ : List α) : Prop := 2 * #(voters M) < 3 * #(votesFor M Λ)

/-- `Λ` is output (with grade `≥ 0`): voted by more than `m/3` processes. -/
def Outputs (M : Votes P α) (Λ : List α) : Prop := #(voters M) < 3 * #(votesFor M Λ)

/-- `Λ` is output with grade exactly 0. -/
def Grade0 (M : Votes P α) (Λ : List α) : Prop := Outputs M Λ ∧ ¬ Grade1 M Λ

/-- `L` is a longest log satisfying `S`. -/
def IsLongest (S : List α → Prop) (L : List α) : Prop := S L ∧ ∀ L', S L' → L'.length ≤ L.length

variable {M M' : Votes P α} {Λ Λ' : List α}

theorem votesFor_subset_voters : votesFor M Λ ⊆ voters M := by
  intro q hq
  simp only [votesFor, voters, mem_filter, mem_univ, true_and] at hq ⊢
  obtain ⟨l, hl, -⟩ := hq
  simp [hl]

theorem votesFor_anti (h : Λ' <+: Λ) : votesFor M Λ ⊆ votesFor M Λ' := by
  intro q hq
  simp only [votesFor, mem_filter, mem_univ, true_and] at hq ⊢
  obtain ⟨l, hl, hΛ⟩ := hq
  exact ⟨l, hl, h.trans hΛ⟩

theorem Grade1.outputs (h : Grade1 M Λ) : Outputs M Λ := by
  unfold Grade1 at h; unfold Outputs; omega

theorem Outputs.of_prefix (h : Outputs M Λ) (h' : Λ' <+: Λ) : Outputs M Λ' := by
  unfold Outputs at *
  have := card_le_card (votesFor_anti (M := M) h'); omega

theorem Grade1.of_prefix (h : Grade1 M Λ) (h' : Λ' <+: Λ) : Grade1 M Λ' := by
  unfold Grade1 at *
  have := card_le_card (votesFor_anti (M := M) h'); omega

/-- Votes for conflicting logs come from disjoint sets of processes. -/
theorem disjoint_votesFor (h : Conflict Λ Λ') : Disjoint (votesFor M Λ) (votesFor M Λ') := by
  rw [Finset.disjoint_left]
  intro q hq hq'
  simp only [votesFor, mem_filter, mem_univ, true_and] at hq hq'
  obtain ⟨l, hl, hΛ⟩ := hq
  obtain ⟨l', hl', hΛ'⟩ := hq'
  rw [hl] at hl'; cases hl'
  exact h (compatible_of_prefix_of_prefix hΛ hΛ')

/-- In one tally, a grade-1 log is compatible with every output log. -/
theorem compatible_of_grade1_of_outputs (h1 : Grade1 M Λ) (h2 : Outputs M Λ') :
    Compatible Λ Λ' := by
  by_contra hc
  have hd := disjoint_votesFor (M := M) hc
  have hu : #(votesFor M Λ ∪ votesFor M Λ') ≤ #(voters M) :=
    card_le_card (union_subset votesFor_subset_voters votesFor_subset_voters)
  rw [card_union_of_disjoint hd] at hu
  unfold Grade1 at h1; unfold Outputs at h2; omega

/-- A longest output log extends every grade-1 log of the same tally. -/
theorem prefix_of_isLongest_outputs {L : List α} (hL : IsLongest (Outputs M) L)
    (hΛ : Grade1 M Λ) : Λ <+: L :=
  prefix_of_compatible_of_length_le (compatible_of_grade1_of_outputs hΛ hL.1) (hL.2 _ hΛ.outputs)

/-- The longest grade-1 log extends every grade-1 log of the same tally. -/
theorem prefix_of_isLongest_grade1 {L : List α} (hL : IsLongest (Grade1 M) L)
    (hΛ : Grade1 M Λ) : Λ <+: L :=
  prefix_of_compatible_of_length_le (compatible_of_grade1_of_outputs hΛ hL.1.outputs) (hL.2 _ hΛ)

/-- **Bounded divergence** (counting core): a family of pairwise conflicting output logs has at
most two members, because their voter sets are disjoint and each has more than `m/3` voters. -/
theorem card_le_two_of_pairwise_conflict (S : Finset (List α))
    (hS : (S : Set (List α)).Pairwise Conflict) (hout : ∀ Λ ∈ S, Outputs M Λ) : #S ≤ 2 := by
  have hdisj : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → Disjoint (votesFor M x) (votesFor M y) :=
    fun x hx y hy hxy => disjoint_votesFor (hS hx hy hxy)
  have hsub : S.biUnion (votesFor M) ⊆ voters M :=
    biUnion_subset.2 fun _ _ => votesFor_subset_voters
  have h1 := card_le_card hsub
  rw [card_biUnion hdisj] at h1
  have h2 : ∑ Λ ∈ S, (#(voters M) + 1) ≤ ∑ Λ ∈ S, 3 * #(votesFor M Λ) :=
    sum_le_sum fun Λ hΛ => hout Λ hΛ
  rw [sum_const, smul_eq_mul, ← mul_sum] at h2
  by_contra hc
  push Not at hc
  have : 3 * (#(voters M) + 1) ≤ #S * (#(voters M) + 1) := Nat.mul_le_mul_right _ hc
  omega

/-! ### Faithful tallies -/

/-- A tally `M` is *faithful* for a universe `U` of possible senders and an honest set `H` with
true votes `h`: every counted process is in `U`, and each honest process is counted with its true
vote. -/
structure Faithful (M : Votes P α) (U H : Finset P) (h : P → List α) : Prop where
  voters_subset : voters M ⊆ U
  honest : ∀ q ∈ H, M q = some (h q)

variable {U H : Finset P} {h : P → List α}

theorem Faithful.honest_subset_voters (hM : Faithful M U H h) : H ⊆ voters M := by
  intro q hq
  simp [voters, hM.honest q hq]

theorem Faithful.filter_subset_votesFor (hM : Faithful M U H h) :
    H.filter (fun q => Λ <+: h q) ⊆ votesFor M Λ := by
  intro q hq
  rw [mem_filter] at hq
  simp only [votesFor, mem_filter, mem_univ, true_and]
  exact ⟨h q, hM.honest q hq.1, hq.2⟩

theorem Faithful.inter_eq (hM : Faithful M U H h) :
    votesFor M Λ ∩ H = H.filter (fun q => Λ <+: h q) := by
  ext q
  simp only [votesFor, mem_inter, mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨⟨l, hl, hΛ⟩, hq⟩
    rw [hM.honest q hq] at hl; cases hl
    exact ⟨hq, hΛ⟩
  · rintro ⟨hq, hΛ⟩
    exact ⟨⟨h q, hM.honest q hq, hΛ⟩, hq⟩

/-- The key count: if a faithful tally outputs `Λ` with grade 1 and `|H| > 2|U|/3`, then more
than `|U|/3` honest processes vote for extensions of `Λ`. -/
theorem Faithful.honest_count (hM : Faithful M U H h) (hH : 2 * #U < 3 * #H)
    (hg : Grade1 M Λ) : #U < 3 * #(H.filter fun q => Λ <+: h q) := by
  rw [← hM.inter_eq]
  have h1 := card_union_add_card_inter (votesFor M Λ) H
  have h2 : #(votesFor M Λ ∪ H) ≤ #(voters M) :=
    card_le_card (union_subset votesFor_subset_voters hM.honest_subset_voters)
  have h3 : #(voters M) ≤ #U := card_le_card hM.voters_subset
  unfold Grade1 at hg
  omega

/-- If more than `|U|/3` honest processes vote for extensions of `Λ`, every faithful tally
outputs `Λ`. -/
theorem Faithful.outputs_of_honest_count (hM : Faithful M U H h)
    (hc : #U < 3 * #(H.filter fun q => Λ <+: h q)) : Outputs M Λ := by
  have h1 := card_le_card (hM.filter_subset_votesFor (Λ := Λ))
  have h3 : #(voters M) ≤ #U := card_le_card hM.voters_subset
  unfold Outputs; omega

/-- Integrity (counting core): an output log is extended by some honest vote. -/
theorem Faithful.integrity (hM : Faithful M U H h) (hH : 2 * #U < 3 * #H) (ho : Outputs M Λ) :
    ∃ q ∈ H, Λ <+: h q := by
  have h1 := card_union_add_card_inter (votesFor M Λ) H
  have h2 : #(votesFor M Λ ∪ H) ≤ #(voters M) :=
    card_le_card (union_subset votesFor_subset_voters hM.honest_subset_voters)
  have h3 : #(voters M) ≤ #U := card_le_card hM.voters_subset
  have hne : (votesFor M Λ ∩ H).Nonempty := by
    rw [← card_pos]; unfold Outputs at ho; omega
  obtain ⟨q, hq⟩ := hne
  rw [hM.inter_eq, mem_filter] at hq
  exact ⟨q, hq.1, hq.2⟩

/-- A tally all of whose senders lie in `U` outputs `Λ` with grade 1 as soon as more than
`2|U|/3` processes are counted with votes for extensions of `Λ`. -/
theorem grade1_of_subset_votesFor {H' : Finset P} (hU : voters M ⊆ U)
    (hH' : H' ⊆ votesFor M Λ) (hc : 2 * #U < 3 * #H') : Grade1 M Λ := by
  have h1 := card_le_card hH'
  have h3 := card_le_card hU
  unfold Grade1; omega

/-- Validity (counting core): if all honest votes extend `Λ`, a faithful tally outputs `Λ` with
grade 1. -/
theorem Faithful.grade1_of_forall (hM : Faithful M U H h) (hH : 2 * #U < 3 * #H)
    (hall : ∀ q ∈ H, Λ <+: h q) : Grade1 M Λ := by
  refine grade1_of_subset_votesFor hM.voters_subset ?_ hH
  intro q hq
  exact hM.filter_subset_votesFor (mem_filter.2 ⟨hq, hall q hq⟩)

/-- Graded consistency (counting core) between two faithful tallies with the same honest votes. -/
theorem Faithful.consistency (hM : Faithful M U H h) (hM' : Faithful M' U H h)
    (hH : 2 * #U < 3 * #H) (hg : Grade1 M Λ) : Outputs M' Λ :=
  hM'.outputs_of_honest_count (hM.honest_count hH hg)

/-- Uniqueness (counting core) between two faithful tallies with the same honest votes. -/
theorem Faithful.uniqueness (hM : Faithful M U H h) (hM' : Faithful M' U H h)
    (hH : 2 * #U < 3 * #H) (hg : Grade1 M Λ) (hg' : Grade1 M' Λ') : Compatible Λ Λ' :=
  (compatible_of_grade1_of_outputs hg' (hM.consistency hM' hH hg)).symm

end

end Podc.SleepyTOB
