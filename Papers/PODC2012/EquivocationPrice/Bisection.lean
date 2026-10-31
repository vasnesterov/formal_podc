import Mathlib

/-!
# Lemma 4: graphs all of whose bisections are crossed

Jaffe, Moscibroda, Sen, *On the Price of Equivocation in Byzantine Agreement*, PODC 2012.

Lemma 4 of the paper: *for a graph `G = (V, E)` on `n` vertices, if all bisections are crossed
by at least one edge, then `|E| ≥ n/2`.* The paper defers the proof to the full version; we
supply one.

A graph on the vertex set `U : Finset V` is given by a family `F : Finset (Finset V)` of
2-element subsets of `U`. A *bisection* of `U` is a pair `(S, U \ S)` with `|S| = ⌊|U|/2⌋`; an
edge `f` *crosses* it if it meets both `S` and `U \ S`.

## Proof

If `2|F| < |U|`, the graph has more than `|U|/2` connected components (adding an edge decreases
the number of components by at most one). A family of `c` positive integers with sum `m < 2c`
realises every `k ∈ [0, m]` as a sub-sum (`exists_subsum_eq`), so some union of components has
exactly `⌊|U|/2⌋` vertices; no edge crosses it.

Instead of connected components we use any colouring `χ : V → V` constant on every edge with
`|U| ≤ |F| + |χ(U)|` (`exists_coloring`), built by induction on `F` by merging colour classes.
-/

namespace Podc.EquivocationPrice

open Finset

/-- A family of `c` positive integers with sum `< 2c` has every number up to its sum as a
sub-sum. -/
theorem exists_subsum_eq {ι : Type*} [DecidableEq ι] (s : ι → ℕ) (I : Finset ι)
    (hpos : ∀ i ∈ I, 0 < s i) (hsum : ∑ i ∈ I, s i < 2 * I.card) :
    ∀ k ≤ ∑ i ∈ I, s i, ∃ J ⊆ I, ∑ i ∈ J, s i = k := by
  induction I using Finset.strongInduction with
  | H I ih =>
  intro k hk
  by_cases h2 : ∃ i ∈ I, 2 ≤ s i
  · obtain ⟨i, hi, hsi⟩ := h2
    set I' := I.erase i with hI'
    have hsub : I' ⊂ I := Finset.erase_ssubset hi
    have hsplit : ∑ j ∈ I, s j = s i + ∑ j ∈ I', s j := (Finset.add_sum_erase I s hi).symm
    have hcard : I'.card + 1 = I.card := Finset.card_erase_add_one hi
    have hge : I'.card ≤ ∑ j ∈ I', s j := by
      rw [Finset.card_eq_sum_ones]
      exact Finset.sum_le_sum fun j hj => hpos j (Finset.mem_of_mem_erase hj)
    have ih' := ih I' hsub (fun j hj => hpos j (Finset.mem_of_mem_erase hj)) (by omega)
    by_cases hk' : k ≤ ∑ j ∈ I', s j
    · obtain ⟨J, hJ, hJs⟩ := ih' k hk'
      exact ⟨J, hJ.trans hsub.subset, hJs⟩
    · obtain ⟨J, hJ, hJs⟩ := ih' (k - s i) (by omega)
      have hiJ : i ∉ J := fun h => by simpa [I'] using hJ h
      refine ⟨insert i J, Finset.insert_subset hi (hJ.trans hsub.subset), ?_⟩
      rw [Finset.sum_insert hiJ]
      omega
  · simp only [not_exists, not_and, not_le] at h2
    have h1 : ∀ i ∈ I, s i = 1 := fun i hi => by have := hpos i hi; have := h2 i hi; omega
    have hsI : ∑ i ∈ I, s i = I.card := by
      rw [Finset.card_eq_sum_ones]; exact Finset.sum_congr rfl h1
    obtain ⟨J, hJ, hJc⟩ := Finset.exists_subset_card_eq (s := I) (n := k) (by omega)
    refine ⟨J, hJ, ?_⟩
    rw [Finset.sum_congr rfl fun i hi => h1 i (hJ hi), ← Finset.card_eq_sum_ones, hJc]

variable {V : Type*} [DecidableEq V]

/-- Every graph `F` on `U` has a vertex colouring that is constant on each edge and uses at
least `|U| - |F|` colours on `U` (the colour classes are unions of connected components). -/
theorem exists_coloring (U : Finset V) (F : Finset (Finset V))
    (hF : ∀ f ∈ F, f.card = 2 ∧ f ⊆ U) :
    ∃ χ : V → V, (∀ f ∈ F, ∀ u ∈ f, ∀ v ∈ f, χ u = χ v) ∧ U.card ≤ F.card + (U.image χ).card := by
  induction F using Finset.induction_on with
  | empty =>
    refine ⟨id, by simp, ?_⟩
    simp
  | insert f F hfF ih =>
    obtain ⟨χ, hχ, hcard⟩ := ih fun g hg => hF g (Finset.mem_insert_of_mem hg)
    obtain ⟨hf2, hfU⟩ := hF f (Finset.mem_insert_self f F)
    obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hf2
    have haU : a ∈ U := hfU (by simp)
    have hbU : b ∈ U := hfU (by simp)
    rw [Finset.card_insert_of_notMem hfF]
    by_cases hc : χ a = χ b
    · refine ⟨χ, ?_, by omega⟩
      intro g hg u hu v hv
      rcases Finset.mem_insert.mp hg with rfl | hg
      · simp only [Finset.mem_insert, Finset.mem_singleton] at hu hv
        rcases hu with rfl | rfl <;> rcases hv with rfl | rfl <;> simp [hc]
      · exact hχ g hg u hu v hv
    · let χ' : V → V := fun x => if χ x = χ b then χ a else χ x
      refine ⟨χ', ?_, ?_⟩
      · intro g hg u hu v hv
        rcases Finset.mem_insert.mp hg with rfl | hg
        · simp only [Finset.mem_insert, Finset.mem_singleton] at hu hv
          rcases hu with rfl | rfl <;> rcases hv with rfl | rfl <;> simp [χ']
        · simp only [χ', hχ g hg u hu v hv]
      · have himg : U.image χ' = (U.image χ).erase (χ b) := by
          ext y
          simp only [Finset.mem_image, Finset.mem_erase, χ']
          constructor
          · rintro ⟨x, hx, rfl⟩
            split_ifs with h
            · exact ⟨hc, a, haU, rfl⟩
            · exact ⟨h, x, hx, rfl⟩
          · rintro ⟨hy, x, hx, rfl⟩
            exact ⟨x, hx, by simp [hy]⟩
        have hmem : χ b ∈ U.image χ := Finset.mem_image_of_mem χ hbU
        rw [himg, Finset.card_erase_of_mem hmem]
        have := Finset.card_pos.mpr ⟨_, hmem⟩
        omega

/-- If `2|F| < |U|`, then for every `k ≤ |U|` some `S ⊆ U` with `|S| = k` is crossed by no
edge of `F`. -/
theorem exists_uncrossed (U : Finset V) (F : Finset (Finset V))
    (hF : ∀ f ∈ F, f.card = 2 ∧ f ⊆ U) (hlt : 2 * F.card < U.card) (k : ℕ) (hk : k ≤ U.card) :
    ∃ S ⊆ U, S.card = k ∧ ∀ f ∈ F, ¬ ((f ∩ S).Nonempty ∧ (f \ S).Nonempty) := by
  obtain ⟨χ, hχ, hcard⟩ := exists_coloring U F hF
  set I := U.image χ
  let s : V → ℕ := fun c => (U.filter fun x => χ x = c).card
  have hsum : ∑ c ∈ I, s c = U.card := (Finset.card_eq_sum_card_image χ U).symm
  have hpos : ∀ c ∈ I, 0 < s c := by
    intro c hc
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hc
    exact Finset.card_pos.mpr ⟨x, by simp [hx]⟩
  obtain ⟨J, hJ, hJs⟩ := exists_subsum_eq s I hpos (by omega) k (by omega)
  refine ⟨U.filter fun x => χ x ∈ J, Finset.filter_subset _ _, ?_, ?_⟩
  · rw [← hJs, Finset.card_eq_sum_card_fiberwise (s := U.filter fun x => χ x ∈ J) (f := χ) (t := J)
      (fun x hx => (Finset.mem_filter.mp hx).2)]
    refine Finset.sum_congr rfl fun c _ => ?_
    congr 1
    ext x
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨⟨hx, _⟩, rfl⟩; exact ⟨hx, rfl⟩
    · rintro ⟨hx, rfl⟩; exact ⟨⟨hx, by assumption⟩, rfl⟩
  · rintro f hf ⟨⟨u, hu⟩, ⟨v, hv⟩⟩
    simp only [Finset.mem_inter, Finset.mem_sdiff, Finset.mem_filter] at hu hv
    exact hv.2 ⟨(hF f hf).2 hv.1, hχ f hf v hv.1 u hu.1 ▸ hu.2.2⟩

/-- **Lemma 4** of [JMS12]: a graph on `U` all of whose bisections `(S, U \ S)`,
`|S| = ⌊|U|/2⌋`, are crossed by an edge has at least `|U|/2` edges (`|U| ≤ 2|F|`).
The paper states it for graphs on `n` vertices without parity assumption; it holds for odd
`|U|` as well (then `|F| ≥ ⌈|U|/2⌉`). -/
theorem lemma_4 (U : Finset V) (F : Finset (Finset V)) (hF : ∀ f ∈ F, f.card = 2 ∧ f ⊆ U)
    (hcross : ∀ S ⊆ U, S.card = U.card / 2 → ∃ f ∈ F, (f ∩ S).Nonempty ∧ (f \ S).Nonempty) :
    U.card ≤ 2 * F.card := by
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨S, hSU, hS, hno⟩ := exists_uncrossed U F hF hlt (U.card / 2) (Nat.div_le_self _ _)
  obtain ⟨f, hf, hfc⟩ := hcross S hSU hS
  exact hno f hf hfc

end Podc.EquivocationPrice
