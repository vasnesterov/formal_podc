import Papers.PODC2010.ArbdefectiveColoring.Basic

/-!
# Completing acyclic partial orientations (Lemma 3.1) and arbdefective colourings

* `exists_complete_extension` (**Lemma 3.1**): an acyclic partial orientation can be completed to
  an acyclic complete orientation by orienting the unoriented edges; every vertex gets at most its
  deficit many new out-edges.
* `isArbdefective_of_parents` (the combinatorial part of **Theorem 3.2**): if every vertex has at
  most `q` parents of its own colour in an acyclic partial orientation of deficit `≤ τ`, the
  colouring is `(q + τ)`-arbdefective (via Lemma 3.1 and Lemma 2.5, which is CSLib's
  `OutOrientation.arboricityLE_of_rank`).
* `isLegal_of_complete_of_parents`: if no vertex shares its colour with a parent of a complete
  orientation, the colouring is legal.

Instead of a topological sort (as in the paper) we orient the unoriented edges along the injective
rank `h v * |V| + e v`, where `h` is a height function of the orientation and `e : V ≃ Fin |V|`.
-/

open Finset

namespace Podc.ArbdefectiveColoring

open scoped Classical

set_option linter.unusedSectionVars false

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

-- CSLib candidate: completion of acyclic partial orientations (`SimpleGraph/Orientation.lean`)
/-- An injective rank refining a height function `h`. -/
noncomputable def rankOf (h : V → ℕ) (v : V) : ℕ :=
  h v * Fintype.card V + (Fintype.equivFin V v : ℕ)

lemma rankOf_lt_of_lt {h : V → ℕ} {u v : V} (huv : h u < h v) : rankOf h u < rankOf h v := by
  have hu := (Fintype.equivFin V u).isLt
  have : (h u + 1) * Fintype.card V ≤ h v * Fintype.card V := Nat.mul_le_mul_right _ huv
  simp only [rankOf]
  nlinarith

lemma rankOf_injective (h : V → ℕ) : Function.Injective (rankOf h) := by
  intro u v huv
  rcases lt_trichotomy (h u) (h v) with hlt | heq | hgt
  · exact absurd huv (rankOf_lt_of_lt hlt).ne
  · simp only [rankOf, heq, Nat.add_left_cancel_iff, Fin.val_inj] at huv
    exact (Fintype.equivFin V).injective huv
  · exact absurd huv (rankOf_lt_of_lt hgt).ne'

/-- **Lemma 3.1.** Any acyclic partial orientation of `G` can be transformed into a complete
acyclic orientation by orienting the unoriented edges. Every vertex `v` gets at most
`deficit G par v` new parents. -/
theorem exists_complete_extension {par : V → Finset V} (hP : IsPartialOrientation G par)
    (hA : IsAcyclic par) :
    ∃ par' : V → Finset V, (∀ v, par v ⊆ par' v) ∧
      (∀ v, #(par' v) ≤ #(par v) + deficit G par v) ∧
      IsPartialOrientation G par' ∧ IsComplete G par' ∧ IsAcyclic par' := by
  obtain ⟨h, -, hh⟩ := exists_height_of_isAcyclic hA
  set f := rankOf h
  let new : V → Finset V := fun v => {u | G.Adj v u ∧ u ∉ par v ∧ v ∉ par u ∧ f u < f v}
  have hdec : ∀ v u, u ∈ par v ∪ new v → f u < f v := by
    intro v u hu
    rcases mem_union.1 hu with hu | hu
    · exact rankOf_lt_of_lt (hh v u hu)
    · simp only [new, mem_filter, mem_univ, true_and] at hu; exact hu.2.2.2
  refine ⟨fun v => par v ∪ new v, fun v => subset_union_left, fun v => ?_, ⟨fun v u hu => ?_,
    fun v u hu hv => ?_⟩, fun u v huv => ?_, IsAcyclic.of_height hdec⟩
  · refine (card_union_le _ _).trans (Nat.add_le_add_left (card_le_card fun u hu => ?_) _)
    simp only [new, mem_filter, mem_univ, true_and] at hu ⊢
    exact ⟨hu.1, hu.2.1, hu.2.2.1⟩
  · rcases mem_union.1 hu with hu | hu
    · exact hP.1 v u hu
    · simp only [new, mem_filter, mem_univ, true_and] at hu; exact hu.1
  · exact lt_asymm (hdec v u hu) (hdec u v hv)
  · by_cases h1 : v ∈ par u
    · exact Or.inl (mem_union_left _ h1)
    by_cases h2 : u ∈ par v
    · exact Or.inr (mem_union_left _ h2)
    rcases lt_or_gt_of_ne ((rankOf_injective h).ne huv.ne) with hlt | hlt
    · exact Or.inr (mem_union_right _ (by
        simp only [new, mem_filter, mem_univ, true_and]; exact ⟨huv.symm, h2, h1, hlt⟩))
    · exact Or.inl (mem_union_right _ (by
        simp only [new, mem_filter, mem_univ, true_and]; exact ⟨huv, h1, h2, hlt⟩))

/-- **Theorem 3.2, combinatorial part** (via Lemmas 3.1 and 2.5). Let `par` be an acyclic partial
orientation of `G` with deficit at most `τ`, and let `c` be a colouring in which every vertex has
at most `q` parents of its own colour. Then `c` is a `(q + τ)`-arbdefective colouring. -/
theorem isArbdefective_of_parents {β : Type*} {par : V → Finset V}
    (hP : IsPartialOrientation G par) (hA : IsAcyclic par) {τ q : ℕ} (hτ : DeficitLE G par τ)
    (c : V → β) (hq : ∀ v, #{u ∈ par v | c u = c v} ≤ q) : IsArbdefective G c (q + τ) := by
  obtain ⟨h, -, hh⟩ := exists_height_of_isAcyclic hA
  set f := rankOf h
  let o : (classGraph G c).OutOrientation (q + τ) :=
    { out := fun v => {u ∈ par v | c u = c v} ∪
        ({u | G.Adj v u ∧ u ∉ par v ∧ v ∉ par u ∧ c u = c v ∧ f u < f v} : Finset V)
      adj_of_mem := fun v u hu => by
        rcases mem_union.1 hu with hu | hu
        · simp only [mem_filter] at hu
          exact ⟨hP.1 v u hu.1, hu.2.symm⟩
        · simp only [mem_filter, mem_univ, true_and] at hu
          exact ⟨hu.1, hu.2.2.2.1.symm⟩
      mem_or_mem := fun u v huv => by
        obtain ⟨huv, hc⟩ := huv
        by_cases h1 : v ∈ par u
        · exact Or.inl (mem_union_left _ (by simp [h1, hc]))
        by_cases h2 : u ∈ par v
        · exact Or.inr (mem_union_left _ (by simp [h2, hc]))
        rcases lt_or_gt_of_ne ((rankOf_injective h).ne huv.ne) with hlt | hlt
        · exact Or.inr (mem_union_right _ (by
            simp only [mem_filter, mem_univ, true_and]; exact ⟨huv.symm, h2, h1, hc, hlt⟩))
        · exact Or.inl (mem_union_right _ (by
            simp only [mem_filter, mem_univ, true_and]; exact ⟨huv, h1, h2, hc.symm, hlt⟩))
      card_out_le := fun v => by
        refine (card_union_le _ _).trans (Nat.add_le_add (hq v) ((card_le_card ?_).trans (hτ v)))
        intro u hu
        simp only [mem_filter, mem_univ, true_and] at hu ⊢
        exact ⟨hu.1, hu.2.1, hu.2.2.1⟩ }
  refine o.arboricityLE_of_rank f fun v u hu => ?_
  rcases mem_union.1 hu with hu | hu
  · exact rankOf_lt_of_lt (hh v u (mem_filter.1 hu).1)
  · simp only [mem_filter, mem_univ, true_and] at hu; exact hu.2.2.2.2

/-- If `par` is complete and no vertex has a parent of its own colour, the colouring is legal. -/
theorem isLegal_of_complete_of_parents {β : Type*} {par : V → Finset V} (hC : IsComplete G par)
    (c : V → β) (hq : ∀ v, ∀ u ∈ par v, c u ≠ c v) : IsLegal G c := by
  intro u v huv
  rcases hC huv with h | h
  · exact (hq u v h).symm
  · exact hq v u h

/-- **Lemma A.2** (Appendix A): a complete acyclic orientation of length `ℓ` gives a legal colouring
with `ℓ + 1` colours (colour a vertex by its height). Hence every complete acyclic orientation has
length at least `χ(G) - 1`. -/
theorem exists_legal_of_complete_of_lengthLE {par : V → Finset V} (hC : IsComplete G par) {ℓ : ℕ}
    (hL : LengthLE par ℓ) : ∃ c : V → ℕ, IsLegal G c ∧ ∀ v, c v ≤ ℓ := by
  obtain ⟨h, hle, hh⟩ := exists_height_of_lengthLE hL
  exact ⟨h, isLegal_of_complete_of_parents hC h fun v u hu => (hh v u hu).ne, hle⟩

end Podc.ArbdefectiveColoring
