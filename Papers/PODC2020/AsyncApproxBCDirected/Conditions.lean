import Papers.PODC2020.AsyncApproxBCDirected.Graph

/-!
# The k-reach conditions versus the partition conditions of Tseng–Vaidya (Appendix A)

The definitions (`InArrow`, Definition 14; `PartCond`; conditions CCS, CCA, BCS of [TV15],
Definitions 16–18) and the core equivalence `partCond_iff : PartCond G F k ↔ ReachCondIn G F k`
are in `Cslib/Computability/Distributed/ApproxConsensus/DigraphConditions.lean`.

* **Theorem 17** (a), (b), (c) (`theorem17a/b/c`). The paper proves (a) and the direction
  "⇒" of (b) by reference to [TV15, SST19]; here all directions are proved.
* Comparison with the iterative condition of Vaidya–Tseng–Liang (PODC 2012, `IterativeCondition`,
  the condition of `Papers/PODC2012/IterativeApproxBC`): it implies BCS, hence 3-reach
  (`threeReach_of_vtl`), and the implication is strict (`exampleGraph`: 5 nodes, `f = 1`).
-/

open Finset Relation

set_option linter.unusedSectionVars false

namespace AsyncApproxBCDirected

open Cslib.ApproxConsensus

variable {V : Type*} [Fintype V] [DecidableEq V] {G : Digraph V}

/-- **Theorem 17 (a)**: CCS ⇔ 1-reach. -/
theorem theorem17a {f : ℕ} : CCS G f ↔ OneReach G f := ccs_iff_oneReach

/-- **Theorem 17 (b)**: CCA ⇔ 2-reach. -/
theorem theorem17b {f : ℕ} : CCA G f ↔ TwoReach G f := cca_iff_twoReach

/-- **Theorem 17 (c)**: BCS ⇔ 3-reach. -/
theorem theorem17c {f : ℕ} : BCS G f ↔ ThreeReach G f := bcs_iff_threeReach

/-! ## Comparison with the iterative condition of [VTL12] -/

/-- The condition of Vaidya–Tseng–Liang (PODC 2012) for *iterative* approximate Byzantine
consensus implies BCS. -/
theorem bcs_of_vtl {f : ℕ} (h : IterativeCondition G f) : BCS G f := h.bcs

/-- The iterative condition of [VTL12] implies 3-reach: every graph on which iterative
approximate Byzantine consensus is possible also allows asynchronous approximate Byzantine
consensus. -/
theorem threeReach_of_vtl {f : ℕ} (h : IterativeCondition G f) : ThreeReach G f := h.threeReach

/-! ## A graph satisfying 3-reach but not the iterative condition -/

/-- Decidable reformulation of BCS by labelings `V → Fin 4` (`0, 1, 2, 3` for `F, L, C, R`). -/
theorem bcs_of_labelings {f : ℕ} [DecidableRel G.Adj]
    (h : ∀ lab : V → Fin 4, (univ.filter fun x => lab x = 0).card ≤ f → (∃ v, lab v = 1) →
      (∃ v, lab v = 3) →
      f + 1 ≤ (univ.filter fun a => (1 ≤ lab a ∧ lab a ≤ 2) ∧ ∃ b, lab b = 3 ∧ G.Adj a b).card ∨
      f + 1 ≤ (univ.filter fun a => 2 ≤ lab a ∧ ∃ b, lab b = 1 ∧ G.Adj a b).card) :
    BCS G f := by
  classical
  intro F hF L C R hLC hLR hCR hU hL hR
  let lab : V → Fin 4 := fun x => if x ∈ F then 0 else if x ∈ L then 1 else if x ∈ C then 2 else 3
  have hmem : ∀ x, x ∈ F ∨ x ∈ L ∨ x ∈ C ∨ x ∈ R := fun x => by
    by_cases hx : x ∈ F
    · exact Or.inl hx
    · have : x ∈ univ \ F := by simp [hx]
      rw [← hU] at this; simp only [mem_union] at this; tauto
  have hdis : ∀ x, x ∈ L ∨ x ∈ C ∨ x ∈ R → x ∉ F := fun x hx => by
    have : x ∈ univ \ F := hU ▸ (by simp only [mem_union]; tauto)
    exact (mem_sdiff.mp this).2
  have hlab : ∀ x, (lab x = 0 ↔ x ∈ F) ∧ (lab x = 1 ↔ x ∈ L) ∧ (lab x = 3 ↔ x ∈ R) ∧
      (2 ≤ lab x ↔ x ∈ R ∪ C) ∧ (1 ≤ lab x ∧ lab x ≤ 2 ↔ x ∈ L ∪ C) := fun x => by
    rcases hmem x with hx | hx | hx | hx
    · have h1 : x ∉ L := fun h => hdis x (Or.inl h) hx
      have h2 : x ∉ C := fun h => hdis x (Or.inr (Or.inl h)) hx
      have h3 : x ∉ R := fun h => hdis x (Or.inr (Or.inr h)) hx
      simp [lab, hx, h1, h2, h3]
    · have := hdis x (Or.inl hx)
      simp [lab, hx, this, disjoint_left.mp hLC hx, disjoint_left.mp hLR hx]
    · have := hdis x (Or.inr (Or.inl hx))
      simp [lab, hx, this, disjoint_right.mp hLC hx, disjoint_left.mp hCR hx]
    · have := hdis x (Or.inr (Or.inr hx))
      simp [lab, hx, this, disjoint_right.mp hLR hx, disjoint_right.mp hCR hx]
  have eF : (univ.filter fun x => lab x = 0) = F := by ext x; simp [(hlab x).1]
  obtain ⟨v, hv⟩ := hL
  obtain ⟨w, hw⟩ := hR
  rcases h lab (eF ▸ hF) ⟨v, ((hlab v).2.1).mpr hv⟩ ⟨w, ((hlab w).2.2.1).mpr hw⟩ with hc | hc
  · left; rw [InArrow]; refine hc.trans_eq (congrArg card ?_)
    ext a; simp only [mem_inNbrsIn, mem_filter, mem_univ, true_and, (hlab a).2.2.2.2]
    constructor
    · rintro ⟨h1, b, hb, e⟩; exact ⟨h1, b, ((hlab b).2.2.1).mp hb, e⟩
    · rintro ⟨h1, b, hb, e⟩; exact ⟨h1, b, ((hlab b).2.2.1).mpr hb, e⟩
  · right; rw [InArrow]; refine hc.trans_eq (congrArg card ?_)
    ext a; simp only [mem_inNbrsIn, mem_filter, mem_univ, true_and, (hlab a).2.2.2.1]
    constructor
    · rintro ⟨h1, b, hb, e⟩; exact ⟨h1, b, ((hlab b).2.1).mp hb, e⟩
    · rintro ⟨h1, b, hb, e⟩; exact ⟨h1, b, ((hlab b).2.1).mpr hb, e⟩

/-- In-neighbourhoods of the example graph on `Fin 5`:
`0 ← {1,2,3}`, `1 ← {0,2,3}`, `2 ← {0,1,3}`, `3 ← {0,1,4}`, `4 ← {0,2,3}`. -/
def exampleIn : Fin 5 → Finset (Fin 5)
  | 0 => {1, 2, 3}
  | 1 => {0, 2, 3}
  | 2 => {0, 1, 3}
  | 3 => {0, 1, 4}
  | 4 => {0, 2, 3}

/-- A 5-node digraph (15 edges) satisfying 3-reach for `f = 1` but violating the iterative
condition of [VTL12]. -/
def exampleGraph : Digraph (Fin 5) where
  Adj a b := a ∈ exampleIn b

instance : DecidableRel exampleGraph.Adj := fun a b => inferInstanceAs (Decidable (a ∈ exampleIn b))

theorem exampleGraph_threeReach : ThreeReach exampleGraph 1 :=
  theorem17c.mp (bcs_of_labelings (by decide +kernel))

theorem exampleGraph_not_vtl : ¬ IterativeCondition exampleGraph 1 := by
  intro h
  have := h {0} {1, 2} ∅ {3, 4} (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)
  simp only [empty_union, union_empty, Arrow] at this
  simp only [inNbrs_eq_filter] at this
  revert this
  decide

end AsyncApproxBCDirected
