import Papers.PODC2020.AsyncApproxBCDirected.Graph
import Papers.PODC2012.IterativeApproxBC.Applications

/-!
# The k-reach conditions versus the partition conditions of Tseng–Vaidya (Appendix A)

* `InArrow G x A B` — Definition 14, `A →ˣ B`: `B` has at least `x` incoming neighbours in `A`.
* `PartCond G F k` — "for every partition `L, C, R` of `V \ F` with `L, R ≠ ∅`:
  `L ∪ C →^{k+1} R` or `R ∪ C →^{k+1} L`".
  Conditions CCS, CCA, BCS of [TV15] (Definitions 16–18) are `PartCond` for `k = 0` and all `F`,
  for `F = ∅` and `k = f`, and for all `F` and `k = f`.
* `partCond_iff` — the core equivalence `PartCond G F k ↔ ReachCondIn G F k`, from which
  **Theorem 17** (a), (b), (c) follow (`theorem17a/b/c`). The paper proves (a) and the direction
  "⇒" of (b) by reference to [TV15, SST19]; here all directions are proved.
* Comparison with the iterative condition of Vaidya–Tseng–Liang (PODC 2012, formalized in
  `Papers/PODC2012/IterativeApproxBC`): it implies BCS, hence 3-reach (`threeReach_of_vtl`), and
  the implication is strict (`exampleGraph`: 5 nodes, `f = 1`).
-/

open Finset Relation

-- CSLib candidate (general directed-network / asynchronous Byzantine infrastructure)

set_option linter.unusedSectionVars false

namespace AsyncApproxBCDirected

variable {V : Type*} [Fintype V] [DecidableEq V] {G : Digraph V}

/-- Definition 14: `A →ˣ B` — the set `B` has at least `x` distinct incoming neighbours in `A`
(for disjoint `A`, `B`). -/
def InArrow (G : Digraph V) (x : ℕ) (A B : Finset V) : Prop := by
  classical exact x ≤ (A.filter fun a => ∃ b ∈ B, G.Adj a b).card

/-- Partition condition on `V \ F`: for every partition `L, C, R` of `V \ F` with `L, R`
non-empty, `L ∪ C →^{k+1} R` or `R ∪ C →^{k+1} L`. -/
def PartCond (G : Digraph V) (F : Finset V) (k : ℕ) : Prop :=
  ∀ L C R : Finset V, Disjoint L C → Disjoint L R → Disjoint C R → L ∪ C ∪ R = univ \ F →
    L.Nonempty → R.Nonempty → InArrow G (k + 1) (L ∪ C) R ∨ InArrow G (k + 1) (R ∪ C) L

/-- Condition CCS (Definition 16). -/
def CCS (G : Digraph V) (f : ℕ) : Prop := ∀ F : Finset V, F.card ≤ f → PartCond G F 0

/-- Condition CCA (Definition 17). -/
def CCA (G : Digraph V) (f : ℕ) : Prop := PartCond G ∅ f

/-- Condition BCS (Definition 18). -/
def BCS (G : Digraph V) (f : ℕ) : Prop := ∀ F : Finset V, F.card ≤ f → PartCond G F f

/-- The in-neighbours of `L` inside `A`. -/
private noncomputable def inN (G : Digraph V) (A L : Finset V) : Finset V := by
  classical exact A.filter fun a => ∃ b ∈ L, G.Adj a b

private theorem inArrow_iff {x : ℕ} {A B : Finset V} : InArrow G x A B ↔ x ≤ (inN G A B).card := by
  classical simp only [InArrow, inN]

/-- The core equivalence behind Theorem 17: the partition condition on `V \ F` with threshold
`k + 1` is equivalent to the reach condition on `G − F` with suspect sets of size `≤ k`. -/
theorem partCond_iff {F : Finset V} {k : ℕ} : PartCond G F k ↔ ReachCondIn G F k := by
  classical
  constructor
  · intro h Fu Fv u v hFu hFv hu hv
    by_contra hcon
    push Not at hcon
    set L := univ.filter fun w => Reaches G (F ∪ Fv) w v
    set R := univ.filter fun w => Reaches G (F ∪ Fu) w u
    set C := ((univ \ F) \ L) \ R
    have hLF : ∀ w ∈ L, w ∉ F := fun w hw => by
      simp only [L, mem_filter] at hw; exact fun h => hw.2.1 (mem_union_left _ h)
    have hRF : ∀ w ∈ R, w ∉ F := fun w hw => by
      simp only [R, mem_filter] at hw; exact fun h => hw.2.1 (mem_union_left _ h)
    have hLR : Disjoint L R := disjoint_left.mpr fun w hwL hwR => by
      simp only [L, R, mem_filter, mem_univ, true_and] at hwL hwR
      exact hcon w hwL hwR
    have hU : L ∪ C ∪ R = univ \ F := by
      ext w; simp only [C, mem_union, mem_sdiff, mem_univ, true_and]
      constructor
      · rintro ((h | h) | h)
        · exact hLF w h
        · exact h.1.1
        · exact hRF w h
      · intro hw; tauto
    have hcl : ∀ (X W : Finset V) (z : V), (∀ w ∈ W, w ∉ F) → X.card ≤ k →
        (∀ a b, G.Adj a b → a ∉ F ∪ X → b ∈ W → a ∈ W) → ¬ (k + 1 ≤ (inN G ((univ \ F) \ W) W).card) := by
      intro X W _ _ hX hcl hk
      have : inN G ((univ \ F) \ W) W ⊆ X := by
        intro a ha
        simp only [inN, mem_filter, mem_sdiff, mem_univ, true_and] at ha
        obtain ⟨⟨haF, haW⟩, b, hb, e⟩ := ha
        by_contra haX
        exact haW (hcl a b e (by simp [haF, haX]) hb)
      have := card_le_card this
      omega
    have eR : L ∪ C = (univ \ F) \ R := by
      rw [← hU]; ext w; simp only [mem_union, mem_sdiff]
      constructor
      · rintro (h | h)
        · exact ⟨Or.inl (Or.inl h), disjoint_left.mp hLR h⟩
        · exact ⟨Or.inl (Or.inr h), (mem_sdiff.mp h).2⟩
      · rintro ⟨(h | h) | h, h'⟩
        · exact Or.inl h
        · exact Or.inr h
        · exact absurd h h'
    have eL : R ∪ C = (univ \ F) \ L := by
      rw [← hU]; ext w; simp only [mem_union, mem_sdiff, C]
      constructor
      · rintro (h | h)
        · exact ⟨Or.inr h, (disjoint_right.mp hLR h)⟩
        · exact ⟨Or.inl (Or.inr (by simp [h.1.1.1, h.1.1.2, h.1.2, h.2])), h.1.2⟩
      · rintro ⟨(h | h) | h, h'⟩
        · exact absurd h h'
        · exact Or.inr (by simpa [C] using h)
        · exact Or.inl h
    rcases h L C R (disjoint_left.mpr fun w hw hwC => (mem_sdiff.mp (mem_sdiff.mp hwC).1).2 hw)
        hLR (disjoint_left.mpr fun w hwC hw => (mem_sdiff.mp hwC).2 hw) hU
        ⟨v, by simp [L, Reaches.refl hv]⟩ ⟨u, by simp [R, Reaches.refl hu]⟩ with h | h
    · rw [inArrow_iff, eR] at h
      exact hcl Fu R u hRF hFu (fun a b e ha hb => by
        simp only [R, mem_filter, mem_univ, true_and] at hb ⊢
        exact hb.head e ha) h
    · rw [inArrow_iff, eL] at h
      exact hcl Fv L v hLF hFv (fun a b e ha hb => by
        simp only [L, mem_filter, mem_univ, true_and] at hb ⊢
        exact hb.head e ha) h
  · intro h L C R hLC hLR hCR hU ⟨v, hv⟩ ⟨u, hu⟩
    by_contra hcon
    rw [not_or, inArrow_iff, inArrow_iff, not_le, not_le] at hcon
    set Fu := inN G (L ∪ C) R
    set Fv := inN G (R ∪ C) L
    have hmem : ∀ w, w ∉ F → w ∈ L ∨ w ∈ C ∨ w ∈ R := fun w hw => by
      have : w ∈ univ \ F := by simp [hw]
      rw [← hU] at this; simp only [mem_union] at this; tauto
    have hLF : ∀ w ∈ L, w ∉ F := fun w hw => by
      have : w ∈ univ \ F := hU ▸ mem_union_left _ (mem_union_left _ hw)
      exact (mem_sdiff.mp this).2
    have hRF : ∀ w ∈ R, w ∉ F := fun w hw => by
      have : w ∈ univ \ F := hU ▸ mem_union_right _ hw
      exact (mem_sdiff.mp this).2
    have hFvL : ∀ w ∈ Fv, w ∉ L := fun w hw => by
      simp only [Fv, inN, mem_filter, mem_union] at hw
      rcases hw.1 with h | h
      · exact disjoint_right.mp hLR h
      · exact disjoint_right.mp hLC h
    have hFuR : ∀ w ∈ Fu, w ∉ R := fun w hw => by
      simp only [Fu, inN, mem_filter, mem_union] at hw
      rcases hw.1 with h | h
      · exact disjoint_left.mp hLR h
      · exact disjoint_left.mp hCR h
    obtain ⟨w, hw1, hw2⟩ := h Fu Fv u v (by omega) (by omega)
      (by simp only [mem_union, not_or]; exact ⟨hRF u hu, fun h => hFuR u h hu⟩)
      (by simp only [mem_union, not_or]; exact ⟨hLF v hv, fun h => hFvL v h hv⟩)
    have hwL : w ∈ L := hw1.mem_of_closed (L := (L : Set V)) (fun a b e ha hb => by
      simp only [mem_union, not_or] at ha
      by_contra haL
      rcases hmem a ha.1 with h | h | h
      · exact haL h
      · exact ha.2 (by simp only [Fv, inN, mem_filter, mem_union]; exact ⟨Or.inr h, b, hb, e⟩)
      · exact ha.2 (by simp only [Fv, inN, mem_filter, mem_union]; exact ⟨Or.inl h, b, hb, e⟩))
      hv
    have hwR : w ∈ R := hw2.mem_of_closed (L := (R : Set V)) (fun a b e ha hb => by
      simp only [mem_union, not_or] at ha
      by_contra haR
      rcases hmem a ha.1 with h | h | h
      · exact ha.2 (by simp only [Fu, inN, mem_filter, mem_union]; exact ⟨Or.inl h, b, hb, e⟩)
      · exact ha.2 (by simp only [Fu, inN, mem_filter, mem_union]; exact ⟨Or.inr h, b, hb, e⟩)
      · exact haR h)
      hu
    exact disjoint_left.mp hLR hwL hwR

/-- **Theorem 17 (a)**: CCS ⇔ 1-reach. -/
theorem theorem17a {f : ℕ} : CCS G f ↔ OneReach G f := by
  rw [oneReach_iff]; exact forall₂_congr fun _ _ => partCond_iff

/-- **Theorem 17 (b)**: CCA ⇔ 2-reach. -/
theorem theorem17b {f : ℕ} : CCA G f ↔ TwoReach G f := by
  rw [twoReach_iff]; exact partCond_iff

/-- **Theorem 17 (c)**: BCS ⇔ 3-reach. -/
theorem theorem17c {f : ℕ} : BCS G f ↔ ThreeReach G f := by
  rw [threeReach_iff]; exact forall₂_congr fun _ _ => partCond_iff

/-! ## Comparison with the iterative condition of [VTL12] -/

/-- The condition of Vaidya–Tseng–Liang (PODC 2012) for *iterative* approximate Byzantine
consensus implies BCS. -/
theorem bcs_of_vtl {f : ℕ} (h : IterativeApproxBC.Condition G f) : BCS G f := by
  classical
  intro F hF L C R hLC hLR hCR hU hL hR
  have hFL : Disjoint F L := disjoint_left.mpr fun x hx hxL => by
    have : x ∈ univ \ F := hU ▸ mem_union_left _ (mem_union_left _ hxL)
    exact (mem_sdiff.mp this).2 hx
  have hFC : Disjoint F C := disjoint_left.mpr fun x hx hxC => by
    have : x ∈ univ \ F := hU ▸ mem_union_left _ (mem_union_right _ hxC)
    exact (mem_sdiff.mp this).2 hx
  have hFR : Disjoint F R := disjoint_left.mpr fun x hx hxR => by
    have : x ∈ univ \ F := hU ▸ mem_union_right _ hxR
    exact (mem_sdiff.mp this).2 hx
  have hU' : F ∪ L ∪ C ∪ R = univ := by
    rw [union_assoc, union_assoc, ← union_assoc L, hU]; simp
  have key : ∀ A B : Finset V, IterativeApproxBC.Arrow G f A B → InArrow G (f + 1) A B := by
    intro A B ⟨v, hv, hc⟩
    rw [inArrow_iff]
    refine hc.trans (card_le_card fun a ha => ?_)
    simp only [mem_inter, Cslib.ApproxConsensus.mem_inNbrs] at ha
    simp only [inN, mem_filter]
    exact ⟨ha.2, v, hv, ha.1.1⟩
  rcases h F L C R hFL hFC hFR hLC hLR hCR hU' hF hL hR with h | h
  · exact Or.inr (by rw [union_comm]; exact key _ _ h)
  · exact Or.inl (key _ _ h)

/-- The iterative condition of [VTL12] implies 3-reach: every graph on which iterative
approximate Byzantine consensus is possible also allows asynchronous approximate Byzantine
consensus. -/
theorem threeReach_of_vtl {f : ℕ} (h : IterativeApproxBC.Condition G f) : ThreeReach G f :=
  theorem17c.mp (bcs_of_vtl h)

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
  · left; rw [inArrow_iff]; refine hc.trans_eq (congrArg card ?_)
    ext a; simp only [inN, mem_filter, mem_univ, true_and, (hlab a).2.2.2.2]
    constructor
    · rintro ⟨h1, b, hb, e⟩; exact ⟨h1, b, ((hlab b).2.2.1).mp hb, e⟩
    · rintro ⟨h1, b, hb, e⟩; exact ⟨h1, b, ((hlab b).2.2.1).mpr hb, e⟩
  · right; rw [inArrow_iff]; refine hc.trans_eq (congrArg card ?_)
    ext a; simp only [inN, mem_filter, mem_univ, true_and, (hlab a).2.2.2.1]
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

theorem exampleGraph_not_vtl : ¬ IterativeApproxBC.Condition exampleGraph 1 := by
  intro h
  have := h {0} {1, 2} ∅ {3, 4} (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)
  simp only [empty_union, union_empty, IterativeApproxBC.Arrow] at this
  simp only [IterativeApproxBC.inNbrs_eq_filter] at this
  revert this
  decide

end AsyncApproxBCDirected
