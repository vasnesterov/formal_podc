import Papers.PODC2026.TreesNetworkSizeKnowledge.Embedding

/-!
# Padding: the graph `G''` of the proof of property 3

Given a component `comp ℓ (j+1) top` embedded in a host `H`, `padTree` is the graph `G''` of the
paper: the component on its own (with the identifiers it has in `H`), plus a path of fresh nodes
attached to a level-1 node at position `0`, so that it has exactly `N` nodes. Nodes in the middle of
the component's path cannot distinguish `H` from `G''` within the relevant radius
(`gAgree_padTree`), hence they terminate by round `T` in `H` if every algorithm run on an `N`-node
tree terminates by round `T` (`time_le_of_pad`).
-/

namespace Podc.TreesNetworkSizeKnowledge

open SimpleGraph

variable {ℓ : ℕ → ℕ} {H : RTree} {hl : ℕ → ℕ} {j : ℕ} {top : Bool} {ι : ℕ → ℕ}

section Pad

variable (hℓ : ∀ i, 2 ≤ ℓ i) (hE : Emb ℓ H hl (j + 1) top ι) (N : ℕ)

include hℓ in
lemma hℓ1 : ∀ i, 1 ≤ ℓ i := fun i => by have := hℓ i; omega

/-- The identifiers of the component. -/
def img (ℓ : ℕ → ℕ) (j : ℕ) (top : Bool) (ι : ℕ → ℕ) : Finset ℕ := (comp ℓ (j + 1) top).V.image ι

/-- The largest identifier of the component. -/
def maxId (ℓ : ℕ → ℕ) (j : ℕ) (top : Bool) (ι : ℕ → ℕ) : ℕ := (img ℓ j top ι).sup id

lemma le_maxId {y : ℕ} (hy : y ∈ img ℓ j top ι) : y ≤ maxId ℓ j top ι :=
  Finset.le_sup (f := id) hy

lemma mem_img {y : ℕ} : y ∈ img ℓ j top ι ↔ ∃ x ∈ (comp ℓ (j + 1) top).V, ι x = y := by
  simp [img]

/-- The padded graph `G''`. -/
def padTree : RTree where
  V := img ℓ j top ι ∪ Finset.Ioc (maxId ℓ j top ι) (maxId ℓ j top ι + (N - (comp ℓ (j + 1) top).V.card))
  root := ι 0
  par y := if maxId ℓ j top ι < y then
      (if y = maxId ℓ j top ι + 1 then ι (leafCode (j + 1)) else y - 1) else H.par y
  rank y := if maxId ℓ j top ι < y then H.rank (ι (leafCode (j + 1))) + (y - maxId ℓ j top ι)
    else H.rank y
  root_mem := Finset.mem_union_left _ (mem_img.2 ⟨0, zero_mem ℓ j top (hℓ1 hℓ), rfl⟩)
  par_mem y hy hr := by
    rcases Finset.mem_union.1 hy with hy | hy
    · obtain ⟨x, hx, rfl⟩ := mem_img.1 hy
      have hx0 : x ≠ 0 := by rintro rfl; exact hr rfl
      rw [ite_eq_right (not_lt.2 (le_maxId hy)), hE.par_eq x hx hx0]
      exact Finset.mem_union_left _ (mem_img.2 ⟨_, (par_wf ℓ _ _ x hx hx0).1, rfl⟩)
    · rw [Finset.mem_Ioc] at hy
      rw [ite_eq_left hy.1]
      split_ifs with h1
      · exact Finset.mem_union_left _
          (mem_img.2 ⟨_, (leafCode_spec ℓ (hℓ1 hℓ) j top).1, rfl⟩)
      · exact Finset.mem_union_right _ (Finset.mem_Ioc.2 ⟨by omega, by omega⟩)
  rank_lt y hy hr := by
    rcases Finset.mem_union.1 hy with hy | hy
    · obtain ⟨x, hx, rfl⟩ := mem_img.1 hy
      have hx0 : x ≠ 0 := by rintro rfl; exact hr rfl
      have hp : H.par (ι x) ∈ img ℓ j top ι := by
        rw [hE.par_eq x hx hx0]; exact mem_img.2 ⟨_, (par_wf ℓ _ _ x hx hx0).1, rfl⟩
      rw [ite_eq_right (not_lt.2 (le_maxId hy)), ite_eq_right (not_lt.2 (le_maxId hp)), ite_eq_right (not_lt.2 (le_maxId hy))]
      exact H.rank_lt _ (hE.mem x hx) (hE.ne_root hx hx0)
    · rw [Finset.mem_Ioc] at hy
      have hw : ι (leafCode (j + 1)) ∈ img ℓ j top ι :=
        mem_img.2 ⟨_, (leafCode_spec ℓ (hℓ1 hℓ) j top).1, rfl⟩
      rw [ite_eq_left hy.1, ite_eq_left hy.1]
      have := le_maxId hw
      split_ifs <;> omega

lemma padTree_card (hN : (comp ℓ (j + 1) top).V.card ≤ N) :
    (padTree hℓ hE N).V.card = N := by
  simp only [padTree]
  rw [Finset.card_union_of_disjoint]
  · rw [img, Finset.card_image_of_injective _ hE.inj, Nat.card_Ioc]; omega
  · rw [Finset.disjoint_left]
    intro y hy hy'
    have := le_maxId hy
    rw [Finset.mem_Ioc] at hy'; omega

lemma padTree_adj_img {x u : ℕ} (hx : x ∈ (comp ℓ (j + 1) top).V)
    (h : (padTree hℓ hE N).graph.Adj (ι x) u) :
    H.graph.Adj (ι x) u ∨ (ι x = ι (leafCode (j + 1)) ∧ u = maxId ℓ j top ι + 1) := by
  have hxi : ι x ∈ img ℓ j top ι := mem_img.2 ⟨x, hx, rfl⟩
  rw [RTree.adj_iff] at h
  simp only [padTree] at h
  rcases h with ⟨-, hr, hp⟩ | ⟨hu, hur, hp⟩
  · have hx0 : x ≠ 0 := by rintro rfl; exact hr rfl
    rw [ite_eq_right (not_lt.2 (le_maxId hxi))] at hp
    subst hp
    exact Or.inl (H.adj_par (hE.mem x hx) (hE.ne_root hx hx0))
  · rcases Finset.mem_union.1 hu with hu | hu
    · obtain ⟨x', hx', rfl⟩ := mem_img.1 hu
      have hx0 : x' ≠ 0 := by rintro rfl; exact hur rfl
      rw [ite_eq_right (not_lt.2 (le_maxId hu))] at hp
      rw [← hp]
      exact Or.inl (H.adj_par (hE.mem x' hx') (hE.ne_root hx' hx0)).symm
    · rw [Finset.mem_Ioc] at hu
      rw [ite_eq_left hu.1] at hp
      split_ifs at hp with h1
      · exact Or.inr ⟨hp.symm, h1⟩
      · have := le_maxId hxi; omega

lemma padTree_adj_pad {v u : ℕ} (hv : maxId ℓ j top ι < v)
    (h : (padTree hℓ hE N).graph.Adj v u) :
    u = (padTree hℓ hE N).par v ∨ u = v + 1 := by
  rw [RTree.adj_iff] at h
  rcases h with ⟨-, -, hp⟩ | ⟨hu, hur, hp⟩
  · exact Or.inl hp.symm
  · right
    simp only [padTree] at hu hur hp
    rcases Finset.mem_union.1 hu with hu | hu
    · obtain ⟨x', hx', rfl⟩ := mem_img.1 hu
      have hx0 : x' ≠ 0 := by rintro rfl; exact hur rfl
      rw [ite_eq_right (not_lt.2 (le_maxId hu)), hE.par_eq x' hx' hx0] at hp
      have := le_maxId (mem_img.2 ⟨_, (par_wf ℓ _ _ x' hx' hx0).1, rfl⟩ : ι _ ∈ img ℓ j top ι)
      omega
    · rw [Finset.mem_Ioc] at hu
      rw [ite_eq_left hu.1] at hp
      split_ifs at hp with h1
      · have := le_maxId (mem_img.2 ⟨_, (leafCode_spec ℓ (hℓ1 hℓ) j top).1, rfl⟩ :
          ι (leafCode (j + 1)) ∈ img ℓ j top ι)
        omega
      · omega

lemma padTree_maxDeg (hH : HostOK H hl) : (padTree hℓ hE N).toInst.MaxDegLE 3 := by
  intro v
  simp only [RTree.toInst_G]
  by_cases hv : v ∈ img ℓ j top ι
  · obtain ⟨x, hx, rfl⟩ := mem_img.1 hv
    have hfin := H.neighborSet_finite (ι x)
    by_cases hw : ι x = ι (leafCode (j + 1))
    · have hsub : (padTree hℓ hE N).graph.neighborSet (ι x) ⊆
          insert (maxId ℓ j top ι + 1) (H.graph.neighborSet (ι x)) := by
        intro u hu
        rcases padTree_adj_img hℓ hE N hx hu with h | ⟨-, rfl⟩
        · exact Set.mem_insert_of_mem _ h
        · exact Set.mem_insert _ _
      have hlf := leafCode_spec ℓ (hℓ1 hℓ) j top
      have hl1 : hl (ι x) = 1 := by rw [hw, hE.lev _ hlf.1, hlf.2.1]
      have hup := (hH (ι x) (hE.mem x hx)).2.2.1
      have heq : {u | H.graph.Adj (ι x) u ∧ hl (ι x) ≤ hl u} = H.graph.neighborSet (ι x) := by
        ext u
        simp only [Set.mem_ofPred_eq, mem_neighborSet, and_iff_left_iff_imp, hl1]
        intro hu
        exact (hH u (H.adj_mem hu.symm)).1
      rw [heq] at hup
      calc _ ≤ (insert (maxId ℓ j top ι + 1) (H.graph.neighborSet (ι x))).ncard :=
            Set.ncard_le_ncard hsub (hfin.insert _)
        _ ≤ _ + 1 := Set.ncard_insert_le _ _
        _ ≤ 3 := by omega
    · have hsub : (padTree hℓ hE N).graph.neighborSet (ι x) ⊆ H.graph.neighborSet (ι x) := by
        intro u hu
        rcases padTree_adj_img hℓ hE N hx hu with h | ⟨h, -⟩
        · exact h
        · exact absurd h hw
      exact (Set.ncard_le_ncard hsub hfin).trans (hH (ι x) (hE.mem x hx)).2.2.2.2
  · by_cases hv' : maxId ℓ j top ι < v
    · refine ncard_le_three_of_subset (a := (padTree hℓ hE N).par v) (b := v + 1) (c := v + 1) ?_
      intro u hu
      rcases padTree_adj_pad hℓ hE N hv' hu with rfl | rfl <;> simp
    · have : (padTree hℓ hE N).graph.neighborSet v = ∅ := by
        ext u
        simp only [mem_neighborSet, Set.mem_empty_iff_false, iff_false]
        intro hu
        have hm := (padTree hℓ hE N).adj_mem hu
        simp only [padTree, Finset.mem_union, Finset.mem_Ioc] at hm
        rcases hm with hm | hm
        · exact hv hm
        · exact hv' hm.1
      simp [this]

/-- Away from the root and the attachment point, the padded graph looks like the host. -/
lemma padTree_adj_iff {x : ℕ} (hx : x ∈ (comp ℓ (j + 1) top).V) (hx0 : x ≠ 0)
    (hxl : x ≠ leafCode (j + 1)) (u : ℕ) :
    (padTree hℓ hE N).graph.Adj (ι x) u ↔ H.graph.Adj (ι x) u := by
  constructor
  · intro h
    rcases padTree_adj_img hℓ hE N hx h with h | ⟨h, -⟩
    · exact h
    · exact absurd (hE.inj h) hxl
  · intro h
    have hxi : ι x ∈ img ℓ j top ι := mem_img.2 ⟨x, hx, rfl⟩
    rw [RTree.adj_iff]
    simp only [padTree]
    rcases (hE.adj_iff hx u).1 h with ⟨-, rfl⟩ | ⟨h0, -, -⟩ | ⟨x', hx', hx'0, hpar, rfl⟩
    · refine Or.inl ⟨Finset.mem_union_left _ hxi, fun h' => hx0 (hE.inj h'), ?_⟩
      rw [ite_eq_right (not_lt.2 (le_maxId hxi)), hE.par_eq x hx hx0]
    · exact absurd h0 hx0
    · have hx'i : ι x' ∈ img ℓ j top ι := mem_img.2 ⟨x', hx', rfl⟩
      refine Or.inr ⟨Finset.mem_union_left _ hx'i, fun h' => hx'0 (hE.inj h'), ?_⟩
      rw [ite_eq_right (not_lt.2 (le_maxId hx'i)), hE.par_eq x' hx' hx'0, hpar]

lemma edist_le_of_lt {G : SimpleGraph ℕ} {u y T : ℕ} (h : G.edist u y < (T + 1 : ℕ)) :
    G.edist u y ≤ T := by
  rw [Nat.cast_add, Nat.cast_one] at h
  exact Order.le_of_lt_add_one h

/-- Middle nodes of the path cannot distinguish the host from the padded graph. -/
lemma gAgree_padTree {t T : ℕ} (ht : T + 1 ≤ t) (ht' : t < ℓ (j + 1)) :
    Cslib.Local.GAgree H.graph (padTree hℓ hE N).graph (ι (Nat.pair 0 t)) (T + 1) := by
  intro y hy u
  have hd := edist_le_of_lt hy
  have hpt := path_mem ℓ j top ht'
  obtain ⟨x', hx', rfl, h1, -⟩ := hE.pos_close hpt hd (by rw [pos_path]; omega)
  rw [pos_path] at h1
  have hx0 : x' ≠ 0 := by
    rintro rfl; rw [show (0 : ℕ) = Nat.pair 0 0 by decide, pos_path] at h1; omega
  have hxl : x' ≠ leafCode (j + 1) := by
    rintro rfl; rw [(leafCode_spec ℓ (hℓ1 hℓ) j top).2.2] at h1; omega
  exact (padTree_adj_iff hℓ hE N hx' hx0 hxl u).symm

end Pad

/-- Property 3 of the proof of Theorem 1: if every run on an `N`-node tree of maximum degree `3`
terminates by round `T` at every node, then the middle nodes of an embedded component terminate by
round `T` in the host. -/
theorem time_le_of_pad {A : Alg Label} (hA : A.IsLocal) (hℓ : ∀ i, 2 ≤ ℓ i) {T N : ℕ}
    (hrun : ∀ I : Inst, I.MaxDegLE 3 → I.V.card = N → ∀ v ∈ I.V, A.time I v ≤ T)
    (hN : (comp ℓ (j + 1) top).V.card ≤ N) (hH : HostOK H hl) (hE : Emb ℓ H hl (j + 1) top ι)
    {t : ℕ} (ht : T + 1 ≤ t) (ht' : t < ℓ (j + 1)) :
    A.time H.toInst (ι (Nat.pair 0 t)) ≤ T := by
  have hpt := path_mem ℓ j top ht'
  have hmem : ι (Nat.pair 0 t) ∈ (padTree hℓ hE N).V :=
    Finset.mem_union_left _ (mem_img.2 ⟨_, hpt, rfl⟩)
  have hloc := hA H.toInst (padTree hℓ hE N).toInst (ι (Nat.pair 0 t)) T (hE.mem _ hpt) hmem
    (gAgree_padTree hℓ hE N ht ht')
  exact hloc.1.2 (hrun _ (padTree_maxDeg hℓ hE N hH) (padTree_card hℓ hE N hN) _ hmem)

end Podc.TreesNetworkSizeKnowledge
