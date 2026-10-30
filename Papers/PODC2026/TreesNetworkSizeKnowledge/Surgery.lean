import Papers.PODC2026.TreesNetworkSizeKnowledge.Embedding

/-!
# The parity surgery: the graph `Ĝ` of the proof of property 4

Given a component embedded in a host `H` and an inner path position `s`, `hatTree` removes the path
node `z = p_s` together with its attached component and joins its two path neighbours
`z₁ = p_{s-1}` and `z₂ = p_{s+1}` by an edge (the graph `Ĝ` of the paper).

* `hatTree` is again a host (`hostOK_hat`) and the components attached to the other path nodes are
  still embedded (`emb_hat_child`): this is what the induction needs, and what the paper's proof
  leaves implicit.
* `hat_adj_of_adj`, `hat_adj_cases`: edges of `Ĝ`.
* `gAgree_hat`: nodes whose position is far from `s` cannot distinguish `H` from `Ĝ`.
-/

set_option linter.unusedSectionVars false

namespace Podc.TreesNetworkSizeKnowledge

open SimpleGraph

variable {ℓ : ℕ → ℕ} {H : RTree} {hl : ℕ → ℕ} {j : ℕ} {top : Bool} {ι : ℕ → ℕ}

section Hat

variable (hE : Emb ℓ H hl (j + 1) top ι) {s : ℕ} (hs1 : 1 ≤ s) (hs2 : s + 1 < ℓ (j + 1))

/-- The removed set: `z = p_s` and its attached component. -/
def remSet (ℓ : ℕ → ℕ) (j : ℕ) (ι : ℕ → ℕ) (s : ℕ) : Finset ℕ :=
  insert (ι (Nat.pair 0 s)) ((comp ℓ j false).V.image (fun y => ι (Nat.pair (2 * s + 1) y)))

lemma mem_remSet {y : ℕ} : y ∈ remSet ℓ j ι s ↔
    y = ι (Nat.pair 0 s) ∨ ∃ y0 ∈ (comp ℓ j false).V, y = ι (Nat.pair (2 * s + 1) y0) := by
  simp only [remSet, Finset.mem_insert, Finset.mem_image]
  constructor
  · rintro (h | ⟨y0, hy0, rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨y0, hy0, rfl⟩
  · rintro (h | ⟨y0, hy0, rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨y0, hy0, rfl⟩

include hE hs1 hs2

lemma not_hasBr1 : ¬ HasBr (ℓ (j + 1)) top s 1 := by
  rintro (h | ⟨-, h | ⟨-, h⟩⟩) <;> omega

lemma s_mem : Nat.pair 0 s ∈ (comp ℓ (j + 1) top).V := path_mem ℓ j top (by omega)

lemma cs_mem {y0 : ℕ} (hy0 : y0 ∈ (comp ℓ j false).V) :
    Nat.pair (2 * s + 1) y0 ∈ (comp ℓ (j + 1) top).V := by
  simpa using child_mem ℓ j top (t := s) (b := 0) (by omega) (by omega) (Or.inl rfl) hy0

lemma remSet_sub {y : ℕ} (hy : y ∈ remSet ℓ j ι s) : y ∈ H.V ∧ y ≠ H.root := by
  rcases (mem_remSet).1 hy with rfl | ⟨y0, hy0, rfl⟩
  · exact ⟨hE.mem _ (s_mem hE hs1 hs2), hE.ne_root (s_mem hE hs1 hs2)
      (by rw [Ne, pair_eq_zero_iff]; omega)⟩
  · exact ⟨hE.mem _ (cs_mem hE hs1 hs2 hy0), hE.ne_root (cs_mem hE hs1 hs2 hy0)
      (by rw [Ne, pair_eq_zero_iff]; omega)⟩

lemma z1_notMem : ι (Nat.pair 0 (s - 1)) ∉ remSet ℓ j ι s := by
  rw [mem_remSet]
  rintro (h | ⟨y0, -, h⟩) <;> have := Nat.pair_eq_pair.1 (hE.inj h) <;> omega

lemma z2_notMem : ι (Nat.pair 0 (s + 1)) ∉ remSet ℓ j ι s := by
  rw [mem_remSet]
  rintro (h | ⟨y0, -, h⟩) <;> have := Nat.pair_eq_pair.1 (hE.inj h) <;> omega

lemma par_z : H.par (ι (Nat.pair 0 s)) = ι (Nat.pair 0 (s - 1)) := by
  rw [hE.par_eq _ (s_mem hE hs1 hs2) (by rw [Ne, pair_eq_zero_iff]; omega), par_path]

lemma par_z2 : H.par (ι (Nat.pair 0 (s + 1))) = ι (Nat.pair 0 s) := by
  rw [hE.par_eq _ (path_mem ℓ j top hs2) (by rw [Ne, pair_eq_zero_iff]; omega), par_path]; rfl

/-- Children of removed nodes are removed, except `z₂`. -/
lemma remSet_child {y : ℕ} (hy : y ∈ H.V) (hyr : y ≠ H.root) (h : H.par y ∈ remSet ℓ j ι s) :
    y ∈ remSet ℓ j ι s ∨ y = ι (Nat.pair 0 (s + 1)) := by
  rcases (mem_remSet).1 h with h | ⟨y0, hy0, h⟩
  · obtain ⟨x', hx', hx0, hpar, rfl⟩ := hE.foreign' hy hyr (s_mem hE hs1 hs2) h
    rcases par_eq_path ℓ j top hx' hx0 hpar with rfl | ⟨b, hb, hbr, rfl⟩
    · exact Or.inr rfl
    · have hb0 : b = 0 := by
        rcases Nat.lt_succ_iff_lt_or_eq.1 hb with h | h
        · omega
        · subst h; exact absurd hbr (not_hasBr1 hE hs1 hs2)
      subst hb0
      exact Or.inl ((mem_remSet).2 (Or.inr ⟨0, ((child_mem_iff hb).1 hx').2.2, rfl⟩))
  · obtain ⟨x', hx', hx0, hpar, rfl⟩ := hE.foreign' hy hyr (cs_mem hE hs1 hs2 hy0) h
    obtain ⟨y'', hy'', -, -, rfl⟩ := par_eq_child ℓ j top (by omega) hx' hx0 hpar
    exact Or.inl ((mem_remSet).2 (Or.inr ⟨y'', hy'', rfl⟩))

/-- Parents of removed nodes other than `z` are removed. -/
lemma remSet_par {y : ℕ} (hy : y ∈ remSet ℓ j ι s) (hyz : y ≠ ι (Nat.pair 0 s)) :
    H.par y ∈ remSet ℓ j ι s := by
  rcases (mem_remSet).1 hy with h | ⟨y0, hy0, rfl⟩
  · exact absurd h hyz
  · by_cases h0 : y0 = 0
    · subst h0
      have hpc := par_childRoot ℓ j top (t := s) (b := 0) (by omega)
      simp only [add_zero] at hpc
      rw [hE.par_eq _ (cs_mem hE hs1 hs2 hy0) (by rw [Ne, pair_eq_zero_iff]; omega), hpc]
      exact (mem_remSet).2 (Or.inl rfl)
    · rw [hE.par_eq _ (cs_mem hE hs1 hs2 hy0) (by rw [Ne, pair_eq_zero_iff]; omega),
        par_child ℓ j top _ (by omega) h0]
      exact (mem_remSet).2 (Or.inr ⟨_, (par_wf ℓ _ _ y0 hy0 h0).1, rfl⟩)

/-- The graph `Ĝ`. -/
def hatTree : RTree where
  V := H.V \ remSet ℓ j ι s
  root := H.root
  par y := if y = ι (Nat.pair 0 (s + 1)) then ι (Nat.pair 0 (s - 1)) else H.par y
  rank := H.rank
  root_mem := Finset.mem_sdiff.2 ⟨H.root_mem, fun h => (remSet_sub hE hs1 hs2 h).2 rfl⟩
  par_mem y hy hr := by
    rw [Finset.mem_sdiff] at hy ⊢
    split_ifs with h
    · exact ⟨hE.mem _ (path_mem ℓ j top (by omega)), z1_notMem hE hs1 hs2⟩
    · refine ⟨H.par_mem y hy.1 hr, fun h' => ?_⟩
      rcases remSet_child hE hs1 hs2 hy.1 hr h' with h'' | h''
      · exact hy.2 h''
      · exact h h''
  rank_lt y hy hr := by
    rw [Finset.mem_sdiff] at hy
    split_ifs with h
    · subst h
      have h1 := H.rank_lt _ hy.1 hr
      have hz := (remSet_sub hE hs1 hs2 ((mem_remSet).2 (Or.inl rfl)))
      have h2 := H.rank_lt _ hz.1 hz.2
      rw [par_z2 hE hs1 hs2] at h1
      rw [par_z hE hs1 hs2] at h2
      omega
    · exact H.rank_lt y hy.1 hr

lemma hat_V {y : ℕ} : y ∈ (hatTree hE hs1 hs2).V ↔ y ∈ H.V ∧ y ∉ remSet ℓ j ι s := by
  simp [hatTree]

lemma hat_root : (hatTree hE hs1 hs2).root = H.root := rfl

lemma hat_par (y : ℕ) : (hatTree hE hs1 hs2).par y =
    if y = ι (Nat.pair 0 (s + 1)) then ι (Nat.pair 0 (s - 1)) else H.par y := rfl

lemma hat_par_of_ne {y : ℕ} (h : y ≠ ι (Nat.pair 0 (s + 1))) :
    (hatTree hE hs1 hs2).par y = H.par y := by simp [hatTree, h]

lemma hat_par_z2 : (hatTree hE hs1 hs2).par (ι (Nat.pair 0 (s + 1))) = ι (Nat.pair 0 (s - 1)) := by
  simp [hatTree]

lemma z1_ne_z2 : ι (Nat.pair 0 (s - 1)) ≠ ι (Nat.pair 0 (s + 1)) := by
  intro h; have := Nat.pair_eq_pair.1 (hE.inj h); omega

lemma z_ne_z2 : ι (Nat.pair 0 s) ≠ ι (Nat.pair 0 (s + 1)) := by
  intro h; have := Nat.pair_eq_pair.1 (hE.inj h); omega

/-- `Ĝ` agrees with `H` at nodes other than `z₁`, `z₂` and the removed ones. -/
lemma hat_adj_iff {x : ℕ} (hxR : x ∉ remSet ℓ j ι s) (hx1 : x ≠ ι (Nat.pair 0 (s - 1)))
    (hx2 : x ≠ ι (Nat.pair 0 (s + 1))) (u : ℕ) :
    (hatTree hE hs1 hs2).graph.Adj x u ↔ H.graph.Adj x u := by
  rw [RTree.adj_iff, RTree.adj_iff, hat_par_of_ne hE hs1 hs2 hx2]
  simp only [hat_V, hat_root, hat_par]
  constructor
  · rintro (⟨⟨hx, -⟩, hr, hp⟩ | ⟨⟨hu, -⟩, hr, hp⟩)
    · exact Or.inl ⟨hx, hr, hp⟩
    · split_ifs at hp with h
      · exact absurd hp.symm hx1
      · exact Or.inr ⟨hu, hr, hp⟩
  · rintro (⟨hx, hr, hp⟩ | ⟨hu, hr, hp⟩)
    · exact Or.inl ⟨⟨hx, hxR⟩, hr, hp⟩
    · have huR : u ∉ remSet ℓ j ι s := by
        intro huR
        by_cases huz : u = ι (Nat.pair 0 s)
        · subst huz; rw [par_z hE hs1 hs2] at hp; exact hx1 hp.symm
        · exact hxR (hp ▸ remSet_par hE hs1 hs2 huR huz)
      have hu2 : u ≠ ι (Nat.pair 0 (s + 1)) := by
        rintro rfl; rw [par_z2 hE hs1 hs2] at hp
        exact hxR (hp ▸ (mem_remSet).2 (Or.inl rfl))
      refine Or.inr ⟨⟨hu, huR⟩, hr, ?_⟩
      rw [ite_eq_right hu2]; exact hp

lemma hat_adj_z1 (u : ℕ) : (hatTree hE hs1 hs2).graph.Adj (ι (Nat.pair 0 (s - 1))) u ↔
    (H.graph.Adj (ι (Nat.pair 0 (s - 1))) u ∧ u ≠ ι (Nat.pair 0 s)) ∨
      u = ι (Nat.pair 0 (s + 1)) := by
  have hz1R := z1_notMem hE hs1 hs2
  have hz2R := z2_notMem hE hs1 hs2
  have h12 := z1_ne_z2 hE hs1 hs2
  rw [RTree.adj_iff, RTree.adj_iff, hat_par_of_ne hE hs1 hs2 h12]
  simp only [hat_V, hat_root, hat_par]
  constructor
  · rintro (⟨⟨hx, -⟩, hr, hp⟩ | ⟨⟨hu, huR⟩, hr, hp⟩)
    · refine Or.inl ⟨Or.inl ⟨hx, hr, hp⟩, ?_⟩
      rintro rfl
      rcases remSet_child hE hs1 hs2 hx hr (hp ▸ (mem_remSet).2 (Or.inl rfl)) with h | h
      · exact hz1R h
      · exact h12 h
    · split_ifs at hp with h
      · exact Or.inr h
      · exact Or.inl ⟨Or.inr ⟨hu, hr, hp⟩, fun h' => huR (h' ▸ (mem_remSet).2 (Or.inl rfl))⟩
  · rintro (⟨hadj | ⟨hu, hr, hp⟩, huz⟩ | rfl)
    · rcases hadj with ⟨hx, hr, hp⟩
      exact Or.inl ⟨⟨hx, hz1R⟩, hr, hp⟩
    · have huR : u ∉ remSet ℓ j ι s := fun huR => hz1R (hp ▸ remSet_par hE hs1 hs2 huR huz)
      by_cases hu2 : u = ι (Nat.pair 0 (s + 1))
      · subst hu2; exact Or.inr ⟨⟨hu, huR⟩, hr, by simp⟩
      · exact Or.inr ⟨⟨hu, huR⟩, hr, by rw [ite_eq_right hu2]; exact hp⟩
    · have hz2 := hE.mem _ (path_mem ℓ j top hs2)
      exact Or.inr ⟨⟨hz2, hz2R⟩, hE.ne_root (path_mem ℓ j top hs2)
        (by rw [Ne, pair_eq_zero_iff]; omega), by simp⟩

lemma hat_adj_z2 (u : ℕ) : (hatTree hE hs1 hs2).graph.Adj (ι (Nat.pair 0 (s + 1))) u ↔
    (H.graph.Adj (ι (Nat.pair 0 (s + 1))) u ∧ u ≠ ι (Nat.pair 0 s)) ∨
      u = ι (Nat.pair 0 (s - 1)) := by
  have hz1R := z1_notMem hE hs1 hs2
  have hz2R := z2_notMem hE hs1 hs2
  have h12 := z1_ne_z2 hE hs1 hs2
  have hz2 := hE.mem _ (path_mem ℓ j top hs2)
  have hz2r := hE.ne_root (path_mem ℓ j top hs2) (by rw [Ne, pair_eq_zero_iff]; omega)
  rw [RTree.adj_iff, RTree.adj_iff]
  simp only [hat_V, hat_root, hat_par, ite_true]
  constructor
  · rintro (⟨-, -, rfl⟩ | ⟨⟨hu, huR⟩, hr, hp⟩)
    · exact Or.inr rfl
    · split_ifs at hp with h
      · exact absurd (h ▸ hp) h12
      · exact Or.inl ⟨Or.inr ⟨hu, hr, hp⟩, fun h' => huR (h' ▸ (mem_remSet).2 (Or.inl rfl))⟩
  · rintro (⟨hadj | ⟨hu, hr, hp⟩, huz⟩ | rfl)
    · rcases hadj with ⟨-, -, hp⟩
      rw [par_z2 hE hs1 hs2] at hp; exact absurd hp.symm huz
    · have huR : u ∉ remSet ℓ j ι s := fun huR => hz2R (hp ▸ remSet_par hE hs1 hs2 huR huz)
      have hu2 : u ≠ ι (Nat.pair 0 (s + 1)) := by
        rintro rfl; exact H.par_ne hu hr hp
      exact Or.inr ⟨⟨hu, huR⟩, hr, by rw [ite_eq_right hu2]; exact hp⟩
    · exact Or.inl ⟨⟨hz2, hz2R⟩, hz2r, rfl⟩

/-- Edges of `H` between kept nodes are edges of `Ĝ`. -/
lemma hat_adj_of_adj {x u : ℕ} (h : H.graph.Adj x u) (hx : x ∉ remSet ℓ j ι s)
    (hu : u ∉ remSet ℓ j ι s) : (hatTree hE hs1 hs2).graph.Adj x u := by
  have huz : u ≠ ι (Nat.pair 0 s) := fun h' => hu (h' ▸ (mem_remSet).2 (Or.inl rfl))
  by_cases h1 : x = ι (Nat.pair 0 (s - 1))
  · subst h1; exact (hat_adj_z1 hE hs1 hs2 u).2 (Or.inl ⟨h, huz⟩)
  by_cases h2 : x = ι (Nat.pair 0 (s + 1))
  · subst h2; exact (hat_adj_z2 hE hs1 hs2 u).2 (Or.inl ⟨h, huz⟩)
  exact (hat_adj_iff hE hs1 hs2 hx h1 h2 u).2 h

/-- Edges of `Ĝ` are edges of `H`, or the new edge `z₁ z₂`. -/
lemma hat_adj_cases {x u : ℕ} (h : (hatTree hE hs1 hs2).graph.Adj x u) :
    H.graph.Adj x u ∨ (x = ι (Nat.pair 0 (s - 1)) ∧ u = ι (Nat.pair 0 (s + 1))) ∨
      (x = ι (Nat.pair 0 (s + 1)) ∧ u = ι (Nat.pair 0 (s - 1))) := by
  have hx : x ∉ remSet ℓ j ι s := ((hat_V hE hs1 hs2).1 ((hatTree hE hs1 hs2).adj_mem h)).2
  by_cases h1 : x = ι (Nat.pair 0 (s - 1))
  · subst h1
    rcases (hat_adj_z1 hE hs1 hs2 u).1 h with ⟨h', -⟩ | rfl
    · exact Or.inl h'
    · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
  by_cases h2 : x = ι (Nat.pair 0 (s + 1))
  · subst h2
    rcases (hat_adj_z2 hE hs1 hs2 u).1 h with ⟨h', -⟩ | rfl
    · exact Or.inl h'
    · exact Or.inr (Or.inr ⟨rfl, rfl⟩)
  exact Or.inl ((hat_adj_iff hE hs1 hs2 hx h1 h2 u).1 h)

lemma not_adj_z1_z2 : ¬ H.graph.Adj (ι (Nat.pair 0 (s - 1))) (ι (Nat.pair 0 (s + 1))) := by
  intro h
  rcases (hE.path_adj_iff (t := s - 1) (by omega) _).1 h with
    ⟨-, h⟩ | ⟨-, htop, h⟩ | ⟨-, h⟩ | ⟨b, -, -, -, h⟩
  · have := Nat.pair_eq_pair.1 (hE.inj h); omega
  · exact hE.par_root htop _ (path_mem ℓ j top hs2) h.symm
  · have := Nat.pair_eq_pair.1 (hE.inj h); omega
  · have := Nat.pair_eq_pair.1 (hE.inj h); omega

lemma adj_z1_z : H.graph.Adj (ι (Nat.pair 0 (s - 1))) (ι (Nat.pair 0 s)) :=
  (hE.path_adj_iff (t := s - 1) (by omega) _).2
    (Or.inr (Or.inr (Or.inl ⟨by omega, by rw [Nat.sub_add_cancel hs1]⟩)))

lemma adj_z2_z : H.graph.Adj (ι (Nat.pair 0 (s + 1))) (ι (Nat.pair 0 s)) :=
  (hE.path_adj_iff (t := s + 1) hs2 _).2 (Or.inl ⟨by omega, rfl⟩)

end Hat

/-! ### `Ĝ` is a host -/

lemma ncard_swap {S : Set ℕ} (hS : S.Finite) {a b : ℕ} (ha : a ∈ S) (hb : b ∉ S) :
    (insert b (S \ {a})).ncard = S.ncard := by
  rw [Set.ncard_insert_of_notMem (fun h => hb h.1) (hS.sdiff),
    Set.ncard_sdiff_singleton_add_one ha hS]

/-- Counting neighbours with a property at a node whose neighbourhood changed by a swap. -/
lemma ncard_swap_adj {G G' : SimpleGraph ℕ} {w a b : ℕ} (P : ℕ → Prop)
    (hfin : (G.neighborSet w).Finite)
    (hG' : ∀ u, G'.Adj w u ↔ (G.Adj w u ∧ u ≠ a) ∨ u = b) (ha : G.Adj w a) (hb : ¬ G.Adj w b)
    (hPa : P a) (hPb : P b) :
    {u | G'.Adj w u ∧ P u}.ncard = {u | G.Adj w u ∧ P u}.ncard := by
  have : {u | G'.Adj w u ∧ P u} = insert b ({u | G.Adj w u ∧ P u} \ {a}) := by
    ext u
    simp only [hG', Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_sdiff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨⟨h1, h2⟩ | rfl, h3⟩
      · exact Or.inr ⟨⟨h1, h3⟩, h2⟩
      · exact Or.inl rfl
    · rintro (rfl | ⟨⟨h1, h3⟩, h2⟩)
      · exact ⟨Or.inr rfl, hPb⟩
      · exact ⟨Or.inl ⟨h1, h2⟩, h3⟩
  rw [this]
  exact ncard_swap (hfin.subset fun u hu => hu.1) ⟨ha, hPa⟩ fun h => hb h.1

lemma hostOK_hat (hH : HostOK H hl) (hE : Emb ℓ H hl (j + 1) top ι) {s : ℕ} (hs1 : 1 ≤ s)
    (hs2 : s + 1 < ℓ (j + 1)) : HostOK (hatTree hE hs1 hs2) hl := by
  intro v hv
  obtain ⟨hvH, hvR⟩ := (hat_V hE hs1 hs2).1 hv
  obtain ⟨h1, h2, h3, h4, h5⟩ := hH v hvH
  have hl1 := hE.lev_path' (t := s - 1) (by omega)
  have hl0 := hE.lev_path' (t := s) (by omega)
  have hl2 := hE.lev_path' (t := s + 1) hs2
  have hnb : ∀ v, (hatTree hE hs1 hs2).graph.neighborSet v = {u | (hatTree hE hs1 hs2).graph.Adj v u ∧ True} := by
    intro v; ext u; simp
  have hnb' : ∀ v, H.graph.neighborSet v = {u | H.graph.Adj v u ∧ True} := by
    intro v; ext u; simp
  by_cases hv1 : v = ι (Nat.pair 0 (s - 1))
  · subst hv1
    have hsw := fun P hPa hPb => ncard_swap_adj (G := H.graph) (G' := (hatTree hE hs1 hs2).graph)
      P (H.neighborSet_finite _) (hat_adj_z1 hE hs1 hs2) (adj_z1_z hE hs1 hs2)
      (not_adj_z1_z2 hE hs1 hs2) hPa hPb
    refine ⟨h1, ?_, ?_, ?_, ?_⟩
    · intro u hu
      rcases (hat_adj_z1 hE hs1 hs2 u).1 hu with ⟨h, -⟩ | rfl
      · exact h2 u h
      · omega
    · rw [hsw _ (by omega) (by omega)]; exact h3
    · rw [hnb, hsw _ trivial trivial, ← hnb']; exact h4
    · rw [hnb, hsw _ trivial trivial, ← hnb']; exact h5
  by_cases hv2 : v = ι (Nat.pair 0 (s + 1))
  · subst hv2
    have hsw := fun P hPa hPb => ncard_swap_adj (G := H.graph) (G' := (hatTree hE hs1 hs2).graph)
      P (H.neighborSet_finite _) (hat_adj_z2 hE hs1 hs2) (adj_z2_z hE hs1 hs2)
      (fun h => not_adj_z1_z2 hE hs1 hs2 h.symm) hPa hPb
    refine ⟨h1, ?_, ?_, ?_, ?_⟩
    · intro u hu
      rcases (hat_adj_z2 hE hs1 hs2 u).1 hu with ⟨h, -⟩ | rfl
      · exact h2 u h
      · omega
    · rw [hsw _ (by omega) (by omega)]; exact h3
    · rw [hnb, hsw _ trivial trivial, ← hnb']; exact h4
    · rw [hnb, hsw _ trivial trivial, ← hnb']; exact h5
  have heq := hat_adj_iff hE hs1 hs2 hvR hv1 hv2
  have hN : (hatTree hE hs1 hs2).graph.neighborSet v = H.graph.neighborSet v := by
    ext u; exact heq u
  refine ⟨h1, fun u hu => h2 u ((heq u).1 hu), ?_, ?_, ?_⟩
  · simp only [heq]; exact h3
  · rw [hN]; exact h4
  · rw [hN]; exact h5

/-- The components attached to the other path nodes are still embedded in `Ĝ`. -/
lemma emb_hat_child (hE : Emb ℓ H hl (j + 1) top ι) {s : ℕ} (hs1 : 1 ≤ s)
    (hs2 : s + 1 < ℓ (j + 1)) {t b : ℕ} (ht : t < ℓ (j + 1)) (hts : t ≠ s) (hb : b < 2)
    (hbr : HasBr (ℓ (j + 1)) top t b) (h0 : 0 ∈ (comp ℓ j false).V) :
    Emb ℓ (hatTree hE hs1 hs2) hl j false (ι ∘ Nat.pair (2 * t + b + 1)) := by
  have hC := hE.child ht hb hbr h0
  have hnR : ∀ y, ι (Nat.pair (2 * t + b + 1) y) ∉ remSet ℓ j ι s := by
    intro y h
    rcases (mem_remSet).1 h with h | ⟨y0, -, h⟩ <;> have := Nat.pair_eq_pair.1 (hE.inj h) <;> omega
  have hn2 : ∀ y, ι (Nat.pair (2 * t + b + 1) y) ≠ ι (Nat.pair 0 (s + 1)) := by
    intro y h; have := Nat.pair_eq_pair.1 (hE.inj h); omega
  exact
  { inj := hC.inj
    mem := fun y hy => (hat_V hE hs1 hs2).2 ⟨hC.mem y hy, hnR y⟩
    root_iff := hC.root_iff
    par_eq := fun y hy hy0 => by
      simp only [Function.comp_apply] at hC ⊢
      rw [hat_par_of_ne hE hs1 hs2 (hn2 y)]; exact hC.par_eq y hy hy0
    par_root := fun h y hy => by
      simp only [Function.comp_apply]
      rw [hat_par_of_ne hE hs1 hs2 (hn2 0)]; exact hC.par_root h y hy
    lev_par_root := fun h => by
      simp only [Function.comp_apply]
      rw [hat_par_of_ne hE hs1 hs2 (hn2 0)]; exact hC.lev_par_root h
    foreign := fun y' hy' hyr y hy h => by
      obtain ⟨hy'H, -⟩ := (hat_V hE hs1 hs2).1 hy'
      by_cases h2 : y' = ι (Nat.pair 0 (s + 1))
      · rw [h2, hat_par_z2] at h
        have := Nat.pair_eq_pair.1 (hE.inj h); omega
      · rw [hat_par_of_ne hE hs1 hs2 h2] at h
        exact hC.foreign y' hy'H hyr y hy h
    lev := hC.lev }

/-- Nodes at positions far from `s` cannot distinguish `H` from `Ĝ`. -/
lemma gAgree_hat (hE : Emb ℓ H hl (j + 1) top ι) {s : ℕ} (hs1 : 1 ≤ s)
    (hs2 : s + 1 < ℓ (j + 1)) {a T : ℕ} (ha : a < ℓ (j + 1)) (haT : T < a)
    (hfar : a + T + 1 < s ∨ s + 1 + T < a) :
    Cslib.Local.GAgree H.graph (hatTree hE hs1 hs2).graph (ι (Nat.pair 0 a)) (T + 1) := by
  intro y hy u
  have hd : H.graph.edist (ι (Nat.pair 0 a)) y ≤ T := by
    rw [Nat.cast_add, Nat.cast_one] at hy; exact Order.le_of_lt_add_one hy
  obtain ⟨x', hx', rfl, h1, h2⟩ := hE.pos_close (path_mem ℓ j top ha) hd (by rw [pos_path]; omega)
  rw [pos_path] at h1 h2
  have hR : ι x' ∉ remSet ℓ j ι s := by
    intro h
    rcases (mem_remSet).1 h with h | ⟨y0, -, h⟩
    · rw [hE.inj h, pos_path] at h1 h2; omega
    · have hpc := pos_child ℓ j top (t := s) (b := 0) (by omega) y0
      simp only [add_zero] at hpc
      rw [hE.inj h, hpc] at h1 h2; omega
  have hx1 : ι x' ≠ ι (Nat.pair 0 (s - 1)) := by
    intro h; rw [hE.inj h, pos_path] at h1 h2; omega
  have hx2 : ι x' ≠ ι (Nat.pair 0 (s + 1)) := by
    intro h; rw [hE.inj h, pos_path] at h1 h2; omega
  exact (hat_adj_iff hE hs1 hs2 hR hx1 hx2 u).symm

end Podc.TreesNetworkSizeKnowledge
