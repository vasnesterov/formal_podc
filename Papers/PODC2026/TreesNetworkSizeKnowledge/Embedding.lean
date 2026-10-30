import Papers.PODC2026.TreesNetworkSizeKnowledge.Construction

/-!
# Hosts and embedded components

The induction in the proof of Theorem 1 is about a level-`j` component of the lower bound graph,
but it must be applied not only in the lower bound graph `G` itself, but also in the modified
graphs `Ĝ` produced by the parity surgery (see `differencies.md`). We therefore work with an
arbitrary *host*: a rooted tree `H` with a level labelling `hl` satisfying the local conditions of
`levelSet_eq` and maximum degree `3` (`HostOK`), into which a component `comp ℓ j top` is
*embedded* by an injective renaming of identifiers `ι` (`Emb`): the component is a union of
subtrees of `H` hanging from one edge (from its root to a node of higher level), or all of `H`.

* `Emb.adj_iff`, `Emb.path_adj_iff`: the neighbours in `H` of an embedded node.
* `Emb.child`: the components attached to the path are embedded as well.
* `Emb.localOK`: the host conditions hold automatically at embedded nodes (so the lower bound
  graph itself is a host, `hostOK_top`).
* `pot`, `Emb.pot_adj`, `pot_le_of_edist`: the position along the path is a 1-Lipschitz potential,
  which bounds distances from below.
-/

namespace Podc.TreesNetworkSizeKnowledge

open SimpleGraph

/-- The local host conditions at a node. -/
def LocalOK (H : RTree) (hl : ℕ → ℕ) (v : ℕ) : Prop :=
  1 ≤ hl v ∧ (∀ u, H.graph.Adj v u → hl v ≤ hl u + 1) ∧
  {u | H.graph.Adj v u ∧ hl v ≤ hl u}.ncard ≤ 2 ∧
  (2 ≤ hl v → 3 ≤ (H.graph.neighborSet v).ncard) ∧ (H.graph.neighborSet v).ncard ≤ 3

/-- A host: a rooted tree with a level labelling satisfying the local conditions everywhere. -/
def HostOK (H : RTree) (hl : ℕ → ℕ) : Prop := ∀ v ∈ H.V, LocalOK H hl v

lemma RTree.neighborSet_finite (H : RTree) (v : ℕ) : (H.graph.neighborSet v).Finite :=
  (H.V.finite_toSet).subset fun _ hu => H.adj_mem hu.symm

lemma HostOK.maxDeg {H : RTree} {hl : ℕ → ℕ} (h : HostOK H hl) : H.toInst.MaxDegLE 3 := by
  intro v
  by_cases hv : v ∈ H.V
  · exact (h v hv).2.2.2.2
  · have : H.graph.neighborSet v = ∅ := by
      ext u; simp only [mem_neighborSet, Set.mem_empty_iff_false, iff_false]
      exact fun hu => hv (H.adj_mem hu)
    simp [this]

lemma HostOK.inLevel_iff {H : RTree} {hl : ℕ → ℕ} (h : HostOK H hl) (i v : ℕ) :
    InLevel H.graph (H.V : Set ℕ) i v ↔ v ∈ H.V ∧ hl v = i :=
  Podc.TreesNetworkSizeKnowledge.inLevel_iff H.graph H.V hl (fun _ _ hab => H.adj_mem hab)
    (fun v hv => (h v hv).1) (fun v hv => (h v hv).2.1) (fun v hv => (h v hv).2.2.1)
    (fun v hv => (h v hv).2.2.2.1) i v

variable (ℓ : ℕ → ℕ)

/-- `ι` embeds the component `comp ℓ j top` into the host `H` (levels `hl`). -/
structure Emb (H : RTree) (hl : ℕ → ℕ) (j : ℕ) (top : Bool) (ι : ℕ → ℕ) : Prop where
  inj : Function.Injective ι
  mem : ∀ x ∈ (comp ℓ j top).V, ι x ∈ H.V
  root_iff : ∀ x ∈ (comp ℓ j top).V, ι x = H.root ↔ (top = true ∧ x = 0)
  par_eq : ∀ x ∈ (comp ℓ j top).V, x ≠ 0 → H.par (ι x) = ι ((comp ℓ j top).par x)
  par_root : top = false → ∀ x ∈ (comp ℓ j top).V, H.par (ι 0) ≠ ι x
  lev_par_root : top = false → j < hl (H.par (ι 0))
  foreign : ∀ y ∈ H.V, y ≠ H.root → ∀ x ∈ (comp ℓ j top).V, H.par y = ι x →
    ∃ x' ∈ (comp ℓ j top).V, y = ι x'
  lev : ∀ x ∈ (comp ℓ j top).V, hl (ι x) = (comp ℓ j top).lev x

variable {ℓ} {H : RTree} {hl : ℕ → ℕ} {j : ℕ} {top : Bool} {ι : ℕ → ℕ}

namespace Emb

lemma ne_root (hE : Emb ℓ H hl j top ι) {x : ℕ} (hx : x ∈ (comp ℓ j top).V) (h0 : x ≠ 0) :
    ι x ≠ H.root := fun h => h0 ((hE.root_iff x hx).1 h).2

/-- A node of `H` whose parent is embedded is embedded, as a child in the component. -/
lemma foreign' (hE : Emb ℓ H hl j top ι) {y x : ℕ} (hy : y ∈ H.V) (hyr : y ≠ H.root)
    (hx : x ∈ (comp ℓ j top).V) (h : H.par y = ι x) :
    ∃ x' ∈ (comp ℓ j top).V, x' ≠ 0 ∧ (comp ℓ j top).par x' = x ∧ y = ι x' := by
  obtain ⟨x', hx', rfl⟩ := hE.foreign y hy hyr x hx h
  have hx0 : x' ≠ 0 := by
    rintro rfl
    cases top
    · exact hE.par_root rfl x hx h
    · exact hyr ((hE.root_iff 0 hx').2 ⟨rfl, rfl⟩)
  refine ⟨x', hx', hx0, hE.inj ?_, rfl⟩
  rw [← hE.par_eq x' hx' hx0, h]

/-- The neighbours in the host of an embedded node. -/
lemma adj_iff (hE : Emb ℓ H hl j top ι) {x : ℕ} (hx : x ∈ (comp ℓ j top).V) (y : ℕ) :
    H.graph.Adj (ι x) y ↔ (x ≠ 0 ∧ y = ι ((comp ℓ j top).par x)) ∨
      (x = 0 ∧ top = false ∧ y = H.par (ι 0)) ∨
      (∃ x' ∈ (comp ℓ j top).V, x' ≠ 0 ∧ (comp ℓ j top).par x' = x ∧ y = ι x') := by
  rw [H.adj_iff]
  constructor
  · rintro (⟨-, hr, rfl⟩ | ⟨hy, hyr, h⟩)
    · by_cases h0 : x = 0
      · subst h0
        cases top
        · exact Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)
        · exact absurd ((hE.root_iff 0 hx).2 ⟨rfl, rfl⟩) hr
      · exact Or.inl ⟨h0, hE.par_eq x hx h0⟩
    · exact Or.inr (Or.inr (hE.foreign' hy hyr hx h))
  · rintro (⟨h0, rfl⟩ | ⟨rfl, htop, rfl⟩ | ⟨x', hx', hx0, hpar, rfl⟩)
    · exact Or.inl ⟨hE.mem x hx, hE.ne_root hx h0, hE.par_eq x hx h0⟩
    · refine Or.inl ⟨hE.mem 0 hx, fun h => ?_, rfl⟩
      have := ((hE.root_iff 0 hx).1 h).1
      rw [htop] at this; exact Bool.false_ne_true this
    · refine Or.inr ⟨hE.mem x' hx', hE.ne_root hx' hx0, ?_⟩
      rw [hE.par_eq x' hx' hx0, hpar]

end Emb

/-! ### Membership in a component -/

lemma path_mem_iff {j : ℕ} {top : Bool} {t : ℕ} :
    Nat.pair 0 t ∈ (comp ℓ (j + 1) top).V ↔ t < ℓ (j + 1) := by
  refine ⟨fun h => ?_, path_mem ℓ j top⟩
  rcases (mem_V ℓ j top).1 h with ⟨t', ht', he⟩ | ⟨t', ht', b, hb, hbr, y, hy, he⟩
  · rw [Nat.pair_eq_pair] at he; omega
  · rw [Nat.pair_eq_pair] at he; omega

lemma child_mem_iff {j : ℕ} {top : Bool} {t b y : ℕ} (hb : b < 2) :
    Nat.pair (2 * t + b + 1) y ∈ (comp ℓ (j + 1) top).V ↔
      t < ℓ (j + 1) ∧ HasBr (ℓ (j + 1)) top t b ∧ y ∈ (comp ℓ j false).V := by
  refine ⟨fun h => ?_, fun ⟨h1, h2, h3⟩ => child_mem ℓ j top h1 hb h2 h3⟩
  rcases (mem_V ℓ j top).1 h with ⟨t', ht', he⟩ | ⟨t', ht', b', hb', hbr, y', hy', he⟩
  · rw [Nat.pair_eq_pair] at he; omega
  · rw [Nat.pair_eq_pair] at he
    obtain ⟨h1, rfl⟩ := he
    obtain ⟨rfl, rfl⟩ : t = t' ∧ b = b' := by omega
    exact ⟨ht', hbr, hy'⟩

lemma zero_mem_of_mem {j : ℕ} {top : Bool} {y : ℕ} (hy : y ∈ (comp ℓ j top).V) :
    0 ∈ (comp ℓ j top).V := by
  cases j with
  | zero => simp at hy
  | succ j =>
    rcases (mem_V ℓ j top).1 hy with ⟨t, ht, -⟩ | ⟨t, ht, -⟩ <;>
      exact path_mem ℓ j top (t := 0) (by omega)

lemma ne_zero_of_mem {j : ℕ} {top : Bool} {y : ℕ} (hy : y ∈ (comp ℓ j top).V) : j ≠ 0 := by
  rintro rfl; simp at hy

namespace Emb

/-- The neighbours of the path node `t` of an embedded component. -/
lemma path_adj_iff (hE : Emb ℓ H hl (j + 1) top ι) {t : ℕ} (ht : t < ℓ (j + 1)) (y : ℕ) :
    H.graph.Adj (ι (Nat.pair 0 t)) y ↔
      (t ≠ 0 ∧ y = ι (Nat.pair 0 (t - 1))) ∨ (t = 0 ∧ top = false ∧ y = H.par (ι 0)) ∨
      (t + 1 < ℓ (j + 1) ∧ y = ι (Nat.pair 0 (t + 1))) ∨
      (∃ b < 2, HasBr (ℓ (j + 1)) top t b ∧ 0 ∈ (comp ℓ j false).V ∧
        y = ι (Nat.pair (2 * t + b + 1) 0)) := by
  have h0t : ∀ t, Nat.pair 0 t = 0 ↔ t = 0 := fun t => by rw [pair_eq_zero_iff]; simp
  rw [hE.adj_iff (path_mem ℓ j top ht), par_path]
  simp only [ne_eq, h0t]
  constructor
  · rintro (h | ⟨rfl, h2, rfl⟩ | ⟨x', hx', hx0, hpar, rfl⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨rfl, h2, by simp⟩)
    · rcases par_eq_path ℓ j top hx' hx0 hpar with rfl | ⟨b, hb, hbr, rfl⟩
      · exact Or.inr (Or.inr (Or.inl ⟨path_mem_iff.1 hx', rfl⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨b, hb, hbr, ((child_mem_iff hb).1 hx').2.2, rfl⟩))
  · rintro (h | ⟨rfl, h2, rfl⟩ | ⟨h1, rfl⟩ | ⟨b, hb, hbr, h0, rfl⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨rfl, h2, by simp⟩)
    · refine Or.inr (Or.inr ⟨_, path_mem ℓ j top h1, by rw [h0t]; omega, ?_, rfl⟩)
      rw [par_path]; simp
    · refine Or.inr (Or.inr ⟨_, child_mem ℓ j top ht hb hbr h0, ?_, par_childRoot ℓ j top hb, rfl⟩)
      rw [pair_eq_zero_iff]; omega

/-- The components attached to the path of an embedded component are embedded. -/
lemma child (hE : Emb ℓ H hl (j + 1) top ι) {t b : ℕ} (ht : t < ℓ (j + 1)) (hb : b < 2)
    (hbr : HasBr (ℓ (j + 1)) top t b) (h0 : 0 ∈ (comp ℓ j false).V) :
    Emb ℓ H hl j false (ι ∘ Nat.pair (2 * t + b + 1)) where
  inj := hE.inj.comp fun _ _ h => (Nat.pair_eq_pair.1 h).2
  mem y hy := hE.mem _ (child_mem ℓ j top ht hb hbr hy)
  root_iff y hy := by
    simp only [Function.comp_apply, Bool.false_eq_true, false_and, iff_false]
    rw [hE.root_iff _ (child_mem ℓ j top ht hb hbr hy), pair_eq_zero_iff]; omega
  par_eq y hy hy0 := by
    simp only [Function.comp_apply]
    rw [hE.par_eq _ (child_mem ℓ j top ht hb hbr hy) (by rw [Ne, pair_eq_zero_iff]; omega),
      par_child ℓ j top _ (by omega) hy0]
  par_root _ y hy := by
    simp only [Function.comp_apply]
    rw [hE.par_eq _ (child_mem ℓ j top ht hb hbr h0) (by rw [Ne, pair_eq_zero_iff]; omega),
      par_childRoot ℓ j top hb]
    intro h
    have := hE.inj h
    rw [Nat.pair_eq_pair] at this; omega
  lev_par_root _ := by
    simp only [Function.comp_apply]
    rw [hE.par_eq _ (child_mem ℓ j top ht hb hbr h0) (by rw [Ne, pair_eq_zero_iff]; omega),
      par_childRoot ℓ j top hb, hE.lev _ (path_mem ℓ j top ht), lev_path]
    omega
  foreign y' hy' hyr y hy h := by
    obtain ⟨x', hx', hx0, hpar, rfl⟩ := hE.foreign' hy' hyr (child_mem ℓ j top ht hb hbr hy) h
    obtain ⟨y'', hy'', -, -, rfl⟩ := par_eq_child ℓ j top (by omega) hx' hx0 hpar
    exact ⟨y'', hy'', rfl⟩
  lev y hy := by
    simp only [Function.comp_apply]
    rw [hE.lev _ (child_mem ℓ j top ht hb hbr hy), lev_child ℓ j top _ (by omega)]

end Emb

/-! ### Counting helpers -/

lemma ncard_le_two_of_subset {s : Set ℕ} {a b : ℕ} (h : s ⊆ {a, b}) : s.ncard ≤ 2 :=
  (Set.ncard_le_ncard h (Set.toFinite _)).trans <|
    (Set.ncard_insert_le _ _).trans (by rw [Set.ncard_singleton])

lemma ncard_le_three_of_subset {s : Set ℕ} {a b c : ℕ} (h : s ⊆ {a, b, c}) : s.ncard ≤ 3 :=
  (Set.ncard_le_ncard h (Set.toFinite _)).trans <|
    (Set.ncard_insert_le _ _).trans (by
      have := (Set.ncard_insert_le b {c}); rw [Set.ncard_singleton] at this; omega)

lemma three_le_ncard {s : Set ℕ} (hs : s.Finite) {a b c : ℕ} (ha : a ∈ s) (hb : b ∈ s)
    (hc : c ∈ s) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) : 3 ≤ s.ncard := by
  have h3 : ({a, b, c} : Set ℕ).ncard = 3 := Set.ncard_eq_three.2 ⟨a, b, c, hab, hac, hbc, rfl⟩
  rw [← h3]
  refine Set.ncard_le_ncard ?_ hs
  intro x hx
  rcases hx with rfl | rfl | rfl <;> assumption

/-! ### Distance lower bounds from a potential -/

-- CSLib candidate
/-- A potential that grows by at most one along edges bounds distances from below. -/
lemma pot_le_of_edist {G : SimpleGraph ℕ} (f : ℕ → ℤ) (hf : ∀ a b, G.Adj a b → f b ≤ f a + 1)
    {u x d : ℕ} (h : G.edist u x ≤ d) : f x ≤ f u + d ∧ f u ≤ f x + d := by
  have hne : G.edist u x ≠ ⊤ := ne_top_of_le_ne_top (by simp) h
  obtain ⟨p, hp⟩ := (SimpleGraph.edist_ne_top_iff_reachable.1 hne).exists_walk_length_eq_edist
  have hlen : p.length ≤ d := by
    have : (p.length : ℕ∞) ≤ d := hp ▸ h
    exact_mod_cast this
  suffices ∀ {a b : ℕ} (q : G.Walk a b), f b ≤ f a + q.length ∧ f a ≤ f b + q.length by
    obtain ⟨h1, h2⟩ := this p
    constructor <;> omega
  intro a b q
  induction q with
  | nil => simp
  | cons hadj q ih =>
    have h1 := hf _ _ hadj
    have h2 := hf _ _ hadj.symm
    simp only [Walk.length_cons]
    push_cast
    omega

/-- The potential: the position of an embedded node, and `-1` outside the component. -/
noncomputable def pot (ℓ : ℕ → ℕ) (j : ℕ) (top : Bool) (ι : ℕ → ℕ) (y : ℕ) : ℤ := by
  classical
  exact if h : ∃ x ∈ (comp ℓ j top).V, ι x = y then ((comp ℓ j top).pos h.choose : ℤ) else -1

lemma pot_apply (hι : Function.Injective ι) {x : ℕ} (hx : x ∈ (comp ℓ j top).V) :
    pot ℓ j top ι (ι x) = (comp ℓ j top).pos x := by
  have h : ∃ x' ∈ (comp ℓ j top).V, ι x' = ι x := ⟨x, hx, rfl⟩
  simp only [pot, h, ↓reduceDIte]
  rw [hι h.choose_spec.2]

lemma pot_of_not {y : ℕ} (h : ∀ x ∈ (comp ℓ j top).V, ι x ≠ y) : pot ℓ j top ι y = -1 := by
  have h' : ¬ ∃ x ∈ (comp ℓ j top).V, ι x = y := fun ⟨x, hx, he⟩ => h x hx he
  simp only [pot, h', ↓reduceDIte]

lemma pot_ge_zero_iff {y : ℕ} (hι : Function.Injective ι) (h : 0 ≤ pot ℓ j top ι y) :
    ∃ x ∈ (comp ℓ j top).V, ι x = y ∧ pot ℓ j top ι y = (comp ℓ j top).pos x := by
  by_cases hy : ∃ x ∈ (comp ℓ j top).V, ι x = y
  · obtain ⟨x, hx, rfl⟩ := hy
    exact ⟨x, hx, rfl, pot_apply hι hx⟩
  · push Not at hy
    rw [pot_of_not hy] at h; omega

namespace Emb

lemma pot_adj (hE : Emb ℓ H hl (j + 1) top ι) (a b : ℕ) (hab : H.graph.Adj a b) :
    pot ℓ (j + 1) top ι b ≤ pot ℓ (j + 1) top ι a + 1 := by
  by_cases ha : ∃ x ∈ (comp ℓ (j + 1) top).V, ι x = a
  · obtain ⟨x, hx, rfl⟩ := ha
    rw [pot_apply hE.inj hx]
    rcases (hE.adj_iff hx b).1 hab with ⟨h0, rfl⟩ | ⟨rfl, htop, rfl⟩ | ⟨x', hx', hx0, hpar, rfl⟩
    · rw [pot_apply hE.inj ((par_wf ℓ _ _ x hx h0).1)]
      have := (pos_par ℓ j top x hx h0).2; omega
    · rw [pot_of_not (fun x' hx' h => hE.par_root htop x' hx' h.symm)]; omega
    · rw [pot_apply hE.inj hx', ← hpar]
      have := (pos_par ℓ j top x' hx' hx0).1; omega
  · push Not at ha
    rw [pot_of_not ha]
    by_cases hb : ∃ x ∈ (comp ℓ (j + 1) top).V, ι x = b
    · obtain ⟨x, hx, rfl⟩ := hb
      rw [pot_apply hE.inj hx]
      rcases (hE.adj_iff hx a).1 hab.symm with ⟨h0, rfl⟩ | ⟨rfl, htop, rfl⟩ | ⟨x', hx', -, -, rfl⟩
      · exact absurd rfl (ha _ ((par_wf ℓ _ _ x hx h0).1))
      · rw [show (0 : ℕ) = Nat.pair 0 0 by decide, pos_path]; omega
      · exact absurd rfl (ha _ hx')
    · push Not at hb
      rw [pot_of_not hb]; omega

/-- Distances in the host from an embedded node are at least the difference of positions. -/
lemma pos_close (hE : Emb ℓ H hl (j + 1) top ι) {x y : ℕ} (hx : x ∈ (comp ℓ (j + 1) top).V)
    {d : ℕ} (h : H.graph.edist (ι x) y ≤ d) (hd : d < (comp ℓ (j + 1) top).pos x) :
    ∃ x' ∈ (comp ℓ (j + 1) top).V, ι x' = y ∧
      (comp ℓ (j + 1) top).pos x ≤ (comp ℓ (j + 1) top).pos x' + d ∧
      (comp ℓ (j + 1) top).pos x' ≤ (comp ℓ (j + 1) top).pos x + d := by
  have := pot_le_of_edist _ hE.pot_adj h
  rw [pot_apply hE.inj hx] at this
  obtain ⟨x', hx', rfl, hp⟩ := pot_ge_zero_iff (ℓ := ℓ) (j := j + 1) (top := top) hE.inj (y := y)
    (by omega)
  rw [hp] at this
  exact ⟨x', hx', rfl, by omega, by omega⟩

/-! ### Host conditions at embedded nodes -/

lemma lev_childRoot (hE : Emb ℓ H hl (j + 1) top ι) {t b : ℕ} (ht : t < ℓ (j + 1)) (hb : b < 2)
    (hbr : HasBr (ℓ (j + 1)) top t b) (h0 : 0 ∈ (comp ℓ j false).V) :
    hl (ι (Nat.pair (2 * t + b + 1) 0)) = j := by
  rw [hE.lev _ (child_mem ℓ j top ht hb hbr h0), lev_child ℓ j top _ (by omega)]
  obtain ⟨j', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (ne_zero_of_mem h0)
  exact lev_zero ℓ j' false

lemma lev_path' (hE : Emb ℓ H hl (j + 1) top ι) {t : ℕ} (ht : t < ℓ (j + 1)) :
    hl (ι (Nat.pair 0 t)) = j + 1 := by
  rw [hE.lev _ (path_mem ℓ j top ht), lev_path]

lemma localOK_path (hℓ : ∀ i, 2 ≤ ℓ i) (hE : Emb ℓ H hl (j + 1) top ι) {t : ℕ}
    (ht : t < ℓ (j + 1)) : LocalOK H hl (ι (Nat.pair 0 t)) := by
  have hm := hℓ (j + 1)
  have hlev := hE.lev_path' ht
  have hpe : ∀ {a b}, ι (Nat.pair 0 a) = ι (Nat.pair 0 b) ↔ a = b := fun {a b} =>
    ⟨fun h => (Nat.pair_eq_pair.1 (hE.inj h)).2, fun h => h ▸ rfl⟩
  have hce : ∀ {a b c d}, ι (Nat.pair a c) = ι (Nat.pair b d) ↔ a = b ∧ c = d := fun {a b c d} =>
    ⟨fun h => Nat.pair_eq_pair.1 (hE.inj h), fun ⟨h1, h2⟩ => h1 ▸ h2 ▸ rfl⟩
  have hpar0 : top = false → ∀ x ∈ (comp ℓ (j + 1) top).V, H.par (ι 0) ≠ ι x := hE.par_root
  have hadj := hE.path_adj_iff ht
  refine ⟨by omega, ?_, ?_, ?_, ?_⟩
  · intro u hu
    rcases (hadj u).1 hu with ⟨-, rfl⟩ | ⟨-, htop, rfl⟩ | ⟨h1, rfl⟩ | ⟨b, hb, hbr, h0, rfl⟩
    · rw [hlev, hE.lev_path' (by omega)]; omega
    · have := hE.lev_par_root htop; omega
    · rw [hlev, hE.lev_path' h1]; omega
    · rw [hlev, hE.lev_childRoot ht hb hbr h0]
  · refine ncard_le_two_of_subset (a := if t = 0 then H.par (ι 0) else ι (Nat.pair 0 (t - 1)))
      (b := ι (Nat.pair 0 (t + 1))) ?_
    rintro u ⟨hu, hl'⟩
    rcases (hadj u).1 hu with ⟨h1, rfl⟩ | ⟨h1, -, rfl⟩ | ⟨-, rfl⟩ | ⟨b, hb, hbr, h0, rfl⟩
    · simp [h1]
    · simp [h1]
    · simp
    · rw [hlev, hE.lev_childRoot ht hb hbr h0] at hl'; omega
  · intro h2
    have hj : 1 ≤ j := by omega
    obtain ⟨j', rfl⟩ := Nat.exists_eq_add_of_le' hj
    have h0 : 0 ∈ (comp ℓ (j' + 1) false).V := zero_mem ℓ j' false (fun i => by have := hℓ i; omega)
    have hfin := H.neighborSet_finite (ι (Nat.pair 0 t))
    have c0 : ∀ b < 2, HasBr (ℓ (j' + 1 + 1)) top t b →
        ι (Nat.pair (2 * t + b + 1) 0) ∈ H.graph.neighborSet (ι (Nat.pair 0 t)) :=
      fun b hb hbr => (hadj _).2 (Or.inr (Or.inr (Or.inr ⟨b, hb, hbr, h0, rfl⟩)))
    have hc01 : ι (Nat.pair (2 * t + 0 + 1) 0) ≠ ι (Nat.pair (2 * t + 1 + 1) 0) := by
      rw [Ne, hce]; omega
    rcases Nat.eq_zero_or_pos t with rfl | htpos
    · have hnext : ι (Nat.pair 0 1) ∈ H.graph.neighborSet (ι (Nat.pair 0 0)) :=
        (hadj _).2 (Or.inr (Or.inr (Or.inl ⟨by omega, rfl⟩)))
      cases top
      · have hp : H.par (ι 0) ∈ H.graph.neighborSet (ι (Nat.pair 0 0)) :=
          (hadj _).2 (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩))
        refine three_le_ncard hfin hp hnext (c0 0 (by omega) (Or.inl rfl)) ?_ ?_ ?_
        · exact hpar0 rfl _ (path_mem ℓ _ false (by omega))
        · exact hpar0 rfl _ (child_mem ℓ _ false (by omega) (by omega) (Or.inl rfl) h0)
        · rw [Ne, hce]; omega
      · refine three_le_ncard hfin hnext (c0 0 (by omega) (Or.inl rfl))
          (c0 1 (by omega) (Or.inr ⟨rfl, Or.inr ⟨rfl, rfl⟩⟩)) ?_ ?_ hc01
        · rw [Ne, hce]; omega
        · rw [Ne, hce]; omega
    · have hprev : ι (Nat.pair 0 (t - 1)) ∈ H.graph.neighborSet (ι (Nat.pair 0 t)) :=
        (hadj _).2 (Or.inl ⟨by omega, rfl⟩)
      by_cases hlast : t + 1 < ℓ (j' + 1 + 1)
      · have hnext : ι (Nat.pair 0 (t + 1)) ∈ H.graph.neighborSet (ι (Nat.pair 0 t)) :=
          (hadj _).2 (Or.inr (Or.inr (Or.inl ⟨hlast, rfl⟩)))
        refine three_le_ncard hfin hprev hnext (c0 0 (by omega) (Or.inl rfl)) ?_ ?_ ?_
        · rw [Ne, hpe]; omega
        · rw [Ne, hce]; omega
        · rw [Ne, hce]; omega
      · refine three_le_ncard hfin hprev (c0 0 (by omega) (Or.inl rfl))
          (c0 1 (by omega) (Or.inr ⟨rfl, Or.inl (by omega)⟩)) ?_ ?_ hc01
        · rw [Ne, hce]; omega
        · rw [Ne, hce]; omega
  · by_cases hbr1 : HasBr (ℓ (j + 1)) top t 1
    · rcases hbr1 with h | ⟨-, hlast | ⟨htop, rfl⟩⟩
      · omega
      · refine ncard_le_three_of_subset (a := if t = 0 then H.par (ι 0) else ι (Nat.pair 0 (t - 1)))
          (b := ι (Nat.pair (2 * t + 0 + 1) 0)) (c := ι (Nat.pair (2 * t + 1 + 1) 0)) ?_
        intro u hu
        rcases (hadj u).1 hu with ⟨h1, rfl⟩ | ⟨h1, -, rfl⟩ | ⟨h1, rfl⟩ | ⟨b, hb, hbr, h0, rfl⟩
        · simp [h1]
        · simp [h1]
        · omega
        · interval_cases b <;> simp
      · refine ncard_le_three_of_subset (a := ι (Nat.pair 0 1))
          (b := ι (Nat.pair (2 * 0 + 0 + 1) 0)) (c := ι (Nat.pair (2 * 0 + 1 + 1) 0)) ?_
        intro u hu
        rcases (hadj u).1 hu with ⟨h1, rfl⟩ | ⟨h1, h2, rfl⟩ | ⟨h1, rfl⟩ | ⟨b, hb, hbr, h0, rfl⟩
        · omega
        · simp [htop] at h2
        · simp
        · interval_cases b <;> simp
    · refine ncard_le_three_of_subset (a := if t = 0 then H.par (ι 0) else ι (Nat.pair 0 (t - 1)))
        (b := ι (Nat.pair 0 (t + 1))) (c := ι (Nat.pair (2 * t + 0 + 1) 0)) ?_
      intro u hu
      rcases (hadj u).1 hu with ⟨h1, rfl⟩ | ⟨h1, -, rfl⟩ | ⟨h1, rfl⟩ | ⟨b, hb, hbr, h0, rfl⟩
      · simp [h1]
      · simp [h1]
      · simp
      · interval_cases b
        · simp
        · exact absurd hbr hbr1

/-- The host conditions hold at every embedded node. -/
lemma localOK (hℓ : ∀ i, 2 ≤ ℓ i) : ∀ (j : ℕ) {top : Bool} {H : RTree} {hl : ℕ → ℕ} {ι : ℕ → ℕ},
    Emb ℓ H hl (j + 1) top ι → ∀ x ∈ (comp ℓ (j + 1) top).V, LocalOK H hl (ι x)
  | j, top, H, hl, ι, hE, x, hx => by
    rcases (mem_V ℓ j top).1 hx with ⟨t, ht, rfl⟩ | ⟨t, ht, b, hb, hbr, y, hy, rfl⟩
    · exact hE.localOK_path hℓ ht
    · obtain ⟨j', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (ne_zero_of_mem hy)
      exact localOK hℓ j' (hE.child ht hb hbr (zero_mem_of_mem hy)) y hy

end Emb

/-! ### The lower bound graph as a host -/

/-- The lower bound graph `comp ℓ (j+1) true` as a rooted tree. -/
def topTree (hℓ : ∀ i, 2 ≤ ℓ i) (j : ℕ) : RTree where
  V := (comp ℓ (j + 1) true).V
  root := 0
  par := (comp ℓ (j + 1) true).par
  rank := (comp ℓ (j + 1) true).rank
  root_mem := zero_mem ℓ j true (fun i => by have := hℓ i; omega)
  par_mem v hv h0 := (par_wf ℓ _ _ v hv h0).1
  rank_lt v hv h0 := (par_wf ℓ _ _ v hv h0).2

lemma emb_top (hℓ : ∀ i, 2 ≤ ℓ i) (j : ℕ) :
    Emb ℓ (topTree hℓ j) (comp ℓ (j + 1) true).lev (j + 1) true id where
  inj := Function.injective_id
  mem _ hx := hx
  root_iff x _ := by simp [topTree]
  par_eq _ _ _ := rfl
  par_root h := by simp at h
  lev_par_root h := by simp at h
  foreign y hy _ _ _ _ := ⟨y, hy, rfl⟩
  lev _ _ := rfl

lemma hostOK_top (hℓ : ∀ i, 2 ≤ ℓ i) (j : ℕ) :
    HostOK (topTree hℓ j) (comp ℓ (j + 1) true).lev :=
  fun v hv => (emb_top hℓ j).localOK hℓ j v hv

end Podc.TreesNetworkSizeKnowledge
