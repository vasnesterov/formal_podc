import Papers.PODC2016.ShortcutsNoEmbedding.Defs
import Podc.Foundations.Combinatorics.SimpleGraph.TreeCut

/-!
# The core subroutine (Lemma 5 and the combinatorial part of Lemma 4 of [HIZ16])

Fix a rooted spanning tree `T` and parts `P`. Tree edges are identified with their lower endpoints.
For a set `U` of *unusable* tree edges, the computed shortcut `H'_i` assigns to part `i` every
usable tree edge that can see `P i` (`RootedTree.cutShortcut`: all ancestor edges of `P i` in the
forest `T \ U`).

* `CoreSlow` (Algorithm 1) processes the tree bottom-up: `L_v` is the set of parts that `v`'s parent
  edge can see in `T \ U` (where `U` is the set of edges marked so far, all below `v`), and the
  edge is marked unusable iff `|L_v| > 2c`. Its output `coreSlowCut T P c` is the unique set `U`
  with `v ∈ U ↔ v ≠ root ∧ 2c < |L_v(U)|` (`coreSlowCut_spec`, uniqueness: `RootedTree.cut_unique`;
  existence is the bottom-up construction `RootedTree.exists_cut`).
* `many_good_of_cut` (the heart of the proofs of Lemmas 4 and 5): for **any** set `U` of tree
  edges each of which sees at least `2c` parts, if some `T`-restricted shortcut `H` has congestion
  `≤ c` and block parameter `≤ b`, then at least half of the parts get at most `3b` block
  components in `H'`. The blame argument is formalized via tops of blocks:
  `blockParam_cutShortcut_le` (`#blocks(H'_i) ≤ #blocks(H_i) + #missed_i`) and
  `card_blamed_le` (part `i` is blamed for at most `#blocks(H_i)` unusable edges).
* `lemma_5`: CoreSlow's shortcut has congestion `≤ 2c` and at least half of the parts have at most
  `3b` block components; every list sent up the tree has at most `2c` part IDs
  (`card_coreSlow_list_le`), so the subroutine takes `depth(T)` phases of `≤ 2c` rounds.
* `lemma_4_combinatorial`: the deterministic part of Lemma 4 (CoreFast): if, as the paper's
  Chernoff bounds give w.h.p., every unusable edge sees `≥ 2c` parts and every usable edge sees
  `≤ 8c` parts, then the congestion is `≤ 8c` and half of the parts have `≤ 3b` blocks.
-/

set_option linter.unusedSectionVars false

namespace ShortcutsNoEmbedding

open SimpleGraph Finset RootedTree

variable {V ι : Type*} [Fintype V] [DecidableEq V] [Fintype ι] [DecidableEq ι]
  {G : SimpleGraph V} {T : G.RootedTree}

/-! ### Tops of blocks -/

/-- If `t` is the top of `x`'s tree in `T \ U` and the climb along `H` from `x` cannot pass `t`
(because `t` is the root or `t`'s parent edge is not in `H`), then the top of the `H`-block of `x`
also has top `t` in `T \ U`. -/
theorem cutTop_climb {U : Finset V} {H : Finset (Sym2 V)} {x t : V} (ht : T.Below U t x)
    (htop : t = T.root ∨ t ∈ U) (hH : ¬ (t ≠ T.root ∧ T.edge t ∈ H)) :
    T.cutTop U (T.climb H x) = t := by
  obtain ⟨k, hk, hki⟩ := T.climb_eq_iterate H x
  obtain ⟨n, hn, hni⟩ := ht
  have hkn : k ≤ n := by
    by_contra hlt
    have := hki n (by omega)
    rw [hn] at this
    exact hH this
  refine (eq_cutTop ⟨n - k, ?_, fun j hj => ?_⟩ htop).symm
  · rw [hk, ← Function.iterate_add_apply, Nat.sub_add_cancel hkn, hn]
  · rw [hk, ← Function.iterate_add_apply]; exact hni _ (by omega)

/-- The missed edges of part `i`: unusable edges used by the canonical shortcut `H i`. -/
noncomputable def missed (U : Finset V) (H : ι → Finset (Sym2 V)) (i : ι) : Finset V :=
  U.filter fun t => T.edge t ∈ H i

variable (T) in
/-- The unusable edges that part `i` is blamed for: they can see `P i` but are not in `H i`. -/
noncomputable def blamed (P : ι → Finset V) (U : Finset V) (H : ι → Finset (Sym2 V)) (i : ι) :
    Finset V :=
  U.filter fun t => i ∈ T.seenParts P U t ∧ T.edge t ∉ H i

/-- Each block component of the computed shortcut `H'_i` corresponds to a block component of the
canonical shortcut `H_i` or to a missed edge. -/
theorem blockParam_cutShortcut_le (P : ι → Finset V) (U : Finset V) {H : ι → Finset (Sym2 V)}
    (hH : ∀ i, T.Restricts (H i)) (i : ι) :
    blockParam (P i) (T.cutShortcut P U i) ≤
      blockParam (P i) (H i) + (missed (T := T) U H i).card := by
  classical
  have h1 := RootedTreeBlocks.blockParam_le_climb_image_ncard (T := T) (P i)
    (T.cutShortcut P U i)
  have h2 : T.climb (T.cutShortcut P U i) '' (P i : Set V) = T.cutTop U '' (P i : Set V) :=
    Set.image_congr fun x hx => climb_cutShortcut_eq_cutTop hx (below_refl U x)
  have h3 : T.cutTop U '' (P i : Set V) ⊆
      (missed (T := T) U H i : Set V) ∪ T.cutTop U '' (T.climb (H i) '' (P i : Set V)) := by
    rintro _ ⟨x, hx, rfl⟩
    by_cases hm : T.cutTop U x ∈ U ∧ T.edge (T.cutTop U x) ∈ H i
    · left; simp [missed, hm.1, hm.2]
    · right
      refine ⟨T.climb (H i) x, ⟨x, hx, rfl⟩, cutTop_climb (below_cutTop U x)
        (cutTop_root_or_mem U x) fun h => ?_⟩
      rcases cutTop_root_or_mem U x with hr | hU
      · exact h.1 hr
      · exact hm ⟨hU, h.2⟩
  have h4 := RootedTreeBlocks.climb_image_ncard_le_blockParam (P := P i) (hH i)
  calc blockParam (P i) (T.cutShortcut P U i)
      ≤ (T.cutTop U '' (P i : Set V)).ncard := h2 ▸ h1
    _ ≤ (missed (T := T) U H i : Set V).ncard +
        (T.cutTop U '' (T.climb (H i) '' (P i : Set V))).ncard :=
        (Set.ncard_le_ncard h3 (Set.toFinite _)).trans (Set.ncard_union_le _ _)
    _ ≤ (missed (T := T) U H i).card + (T.climb (H i) '' (P i : Set V)).ncard := by
        rw [Set.ncard_coe_finset]
        exact Nat.add_le_add_left (Set.ncard_image_le (Set.toFinite _)) _
    _ ≤ _ := by omega

/-- A part is blamed at most once per block component of the canonical shortcut: the blamed edge
is the first unusable edge above the top of the block. -/
theorem card_blamed_le (P : ι → Finset V) {U : Finset V}
    {H : ι → Finset (Sym2 V)} (hH : ∀ i, T.Restricts (H i)) (i : ι) :
    (blamed T P U H i).card ≤ blockParam (P i) (H i) := by
  classical
  have hsub : (blamed T P U H i : Set V) ⊆ T.cutTop U '' (T.climb (H i) '' (P i : Set V)) := by
    intro t ht
    simp only [blamed, coe_filter, Set.mem_ofPred_eq] at ht
    obtain ⟨htU, hseen, hnH⟩ := ht
    obtain ⟨x, hx, hb⟩ := mem_seenParts.1 hseen
    exact ⟨T.climb (H i) x, ⟨x, hx, rfl⟩,
      cutTop_climb hb (Or.inr htU) fun h => hnH h.2⟩
  calc (blamed T P U H i).card = (blamed T P U H i : Set V).ncard := (Set.ncard_coe_finset _).symm
    _ ≤ (T.cutTop U '' (T.climb (H i) '' (P i : Set V))).ncard :=
        Set.ncard_le_ncard hsub (Set.toFinite _)
    _ ≤ (T.climb (H i) '' (P i : Set V)).ncard := Set.ncard_image_le (Set.toFinite _)
    _ ≤ _ := RootedTreeBlocks.climb_image_ncard_le_blockParam (hH i)

/-- Double counting: the total number of missed edges is at most the total number of blames,
because every unusable edge sees `≥ 2c` parts, of which at most `c` use it in `H`. -/
theorem sum_missed_le_sum_blamed (P : ι → Finset V) {U : Finset V} {c : ℕ}
    (hU : ∀ t ∈ U, t ≠ T.root ∧ 2 * c ≤ (T.seenParts P U t).card)
    {H : ι → Finset (Sym2 V)} (hHc : G.CongestionLE univ H c) :
    ∑ i, (missed (T := T) U H i).card ≤ ∑ i, (blamed T P U H i).card := by
  classical
  have hswap : ∀ p : ι → V → Prop, [∀ i t, Decidable (p i t)] →
      ∑ i, (U.filter (p i)).card = ∑ t ∈ U, (univ.filter fun i => p i t).card := by
    intro p _
    simp only [card_filter]
    exact sum_comm
  unfold missed blamed
  rw [hswap (fun i t => T.edge t ∈ H i), hswap (fun i t => i ∈ T.seenParts P U t ∧ T.edge t ∉ H i)]
  refine sum_le_sum fun t ht => ?_
  obtain ⟨hr, hseen⟩ := hU t ht
  have hc : (univ.filter fun i => T.edge t ∈ H i).card ≤ c := by
    have := hHc (T.edge t) (T.adj_parent t hr)
    exact_mod_cast this
  have hsplit : (T.seenParts P U t).card ≤
      (univ.filter fun i => i ∈ T.seenParts P U t ∧ T.edge t ∉ H i).card +
        (univ.filter fun i => T.edge t ∈ H i).card := by
    refine (card_le_card fun i hi => ?_).trans (card_union_le _ _)
    by_cases h : T.edge t ∈ H i
    · exact mem_union_right _ (by simp [h])
    · exact mem_union_left _ (by simp [hi, h])
  omega

/-- **The core of the proofs of Lemmas 4 and 5 of [HIZ16]**, relative to a set `K` of active parts
(the parts outside `K` are empty and have empty canonical shortcuts; this is used when the core
subroutine is rerun on the parts that are not yet good). Let `U` be a set of non-root tree edges
each of which sees at least `2c` parts in `T \ U`, and let `H` be any `T`-restricted shortcut with
congestion `≤ c` and block parameter `≤ b`. Then for at least half of the parts of `K` the
computed shortcut `H'_i = cutShortcut P U i` has at most `3b` block components. -/
theorem many_good_of_cut_on (P : ι → Finset V) {U : Finset V} {c b : ℕ}
    (hU : ∀ t ∈ U, t ≠ T.root ∧ 2 * c ≤ (T.seenParts P U t).card)
    {H : ι → Finset (Sym2 V)} (hHr : ∀ i, T.Restricts (H i)) (hHc : G.CongestionLE univ H c)
    (hHb : ∀ i, blockParam (P i) (H i) ≤ b) (K : Finset ι) (hK : ∀ i ∉ K, P i = ∅ ∧ H i = ∅) :
    ∃ J ⊆ K, K.card ≤ 2 * J.card ∧
      ∀ i ∈ J, blockParam (P i) (T.cutShortcut P U i) ≤ 3 * b := by
  classical
  let J := K.filter fun i => (missed (T := T) U H i).card ≤ 2 * b
  refine ⟨J, filter_subset _ _, ?_, fun i hi => ?_⟩
  · have hout : ∀ i ∉ K, (blamed T P U H i).card = 0 ∧ (missed (T := T) U H i).card = 0 := by
      intro i hi
      obtain ⟨hP, hH⟩ := hK i hi
      constructor
      · rw [card_eq_zero, eq_empty_iff_forall_notMem]
        intro t ht
        simp only [blamed, mem_filter] at ht
        obtain ⟨w, hw, -⟩ := mem_seenParts.1 ht.2.1
        simp [hP] at hw
      · rw [card_eq_zero, eq_empty_iff_forall_notMem]
        intro t ht
        simp [missed, hH] at ht
    have hsum : ∑ i ∈ K, (missed (T := T) U H i).card ≤ K.card * b := by
      rw [sum_subset (subset_univ K) fun i _ hi => (hout i hi).2]
      refine (sum_missed_le_sum_blamed P hU hHc).trans ?_
      rw [← sum_subset (subset_univ K) fun i _ hi => (hout i hi).1]
      calc ∑ i ∈ K, (blamed T P U H i).card ≤ ∑ _i ∈ K, b :=
            sum_le_sum fun i _ => (card_blamed_le P hHr i).trans (hHb i)
        _ = _ := by simp
    have hbad : (K.filter fun i => ¬ (missed (T := T) U H i).card ≤ 2 * b).card * (2 * b + 1) ≤
        K.card * b := by
      refine le_trans ?_ hsum
      calc _ = ∑ _i ∈ K.filter fun i => ¬ (missed (T := T) U H i).card ≤ 2 * b, (2 * b + 1) :=
            by simp
        _ ≤ ∑ i ∈ K.filter fun i => ¬ (missed (T := T) U H i).card ≤ 2 * b,
              (missed (T := T) U H i).card :=
            sum_le_sum fun i hi => by simp only [mem_filter] at hi; omega
        _ ≤ _ := sum_le_sum_of_subset (filter_subset _ _)
    have hsplit := card_filter_add_card_filter_not (s := K)
      (p := fun i => (missed (T := T) U H i).card ≤ 2 * b)
    set B := (K.filter fun i => ¬ (missed (T := T) U H i).card ≤ 2 * b).card
    set N := K.card
    have : 2 * B ≤ N := by
      rcases Nat.eq_zero_or_pos b with hb | hb
      · subst hb; simp at hbad; omega
      · nlinarith
    change N ≤ 2 * (K.filter fun i => (missed (T := T) U H i).card ≤ 2 * b).card
    omega
  · have h1 := blockParam_cutShortcut_le P U hHr i
    have h2 := hHb i
    simp only [J, mem_filter] at hi
    omega

/-- **The core of the proofs of Lemmas 4 and 5 of [HIZ16].** Let `U` be a set of non-root tree
edges each of which sees at least `2c` parts in `T \ U`, and let `H` be any `T`-restricted
shortcut with congestion `≤ c` and block parameter `≤ b`. Then for at least half of the parts the
computed shortcut `H'_i = cutShortcut P U i` has at most `3b` block components (more precisely,
at most `#blocks(H_i) + 2b`). -/
theorem many_good_of_cut (P : ι → Finset V) {U : Finset V} {c b : ℕ}
    (hU : ∀ t ∈ U, t ≠ T.root ∧ 2 * c ≤ (T.seenParts P U t).card)
    {H : ι → Finset (Sym2 V)} (hHr : ∀ i, T.Restricts (H i)) (hHc : G.CongestionLE univ H c)
    (hHb : ∀ i, blockParam (P i) (H i) ≤ b) :
    ∃ J : Finset ι, Fintype.card ι ≤ 2 * J.card ∧
      ∀ i ∈ J, blockParam (P i) (T.cutShortcut P U i) ≤ 3 * b := by
  obtain ⟨J, -, h1, h2⟩ := many_good_of_cut_on P hU hHr hHc hHb univ (by simp)
  exact ⟨J, by simpa using h1, h2⟩

/-! ### CoreSlow -/

variable (T) in
/-- The set of unusable edges marked by `CoreSlow` (Algorithm 1 of [HIZ16]) with congestion
parameter `c`: the unique `U` with `v ∈ U ↔ v ≠ root ∧ |L_v| > 2c`, where `L_v` is the set of
parts that `v`'s parent edge can see in `T \ U`. (It is produced by processing the tree bottom-up,
see `RootedTree.exists_cut`; uniqueness: `RootedTree.cut_unique`.) -/
noncomputable def coreSlowCut (P : ι → Finset V) (c : ℕ) : Finset V :=
  (T.exists_cut P (2 * c) (D := univ.sup T.depth) fun v => le_sup (mem_univ v)).choose

theorem coreSlowCut_spec (P : ι → Finset V) (c : ℕ) (v : V) :
    v ∈ coreSlowCut T P c ↔ v ≠ T.root ∧ 2 * c < (T.seenParts P (coreSlowCut T P c) v).card :=
  (T.exists_cut P (2 * c) (D := univ.sup T.depth) fun v => le_sup (mem_univ v)).choose_spec v

/-- Every list `L_v` sent up the tree by `CoreSlow` (over a usable edge) has at most `2c` part IDs;
so each of the `depth(T)` phases takes at most `2c` rounds (`O(D c)` rounds in total). -/
theorem card_coreSlow_list_le (P : ι → Finset V) (c : ℕ) {v : V} (hv : v ≠ T.root)
    (hU : v ∉ coreSlowCut T P c) : (T.seenParts P (coreSlowCut T P c) v).card ≤ 2 * c := by
  rw [coreSlowCut_spec] at hU
  push Not at hU
  exact hU hv

variable (T) in
/-- The shortcut computed by `CoreSlow`: the parent edge of every usable `v` is assigned to all
parts in `L_v`. -/
noncomputable def coreSlow (P : ι → Finset V) (c : ℕ) (i : ι) : Finset (Sym2 V) :=
  T.cutShortcut P (coreSlowCut T P c) i

/-- **Lemma 5 of [HIZ16].** Let `T` be a rooted spanning tree and suppose some `T`-restricted
shortcut `H` has congestion `≤ c` and block parameter `≤ b` (Definition 5). The shortcut `H'`
computed by `CoreSlow` is `T`-restricted, has congestion `≤ 2c`, and at least half of the parts
have at most `3b` block components in `H'` (each of which contains a vertex of the part). -/
theorem lemma_5 (P : ι → Finset V) {c b : ℕ} {H : ι → Finset (Sym2 V)}
    (hHr : ∀ i, T.Restricts (H i)) (hHc : G.CongestionLE univ H c)
    (hHb : ∀ i, blockParam (P i) (H i) ≤ b) :
    (∀ i, T.Restricts (coreSlow T P c i)) ∧ G.CongestionLE univ (coreSlow T P c) (2 * c : ℕ) ∧
      (∀ i, BlocksMeetPart (P i) (coreSlow T P c i)) ∧
      ∃ J : Finset ι, Fintype.card ι ≤ 2 * J.card ∧
        ∀ i ∈ J, blockParam (P i) (coreSlow T P c i) ≤ 3 * b := by
  refine ⟨fun i => restricts_cutShortcut P _ i, fun e _ => ?_,
    fun i => blocksMeetPart_cutShortcut P _ i, ?_⟩
  · exact_mod_cast card_filter_mem_cutShortcut_le univ
      (fun v hv hU => card_coreSlow_list_le P c hv hU) e
  · refine many_good_of_cut P (fun t ht => ?_) hHr hHc hHb
    have := (coreSlowCut_spec P c t).1 ht
    exact ⟨this.1, this.2.le⟩

/-- **Lemma 4 of [HIZ16], deterministic part.** `CoreFast` marks a set `U` of unusable edges by
sampling. The paper's Chernoff bounds show that w.h.p. (a) every unusable edge sees at least `2c`
parts and (b) every usable edge sees fewer than `8c` parts. Given (a) and (b), the computed
shortcut has congestion `≤ 8c` and at least half of the parts have at most `3b` block
components. -/
theorem lemma_4_combinatorial (P : ι → Finset V) {c b : ℕ} {U : Finset V}
    (hUa : ∀ t ∈ U, t ≠ T.root ∧ 2 * c ≤ (T.seenParts P U t).card)
    (hUb : ∀ v, v ≠ T.root → v ∉ U → (T.seenParts P U v).card ≤ 8 * c)
    {H : ι → Finset (Sym2 V)} (hHr : ∀ i, T.Restricts (H i)) (hHc : G.CongestionLE univ H c)
    (hHb : ∀ i, blockParam (P i) (H i) ≤ b) :
    (∀ i, T.Restricts (T.cutShortcut P U i)) ∧
      G.CongestionLE univ (T.cutShortcut P U) (8 * c : ℕ) ∧
      ∃ J : Finset ι, Fintype.card ι ≤ 2 * J.card ∧
        ∀ i ∈ J, blockParam (P i) (T.cutShortcut P U i) ≤ 3 * b :=
  ⟨fun i => restricts_cutShortcut P _ i,
    fun e _ => by exact_mod_cast card_filter_mem_cutShortcut_le univ hUb e,
    many_good_of_cut P hUa hHr hHc hHb⟩

end ShortcutsNoEmbedding
