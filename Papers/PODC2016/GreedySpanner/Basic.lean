import Cslib.Foundations.Combinatorics.SimpleGraph.WeightedSpanner
import Cslib.Foundations.Combinatorics.SimpleGraph.ShortestWalks
import Mathlib.Combinatorics.SimpleGraph.Walk.Counting
import Mathlib.Data.Set.Finite.Lemmas

/-!
# The greedy spanner: model (Filtser–Solomon, PODC 2016, Section 2)

A weighted graph is a `G : SimpleGraph V` together with `w : Sym2 V → ℝ≥0` (CSLib convention: only
the values on edges matter); distances are CSLib's `wdist` (in `ℝ≥0∞`, `⊤` = disconnected).
The stretch `t` is a real number (`t : ℝ≥0`, `1 ≤ t` where needed).

* `IsWSpanner G H w t` — `H ≤ G` and `δ_H(u, v) ≤ t · δ_G(u, v)` for all `u, v`.
* `greedy w t L` — **Algorithm 1**: scan the list `L` of edges and add `e = {u, v}` iff
  `δ_H(u, v) > t · w(e)` for the current `H`.
* `IsGreedyOrder G w L` — `L` lists every edge of `G` exactly once, in non-decreasing order of
  weight (ties in arbitrary order). `IsGreedySpanner G w t H` — `H` is the output of *some*
  execution of Algorithm 1 (the paper's "the greedy `t`-spanner" = an arbitrary execution).
* `wt w H` — total weight of the edges of `H`.

Basic facts: `exists_isGreedySpanner`, `IsGreedySpanner.isWSpanner` (the output is a `t`-spanner),
the two properties of the scan used in all proofs (`lt_wlength_of_mem_greedySet`: an added edge is
heavier than `t⁻¹ ×` any walk between its endpoints made of earlier added edges; and
`exists_walk_of_not_mem_greedySet`: a rejected edge has a walk of earlier, hence lighter, added
edges), and `exists_isPath_wlength_eq` (weighted distances are attained by paths on finite graphs).
-/

open Finset SimpleGraph
open scoped ENNReal NNReal

namespace GreedySpanner

variable {V : Type*} {G H : SimpleGraph V} {w : Sym2 V → ℝ≥0}

/-! ### Weighted spanners with a real stretch -/

-- CSLib candidate
/-- `H` is a `t`-spanner of the weighted graph `(G, w)`. -/
def IsWSpanner (G H : SimpleGraph V) (w : Sym2 V → ℝ≥0) (t : ℝ≥0) : Prop :=
  H ≤ G ∧ ∀ u v, H.wdist w u v ≤ t * G.wdist w u v

lemma IsWSpanner.wdist_le_of_adj {t : ℝ≥0} (h : IsWSpanner G H w t) {x y : V} (hxy : G.Adj x y) :
    H.wdist w x y ≤ t * w s(x, y) :=
  (h.2 x y).trans (mul_le_mul_right (SimpleGraph.wdist_le_of_adj hxy) _)

-- CSLib candidate
/-- **Local criterion** (Section 2 of the paper): it suffices to check the stretch on edges. -/
lemma isWSpanner_of_adj {t : ℝ≥0} (ht : 1 ≤ t) (hHG : H ≤ G)
    (h : ∀ x y, G.Adj x y → H.wdist w x y ≤ t * w s(x, y)) : IsWSpanner G H w t := by
  refine ⟨hHG, fun u v => ?_⟩
  have key : ∀ p : G.Walk u v, H.wdist w u v ≤ t * p.wlength w :=
    fun p => wdist_le_mul_wlength p fun a b hab _ => h a b hab
  change _ ≤ (t : ℝ≥0∞) * ⨅ p : G.Walk u v, p.wlength w
  have ht0 : (t : ℝ≥0∞) ≠ 0 := by
    have : (0 : ℝ≥0) < t := lt_of_lt_of_le one_pos ht
    exact_mod_cast this.ne'
  rw [ENNReal.mul_iInf_of_ne ht0 ENNReal.coe_ne_top]
  exact le_iInf key

lemma isWSpanner_refl {t : ℝ≥0} (ht : 1 ≤ t) : IsWSpanner G G w t :=
  ⟨le_rfl, fun u v => le_mul_of_one_le_left zero_le (by exact_mod_cast ht)⟩

/-! ### Weighted distances are attained -/

lemma wdist_eq_top_of_not_reachable {u v : V} (h : ¬ G.Reachable u v) : G.wdist w u v = ⊤ := by
  have : IsEmpty (G.Walk u v) := ⟨fun p => h ⟨p⟩⟩
  simp [wdist]

lemma reachable_of_wdist_lt_top {u v : V} (h : G.wdist w u v < ⊤) : G.Reachable u v := by
  by_contra hr
  rw [wdist_eq_top_of_not_reachable hr] at h
  exact lt_irrefl _ h

/-- The sum of a function over a duplicate-free sublist-by-membership is at most the sum. -/
lemma sum_map_le_of_subset {α : Type*} [DecidableEq α] (f : α → ℝ≥0∞) {l₁ l₂ : List α}
    (h₁ : l₁.Nodup) (h : l₁ ⊆ l₂) : (l₁.map f).sum ≤ (l₂.map f).sum := by
  rw [← List.sum_toFinset f h₁]
  calc ∑ x ∈ l₁.toFinset, f x ≤ ∑ x ∈ l₂.toFinset, f x :=
        Finset.sum_le_sum_of_subset (fun x hx => by
          rw [List.mem_toFinset] at hx ⊢; exact h hx)
    _ ≤ (l₂.map f).sum := by
        rw [Finset.sum_list_map_count]
        refine Finset.sum_le_sum fun x hx => ?_
        have : 1 ≤ l₂.count x := List.count_pos_iff.mpr (List.mem_toFinset.mp hx)
        calc f x = 1 • f x := (one_nsmul _).symm
          _ ≤ l₂.count x • f x := nsmul_le_nsmul_left zero_le this

lemma Walk.wlength_bypass_le [DecidableEq V] {u v : V} (p : G.Walk u v) :
    p.bypass.wlength w ≤ p.wlength w :=
  sum_map_le_of_subset _ ((p.bypass_isPath).isTrail.edges_nodup) (p.edges_bypass_subset_edges)

-- CSLib candidate
/-- On a finite graph the weighted distance between connected vertices is the weight of a path. -/
lemma exists_isPath_wlength_eq [Finite V] {u v : V} (h : G.Reachable u v) :
    ∃ p : G.Walk u v, p.IsPath ∧ p.wlength w = G.wdist w u v := by
  classical
  have := Fintype.ofFinite V
  set S : Set (G.Walk u v) := {p | p.IsPath ∧ p.length < Fintype.card V}
  have hfin : S.Finite := Set.toFinite S
  have hne : S.Nonempty := ⟨h.some.bypass, h.some.bypass_isPath, h.some.bypass_isPath.length_lt⟩
  obtain ⟨p, hpS, hpmin⟩ := Set.exists_min_image S (fun p => p.wlength w) hfin hne
  refine ⟨p, hpS.1, le_antisymm (le_iInf fun q => ?_) (wdist_le p)⟩
  exact (hpmin q.bypass ⟨q.bypass_isPath, q.bypass_isPath.length_lt⟩).trans
    (Walk.wlength_bypass_le q)

/-! ### Weight of a graph -/

-- CSLib candidate
/-- Total weight `w(H) = ∑_{e ∈ E(H)} w(e)`. -/
noncomputable def wt [Fintype V] (w : Sym2 V → ℝ≥0) (H : SimpleGraph V) : ℝ≥0∞ :=
  ∑ e : Sym2 V, H.edgeSet.indicator (fun e => (w e : ℝ≥0∞)) e

lemma wt_mono [Fintype V] {H₁ H₂ : SimpleGraph V} (h : H₁ ≤ H₂) : wt w H₁ ≤ wt w H₂ :=
  Finset.sum_le_sum fun e _ =>
    Set.indicator_le_indicator_of_subset (edgeSet_mono h) (fun _ => zero_le) e

lemma sum_indicator_union_singleton [Fintype V] (g : Sym2 V → ℝ≥0∞) {S : Set (Sym2 V)}
    {f : Sym2 V} (hf : f ∉ S) :
    ∑ e : Sym2 V, (S ∪ {f}).indicator g e = ∑ e : Sym2 V, S.indicator g e + g f := by
  classical
  rw [Set.indicator_union_of_disjoint (Set.disjoint_singleton_right.mpr hf)]
  rw [Finset.sum_add_distrib]
  congr 1
  simp [Set.indicator_apply]

/-! ### Edge orders and Algorithm 1 -/

/-- The symmetric version of `wdist`, as a function of an edge `e = {u, v}`. -/
noncomputable def _root_.SimpleGraph.wdistS (G : SimpleGraph V) (w : Sym2 V → ℝ≥0) (e : Sym2 V) : ℝ≥0∞ :=
  Sym2.lift ⟨fun u v => G.wdist w u v, fun _ _ => wdist_comm⟩ e

@[simp] lemma wdistS_mk (u v : V) : G.wdistS w s(u, v) = G.wdist w u v := rfl

/-- One step of Algorithm 1: add `e` to the current edge set `A` iff
`δ_A(e) > t · w(e)`. -/
noncomputable def greedyStep (w : Sym2 V → ℝ≥0) (t : ℝ≥0) (A : Set (Sym2 V)) (e : Sym2 V) :
    Set (Sym2 V) :=
  open Classical in
  if (t : ℝ≥0∞) * w e < (fromEdgeSet A).wdistS w e then insert e A else A

/-- The edges added by Algorithm 1 when it scans the list `L`. -/
noncomputable def greedySet (w : Sym2 V → ℝ≥0) (t : ℝ≥0) (L : List (Sym2 V)) : Set (Sym2 V) :=
  L.foldl (greedyStep w t) ∅

-- CSLib candidate
/-- **Algorithm 1** (`Greedy(G, t)`), run on the edge list `L`. -/
noncomputable def greedy (w : Sym2 V → ℝ≥0) (t : ℝ≥0) (L : List (Sym2 V)) : SimpleGraph V :=
  fromEdgeSet (greedySet w t L)

/-- `L` lists the edges of `G`, each exactly once, in non-decreasing order of weight. -/
def IsGreedyOrder (G : SimpleGraph V) (w : Sym2 V → ℝ≥0) (L : List (Sym2 V)) : Prop :=
  L.Nodup ∧ (∀ e, e ∈ L ↔ e ∈ G.edgeSet) ∧ L.Pairwise (fun a b => w a ≤ w b)

/-- `H` is (the output of an execution of) the greedy `t`-spanner of `(G, w)`. -/
def IsGreedySpanner (G : SimpleGraph V) (w : Sym2 V → ℝ≥0) (t : ℝ≥0) (H : SimpleGraph V) : Prop :=
  ∃ L, IsGreedyOrder G w L ∧ H = greedy w t L

lemma exists_isGreedyOrder [Finite V] (G : SimpleGraph V) (w : Sym2 V → ℝ≥0) :
    ∃ L, IsGreedyOrder G w L := by
  classical
  have := Fintype.ofFinite V
  let L := ((univ.filter fun e : Sym2 V => e ∈ G.edgeSet).toList).mergeSort
    fun a b => decide (w a ≤ w b)
  refine ⟨L, ?_, fun e => by simp [L, List.mem_mergeSort], ?_⟩
  · exact (List.mergeSort_perm _ _).nodup_iff.mpr (Finset.nodup_toList _)
  · have := List.pairwise_mergeSort (le := fun a b : Sym2 V => decide (w a ≤ w b))
      (fun a b c hab hbc => by simp only [decide_eq_true_eq] at *; exact hab.trans hbc)
      (fun a b => by simpa using le_total _ _)
      ((univ.filter fun e : Sym2 V => e ∈ G.edgeSet).toList)
    simpa using this

lemma exists_isGreedySpanner [Finite V] (G : SimpleGraph V) (w : Sym2 V → ℝ≥0) (t : ℝ≥0) :
    ∃ H, IsGreedySpanner G w t H :=
  let ⟨L, hL⟩ := exists_isGreedyOrder G w
  ⟨_, L, hL, rfl⟩

variable {t : ℝ≥0}

lemma subset_foldl_greedyStep : ∀ (L : List (Sym2 V)) (A : Set (Sym2 V)),
    A ⊆ L.foldl (greedyStep w t) A
  | [], _ => subset_rfl
  | e :: L, A => by
    rw [List.foldl_cons]
    refine subset_trans ?_ (subset_foldl_greedyStep L _)
    unfold greedyStep
    split_ifs
    · exact Set.subset_insert _ _
    · exact subset_rfl

lemma foldl_greedyStep_subset : ∀ (L : List (Sym2 V)) (A : Set (Sym2 V)),
    L.foldl (greedyStep w t) A ⊆ A ∪ {e | e ∈ L}
  | [], A => by simp
  | e :: L, A => by
    rw [List.foldl_cons]
    refine (foldl_greedyStep_subset L _).trans ?_
    intro x hx
    rcases hx with hx | hx
    · unfold greedyStep at hx
      split_ifs at hx
      · rcases hx with rfl | hx
        · exact Or.inr (List.mem_cons_self ..)
        · exact Or.inl hx
      · exact Or.inl hx
    · exact Or.inr (List.mem_cons_of_mem _ hx)

lemma greedySet_subset (L : List (Sym2 V)) : greedySet w t L ⊆ {e | e ∈ L} := by
  intro x hx
  rcases foldl_greedyStep_subset L ∅ hx with h | h
  · exact absurd h (Set.notMem_empty _)
  · exact h

lemma greedySet_append (L₁ L₂ : List (Sym2 V)) :
    greedySet w t (L₁ ++ L₂) = L₂.foldl (greedyStep w t) (greedySet w t L₁) := by
  simp [greedySet, List.foldl_append]

lemma greedySet_take_subset (L : List (Sym2 V)) (i : ℕ) :
    greedySet w t (L.take i) ⊆ greedySet w t L := by
  conv_rhs => rw [← List.take_append_drop i L]
  rw [greedySet_append]
  exact subset_foldl_greedyStep _ _

lemma greedySet_take_succ (L : List (Sym2 V)) {i : ℕ} (hi : i < L.length) :
    greedySet w t (L.take (i + 1)) = greedyStep w t (greedySet w t (L.take i)) L[i] := by
  rw [List.take_succ_eq_append_getElem hi, greedySet_append]
  rfl

/-- With a duplicate-free list, the edges added while scanning the prefix `L.take i` are exactly the
added edges lying in that prefix. -/
lemma greedySet_take_eq {L : List (Sym2 V)} (hL : L.Nodup) (i : ℕ) :
    greedySet w t (L.take i) = greedySet w t L ∩ {e | e ∈ L.take i} := by
  apply subset_antisymm
  · exact Set.subset_inter (greedySet_take_subset L i) (greedySet_subset _)
  · rintro x ⟨hx, hxi⟩
    have hnd : (L.take i ++ L.drop i).Nodup := by rwa [List.take_append_drop]
    rw [← List.take_append_drop i L, greedySet_append] at hx
    rcases foldl_greedyStep_subset _ _ hx with h | h
    · exact h
    · exact absurd h (List.disjoint_of_nodup_append hnd hxi)

/-- An edge added by the scan was accepted at its position. -/
lemma accepted_of_mem_greedySet [DecidableEq V] {L : List (Sym2 V)} (hL : L.Nodup) {e : Sym2 V}
    (he : e ∈ greedySet w t L) :
    (t : ℝ≥0∞) * w e < (fromEdgeSet (greedySet w t (L.take (L.idxOf e)))).wdistS w e := by
  have heL : e ∈ L := greedySet_subset L he
  set i := L.idxOf e
  have hi : i < L.length := List.idxOf_lt_length_of_mem heL
  have hLi : L[i] = e := List.getElem_idxOf hi
  have h1 : e ∈ greedySet w t (L.take (i + 1)) := by
    rw [greedySet_take_eq hL]
    exact ⟨he, (List.mem_take_iff_idxOf_lt heL).mpr (Nat.lt_succ_self _)⟩
  have h2 : e ∉ greedySet w t (L.take i) := by
    intro h
    exact (lt_irrefl i) ((List.mem_take_iff_idxOf_lt heL).mp (greedySet_subset _ h))
  rw [greedySet_take_succ L hi, hLi] at h1
  unfold greedyStep at h1
  split_ifs at h1 with hacc
  · exact hacc
  · exact absurd h1 h2

/-- **Key property of an added edge.** If `{u, v}` was added, then every walk between `u` and `v`
all of whose edges were added *before* `{u, v}` weighs more than `t · w(uv)`. -/
lemma lt_wlength_of_mem_greedySet [DecidableEq V] {L : List (Sym2 V)} (hL : L.Nodup) {u v : V}
    (he : s(u, v) ∈ greedySet w t L) {G' : SimpleGraph V} (p : G'.Walk u v)
    (hp : ∀ f ∈ p.edges, f ∈ greedySet w t L ∧ L.idxOf f < L.idxOf s(u, v)) :
    (t : ℝ≥0∞) * w s(u, v) < p.wlength w := by
  have hacc := accepted_of_mem_greedySet hL he
  rw [wdistS_mk] at hacc
  have hsub : ∀ f ∈ p.edges, f ∈ (fromEdgeSet (greedySet w t (L.take (L.idxOf s(u, v))))).edgeSet := by
    intro f hf
    obtain ⟨hfA, hfi⟩ := hp f hf
    rw [edgeSet_fromEdgeSet, greedySet_take_eq hL]
    refine ⟨⟨hfA, (List.mem_take_iff_idxOf_lt (greedySet_subset L hfA)).mpr hfi⟩, ?_⟩
    exact G'.not_isDiag_of_mem_edgeSet (p.edges_subset_edgeSet hf)
  calc (t : ℝ≥0∞) * w s(u, v) < _ := hacc
    _ ≤ (p.transfer _ hsub).wlength w := wdist_le _
    _ = p.wlength w := Walk.wlength_transfer w p hsub

/-- **Key property of a rejected edge.** If `L[i] = {u, v}` was not added, then `u` and `v` are
joined by a walk of edges added before position `i`, of total weight at most `t · w(uv)`. -/
lemma exists_walk_of_not_mem_greedySet [Finite V] {L : List (Sym2 V)} {i : ℕ} (hi : i < L.length)
    {u v : V} (hLi : L[i] = s(u, v)) (hrej : s(u, v) ∉ greedySet w t L) :
    ∃ p : (fromEdgeSet (greedySet w t (L.take i))).Walk u v,
      p.wlength w ≤ t * w s(u, v) := by
  have hrej' : ¬ ((t : ℝ≥0∞) * w s(u, v) <
      (fromEdgeSet (greedySet w t (L.take i))).wdistS w s(u, v)) := by
    intro hacc
    apply hrej
    apply greedySet_take_subset L (i + 1)
    rw [greedySet_take_succ L hi, hLi]
    unfold greedyStep
    rw [wdistS_mk] at hacc
    simp [hacc]
  rw [not_lt, wdistS_mk] at hrej'
  have hlt : (fromEdgeSet (greedySet w t (L.take i))).wdist w u v < ⊤ :=
    hrej'.trans_lt (ENNReal.mul_lt_top ENNReal.coe_lt_top ENNReal.coe_lt_top)
  obtain ⟨p, -, hp⟩ := exists_isPath_wlength_eq (w := w) (reachable_of_wdist_lt_top hlt)
  exact ⟨p, hp ▸ hrej'⟩

lemma mem_greedySet_of_mem_edgeSet {L : List (Sym2 V)} {f : Sym2 V}
    (hf : f ∈ (greedy w t L).edgeSet) : f ∈ greedySet w t L := by
  rw [greedy, edgeSet_fromEdgeSet] at hf
  exact hf.1

/-- In a sorted order, an edge listed earlier is not heavier. -/
lemma weight_le_of_idxOf_lt [DecidableEq V] {L : List (Sym2 V)}
    (hsort : L.Pairwise (fun a b => w a ≤ w b)) {a b : Sym2 V} (ha : a ∈ L) (hb : b ∈ L)
    (h : L.idxOf a < L.idxOf b) : w a ≤ w b := by
  have hia := List.idxOf_lt_length_of_mem ha
  have hib := List.idxOf_lt_length_of_mem hb
  have := List.pairwise_iff_getElem.mp hsort _ _ hia hib h
  rwa [List.getElem_idxOf hia, List.getElem_idxOf hib] at this

/-! ### The greedy output is a `t`-spanner -/

lemma greedy_le {L : List (Sym2 V)} (hL : ∀ e, e ∈ L ↔ e ∈ G.edgeSet) : greedy w t L ≤ G := by
  intro u v huv
  rw [greedy, fromEdgeSet_adj] at huv
  exact (hL _).mp (greedySet_subset L huv.1)

lemma greedy_wdist_le_of_mem [Finite V] {L : List (Sym2 V)} (ht : 1 ≤ t) {u v : V}
    (huvL : s(u, v) ∈ L) : (greedy w t L).wdist w u v ≤ t * w s(u, v) := by
  by_cases hmem : s(u, v) ∈ greedySet w t L
  · by_cases huv : u = v
    · subst huv
      exact (wdist_le (Walk.nil : (greedy w t L).Walk u u)).trans (by simp)
    · calc (greedy w t L).wdist w u v ≤ w s(u, v) :=
            wdist_le_of_adj ((fromEdgeSet_adj _).mpr ⟨hmem, huv⟩)
        _ ≤ t * w s(u, v) := le_mul_of_one_le_left zero_le (by exact_mod_cast ht)
  · classical
    have hi : L.idxOf s(u, v) < L.length := List.idxOf_lt_length_of_mem huvL
    obtain ⟨p, hp⟩ := exists_walk_of_not_mem_greedySet hi (List.getElem_idxOf hi) hmem
    have hle : fromEdgeSet (greedySet w t (L.take (L.idxOf s(u, v)))) ≤ greedy w t L :=
      fromEdgeSet_mono (greedySet_take_subset L _)
    calc (greedy w t L).wdist w u v ≤ (p.mapLe hle).wlength w := wdist_le _
      _ = p.wlength w := Walk.wlength_mapLe w hle p
      _ ≤ t * w s(u, v) := hp

/-- The greedy `t`-spanner is a `t`-spanner (the paper: "It is immediate that `H` has stretch at
most `t`"). -/
theorem IsGreedySpanner.isWSpanner [Finite V] (ht : 1 ≤ t) (hH : IsGreedySpanner G w t H) :
    IsWSpanner G H w t := by
  obtain ⟨L, ⟨-, hLG, -⟩, rfl⟩ := hH
  exact isWSpanner_of_adj ht (greedy_le hLG) fun x y hxy => greedy_wdist_le_of_mem ht ((hLG _).mpr hxy)

end GreedySpanner
