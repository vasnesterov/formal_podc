import Papers.PODC2016.GreedySpanner.Basic

/-!
# Minimum spanning trees and Observation 2

We do not need a separate MST algorithm: the weight of a minimum spanning tree (forest) is
`mstWeight G w`, the minimum weight of a subgraph `T ≤ G` with the same connected components as
`G` (`IsSpanningSub G T`). For connected `G` this is the minimum over connected spanning subgraphs,
which is the MST weight (an optimal subgraph can be chosen acyclic since weights are `≥ 0`; see
`exists_isAcyclic_isSpanningSub` in `MSTTree.lean`).

* `mstWeight_eq_of_forall_walk` — **exchange lemma**: if `H ≤ G` and every edge `uv` of `G` missing
  from `H` is bypassed in `H` by a walk of edges of weight `≤ w(uv)`, then `G` and `H` have the same
  MST weight (and the minimum for `G` is attained inside `H`).
* `IsGreedySpanner.mstWeight_eq` — **Observation 2**: the greedy spanner `H` contains an MST of `G`,
  hence `w(MST(H)) = w(MST(G))` (from the shared `SimpleGraph.IsGreedySpanner.forall_walk`).
-/

open Finset SimpleGraph
open scoped ENNReal NNReal

namespace GreedySpanner

variable {V : Type*} {G H T : SimpleGraph V} {w : Sym2 V → ℝ≥0}

/-- `T` is a spanning subgraph of `G` with the same connected components. -/
def IsSpanningSub (G T : SimpleGraph V) : Prop :=
  T ≤ G ∧ ∀ u v, G.Reachable u v → T.Reachable u v

-- CSLib candidate
/-- Weight of a minimum spanning tree (forest, if `G` is disconnected) of `(G, w)`. -/
noncomputable def mstWeight [Fintype V] (G : SimpleGraph V) (w : Sym2 V → ℝ≥0) : ℝ≥0∞ :=
  ⨅ (T : SimpleGraph V) (_ : IsSpanningSub G T), wt w T

lemma isSpanningSub_refl : IsSpanningSub G G := ⟨le_rfl, fun _ _ h => h⟩

lemma mstWeight_le_wt [Fintype V] (hT : IsSpanningSub G T) : mstWeight G w ≤ wt w T :=
  iInf₂_le T hT

lemma mstWeight_le_wt_self [Fintype V] : mstWeight G w ≤ wt w G :=
  mstWeight_le_wt isSpanningSub_refl

/-- The minimum is attained. -/
lemma exists_wt_eq_mstWeight [Fintype V] (G : SimpleGraph V) (w : Sym2 V → ℝ≥0) :
    ∃ T, IsSpanningSub G T ∧ wt w T = mstWeight G w := by
  obtain ⟨T, hT, hmin⟩ := Set.exists_min_image {T | IsSpanningSub G T} (wt w) (Set.toFinite _)
    ⟨G, isSpanningSub_refl⟩
  exact ⟨T, hT, le_antisymm (le_iInf₂ fun T' hT' => hmin T' hT') (mstWeight_le_wt hT)⟩

/-- Reachability is inherited if every edge of `T` joins `T'`-reachable vertices. -/
lemma reachable_of_forall_adj {T T' : SimpleGraph V} (h : ∀ x y, T.Adj x y → T'.Reachable x y)
    {u v : V} (huv : T.Reachable u v) : T'.Reachable u v := by
  obtain ⟨p⟩ := huv
  induction p with
  | nil => rfl
  | cons hadj q ih => exact (h _ _ hadj).trans ih

/-- After deleting the edge `uv`, every vertex reachable from `a` is reachable from `a`, `u` or
`v`. -/
lemma reachable_deleteEdges_cases {u v a b : V} (p : T.Walk a b) :
    (T.deleteEdges {s(u, v)}).Reachable a b ∨ (T.deleteEdges {s(u, v)}).Reachable u b ∨
      (T.deleteEdges {s(u, v)}).Reachable v b := by
  induction p with
  | nil => exact Or.inl (Reachable.refl _)
  | @cons a a' b hadj q ih =>
    by_cases hev : s(a, a') = s(u, v)
    · rcases ih with h | h | h
      · rcases Sym2.eq_iff.mp hev with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact Or.inr (Or.inr h)
        · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
    · have hadj' : (T.deleteEdges {s(u, v)}).Adj a a' := by
        rw [deleteEdges_adj]
        exact ⟨hadj, by simpa using hev⟩
      rcases ih with h | h | h
      · exact Or.inl (hadj'.reachable.trans h)
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)

lemma wt_union_singleton [Fintype V] {T T₀ : SimpleGraph V} {f : Sym2 V}
    (hT : T.edgeSet = T₀.edgeSet ∪ {f}) (hf : f ∉ T₀.edgeSet) : wt w T = wt w T₀ + w f := by
  unfold wt
  rw [hT, sum_indicator_union_singleton _ hf]

/-- The exchange step, by strong induction on the number of edges of `T` outside `H`. -/
lemma exchange_aux [Fintype V] (hHG : H ≤ G)
    (h : ∀ u v, G.Adj u v → ¬ H.Adj u v → ∃ p : H.Walk u v, ∀ f ∈ p.edges, w f ≤ w s(u, v)) :
    ∀ n T, IsSpanningSub G T → (T.edgeSet \ H.edgeSet).ncard = n →
      ∃ T', IsSpanningSub G T' ∧ T' ≤ H ∧ wt w T' ≤ wt w T := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro T hT hn
  by_cases hsub : T.edgeSet ⊆ H.edgeSet
  · exact ⟨T, hT, edgeSet_subset_edgeSet.mp hsub, le_rfl⟩
  obtain ⟨e, heT, heH⟩ := Set.not_subset.mp hsub
  induction e using Sym2.ind with
  | _ u v =>
  have hadj : T.Adj u v := heT
  have hnH : ¬ H.Adj u v := heH
  set T₀ := T.deleteEdges {s(u, v)} with hT₀
  have hT₀e : T₀.edgeSet = T.edgeSet \ {s(u, v)} := edgeSet_deleteEdges _
  have hT₀T : T₀ ≤ T := deleteEdges_le _
  have huvT₀ : s(u, v) ∉ T₀.edgeSet := by rw [hT₀e]; simp
  -- it suffices to find a better `T₁` with fewer edges outside `H`
  suffices ∃ T₁, IsSpanningSub G T₁ ∧ T₁.edgeSet \ H.edgeSet ⊂ T.edgeSet \ H.edgeSet ∧
      wt w T₁ ≤ wt w T by
    obtain ⟨T₁, hT₁, hss, hw⟩ := this
    have hlt : (T₁.edgeSet \ H.edgeSet).ncard < n := hn ▸ Set.ncard_lt_ncard hss (Set.toFinite _)
    obtain ⟨T', hT', hT'H, hw'⟩ := ih _ hlt T₁ hT₁ rfl
    exact ⟨T', hT', hT'H, hw'.trans hw⟩
  by_cases hreach : T₀.Reachable u v
  · -- `uv` lies on a cycle of `T`: drop it
    refine ⟨T₀, ⟨hT₀T.trans hT.1, fun a b hab => reachable_of_forall_adj ?_ (hT.2 a b hab)⟩,
      ?_, wt_mono hT₀T⟩
    · intro x y hxy
      by_cases hxy' : s(x, y) = s(u, v)
      · rcases Sym2.eq_iff.mp hxy' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact hreach
        · exact hreach.symm
      · exact (deleteEdges_adj.mpr ⟨hxy, by simpa using hxy'⟩).reachable
    · rw [hT₀e]
      refine Set.ssubset_iff_of_subset (Set.sdiff_subset_sdiff_left Set.sdiff_subset) |>.mpr
        ⟨s(u, v), ⟨heT, heH⟩, fun h => ?_⟩
      simp at h
  · -- `uv` is a bridge of `T`: exchange it for an edge of the bypassing walk in `H`
    obtain ⟨p, hp⟩ := h u v (hT.1 hadj) hnH
    obtain ⟨x, y, hxy, p₁, p₂, hpeq, hx, hy⟩ :=
      p.exists_dart_of_pred (T₀.Reachable u ·) (Reachable.refl u) hreach
    have hxyne : x ≠ y := hxy.ne
    have hfT₀ : s(x, y) ∉ T₀.edgeSet := fun hf => hy (hx.trans (Adj.reachable hf))
    have hfH : s(x, y) ∈ H.edgeSet := hxy
    have hfp : s(x, y) ∈ p.edges := by rw [hpeq]; simp [Walk.edges_append]
    have hGuy : G.Reachable u y :=
      (hT.1 hadj).reachable.trans (p₂.mapLe hHG).reachable.symm
    have hT₀vy : T₀.Reachable v y := by
      rcases reachable_deleteEdges_cases (u := u) (v := v) (hT.2 u y hGuy).some with h' | h' | h'
      · exact absurd h' hy
      · exact absurd h' hy
      · exact h'
    set T₁ := T₀ ⊔ edge x y with hT₁
    have hT₁e : T₁.edgeSet = T₀.edgeSet ∪ {s(x, y)} := by
      rw [hT₁, edgeSet_sup, edgeSet_edge_of_ne hxyne]
    have hT₁uv : T₁.Reachable u v := by
      have hxy1 : T₁.Adj x y := Or.inr ((edge_adj _ _ _ _).mpr ⟨Or.inl ⟨rfl, rfl⟩, hxyne⟩)
      exact (hx.mono le_sup_left).trans (hxy1.reachable.trans (hT₀vy.symm.mono le_sup_left))
    refine ⟨T₁, ⟨sup_le (hT₀T.trans hT.1) ((edge_le_iff G).mpr (Or.inr (hHG hxy))),
      fun a b hab => reachable_of_forall_adj ?_ (hT.2 a b hab)⟩, ?_, ?_⟩
    · intro a b hab
      by_cases hab' : s(a, b) = s(u, v)
      · rcases Sym2.eq_iff.mp hab' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact hT₁uv
        · exact hT₁uv.symm
      · exact (Adj.reachable (Or.inl (deleteEdges_adj.mpr ⟨hab, by simpa using hab'⟩) :
          T₁.Adj a b))
    · rw [hT₁e, hT₀e]
      refine (Set.ssubset_iff_of_subset ?_).mpr ⟨s(u, v), ⟨heT, heH⟩, fun h => ?_⟩
      · rintro f ⟨hf1 | hf1, hf2⟩
        · exact ⟨hf1.1, hf2⟩
        · exact absurd (Set.mem_singleton_iff.mp hf1 ▸ hfH) hf2
      · rcases h with ⟨h1 | h1, -⟩
        · simp at h1
        · exact heH (Set.mem_singleton_iff.mp h1 ▸ hfH)
    · have hTe : T.edgeSet = T₀.edgeSet ∪ {s(u, v)} := by
        rw [hT₀e, Set.sdiff_union_of_subset (Set.singleton_subset_iff.mpr heT)]
      rw [wt_union_singleton hT₁e hfT₀, wt_union_singleton hTe huvT₀]
      gcongr
      exact_mod_cast hp _ hfp

/-- Reachability under the hypothesis of the exchange lemma. -/
lemma reachable_of_forall_walk
    (h : ∀ u v, G.Adj u v → ¬ H.Adj u v → ∃ p : H.Walk u v, ∀ f ∈ p.edges, w f ≤ w s(u, v))
    {a b : V} (hab : G.Reachable a b) : H.Reachable a b := by
  refine reachable_of_forall_adj (fun x y hxy => ?_) hab
  by_cases hH : H.Adj x y
  · exact hH.reachable
  · exact (h x y hxy hH).choose.reachable

-- CSLib candidate
/-- **Exchange lemma.** If every edge `uv` of `G` missing from `H ≤ G` is bypassed in `H` by a walk
of edges of weight `≤ w(uv)`, then `H` contains a minimum spanning tree (forest) of `G`, so
`w(MST(H)) = w(MST(G))`. -/
theorem mstWeight_eq_of_forall_walk [Fintype V] (hHG : H ≤ G)
    (h : ∀ u v, G.Adj u v → ¬ H.Adj u v → ∃ p : H.Walk u v, ∀ f ∈ p.edges, w f ≤ w s(u, v)) :
    mstWeight H w = mstWeight G w := by
  refine le_antisymm (le_iInf₂ fun T hT => ?_) (le_iInf₂ fun T hT => ?_)
  · obtain ⟨T', hT', hT'H, hw⟩ := exchange_aux hHG h _ T hT rfl
    exact (mstWeight_le_wt ⟨hT'H, fun a b hab => hT'.2 a b (hab.mono hHG)⟩).trans hw
  · exact mstWeight_le_wt ⟨hT.1.trans hHG, fun a b hab => hT.2 a b (reachable_of_forall_walk h hab)⟩

/-- **Observation 2.** The greedy `t`-spanner `H` of `G` contains an MST of `G`; hence
`w(MST(H)) = w(MST(G))`. -/
theorem IsGreedySpanner.mstWeight_eq [Fintype V] {t : ℝ≥0} (hH : IsGreedySpanner G w t H) :
    mstWeight H w = mstWeight G w :=
  mstWeight_eq_of_forall_walk hH.forall_walk.1 hH.forall_walk.2

/-- Observation 2 in the paper's form: `H` contains a minimum spanning tree (forest) `Z` of `G`. -/
theorem IsGreedySpanner.exists_mst_le [Fintype V] {t : ℝ≥0} (hH : IsGreedySpanner G w t H) :
    ∃ Z ≤ H, IsSpanningSub G Z ∧ wt w Z = mstWeight G w := by
  obtain ⟨Z, hZ, hZw⟩ := exists_wt_eq_mstWeight H w
  exact ⟨Z, hZ.1, ⟨hZ.1.trans hH.forall_walk.1,
    fun a b hab => hZ.2 a b (reachable_of_forall_walk hH.forall_walk.2 hab)⟩,
    hZw.trans (IsGreedySpanner.mstWeight_eq hH)⟩

end GreedySpanner
