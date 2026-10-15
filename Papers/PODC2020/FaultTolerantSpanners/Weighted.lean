import Papers.PODC2020.FaultTolerantSpanners.Size
import Cslib.Foundations.Combinatorics.SimpleGraph.WeightedSpanner
import Mathlib

/-!
# Weighted graphs: Algorithm 4 and Theorem 10 (Section 4 of Dinitz–Robelle, PODC'20)

**Algorithm 4** is Algorithm 3 run on the edges in nondecreasing weight order, with Algorithm 2 run
on the current graph *ignoring the weights*. We model it as `modifiedGreedy O k f L` together with
the hypothesis `L.Pairwise (w · ≤ w ·)` (the list is sorted by weight).

**Theorem 10**: the output is an `f`-VFT `(2k - 1)`-spanner of the weighted graph `(G, w)`
(`modifiedGreedy_isWeightedVFTSpanner`), and has at most `32 k f^{1-1/k} n^{1+1/k}` edges
(`modifiedGreedyWeighted_card_edges_le`, immediate from Theorem 8 which holds for every order).
The edge-fault version is `modifiedGreedyEdge_isWeightedEFTSpanner`.
-/

open Finset SimpleGraph
open scoped ENNReal NNReal

namespace FaultTolerantSpanners

variable {V : Type*} {dec : SimpleGraph V → V → V → Bool}

/-- Every edge of the graph built before scanning position `i` comes from an entry `L[j]`, `j < i`;
so if `L` is sorted by weight, it is no heavier than `L[i]`. -/
lemma weight_le_of_mem_edgeGraph_take {w : Sym2 V → ℝ≥0} {L : List (V × V)}
    (hsort : L.Pairwise fun a b => w s(a.1, a.2) ≤ w s(b.1, b.2)) {i : ℕ} (hi : i < L.length)
    {e : Sym2 V} (he : e ∈ (edgeGraph (greedyList dec (L.take i))).edgeSet) :
    w e ≤ w s(L[i].1, L[i].2) := by
  rw [mem_edgeSet_edgeGraph] at he
  obtain ⟨⟨r, hr, rfl⟩, -⟩ := he
  have hr' := mem_of_mem_greedyList hr
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hr'
  rw [List.length_take] at hj
  rw [List.getElem_take]
  exact List.pairwise_iff_getElem.mp hsort j i (by omega) hi (by omega)

/-- A walk in the graph built before position `i`, avoiding `F`, of length `≤ t`, witnesses
`d_{H \ F}(L[i]) ≤ t · w(L[i])` in the final graph. -/
lemma wdist_le_of_reject {w : Sym2 V → ℝ≥0} {L : List (V × V)}
    (hsort : L.Pairwise fun a b => w s(a.1, a.2) ≤ w s(b.1, b.2)) {i : ℕ} (hi : i < L.length)
    {t : ℕ} (G' H' : SimpleGraph V) (hG' : G' ≤ edgeGraph (greedyList dec (L.take i)))
    (hH' : G' ≤ H') (hdist : G'.edist L[i].1 L[i].2 ≤ t) :
    H'.wdist w L[i].1 L[i].2 ≤ t * w s(L[i].1, L[i].2) := by
  obtain ⟨q, hq⟩ := edist_le_coe_iff.mp hdist
  calc H'.wdist w L[i].1 L[i].2 ≤ (q.mapLe hH').wlength w := wdist_le _
    _ = q.wlength w := Walk.wlength_mapLe _ _ _
    _ ≤ q.length * w s(L[i].1, L[i].2) := q.wlength_le_length_mul w fun e he => by
        exact_mod_cast weight_le_of_mem_edgeGraph_take hsort hi
          (edgeSet_mono hG' (q.edges_subset_edgeSet he))
    _ ≤ t * w s(L[i].1, L[i].2) := by gcongr

variable [DecidableEq V] [Fintype V]

/-- **Theorem 10 of Dinitz–Robelle (correctness).** If the edges are scanned in nondecreasing weight
order, Algorithm 3 (which ignores weights inside Algorithm 2) returns an `f`-VFT `(2k-1)`-spanner of
the weighted graph `(G, w)`. -/
theorem modifiedGreedy_isWeightedVFTSpanner {O : ShortPathOracle V} (hO : O.Spec)
    {G : SimpleGraph V} {w : Sym2 V → ℝ≥0} {L : List (V × V)} {k f : ℕ} (hk : 1 ≤ k)
    (hLG : ∀ p ∈ L, G.Adj p.1 p.2) (hL : ∀ u v, G.Adj u v → (u, v) ∈ L ∨ (v, u) ∈ L)
    (hsort : L.Pairwise fun a b => w s(a.1, a.2) ≤ w s(b.1, b.2)) :
    IsWeightedVFTSpanner G (modifiedGreedy O k f L) w f (2 * k - 1) := by
  set H := modifiedGreedy O k f L
  have ht : 1 ≤ 2 * k - 1 := by omega
  refine isWeightedVFTSpanner_of_adj ht (greedy_le hLG) fun F hF u v huv hu hv => ?_
  have key : ∀ p ∈ L, p.1 ∉ F → p.2 ∉ F →
      (H.deleteVerts F).wdist w p.1 p.2 ≤ (2 * k - 1 : ℕ) * w s(p.1, p.2) := by
    intro p hp h1 h2
    rcases greedy_mem_or_reject L hp with hmem | ⟨i, hi, hLi, hrej⟩
    · have hadj : (H.deleteVerts F).Adj p.1 p.2 :=
        ⟨edgeGraph_adj_of_mem hmem (hLG p hp).ne, h1, h2⟩
      refine (wdist_le_of_adj hadj).trans ?_
      exact le_mul_of_one_le_left zero_le (by exact_mod_cast ht)
    · have hLi' : L[i] = p := by simpa [hi] using hLi
      subst hLi'
      -- Algorithm 2 said NO, so `F` is not a cut: a short path survives in `H_i \ F`
      have hcut : ((edgeGraph (greedyList (fun H u v => lbc O H u v (2 * k - 1) f)
          (L.take i))).deleteVerts F).edist L[i].1 L[i].2 ≤ (2 * k - 1 : ℕ) := by
        by_contra hlt
        rw [not_le] at hlt
        have := lbc_eq_true_of_isLengthCut hO ⟨h1, h2, hlt⟩ hF
        simp [this] at hrej
      exact wdist_le_of_reject hsort hi _ _ (deleteVerts_le _ _)
        (deleteVerts_mono (edgeGraph_take_le_greedy L i)) hcut
  rcases hL u v huv with h | h
  · exact key _ h hu hv
  · rw [wdist_comm, Sym2.eq_swap]; exact key _ h hv hu

/-- **Theorem 10, edge-fault version.** -/
theorem modifiedGreedyEdge_isWeightedEFTSpanner {O : ShortPathOracle V} (hO : O.Spec)
    {G : SimpleGraph V} {w : Sym2 V → ℝ≥0} {L : List (V × V)} {k f : ℕ} (hk : 1 ≤ k)
    (hLG : ∀ p ∈ L, G.Adj p.1 p.2) (hL : ∀ u v, G.Adj u v → (u, v) ∈ L ∨ (v, u) ∈ L)
    (hsort : L.Pairwise fun a b => w s(a.1, a.2) ≤ w s(b.1, b.2)) :
    IsWeightedEFTSpanner G (modifiedGreedyEdge O k f L) w f (2 * k - 1) := by
  set H := modifiedGreedyEdge O k f L
  have ht : 1 ≤ 2 * k - 1 := by omega
  refine isWeightedEFTSpanner_of_adj ht (greedy_le hLG) fun F hF u v huv huvF => ?_
  have key : ∀ p ∈ L, s(p.1, p.2) ∉ F →
      (H.deleteEdges F).wdist w p.1 p.2 ≤ (2 * k - 1 : ℕ) * w s(p.1, p.2) := by
    intro p hp hpF
    rcases greedy_mem_or_reject L hp with hmem | ⟨i, hi, hLi, hrej⟩
    · have hadj : (H.deleteEdges F).Adj p.1 p.2 := by
        rw [deleteEdges_adj]
        exact ⟨edgeGraph_adj_of_mem hmem (hLG p hp).ne, by simpa using hpF⟩
      refine (wdist_le_of_adj hadj).trans ?_
      exact le_mul_of_one_le_left zero_le (by exact_mod_cast ht)
    · have hLi' : L[i] = p := by simpa [hi] using hLi
      subst hLi'
      have hcut : ((edgeGraph (greedyList (fun H u v => lbcEdge O H u v (2 * k - 1) f)
          (L.take i))).deleteEdges F).edist L[i].1 L[i].2 ≤ (2 * k - 1 : ℕ) := by
        by_contra hlt
        rw [not_le] at hlt
        have := (lbcEdge_correct hO _ L[i].1 L[i].2 (2 * k - 1) f).1 ⟨F, hlt, hF⟩
        simp [this] at hrej
      exact wdist_le_of_reject hsort hi _ _ (SimpleGraph.deleteEdges_le _)
        (deleteEdges_mono (edgeGraph_take_le_greedy L i)) hcut
  rcases hL u v huv with h | h
  · exact key _ h huvF
  · rw [wdist_comm, Sym2.eq_swap]; exact key _ h (by rwa [Sym2.eq_swap])

/-- **Theorem 10 of Dinitz–Robelle (size).** The weighted algorithm is Algorithm 3 for a particular
order, so Theorem 8 applies verbatim. -/
theorem modifiedGreedyWeighted_card_edges_le {O : ShortPathOracle V} (hO : O.Spec)
    {w : Sym2 V → ℝ≥0} (L : List (V × V)) {k f : ℕ} (hk : 1 ≤ k) (hf : 1 ≤ f)
    (_hsort : L.Pairwise fun a b => w s(a.1, a.2) ≤ w s(b.1, b.2)) :
    ((modifiedGreedy O k f L).edgeSet.ncard : ℝ) ≤
      32 * k * (f : ℝ) ^ (1 - 1 / (k : ℝ)) * (Fintype.card V : ℝ) ^ (1 + 1 / (k : ℝ)) :=
  modifiedGreedy_card_edges_le hO L hk hf

end FaultTolerantSpanners
