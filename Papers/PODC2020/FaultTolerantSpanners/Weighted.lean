import Papers.PODC2020.FaultTolerantSpanners.Size
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
    {e : Sym2 V} (he : e ∈ (edgeGraph (greedyEdges dec (L.take i))).edgeSet) :
    w e ≤ w s(L[i].1, L[i].2) := by
  rw [mem_edgeSet_edgeGraph] at he
  obtain ⟨⟨r, hr, rfl⟩, -⟩ := he
  have hr' := mem_of_mem_greedyEdges hr
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hr'
  rw [List.length_take] at hj
  rw [List.getElem_take]
  exact List.pairwise_iff_getElem.mp hsort j i (by omega) hi (by omega)

/-- A walk of length `≤ t` in a subgraph `G'` of the graph built before position `i` witnesses
`d_{G'}(L[i]) ≤ t · w(L[i])`. -/
lemma wdist_le_of_reject {w : Sym2 V → ℝ≥0} {L : List (V × V)}
    (hsort : L.Pairwise fun a b => w s(a.1, a.2) ≤ w s(b.1, b.2)) {i : ℕ} (hi : i < L.length)
    {t : ℕ} {G' : SimpleGraph V} (hG' : G' ≤ edgeGraph (greedyEdges dec (L.take i)))
    (hdist : G'.edist L[i].1 L[i].2 ≤ t) :
    G'.wdist w L[i].1 L[i].2 ≤ t * w s(L[i].1, L[i].2) := by
  obtain ⟨q, hq⟩ := edist_le_coe_iff.mp hdist
  calc G'.wdist w L[i].1 L[i].2 ≤ q.wlength w := wdist_le _
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
  refine greedyGraph_isWeightedVFTSpanner (by omega) (fun i hi hrej F hF h1 h2 => ?_) hLG hL
  -- Algorithm 2 said NO, so `F` is not a cut: a short path survives in `H_i \ F`
  have hcut : ((edgeGraph (greedyEdges (fun H u v => lbc O H u v (2 * k - 1) f)
      (L.take i))).deleteVerts F).edist L[i].1 L[i].2 ≤ (2 * k - 1 : ℕ) := by
    by_contra hlt
    rw [not_le] at hlt
    have := lbc_eq_true_of_isLengthCut hO ⟨h1, h2, hlt⟩ hF
    simp [this] at hrej
  exact wdist_le_of_reject hsort hi (deleteVerts_le _ _) hcut

/-- **Theorem 10, edge-fault version.** -/
theorem modifiedGreedyEdge_isWeightedEFTSpanner {O : ShortPathOracle V} (hO : O.Spec)
    {G : SimpleGraph V} {w : Sym2 V → ℝ≥0} {L : List (V × V)} {k f : ℕ} (hk : 1 ≤ k)
    (hLG : ∀ p ∈ L, G.Adj p.1 p.2) (hL : ∀ u v, G.Adj u v → (u, v) ∈ L ∨ (v, u) ∈ L)
    (hsort : L.Pairwise fun a b => w s(a.1, a.2) ≤ w s(b.1, b.2)) :
    IsWeightedEFTSpanner G (modifiedGreedyEdge O k f L) w f (2 * k - 1) := by
  refine greedyGraph_isWeightedEFTSpanner (by omega) (fun i hi hrej F hF hiF => ?_) hLG hL
  have hcut : ((edgeGraph (greedyEdges (fun H u v => lbcEdge O H u v (2 * k - 1) f)
      (L.take i))).deleteEdges F).edist L[i].1 L[i].2 ≤ (2 * k - 1 : ℕ) := by
    by_contra hlt
    rw [not_le] at hlt
    have := (lbcEdge_correct hO _ L[i].1 L[i].2 (2 * k - 1) f).1 ⟨F, hlt, hF⟩
    simp [this] at hrej
  exact wdist_le_of_reject hsort hi (deleteEdges_le _) hcut

/-- **Theorem 10 of Dinitz–Robelle (size).** The weighted algorithm is Algorithm 3 for a particular
order, so Theorem 8 applies verbatim. -/
theorem modifiedGreedyWeighted_card_edges_le {O : ShortPathOracle V} (hO : O.Spec)
    {w : Sym2 V → ℝ≥0} (L : List (V × V)) {k f : ℕ} (hk : 1 ≤ k) (hf : 1 ≤ f)
    (_hsort : L.Pairwise fun a b => w s(a.1, a.2) ≤ w s(b.1, b.2)) :
    ((modifiedGreedy O k f L).edgeSet.ncard : ℝ) ≤
      32 * k * (f : ℝ) ^ (1 - 1 / (k : ℝ)) * (Fintype.card V : ℝ) ^ (1 + 1 / (k : ℝ)) :=
  modifiedGreedy_card_edges_le hO L hk hf

end FaultTolerantSpanners
