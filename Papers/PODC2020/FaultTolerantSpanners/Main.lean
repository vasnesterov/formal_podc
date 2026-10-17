import Papers.PODC2020.FaultTolerantSpanners.Weighted

/-!
# Main results of Dinitz–Robelle, *Efficient and Simple Algorithms for Fault-Tolerant Spanners*
(PODC 2020), sequential part

* valid inputs for Algorithms 3/4 exist (`SimpleGraph.exists_sorted_edgeList`, non-vacuity).
* `theorem2_unweighted`, `theorem2_weighted` — Theorem 2 (without the running-time claim): for every
  correct BFS oracle, the (weighted) modified greedy algorithm outputs an `f`-VFT `(2k-1)`-spanner
  with at most `32 k f^{1-1/k} n^{1+1/k}` edges.
-/

open Finset SimpleGraph
open scoped NNReal

namespace FaultTolerantSpanners

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- **Theorem 2 of Dinitz–Robelle (unweighted; correctness and size).** For every correct BFS oracle
and every order of the edges, Algorithm 3 returns an `f`-VFT `(2k-1)`-spanner of `G` with at most
`32 k f^{1-1/k} n^{1+1/k}` edges. -/
theorem theorem2_unweighted {O : ShortPathOracle V} (hO : O.Spec) {G : SimpleGraph V}
    {L : List (V × V)} {k f : ℕ} (hk : 1 ≤ k) (hf : 1 ≤ f)
    (hLG : ∀ p ∈ L, G.Adj p.1 p.2) (hL : ∀ u v, G.Adj u v → (u, v) ∈ L ∨ (v, u) ∈ L) :
    IsVFTSpanner G (modifiedGreedy O k f L) f (2 * k - 1) ∧
      ((modifiedGreedy O k f L).edgeSet.ncard : ℝ) ≤
        32 * k * (f : ℝ) ^ (1 - 1 / (k : ℝ)) * (Fintype.card V : ℝ) ^ (1 + 1 / (k : ℝ)) :=
  ⟨modifiedGreedy_isVFTSpanner hO hk hLG hL, modifiedGreedy_card_edges_le hO L hk hf⟩

/-- **Theorem 2 / Theorem 10 of Dinitz–Robelle (weighted; correctness and size).** For every correct
BFS oracle, Algorithm 4 (Algorithm 3 on the edges in nondecreasing weight order) returns an `f`-VFT
`(2k-1)`-spanner of `(G, w)` with at most `32 k f^{1-1/k} n^{1+1/k}` edges. -/
theorem theorem2_weighted {O : ShortPathOracle V} (hO : O.Spec) {G : SimpleGraph V}
    {w : Sym2 V → ℝ≥0} {L : List (V × V)} {k f : ℕ} (hk : 1 ≤ k) (hf : 1 ≤ f)
    (hLG : ∀ p ∈ L, G.Adj p.1 p.2) (hL : ∀ u v, G.Adj u v → (u, v) ∈ L ∨ (v, u) ∈ L)
    (hsort : L.Pairwise fun a b => w s(a.1, a.2) ≤ w s(b.1, b.2)) :
    IsWeightedVFTSpanner G (modifiedGreedy O k f L) w f (2 * k - 1) ∧
      ((modifiedGreedy O k f L).edgeSet.ncard : ℝ) ≤
        32 * k * (f : ℝ) ^ (1 - 1 / (k : ℝ)) * (Fintype.card V : ℝ) ^ (1 + 1 / (k : ℝ)) :=
  ⟨modifiedGreedy_isWeightedVFTSpanner hO hk hLG hL hsort,
    modifiedGreedyWeighted_card_edges_le hO L hk hf hsort⟩

/-- Existence form of Theorem 2: every finite weighted graph has an `f`-VFT `(2k-1)`-spanner with
at most `32 k f^{1-1/k} n^{1+1/k}` edges. -/
theorem exists_vft_spanner (G : SimpleGraph V) (w : Sym2 V → ℝ≥0) {k f : ℕ} (hk : 1 ≤ k)
    (hf : 1 ≤ f) :
    ∃ H : SimpleGraph V, IsWeightedVFTSpanner G H w f (2 * k - 1) ∧
      (H.edgeSet.ncard : ℝ) ≤
        32 * k * (f : ℝ) ^ (1 - 1 / (k : ℝ)) * (Fintype.card V : ℝ) ^ (1 + 1 / (k : ℝ)) := by
  obtain ⟨O, hO⟩ := ShortPathOracle.exists_spec (V := V)
  obtain ⟨L, hLG, hL, hsort⟩ := exists_sorted_edgeList G w
  exact ⟨_, theorem2_weighted hO hk hf hLG (fun u v h => Or.inl (hL u v h)) hsort⟩

end FaultTolerantSpanners
