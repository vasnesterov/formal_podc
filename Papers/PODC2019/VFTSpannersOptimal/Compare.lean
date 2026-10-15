import Papers.PODC2019.VFTSpannersOptimal.FTGreedy
import Papers.PODC2020.FaultTolerantSpanners.Main

/-!
# Relation to Dinitz–Robelle (PODC'20)

Both analyses go through the same two steps, formalized once in `Cslib/Foundations/Combinatorics/SimpleGraph`:
a small blocking set (`IsBlockingSet`) ⇒ a dense subgraph of high girth on few vertices
(`IsBlockingSet.exists_dense_subgraph_of_le`) ⇒ a bound in terms of `b = girthExtremal`
(`IsBlockingSet.ncard_le_girthExtremal`) or, via the Moore bound, in terms of `n^{1+1/k}`.
The only difference is the size of the blocking set:

| | algorithm | blocking set (stretch `2k-1`) | `b`-bound | Moore form |
|---|---|---|---|---|
| Bodwin–Patel | exact FT greedy (exp. time) | `f · |E|` | `32 f² b(n/2f, 2k)` | `16 f^{1-1/k} n^{1+1/k}` |
| Dinitz–Robelle | greedy + LBC approx. (poly time) | `(2k-1) f · |E|` | `32 ((2k-1)f)² b(n/(2(2k-1)f), 2k)` | `32 k f^{1-1/k} n^{1+1/k}` |

`dinitzRobelle_card_edges_le_girthExtremal` below is the `b`-form of the Dinitz–Robelle bound (not
stated in either paper).
-/

open Finset SimpleGraph FaultTolerantSpanners

namespace VFTSpannersOptimal

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- **Dinitz–Robelle in extremal form.** The output of their polynomial-time Algorithm 3 (stretch
`2k - 1`, any edge order, any BFS oracle) has at most `32 ((2k-1) f)² · max(b(⌊n / 2(2k-1)f⌋, 2k), 1)`
edges — the Bodwin–Patel bound with `f` replaced by `(2k - 1) f`. -/
theorem dinitzRobelle_card_edges_le_girthExtremal {O : ShortPathOracle V} (hO : O.Spec)
    (L : List (V × V)) {k f : ℕ} (hk : 1 ≤ k) (hf : 1 ≤ f) :
    (modifiedGreedy O k f L).edgeSet.ncard ≤ 32 * ((2 * k - 1) * f) ^ 2 *
      max (girthExtremal (Fintype.card V / (2 * ((2 * k - 1) * f))) (2 * k)) 1 := by
  obtain ⟨B, hB, hBc⟩ := modifiedGreedy_exists_blockingSet hO (L := L) (f := f) hk
  exact hB.ncard_le_girthExtremal hBc (Nat.mul_pos (by omega) (by omega))

/-- The two Moore-form constants: Bodwin–Patel's `16 f^{1-1/k}` is at most Dinitz–Robelle's
`32 k f^{1-1/k}` (the latter loses a factor `2k`). -/
lemma bodwinPatel_constant_le_dinitzRobelle {k f : ℕ} (hk : 1 ≤ k) :
    16 * (f : ℝ) ^ (1 - 1 / (k : ℝ)) ≤ 32 * k * (f : ℝ) ^ (1 - 1 / (k : ℝ)) := by
  have : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have h0 : 0 ≤ (f : ℝ) ^ (1 - 1 / (k : ℝ)) := by positivity
  nlinarith

/-- **Non-vacuity / existence form of Corollary 2 (Bodwin–Patel).** Every finite weighted graph has
an `f`-VFT `(2k-1)`-spanner with at most `16 f^{1-1/k} n^{1+1/k}` edges, namely the output of the VFT
greedy algorithm on a weight-sorted edge list. -/
theorem exists_vft_spanner_ftGreedy (G : SimpleGraph V) (w : Sym2 V → NNReal) {k f : ℕ}
    (hk : 1 ≤ k) (hf : 1 ≤ f) :
    ∃ H : SimpleGraph V, IsWeightedVFTSpanner G H w f (2 * k - 1) ∧
      (H.edgeSet.ncard : ℝ) ≤
        16 * (f : ℝ) ^ (1 - 1 / (k : ℝ)) * (Fintype.card V : ℝ) ^ (1 + 1 / (k : ℝ)) := by
  obtain ⟨L, hLG, hL, hsort⟩ := exists_sorted_edgeList G w
  exact ⟨ftGreedy w (2 * k - 1) f L,
    ftGreedy_isWeightedVFTSpanner (by omega) hLG (fun u v h => Or.inl (hL u v h)),
    ftGreedy_card_edges_le_rpow hk hf hsort⟩

end VFTSpannersOptimal
