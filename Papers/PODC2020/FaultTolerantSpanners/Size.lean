import Papers.PODC2020.FaultTolerantSpanners.Greedy
import Cslib.Foundations.Combinatorics.SimpleGraph.BlockingSet
import Mathlib

/-!
# Size of the modified greedy spanner (Lemma 6, Theorem 8 of Dinitz–Robelle, PODC'20)

* `exists_blockingSet_of_cuts` — the core of **Lemma 6**: if every edge of a list `A` (in insertion
  order) had, when inserted, a length-`(2k-1)` cut of size `≤ D` in the graph of the earlier edges,
  then `edgeGraph A` has a `2k`-blocking set of size `≤ D · |E|` (an instance of the shared
  `SimpleGraph.exists_blockingSet_of_insertion`).
* `modifiedGreedy_exists_blockingSet` — **Lemma 6**: the output of Algorithm 3 has a `2k`-blocking set
  of size `≤ (2k - 1) f |E(H)|`.
* `modifiedGreedy_card_edges_le` — **Theorem 8** with explicit constants:
  `|E(H)| ≤ 8 (2 (2k-1) f)^{1-1/k} n^{1+1/k} ≤ 32 k f^{1-1/k} n^{1+1/k}`.
-/

open Finset SimpleGraph

namespace FaultTolerantSpanners

variable {V : Type*} [DecidableEq V]

/-- **Lemma 6 (abstract form).** Let `A` be a list of edges (in insertion order) such that the
`i`-th edge `(u, v)` has a length-`(2k-1)` cut of size `≤ D` in the graph of the first `i` edges.
Then `edgeGraph A` has a `2k`-blocking set `B` with `|B| ≤ D · |E(edgeGraph A)|`. -/
theorem exists_blockingSet_of_cuts {A : List (V × V)} {k D : ℕ} (hk : 1 ≤ k)
    (hA : ∀ i (h : i < A.length), ∃ F : Finset V,
      IsLengthCut (edgeGraph (A.take i)) A[i].1 A[i].2 (2 * k - 1) F ∧ #F ≤ D) :
    ∃ B : Finset (V × Sym2 V), (edgeGraph A).IsBlockingSet (2 * k) B ∧
      #B ≤ D * (edgeGraph A).edgeSet.ncard := by
  choose F hF hFD using hA
  refine exists_blockingSet_of_insertion (fun i h heq => ?_) (fun i h hadj => ?_) F hFD
    (fun i h x hx => ⟨fun h' => (hF i h).1 (h' ▸ hx), fun h' => (hF i h).2.1 (h' ▸ hx)⟩)
    (fun i h p hp _ => ?_)
  · -- endpoints are distinct
    have := (hF i h).2.2
    rw [heq, edist_self] at this
    simp at this
  · -- the `i`-th edge is not yet present
    obtain ⟨hu, hv, hlt⟩ := hF i h
    rw [edist_eq_one_iff_adj.mpr (show ((edgeGraph (A.take i)).deleteVerts (F i h)).Adj _ _ from
      ⟨hadj, hu, hv⟩)] at hlt
    have : ((2 * k - 1 : ℕ) : ℕ∞) < 1 := hlt
    norm_cast at this
    omega
  · -- a short walk of earlier edges meets the cut
    obtain ⟨hu, hv, hcut⟩ := hF i h
    obtain ⟨x, hxp, hxF⟩ := not_disjoint_iff.mp
      ((lt_edist_deleteVerts_iff hu hv).mp hcut p (by omega))
    exact ⟨x, (Walk.mem_interior.mp hxp).1, hxF⟩

variable [Fintype V]

/-- **Lemma 6 of Dinitz–Robelle.** The output `H` of Algorithm 3 has a `2k`-blocking set of size at
most `(2k - 1) f |E(H)|`. -/
theorem modifiedGreedy_exists_blockingSet {O : ShortPathOracle V} (hO : O.Spec)
    {L : List (V × V)} {k f : ℕ} (hk : 1 ≤ k) :
    ∃ B : Finset (V × Sym2 V), (modifiedGreedy O k f L).IsBlockingSet (2 * k) B ∧
      #B ≤ (2 * k - 1) * f * (modifiedGreedy O k f L).edgeSet.ncard := by
  apply exists_blockingSet_of_cuts hk
  intro i hi
  have := dec_greedyEdges_take (dec := fun H u v => lbc O H u v (2 * k - 1) f) L i hi
  obtain ⟨F, hF, hFc⟩ := exists_isLengthCut_of_lbc hO this
  exact ⟨F, hF, by rw [mul_comm]; exact hFc⟩

/-- **Theorem 8 of Dinitz–Robelle** (explicit constants, first form): the output of Algorithm 3 has
at most `8 (2 (2k-1) f)^{1-1/k} n^{1+1/k}` edges, for every edge order and every BFS oracle. -/
theorem modifiedGreedy_card_edges_le' {O : ShortPathOracle V} (hO : O.Spec)
    (L : List (V × V)) {k f : ℕ} (hk : 1 ≤ k) (hf : 1 ≤ f) :
    ((modifiedGreedy O k f L).edgeSet.ncard : ℝ) ≤
      8 * (2 * ((2 * k - 1) * f : ℕ) : ℝ) ^ (1 - 1 / (k : ℝ)) *
        (Fintype.card V : ℝ) ^ (1 + 1 / (k : ℝ)) := by
  obtain ⟨B, hB, hBcard⟩ := modifiedGreedy_exists_blockingSet hO (L := L) (f := f) hk
  exact hB.ncard_edgeSet_le_rpow hk (Nat.mul_pos (by omega) (by omega)) hBcard

/-- **Theorem 8 of Dinitz–Robelle**: the output of Algorithm 3 has at most
`32 k f^{1-1/k} n^{1+1/k}` edges (`= O(k f^{1-1/k} n^{1+1/k})`), for every edge order and every BFS
oracle. -/
theorem modifiedGreedy_card_edges_le {O : ShortPathOracle V} (hO : O.Spec)
    (L : List (V × V)) {k f : ℕ} (hk : 1 ≤ k) (hf : 1 ≤ f) :
    ((modifiedGreedy O k f L).edgeSet.ncard : ℝ) ≤
      32 * k * (f : ℝ) ^ (1 - 1 / (k : ℝ)) * (Fintype.card V : ℝ) ^ (1 + 1 / (k : ℝ)) := by
  obtain ⟨B, hB, hBcard⟩ := modifiedGreedy_exists_blockingSet hO (L := L) (f := f) hk
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hDc : (((2 * k - 1) * f : ℕ) : ℝ) ≤ (2 * k) * f := by
    have : (2 * k - 1) * f ≤ 2 * k * f := Nat.mul_le_mul_right _ (Nat.sub_le _ _)
    exact_mod_cast this
  refine (hB.ncard_edgeSet_le_mul_rpow hk (Nat.mul_pos (by omega) (by omega)) hBcard
    (Nat.cast_nonneg f) (by linarith) hDc).trans_eq (by ring)

end FaultTolerantSpanners
