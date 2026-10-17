import Papers.PODC2020.FaultTolerantSpanners.Greedy
import Papers.PODC2020.FaultTolerantSpanners.SizeArith
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
  classical
  set H := modifiedGreedy O k f L
  obtain ⟨B, hB, hBcard⟩ := modifiedGreedy_exists_blockingSet hO (L := L) (f := f) hk
  have hD : 1 ≤ (2 * k - 1) * f := Nat.mul_pos (by omega) (by omega)
  apply size_bound_of_nat hk hD
  · have h1 : H.edgeSet.ncard = #H.edgeFinset := by
      rw [← coe_edgeFinset, Set.ncard_coe_finset]
    have h2 := card_edgeFinset_le_card_choose_two (G := H)
    rw [Nat.choose_two_right] at h2
    have h3 := Nat.div_mul_le_self (Fintype.card V * (Fintype.card V - 1)) 2
    omega
  · intro s d hs hsd
    exact hB.ncard_edgeSet_mul_le hk hBcard hD hs hsd

/-- **Theorem 8 of Dinitz–Robelle**: the output of Algorithm 3 has at most
`32 k f^{1-1/k} n^{1+1/k}` edges (`= O(k f^{1-1/k} n^{1+1/k})`), for every edge order and every BFS
oracle. -/
theorem modifiedGreedy_card_edges_le {O : ShortPathOracle V} (hO : O.Spec)
    (L : List (V × V)) {k f : ℕ} (hk : 1 ≤ k) (hf : 1 ≤ f) :
    ((modifiedGreedy O k f L).edgeSet.ncard : ℝ) ≤
      32 * k * (f : ℝ) ^ (1 - 1 / (k : ℝ)) * (Fintype.card V : ℝ) ^ (1 + 1 / (k : ℝ)) := by
  refine (modifiedGreedy_card_edges_le' hO L hk hf).trans ?_
  exact mul_le_mul_of_nonneg_right (constant_le hk hf) (by positivity)

end FaultTolerantSpanners
