import Papers.PODC2020.FaultTolerantSpanners.Greedy
import Papers.PODC2020.FaultTolerantSpanners.SizeArith
import Cslib.Foundations.Combinatorics.SimpleGraph.BlockingSet
import Cslib.Foundations.Combinatorics.SimpleGraph.Cycle
import Mathlib

/-!
# Size of the modified greedy spanner (Lemma 6, Theorem 8 of Dinitz–Robelle, PODC'20)

* `exists_blockingSet_of_cuts` — the core of **Lemma 6**: if every edge of a list `A` (in insertion
  order) had, when inserted, a length-`(2k-1)` cut of size `≤ D` in the graph of the earlier edges,
  then `edgeGraph A` has a `2k`-blocking set of size `≤ D · |E|`.
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
  set M : List (Sym2 V) := A.map (fun p => s(p.1, p.2)) with hM
  -- endpoints are distinct
  have hne : ∀ i (h : i < A.length), A[i].1 ≠ A[i].2 := by
    intro i h heq
    have := (hF i h).2.2
    rw [heq, edist_self] at this
    simp at this
  -- the `i`-th edge is not yet present
  have hnotadj : ∀ i (h : i < A.length), ¬ (edgeGraph (A.take i)).Adj A[i].1 A[i].2 := by
    intro i h hadj
    obtain ⟨hu, hv, hlt⟩ := hF i h
    have h1 : ((edgeGraph (A.take i)).deleteVerts (F i h)).edist A[i].1 A[i].2 = 1 :=
      edist_eq_one_iff_adj.mpr ⟨hadj, hu, hv⟩
    rw [h1] at hlt
    have : ((2 * k - 1 : ℕ) : ℕ∞) < 1 := hlt
    norm_cast at this
    omega
  have hMlen : M.length = A.length := by simp [hM]
  have hMget : ∀ i (h : i < M.length), M[i] = s(A[i].1, A[i].2) := by
    intro i h; simp [hM]
  -- no edge is inserted twice
  have hnodup : M.Nodup := by
    rw [List.Nodup, List.pairwise_iff_getElem]
    intro j i hj hi hji heq
    rw [hMlen] at hj hi
    rw [hMget j (by omega), hMget i (by omega)] at heq
    apply hnotadj i hi
    refine edgeGraph_adj.mpr ⟨hne i hi, A[j], ?_, heq⟩
    have : (A.take i)[j]'(by simp; omega) = A[j] := List.getElem_take
    rw [← this]
    exact List.getElem_mem _
  have hmemM : ∀ e, e ∈ (edgeGraph A).edgeSet ↔ e ∈ M := by
    intro e
    rw [mem_edgeSet_edgeGraph]
    constructor
    · rintro ⟨⟨p, hp, rfl⟩, -⟩
      exact List.mem_map_of_mem hp
    · intro he
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem he
      rw [hMget]
      refine ⟨⟨A[i], List.getElem_mem _, rfl⟩, ?_⟩
      simpa using hne i (by omega)
  have hncard : (edgeGraph A).edgeSet.ncard = A.length := by
    have : (edgeGraph A).edgeSet = ↑M.toFinset := by
      ext e; simp [hmemM]
    rw [this, Set.ncard_coe_finset, List.toFinset_card_of_nodup hnodup, hMlen]
  -- the blocking set
  let B : Finset (V × Sym2 V) := univ.biUnion fun i : Fin A.length =>
    (F i i.2).image fun x => (x, s(A[i].1, A[i].2))
  refine ⟨B, ⟨?_, ?_⟩, ?_⟩
  · -- pairs are (vertex ∉ edge, edge)
    intro p hp
    simp only [B, mem_biUnion, mem_univ, true_and, mem_image] at hp
    obtain ⟨i, x, hx, rfl⟩ := hp
    refine ⟨(hmemM _).mpr ?_, ?_⟩
    · exact List.mem_map.mpr ⟨_, List.getElem_mem i.2, rfl⟩
    · obtain ⟨hu, hv, -⟩ := hF i i.2
      simp only [Sym2.mem_iff, not_or]
      exact ⟨fun h => hu (h ▸ hx), fun h => hv (h ▸ hx)⟩
  · -- every short cycle is blocked
    intro v c hc hlen
    have hcM : ∀ e ∈ c.edges, e ∈ M := fun e he => (hmemM e).mp (c.edges_subset_edgeSet he)
    have hne' : c.edges.toFinset.Nonempty := by
      cases c with
      | nil => exact absurd hc (by simp [Walk.isCycle_def])
      | cons h q => simp
    obtain ⟨e, he, hmax⟩ := c.edges.toFinset.exists_max_image (fun e => M.idxOf e) hne'
    rw [List.mem_toFinset] at he
    set i := M.idxOf e with hi_def
    have hiM : i < M.length := List.idxOf_lt_length_of_mem (hcM e he)
    have hiA : i < A.length := by omega
    have hMi : M[i] = e := List.getElem_idxOf hiM
    have heA : e = s(A[i].1, A[i].2) := by rw [← hMi, hMget]
    rw [heA] at he
    obtain ⟨p, -, hpe, hps, hpl⟩ := hc.exists_path_of_mem_edges he
    -- all edges of `p` were inserted before `e`
    have hpold : ∀ e' ∈ p.edges, e' ∈ (edgeGraph (A.take i)).edgeSet := by
      intro e' he'
      obtain ⟨he'c, he'ne⟩ := hpe e' he'
      have hj : M.idxOf e' < M.length := List.idxOf_lt_length_of_mem (hcM e' he'c)
      have hMj : M[M.idxOf e'] = e' := List.getElem_idxOf hj
      have hle : M.idxOf e' ≤ i := hmax e' (List.mem_toFinset.mpr he'c)
      have hlt : M.idxOf e' < i := by
        refine lt_of_le_of_ne hle fun heq => he'ne ?_
        rw [← hMj, ← heA, ← hMi]
        simp only [heq]
      rw [mem_edgeSet_edgeGraph]
      refine ⟨⟨A[M.idxOf e'], ?_, by rw [← hMget _ hj, hMj]⟩, ?_⟩
      · have : (A.take i)[M.idxOf e']'(by simp; omega) = A[M.idxOf e'] := List.getElem_take
        rw [← this]
        exact List.getElem_mem _
      · exact (edgeGraph A).not_isDiag_of_mem_edgeSet (p.edges_subset_edgeSet he')
    let p' := p.transfer (edgeGraph (A.take i)) hpold
    obtain ⟨hu, hv, hcut⟩ := hF i hiA
    have hp'len : p'.length ≤ 2 * k - 1 := by
      simp only [p', Walk.length_transfer]; omega
    have := (lt_edist_deleteVerts_iff hu hv).mp hcut p' hp'len
    obtain ⟨x, hxp, hxF⟩ := not_disjoint_iff.mp this
    have hxs : x ∈ p.support := by
      have := (Walk.mem_interior.mp hxp).1
      simpa [p', Walk.support_transfer] using this
    refine ⟨(x, s(A[i].1, A[i].2)), ?_, hps x hxs, he⟩
    simp only [B, mem_biUnion, mem_univ, true_and, mem_image]
    exact ⟨⟨i, hiA⟩, x, hxF, rfl⟩
  · -- size
    rw [hncard]
    calc #B ≤ ∑ i : Fin A.length, #((F i i.2).image fun x => (x, s(A[i].1, A[i].2))) :=
          card_biUnion_le
      _ ≤ ∑ _i : Fin A.length, D := sum_le_sum fun i _ => card_image_le.trans (hFD i i.2)
      _ = D * A.length := by simp [mul_comm]

variable [Fintype V]

/-- **Lemma 6 of Dinitz–Robelle.** The output `H` of Algorithm 3 has a `2k`-blocking set of size at
most `(2k - 1) f |E(H)|`. -/
theorem modifiedGreedy_exists_blockingSet {O : ShortPathOracle V} (hO : O.Spec)
    {L : List (V × V)} {k f : ℕ} (hk : 1 ≤ k) :
    ∃ B : Finset (V × Sym2 V), (modifiedGreedy O k f L).IsBlockingSet (2 * k) B ∧
      #B ≤ (2 * k - 1) * f * (modifiedGreedy O k f L).edgeSet.ncard := by
  apply exists_blockingSet_of_cuts hk
  intro i hi
  have := greedyGood_greedyList (dec := fun H u v => lbc O H u v (2 * k - 1) f) L i hi
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
