import Papers.PODC2020.FaultTolerantSpanners.Greedy
import Cslib.Foundations.Combinatorics.SimpleGraph.BlockingSet
import Cslib.Foundations.Combinatorics.SimpleGraph.Cycle
import Mathlib

/-!
# Blocking sets from insertion histories (core of Lemma 3 of Bodwin–Patel, PODC'19)

`exists_blockingSet_of_insertion`: let `A` be a list of edges in insertion order (the output of a
greedy scan, `FaultTolerantSpanners.greedyList`). Suppose that for the `i`-th edge `(u, v)` there is a
set `X_i ∌ u, v` of at most `D` vertices hitting every `u`–`v` walk of length `≤ t - 1` that uses only
earlier edges. Then `edgeGraph A` has a `t`-blocking set of size `≤ D · |E|`.

The argument is the one of Bodwin–Patel: for a cycle `C` with `≤ t` edges, let `e` be its edge
inserted last; then `C - e` is a walk between the endpoints of `e`, with `≤ t - 1` earlier edges, so it
meets `X_e`.
-/

open Finset SimpleGraph FaultTolerantSpanners

namespace VFTSpannersOptimal

variable {V : Type*}

/-- The greedy scan keeps a sublist of its input. -/
lemma greedyList_sublist {dec : SimpleGraph V → V → V → Bool} (L : List (V × V)) :
    List.Sublist (greedyList dec L) L := by
  suffices ∀ (l A : List (V × V)), ∃ l' : List (V × V), List.Sublist l' l ∧
      l.foldl (greedyStep dec) A = A ++ l' by
    obtain ⟨l', hl', h⟩ := this L []
    rw [greedyList, h, List.nil_append]
    exact hl'
  intro l
  induction l with
  | nil => intro A; exact ⟨[], List.Sublist.slnil, by simp⟩
  | cons e l ih =>
    intro A
    rw [List.foldl_cons]
    by_cases hd : dec (edgeGraph A) e.1 e.2
    · have hs : greedyStep dec A e = A ++ [e] := by simp [greedyStep, hd]
      obtain ⟨l', hl', h⟩ := ih (A ++ [e])
      exact ⟨e :: l', hl'.cons_cons e, by rw [hs, h]; simp⟩
    · have hs : greedyStep dec A e = A := by simp [greedyStep, hd]
      obtain ⟨l', hl', h⟩ := ih A
      exact ⟨l', hl'.cons e, by rw [hs, h]⟩

variable [DecidableEq V]

/-- **Blocking sets from an insertion history.** -/
theorem exists_blockingSet_of_insertion {A : List (V × V)} {t D : ℕ}
    (hne : ∀ i (h : i < A.length), A[i].1 ≠ A[i].2)
    (hnew : ∀ i (h : i < A.length), ¬ (edgeGraph (A.take i)).Adj A[i].1 A[i].2)
    (X : ∀ i, i < A.length → Finset V) (hXcard : ∀ i h, #(X i h) ≤ D)
    (hXe : ∀ i h, ∀ x ∈ X i h, x ≠ A[i].1 ∧ x ≠ A[i].2)
    (hhit : ∀ i (h : i < A.length) (p : (edgeGraph (A.take i)).Walk A[i].1 A[i].2),
      p.length + 1 ≤ t →
      (∀ e ∈ p.edges, ∃ j, ∃ hj : j < A.length, j < i ∧ e = s(A[j].1, A[j].2)) →
      ∃ x ∈ p.support, x ∈ X i h) :
    ∃ B : Finset (V × Sym2 V), (edgeGraph A).IsBlockingSet t B ∧
      #B ≤ D * (edgeGraph A).edgeSet.ncard := by
  set M : List (Sym2 V) := A.map (fun p => s(p.1, p.2)) with hM
  have hMlen : M.length = A.length := by simp [hM]
  have hMget : ∀ i (h : i < M.length), M[i] = s(A[i].1, A[i].2) := by
    intro i h; simp [hM]
  -- no edge is inserted twice
  have hnodup : M.Nodup := by
    rw [List.Nodup, List.pairwise_iff_getElem]
    intro j i hj hi hji heq
    rw [hMlen] at hj hi
    rw [hMget j (by omega), hMget i (by omega)] at heq
    apply hnew i hi
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
    (X i i.2).image fun x => (x, s(A[i].1, A[i].2))
  refine ⟨B, ⟨?_, ?_⟩, ?_⟩
  · -- pairs are (vertex ∉ edge, edge)
    intro p hp
    simp only [B, mem_biUnion, mem_univ, true_and, mem_image] at hp
    obtain ⟨i, x, hx, rfl⟩ := hp
    refine ⟨(hmemM _).mpr ?_, ?_⟩
    · exact List.mem_map.mpr ⟨_, List.getElem_mem i.2, rfl⟩
    · obtain ⟨hu, hv⟩ := hXe i i.2 x hx
      simp only [Sym2.mem_iff, not_or]
      exact ⟨hu, hv⟩
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
    have hold : ∀ e' ∈ p.edges, ∃ j, ∃ hj : j < A.length, j < i ∧ e' = s(A[j].1, A[j].2) := by
      intro e' he'
      obtain ⟨he'c, he'ne⟩ := hpe e' he'
      have hj : M.idxOf e' < M.length := List.idxOf_lt_length_of_mem (hcM e' he'c)
      have hMj : M[M.idxOf e'] = e' := List.getElem_idxOf hj
      have hle : M.idxOf e' ≤ i := hmax e' (List.mem_toFinset.mpr he'c)
      have hlt : M.idxOf e' < i := by
        refine lt_of_le_of_ne hle fun heq => he'ne ?_
        rw [← hMj, ← heA, ← hMi]
        simp only [heq]
      exact ⟨M.idxOf e', by omega, hlt, by rw [← hMget _ hj, hMj]⟩
    have hpold : ∀ e' ∈ p.edges, e' ∈ (edgeGraph (A.take i)).edgeSet := by
      intro e' he'
      obtain ⟨j, hj, hji, rfl⟩ := hold e' he'
      rw [mem_edgeSet_edgeGraph]
      refine ⟨⟨A[j], ?_, rfl⟩, ?_⟩
      · have : (A.take i)[j]'(by simp; omega) = A[j] := List.getElem_take
        rw [← this]
        exact List.getElem_mem _
      · exact (edgeGraph A).not_isDiag_of_mem_edgeSet (p.edges_subset_edgeSet he')
    let p' := p.transfer (edgeGraph (A.take i)) hpold
    obtain ⟨x, hxp, hxX⟩ := hhit i hiA p' (by simp only [p', Walk.length_transfer]; omega)
      (fun e' he' => hold e' (by simpa [p', Walk.edges_transfer] using he'))
    have hxs : x ∈ p.support := by simpa [p', Walk.support_transfer] using hxp
    refine ⟨(x, s(A[i].1, A[i].2)), ?_, hps x hxs, he⟩
    simp only [B, mem_biUnion, mem_univ, true_and, mem_image]
    exact ⟨⟨i, hiA⟩, x, hxX, rfl⟩
  · -- size
    rw [hncard]
    calc #B ≤ ∑ i : Fin A.length, #((X i i.2).image fun x => (x, s(A[i].1, A[i].2))) :=
          card_biUnion_le
      _ ≤ ∑ _i : Fin A.length, D := sum_le_sum fun i _ => card_image_le.trans (hXcard i i.2)
      _ = D * A.length := by simp [mul_comm]

end VFTSpannersOptimal
