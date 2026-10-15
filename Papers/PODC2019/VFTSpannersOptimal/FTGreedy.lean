import Papers.PODC2019.VFTSpannersOptimal.Blocking
import Papers.PODC2020.FaultTolerantSpanners.SizeArith
import Cslib.Foundations.Combinatorics.SimpleGraph.WeightedSpanner
import Cslib.Foundations.Combinatorics.SimpleGraph.GirthExtremal
import Mathlib

/-!
# The FT greedy algorithm and its size (Bodwin–Patel, PODC'19)

**Algorithm 1** (VFT / EFT greedy): scan the edges in nondecreasing weight order and add `(u, v)` to
the current graph `H` iff there is a fault set `F` of at most `f` vertices (resp. edges) with
`d_{H \ F}(u, v) > k · w(u, v)`. Fault sets are required to avoid the edge being tested (`u, v ∉ F`,
resp. `{u, v} ∉ F`); see `differencies.md` (without this the literal test is always true for
`f ≥ 1`, cf. `ftGreedyLiteral_eq`).

* `ftGreedy w k f L` / `ftGreedyEdge w k f L` — Algorithm 1 for vertex / edge faults, on top of the
  generic greedy scan `FaultTolerantSpanners.greedy` (edge list `L`, weights `w`, stretch `k`).
* `ftGreedy_isWeightedVFTSpanner` / `ftGreedyEdge_isWeightedEFTSpanner` — correctness (for any order).
* **Lemma 3**: `ftGreedy_exists_blockingSet` / `ftGreedyEdge_exists_blockingSet` — a `(k+1)`-blocking set
  of size `≤ f |E(H)|` (the edge version produces a *vertex*–edge blocking set too).
* **Theorem 1**: `ftGreedy_card_edges_le` / `ftGreedyEdge_card_edges_le`:
  `|E(H)| ≤ 32 f² · max(b(⌊n / 2f⌋, k + 1), 1)`, with `b = SimpleGraph.girthExtremal`.
* **Corollary 2**: `ftGreedy_card_edges_le_rpow` / `ftGreedyEdge_card_edges_le_rpow`: for stretch
  `2k - 1`, `|E(H)| ≤ 16 f^{1-1/k} n^{1+1/k}`.
-/

open Finset SimpleGraph FaultTolerantSpanners
open scoped ENNReal NNReal

namespace VFTSpannersOptimal

variable {V : Type*}

/-! ### Algorithm 1 -/

open Classical in
/-- The test of the VFT greedy algorithm: is there a set `F ∌ u, v` of at most `f` vertices with
`d_{H \ F}(u, v) > k · w(u, v)`? -/
noncomputable def vftTest (w : Sym2 V → ℝ≥0) (k f : ℕ) (H : SimpleGraph V) (u v : V) : Bool :=
  decide (∃ F : Finset V, #F ≤ f ∧ u ∉ F ∧ v ∉ F ∧
    (k : ℝ≥0∞) * w s(u, v) < (H.deleteVerts F).wdist w u v)

open Classical in
/-- The test of the EFT greedy algorithm: is there a set `F ∌ {u, v}` of at most `f` edges with
`d_{H \ F}(u, v) > k · w(u, v)`? -/
noncomputable def eftTest (w : Sym2 V → ℝ≥0) (k f : ℕ) (H : SimpleGraph V) (u v : V) : Bool :=
  decide (∃ F : Finset (Sym2 V), #F ≤ f ∧ s(u, v) ∉ F ∧
    (k : ℝ≥0∞) * w s(u, v) < (H.deleteEdges F).wdist w u v)

/-- **Algorithm 1 (VFT greedy)** on the edge list `L` (to be sorted by weight). -/
noncomputable def ftGreedy (w : Sym2 V → ℝ≥0) (k f : ℕ) (L : List (V × V)) : SimpleGraph V :=
  greedy (vftTest w k f) L

/-- **Algorithm 1 (EFT greedy)** on the edge list `L` (to be sorted by weight). -/
noncomputable def ftGreedyEdge (w : Sym2 V → ℝ≥0) (k f : ℕ) (L : List (V × V)) : SimpleGraph V :=
  greedy (eftTest w k f) L

lemma vftTest_eq_true {w : Sym2 V → ℝ≥0} {k f : ℕ} {H : SimpleGraph V} {u v : V} :
    vftTest w k f H u v = true ↔ ∃ F : Finset V, #F ≤ f ∧ u ∉ F ∧ v ∉ F ∧
      (k : ℝ≥0∞) * w s(u, v) < (H.deleteVerts F).wdist w u v := by
  simp [vftTest]

lemma eftTest_eq_true {w : Sym2 V → ℝ≥0} {k f : ℕ} {H : SimpleGraph V} {u v : V} :
    eftTest w k f H u v = true ↔ ∃ F : Finset (Sym2 V), #F ≤ f ∧ s(u, v) ∉ F ∧
      (k : ℝ≥0∞) * w s(u, v) < (H.deleteEdges F).wdist w u v := by
  simp [eftTest]

lemma wdist_self_eq_zero {G : SimpleGraph V} {w : Sym2 V → ℝ≥0} {u : V} : G.wdist w u u = 0 :=
  le_antisymm ((wdist_le (Walk.nil : G.Walk u u)).trans (by simp)) zero_le

/-! ### Correctness -/

/-- **Correctness of the VFT greedy algorithm** (any edge order): the output is an `f`-VFT
`k`-spanner of `(G, w)`. -/
theorem ftGreedy_isWeightedVFTSpanner {G : SimpleGraph V} {w : Sym2 V → ℝ≥0}
    {L : List (V × V)} {k f : ℕ} (hk : 1 ≤ k)
    (hLG : ∀ p ∈ L, G.Adj p.1 p.2) (hL : ∀ u v, G.Adj u v → (u, v) ∈ L ∨ (v, u) ∈ L) :
    IsWeightedVFTSpanner G (ftGreedy w k f L) w f k := by
  set H := ftGreedy w k f L
  refine isWeightedVFTSpanner_of_adj hk (greedy_le hLG) fun F hF u v huv hu hv => ?_
  have key : ∀ p ∈ L, p.1 ∉ F → p.2 ∉ F →
      (H.deleteVerts F).wdist w p.1 p.2 ≤ k * w s(p.1, p.2) := by
    intro p hp h1 h2
    rcases greedy_mem_or_reject L hp with hmem | ⟨i, hi, -, hrej⟩
    · have hadj : (H.deleteVerts F).Adj p.1 p.2 :=
        ⟨edgeGraph_adj_of_mem hmem (hLG p hp).ne, h1, h2⟩
      refine (wdist_le_of_adj hadj).trans ?_
      exact le_mul_of_one_le_left zero_le (by exact_mod_cast hk)
    · have hno := hrej
      rw [← Bool.not_eq_true, vftTest_eq_true] at hno
      push Not at hno
      exact (wdist_anti (deleteVerts_mono (edgeGraph_take_le_greedy L i))).trans
        (hno F hF h1 h2)
  rcases hL u v huv with h | h
  · exact key _ h hu hv
  · rw [wdist_comm, Sym2.eq_swap]; exact key _ h hv hu

/-- **Correctness of the EFT greedy algorithm** (any edge order). -/
theorem ftGreedyEdge_isWeightedEFTSpanner {G : SimpleGraph V} {w : Sym2 V → ℝ≥0}
    {L : List (V × V)} {k f : ℕ} (hk : 1 ≤ k)
    (hLG : ∀ p ∈ L, G.Adj p.1 p.2) (hL : ∀ u v, G.Adj u v → (u, v) ∈ L ∨ (v, u) ∈ L) :
    IsWeightedEFTSpanner G (ftGreedyEdge w k f L) w f k := by
  set H := ftGreedyEdge w k f L
  refine isWeightedEFTSpanner_of_adj hk (greedy_le hLG) fun F hF u v huv huvF => ?_
  have key : ∀ p ∈ L, s(p.1, p.2) ∉ F →
      (H.deleteEdges F).wdist w p.1 p.2 ≤ k * w s(p.1, p.2) := by
    intro p hp hpF
    rcases greedy_mem_or_reject L hp with hmem | ⟨i, hi, -, hrej⟩
    · have hadj : (H.deleteEdges F).Adj p.1 p.2 := by
        rw [deleteEdges_adj]
        exact ⟨edgeGraph_adj_of_mem hmem (hLG p hp).ne, by simpa using hpF⟩
      refine (wdist_le_of_adj hadj).trans ?_
      exact le_mul_of_one_le_left zero_le (by exact_mod_cast hk)
    · have hno := hrej
      rw [← Bool.not_eq_true, eftTest_eq_true] at hno
      push Not at hno
      exact (wdist_anti (deleteEdges_mono (edgeGraph_take_le_greedy L i))).trans
        (hno F hF hpF)
  rcases hL u v huv with h | h
  · exact key _ h huvF
  · rw [wdist_comm, Sym2.eq_swap]; exact key _ h (by rwa [Sym2.eq_swap])

/-! ### Lemma 3: blocking sets -/

variable [DecidableEq V]

omit [DecidableEq V] in
/-- An earlier edge of a sorted insertion list is no heavier. -/
private lemma weight_le_of_lt {w : Sym2 V → ℝ≥0} {A : List (V × V)}
    (hA : A.Pairwise fun a b => w s(a.1, a.2) ≤ w s(b.1, b.2)) {i j : ℕ} (hi : i < A.length)
    (hj : j < A.length) (hji : j < i) : w s(A[j].1, A[j].2) ≤ w s(A[i].1, A[i].2) :=
  List.pairwise_iff_getElem.mp hA j i hj hi hji

omit [DecidableEq V] in
/-- A walk using only edges no heavier than `c` has weight at most `length · c`. -/
private lemma wlength_le_of_old {w : Sym2 V → ℝ≥0} {A : List (V × V)}
    (hA : A.Pairwise fun a b => w s(a.1, a.2) ≤ w s(b.1, b.2)) {i : ℕ} (hi : i < A.length)
    {G : SimpleGraph V} {a b : V} (p : G.Walk a b)
    (hold : ∀ e ∈ p.edges, ∃ j, ∃ hj : j < A.length, j < i ∧ e = s(A[j].1, A[j].2)) :
    p.wlength w ≤ p.length * w s(A[i].1, A[i].2) := by
  refine p.wlength_le_length_mul w fun e he => ?_
  obtain ⟨j, hj, hji, rfl⟩ := hold e he
  exact_mod_cast weight_le_of_lt hA hi hj hji

/-- **Lemma 3 of Bodwin–Patel (VFT).** If the edges are scanned in nondecreasing weight order, the
output of the VFT greedy algorithm has a `(k+1)`-blocking set of size at most `f |E(H)|`. -/
theorem ftGreedy_exists_blockingSet {w : Sym2 V → ℝ≥0} {L : List (V × V)} {k f : ℕ}
    (hk : 1 ≤ k) (hsort : L.Pairwise fun a b => w s(a.1, a.2) ≤ w s(b.1, b.2)) :
    ∃ B : Finset (V × Sym2 V), (ftGreedy w k f L).IsBlockingSet (k + 1) B ∧
      #B ≤ f * (ftGreedy w k f L).edgeSet.ncard := by
  set A := greedyList (vftTest w k f) L
  have hA : A.Pairwise fun a b => w s(a.1, a.2) ≤ w s(b.1, b.2) :=
    hsort.sublist (greedyList_sublist L)
  have hgood := greedyGood_greedyList (dec := vftTest w k f) L
  have hcut : ∀ i (h : i < A.length), ∃ F : Finset V, #F ≤ f ∧ A[i].1 ∉ F ∧ A[i].2 ∉ F ∧
      (k : ℝ≥0∞) * w s(A[i].1, A[i].2) <
        ((edgeGraph (A.take i)).deleteVerts F).wdist w A[i].1 A[i].2 :=
    fun i h => vftTest_eq_true.mp (hgood i h)
  choose F hFc hu hv hlt using hcut
  refine exists_blockingSet_of_insertion (fun i h heq => ?_) (fun i h hadj => ?_) F hFc
    (fun i h x hx => ⟨fun h' => hu i h (h' ▸ hx), fun h' => hv i h (h' ▸ hx)⟩) ?_
  · have := hlt i h
    rw [heq, wdist_self_eq_zero] at this
    exact absurd this (not_lt.mpr zero_le)
  · have h1 := wdist_le_of_adj (w := w) (show ((edgeGraph (A.take i)).deleteVerts (F i h)).Adj
      A[i].1 A[i].2 from ⟨hadj, hu i h, hv i h⟩)
    have h2 : (w s(A[i].1, A[i].2) : ℝ≥0∞) ≤ k * w s(A[i].1, A[i].2) :=
      le_mul_of_one_le_left zero_le (by exact_mod_cast hk)
    exact absurd (hlt i h) (not_lt.mpr (h1.trans h2))
  · intro i h p hplen hold
    by_contra hnone
    push Not at hnone
    have hsupp : ∀ x ∈ p.support, x ∉ (F i h : Set V) := fun x hx hxF => hnone x hx hxF
    have := hlt i h
    refine absurd this (not_lt.mpr ?_)
    calc ((edgeGraph (A.take i)).deleteVerts (F i h)).wdist w A[i].1 A[i].2
        ≤ (p.toDeleteVerts hsupp).wlength w := wdist_le _
      _ = p.wlength w := by simp [Walk.toDeleteVerts]
      _ ≤ p.length * w s(A[i].1, A[i].2) := wlength_le_of_old hA h p hold
      _ ≤ k * w s(A[i].1, A[i].2) := by gcongr; exact_mod_cast (by omega : p.length ≤ k)

/-- **Lemma 3 of Bodwin–Patel (EFT).** The output of the EFT greedy algorithm also has a
(vertex–edge) `(k+1)`-blocking set of size at most `f |E(H)|`: from each fault edge on the cycle we
keep one of its endpoints outside the tested edge. -/
theorem ftGreedyEdge_exists_blockingSet {w : Sym2 V → ℝ≥0} {L : List (V × V)} {k f : ℕ}
    (hk : 1 ≤ k) (hsort : L.Pairwise fun a b => w s(a.1, a.2) ≤ w s(b.1, b.2)) :
    ∃ B : Finset (V × Sym2 V), (ftGreedyEdge w k f L).IsBlockingSet (k + 1) B ∧
      #B ≤ f * (ftGreedyEdge w k f L).edgeSet.ncard := by
  classical
  set A := greedyList (eftTest w k f) L
  have hA : A.Pairwise fun a b => w s(a.1, a.2) ≤ w s(b.1, b.2) :=
    hsort.sublist (greedyList_sublist L)
  have hgood := greedyGood_greedyList (dec := eftTest w k f) L
  have hcut : ∀ i (h : i < A.length), ∃ F : Finset (Sym2 V), #F ≤ f ∧ s(A[i].1, A[i].2) ∉ F ∧
      (k : ℝ≥0∞) * w s(A[i].1, A[i].2) <
        ((edgeGraph (A.take i)).deleteEdges F).wdist w A[i].1 A[i].2 :=
    fun i h => eftTest_eq_true.mp (hgood i h)
  choose F hFc hFe hlt using hcut
  -- an endpoint of a fault edge outside the tested edge
  let P : ∀ i, i < A.length → Sym2 V → Prop := fun i _ e' => ∃ x ∈ e', x ≠ A[i].1 ∧ x ≠ A[i].2
  let pick : ∀ i (h : i < A.length), Sym2 V → V := fun i h e' =>
    if hx : P i h e' then hx.choose else A[i].1
  let X : ∀ i, i < A.length → Finset V := fun i h =>
    ((F i h).filter (P i h)).image (pick i h)
  have hpick : ∀ i h e', P i h e' → pick i h e' ∈ e' ∧ pick i h e' ≠ A[i].1 ∧
      pick i h e' ≠ A[i].2 := by
    intro i h e' he'
    have hp : pick i h e' = he'.choose := dite_eq_left_of_eq_true (eq_true he')
    rw [hp]
    exact he'.choose_spec
  refine exists_blockingSet_of_insertion (D := f) (fun i h heq => ?_) (fun i h hadj => ?_) X
    (fun i h => card_image_le.trans ((card_filter_le _ _).trans (hFc i h))) ?_ ?_
  · have := hlt i h
    rw [heq, wdist_self_eq_zero] at this
    exact absurd this (not_lt.mpr zero_le)
  · have hadj' : ((edgeGraph (A.take i)).deleteEdges (F i h)).Adj A[i].1 A[i].2 := by
      rw [deleteEdges_adj]; exact ⟨hadj, by simpa using hFe i h⟩
    have h1 := wdist_le_of_adj (w := w) hadj'
    have h2 : (w s(A[i].1, A[i].2) : ℝ≥0∞) ≤ k * w s(A[i].1, A[i].2) :=
      le_mul_of_one_le_left zero_le (by exact_mod_cast hk)
    exact absurd (hlt i h) (not_lt.mpr (h1.trans h2))
  · intro i h x hx
    simp only [X, mem_image, mem_filter] at hx
    obtain ⟨e', ⟨-, he'⟩, rfl⟩ := hx
    exact ⟨(hpick i h e' he').2.1, (hpick i h e' he').2.2⟩
  · intro i h p hplen hold
    -- some edge of `p` is a fault edge
    have hne_uv : A[i].1 ≠ A[i].2 := by
      intro heq
      have := hlt i h
      rw [heq, wdist_self_eq_zero] at this
      exact absurd this (not_lt.mpr zero_le)
    have : ∃ e' ∈ p.edges, e' ∈ F i h := by
      by_contra hnone
      push Not at hnone
      have := hlt i h
      refine absurd this (not_lt.mpr ?_)
      calc ((edgeGraph (A.take i)).deleteEdges (F i h)).wdist w A[i].1 A[i].2
          ≤ (p.toDeleteEdges (F i h) fun e he heF => hnone e he heF).wlength w := wdist_le _
        _ = p.wlength w := by simp [Walk.toDeleteEdges]
        _ ≤ p.length * w s(A[i].1, A[i].2) := wlength_le_of_old hA h p hold
        _ ≤ k * w s(A[i].1, A[i].2) := by gcongr; exact_mod_cast (by omega : p.length ≤ k)
    obtain ⟨e', he'p, he'F⟩ := this
    -- `e'` is not the tested edge, so it has an endpoint outside it
    have hP : P i h e' := by
      induction e' using Sym2.ind with
      | _ a b =>
        have hab : a ≠ b := (p.adj_of_mem_edges he'p).ne
        by_contra hno
        simp only [P, Sym2.mem_iff, not_exists, not_and] at hno
        have ha := hno a (Or.inl rfl)
        have hb := hno b (Or.inr rfl)
        apply hFe i h
        have heq : s(A[i].1, A[i].2) = s(a, b) := by
          by_cases ha1 : a = A[i].1
          · have hb2 : b = A[i].2 := by
              by_contra hb2
              exact hb (fun hb1 => hab (ha1.trans hb1.symm)) hb2
            rw [ha1, hb2]
          · have ha2 : a = A[i].2 := by_contra fun h' => ha ha1 h'
            have hb1 : b = A[i].1 := by
              by_contra hb1
              exact hb hb1 (fun hb2 => hab (ha2.trans hb2.symm))
            rw [ha2, hb1, Sym2.eq_swap]
        rw [heq]; exact he'F
    refine ⟨pick i h e', ?_, ?_⟩
    · have hmem := (hpick i h e' hP).1
      induction e' using Sym2.ind with
      | _ a b =>
        rcases Sym2.mem_iff.mp hmem with h' | h'
        · rw [h']; exact p.fst_mem_support_of_mem_edges he'p
        · rw [h']; exact p.snd_mem_support_of_mem_edges he'p
    · simp only [X, mem_image, mem_filter]
      exact ⟨e', ⟨he'F, hP⟩, rfl⟩

/-! ### Theorem 1 and Corollary 2 -/

variable [Fintype V]

/-- **Theorem 1 of Bodwin–Patel (VFT), explicit form.** For edges scanned in nondecreasing weight
order, the VFT greedy spanner with parameters `f ≥ 1`, `k ≥ 1` satisfies
`|E(H)| ≤ 32 f² · max(b(⌊n / 2f⌋, k + 1), 1)`. -/
theorem ftGreedy_card_edges_le {w : Sym2 V → ℝ≥0} {L : List (V × V)} {k f : ℕ}
    (hk : 1 ≤ k) (hf : 1 ≤ f) (hsort : L.Pairwise fun a b => w s(a.1, a.2) ≤ w s(b.1, b.2)) :
    (ftGreedy w k f L).edgeSet.ncard ≤
      32 * f ^ 2 * max (girthExtremal (Fintype.card V / (2 * f)) (k + 1)) 1 := by
  obtain ⟨B, hB, hBc⟩ := ftGreedy_exists_blockingSet (f := f) hk hsort
  exact hB.ncard_le_girthExtremal hBc hf

/-- **Theorem 1 of Bodwin–Patel (EFT), explicit form.** -/
theorem ftGreedyEdge_card_edges_le {w : Sym2 V → ℝ≥0} {L : List (V × V)} {k f : ℕ}
    (hk : 1 ≤ k) (hf : 1 ≤ f) (hsort : L.Pairwise fun a b => w s(a.1, a.2) ≤ w s(b.1, b.2)) :
    (ftGreedyEdge w k f L).edgeSet.ncard ≤
      32 * f ^ 2 * max (girthExtremal (Fintype.card V / (2 * f)) (k + 1)) 1 := by
  obtain ⟨B, hB, hBc⟩ := ftGreedyEdge_exists_blockingSet (f := f) hk hsort
  exact hB.ncard_le_girthExtremal hBc hf

/-- `8 (2f)^{1-1/k} ≤ 16 f^{1-1/k}`. -/
lemma constant_le_two {k f : ℕ} (hk : 1 ≤ k) :
    8 * (2 * f : ℝ) ^ (1 - 1 / (k : ℝ)) ≤ 16 * (f : ℝ) ^ (1 - 1 / (k : ℝ)) := by
  have he0 : 0 ≤ 1 - 1 / (k : ℝ) := by
    have : (1 : ℝ) ≤ k := by exact_mod_cast hk
    rw [sub_nonneg, div_le_one (by linarith)]; exact this
  have he1 : 1 - 1 / (k : ℝ) ≤ 1 := by
    have : 0 ≤ 1 / (k : ℝ) := by positivity
    linarith
  rw [Real.mul_rpow (by norm_num) (by positivity)]
  have h2 : (2 : ℝ) ^ (1 - 1 / (k : ℝ)) ≤ 2 := by
    calc (2 : ℝ) ^ (1 - 1 / (k : ℝ)) ≤ 2 ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) he1
      _ = 2 := Real.rpow_one 2
  have hf0 : 0 ≤ (f : ℝ) ^ (1 - 1 / (k : ℝ)) := by positivity
  nlinarith

/-- The size bound for any graph with a `2k`-blocking set of size `≤ f |E|`, via the Moore bound. -/
lemma card_le_rpow_of_blockingSet {H : SimpleGraph V} {k f : ℕ} {B : Finset (V × Sym2 V)}
    (hk : 1 ≤ k) (hf : 1 ≤ f) (hB : H.IsBlockingSet (2 * k) B)
    (hBc : #B ≤ f * H.edgeSet.ncard) :
    (H.edgeSet.ncard : ℝ) ≤ 16 * (f : ℝ) ^ (1 - 1 / (k : ℝ)) *
      (Fintype.card V : ℝ) ^ (1 + 1 / (k : ℝ)) := by
  classical
  have h := size_bound_of_nat (m := H.edgeSet.ncard) (n := Fintype.card V) hk hf ?_
    (fun s d hs hsd => hB.ncard_edgeSet_mul_le hk hBc hf hs hsd)
  · refine h.trans ?_
    have := constant_le_two (f := f) hk
    have hn : 0 ≤ (Fintype.card V : ℝ) ^ (1 + 1 / (k : ℝ)) := by positivity
    have : 8 * (2 * (f : ℕ) : ℝ) ^ (1 - 1 / (k : ℝ)) ≤ 16 * (f : ℝ) ^ (1 - 1 / (k : ℝ)) := by
      exact_mod_cast this
    nlinarith
  · have h1 := H.card_edgeFinset_le_card_choose_two
    rw [Nat.choose_two_right] at h1
    rw [← coe_edgeFinset, Set.ncard_coe_finset]
    have := Nat.mul_div_le (Fintype.card V * (Fintype.card V - 1)) 2
    omega

/-- **Corollary 2 of Bodwin–Patel (VFT).** With stretch `2k - 1`, the VFT greedy spanner has at most
`16 f^{1-1/k} n^{1+1/k}` edges. -/
theorem ftGreedy_card_edges_le_rpow {w : Sym2 V → ℝ≥0} {L : List (V × V)} {k f : ℕ}
    (hk : 1 ≤ k) (hf : 1 ≤ f) (hsort : L.Pairwise fun a b => w s(a.1, a.2) ≤ w s(b.1, b.2)) :
    ((ftGreedy w (2 * k - 1) f L).edgeSet.ncard : ℝ) ≤
      16 * (f : ℝ) ^ (1 - 1 / (k : ℝ)) * (Fintype.card V : ℝ) ^ (1 + 1 / (k : ℝ)) := by
  obtain ⟨B, hB, hBc⟩ := ftGreedy_exists_blockingSet (f := f) (by omega : 1 ≤ 2 * k - 1) hsort
  rw [show 2 * k - 1 + 1 = 2 * k by omega] at hB
  exact card_le_rpow_of_blockingSet hk hf hB hBc

/-- **Corollary 2 of Bodwin–Patel (EFT).** -/
theorem ftGreedyEdge_card_edges_le_rpow {w : Sym2 V → ℝ≥0} {L : List (V × V)} {k f : ℕ}
    (hk : 1 ≤ k) (hf : 1 ≤ f) (hsort : L.Pairwise fun a b => w s(a.1, a.2) ≤ w s(b.1, b.2)) :
    ((ftGreedyEdge w (2 * k - 1) f L).edgeSet.ncard : ℝ) ≤
      16 * (f : ℝ) ^ (1 - 1 / (k : ℝ)) * (Fintype.card V : ℝ) ^ (1 + 1 / (k : ℝ)) := by
  obtain ⟨B, hB, hBc⟩ :=
    ftGreedyEdge_exists_blockingSet (f := f) (by omega : 1 ≤ 2 * k - 1) hsort
  rw [show 2 * k - 1 + 1 = 2 * k by omega] at hB
  exact card_le_rpow_of_blockingSet hk hf hB hBc

end VFTSpannersOptimal
