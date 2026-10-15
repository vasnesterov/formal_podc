import Papers.PODC2020.FaultTolerantSpanners.LBC

/-!
# Algorithm 3: the modified greedy algorithm (Section 3.2 of Dinitz–Robelle, PODC'20)

The edges of `G` are given as a list `L` of ordered pairs (`(u, v)` stands for the edge `{u, v}`),
in arbitrary order; every edge of `G` must occur in `L` (in at least one orientation) and every
entry of `L` must be an edge of `G`. Starting from the empty graph, the algorithm scans `L` and adds
the edge `(u, v)` to the current graph `H` iff a decision procedure `dec H u v` answers YES.

* `greedy dec L` — the generic greedy scheme; the list of added edges is `greedyList dec L`
  (in insertion order).
* `modifiedGreedy O k f L` — **Algorithm 3**: `dec H u v := lbc O H u v (2k - 1) f` (Algorithm 2
  with `t = 2k - 1`, `α = f`, run on the current `H`, unweighted).
* `modifiedGreedyEdge O k f L` — the EFT variant (edge version of Algorithm 2).

Main results: `greedy_isVFTSpanner` / `greedy_isEFTSpanner` (correctness for any decision procedure
that answers NO only when no small fault set separates `u, v`), and **Theorem 5**
`modifiedGreedy_isVFTSpanner` (plus `modifiedGreedyEdge_isEFTSpanner`).
-/

open Finset SimpleGraph

namespace FaultTolerantSpanners

variable {V : Type*}

/-! ### Graphs given by edge lists -/

/-- The graph whose edges are the pairs of `A` (loops are dropped). -/
def edgeGraph (A : List (V × V)) : SimpleGraph V :=
  fromEdgeSet {e | ∃ p ∈ A, s(p.1, p.2) = e}

lemma edgeGraph_adj {A : List (V × V)} {u v : V} :
    (edgeGraph A).Adj u v ↔ u ≠ v ∧ ∃ p ∈ A, s(p.1, p.2) = s(u, v) := by
  simp [edgeGraph, and_comm]

lemma mem_edgeSet_edgeGraph {A : List (V × V)} {e : Sym2 V} :
    e ∈ (edgeGraph A).edgeSet ↔ (∃ p ∈ A, s(p.1, p.2) = e) ∧ ¬ e.IsDiag := by
  simp [edgeGraph]

lemma edgeGraph_mono {A A' : List (V × V)} (h : ∀ x ∈ A, x ∈ A') : edgeGraph A ≤ edgeGraph A' := by
  intro u v huv
  rw [edgeGraph_adj] at huv ⊢
  obtain ⟨hne, p, hp, hpe⟩ := huv
  exact ⟨hne, p, h p hp, hpe⟩

lemma edgeGraph_le {G : SimpleGraph V} {A : List (V × V)} (h : ∀ p ∈ A, G.Adj p.1 p.2) :
    edgeGraph A ≤ G := by
  intro u v huv
  rw [edgeGraph_adj] at huv
  obtain ⟨-, p, hp, hpe⟩ := huv
  have := h p hp
  rw [← mem_edgeSet, hpe] at this
  exact this

lemma edgeGraph_adj_of_mem {A : List (V × V)} {p : V × V} (hp : p ∈ A) (hne : p.1 ≠ p.2) :
    (edgeGraph A).Adj p.1 p.2 :=
  edgeGraph_adj.mpr ⟨hne, p, hp, rfl⟩

/-! ### The generic greedy scheme -/

/-- One step of the greedy scheme: add `e` iff `dec` answers YES on the current graph. -/
def greedyStep (dec : SimpleGraph V → V → V → Bool) (A : List (V × V)) (e : V × V) :
    List (V × V) :=
  if dec (edgeGraph A) e.1 e.2 then A ++ [e] else A

/-- The list of edges added by the greedy scheme, in insertion order. -/
def greedyList (dec : SimpleGraph V → V → V → Bool) (L : List (V × V)) : List (V × V) :=
  L.foldl (greedyStep dec) []

/-- The output of the greedy scheme. -/
def greedy (dec : SimpleGraph V → V → V → Bool) (L : List (V × V)) : SimpleGraph V :=
  edgeGraph (greedyList dec L)

variable {dec : SimpleGraph V → V → V → Bool}

lemma prefix_foldl_greedyStep : ∀ (l A : List (V × V)), A <+: l.foldl (greedyStep dec) A
  | [], _ => List.prefix_refl _
  | e :: l, A => by
    rw [List.foldl_cons]
    refine List.IsPrefix.trans ?_ (prefix_foldl_greedyStep l _)
    unfold greedyStep
    split_ifs
    · exact List.prefix_append _ _
    · exact List.prefix_refl _

lemma mem_foldl_greedyStep : ∀ (l A : List (V × V)) x, x ∈ l.foldl (greedyStep dec) A →
    x ∈ A ∨ x ∈ l
  | [], _, _, h => Or.inl h
  | e :: l, A, x, h => by
    rw [List.foldl_cons] at h
    rcases mem_foldl_greedyStep l _ x h with h | h
    · unfold greedyStep at h
      split_ifs at h
      · rcases List.mem_append.mp h with h | h
        · exact Or.inl h
        · exact Or.inr (by simp at h; simp [h])
      · exact Or.inl h
    · exact Or.inr (List.mem_cons_of_mem _ h)

lemma mem_of_mem_greedyList {L : List (V × V)} {x : V × V} (h : x ∈ greedyList dec L) : x ∈ L := by
  rcases mem_foldl_greedyStep L [] x h with h | h
  · simp at h
  · exact h

lemma greedyList_take_prefix (L : List (V × V)) (i : ℕ) :
    greedyList dec (L.take i) <+: greedyList dec L := by
  conv_rhs => rw [← List.take_append_drop i L]
  rw [greedyList, greedyList, List.foldl_append]
  exact prefix_foldl_greedyStep _ _

lemma greedyList_take_succ (L : List (V × V)) {i : ℕ} (hi : i < L.length) :
    greedyList dec (L.take (i + 1)) = greedyStep dec (greedyList dec (L.take i)) L[i] := by
  rw [greedyList, greedyList, List.take_succ_eq_append_getElem hi, List.foldl_append]
  rfl

/-- Invariant: each added edge was accepted by `dec` on the graph of the edges added before it. -/
def GreedyGood (dec : SimpleGraph V → V → V → Bool) (A : List (V × V)) : Prop :=
  ∀ i (h : i < A.length), dec (edgeGraph (A.take i)) A[i].1 A[i].2 = true

lemma greedyGood_foldl : ∀ (l A : List (V × V)), GreedyGood dec A →
    GreedyGood dec (l.foldl (greedyStep dec) A)
  | [], _, h => h
  | e :: l, A, h => by
    rw [List.foldl_cons]
    apply greedyGood_foldl l
    unfold greedyStep
    split_ifs with he
    · intro i hi
      rw [List.length_append, List.length_singleton] at hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
      · have h1 : (A ++ [e]).take i = A.take i := List.take_append_of_le_length hi.le
        simp only [h1, List.getElem_append_left hi]
        exact h i hi
      · simpa using he
    · exact h

lemma greedyGood_greedyList (L : List (V × V)) : GreedyGood dec (greedyList dec L) :=
  greedyGood_foldl L [] (fun i h => by simp at h)

/-- Key property of the scan: each `(u, v) ∈ L` is either added, or rejected by `dec` on a graph
`edgeGraph A'` whose edges were added before it (in particular `edgeGraph A' ≤ greedy dec L`). -/
lemma greedy_mem_or_reject (L : List (V × V)) {p : V × V} (hp : p ∈ L) :
    p ∈ greedyList dec L ∨ ∃ i, i < L.length ∧ L[i]? = some p ∧
      dec (edgeGraph (greedyList dec (L.take i))) p.1 p.2 = false := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hp
  cases hdec : dec (edgeGraph (greedyList dec (L.take i))) L[i].1 L[i].2 with
  | false => exact Or.inr ⟨i, hi, by simp [hi], hdec⟩
  | true =>
    left
    have h1 := greedyList_take_succ (dec := dec) L hi
    simp only [greedyStep, hdec, ↓reduceIte] at h1
    have h2 := (greedyList_take_prefix (dec := dec) L (i + 1)).subset
    rw [h1] at h2
    exact h2 (by simp)

lemma edgeGraph_take_le_greedy (L : List (V × V)) (i : ℕ) :
    edgeGraph (greedyList dec (L.take i)) ≤ greedy dec L :=
  edgeGraph_mono fun _ hx => (greedyList_take_prefix L i).subset hx

lemma greedy_le {G : SimpleGraph V} {L : List (V × V)} (hLG : ∀ p ∈ L, G.Adj p.1 p.2) :
    greedy dec L ≤ G :=
  edgeGraph_le fun p hp => hLG p (mem_of_mem_greedyList hp)

/-- **Correctness of the greedy scheme (vertex faults).** If `dec H u v` answers NO only when
`d_{H \ F}(u, v) ≤ t` for every fault set `F ∌ u, v` with `|F| ≤ f`, then the greedy output is an
`f`-VFT `t`-spanner. -/
theorem greedy_isVFTSpanner {G : SimpleGraph V} {L : List (V × V)} {f t : ℕ} (ht : 1 ≤ t)
    (hdec : ∀ H u v, dec H u v = false → ∀ F : Finset V, #F ≤ f → u ∉ F → v ∉ F →
      (H.deleteVerts F).edist u v ≤ t)
    (hLG : ∀ p ∈ L, G.Adj p.1 p.2) (hL : ∀ u v, G.Adj u v → (u, v) ∈ L ∨ (v, u) ∈ L) :
    IsVFTSpanner G (greedy dec L) f t := by
  rw [isVFTSpanner_iff ht (greedy_le hLG)]
  intro F hF u v huv hu hv
  have key : ∀ p ∈ L, p.1 ∉ F → p.2 ∉ F → ((greedy dec L).deleteVerts F).edist p.1 p.2 ≤ t := by
    intro p hp h1 h2
    rcases greedy_mem_or_reject L hp with hmem | ⟨i, hi, -, hrej⟩
    · have hadj : ((greedy dec L).deleteVerts F).Adj p.1 p.2 :=
        ⟨edgeGraph_adj_of_mem hmem (hLG p hp).ne, h1, h2⟩
      rw [← edist_eq_one_iff_adj] at hadj
      rw [hadj]; exact_mod_cast ht
    · exact (edist_anti (deleteVerts_mono (edgeGraph_take_le_greedy L i))).trans
        (hdec _ _ _ hrej F hF h1 h2)
  rcases hL u v huv with h | h
  · exact key _ h hu hv
  · rw [edist_comm]; exact key _ h hv hu

/-- **Correctness of the greedy scheme (edge faults).** -/
theorem greedy_isEFTSpanner {G : SimpleGraph V} {L : List (V × V)} {f t : ℕ} (ht : 1 ≤ t)
    (hdec : ∀ H u v, dec H u v = false → ∀ F : Finset (Sym2 V), #F ≤ f →
      (H.deleteEdges F).edist u v ≤ t)
    (hLG : ∀ p ∈ L, G.Adj p.1 p.2) (hL : ∀ u v, G.Adj u v → (u, v) ∈ L ∨ (v, u) ∈ L) :
    IsEFTSpanner G (greedy dec L) f t := by
  rw [isEFTSpanner_iff ht (greedy_le hLG)]
  intro F hF u v huv huvF
  have key : ∀ p ∈ L, s(p.1, p.2) ∉ F →
      ((greedy dec L).deleteEdges F).edist p.1 p.2 ≤ t := by
    intro p hp hpF
    rcases greedy_mem_or_reject L hp with hmem | ⟨i, hi, -, hrej⟩
    · have hadj : ((greedy dec L).deleteEdges F).Adj p.1 p.2 := by
        rw [deleteEdges_adj]
        exact ⟨edgeGraph_adj_of_mem hmem (hLG p hp).ne, by simpa using hpF⟩
      rw [← edist_eq_one_iff_adj] at hadj
      rw [hadj]; exact_mod_cast ht
    · exact (edist_anti (deleteEdges_mono (edgeGraph_take_le_greedy L i))).trans
        (hdec _ _ _ hrej F hF)
  rcases hL u v huv with h | h
  · exact key _ h huvF
  · rw [edist_comm]; exact key _ h (by rwa [Sym2.eq_swap])

/-! ### Algorithm 3 -/

variable [DecidableEq V]

/-- **Algorithm 3** (modified greedy, vertex faults): scan `L`, adding `(u, v)` iff Algorithm 2 with
`t = 2k - 1`, `α = f` answers YES on the current graph. -/
def modifiedGreedy (O : ShortPathOracle V) (k f : ℕ) (L : List (V × V)) : SimpleGraph V :=
  greedy (fun H u v => lbc O H u v (2 * k - 1) f) L

/-- Algorithm 3 for edge faults (using the edge version of Algorithm 2). -/
def modifiedGreedyEdge (O : ShortPathOracle V) (k f : ℕ) (L : List (V × V)) : SimpleGraph V :=
  greedy (fun H u v => lbcEdge O H u v (2 * k - 1) f) L

variable [Fintype V]

/-- **Theorem 5 of Dinitz–Robelle.** For every correct BFS oracle and every order `L` of the edges,
Algorithm 3 returns an `f`-VFT `(2k - 1)`-spanner of `G`. -/
theorem modifiedGreedy_isVFTSpanner {O : ShortPathOracle V} (hO : O.Spec) {G : SimpleGraph V}
    {L : List (V × V)} {k f : ℕ} (hk : 1 ≤ k)
    (hLG : ∀ p ∈ L, G.Adj p.1 p.2) (hL : ∀ u v, G.Adj u v → (u, v) ∈ L ∨ (v, u) ∈ L) :
    IsVFTSpanner G (modifiedGreedy O k f L) f (2 * k - 1) := by
  refine greedy_isVFTSpanner (by omega) ?_ hLG hL
  intro H u v hno F hF hu hv
  by_contra hlt
  rw [not_le] at hlt
  have := lbc_eq_true_of_isLengthCut hO ⟨hu, hv, hlt⟩ hF
  simp [this] at hno

/-- **Theorem 5, edge version**: Algorithm 3 with the edge version of Algorithm 2 returns an
`f`-EFT `(2k - 1)`-spanner. -/
theorem modifiedGreedyEdge_isEFTSpanner {O : ShortPathOracle V} (hO : O.Spec)
    {G : SimpleGraph V} {L : List (V × V)} {k f : ℕ} (hk : 1 ≤ k)
    (hLG : ∀ p ∈ L, G.Adj p.1 p.2) (hL : ∀ u v, G.Adj u v → (u, v) ∈ L ∨ (v, u) ∈ L) :
    IsEFTSpanner G (modifiedGreedyEdge O k f L) f (2 * k - 1) := by
  refine greedy_isEFTSpanner (by omega) ?_ hLG hL
  intro H u v hno F hF
  by_contra hlt
  rw [not_le] at hlt
  have := (lbcEdge_correct hO H u v (2 * k - 1) f).1 ⟨F, hlt, hF⟩
  simp [this] at hno

end FaultTolerantSpanners
