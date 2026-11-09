import Papers.PODC2016.BCCConnectivitySketches.Model
import Cslib.Foundations.Combinatorics.SimpleGraph.Girth
import Cslib.Foundations.Combinatorics.SimpleGraph.Cycle

-- CSLib candidate: `proposition_1` (cycle-max deletion preserves components), `proposition_2` (girth ⇒ degeneracy)

/-!
# Removing the heaviest edge of every short cycle (Propositions 1 and 2)

Montealegre–Todinca, *Deterministic graph connectivity in the broadcast congested clique*
(PODC 2016 BA; arXiv:1602.04095v3), Section 3.

Fix a graph `G`, `r > 0` and a total order of the edges, given by an injective weight
`w : Sym2 V → ℕ`. For every cycle of length `≤ 2r` pick its `w`-maximal edge (`IsHeavy`) and delete
all picked edges: this is `prunedGraph G r w` (the paper's `G̃`).

* `proposition_1`: `G̃` has the same connected components as `G`; hence (`connected_iff`,
  `IsSpanningForest.of_prunedGraph`) `G` is connected iff `G̃` is, and every spanning forest of
  `G̃` is one of `G`. Injectivity of `w` (a *total* order) is essential: with ties, a triangle whose
  three edges have equal weight loses all three edges.
* `prunedGraph_noShortCycles`: `G̃` has no cycle of length `≤ 2r`.
* `proposition_2` (corrected): a graph with no cycle of length `≤ 2r` (girth `> 2r`) on
  `n ≤ s ^ r` vertices is `s`-degenerate, i.e. `O(n^{1/r})`-degenerate. The paper states girth
  `≥ 2r`, which is false: `proposition_2_false` (for `r = 2`, `K_{m,m}` has girth `4` and is not
  `(m-1)`-degenerate).
* `ball`, `localView`, `isHeavy_localView_iff`: whether an edge at `v` is heavy can be decided by
  `v` from the subgraph spanned by its `r`-ball (the local computation in Theorem 3).
-/

namespace Podc.BCCConnectivitySketches

open SimpleGraph Finset

variable {V : Type*}

/-- `e` is the `w`-maximal edge of some cycle of `G` of length `≤ 2r`. -/
def IsHeavy (G : SimpleGraph V) (r : ℕ) (w : Sym2 V → ℕ) (e : Sym2 V) : Prop :=
  ∃ (a : V) (c : G.Walk a a), c.IsCycle ∧ c.length ≤ 2 * r ∧ e ∈ c.edges ∧ ∀ f ∈ c.edges, w f ≤ w e

/-- The paper's `G̃ = (V, E − Ẽ)`: delete the maximal edge of every cycle of length `≤ 2r`. -/
def prunedGraph (G : SimpleGraph V) (r : ℕ) (w : Sym2 V → ℕ) : SimpleGraph V :=
  G.deleteEdges {e | IsHeavy G r w e}

variable {G : SimpleGraph V} {r : ℕ} {w : Sym2 V → ℕ}

theorem prunedGraph_le : prunedGraph G r w ≤ G := G.deleteEdges_le _

/-- If every edge of a `G`-walk joins two `H`-reachable vertices, so do its endpoints. -/
lemma reachable_of_walk {H : SimpleGraph V} {x y : V} (p : G.Walk x y)
    (h : ∀ a b, s(a, b) ∈ p.edges → H.Reachable a b) : H.Reachable x y := by
  induction p with
  | nil => rfl
  | cons hadj q ih =>
    exact (h _ _ (by simp)).trans (ih fun a b hab => h a b (by simp [hab]))

/-- The endpoints of every edge of `G` are connected in `G̃` (strong induction on the weight). -/
lemma prunedGraph_reachable_of_adj (hw : Function.Injective w) {a b : V} (hab : G.Adj a b) :
    (prunedGraph G r w).Reachable a b := by
  suffices H : ∀ n, ∀ a b, G.Adj a b → w s(a, b) = n → (prunedGraph G r w).Reachable a b from
    H _ a b hab rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro a b hab hn
  by_cases hh : IsHeavy G r w s(a, b)
  · obtain ⟨x, c, hc, -, he, hmax⟩ := hh
    obtain ⟨p, -, hpe, -, -⟩ := hc.exists_path_of_mem_edges he
    refine reachable_of_walk p fun a' b' he' => ?_
    obtain ⟨h1, h2⟩ := hpe _ he'
    have hlt : w s(a', b') < n := by
      rw [← hn]
      exact lt_of_le_of_ne (hmax _ h1) fun h => h2 (hw h)
    exact ih _ hlt a' b' (c.adj_of_mem_edges h1) rfl
  · exact Adj.reachable (by simp [prunedGraph, hab, hh])

/-- **Proposition 1** of [Montealegre–Todinca] (after Awerbuch et al.): `G̃` has the same connected
components as `G` (for a total order of the edges, `w` injective). -/
theorem proposition_1 (hw : Function.Injective w) (u v : V) :
    (prunedGraph G r w).Reachable u v ↔ G.Reachable u v := by
  refine ⟨fun h => h.mono prunedGraph_le, fun ⟨p⟩ => reachable_of_walk p fun a b hab => ?_⟩
  exact prunedGraph_reachable_of_adj hw (p.adj_of_mem_edges hab)

/-- **Proposition 1**, first part: `G` is connected iff `G̃` is. -/
theorem connected_iff (hw : Function.Injective w) :
    (prunedGraph G r w).Connected ↔ G.Connected := by
  simp only [connected_iff_exists_forall_reachable, proposition_1 hw]

/-- **Proposition 1**, second part: every spanning forest of `G̃` is a spanning forest of `G`. -/
theorem IsSpanningForest.of_prunedGraph (hw : Function.Injective w) {F : SimpleGraph V}
    (hF : IsSpanningForest (prunedGraph G r w) F) : IsSpanningForest G F :=
  hF.of_le prunedGraph_le (proposition_1 hw)

/-- `G̃` has no cycle of length `≤ 2r` (does not even need `w` injective). -/
theorem prunedGraph_noShortCycles : (prunedGraph G r w).NoShortCycles (2 * r) := by
  classical
  intro x c hc
  by_contra hlen
  push Not at hlen
  have hne : c.edges.toFinset.Nonempty := by
    obtain ⟨d, hd⟩ := List.exists_mem_of_ne_nil c.edges (by
      intro h
      have := hc.three_le_length
      rw [← Walk.length_edges, h] at this
      simp at this)
    exact ⟨d, List.mem_toFinset.mpr hd⟩
  obtain ⟨e, he, hmax⟩ := c.edges.toFinset.exists_max_image w hne
  rw [List.mem_toFinset] at he
  have hheavy : IsHeavy G r w e := by
    refine ⟨x, c.mapLe prunedGraph_le, hc.mapLe _, by simpa using hlen, ?_, ?_⟩
    · rwa [Walk.edges_mapLe_eq_edges]
    · intro f hf
      rw [Walk.edges_mapLe_eq_edges] at hf
      exact hmax f (List.mem_toFinset.mpr hf)
  have := c.edges_subset_edgeSet he
  simp only [prunedGraph, edgeSet_deleteEdges, Set.mem_sdiff, Set.mem_ofPred_eq] at this
  exact this.2 hheavy

/-- **Proposition 2** of [Montealegre–Todinca] (after Drucker–Kuhn–Oshman), corrected: a graph
with no cycle of length `≤ 2r` (girth `> 2r`; the paper says `≥ 2r`, see `proposition_2_false`) on
`n ≤ s ^ r` vertices is `s`-degenerate; with `s = ⌈n^{1/r}⌉` this is `O(n^{1/r})`. -/
theorem proposition_2 [Fintype V] [DecidableRel G.Adj] (hr : 1 ≤ r) (h : G.NoShortCycles (2 * r)) (s : ℕ)
    (hs : Fintype.card V ≤ s ^ r) : Podc.CongestedCliquePower.IsDegenerate G s := by
  classical
  intro S hS
  by_contra hcon
  push Not at hcon
  obtain ⟨v, hv⟩ := hS
  let H : SimpleGraph V :=
    { Adj := fun a b => G.Adj a b ∧ a ∈ S ∧ b ∈ S
      symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩
      loopless := ⟨fun _ h => G.irrefl h.1⟩ }
  have hHG : H ≤ G := fun a b h => h.1
  have hdeg : ∀ x ∈ S, s < H.degree x := by
    intro x hx
    rw [← card_neighborFinset_eq_degree]
    convert hcon x hx using 2
    ext y
    simp [H, hx, and_comm]
  have := (h.anti hHG).pow_lt_card hr S (fun a b hab => hab.2.1) hdeg hv
  have := S.card_le_univ
  omega

/-! ### Local computability of heavy edges -/

/-- The vertices at distance `≤ r` from `v`. -/
def ball (G : SimpleGraph V) (r : ℕ) (v : V) : Set V := {u | ∃ p : G.Walk v u, p.length ≤ r}

/-- What node `v` sees after `r` rounds of flooding: the edges of `G` between vertices of its
`r`-ball. -/
def localView (G : SimpleGraph V) (r : ℕ) (v : V) : SimpleGraph V where
  Adj a b := G.Adj a b ∧ a ∈ ball G r v ∧ b ∈ ball G r v
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩
  loopless := ⟨fun _ h => G.irrefl h.1⟩

variable {v : V}

theorem localView_le : localView G r v ≤ G := fun _ _ h => h.1

theorem localView_adj_iff (hr : 1 ≤ r) {u : V} : (localView G r v).Adj v u ↔ G.Adj v u := by
  refine ⟨fun h => h.1, fun h => ⟨h, ⟨Walk.nil, by simp⟩, ⟨h.toWalk, by simpa using hr⟩⟩⟩

/-- Every vertex of a cycle of length `≤ 2r` through `v` is in the `r`-ball of `v`. -/
lemma mem_ball_of_mem_support {c : G.Walk v v} (hlen : c.length ≤ 2 * r) {y : V}
    (hy : y ∈ c.support) : y ∈ ball G r v := by
  classical
  have hsum := congrArg Walk.length (c.take_spec hy)
  rw [Walk.length_append] at hsum
  by_cases h1 : (c.takeUntil y hy).length ≤ r
  · exact ⟨_, h1⟩
  · refine ⟨(c.dropUntil y hy).reverse, ?_⟩
    rw [Walk.length_reverse]
    omega

/-- Whether an edge at `v` is heavy (the maximal edge of a cycle of length `≤ 2r`) can be decided
from the `r`-ball of `v`: this is the local computation of node `v` in Theorem 3. -/
theorem isHeavy_localView_iff {e : Sym2 V} (hv : v ∈ e) :
    IsHeavy (localView G r v) r w e ↔ IsHeavy G r w e := by
  constructor
  · rintro ⟨a, c, hc, hlen, he, hmax⟩
    refine ⟨a, c.mapLe localView_le, hc.mapLe _, by simpa using hlen, ?_, ?_⟩
    · rwa [Walk.edges_mapLe_eq_edges]
    · intro f hf
      rw [Walk.edges_mapLe_eq_edges] at hf
      exact hmax f hf
  · rintro ⟨a, c, hc, hlen, he, hmax⟩
    classical
    obtain ⟨x, rfl⟩ := Sym2.mem_iff_exists.mp hv
    have hvs : v ∈ c.support := c.fst_mem_support_of_mem_edges he
    set c' := c.rotate v hvs with hc'
    have hedges : ∀ f, f ∈ c'.edges ↔ f ∈ c.edges := fun f => (c.rotate_edges v hvs).mem_iff
    have hlen' : c'.length ≤ 2 * r := by simpa [c'] using hlen
    have hsub : ∀ f ∈ c'.edges, f ∈ (localView G r v).edgeSet := by
      intro f hf
      induction f using Sym2.ind with
      | _ y z =>
      exact ⟨c'.adj_of_mem_edges hf,
        mem_ball_of_mem_support hlen' (c'.fst_mem_support_of_mem_edges hf),
        mem_ball_of_mem_support hlen' (c'.snd_mem_support_of_mem_edges hf)⟩
    refine ⟨v, c'.transfer _ hsub, (hc.rotate hvs).transfer hsub, by simpa using hlen', ?_, ?_⟩
    · rw [Walk.edges_transfer, hedges]; exact he
    · intro f hf
      rw [Walk.edges_transfer, hedges] at hf
      exact hmax f hf

/-! ### Proposition 2 as printed (girth `≥ 2r`) is false -/

/-- `K_{m,m}` has no triangle (girth `4 = 2r` for `r = 2`): all its closed walks have even
length. -/
lemma completeBipartite_noShortCycles (m : ℕ) :
    (completeBipartiteGraph (Fin m) (Fin m)).NoShortCycles 3 := by
  intro x c hc
  have h3 := hc.three_le_length
  obtain ⟨k, hk⟩ :=
    ((CompleteBipartiteGraph.bicoloring (Fin m) (Fin m)).even_length_iff_congr c).mpr Iff.rfl
  omega

/-- Every vertex of `K_{m,m}` has `m` neighbours. -/
lemma card_filter_completeBipartite_adj (m : ℕ)
    [DecidableRel (completeBipartiteGraph (Fin m) (Fin m)).Adj] (x : Fin m ⊕ Fin m) :
    (univ.filter ((completeBipartiteGraph (Fin m) (Fin m)).Adj x)).card = m := by
  rw [Finset.card_filter, Fintype.sum_sum_type]
  rcases x with x | x <;> simp

/-- For `m > 2C²`, `C · √(2m) < m`. -/
lemma mul_sqrt_lt (C : ℝ) (m : ℕ) (hm : 2 * C ^ 2 < m) :
    C * ((m + m : ℕ) : ℝ) ^ ((1 : ℝ) / 2) < m := by
  rw [← Real.sqrt_eq_rpow]
  set t := √((m + m : ℕ) : ℝ) with ht
  have ht0 : 0 ≤ t := Real.sqrt_nonneg _
  have htt : t ^ 2 = 2 * m := by
    rw [ht, Real.sq_sqrt (by positivity)]; push_cast; ring
  have hm0 : (0 : ℝ) < m := lt_of_le_of_lt (by positivity) hm
  rcases le_or_gt C 0 with hC | hC
  · nlinarith
  · have h2C : 2 * C < t := by
      rw [ht, Real.lt_sqrt (by positivity)]; push_cast; nlinarith
    nlinarith

/-- **Proposition 2 as stated** (girth `≥ 2r` ⇒ `O(n^{1/r})`-degenerate) is false for `r = 2`:
`K_{m,m}` (`n = 2m` vertices) has girth `4 ≥ 2r` but every vertex has degree `m`, and
`m > C·√(2m)` for large `m`. The hypothesis "girth `≥ 4`" is `NoShortCycles 3`. -/
theorem proposition_2_false : ¬ ∃ (C : ℝ) (n₀ : ℕ), ∀ (W : Type) [Fintype W] [DecidableEq W]
    (G : SimpleGraph W) [DecidableRel G.Adj], n₀ ≤ Fintype.card W → G.NoShortCycles (2 * 2 - 1) →
    Podc.CongestedCliquePower.IsDegenerate G ⌊C * (Fintype.card W : ℝ) ^ ((1 : ℝ) / 2)⌋₊ := by
  classical
  rintro ⟨C, n₀, h⟩
  set m := n₀ + ⌈2 * C ^ 2⌉₊ + 1 with hm
  obtain ⟨x, -, hx⟩ := h (Fin m ⊕ Fin m) (completeBipartiteGraph (Fin m) (Fin m))
    (by simp; omega) (completeBipartite_noShortCycles m) univ ⟨Sum.inl ⟨0, by omega⟩, mem_univ _⟩
  rw [card_filter_completeBipartite_adj, Fintype.card_sum, Fintype.card_fin] at hx
  have hC : 2 * C ^ 2 < m := by
    have := Nat.le_ceil (2 * C ^ 2)
    have : (⌈2 * C ^ 2⌉₊ : ℝ) + 1 ≤ m := by
      rw [hm]; push_cast; linarith [(n₀.cast_nonneg : (0 : ℝ) ≤ n₀)]
    linarith
  have := (Nat.floor_lt' (by omega)).mpr (mul_sqrt_lt C m hC)
  omega

end Podc.BCCConnectivitySketches
