import Papers.PODC2018.AtomicCrossChainSwaps.Pebble

/-!
# Lemma 4.13 (single leader) of Herlihy, *Atomic Cross-Chain Swaps* (PODC 2018)

With a single leader `v̂` the paper sets the timeout of an arc `(u, v)` to
`(diam(D) + D(v, v̂) + 1)·Δ`, where `D(v, v̂)` is the length of a longest path from `v` to `v̂`.
Lemma 4.13 states `D(v, v̂) ≥ D(w, v̂) + 1` for every arc `(v, w)` with `v ≠ v̂`.

* `longest D vh v`: longest *simple* path from `v` to `vh`; Lemma 4.13 holds (`lemma_4_13`), and
  hence consecutive timeouts differ by at least `Δ` (`timeout_gap`).
* `longestLax D vh v`: longest path in the paper's literal sense of §2.1 (`IsPath`: only the last
  vertex may repeat). Lemma 4.13 fails for it (`Lasso.not_lemma_4_13_lax`), on a strongly
  connected digraph on 4 vertices with single leader `0`.
-/

namespace AtomicSwap

section General

variable {V : Type*} {D : Digraph V}

/-- `D(v, v̂)` of §4.6: the length of a longest simple path from `v` to `vh` (`0` if there is
none). -/
noncomputable def longest (D : Digraph V) (vh v : V) : ℕ :=
  sSup {n | ∃ p : List V, p.Nodup ∧ p.IsChain D.Adj ∧ p.head? = some v ∧ p.getLast? = some vh ∧
    p.length = n + 1}

lemma longest_set_bdd [Fintype V] (D : Digraph V) (vh v : V) :
    BddAbove {n | ∃ p : List V, p.Nodup ∧ p.IsChain D.Adj ∧ p.head? = some v ∧
      p.getLast? = some vh ∧ p.length = n + 1} :=
  ⟨Fintype.card V, fun n ⟨p, hp, _, _, _, hl⟩ => by have := hp.length_le_card; omega⟩

lemma le_longest [Fintype V] {vh v : V} {p : List V} (hnd : p.Nodup) (hch : p.IsChain D.Adj)
    (hh : p.head? = some v) (hl : p.getLast? = some vh) : p.length - 1 ≤ longest D vh v := by
  apply le_csSup (longest_set_bdd D vh v)
  refine ⟨p, hnd, hch, hh, hl, ?_⟩
  have : p ≠ [] := by rintro rfl; simp at hh
  have : 0 < p.length := List.length_pos_iff.mpr this
  omega

/-- If `vh` is reachable from `v`, a longest simple path from `v` to `vh` exists. -/
lemma exists_longest [Fintype V] {vh v : V} (h : Reach D v vh) :
    ∃ p : List V, p.Nodup ∧ p.IsChain D.Adj ∧ p.head? = some v ∧ p.getLast? = some vh ∧
      p.length = longest D vh v + 1 := by
  apply Nat.sSup_mem _ (longest_set_bdd D vh v)
  obtain ⟨p, hnd, hch, hh, hl⟩ := h.exists_nodup
  have : p ≠ [] := by rintro rfl; simp at hh
  have : 0 < p.length := List.length_pos_iff.mpr this
  exact ⟨p.length - 1, p, hnd, hch, hh, hl, by omega⟩

/-- **Lemma 4.13** of [Herlihy, PODC 2018]: with a single leader `vh` (i.e. `{vh}` is a feedback
vertex set), for every arc `(v, w)` with `v ≠ vh` from which `vh` is reachable,
`D(v, v̂) ≥ D(w, v̂) + 1` (for longest *simple* paths). -/
theorem lemma_4_13 [Fintype V] {vh v w : V} (hL : IsFVS D {vh}) (hvw : D.Adj v w) (hv : v ≠ vh)
    (hw : Reach D w vh) : longest D vh w + 1 ≤ longest D vh v := by
  obtain ⟨p, hnd, hch, hh, hl, hlen⟩ := exists_longest hw
  have hvp : v ∉ p := by
    intro hvp
    obtain ⟨s, t, rfl⟩ := List.append_of_mem hvp
    have ht : t ≠ [] := by
      rintro rfl
      simp at hl
      exact hv hl
    have hvht : vh ∈ t := by
      rw [List.getLast?_append, List.getLast?_cons, List.getLast?_eq_some_getLast ht] at hl
      simp only [Option.getD_some, Option.some_or, Option.some.injEq] at hl
      exact hl ▸ List.getLast_mem ht
    have hnd' : vh ∉ s ++ [v] := by
      have : (s ++ [v] ++ t).Nodup := by simpa using hnd
      exact fun h => (List.nodup_append.1 this).2.2 vh h vh hvht rfl
    have hch' : (s ++ [v]).IsChain D.Adj := hch.prefix ⟨t, by simp⟩
    have hhd : (s ++ [v]).head? = some w := by
      rw [← hh]; cases s <;> simp
    have hfol : (v :: (s ++ [v])).IsChain (FollowerAdj D {vh}) := by
      refine isChain_followerAdj (hch'.cons (by simpa [hhd] using hvw)) ?_
      simp only [List.mem_cons, Set.mem_singleton_iff]
      rintro x (rfl | hx) rfl
      · exact hv rfl
      · exact hnd' hx
    exact hL v (transGen_of_isChain hfol (by simp))
  have hne : p ≠ [] := by rintro rfl; simp at hh
  have hl' : (v :: p).getLast? = some vh := by rw [List.getLast?_cons, hl]; rfl
  have := le_longest (D := D) (p := v :: p) (List.nodup_cons.2 ⟨hvp, hnd⟩)
    (hch.cons (by simpa [hh] using hvw)) rfl hl'
  simp only [List.length_cons] at this
  omega

/-- The single-leader timeout (in units of `Δ`) of the arc `(u, v)`: `B + D(v, v̂) + 1`
(§4.6 of the paper, with `B = diam D`). -/
noncomputable def slTimeout (D : Digraph V) (vh : V) (B : ℕ) (_u v : V) : ℕ :=
  B + longest D vh v + 1

/-- Consequence of **Lemma 4.13** of [Herlihy, PODC 2018]: the single-leader timeout of an arc
`(u, v)` entering a follower `v` is at least one `Δ` later than that of any arc `(v, w)` leaving
`v`. -/
theorem timeout_gap [Fintype V] {vh u v w : V} (B : ℕ) (hL : IsFVS D {vh}) (hvw : D.Adj v w)
    (hv : v ≠ vh) (hw : Reach D w vh) : slTimeout D vh B v w + 1 ≤ slTimeout D vh B u v := by
  have := lemma_4_13 hL hvw hv hw
  simp only [slTimeout]
  omega

/-- `D(v, v̂)` read literally with the paper's path notion `IsPath` of §2.1 (only `u₀, …, u_{ℓ-1}`
distinct): the length of a longest such path from `v` to `vh`. -/
noncomputable def longestLax (D : Digraph V) (vh v : V) : ℕ :=
  sSup {n | ∃ p : List V, IsPath D p ∧ p.head? = some v ∧ p.getLast? = some vh ∧
    p.length = n + 1}

lemma longestLax_set_bdd [Fintype V] (D : Digraph V) (vh v : V) :
    BddAbove {n | ∃ p : List V, IsPath D p ∧ p.head? = some v ∧ p.getLast? = some vh ∧
      p.length = n + 1} :=
  ⟨Fintype.card V, fun n ⟨p, hp, _, _, hl⟩ => by have := hp.length_le; omega⟩

/-- `longestLax` is determined by a witness and an upper bound. -/
lemma longestLax_eq [Fintype V] {vh v : V} {n : ℕ} {p : List V} (hp : IsPath D p)
    (hh : p.head? = some v) (hl : p.getLast? = some vh) (hlen : p.length = n + 1)
    (hmax : ∀ q : List V, IsPath D q → q.head? = some v → q.getLast? = some vh →
      q.length ≤ n + 1) : longestLax D vh v = n := by
  apply le_antisymm
  · apply csSup_le
    · exact ⟨n, p, hp, hh, hl, hlen⟩
    rintro m ⟨q, hq, hqh, hql, hqlen⟩
    have := hmax q hq hqh hql
    omega
  · exact le_csSup (longestLax_set_bdd D vh v) ⟨p, hp, hh, hl, hlen⟩

end General

namespace Lasso

/-- The counterexample digraph on `Fin 4`: arcs `0→1, 1→2, 2→0, 1→3, 3→0`; single leader `0`. -/
def G : Digraph (Fin 4) where
  Adj a b := (a, b) ∈ ({(0, 1), (1, 2), (2, 0), (1, 3), (3, 0)} : Finset (Fin 4 × Fin 4))

instance : DecidableRel G.Adj := fun a b =>
  inferInstanceAs (Decidable ((a, b) ∈ ({(0, 1), (1, 2), (2, 0), (1, 3), (3, 0)} : Finset _)))

lemma reach_zero (v : Fin 4) : Reach G v 0 := by
  have a01 : G.Adj 0 1 := by decide
  have a12 : G.Adj 1 2 := by decide
  have a20 : G.Adj 2 0 := by decide
  have a30 : G.Adj 3 0 := by decide
  fin_cases v
  · exact .refl
  · exact .head a12 (.single a20)
  · exact .single a20
  · exact .single a30

lemma zero_reach (v : Fin 4) : Reach G 0 v := by
  have a01 : G.Adj 0 1 := by decide
  have a12 : G.Adj 1 2 := by decide
  have a13 : G.Adj 1 3 := by decide
  fin_cases v
  · exact .refl
  · exact .single a01
  · exact .head a01 (.single a12)
  · exact .head a01 (.single a13)

/-- The counterexample digraph is strongly connected. -/
theorem stronglyConnected : StronglyConnected G :=
  fun u v => (reach_zero u).trans (zero_reach v)

/-- `{0}` is a feedback vertex set: the follower arcs `1→2, 1→3` form no cycle. -/
theorem isFVS : IsFVS G {0} := by
  let f : Fin 4 → ℕ := ![0, 0, 1, 1]
  have hf : ∀ a b, FollowerAdj G {0} a b → f a < f b := by
    rintro a b ⟨h, ha, hb⟩
    simp only [Set.mem_singleton_iff] at ha hb
    revert a b
    decide
  have key : ∀ a b, Relation.TransGen (FollowerAdj G {0}) a b → f a < f b := by
    intro a b h
    induction h with
    | single h => exact hf _ _ h
    | tail _ h ih => exact ih.trans (hf _ _ h)
  exact fun v hv => lt_irrefl _ (key v v hv)

/-- The lasso `(2, 0, 1, 3, 0)` is a path in the paper's sense, so `G(2, 0) = 4`. -/
theorem longestLax_two : longestLax G 0 2 = 4 := by
  refine longestLax_eq (p := [2, 0, 1, 3, 0]) (by decide) rfl rfl rfl fun q hq _ _ => ?_
  simpa using hq.length_le

/-- From `1` the longest paths in the paper's sense to `0` are `(1, 2, 0)` and `(1, 3, 0)`. -/
theorem longestLax_one : longestLax G 0 1 = 2 := by
  refine longestLax_eq (p := [1, 2, 0]) (by decide) rfl rfl rfl fun q hq hh hl => ?_
  have h5 := hq.length_le
  simp only [Fintype.card_fin] at h5
  rcases q with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | ⟨e, _ | ⟨f, q⟩⟩⟩⟩⟩⟩ <;>
    simp only [List.length_cons, List.length_nil, List.head?_cons, Option.some.injEq] at h5 hh ⊢
  all_goals first
    | omega
    | (subst hh; revert hq hl; revert b c d; decide)
    | (subst hh; revert hq hl; revert b c d e; decide)

/-- **Lemma 4.13 fails for the paper's literal path notion**: on the strongly connected digraph
`G` with single leader `0` (a feedback vertex set) and the arc `(1, 2)` leaving the follower `1`,
`G(1, 0) ≥ G(2, 0) + 1` is false when `G(·, ·)` measures paths in the sense of §2.1. -/
theorem not_lemma_4_13_lax : StronglyConnected G ∧ IsFVS G {0} ∧ G.Adj 1 2 ∧ (1 : Fin 4) ≠ 0 ∧
    ¬ (longestLax G 0 2 + 1 ≤ longestLax G 0 1) := by
  refine ⟨stronglyConnected, isFVS, by decide, by decide, ?_⟩
  rw [longestLax_two, longestLax_one]
  omega

end Lasso

end AtomicSwap
