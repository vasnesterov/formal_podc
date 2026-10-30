import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Sum
import Mathlib.Tactic

-- CSLib candidate: Cslib/Foundations/Combinatorics/SimpleGraph/HubLabeling.lean

/-!
# Hub labelings (2-hop covers)

A *hub labeling* of a graph `G` assigns to every vertex `v` a set of hubs `S v` such that every pair
`u, v` has a common hub `w ∈ S u ∩ S v` on a shortest `u`–`v` path
(Cohen–Halperin–Kaplan–Zwick 2003). Distances are then decoded as
`min_{w ∈ S u ∩ S v} d(u, w) + d(w, v)`.

## Main definitions

* `SimpleGraph.IsHubLabeling G S`: for every *reachable* pair `u, v` there is
  `w ∈ S u ∩ S v` with `d(u, w) + d(w, v) = d(u, v)` (extended distances `edist`). On connected
  graphs this is the usual definition; requiring nothing for unreachable pairs makes lower bounds
  stronger.

## Main results

* `SimpleGraph.IsHubLabeling.card_le_mul_sum`: the counting lower bound of Kosowski–Uznański–Viennot
  (PODC'19, proof of Theorem 2.1). Let `P` be a set of triples `(x, y, z)` with `d(x, z) ≤ L` such
  that every shortest `x`–`z` walk visits `y`, and such that `(x, y)` and `(z, y)` both determine the
  triple. Then `|P| ≤ 2 (L + 1) Σ_v |S v|`. (Each `y` lies on a fixed shortest path from `x` or from
  `z` to their common hub; the union of these paths is at most `L + 1` times larger than `S v`.)
-/

namespace SimpleGraph

variable {V : Type*} (G : SimpleGraph V)

/-- A hub labeling: every reachable pair `u, v` has a common hub `w ∈ S u ∩ S v` lying on a
shortest `u`–`v` path, i.e. `d(u, w) + d(w, v) = d(u, v)`. -/
def IsHubLabeling (S : V → Finset V) : Prop :=
  ∀ u v, G.Reachable u v → ∃ w ∈ S u, w ∈ S v ∧ G.edist u w + G.edist w v = G.edist u v

variable {G}

open Classical in
/-- The vertices of fixed shortest paths from `v` to its hubs at distance `≤ L`. -/
noncomputable def hubPathSet (S : V → Finset V) (L : ℕ) (v : V) : Finset V :=
  (S v).biUnion fun h =>
    if hr : G.Reachable v h ∧ G.edist v h ≤ L then
      (Classical.choose hr.1.exists_walk_length_eq_edist).support.toFinset
    else ∅

lemma card_hubPathSet_le (S : V → Finset V) (L : ℕ) (v : V) :
    (hubPathSet (G := G) S L v).card ≤ (L + 1) * (S v).card := by
  classical
  unfold hubPathSet
  refine (Finset.card_biUnion_le).trans ?_
  rw [mul_comm]
  refine Finset.sum_le_card_nsmul _ _ _ fun h _ => ?_
  split_ifs with hr
  · have hlen := Classical.choose_spec hr.1.exists_walk_length_eq_edist
    refine (List.toFinset_card_le _).trans ?_
    rw [Walk.length_support]
    have : ((Classical.choose hr.1.exists_walk_length_eq_edist).length : ℕ∞) ≤ L :=
      hlen.symm ▸ hr.2
    have : (Classical.choose hr.1.exists_walk_length_eq_edist).length ≤ L := by exact_mod_cast this
    omega
  · simp

lemma mem_hubPathSet {S : V → Finset V} {L : ℕ} {v h : V} (hh : h ∈ S v) (hr : G.Reachable v h)
    (hL : G.edist v h ≤ L) :
    ∃ p : G.Walk v h, (p.length : ℕ∞) = G.edist v h ∧
      ∀ y ∈ p.support, y ∈ hubPathSet (G := G) S L v := by
  classical
  refine ⟨Classical.choose hr.exists_walk_length_eq_edist,
    Classical.choose_spec hr.exists_walk_length_eq_edist, fun y hy => ?_⟩
  unfold hubPathSet
  refine Finset.mem_biUnion.2 ⟨h, hh, ?_⟩
  rw [dite_eq_left_of_eq_true (eq_true ⟨hr, hL⟩)]
  simpa using hy

/-- **Counting lower bound for hub labelings** (Kosowski–Uznański–Viennot, proof of Thm 2.1).
If every shortest `x`–`z` walk visits `y` for each triple `(x, y, z) ∈ P`, all these distances are
`≤ L`, and a triple is determined both by `(x, y)` and by `(z, y)`, then every hub labeling has
total size `Σ_v |S v| ≥ |P| / (2 (L + 1))`. -/
theorem IsHubLabeling.card_le_mul_sum [Fintype V] [DecidableEq V] {S : V → Finset V}
    (hS : G.IsHubLabeling S) (P : Finset (V × V × V)) (L : ℕ)
    (hreach : ∀ t ∈ P, G.Reachable t.1 t.2.2)
    (hL : ∀ t ∈ P, G.edist t.1 t.2.2 ≤ L)
    (hpass : ∀ t ∈ P, ∀ p : G.Walk t.1 t.2.2, (p.length : ℕ∞) = G.edist t.1 t.2.2 →
      t.2.1 ∈ p.support)
    (hinj₁ : Set.InjOn (fun t : V × V × V => (t.1, t.2.1)) P)
    (hinj₂ : Set.InjOn (fun t : V × V × V => (t.2.2, t.2.1)) P) :
    P.card ≤ 2 * (L + 1) * ∑ v, (S v).card := by
  classical
  set T := hubPathSet (G := G) S L
  -- every triple has its middle vertex in `T x` or in `T z`
  have key : ∀ t ∈ P, t.2.1 ∈ T t.1 ∨ t.2.1 ∈ T t.2.2 := by
    rintro ⟨x, y, z⟩ ht
    simp only at *
    obtain ⟨w, hwx, hwz, hsum⟩ := hS x z (hreach _ ht)
    have hfin : G.edist x z ≠ ⊤ := edist_ne_top_iff_reachable.2 (hreach _ ht)
    have hxw : G.edist x w ≠ ⊤ := fun h => hfin (by rw [← hsum, h]; simp)
    have hwz' : G.edist w z ≠ ⊤ := fun h => hfin (by rw [← hsum, h]; simp)
    have hxwL : G.edist x w ≤ L :=
      le_trans (le_trans le_self_add hsum.le) (hL _ ht)
    have hzwL : G.edist z w ≤ L := by
      rw [edist_comm]
      exact le_trans (le_trans le_add_self hsum.le) (hL _ ht)
    obtain ⟨p, hp, hpT⟩ := mem_hubPathSet (G := G) hwx (reachable_of_edist_ne_top hxw) hxwL
    obtain ⟨q, hq, hqT⟩ := mem_hubPathSet (G := G) hwz
      (reachable_of_edist_ne_top (by rwa [edist_comm])) hzwL
    have hlen : ((p.append q.reverse).length : ℕ∞) = G.edist x z := by
      rw [Walk.length_append, Walk.length_reverse, Nat.cast_add, hp, hq, edist_comm (u := z), hsum]
    have hy := hpass _ ht _ hlen
    rw [Walk.mem_support_append_iff, Walk.support_reverse, List.mem_reverse] at hy
    rcases hy with hy | hy
    · exact Or.inl (hpT y hy)
    · exact Or.inr (hqT y hy)
  -- inject `P` into `Σ v, T v ⊕ Σ v, T v`
  let D : Finset (V × V) := Finset.univ.sigma (fun v => T v) |>.map
    ⟨fun e => (e.1, e.2), fun a c h => by
      simp only [Prod.mk.injEq] at h
      exact Sigma.ext h.1 (heq_of_eq h.2)⟩
  have hD : D.card = ∑ v, (T v).card := by
    simp [D, Finset.card_sigma]
  have hmemD : ∀ v y, y ∈ T v → (v, y) ∈ D := by
    intro v y hy
    simp only [D, Finset.mem_map, Finset.mem_sigma, Finset.mem_univ, true_and]
    exact ⟨⟨v, y⟩, hy, rfl⟩
  let P₁ := P.filter fun t => t.2.1 ∈ T t.1
  let P₂ := P.filter fun t => t.2.1 ∉ T t.1
  have h₁ : P₁.card ≤ D.card := by
    refine Finset.card_le_card_of_injOn (fun t => (t.1, t.2.1)) (fun t ht => ?_) ?_
    · have := (Finset.mem_filter.1 ht).2
      exact hmemD _ _ this
    · exact hinj₁.mono (by intro t ht; exact (Finset.mem_filter.1 ht).1)
  have h₂ : P₂.card ≤ D.card := by
    refine Finset.card_le_card_of_injOn (fun t => (t.2.2, t.2.1)) (fun t ht => ?_) ?_
    · obtain ⟨htP, hn⟩ := Finset.mem_filter.1 ht
      exact hmemD _ _ ((key t htP).resolve_left hn)
    · exact hinj₂.mono (by intro t ht; exact (Finset.mem_filter.1 ht).1)
  have hsplit : P.card = P₁.card + P₂.card := (Finset.card_filter_add_card_filter_not _).symm
  have hT : ∑ v, (T v).card ≤ (L + 1) * ∑ v, (S v).card := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun v _ => card_hubPathSet_le S L v
  calc P.card = P₁.card + P₂.card := hsplit
    _ ≤ D.card + D.card := add_le_add h₁ h₂
    _ = 2 * ∑ v, (T v).card := by rw [hD]; ring
    _ ≤ 2 * ((L + 1) * ∑ v, (S v).card) := by gcongr
    _ = 2 * (L + 1) * ∑ v, (S v).card := by ring

end SimpleGraph
