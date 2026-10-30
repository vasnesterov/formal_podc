import Cslib.Foundations.Combinatorics.SimpleGraph.Ball
import Mathlib

-- CSLib candidate: Cslib/Foundations/Combinatorics/SimpleGraph/Power.lean

/-!
# Powers of a simple graph

The `r`-th power `G.power r` of a simple graph `G` joins two distinct vertices iff their
`G`-distance is at most `r` (unreachable pairs have `edist = ⊤` and are never joined). The square
`G.power 2` is the graph of the "distance-2" problems (`G²`-colouring, `G²`-vertex cover,
`G²`-dominating set, …) where the input/communication graph is `G` but the problem is solved on
`G²`.

## Main definitions and results

* `SimpleGraph.power G r`: the `r`-th power.
* `power_one`, `le_power`, `power_mono`: `G¹ = G`, `G ≤ Gʳ` for `r ≥ 1`, monotone in `r`.
* `power_two_adj`: `u ~ v` in `G²` iff `u ≠ v` and `u ~ v` in `G` or they have a common neighbour.
-/

namespace SimpleGraph

variable {V : Type*} (G : SimpleGraph V)

/-- The `r`-th power of `G`: distinct vertices at `G`-distance at most `r` are adjacent. -/
def power (r : ℕ) : SimpleGraph V where
  Adj u v := u ≠ v ∧ G.edist u v ≤ r
  symm := ⟨fun _ _ h => ⟨h.1.symm, by rw [edist_comm]; exact h.2⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

variable {G}

@[simp] lemma power_adj {r : ℕ} {u v : V} : (G.power r).Adj u v ↔ u ≠ v ∧ G.edist u v ≤ r :=
  Iff.rfl

lemma power_mono {r s : ℕ} (h : r ≤ s) : G.power r ≤ G.power s := fun _ _ huv =>
  ⟨huv.1, huv.2.trans (by exact_mod_cast h)⟩

@[simp] lemma power_one : G.power 1 = G := by
  ext u v
  simp only [power_adj, Nat.cast_one]
  constructor
  · rintro ⟨hne, h⟩
    rcases (le_iff_lt_or_eq.1 h) with h | h
    · exact absurd (Order.lt_one_iff.1 h) (by simpa using hne)
    · exact edist_eq_one_iff_adj.1 h
  · intro h
    exact ⟨h.ne, (edist_eq_one_iff_adj.2 h).le⟩

lemma le_power {r : ℕ} (hr : 1 ≤ r) : G ≤ G.power r := by
  simpa using power_mono (G := G) hr

/-- Adjacency in the square: distinct and at distance one or two. -/
lemma power_two_adj {u v : V} :
    (G.power 2).Adj u v ↔ u ≠ v ∧ (G.Adj u v ∨ ∃ w, G.Adj u w ∧ G.Adj w v) := by
  simp only [power_adj]
  refine and_congr_right fun hne => ?_
  constructor
  · intro h
    have hr : G.edist u v ≠ ⊤ := ne_top_of_le_ne_top (by simp) h
    obtain ⟨p, hp⟩ := exists_walk_of_edist_ne_top hr
    have hlen : p.length ≤ 2 := by
      have : (p.length : ℕ∞) ≤ 2 := hp ▸ h
      exact_mod_cast this
    match p, hlen with
    | .nil, _ => exact absurd rfl hne
    | .cons h1 .nil, _ => exact Or.inl h1
    | .cons h1 (.cons h2 .nil), _ => exact Or.inr ⟨_, h1, h2⟩
    | .cons _ (.cons _ (.cons _ _)), h => simp at h
  · rintro (h | ⟨w, h1, h2⟩)
    · exact (edist_eq_one_iff_adj.2 h).le.trans (by norm_num)
    · have := edist_le_natCast_add (n := 1) (m := 1) (edist_eq_one_iff_adj.2 h1).le
        (edist_eq_one_iff_adj.2 h2).le
      simpa [one_add_one_eq_two] using this

lemma Adj.power_two {u v : V} (h : G.Adj u v) : (G.power 2).Adj u v :=
  power_two_adj.2 ⟨h.ne, Or.inl h⟩

lemma power_two_adj_of_adj_adj {u v w : V} (h1 : G.Adj u w) (h2 : G.Adj w v) (hne : u ≠ v) :
    (G.power 2).Adj u v :=
  power_two_adj.2 ⟨hne, Or.inr ⟨w, h1, h2⟩⟩

/-- For a finite graph with decidable adjacency, adjacency in the square is decidable. -/
noncomputable instance decidableRelPowerTwo [Fintype V] [DecidableEq V] [DecidableRel G.Adj] :
    DecidableRel (G.power 2).Adj := fun _ _ =>
  decidable_of_iff _ power_two_adj.symm

end SimpleGraph
