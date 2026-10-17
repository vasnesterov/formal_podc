-- CSLib candidate: Cslib/Foundations/Combinatorics/SimpleGraph/Girth.lean
import Cslib.Foundations.Combinatorics.SimpleGraph.Girth

/-!
# The Moore bound relative to a vertex set

`NoShortCycles.ncard_edgeSet_le_card_rpow`: a graph of girth `> 2k` all of whose edges have their
endpoints in a vertex set `S` has at most `|S|^{1+1/k} + |S|` edges. This is the form needed when the
graph lives on a large vertex type but only uses the vertices of `S` (e.g. a spanner of an induced
subgraph `G[S]`); CSLib's `NoShortCycles.ncard_edgeSet_le_rpow` is the case `S = univ`.
-/

open Finset

namespace SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-- **Moore bound relative to a vertex set.** If all edges of `G` have their endpoints in `S` and
`G` has girth `> 2k`, then `|E(G)| ≤ |S|^{1+1/k} + |S|`. -/
theorem NoShortCycles.ncard_edgeSet_le_card_rpow [Finite V] {k : ℕ} (hk : 1 ≤ k)
    (h : G.NoShortCycles (2 * k)) (S : Finset V) (hS : ∀ u v, G.Adj u v → u ∈ S) :
    (G.edgeSet.ncard : ℝ) ≤ (#S : ℝ) ^ (1 + 1 / (k : ℝ)) + #S := by
  set s := #S
  have hx : (0 : ℝ) ≤ (s : ℝ) ^ (1 / (k : ℝ)) := by positivity
  set d := ⌈(s : ℝ) ^ (1 / (k : ℝ))⌉₊
  have hd : #S ≤ d ^ k := by
    have : (s : ℝ) ≤ (d : ℝ) ^ k := by
      calc (s : ℝ) = ((s : ℝ) ^ ((k : ℝ)⁻¹)) ^ k :=
            (Real.rpow_inv_natCast_pow (Nat.cast_nonneg s) (by omega)).symm
        _ ≤ (d : ℝ) ^ k := by
            rw [← one_div]
            exact pow_le_pow_left₀ hx (Nat.le_ceil _) k
    exact_mod_cast this
  have hE := h.ncard_edgeSet_le hk S hS hd
  calc (G.edgeSet.ncard : ℝ) ≤ d * s := by exact_mod_cast hE
    _ ≤ ((s : ℝ) ^ (1 / (k : ℝ)) + 1) * s :=
        mul_le_mul_of_nonneg_right (Nat.ceil_lt_add_one hx).le (Nat.cast_nonneg _)
    _ = (s : ℝ) ^ (1 + 1 / (k : ℝ)) + s := by
        rw [Real.rpow_add' (Nat.cast_nonneg _) (by positivity), Real.rpow_one]
        ring

-- At CSLib migration, `NoShortCycles.ncard_edgeSet_le_rpow` becomes this one-line corollary.
example [Fintype V] {k : ℕ} (hk : 1 ≤ k) (h : G.NoShortCycles (2 * k)) :
    (G.edgeSet.ncard : ℝ) ≤ (Fintype.card V : ℝ) ^ (1 + 1 / (k : ℝ)) + Fintype.card V := by
  simpa using h.ncard_edgeSet_le_card_rpow hk univ fun _ _ _ => mem_univ _

end SimpleGraph
