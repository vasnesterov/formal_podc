import Mathlib.Combinatorics.SimpleGraph.Hasse

-- CSLib candidate: Cslib/Foundations/Combinatorics/SimpleGraph/Path.lean (Mathlib candidate:
-- `Mathlib/Combinatorics/SimpleGraph/Hasse.lean`)

/-!
# Decidable adjacency in the path graph

Mathlib's `SimpleGraph.pathGraph n` on `Fin n` comes without a `DecidableRel` instance for its
adjacency, which is needed to compute degrees and edge sets. Adjacency is decided through
`SimpleGraph.pathGraph_adj` (consecutive values).
-/

namespace SimpleGraph

/-- Adjacency in `pathGraph n` is decidable: it means having consecutive values. -/
instance decidableAdjPathGraph (n : ℕ) : DecidableRel (pathGraph n).Adj := fun _ _ =>
  decidable_of_iff _ pathGraph_adj.symm

end SimpleGraph
