import Papers.PODC2022.ArrowTopology.SignModel

/-!
# Counting faces of `N_I` and `N_O` (two voters, three alternatives)

Cheap sanity facts in the sign model (`SignModel.lean`) for two voters, from Sections 2.3.2 and 6
of S. Rajsbaum, A. Raventós-Pujol, *A Distributed Combinatorial Topology Approach to Arrow's
Impossibility Theorem*, PODC 2022. A *chromatic triangle* is any choice of a label
`t j : Fin 2 → Bool` (`++, −−, +−, −+`) for each pair `j ∈ {AB, BC, CA}`; the triangles of `N_I`
are the consistent ones (`Consistent`: no voter has a cyclic preference). By
`ThreeAlts.exists_sig_eq` / `ThreeAlts.sig_injective`, these are in bijection with profiles.
-/

namespace Podc.ArrowTopology

/-- `N_I` has 12 vertices (3 pairs × 4 sign vectors), and each of them lies in a triangle. -/
theorem NI_vertices : Fintype.card (Vtx (Fin 2)) = 12 ∧
    ∀ v : Vtx (Fin 2), ∃ t : Fin 3 → Fin 2 → Bool, Consistent t ∧ t v.1 = v.2 := by
  decide

/-- `N_I` has 36 triangles (= the 6 × 6 profiles). -/
theorem NI_triangles :
    (Finset.univ.filter fun t : Fin 3 → Fin 2 → Bool => Consistent t).card = 36 := by
  decide

/-- There are 64 chromatic triangles; the 28 excluded ones are exactly those in which the first
voter's sign is the same on all pairs or the second voter's sign is the same on all pairs. -/
theorem NI_triangles_eq_chromatic_minus :
    Fintype.card (Fin 3 → Fin 2 → Bool) = 64 ∧
    (Finset.univ.filter fun t : Fin 3 → Fin 2 → Bool =>
      (t 0 0 = t 1 0 ∧ t 1 0 = t 2 0) ∨ (t 0 1 = t 1 1 ∧ t 1 1 = t 2 1)).card = 28 ∧
    ∀ t : Fin 3 → Fin 2 → Bool,
      Consistent t ↔ ¬ ((t 0 0 = t 1 0 ∧ t 1 0 = t 2 0) ∨ (t 0 1 = t 1 1 ∧ t 1 1 = t 2 1)) := by
  decide

/-- Number of pairs on which the two voters disagree. -/
def numDisagree (t : Fin 3 → Fin 2 → Bool) : ℕ :=
  (Finset.univ.filter fun j : Fin 3 => t j 0 ≠ t j 1).card

/-- 24 triangles of `N_I` have three distinct labels; they are exactly those where the voters
disagree on one or two pairs (the torus `T`, the renaming-task complex). The other 12 have a
repeated label. -/
theorem NI_distinct_labels :
    (Finset.univ.filter fun t : Fin 3 → Fin 2 → Bool =>
      Consistent t ∧ Function.Injective t).card = 24 ∧
    (Finset.univ.filter fun t : Fin 3 → Fin 2 → Bool =>
      Consistent t ∧ ¬ Function.Injective t).card = 12 ∧
    ∀ t : Fin 3 → Fin 2 → Bool, Consistent t →
      (Function.Injective t ↔ numDisagree t = 1 ∨ numDisagree t = 2) := by
  decide

/-- `N_O` (weak symmetry breaking output complex) has as triangles the 8 sign triples minus the
2 constant ones. -/
theorem NO_triangles :
    (Finset.univ.filter fun s : Bool × Bool × Bool => OutTri s.1 s.2.1 s.2.2).card = 6 ∧
    ∀ s : Bool × Bool × Bool, ¬ OutTri s.1 s.2.1 s.2.2 ↔ s = (true, true, true) ∨
      s = (false, false, false) := by
  decide

end Podc.ArrowTopology
