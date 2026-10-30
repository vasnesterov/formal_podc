import Papers.PODC2026.ContentObliviousEulerian.Theorem1
import Papers.PODC2026.ContentObliviousEulerian.DoubleMerge

/-!
# Non-vacuity of Theorem 1 (circuit level)

The hypotheses of `theorem1_circuit_level` are satisfiable: `K_{2,4}` is connected, all its
degrees are even, port numberings and election outcomes exist.
-/

namespace Podc.ContentObliviousEulerian.DoubleMerge

open SimpleGraph

lemma reach0 : ∀ u, K24.Reachable 0 u := by
  intro u
  fin_cases u
  · rfl
  · exact (Adj.reachable (by decide : K24.Adj 0 2)).trans (Adj.reachable (by decide))
  all_goals exact Adj.reachable (by decide)

lemma K24_connected : K24.Connected where
  preconnected u w := (reach0 u).symm.trans (reach0 w)
  nonempty := ⟨0⟩

lemma K24_even : ∀ v, Even (K24.degree v) := by decide

/-- Theorem 1 (circuit level) applies to `K_{2,4}`, with any port numbering and any election
outcome; e.g. one exists. -/
theorem theorem1_K24 :
    ∃ (port : PortNumbering K24) (elect : K24.Dart → Fin 6)
      (_ : ∀ d d', (stdPairing port K24_even).Circ d d' → elect d = elect d')
      (_ : ∀ d, ∃ x, (stdPairing port K24_even).Circ d x ∧ x.fst = elect d),
      ∃ π₁, Stage3 elect Finset.univ.toList (stdPairing port K24_even) π₁ ∧
        LeaderInv π₁ elect := by
  obtain ⟨port⟩ := PortNumbering.exists (G := K24)
  obtain ⟨elect, h1, h2⟩ := exists_elect (stdPairing port K24_even)
  obtain ⟨⟨π₁, hs⟩, hrest⟩ :=
    theorem1_circuit_level K24_connected port K24_even Fin.val Fin.val_injective elect h1 h2
  exact ⟨port, elect, h1, h2, π₁, hs, (hrest π₁ hs).1⟩

end Podc.ContentObliviousEulerian.DoubleMerge
