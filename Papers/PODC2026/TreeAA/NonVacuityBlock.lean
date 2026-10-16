import Papers.PODC2026.TreeAA.BlockGraph
import Papers.PODC2026.TreeAA.NonVacuity

/-!
# Non-vacuity of the block-graph hypotheses

The edge `K₂` is a connected block graph with the one-node clique tree; Theorem 8 composed with
Theorem 5 applies to it with the trivial `t = 0` black boxes of `NonVacuity.lean`.
-/

namespace TreeAA

open Cslib.Byzantine.LockStep SimpleGraph

lemma isMaxClique_univ_top : IsMaxClique (⊤ : SimpleGraph (Fin 2)) Finset.univ :=
  ⟨by simp, fun K _ h => Finset.eq_univ_of_forall fun v => h (Finset.mem_univ v)⟩

lemma isBlockGraph_top : IsBlockGraph (⊤ : SimpleGraph (Fin 2)) := by
  intro K K' hK hK' hne
  have e1 := hK.2 Finset.univ (by simp) (Finset.subset_univ _)
  have e2 := hK'.2 Finset.univ (by simp) (Finset.subset_univ _)
  exact absurd (e1.symm.trans e2) hne

lemma isCliqueTree_top :
    IsCliqueTree (⊤ : SimpleGraph (Fin 2)) (⊥ : SimpleGraph Unit) fun _ => Finset.univ where
  isTree := IsTree.of_subsingleton
  isMaxClique _ := isMaxClique_univ_top
  injective _ _ _ := rfl
  surjective K hK := ⟨(), hK.2 Finset.univ (by simp) (Finset.subset_univ _)⟩
  adj_nonempty _ _ h := absurd h (by simp)
  rip _ _ _ _ := fun _ h => Finset.mem_univ _

/-- Theorem 8 (with Theorem 5) has satisfiable hypotheses: `BlockGraphAA` on `K₂`. -/
theorem blockGraphAA_nonvacuous :
    SolvesAuthWithin ⊤
      (blockGraphAA (⊤ : SimpleGraph (Fin 2)) (fun _ : Unit => Finset.univ)
        (fun (_ : Fin 2) _ => ())
        (treeAA (subdiv_isTree isCliqueTree_top.isTree) (Sum.inl ()) 0 1 gcTriv realTriv))
      (treeAuth (Auth.none (Fin 2) _) (Auth.none (Fin 2) ℝ)) (atMost 0) noPre
      (GraphAA (⊤ : SimpleGraph (Fin 2))) (1 + 1) :=
  (blockGraphAA_of_gc_realAA (connected_top) isBlockGraph_top isCliqueTree_top _
    (fun _ _ => Finset.mem_univ _) () (by decide) _ _ (fun _ => Protocol.unforging_none _)
    (fun s => gcTriv_solves s) _ _ (Protocol.unforging_none _)
    (realTriv_solves _ 1 zero_le_one)).2

end TreeAA
