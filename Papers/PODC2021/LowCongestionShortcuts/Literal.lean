import Papers.PODC2021.LowCongestionShortcuts.Theorems

/-!
# The literal Theorem 3.1 (with `8δ` blocks) fails in a degenerate case

On the one-vertex graph, `δ(G) = 0`, so the literal statement asks for `0`-block partial shortcuts;
but a part `{v}` always has at least one block. Hence `8δ` must be weakened (we prove `8δ + 1`,
`theorem_3_1`).
-/

namespace LowCongestionShortcuts

open SimpleGraph Finset

/-- The trivial rooted tree on one vertex. -/
def singletonTree : (⊥ : SimpleGraph (Fin 1)).RootedTree where
  root := 0
  parent := id
  depth := fun _ => 0
  parent_root := rfl
  depth_root := rfl
  depth_parent := fun v hv => absurd (Subsingleton.elim v 0) hv
  adj_parent := fun v hv => absurd (Subsingleton.elim v 0) hv

/-- **The literal Theorem 3.1 of [GH21] is false for the one-vertex graph**: its minor density is
`δ(G) = 0`, and it does not admit tree-restricted `8δD`-congestion `8δ`-block partial shortcuts
(for `D = 0`, its diameter). -/
theorem theorem_3_1_literal_false_singleton :
    (⊥ : SimpleGraph (Fin 1)).minorDensity = 0 ∧
      ¬ (⊥ : SimpleGraph (Fin 1)).AdmitsPartialTreeShortcuts 0
        (8 * (⊥ : SimpleGraph (Fin 1)).minorDensity * 0)
        (8 * (⊥ : SimpleGraph (Fin 1)).minorDensity) := by
  have hδ : (⊥ : SimpleGraph (Fin 1)).minorDensity = 0 := by
    refine le_antisymm ((minorDensity_le_iff le_rfl).2 ?_) minorDensity_nonneg
    intro W _ H ⟨M⟩
    have : H.edgeSet = ∅ := by
      ext e
      induction e using Sym2.ind with
      | h a b =>
        simp only [mem_edgeSet, Set.mem_empty_iff_false, iff_false]
        intro hab
        obtain ⟨x, -, y, -, hxy⟩ := M.adj a b hab
        exact hxy
    simp [this]
  refine ⟨hδ, fun h => ?_⟩
  rw [hδ] at h
  obtain ⟨J, hJ, H, -, -, hb⟩ := h singletonTree (fun _ => le_rfl) (ι := Unit)
    (fun _ => {0}) ⟨fun i j hij => absurd (Subsingleton.elim i j) hij, fun _ => by
      exact connected_iff_exists_forall_reachable _ |>.2
        ⟨⟨0, by simp⟩, fun w => by rw [Subsingleton.elim w ⟨0, by simp⟩]⟩⟩
  have hJ' : () ∈ J := by
    rcases Finset.eq_empty_or_nonempty J with h | ⟨i, hi⟩
    · simp [h] at hJ
    · exact Subsingleton.elim i () ▸ hi
  have h1 := (hb () hJ').1
  have h2 : 0 < numBlocks ({0} : Finset (Fin 1)) (H ()) := by
    unfold numBlocks
    refine (Set.ncard_pos (Set.toFinite _)).2 ⟨_, 0, Or.inl (by simp), rfl⟩
  have : (0 : ℝ) < numBlocks ({0} : Finset (Fin 1)) (H ()) := by exact_mod_cast h2
  linarith

end LowCongestionShortcuts
