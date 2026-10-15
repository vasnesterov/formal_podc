import Papers.PODC2019.LocalBroadcastBC.Necessity

/-!
# Degenerate counterexample to the literal statement of Theorem 4.1 / Lemma A.2

On a single node (`n = 1`) consensus is trivially solvable (decide your own input), for every
`f`. With the paper's definition of `k`-connectivity (which requires `n > k`), the single-node
graph is not `1`-connected, so the literal Theorem 4.1 (and Lemma A.2) fails for `n = 1`, `f = 0`
(which satisfies the paper's standing assumption `f < n`). For `n = 1`, `f ≥ 1` the degree
condition fails as well, which shows that the assumption `f < n` is needed.
-/

open Cslib.Byzantine.LockStep

namespace LocalBroadcastBC

/-- The trivial protocol: send nothing, decide the own input immediately. -/
def trivialAlg (V : Type) : Protocol V Bool Unit Bool where
  send _ _ _ _ := none
  decide _ x _ := some x

/-- On a single node, consensus is solvable for every `f` (and every graph). -/
theorem single_node_solvable (G : SimpleGraph (Fin 1)) (f : ℕ) :
    SolvableLB G (atMost f) (Consensus : Spec (Fin 1) Bool Bool) := by
  refine ⟨Unit, trivialAlg (Fin 1), fun _ _ _ _ _ => rfl, fun s _ _ _ => ?_⟩
  have hdec : ∀ p o, Decides G (trivialAlg (Fin 1)) s p o ↔ o = s.input p := by
    intro p o
    constructor
    · rintro ⟨r, hr, -⟩
      simpa [status, trivialAlg, eq_comm] using hr
    · rintro rfl
      exact ⟨0, rfl, fun r hr => absurd hr (Nat.not_lt_zero _)⟩
  refine ⟨fun p _ => ⟨_, (hdec p _).2 rfl⟩, fun p hp v hv => ⟨p, hp, ((hdec p v).1 hv).symm⟩,
    fun p _ q _ v w hv hw => ?_⟩
  rw [hdec] at hv hw
  rw [hv, hw, Subsingleton.elim p q]

/-- The literal Theorem 4.1 (connectivity part) is false for `n = 1`, `f = 0`. -/
theorem not_theorem_4_1_single_node :
    SolvableLB (⊥ : SimpleGraph (Fin 1)) (atMost 0) (Consensus : Spec (Fin 1) Bool Bool) ∧
      0 < Fintype.card (Fin 1) ∧
      ¬ (⊥ : SimpleGraph (Fin 1)).IsVertexConnected (3 * 0 / 2 + 1) :=
  ⟨single_node_solvable _ 0, by simp, fun h => by simpa using h.1⟩

/-- Without `f < n` the degree condition of Theorem 4.1 fails (`n = 1`, `f = 1`). -/
theorem not_degree_single_node :
    SolvableLB (⊥ : SimpleGraph (Fin 1)) (atMost 1) (Consensus : Spec (Fin 1) Bool Bool) ∧
      ¬ 2 * 1 ≤ (⊥ : SimpleGraph (Fin 1)).degree 0 :=
  ⟨single_node_solvable _ 1, by simp⟩

end LocalBroadcastBC
