import Cslib.Computability.Distributed.Congest.LowerBound
import Mathlib.Combinatorics.SimpleGraph.Diam

-- CSLib candidate: Cslib/Computability/Distributed/Congest/GatherInputs.lean

/-!
# Gathering all node inputs (full-information flooding)

A generalisation of `Cslib.Congest.gatherAlg` (which gathers adjacency rows) to arbitrary finite
node inputs `J`: every node keeps a partial map `V → Option J` of the inputs it knows, and in each
round sends all of it (encoded in `gatherInputsBits V J` bits) to every neighbour.

* `gatherInputs_sound`: everything a node knows is correct.
* `gatherInputs_known`: after `t` rounds, node `v` knows the input of every node at distance `≤ t`.
* `gatherInputs_run_of_ediam`: on a graph of diameter `≤ D`, after `D` rounds every node knows all
  inputs.

Used for non-vacuity: any function of the global input can be computed within `ediam` rounds, so
lower-bound hypotheses "an algorithm computes `f` in `T` rounds" are satisfiable for large `B`.
-/

namespace Cslib.Congest

variable {V J : Type*} [Fintype V] [DecidableEq V] [Fintype J]

/-- Number of message bits: enough to encode a partial input map `V → Option J`. -/
noncomputable def gatherInputsBits (V J : Type*) [Fintype V] [DecidableEq V] [Fintype J] : ℕ :=
  Nat.clog 2 (Fintype.card (V → Option J))

/-- Binary encoding of a partial input map. -/
noncomputable def encInputs : (V → Option J) → Msg (gatherInputsBits V J) := fun k =>
  (Fintype.equivFin (Msg (gatherInputsBits V J))).symm
    (Fin.castLE (by
      have : Fintype.card (Msg (gatherInputsBits V J)) = 2 ^ gatherInputsBits V J := by simp [Msg]
      rw [this]
      exact Nat.le_pow_clog (by norm_num) _) (Fintype.equivFin (V → Option J) k))

lemma encInputs_injective : Function.Injective (encInputs (V := V) (J := J)) := by
  intro a b h
  simp only [encInputs, EmbeddingLike.apply_eq_iff_eq, Fin.castLE_inj] at h
  exact h

/-- Decoding (a left inverse of `encInputs`). -/
noncomputable def decInputs : Msg (gatherInputsBits V J) → V → Option J :=
  Function.invFun encInputs

lemma decInputs_encInputs (k : V → Option J) : decInputs (encInputs k) = k :=
  Function.leftInverse_invFun encInputs_injective k

/-- The full-information flooding algorithm for inputs in `J` (the output bit is unused). -/
noncomputable def gatherInputsAlg (V J : Type*) [Fintype V] [DecidableEq V] [Fintype J] :
    Algorithm V J (V → Option J) (gatherInputsBits V J) := by
  classical
  exact
  { init := fun v j a => if a = v then some j else none
    send := fun _ k _ => encInputs k
    step := fun _ k m a =>
      match k a with
      | some j => some j
      | none =>
        if h : ∃ j, ∃ u c, m u = some c ∧ decInputs c a = some j then some (Classical.choose h)
        else none
    out := fun _ _ => true }

variable (G : SimpleGraph V) [DecidableRel G.Adj] (inp : V → J)

/-- Messages from neighbours carry their full knowledge. -/
lemma gatherInputs_msg {t : ℕ} {v a : V} {j : J} :
    (∃ u c, (if G.Adj u v then some (encInputs ((gatherInputsAlg V J).run G inp t u)) else none) =
      some c ∧ decInputs c a = some j) ↔
      ∃ u, G.Adj u v ∧ (gatherInputsAlg V J).run G inp t u a = some j := by
  constructor
  · rintro ⟨u, c, hc, hj⟩
    by_cases hu : G.Adj u v
    · simp only [hu, ↓reduceIte, Option.some.injEq] at hc
      subst hc
      rw [decInputs_encInputs] at hj
      exact ⟨u, hu, hj⟩
    · simp [hu] at hc
  · rintro ⟨u, hu, hj⟩
    exact ⟨u, encInputs ((gatherInputsAlg V J).run G inp t u), by simp [hu],
      by rw [decInputs_encInputs]; exact hj⟩

/-- What a node knows after a round, it knew before or a neighbour knew. -/
lemma gatherInputs_some_succ {t : ℕ} {v a : V} {j : J}
    (h : (gatherInputsAlg V J).run G inp (t + 1) v a = some j) :
    (gatherInputsAlg V J).run G inp t v a = some j ∨
      ∃ u, G.Adj u v ∧ (gatherInputsAlg V J).run G inp t u a = some j := by
  simp only [Algorithm.run, gatherInputsAlg] at h
  split at h
  · rename_i j0 hk
    exact Or.inl (by simpa [gatherInputsAlg] using hk.trans h)
  · split_ifs at h with hex
    cases h
    exact Or.inr ((gatherInputs_msg G inp).1 (Classical.choose_spec hex))

/-- A node learns what it or a neighbour knew in the previous round. -/
lemma gatherInputs_isSome_succ {t : ℕ} {v a : V}
    (h : ((gatherInputsAlg V J).run G inp t v a).isSome ∨
      ∃ u, G.Adj u v ∧ ((gatherInputsAlg V J).run G inp t u a).isSome) :
    ((gatherInputsAlg V J).run G inp (t + 1) v a).isSome := by
  simp only [Algorithm.run, gatherInputsAlg]
  split
  · rfl
  · rename_i hk
    split_ifs with hex
    · rfl
    · exfalso
      rcases h with h | ⟨u, hu, h⟩
      · simp only [gatherInputsAlg] at h
        rw [hk] at h; simp at h
      · obtain ⟨j, hj⟩ := Option.isSome_iff_exists.1 h
        exact hex ⟨j, (gatherInputs_msg G inp).2 ⟨u, hu, hj⟩⟩

/-- **Soundness**: every input a node knows is the true input. -/
lemma gatherInputs_sound : ∀ t v a j, (gatherInputsAlg V J).run G inp t v a = some j → j = inp a
  | 0, v, a, j, h => by
    classical
    simp only [Algorithm.run, gatherInputsAlg] at h
    split_ifs at h with ha
    · subst ha; exact (Option.some.inj h).symm
  | t + 1, v, a, j, h => by
    rcases gatherInputs_some_succ G inp h with h' | ⟨u, -, h'⟩
    · exact gatherInputs_sound t v a j h'
    · exact gatherInputs_sound t u a j h'

/-- **Completeness**: after `t` rounds, `v` knows the input of every node at distance `≤ t`. -/
lemma gatherInputs_known : ∀ (t : ℕ) (v a : V) (p : G.Walk v a), p.length ≤ t →
    ((gatherInputsAlg V J).run G inp t v a).isSome
  | 0, v, a, p, hp => by
    classical
    obtain rfl := SimpleGraph.Walk.eq_of_length_eq_zero (Nat.le_zero.1 hp)
    simp [Algorithm.run, gatherInputsAlg]
  | t + 1, v, _, .nil, _ =>
    gatherInputs_isSome_succ G inp (Or.inl (gatherInputs_known t v v .nil (Nat.zero_le _)))
  | t + 1, v, a, .cons (v := u) hvu q, hp =>
    gatherInputs_isSome_succ G inp
      (Or.inr ⟨u, hvu.symm, gatherInputs_known t u a q (by simp at hp; omega)⟩)

/-- On a graph of diameter `≤ D`, after `D` rounds every node knows every input. -/
theorem gatherInputs_run_of_ediam {D : ℕ} (hD : G.ediam ≤ D) (v : V) :
    (gatherInputsAlg V J).run G inp D v = fun a => some (inp a) := by
  funext a
  have hd : G.edist v a ≤ D := G.edist_le_ediam.trans hD
  obtain ⟨p, hp⟩ := SimpleGraph.exists_walk_of_edist_ne_top (ne_top_of_le_ne_top
    (by exact ENat.natCast_ne_top D) hd)
  have hlen : p.length ≤ D := by rw [← hp] at hd; exact_mod_cast hd
  obtain ⟨j, hj⟩ := Option.isSome_iff_exists.1 (gatherInputs_known G inp D v a p hlen)
  rw [hj, gatherInputs_sound G inp D v a j hj]

end Cslib.Congest
