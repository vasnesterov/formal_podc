import Papers.PODC2013.SpeculativeStabilization.Theorem2

/-!
# Lemma 4 of the paper is false

Lemma 4 claims: if `γ₀ ∉ Γ₁`, then in the synchronous execution every register at time
`D = diam(g)` lies in `init_X ∪ {K - D, …, K - 1} ∪ {0, …, 2D - 1}`.

Counterexample: the cycle `C₅` (`n = 5`, `D = 2`, `K = 29`) with registers `(10, 10, 10, 12, 11)`.
The edge `2 – 3` is incorrect, so `γ₀ ∉ Γ₁`; processes `2, 3` reset at step `0`, processes `1, 4`
at step `1`, but process `0` (at distance `2 = D` from both `2` and `3`) increments at steps
`0, 1` and holds `12` at time `D = 2` (it resets only at step `2`). The off-by-one comes from the
paper's third case: a process at distance `i` from the resetting set `V'` is only reached by the
reset wave at time `i`, and `i = D` is possible.

The corrected statement (time `D + 1`, upper part `≥ K - D - 1`) is `lemma_4_corrected`
(`Theorem2.lean`); it suffices for Theorem 2.
-/

namespace Podc.SpeculativeStabilization

open Cslib.SelfStabilization Cslib.SelfStabilization.ResetUnison

/-- The cycle on five vertices `0 – 1 – 2 – 3 – 4 – 0`. -/
def C5 : SimpleGraph (Fin 5) where
  Adj a b := b = a + 1 ∨ a = b + 1
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨by decide⟩

instance : DecidableRel C5.Adj := fun a b => by unfold C5; infer_instance

theorem C5_connected : C5.Connected := by
  have h01 : C5.Adj 0 1 := by decide
  have h12 : C5.Adj 1 2 := by decide
  have h23 : C5.Adj 2 3 := by decide
  have h34 : C5.Adj 3 4 := by decide
  have h : ∀ u, C5.Reachable 0 u := by
    intro u
    fin_cases u
    · rfl
    · exact h01.reachable
    · exact h01.reachable.trans h12.reachable
    · exact (h01.reachable.trans h12.reachable).trans h23.reachable
    · exact ((h01.reachable.trans h12.reachable).trans h23.reachable).trans h34.reachable
  exact SimpleGraph.Connected.mk fun u v => (h u).symm.trans (h v)

theorem C5_diam : C5.diam = 2 := by
  have hle : C5.ediam ≤ 2 := by
    rw [SimpleGraph.ediam_le_iff]
    have key : ∀ u v : Fin 5, u = v ∨ C5.Adj u v ∨ ∃ w, C5.Adj u w ∧ C5.Adj w v := by decide
    intro u v
    rcases key u v with rfl | h | ⟨w, h1, h2⟩
    · simp
    · rw [SimpleGraph.edist_eq_one_iff_adj.2 h]; norm_num
    · exact (SimpleGraph.edist_le (SimpleGraph.Walk.cons h1 (SimpleGraph.Walk.cons h2 .nil))).trans
        (by simp)
  have hge : 2 ≤ C5.edist 0 2 := by
    have h0 : C5.edist 0 2 ≠ 0 := by simp
    have h1 : C5.edist 0 2 ≠ 1 := by
      rw [Ne, SimpleGraph.edist_eq_one_iff_adj]; decide
    have h2 : C5.edist 0 2 ≠ ⊤ := by
      exact SimpleGraph.edist_ne_top_iff_reachable.2 <| C5_connected.preconnected 0 2
    obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.1 h2
    rw [← hk] at h0 h1 ⊢
    norm_cast at h0 h1 ⊢
    omega
  have : C5.ediam = 2 := le_antisymm hle (hge.trans SimpleGraph.edist_le_ediam)
  rw [SimpleGraph.diam, this]; rfl

theorem C5_clockSize : clockSize C5 = 29 := by
  simp [clockSize, C5_diam]

/-- The initial configuration of the counterexample. -/
def γ5 : Fin 5 → ℤ := ![10, 10, 10, 12, 11]

/-- The conclusion of the paper's Lemma 4 for the configuration at time `D`. -/
def Lemma4Concl {V : Type*} [Fintype V] (G : SimpleGraph V) (γ : V → ℤ) : Prop :=
  ∀ v, (-(Fintype.card V : ℤ) ≤ γ v ∧ γ v ≤ 0) ∨
    ((clockSize G : ℤ) - G.diam ≤ γ v ∧ γ v ≤ clockSize G - 1) ∨ (0 ≤ γ v ∧ γ v ≤ 2 * G.diam - 1)

/-- **Lemma 4 is false**: on `C₅` from `(10, 10, 10, 12, 11)` (not in `Γ₁`), the synchronous
execution of SSME has register `12` at process `0` at time `D = 2`. -/
theorem lemma_4_false :
    SValid C5 γ5 ∧ ¬ Gamma1 C5 γ5 ∧ (ssme C5)^[C5.diam] γ5 0 = 12 ∧
      ¬ Lemma4Concl C5 ((ssme C5)^[C5.diam] γ5) := by
  have hs : ssme C5 = next 29 5 C5 := by
    unfold ssme; rw [C5_clockSize]; rfl
  have hval : (next 29 5 C5)^[2] γ5 0 = 12 := by decide
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold SValid; rw [C5_clockSize]; decide
  · unfold Gamma1; rw [C5_clockSize]; decide
  · rw [hs, C5_diam, hval]
  · intro h
    have := h 0
    rw [hs, C5_diam, hval, C5_clockSize] at this
    simp at this

/-- Non-vacuity of the hypotheses of Theorems 1 and 2: they apply to `C₅` with identities
`0, …, 4`. -/
example : SelfStabilizing (unfairExecs (ssme C5) (SValid C5))
      (MutualExclusion (Privileged C5 fun v => v.val)) ∧
    PseudoStabilizingWithin (syncExecs (ssme C5) (SValid C5))
      (MutualExclusion (Privileged C5 fun v => v.val)) 1 := by
  refine ⟨theorem_1' C5_connected _ Fin.val_injective fun v => v.2, ?_⟩
  have := theorem_2 C5_connected (fun v : Fin 5 => v.val) Fin.val_injective fun v => v.2
  rwa [C5_diam] at this

end Podc.SpeculativeStabilization
