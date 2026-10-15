import Papers.PODC2016.DynamicMIS.Alg2Graceful
import Papers.PODC2016.DynamicMIS.Alg2Abrupt

/-!
# Theorem 7: expected complexity of Algorithm 2

Combining the deterministic bounds of `Alg2Graceful` / `Alg2Abrupt` (in terms of `|S|`) with
Theorem 1 (`E|S| ≤ 1`), for a uniformly random order `π`:

* edge insertion/deletion, graceful node deletion, node unmuting (`theorem7_graceful`):
  `E[rounds] ≤ 3`, `E[broadcasts] ≤ 3`, `E[adjustments] ≤ 1`;
* abrupt deletion of `x` (`theorem7_abrupt`): `E[rounds] ≤ 3`,
  `E[broadcasts] ≤ 3 · min(log₃(|V|+1) + 1, deg x)`.

"Rounds" is the stabilisation time `alg2Rounds` (the first round from which the configuration never
changes; by the correctness theorems it is then the new greedy MIS). The node *insertion* variant of
Section 4.1 (two extra rounds announcing the new node) is not modelled separately: an inserted node
that knows its neighbours' states is the unmuting case.
-/

open Finset SimpleGraph
open scoped BigOperators

namespace DynamicMIS

namespace Alg2

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- Round complexity: the first round from which the configuration never changes. -/
noncomputable def alg2Rounds (N : Net V) (c₀ : V → St) : ℕ := sInf {T | StableFrom N c₀ T}

omit [DecidableEq V] [Fintype V] in
theorem alg2Rounds_le {N : Net V} {c₀ : V → St} {T : ℕ} (h : StableFrom N c₀ T) :
    alg2Rounds N c₀ ≤ T := Nat.sInf_le h

/-- Total number of broadcasts (state changes) of a stabilising run. -/
noncomputable def alg2Broadcasts (N : Net V) (c₀ : V → St) : ℕ :=
  ∑ t ∈ range (alg2Rounds N c₀), broadcastsAt N c₀ t

theorem expect_le_of_sum_le {f : (V ≃ Fin (Fintype.card V)) → ℕ} {k : ℕ}
    (h : ∑ π, f π ≤ k * (Fintype.card V).factorial) : 𝔼 π, (f π : ℚ) ≤ k := by
  rw [Fintype.expect_eq_sum_div_card, Fintype.card_equiv (Fintype.equivFin V)]
  rw [div_le_iff₀ (by positivity)]
  exact_mod_cast h

theorem sum_mul_ncard_infl_le (c : Change V) (cfg : Config V) (k : ℕ) :
    ∑ π : V ≃ Fin (Fintype.card V), k * (infl c cfg (orderRank π)).ncard ≤
      k * (Fintype.card V).factorial := by
  rw [← Finset.mul_sum]
  exact Nat.mul_le_mul_left k (sum_ncard_infl_le c cfg)

/-- **Theorem 7 / Lemma 9** (non-abrupt changes): Algorithm 2 needs in expectation at most one
adjustment, at most `3` rounds and at most `3` broadcasts. -/
theorem theorem7_graceful (c : Change V) (cfg : Config V) :
    𝔼 π : V ≃ Fin (Fintype.card V),
        ((adjustments c cfg (orderRank π)).ncard : ℚ) ≤ 1 ∧
      𝔼 π : V ≃ Fin (Fintype.card V),
        (alg2Rounds (netOf c cfg (orderRank π)) (initOf c cfg (orderRank π)) : ℚ) ≤ 3 ∧
      𝔼 π : V ≃ Fin (Fintype.card V),
        (alg2Broadcasts (netOf c cfg (orderRank π)) (initOf c cfg (orderRank π)) : ℚ) ≤ 3 := by
  refine ⟨expected_adjustments_le_one c cfg, ?_, ?_⟩
  · exact_mod_cast expect_le_of_sum_le ((Finset.sum_le_sum fun π _ =>
      alg2Rounds_le (graceful_stableFrom (orderRank_injective π))).trans
        (sum_mul_ncard_infl_le c cfg 3))
  · exact_mod_cast expect_le_of_sum_le ((Finset.sum_le_sum fun π _ =>
      graceful_broadcasts_le _).trans (sum_mul_ncard_infl_le c cfg 3))

/-- **Theorem 7 / Lemma 13** (abrupt deletion of `x`): at most one adjustment and `3` rounds in
expectation, and `O(min(log n, deg x))` broadcasts in expectation. -/
theorem theorem7_abrupt (x : V) (cfg : Config V) :
    𝔼 π : V ≃ Fin (Fintype.card V),
        ((adjustments (.deleteNode x) cfg (orderRank π)).ncard : ℚ) ≤ 1 ∧
      𝔼 π : V ≃ Fin (Fintype.card V),
        (alg2Rounds (netAbrupt x cfg (orderRank π)) (initAbrupt x cfg (orderRank π)) : ℚ) ≤ 3 ∧
      𝔼 π : V ≃ Fin (Fintype.card V),
        (alg2Broadcasts (netAbrupt x cfg (orderRank π)) (initAbrupt x cfg (orderRank π)) : ℚ) ≤
          ((3 * min (Nat.log 3 (Fintype.card V + 1) + 1)
            (cfg.graph.neighborSet x).ncard : ℕ) : ℚ) := by
  refine ⟨expected_adjustments_le_one _ cfg, ?_, ?_⟩
  · exact_mod_cast expect_le_of_sum_le ((Finset.sum_le_sum fun π _ =>
      alg2Rounds_le abrupt_stableFrom).trans (sum_mul_ncard_infl_le _ cfg 3))
  · refine expect_le_of_sum_le ((Finset.sum_le_sum fun π _ => ?_).trans
      (sum_mul_ncard_infl_le (.deleteNode x) cfg _))
    refine (abrupt_broadcasts_le _).trans ?_
    have hS : (infl (.deleteNode x) cfg (orderRank π)).ncard ≤ Fintype.card V :=
      (Set.ncard_le_card _).trans_eq Nat.card_eq_fintype_card
    have hm : min (Nat.log 3 ((infl (.deleteNode x) cfg (orderRank π)).ncard + 1) + 1)
          (cfg.graph.neighborSet x).ncard ≤
        min (Nat.log 3 (Fintype.card V + 1) + 1) (cfg.graph.neighborSet x).ncard :=
      min_le_min_right _ (Nat.add_le_add_right (Nat.log_mono_right (by omega)) 1)
    calc 3 * (infl (.deleteNode x) cfg (orderRank π)).ncard *
          min (Nat.log 3 ((infl (.deleteNode x) cfg (orderRank π)).ncard + 1) + 1)
            (cfg.graph.neighborSet x).ncard
        ≤ 3 * (infl (.deleteNode x) cfg (orderRank π)).ncard *
          min (Nat.log 3 (Fintype.card V + 1) + 1) (cfg.graph.neighborSet x).ncard :=
          Nat.mul_le_mul_left _ hm
      _ = 3 * min (Nat.log 3 (Fintype.card V + 1) + 1) (cfg.graph.neighborSet x).ncard *
          (infl (.deleteNode x) cfg (orderRank π)).ncard := by ring

/-- **History independence of Algorithm 2** (one step): after any non-abrupt change, from round
`3|V|` on the configuration of Algorithm 2 encodes the greedy MIS of the new configuration, which
only depends on the new configuration and `π`. -/
theorem alg2_run_eq_of_le {c : Change V} {cfg : Config V} {r : V → ℕ} (hr : Function.Injective r)
    {t : ℕ} (ht : 3 * Fintype.card V ≤ t) :
    run (netOf c cfg r) (initOf c cfg r) t =
      ofSet ((c.apply cfg).graph.greedyMIS (c.apply cfg).nodes r) := by
  have hS : (infl c cfg r).ncard ≤ Fintype.card V :=
    (Set.ncard_le_card _).trans_eq Nat.card_eq_fintype_card
  rw [graceful_stableFrom hr t (by omega), graceful_run_eq hr]

end Alg2

end DynamicMIS
