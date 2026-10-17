import Papers.PODC2026.RankingOpinions.RankingProtocol
import Cslib.Computability.Distributed.PopulationProtocols.Schedules
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.IntervalCases
import Mathlib.Data.List.GetD

/-!
# The Ranking protocol as stated in the paper is incorrect

Breitkopf, Dallot, El-Hayek, Schmid, PODC 2026, Section 6 (Theorem 1.2).

Without our self-synchronisation fix (`norm`), the rules (1)–(8) of Section 6 (with the
interpretation fixed in `RankingProtocol.lean`) fail already for `k = 2` colors and `3` agents with
inputs `0, 1, 1` (so `x₀ = 1`, `x₁ = 2`: all colors present, no tie). The configuration

  `⟨0,1|0,1⟩, ⟨1,0|1,0⟩*, ⟨1,1|0,1⟩*`

is reachable and *silent* (no interaction changes it), but agent `2` (color `1`, the majority)
outputs `1` instead of `0`. The token of color `1` sits on agent `2`'s own ket while agent `2`'s
bra still carries the old ranking `1`: rule (4) only lets a token holder update *other* agents.
(The paper's proof of Lemma 6.10 overlooks this case.)
-/

namespace RankingOpinions.Ranking

open Cslib.PopulationProtocol Cslib.PopulationProtocol.Protocol Finset

/-- The Ranking protocol exactly as stated in the paper (no self-synchronisation). -/
def rankingLit (k : ℕ) [NeZero k] : Protocol (RState k) := ⟨firstChange rules⟩

namespace Counterexample

/-- Inputs: agent `0` has color `0`, agents `1, 2` have color `1`. -/
def input : Fin 3 → Fin 2 := ![0, 1, 1]

/-- The schedule leading to the bad silent configuration. -/
def path : List (Fin 3 × Fin 3) :=
  [(0, 1), (1, 2), (0, 2), (0, 2), (0, 2), (0, 1), (1, 2), (0, 2), (1, 2)]

/-- The schedule: follow `path`, then let agents `0` and `1` interact forever. -/
def sched (t : ℕ) : Fin 3 × Fin 3 := path.getD t (0, 1)

/-- The bad silent configuration `⟨0,1|0,1⟩, ⟨1,0|1,0⟩*, ⟨1,1|0,1⟩*`. -/
def bad : Config (Fin 3) (RState 2) := ![⟨0, 1, 0, 1, false⟩, ⟨1, 0, 1, 0, true⟩, ⟨1, 1, 0, 1, true⟩]

lemma sched_ne (t : ℕ) : (sched t).1 ≠ (sched t).2 := by
  unfold sched
  rcases Nat.lt_or_ge t 9 with h | h
  · interval_cases t <;> decide
  · rw [List.getD_eq_default _ _ (by simp [path]; omega)]; decide

/-- The execution. -/
def E : (rankingLit 2).Execution (Fin 3) :=
  Execution.ofSched _ (fun a => initState (input a)) sched sched_ne

lemma config_nine : E.config 9 = bad := by decide +kernel

lemma bad_silent (a b : Fin 3) : (rankingLit 2).interact bad a b = bad := by
  revert a b; decide +kernel

lemma config_bad (t : ℕ) (h : 9 ≤ t) : E.config t = bad := by
  induction t, h using Nat.le_induction with
  | base => exact config_nine
  | succ t _ ih => rw [E.step, ih, bad_silent]

lemma E_globallyFair : E.GloballyFair := by
  intro C C' hst hC T
  obtain ⟨t, ht, hCt⟩ := hC 9
  have hCb : C = bad := hCt ▸ config_bad t ht
  obtain ⟨a, b, -, rfl⟩ := hst
  refine ⟨max T 9, le_max_left _ _, ?_⟩
  rw [hCb, bad_silent]; exact config_bad _ (le_max_right _ _)

/-- **The Ranking protocol of Section 6, as stated, does not solve the ranking problem**:
for `k = 2` and inputs `0, 1, 1` (Definition 6.1 holds: both colors present, `x₀ = 1 ≠ 2 = x₁`),
there is a globally fair execution in which agent `2` outputs a wrong value forever. -/
theorem literal_not_correct :
    ∃ E : (rankingLit 2).Execution (Fin 3),
      E.config 0 = (fun a => initState (input a)) ∧ E.GloballyFair ∧
      (∀ c, ∃ a, input a = c) ∧ Function.Injective (inputCount input) ∧
      ∀ t ≥ 9, ((E.config t 2).br : ℕ) ≠
        (univ.filter fun ℓ => inputCount input (input 2) < inputCount input ℓ).card := by
  refine ⟨E, rfl, E_globallyFair, by decide, ?_, fun t ht => ?_⟩
  · intro c d h
    revert c d h; decide
  · rw [config_bad t ht]; decide

end Counterexample

end RankingOpinions.Ranking
