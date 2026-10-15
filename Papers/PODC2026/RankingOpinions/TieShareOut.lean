import Papers.PODC2026.RankingOpinions.TieShare
import Papers.PODC2026.RankingOpinions.TieReport

/-!
# Theorem 4.2 with the `out` variable as output

Theorem 4.2 claims that "the output of every winner or winner_spreader is its initial color".
Our main formalization (`tieShare_correct`) uses the output map `tsOut`: winners output their own
bra (= initial color), losers output `out`. If instead *every* agent outputs its `out` variable
(as Circles does: "Output: return out"), the claim fails, even for the sequential reading of the
rules: with 4 agents of colors `0, 0, 1, 1` (`k = 2`, a tie, both colors are winning) the schedule
`(0,2), (0,1), (1,2), (1,3), (1,2), (3,2)` leads to a configuration that no interaction changes, in
which agent `2` (color `1`, a winner spreader) has `out = 0`.
-/

namespace RankingOpinions

open Cslib.PopulationProtocol Cslib.PopulationProtocol.Protocol

namespace OutCounterexample

def input : Fin 4 → Fin 2 := ![0, 0, 1, 1]

def pre : List (Fin 4 × Fin 4) := [(0, 2), (0, 1), (1, 2), (1, 3), (1, 2), (3, 2)]

/-- The reached configuration (braket, out, status). -/
def X : Config (Fin 4) (TSState 2) :=
  ![((0, 1), 0, St.win), ((0, 1), 0, St.ws), ((1, 0), 0, St.ws), ((1, 0), 1, St.win)]

lemma reach : (tieShare 2 false).runSched (tsInit input) (cexSched pre) 6 = X := by decide

lemma fixed : ∀ a b : Fin 4, a ≠ b → (tieShare 2 false).interact X a b = X := by decide

lemma closed : (tieShare 2 false).Closed fun C : Config (Fin 4) (TSState 2) => C = X := by
  rintro C C' rfl ⟨a, b, hab, rfl⟩
  exact fixed a b hab

/-- **Theorem 4.2 fails for the reading "output = `out`"**: there is a weakly fair execution of
Circles_TieSharing (sequential reading) from colors `0,0,1,1` in which agent `2`, whose color `1` is
in relative majority, is never a loser but has `out = 0 ≠ 1` at all times `t ≥ 6`. -/
theorem tieShare_out_counterexample :
    ∃ E : (tieShare 2 false).Execution (Fin 4), E.config 0 = tsInit input ∧ E.WeaklyFair ∧
      inputCount input (input 2) = Finset.univ.sup (inputCount input) ∧
      ∀ t ≥ 6, (E.config t 2).2.2 ≠ St.los ∧ (E.config t 2).2.1 ≠ input 2 := by
  have hpre : ∀ p ∈ pre, p.1 ≠ p.2 := by decide
  set E := Execution.ofSched (tieShare 2 false) (tsInit input) (cexSched pre) (cexSched_ne pre hpre)
  refine ⟨E, rfl, ?_, by unfold inputCount; decide, fun t ht => ?_⟩
  · apply Execution.weaklyFair_of_cycle _ allPairs4 (by decide) pre.length
    · intro t
      show cexSched pre (pre.length + t) = _
      simp [cexSched]; rfl
    · decide
  · have h := closed.execution E (T := 6) reach t ht
    rw [h]; decide

end OutCounterexample

end RankingOpinions
