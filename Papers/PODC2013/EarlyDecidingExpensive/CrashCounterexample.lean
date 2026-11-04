import Papers.PODC2013.EarlyDecidingExpensive.Orderly

/-!
# The algorithm of Theorem 4.5 needs orderly crashes

With ordinary crashes (Definition 4.1) the algorithm of Section 4 violates agreement already for
`n = 3`, `t = 1`: node `0` (input `0`) crashes in round 1 delivering its value only to node `2`;
node `1` received nothing in round 1, so it decides its own input `1`; node `2` decided `0`
after round 1. Nodes `1` and `2` never fail. The crash is not orderly (node `1` precedes node `2`
in node `0`'s order), so this does not contradict Theorem 4.5, but it shows that its proof must
use orderliness, which the paper's correctness argument never mentions.
-/

namespace Podc.EarlyDecidingExpensive.Orderly

/-- The execution: node `0` crashes in round 1, reaching only node `2`. -/
def cex : Execution (Fin 3) Bool where
  input := ![false, true, true]
  F := {0}
  fr := fun _ => 1
  adv := fun k _ q => if k = 1 ∧ q = 2 then some false else none

lemma cex_crash : crashAdm (alg 1) 1 cex := by
  refine ⟨by decide, ?_⟩
  intro p hp k q
  have hp0 : p = 0 := by simpa [cex] using hp
  subst hp0
  refine ⟨fun hk => ?_, fun hk => ?_⟩
  · by_cases h0 : (0 : Fin 3) = q
    · subst h0; exact msg_self _ _ _
    rw [msg_of_faultyAt ⟨by simp [cex], by simp [cex]; omega⟩ h0]
    simp only [cex] at hk ⊢
    simp [show k ≠ 1 by omega]
  · simp only [cex] at hk
    subst hk
    revert q
    decide

lemma cex_decides1 : DecidesAt (alg 1) cex 1 1 true := by unfold DecidesAt; decide

lemma cex_decides2 : DecidesAt (alg 1) cex 2 1 false := by unfold DecidesAt; decide

/-- The algorithm of Theorem 4.5 is not resilient to (non-orderly) crash faults. -/
theorem not_crash_correct : ¬ Correct (alg (n := 3) 1) (crashAdm (alg 1) 1) := by
  intro hA
  have := hA.agreement cex cex_crash 1 (by decide) 2 (by decide) true false
    ⟨1, cex_decides1⟩ ⟨1, cex_decides2⟩
  simp at this

end Podc.EarlyDecidingExpensive.Orderly
