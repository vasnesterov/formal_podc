import Papers.PODC2020.NullMessagesByzantine.Complexity

/-!
# Non-vacuity

The hypothesis of Theorem 2.1 ("`B` solves binary Byzantine agreement against `t` faults") is
satisfiable: for `t = 0` by the leader protocol `leaderBA` (the leader `0` sends its input, every
process decides the leader's input). For `t ≥ 1` any classical unauthenticated protocol for
`n > 3t` (e.g. Phase King, EIG) qualifies; none is formalized here.
-/

namespace Podc.NullMessagesByzantine

open Cslib.Byzantine.LockStep

variable {n : ℕ} [NeZero n]

/-- The leader protocol: `0` sends its input in round 0; everyone decides the leader's input. -/
def leaderBA : Protocol (Fin n) Bool Bool Bool where
  send p x h _ := if p = 0 ∧ h = [] then some x else none
  decide p x h := if p = 0 then some x else (h[0]?.bind fun ib => ib 0)

lemma leaderBA_decides (s : Scenario (Fin n) Bool Bool) (hs : s.byz = ∅) (hrel : s.Reliable)
    (p : Fin n) : Decides ⊤ leaderBA s p (s.input 0) := by
  by_cases hp : p = 0
  · subst hp; exact ⟨0, by simp [status, leaderBA], fun r hr => by omega⟩
  · refine ⟨1, ?_, fun r hr => ?_⟩
    · simp only [status, leaderBA, hp, ite_false]
      rw [getElem?_hist _ _ _ Nat.zero_lt_one]
      simp only [Option.bind_some]
      rw [deliver_honest _ _ _ hrel (by simp [hs]) (by simpa using Ne.symm hp)]
      simp
    · obtain rfl : r = 0 := by omega
      simp [status, leaderBA, hp]

/-- `leaderBA` solves binary Byzantine agreement without faults. -/
theorem leaderBA_solves : Solves ⊤ (leaderBA (n := n)) (atMost 0) BA := by
  intro s hs hrel
  have hs' : s.byz = ∅ := eq_empty_of_mem_atMost_zero hs
  refine ⟨fun p _ => ⟨_, leaderBA_decides s hs' hrel p⟩, ?_, ?_⟩
  · intro v hv p _
    rw [← hv 0 (by simp [Scenario.honest, hs'])]
    exact leaderBA_decides s hs' hrel p
  · intro p _ q _ v w hv hw
    rw [Decides.unique _ _ hv (leaderBA_decides s hs' hrel p),
      Decides.unique _ _ hw (leaderBA_decides s hs' hrel q)]

/-- Theorem 2.1 is not vacuous: SmallCouncil composed with `leaderBA` (for `t = 0`). -/
example : Solves ⊤ (smallCouncil 0 (leaderBA (n := n))) (atMost 0) BA :=
  theorem_2_1_consensus (k := 3) 0 leaderBA le_rfl (by simpa using NeZero.pos n) leaderBA_solves

end Podc.NullMessagesByzantine
