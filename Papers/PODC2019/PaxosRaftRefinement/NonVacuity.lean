import Papers.PODC2019.PaxosRaftRefinement.Counterexamples
import Papers.PODC2019.PaxosRaftRefinement.Refinement

/-!
# Non-vacuity of the refinement theorem

Repaired Raft* (`Rules.repaired`) does commit entries: with five servers, `A` is elected in term 1
by `{A, B, D}`, appends `x`, `B` and `D` accept and `A` commits it. The safety theorem
`raftStar_commitSafe` therefore speaks about runs with non-trivial commits.
-/

namespace Podc.PaxosRaftRefinement.Raft

open Relation Counterex
open scoped Classical

/-- `vote s d t L`: a `requestVoteOK`. -/
local notation "vote" => @RVOKMsg.mk (Fin 5) (Fin 4)
/-- `aeok s d t n`: an `appendOK`. -/
local notation "aeok" => @AEOKMsg.mk (Fin 5)

/-- Discharges the guard of a concrete step by evaluation. -/
local syntax "guard_r" (" [" Lean.Parser.Tactic.simpArg,* "]")? : tactic
macro_rules
  | `(tactic| guard_r) => `(tactic| guard_r [])
  | `(tactic| guard_r [$args,*]) =>
    `(tactic| (try clear $(Lean.mkIdent `h)); simp (config := {decide := true}) [init, lastTerm,
      termAt, Function.update_apply, Rules.repaired, ExtOK, PrevMatch, Counterex.Q5,
      QuorumSystem.majority, Finset.mem_insert, forall_eq_or_imp, $args,*])

/-- A reachable state of repaired Raft* in which server `A` has committed one entry. -/
theorem repaired_commits : ∃ r, Reachable Q5 (Rules.repaired (V := Fin 4)) r ∧ r.commit 0 = 1 := by
  have h : Reachable Q5 (Rules.repaired (V := Fin 4)) init := .refl
  replace h := h.tail (Step.requestVote _ 0)
  replace h := h.tail (Step.receiveVote _ 1 ⟨0, 1, 0, 0⟩ (by guard_r) (by guard_r) (by guard_r))
  replace h := h.tail (Step.receiveVote _ 3 ⟨0, 1, 0, 0⟩ (by guard_r) (by guard_r) (by guard_r))
  replace h := h.tail (Step.becomeLeader _ 0
    {vote 0 0 1 [], vote 1 0 1 [], vote 3 0 1 []} []
    (by guard_r) (by guard_r) (by guard_r) (by guard_r) (by guard_r))
  replace h := h.tail (Step.appendEntries _ 0 [0] 0 (by guard_r) (by guard_r) (by guard_r))
  replace h := h.tail (Step.receiveAppend _ 1 ⟨0, 1, 0, [(1, 0)], 0⟩ (by guard_r)
    (by guard_r) (by guard_r) (by guard_r) (by guard_r))
  replace h := h.tail (Step.receiveAppend _ 3 ⟨0, 1, 0, [(1, 0)], 0⟩ (by guard_r)
    (by guard_r) (by guard_r) (by guard_r) (by guard_r))
  replace h := h.tail (Step.leaderLearn _ 0 {aeok 1 0 1 1, aeok 3 0 1 1} 1
    (by guard_r) (by guard_r) (by guard_r) (by guard_r) (by guard_r))
  exact ⟨_, h, by simp [Function.update_apply, init]⟩

end Podc.PaxosRaftRefinement.Raft
