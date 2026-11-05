import Papers.PODC2019.PaxosRaftRefinement.RaftStar

/-!
# Raft* as printed is not safe: two concrete counterexamples

Two explicit executions of the Raft* transition system (`RaftStar.lean`) with five servers,
majority quorums and values in `Fin 4` that end in a state violating state machine safety
(`CommitSafe`):

* `fig2_not_commitSafe` — **Figure 2 literally** (`Rules.fig2`). Every `AppendEntries` in the run
  carries a value, so the culprit is the printed vote rule alone: a voter compares *its entry at
  the candidate's last index* (not its last entry) with the candidate's last term, so it may vote
  for a candidate whose log is behind its own. `fig2_voter_reports_higher_term` isolates the
  moment: just before the second election of `C`, voter `B` reports a log whose last term `3`
  exceeds `C`'s last term `2` while disagreeing with `C` at index `0`. This refutes step 4.2 of
  the proof in Appendix C ("`s.instances[0, s.lastIndex]` is already the safe entries").
* `heartbeat_not_commitSafe` — Raft's **own** vote rule (`raftVoteOK`, the TLA+ spec B.2) but
  `AppendEntries` with no new value allowed (Figure 2 does not exclude `vals = []`): Raft's
  "Figure 8" scenario. A leader commits an entry of an older term by counting replicas of a
  heartbeat in its current term, without any entry of its current term in the log.

Servers `A, B, C, D, E` (resp. `S1, …, S5`) are `0, …, 4`; values `x, y, z, w` (resp. `a, b, c`)
are `0, 1, 2, 3`. Each run is split into phases; a phase lemma ends in an explicit snapshot
(`Snap`) of the servers' terms, leader flags, logs and commit lengths, from which the next phase
continues (this keeps the terms small).
-/

namespace Podc.PaxosRaftRefinement

namespace Raft

open Relation
open scoped Classical

namespace Counterex

/-- Majority quorums of five servers. -/
abbrev Q5 : QuorumSystem (Fin 5) := QuorumSystem.majority (Fin 5)

/-- A snapshot of the local states (term, leader flag, log, commit length) of five servers. -/
def Snap (r : State (Fin 5) (Fin 4)) (t : Fin 5 → ℕ) (l : Fin 5 → Bool)
    (g : Fin 5 → List (ℕ × Fin 4)) (c : Fin 5 → ℕ) : Prop :=
  r.term = t ∧ r.leader = l ∧ r.log = g ∧ r.commit = c

/-- Raft's own vote rule, with heartbeats (`AppendEntries` with no value) allowed. -/
abbrev raftHB : Rules (Fin 4) := ⟨raftVoteOK, True⟩

end Counterex

open Counterex

/-- `vote s d t L`: the `requestVoteOK` of voter `s` for candidate `d` in term `t`, with log `L`. -/
local notation "vote" => @RVOKMsg.mk (Fin 5) (Fin 4)
/-- `aeok s d t n`: the `appendOK` of follower `s` to leader `d` in term `t`, log length `n`. -/
local notation "aeok" => @AEOKMsg.mk (Fin 5)

/-- Discharges the guard of a concrete step by evaluation (with the snapshot equations given). -/
local syntax "step_guard" (" [" Lean.Parser.Tactic.simpArg,* "]")? : tactic
macro_rules
  | `(tactic| step_guard) => `(tactic| step_guard [])
  | `(tactic| step_guard [$args,*]) =>
    `(tactic| (try clear $(Lean.mkIdent `h)); simp (config := {decide := true}) [init, lastTerm,
      termAt, Function.update_apply, Rules.fig2, fig2VoteOK, raftVoteOK, ExtOK, PrevMatch, Counterex.Q5,
      QuorumSystem.majority, Finset.mem_insert, forall_eq_or_imp, $args,*])

/-- Proves the snapshot of a concrete state. -/
local syntax "snap" (" [" Lean.Parser.Tactic.simpArg,* "]")? : tactic
macro_rules
  | `(tactic| snap) => `(tactic| snap [])
  | `(tactic| snap [$args,*]) =>
    `(tactic| (refine ⟨?_, ?_, ?_, ?_⟩ <;> funext i <;> fin_cases i <;>
      simp [init, lastTerm, Function.update_apply, $args,*]))

/-! ### Figure 2 as printed -/

/-- Phase 1: `A` is elected in term 1 by `{A, B, D, E}` and appends `x`; nobody receives it. -/
theorem Counterex.fig2_phase1 : ∃ r, Reachable Q5 Rules.fig2 r ∧
    Snap r ![1, 1, 0, 1, 1] ![true, false, false, false, false]
      ![[(1, 0)], [], [], [], []] ![0, 0, 0, 0, 0] := by
  have h : Reachable Q5 (Rules.fig2 (V := Fin 4)) init := .refl
  replace h := h.tail (Step.requestVote _ 0)
  replace h := h.tail (Step.receiveVote _ 1 ⟨0, 1, 0, 0⟩ (by step_guard) (by step_guard) (by step_guard))
  replace h := h.tail (Step.receiveVote _ 3 ⟨0, 1, 0, 0⟩ (by step_guard) (by step_guard) (by step_guard))
  replace h := h.tail (Step.receiveVote _ 4 ⟨0, 1, 0, 0⟩ (by step_guard) (by step_guard) (by step_guard))
  replace h := h.tail (Step.becomeLeader _ 0
    {vote 0 0 1 [], vote 1 0 1 [], vote 3 0 1 [], vote 4 0 1 []} []
    (by step_guard) (by step_guard) (by step_guard) (by step_guard) (by step_guard))
  replace h := h.tail (Step.appendEntries _ 0 [0] 0 (by step_guard) (by step_guard) (by step_guard))
  exact ⟨_, h, by snap⟩

/-- Phase 2: `C` is elected in term 2 by `{C, B, D, E}` and appends `y`; nobody receives it. -/
theorem Counterex.fig2_phase2 : ∃ r, Reachable Q5 Rules.fig2 r ∧
    Snap r ![1, 2, 2, 2, 2] ![true, false, true, false, false]
      ![[(1, 0)], [], [(2, 1)], [], []] ![0, 0, 0, 0, 0] := by
  obtain ⟨r, h, ht, hl, hg, hc⟩ := fig2_phase1
  replace h := h.tail (Step.requestVote r 2)
  replace h := h.tail (Step.requestVote _ 2)
  replace h := h.tail (Step.receiveVote _ 1 ⟨2, 2, 0, 0⟩ (by step_guard [ht, hg]) (by step_guard [ht])
    (by step_guard [hg]))
  replace h := h.tail (Step.receiveVote _ 3 ⟨2, 2, 0, 0⟩ (by step_guard [ht, hg]) (by step_guard [ht])
    (by step_guard [hg]))
  replace h := h.tail (Step.receiveVote _ 4 ⟨2, 2, 0, 0⟩ (by step_guard [ht, hg]) (by step_guard [ht])
    (by step_guard [hg]))
  replace h := h.tail (Step.becomeLeader _ 2
    {vote 2 2 2 [], vote 1 2 2 [], vote 3 2 2 [], vote 4 2 2 []} []
    (by step_guard [hl]) (by step_guard [ht, hg]) (by step_guard) (by step_guard) (by step_guard [hg]))
  replace h := h.tail (Step.appendEntries _ 2 [1] 0 (by step_guard) (by step_guard) (by step_guard))
  exact ⟨_, h, by snap [ht, hl, hg, hc]⟩

/-- Phase 3: `A` is elected in term 3 by `{A, B, D, E}` (their logs are empty), appends `z`
(sending its whole log `[(1,x), (3,z)]`), `B, D, E` accept it and `A` commits both entries. -/
theorem Counterex.fig2_phase3 : ∃ r, Reachable Q5 Rules.fig2 r ∧
    Snap r ![3, 3, 2, 3, 3] ![true, false, true, false, false]
      ![[(1, 0), (3, 2)], [(1, 0), (3, 2)], [(2, 1)], [(1, 0), (3, 2)], [(1, 0), (3, 2)]]
      ![2, 0, 0, 0, 0] := by
  obtain ⟨r, h, ht, hl, hg, hc⟩ := fig2_phase2
  replace h := h.tail (Step.requestVote r 0)
  replace h := h.tail (Step.requestVote _ 0)
  replace h := h.tail (Step.receiveVote _ 1 ⟨0, 3, 1, 1⟩ (by step_guard [ht, hg]) (by step_guard [ht])
    (by step_guard [hg]))
  replace h := h.tail (Step.receiveVote _ 3 ⟨0, 3, 1, 1⟩ (by step_guard [ht, hg]) (by step_guard [ht])
    (by step_guard [hg]))
  replace h := h.tail (Step.receiveVote _ 4 ⟨0, 3, 1, 1⟩ (by step_guard [ht, hg]) (by step_guard [ht])
    (by step_guard [hg]))
  replace h := h.tail (Step.becomeLeader _ 0
    {vote 0 0 3 [(1, 0)], vote 1 0 3 [], vote 3 0 3 [], vote 4 0 3 []} []
    (by step_guard [hl]) (by step_guard [ht, hg]) (by step_guard) (by step_guard) (by step_guard [hg]))
  replace h := h.tail (Step.appendEntries _ 0 [2] 0 (by step_guard) (by step_guard) (by step_guard))
  replace h := h.tail (Step.receiveAppend _ 1 ⟨0, 3, 0, [(1, 0), (3, 2)], 0⟩ (by step_guard [ht, hg, hc])
    (by step_guard [ht]) (by step_guard [hg]) (by step_guard) (by step_guard [hg]))
  replace h := h.tail (Step.receiveAppend _ 3 ⟨0, 3, 0, [(1, 0), (3, 2)], 0⟩ (by step_guard [ht, hg, hc])
    (by step_guard [ht]) (by step_guard [hg]) (by step_guard) (by step_guard [hg]))
  replace h := h.tail (Step.receiveAppend _ 4 ⟨0, 3, 0, [(1, 0), (3, 2)], 0⟩ (by step_guard [ht, hg, hc])
    (by step_guard [ht]) (by step_guard [hg]) (by step_guard) (by step_guard [hg]))
  replace h := h.tail (Step.leaderLearn _ 0 {aeok 1 0 3 2, aeok 3 0 3 2} 2
    (by step_guard [hl]) (by step_guard [ht]) (by step_guard) (by step_guard) (by step_guard [hg]))
  exact ⟨_, h, by snap [ht, hl, hg, hc]⟩

/-- Phase 4a: `C` asks for votes in term 4 (last index 0, last term 2); `B, D, E` grant them by
the printed rule, since their entry at index 0 has term `1 < 2`. -/
theorem Counterex.fig2_phase4a : ∃ r, Reachable Q5 Rules.fig2 r ∧
    Snap r ![3, 4, 4, 4, 4] ![true, false, false, false, false]
      ![[(1, 0), (3, 2)], [(1, 0), (3, 2)], [(2, 1)], [(1, 0), (3, 2)], [(1, 0), (3, 2)]]
      ![2, 0, 0, 0, 0] ∧
    vote 2 2 4 [(2, 1)] ∈ r.rvok ∧ vote 1 2 4 [(1, 0), (3, 2)] ∈ r.rvok ∧
    vote 3 2 4 [(1, 0), (3, 2)] ∈ r.rvok ∧ vote 4 2 4 [(1, 0), (3, 2)] ∈ r.rvok := by
  obtain ⟨r, h, ht, hl, hg, hc⟩ := fig2_phase3
  replace h := h.tail (Step.requestVote r 2)
  replace h := h.tail (Step.requestVote _ 2)
  replace h := h.tail (Step.receiveVote _ 1 ⟨2, 4, 1, 2⟩ (by step_guard [ht, hg]) (by step_guard [ht])
    (by step_guard [hg]))
  replace h := h.tail (Step.receiveVote _ 3 ⟨2, 4, 1, 2⟩ (by step_guard [ht, hg]) (by step_guard [ht])
    (by step_guard [hg]))
  replace h := h.tail (Step.receiveVote _ 4 ⟨2, 4, 1, 2⟩ (by step_guard [ht, hg]) (by step_guard [ht])
    (by step_guard [hg]))
  exact ⟨_, h, by snap [ht, hl, hg, hc], by step_guard [ht, hg], by step_guard [ht, hg], by step_guard [ht, hg],
    by step_guard [ht, hg]⟩

/-- Phase 4b: `C` becomes leader with votes `{C, B, D, E}`, extends its log by the safe entry `z`
at index 1, appends `w`, `B, D` accept, and `C` commits its three entries. -/
theorem Counterex.fig2_phase4b : ∃ r, Reachable Q5 Rules.fig2 r ∧
    Snap r ![3, 4, 4, 4, 4] ![true, false, true, false, false]
      ![[(1, 0), (3, 2)], [(2, 1), (4, 2), (4, 3)], [(2, 1), (4, 2), (4, 3)],
        [(2, 1), (4, 2), (4, 3)], [(1, 0), (3, 2)]]
      ![2, 0, 3, 0, 0] := by
  obtain ⟨r, h, ⟨ht, hl, hg, hc⟩, h1, h2, h3, h4⟩ := fig2_phase4a
  replace h := h.tail (Step.becomeLeader r 2
    {vote 2 2 4 [(2, 1)], vote 1 2 4 [(1, 0), (3, 2)], vote 3 2 4 [(1, 0), (3, 2)],
      vote 4 2 4 [(1, 0), (3, 2)]} [2]
    (by step_guard [hl]) (by step_guard [ht, h1, h2, h3, h4]) (by step_guard) (by step_guard) (by step_guard [hg]))
  replace h := h.tail (Step.appendEntries _ 2 [3] 0 (by step_guard) (by step_guard) (by step_guard))
  replace h := h.tail (Step.receiveAppend _ 1 ⟨2, 4, 0, [(2, 1), (4, 2), (4, 3)], 0⟩
    (by step_guard [ht, hg, hc]) (by step_guard [ht]) (by step_guard [hg]) (by step_guard) (by step_guard [hg]))
  replace h := h.tail (Step.receiveAppend _ 3 ⟨2, 4, 0, [(2, 1), (4, 2), (4, 3)], 0⟩
    (by step_guard [ht, hg, hc]) (by step_guard [ht]) (by step_guard [hg]) (by step_guard) (by step_guard [hg]))
  replace h := h.tail (Step.leaderLearn _ 2 {aeok 1 2 4 3, aeok 3 2 4 3} 3
    (by step_guard [hl]) (by step_guard [ht]) (by step_guard) (by step_guard) (by step_guard [hg]))
  exact ⟨_, h, by snap [ht, hl, hg, hc]⟩

/-- **Figure 2 of [paper], as printed, violates state machine safety.** With five servers and
majority quorums, a reachable state of Raft* under the printed rules has two committed logs
disagreeing at index 0 (`A` committed `x`, `C` committed `y`). No `AppendEntries` of the run is a
heartbeat: the printed vote rule alone is to blame. -/
theorem fig2_not_commitSafe :
    ∃ r, Reachable (QuorumSystem.majority (Fin 5)) (Rules.fig2 (V := Fin 4)) r ∧ ¬ CommitSafe r := by
  obtain ⟨r, h, ht, hl, hg, hc⟩ := fig2_phase4b
  refine ⟨r, h, fun hs => ?_⟩
  have := hs 0 2 0 (by simp [hg]) (by simp [hg]) (by simp [hc]) (by simp [hc])
  simp [hg] at this

/-- The essential point of `fig2_not_commitSafe`: just before `C`'s second election, voter `B`
has sent `C` a vote whose log `[(1,x), (3,z)]` has last term `3`, larger than the last term `2`
of `C`'s own log `[(2,y)]`, and disagrees with it at index `0`; `x` at index `0` is already
committed by `A`. So the candidate's own entries are *not* the safe entries, contradicting
step 4.2 of the proof in Appendix C of [paper]. -/
theorem fig2_voter_reports_higher_term :
    ∃ r, Reachable (QuorumSystem.majority (Fin 5)) (Rules.fig2 (V := Fin 4)) r ∧
      r.term 2 = 4 ∧ r.log 2 = [(2, 1)] ∧ vote 1 2 4 [(1, 0), (3, 2)] ∈ r.rvok ∧
      lastTerm (r.log 2) < lastTerm [((1 : ℕ), (0 : Fin 4)), (3, 2)] ∧
      ((r.log 2)[0]?).map Prod.snd ≠ ([((1 : ℕ), (0 : Fin 4)), (3, 2)][0]?).map Prod.snd ∧
      r.log 0 = [(1, 0), (3, 2)] ∧ 0 < r.commit 0 := by
  obtain ⟨r, h, ⟨ht, hl, hg, hc⟩, h1, h2, h3, h4⟩ := fig2_phase4a
  exact ⟨r, h, by simp [ht], by simp [hg], h2, by simp [hg, lastTerm], by simp [hg],
    by simp [hg], by simp [hc]⟩

/-! ### Raft's vote rule with heartbeats: Raft's "Figure 8" -/

/-- Phase 1: `S1` is elected in term 1 by `{S1, S2, S3}`, appends `a`, and `S2` receives it. -/
theorem Counterex.hb_phase1 : ∃ r, Reachable Q5 raftHB r ∧
    Snap r ![1, 1, 1, 0, 0] ![true, false, false, false, false]
      ![[(1, 0)], [(1, 0)], [], [], []] ![0, 0, 0, 0, 0] := by
  have h : Reachable Q5 raftHB init := .refl
  replace h := h.tail (Step.requestVote _ 0)
  replace h := h.tail (Step.receiveVote _ 1 ⟨0, 1, 0, 0⟩ (by step_guard) (by step_guard) (by step_guard))
  replace h := h.tail (Step.receiveVote _ 2 ⟨0, 1, 0, 0⟩ (by step_guard) (by step_guard) (by step_guard))
  replace h := h.tail (Step.becomeLeader _ 0 {vote 0 0 1 [], vote 1 0 1 [], vote 2 0 1 []} []
    (by step_guard) (by step_guard) (by step_guard) (by step_guard) (by step_guard))
  replace h := h.tail (Step.appendEntries _ 0 [0] 0 (by step_guard) (by step_guard) (by step_guard))
  replace h := h.tail (Step.receiveAppend _ 1 ⟨0, 1, 0, [(1, 0)], 0⟩ (by step_guard) (by step_guard)
    (by step_guard) (by step_guard) (by step_guard))
  exact ⟨_, h, by snap⟩

/-- Phase 2: `S5` is elected in term 2 by `{S5, S3, S4}` and appends `b`; nobody receives it. -/
theorem Counterex.hb_phase2 : ∃ r, Reachable Q5 raftHB r ∧
    Snap r ![1, 1, 2, 2, 2] ![true, false, false, false, true]
      ![[(1, 0)], [(1, 0)], [], [], [(2, 1)]] ![0, 0, 0, 0, 0] := by
  obtain ⟨r, h, ht, hl, hg, hc⟩ := hb_phase1
  replace h := h.tail (Step.requestVote r 4)
  replace h := h.tail (Step.requestVote _ 4)
  replace h := h.tail (Step.receiveVote _ 2 ⟨4, 2, 0, 0⟩ (by step_guard [ht, hg]) (by step_guard [ht])
    (by step_guard [hg]))
  replace h := h.tail (Step.receiveVote _ 3 ⟨4, 2, 0, 0⟩ (by step_guard [ht, hg]) (by step_guard [ht])
    (by step_guard [hg]))
  replace h := h.tail (Step.becomeLeader _ 4 {vote 4 4 2 [], vote 2 4 2 [], vote 3 4 2 []} []
    (by step_guard [hl]) (by step_guard [ht, hg]) (by step_guard) (by step_guard) (by step_guard [hg]))
  replace h := h.tail (Step.appendEntries _ 4 [1] 0 (by step_guard) (by step_guard) (by step_guard))
  exact ⟨_, h, by snap [ht, hl, hg, hc]⟩

/-- Phase 3: `S1` is elected in term 3 by `{S1, S2, S3}`, sends a heartbeat (no new value) with
its log `[(1,a)]`, `S2, S3` accept it and `S1` commits `a` at index 0. -/
theorem Counterex.hb_phase3 : ∃ r, Reachable Q5 raftHB r ∧
    Snap r ![3, 3, 3, 2, 2] ![true, false, false, false, true]
      ![[(1, 0)], [(1, 0)], [(1, 0)], [], [(2, 1)]] ![1, 0, 0, 0, 0] := by
  obtain ⟨r, h, ht, hl, hg, hc⟩ := hb_phase2
  replace h := h.tail (Step.requestVote r 0)
  replace h := h.tail (Step.requestVote _ 0)
  replace h := h.tail (Step.receiveVote _ 1 ⟨0, 3, 1, 1⟩ (by step_guard [ht, hg]) (by step_guard [ht])
    (by step_guard [hg]))
  replace h := h.tail (Step.receiveVote _ 2 ⟨0, 3, 1, 1⟩ (by step_guard [ht, hg]) (by step_guard [ht])
    (by step_guard [hg]))
  replace h := h.tail (Step.becomeLeader _ 0
    {vote 0 0 3 [(1, 0)], vote 1 0 3 [(1, 0)], vote 2 0 3 []} []
    (by step_guard [hl]) (by step_guard [ht, hg]) (by step_guard) (by step_guard) (by step_guard [hg]))
  -- the heartbeat: no new value
  replace h := h.tail (Step.appendEntries _ 0 [] 0 (by step_guard) (by step_guard) (by step_guard))
  replace h := h.tail (Step.receiveAppend _ 1 ⟨0, 3, 0, [(1, 0)], 0⟩ (by step_guard [ht, hg, hc])
    (by step_guard [ht]) (by step_guard [hg]) (by step_guard) (by step_guard [hg]))
  replace h := h.tail (Step.receiveAppend _ 2 ⟨0, 3, 0, [(1, 0)], 0⟩ (by step_guard [ht, hg, hc])
    (by step_guard [ht]) (by step_guard [hg]) (by step_guard) (by step_guard [hg]))
  replace h := h.tail (Step.leaderLearn _ 0 {aeok 1 0 3 1, aeok 2 0 3 1} 1
    (by step_guard [hl]) (by step_guard [ht]) (by step_guard) (by step_guard) (by step_guard [hg]))
  exact ⟨_, h, by snap [ht, hl, hg, hc]⟩

/-- Phase 4: `S5` is elected in term 4 by `{S5, S2, S3}` (their last term `1 < 2`), appends `c`,
`S2, S3` accept (overwriting `a`), and `S5` commits `[(2,b), (4,c)]`. -/
theorem Counterex.hb_phase4 : ∃ r, Reachable Q5 raftHB r ∧
    Snap r ![3, 4, 4, 2, 4] ![true, false, false, false, true]
      ![[(1, 0)], [(2, 1), (4, 2)], [(2, 1), (4, 2)], [], [(2, 1), (4, 2)]]
      ![1, 0, 0, 0, 2] := by
  obtain ⟨r, h, ht, hl, hg, hc⟩ := hb_phase3
  replace h := h.tail (Step.requestVote r 4)
  replace h := h.tail (Step.requestVote _ 4)
  replace h := h.tail (Step.receiveVote _ 1 ⟨4, 4, 1, 2⟩ (by step_guard [ht, hg]) (by step_guard [ht])
    (by step_guard [hg]))
  replace h := h.tail (Step.receiveVote _ 2 ⟨4, 4, 1, 2⟩ (by step_guard [ht, hg]) (by step_guard [ht])
    (by step_guard [hg]))
  replace h := h.tail (Step.becomeLeader _ 4
    {vote 4 4 4 [(2, 1)], vote 1 4 4 [(1, 0)], vote 2 4 4 [(1, 0)]} []
    (by step_guard [hl]) (by step_guard [ht, hg]) (by step_guard) (by step_guard) (by step_guard [hg]))
  replace h := h.tail (Step.appendEntries _ 4 [2] 0 (by step_guard) (by step_guard) (by step_guard))
  replace h := h.tail (Step.receiveAppend _ 1 ⟨4, 4, 0, [(2, 1), (4, 2)], 0⟩
    (by step_guard [ht, hg, hc]) (by step_guard [ht]) (by step_guard [hg]) (by step_guard) (by step_guard [hg]))
  replace h := h.tail (Step.receiveAppend _ 2 ⟨4, 4, 0, [(2, 1), (4, 2)], 0⟩
    (by step_guard [ht, hg, hc]) (by step_guard [ht]) (by step_guard [hg]) (by step_guard) (by step_guard [hg]))
  replace h := h.tail (Step.leaderLearn _ 4 {aeok 1 4 4 2, aeok 2 4 4 2} 2
    (by step_guard [hl]) (by step_guard [ht]) (by step_guard) (by step_guard) (by step_guard [hg]))
  exact ⟨_, h, by snap [ht, hl, hg, hc]⟩

/-- **Raft's vote rule is not enough if `AppendEntries` may be empty** (Raft's "Figure 8"
scenario). With Raft's up-to-date check but heartbeats allowed, as Figure 2 of [paper] allows,
Raft* violates state machine safety: `S1` commits `a` and `S5` commits `b` at index 0. -/
theorem heartbeat_not_commitSafe :
    ∃ r, Reachable (QuorumSystem.majority (Fin 5)) (⟨raftVoteOK, True⟩ : Rules (Fin 4)) r ∧
      ¬ CommitSafe r := by
  obtain ⟨r, h, ht, hl, hg, hc⟩ := hb_phase4
  refine ⟨r, h, fun hs => ?_⟩
  have := hs 0 4 0 (by simp [hg]) (by simp [hg]) (by simp [hc]) (by simp [hc])
  simp [hg] at this

end Raft

end Podc.PaxosRaftRefinement
