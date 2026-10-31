import Papers.PODC2012.GeneralizedLatticeAgreement.Safety

/-!
# Theorem 5.15 is false: a received value that is never learnt

Three processes `0, 1, 2`, each playing all three roles (proposer, acceptor, learner), as in the
paper's Section 6. Process `2` is faulty; `0` and `1` are correct (a majority). The lattice is
`Finset ℕ` (the power-set lattice used throughout the paper).

Process `2`'s acceptor acknowledges proposer `0`'s proposal `{1,2}` and crashes in the middle of
this `Accept` step: its `ACK` reaches proposer `0` (which decides) but not the learners. The
third acceptor (process `1`) rejects `{1,2}`, because it had already accepted `{3}` (from process
`2`). So the learners see only one `ACK` for `{1,2}`, and the proposers, both passive and with
their buffers already included in their `proposedValue`s (through late `NACK`s), never propose
again. The learners keep `learntValue = {2}`, and the value `{1}` received by the correct process
`0` is never learnt.

Apart from that last `ACK` of the crashing acceptor, every message sent to a correct process is
processed (`all_delivered`), so the counterexample needs neither message loss nor any unusual
scheduling: the paper's model explicitly allows "a process may fail in the middle of an
execution step".
-/

namespace Podc.GeneralizedLatticeAgreement.Cex515

open Podc.GeneralizedLatticeAgreement Action

/-- Process identities (each process plays all roles). -/
abbrev N := Fin 3
/-- Values: the power-set lattice. -/
abbrev V := Finset ℕ

/-- Process `2` is faulty, `0` and `1` are correct. -/
def corr : N ⊕ N ⊕ N → Prop
  | .inl i | .inr (.inl i) | .inr (.inr i) => i ≠ 2

instance : DecidablePred corr := fun r => by
  rcases r with i | i | i <;> simp only [corr] <;> infer_instance

/-- The schedule. -/
def tr : List (Action N N N V) := [
  -- process 2 receives {3}, proposes it; acceptor 1 accepts it
  receive 2 {3}, propose 2, accept 1 2 1 {3},
  -- process 0 receives {1}, process 1 receives {2}; process 1 proposes {2}
  receive 0 {1}, receive 1 {2}, propose 1,
  accept 0 1 1 {2}, accept 2 1 1 {2},
  processAck 1 0 1 {2}, processAck 1 2 1 {2}, decide 1,
  -- the learners learn {2}
  learn 0 0 1 1 {2}, learn 0 2 1 1 {2}, learn 1 0 1 1 {2}, learn 1 2 1 1 {2},
  -- process 0 proposes {1,2}; acceptor 2 acknowledges it and crashes (its ACK reaches only
  -- proposer 0); proposer 0 decides
  buffer 0 1 {2}, propose 0,
  accept 0 0 1 {1, 2}, accept 2 0 1 {1, 2},
  processAck 0 0 1 {1, 2}, processAck 0 2 1 {1, 2}, decide 0,
  -- acceptor 1 rejects both proposals; the late NACKs are processed by the passive proposers
  reject 1 0 1 {1, 2}, processNack 0 1 1 {1, 2, 3},
  reject 1 1 1 {2}, processNack 1 1 1 {1, 2, 3},
  -- remaining InternalReceive messages and proposals are processed
  buffer 0 2 {3}, buffer 1 0 {1}, buffer 1 2 {3},
  reject 0 2 1 {3},
  -- remaining ACKs of correct acceptors reach the learners
  learn 0 0 0 1 {1, 2}, learn 1 0 0 1 {1, 2},
  learn 0 1 2 1 {3}, learn 1 1 2 1 {3}]

/-- The message lost because acceptor `2` crashes in the middle of its `Accept` step. -/
def lostAck : Msg N N V := .ack 2 0 1 {1, 2}

/-- Every message sent to a correct process has been processed by it, except the copies of
`lostAck` for the learners (`lostAck` itself did reach proposer `0`). -/
def AllDelivered (s : State N N N V) : Prop :=
  (0 : N) ∈ (s.prop 0).acks 1 ∧
  ∀ m ∈ s.sent, match m with
    | .proposal p n _ => ∀ a : N, a ≠ 2 → (p, n) ∈ s.adone a
    | .ack a p n v => (p ≠ 2 → a ∈ (s.prop p).acks n) ∧
        (Msg.ack a p n v ≠ lostAck → ∀ l : N, l ≠ 2 → a ∈ s.lacks l p n)
    | .nack a p n _ => p ≠ 2 → a ∈ (s.prop p).nacks n
    | .internal q v => ∀ p : N, p ≠ 2 → p ≠ q → (q, v) ∈ (s.prop p).seen

instance (s : State N N N V) : Decidable (AllDelivered s) := by
  unfold AllDelivered
  refine instDecidableAnd (dq := ?_)
  refine Finset.decidableDforallFinset (_hp := fun m _ => ?_)
  cases m <;> dsimp only <;> infer_instance

/-- The run succeeds and ends in a quiescent state where the learners have learnt `{2}`, and
all messages except the learners' copies of `lostAck` were delivered. -/
lemma run_tr : ((run (initState (A := N) (Ln := N) fun _ : N => (⊥ : V)) tr).elim false fun s =>
    decide (Quiescent corr s ∧ s.learnt 0 = {2} ∧ s.learnt 1 = {2} ∧ AllDelivered s)) =
      true := by
  decide +kernel

/-- **Theorem 5.15 of [paper] is false** (and so is the claim that Algorithm 2 solves generalized
lattice agreement with liveness). In a fair execution with three processes (each a proposer, an
acceptor and a learner), one of which crashes, the value `{1}` received by the correct process `0`
is never included in the `learntValue` of the correct learner `0`. -/
theorem theorem_5_15_false :
    ∃ e : Exec (P := N) (A := N) (Ln := N) (L := V) (fun _ => ⊥),
      LivenessAssumptions corr ∧ e.Fair corr ∧ e.CrashStop corr ∧
      (∀ t, e.act t = some (.receive 0 {1}) → t = 3) ∧ e.act 3 = some (.receive 0 {1}) ∧
      (∀ t, ¬ ({1} : V) ≤ (e.st t).learnt 0) ∧ ¬ e.GLALiveness corr := by
  have h := run_tr
  cases hr : run (initState (A := N) (Ln := N) fun _ : N => (⊥ : V)) tr with
  | none => rw [hr] at h; simp at h
  | some s =>
    rw [hr] at h
    simp only [Option.elim, decide_eq_true_eq] at h
    obtain ⟨hq, h0, -⟩ := h
    have hnever : ∀ t, ¬ ({1} : V) ≤ ((Exec.ofRun _ tr s hr).st t).learnt 0 := by
      intro t ht
      have hm := (Exec.ofRun _ tr s hr).learnt_mono 0 (le_max_left t tr.length)
      rw [Exec.ofRun_st_of_le hr (le_max_right _ _), h0] at hm
      exact absurd (ht.trans hm) (by decide)
    let isR : Action N N N V → Bool
      | .receive p v => decide (p = 0 ∧ v = {1})
      | _ => false
    have key' : ∀ i ∈ List.range tr.length, i ≠ 3 → tr[i]?.any isR = false := by
      decide +kernel
    have key : ∀ i ∈ List.range tr.length, i ≠ 3 → tr[i]? ≠ some (Action.receive 0 {1}) := by
      intro i hi h3 he
      have := key' i hi h3
      rw [he] at this
      simp [isR] at this
    refine ⟨Exec.ofRun _ tr s hr, ⟨by decide, ⟨0, by decide⟩, ⟨0, by decide⟩⟩,
      Exec.ofRun_fair hr hq,
      Exec.ofRun_crashStop hr _, ?_, rfl, hnever, ?_⟩
    · intro t ht
      by_contra hne
      by_cases hlt : t < tr.length
      · exact key t (List.mem_range.2 hlt) hne ht
      · rw [Exec.ofRun_act_of_le hr (by omega)] at ht; cases ht
    · intro hl
      obtain ⟨t, ht⟩ := hl 0 {1} (by decide) ⟨3, rfl⟩ 0 (by decide)
      exact hnever t ht

end Podc.GeneralizedLatticeAgreement.Cex515

/-!
## A second counterexample: reliable channels, a clean crash

Again three processes with all roles, process `2` faulty. This time process `2` crashes *between*
two steps and **every message sent to a correct process is processed** (`AllDeliveredB`): the
channels are reliable even for the faulty process. The price is a non-singleton input value: the
correct process `0` receives `{1,2}` after it has absorbed `{1,2}` into its `proposedValue`
through a late `NACK` (a join of its own proposal `{1}` with the faulty process's `{2}`). So its
`Propose` guard stays false, `{1,2}` is never part of any proposal (refuting Lemma 5.14 as well),
and the learners keep `learntValue = {1}`.
-/

namespace Podc.GeneralizedLatticeAgreement.Cex515b

open Podc.GeneralizedLatticeAgreement Action
open Podc.GeneralizedLatticeAgreement.Cex515 (N V corr)

/-- The schedule. Process `2` takes its last step at `reject 2 1 1 {1}`. -/
def tr : List (Action N N N V) := [
  receive 2 {2}, propose 2, accept 2 2 1 {2},
  receive 0 {1}, propose 0,
  accept 0 0 1 {1}, accept 1 0 1 {1}, processAck 0 0 1 {1}, processAck 0 1 1 {1}, decide 0,
  reject 2 0 1 {1}, processNack 0 2 1 {1, 2},
  buffer 1 0 {1}, propose 1,
  accept 0 1 1 {1}, accept 1 1 1 {1}, processAck 1 0 1 {1}, processAck 1 1 1 {1}, decide 1,
  reject 2 1 1 {1}, processNack 1 2 1 {1, 2},
  -- process 2 has crashed; its proposal is rejected by acceptors 0 and 1
  reject 0 2 1 {2}, reject 1 2 1 {2},
  -- process 0 receives {1,2}, which is already below its proposedValue
  receive 0 {1, 2},
  buffer 0 2 {2}, buffer 1 2 {2}, buffer 1 0 {1, 2},
  learn 0 2 2 1 {2}, learn 1 2 2 1 {2},
  learn 0 0 0 1 {1}, learn 0 1 0 1 {1}, learn 1 0 0 1 {1}, learn 1 1 0 1 {1},
  learn 0 0 1 1 {1}, learn 0 1 1 1 {1}, learn 1 0 1 1 {1}, learn 1 1 1 1 {1}]

/-- Every message sent (by any process, faulty or not) to a correct process has been processed
by it. -/
def AllDeliveredB (s : State N N N V) : Prop :=
  ∀ m ∈ s.sent, match m with
    | .proposal p n _ => ∀ a : N, a ≠ 2 → (p, n) ∈ s.adone a
    | .ack a p n _ => (p ≠ 2 → a ∈ (s.prop p).acks n) ∧ ∀ l : N, l ≠ 2 → a ∈ s.lacks l p n
    | .nack a p n _ => p ≠ 2 → a ∈ (s.prop p).nacks n
    | .internal q v => ∀ p : N, p ≠ 2 → p ≠ q → (q, v) ∈ (s.prop p).seen

instance (s : State N N N V) : Decidable (AllDeliveredB s) := by
  unfold AllDeliveredB
  refine Finset.decidableDforallFinset (_hp := fun m _ => ?_)
  cases m <;> dsimp only <;> infer_instance

/-- No proposal includes `{1,2}`. -/
def NoProposalAbove (s : State N N N V) : Prop :=
  ∀ m ∈ s.sent, match m with
    | .proposal _ _ v => ¬ ({1, 2} : V) ≤ v
    | _ => True

instance (s : State N N N V) : Decidable (NoProposalAbove s) := by
  unfold NoProposalAbove
  refine Finset.decidableDforallFinset (_hp := fun m _ => ?_)
  cases m <;> dsimp only <;> infer_instance

lemma run_tr : ((run (initState (A := N) (Ln := N) fun _ : N => (⊥ : V)) tr).elim false fun s =>
    decide (Quiescent corr s ∧ s.learnt 0 = {1} ∧ s.learnt 1 = {1} ∧ AllDeliveredB s ∧
      NoProposalAbove s)) = true := by
  decide +kernel

/-- **Theorem 5.15 of [paper] is false even with reliable channels and crashes between steps**,
for inputs that are not singletons. The value `{1,2}`, received by the correct process `0` at
time `23`, is never included in the learnt value of the correct learner `0`, and no proposal ever
includes it (so Lemma 5.14 fails too); in particular no learner ever executes a `Learn(w)` step
with `w ⊒ {1,2}`, so Theorem 5.15 also fails for the paper's literal definition of "learnt". -/
theorem theorem_5_15_false_reliable :
    ∃ e : Exec (P := N) (A := N) (Ln := N) (L := V) (fun _ => ⊥),
      LivenessAssumptions corr ∧ e.Fair corr ∧ e.CrashStop corr ∧
      e.act 23 = some (.receive 0 {1, 2}) ∧
      (∀ t, ¬ ({1, 2} : V) ≤ (e.st t).learnt 0) ∧
      (∀ t p n v, Msg.proposal p n v ∈ (e.st t).sent → ¬ ({1, 2} : V) ≤ v) ∧
      (∀ t l a p n w, e.act t = some (.learn l a p n w) → ¬ ({1, 2} : V) ≤ w) ∧
      ¬ e.GLALiveness corr := by
  have h := run_tr
  cases hr : run (initState (A := N) (Ln := N) fun _ : N => (⊥ : V)) tr with
  | none => rw [hr] at h; simp at h
  | some s =>
    rw [hr] at h
    simp only [Option.elim, decide_eq_true_eq] at h
    obtain ⟨hq, h0, -, -, hprop⟩ := h
    set e := Exec.ofRun _ tr s hr
    have hnever : ∀ t, ¬ ({1, 2} : V) ≤ (e.st t).learnt 0 := by
      intro t ht
      have hm := e.learnt_mono 0 (le_max_left t tr.length)
      rw [Exec.ofRun_st_of_le hr (le_max_right _ _), h0] at hm
      exact absurd (ht.trans hm) (by decide)
    have hnoprop : ∀ t p n v, Msg.proposal p n v ∈ (e.st t).sent → ¬ ({1, 2} : V) ≤ v := by
      intro t p n v hm
      have hm' := e.sent_mono (le_max_left t tr.length) hm
      rw [Exec.ofRun_st_of_le hr (le_max_right _ _)] at hm'
      exact hprop _ hm'
    refine ⟨e, ⟨by decide, ⟨0, by decide⟩, ⟨0, by decide⟩⟩, Exec.ofRun_fair hr hq,
      Exec.ofRun_crashStop hr _, rfl, hnever, hnoprop, ?_, ?_⟩
    · intro t l a p n w ht
      have hst := e.step t
      rw [ht] at hst
      exact hnoprop t p n w ((e.reachable t).inv.ack_prop hst.1.1)
    · intro hl
      obtain ⟨t, ht⟩ := hl 0 {1, 2} (by decide) ⟨23, rfl⟩ 0 (by decide)
      exact hnever t ht

end Podc.GeneralizedLatticeAgreement.Cex515b

/-!
## A third counterexample: singleton inputs, independent of late `NACK`s

Executions 1 and 2 both use that a *passive* proposer still processes late `NACK`s
(`ProcessNACK` checks only `proposalNumber = activeProposalNumber`). One might read a guard
`status = active` into `ProcessNACK` as intended. This execution does not depend on it: the
learners never see a quorum of `ACK`s because the faulty acceptor `2` acknowledges the proposals
of both correct proposers, and its copies of these `ACK`s for the learners are lost (the paper's
assumption (d) only covers messages *between correct processes*; its failure model includes
message loss). Inputs are singletons, and every message from a correct process to a correct
process is processed (`AllCorrectDelivered`). The correct learners stay at `learntValue = ⊥`.

`run_trNoNack` shows that the same schedule without the two late `ProcessNACK` steps is also a
run, ending with both correct proposers passive and nothing to propose; the only messages between
correct processes left unprocessed are the `NACK`s to these passive proposers. So the execution is
also a counterexample for the variant of Algorithm 2 in which passive proposers ignore `NACK`s.
-/

namespace Podc.GeneralizedLatticeAgreement.Cex515c

open Podc.GeneralizedLatticeAgreement Action
open Podc.GeneralizedLatticeAgreement.Cex515 (N V corr)

/-- The schedule before the late `NACK`s. -/
def trPre : List (Action N N N V) := [
  -- process 2 receives {3} and proposes it; acceptor 1 accepts it
  receive 2 {3}, propose 2, accept 1 2 1 {3},
  -- process 0 receives {1} and proposes it; acceptors 0 and 2 acknowledge; proposer 0 decides
  receive 0 {1}, propose 0, accept 0 0 1 {1}, accept 2 0 1 {1},
  processAck 0 0 1 {1}, processAck 0 2 1 {1}, decide 0,
  -- proposer 1 buffers {1} and proposes it; acceptors 0 and 2 acknowledge; proposer 1 decides
  buffer 1 0 {1}, propose 1, accept 0 1 1 {1}, accept 2 1 1 {1},
  processAck 1 0 1 {1}, processAck 1 2 1 {1}, decide 1,
  -- acceptor 1 (holding {3}) rejects both proposals
  reject 1 0 1 {1}, reject 1 1 1 {1}]

/-- The schedule after the late `NACK`s: the learners process all `ACK`s of correct acceptors.
(Acceptor 2's `ACK`s to the learners are lost.) -/
def trPost : List (Action N N N V) := [
  learn 0 0 0 1 {1}, learn 1 0 0 1 {1}, learn 0 0 1 1 {1}, learn 1 0 1 1 {1},
  learn 0 1 2 1 {3}, learn 1 1 2 1 {3}]

/-- The schedule (Algorithm 2 as written: the passive proposers process the late `NACK`s). -/
def tr : List (Action N N N V) :=
  trPre ++ [processNack 0 1 1 {1, 3}, processNack 1 1 1 {1, 3}] ++ trPost

/-- The same schedule without the late `NACK`s. -/
def trNoNack : List (Action N N N V) := trPre ++ trPost

/-- Every message sent by a correct process to a correct process has been processed, except
possibly `NACK`s to passive proposers when `nacksOk = false`. -/
def AllCorrectDelivered (nacksOk : Bool) (s : State N N N V) : Prop :=
  ∀ m ∈ s.sent, match m with
    | .proposal p n _ => p ≠ 2 → ∀ a : N, a ≠ 2 → (p, n) ∈ s.adone a
    | .ack a p n _ => a ≠ 2 → (p ≠ 2 → a ∈ (s.prop p).acks n) ∧ ∀ l : N, l ≠ 2 → a ∈ s.lacks l p n
    | .nack a p n _ => a ≠ 2 → p ≠ 2 →
        (a ∈ (s.prop p).nacks n ∨ (nacksOk = false ∧ (s.prop p).active = false))
    | .internal q v => q ≠ 2 → ∀ p : N, p ≠ 2 → p ≠ q → (q, v) ∈ (s.prop p).seen

instance (nacksOk : Bool) (s : State N N N V) : Decidable (AllCorrectDelivered nacksOk s) := by
  unfold AllCorrectDelivered
  refine Finset.decidableDforallFinset (_hp := fun m _ => ?_)
  cases m <;> dsimp only <;> infer_instance

lemma run_tr : ((run (initState (A := N) (Ln := N) fun _ : N => (⊥ : V)) tr).elim false fun s =>
    decide (Quiescent corr s ∧ s.learnt 0 = ⊥ ∧ s.learnt 1 = ⊥ ∧ AllCorrectDelivered true s)) =
      true := by
  decide +kernel

/-- Without the late `NACK`s: both correct proposers are passive and cannot `Propose`, `Refine`
or `Decide`, the learners stay at `⊥`, and every message between correct processes except the
`NACK`s to the passive proposers has been processed. -/
lemma run_trNoNack :
    ((run (initState (A := N) (Ln := N) fun _ : N => (⊥ : V)) trNoNack).elim false fun s =>
      decide ((∀ p : N, p ≠ 2 → (s.prop p).active = false ∧ ¬ Enabled s (.propose p) ∧
          ¬ Enabled s (.refine p) ∧ ¬ Enabled s (.decide p)) ∧
        s.learnt 0 = ⊥ ∧ s.learnt 1 = ⊥ ∧ AllCorrectDelivered false s)) = true := by
  decide +kernel

/-- **Theorem 5.15 of [paper] is false even with singleton inputs and without late `NACK`s
reaching passive proposers.** In a fair execution with three processes (all roles), one of which
is faulty and loses its `ACK`s to the learners, the value `{1}` received by the correct process
`0` at time `3` is never included in the learnt value of the correct learner `0`. -/
theorem theorem_5_15_false_singleton :
    ∃ e : Exec (P := N) (A := N) (Ln := N) (L := V) (fun _ => ⊥),
      LivenessAssumptions corr ∧ e.Fair corr ∧ e.CrashStop corr ∧
      e.act 3 = some (.receive 0 {1}) ∧
      (∀ t, ¬ ({1} : V) ≤ (e.st t).learnt 0) ∧ ¬ e.GLALiveness corr := by
  have h := run_tr
  cases hr : run (initState (A := N) (Ln := N) fun _ : N => (⊥ : V)) tr with
  | none => rw [hr] at h; simp at h
  | some s =>
    rw [hr] at h
    simp only [Option.elim, decide_eq_true_eq] at h
    obtain ⟨hq, h0, -⟩ := h
    set e := Exec.ofRun _ tr s hr
    have hnever : ∀ t, ¬ ({1} : V) ≤ (e.st t).learnt 0 := by
      intro t ht
      have hm := e.learnt_mono 0 (le_max_left t tr.length)
      rw [Exec.ofRun_st_of_le hr (le_max_right _ _), h0] at hm
      exact absurd (ht.trans hm) (by decide)
    refine ⟨e, ⟨by decide, ⟨0, by decide⟩, ⟨0, by decide⟩⟩, Exec.ofRun_fair hr hq,
      Exec.ofRun_crashStop hr _, rfl, hnever, ?_⟩
    intro hl
    obtain ⟨t, ht⟩ := hl 0 {1} (by decide) ⟨3, rfl⟩ 0 (by decide)
    exact hnever t ht

end Podc.GeneralizedLatticeAgreement.Cex515c
