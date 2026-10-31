import Papers.PODC2012.GeneralizedLatticeAgreement.Rounds
import Papers.PODC2012.GeneralizedLatticeAgreement.Runs

/-!
# Lemma 5.9 (second half) and Lemma 5.13 as stated are false

* `Cex59.lemma_5_9_decide_false`: in a failure-free fair execution, proposer `0` executes two
  `Decide` steps in the same round. Its first `Decide` outputs `{1,2}`: the join of its proposal
  `{1}` (chosen) with a `NACK` value processed before the quorum of `ACK`s. `{1,2}` is never
  chosen, and its round is that of the next chosen value `{1,2,3}`, which proposer `0` decides
  next. The paper's proof assumes that a decided value is chosen.
* `Cex513.lemma_5_13_false`: a value initiated by a proposer that crashes right after its
  `Propose` (its messages are lost) is never included in a chosen value. Lemma 5.13 needs the
  hypothesis "initiated by a correct proposer" (which holds where it is used).
-/

namespace Podc.GeneralizedLatticeAgreement

variable {P A Ln L : Type}
variable [SemilatticeSup L] [OrderBot L] [DecidableEq P] [DecidableEq A] [DecidableEq Ln]
  [DecidableEq L] [DecidableLE L] [Fintype P] [Fintype A]

/-- A decidable sufficient condition for `SameRound`: only values of acknowledged proposals can
be chosen. -/
def RoundCheck (s : State P A Ln L) (u w : L) : Prop :=
  ∀ m ∈ s.sent, match m with
    | .ack _ p n v => quorum A ≤ (ackers s p n v).card → (u ≤ v ↔ w ≤ v)
    | _ => True

instance (s : State P A Ln L) (u w : L) : Decidable (RoundCheck s u w) := by
  unfold RoundCheck
  refine Finset.decidableDforallFinset (_hp := fun m _ => ?_)
  cases m <;> dsimp only <;> infer_instance

lemma sameRound_of_check {s : State P A Ln L} {u w : L} (h : RoundCheck s u w) :
    SameRound s u w := by
  rintro c ⟨p, n, hc⟩
  obtain ⟨a, ha⟩ : (ackers s p n c).Nonempty := by
    rw [← Finset.card_pos]; unfold quorum at hc; omega
  have hm : Msg.ack a p n c ∈ s.sent := by simpa [ackers] using ha
  exact h _ hm hc

namespace Cex59

open Action

/-- Values. -/
abbrev V := Finset ℕ

/-- A failure-free schedule with two proposers, three acceptors and one learner. -/
def tr : List (Action (Fin 2) (Fin 3) (Fin 1) V) := [
  receive 1 {2}, propose 1, accept 2 1 1 {2},
  receive 0 {1}, propose 0,
  reject 2 0 1 {1}, accept 0 0 1 {1}, accept 1 0 1 {1},
  -- proposer 0 processes the NACK `{1,2}` and then a quorum of ACKs for `{1}`: it decides `{1,2}`
  processNack 0 2 1 {1, 2}, processAck 0 0 1 {1}, processAck 0 1 1 {1}, decide 0,
  receive 0 {3}, propose 0,
  accept 0 0 2 {1, 2, 3}, accept 1 0 2 {1, 2, 3}, accept 2 0 2 {1, 2, 3},
  processAck 0 0 2 {1, 2, 3}, processAck 0 1 2 {1, 2, 3}, decide 0,
  processAck 0 2 2 {1, 2, 3},
  -- proposer 1 completes
  reject 0 1 1 {2}, reject 1 1 1 {2},
  processAck 1 2 1 {2}, processNack 1 0 1 {1, 2, 3}, processNack 1 1 1 {1, 2, 3}, refine 1,
  accept 0 1 2 {1, 2, 3}, accept 1 1 2 {1, 2, 3}, accept 2 1 2 {1, 2, 3},
  processAck 1 0 2 {1, 2, 3}, processAck 1 1 2 {1, 2, 3}, processAck 1 2 2 {1, 2, 3}, decide 1,
  buffer 0 1 {2}, buffer 1 0 {1}, buffer 1 0 {3},
  learn 0 2 1 1 {2}, learn 0 0 0 1 {1}, learn 0 1 0 1 {1},
  learn 0 0 0 2 {1, 2, 3}, learn 0 1 0 2 {1, 2, 3}, learn 0 2 0 2 {1, 2, 3},
  learn 0 0 1 2 {1, 2, 3}, learn 0 1 1 2 {1, 2, 3}, learn 0 2 1 2 {1, 2, 3}]

/-- All processes are correct. -/
def corr : Fin 2 ⊕ Fin 3 ⊕ Fin 1 → Prop := fun _ => True

instance : DecidablePred corr := fun _ => inferInstanceAs (Decidable True)

lemma run_tr : ((run (initState (A := Fin 3) (Ln := Fin 1) fun _ : Fin 2 => (⊥ : V)) tr).elim
    false fun s => decide (Quiescent corr s ∧ (0, 1, ({1, 2} : V), false) ∈ s.decisions ∧
      (0, 2, ({1, 2, 3} : V), true) ∈ s.decisions ∧ RoundCheck s {1, 2} {1, 2, 3})) = true := by
  decide +kernel

/-- **Lemma 5.9 of [paper] ("a proposer executes at most one `Decide` step in a round") is
false**: in a failure-free fair execution, proposer `0` decides `{1,2}` (at proposal 1) and
`{1,2,3}` (at proposal 2), and both values are below exactly the same chosen values, i.e. both
`Decide` steps are in the same round. -/
theorem lemma_5_9_decide_false :
    ∃ (tr : List (Action (Fin 2) (Fin 3) (Fin 1) V)) (s : State (Fin 2) (Fin 3) (Fin 1) V)
      (h : run (initState fun _ => ⊥) tr = some s),
      (Exec.ofRun _ tr s h).Fair corr ∧ LivenessAssumptions corr ∧
      (0, 1, ({1, 2} : V), false) ∈ s.decisions ∧ (0, 2, ({1, 2, 3} : V), true) ∈ s.decisions ∧
      SameRound s {1, 2} {1, 2, 3} := by
  have h := run_tr
  cases hr : run (initState (A := Fin 3) (Ln := Fin 1) fun _ : Fin 2 => (⊥ : V)) tr with
  | none => rw [hr] at h; simp at h
  | some s =>
    rw [hr] at h
    simp only [Option.elim, decide_eq_true_eq] at h
    obtain ⟨hq, h1, h2, h3⟩ := h
    exact ⟨tr, s, hr, Exec.ofRun_fair hr hq, ⟨by decide, ⟨0, trivial⟩, ⟨0, trivial⟩⟩, h1, h2,
      sameRound_of_check h3⟩

end Cex59

namespace Cex513

open Action

/-- Values. -/
abbrev V := Finset ℕ

/-- Process `2` (all roles) is faulty. -/
def corr : Fin 3 ⊕ Fin 3 ⊕ Fin 3 → Prop
  | .inl i | .inr (.inl i) | .inr (.inr i) => i ≠ 2

instance : DecidablePred corr := fun r => by
  rcases r with i | i | i <;> simp only [corr] <;> infer_instance

/-- Process `2` receives `{3}` and proposes it; then it crashes, and its messages are lost. -/
def tr : List (Action (Fin 3) (Fin 3) (Fin 3) V) := [receive 2 {3}, propose 2]

/-- Is the message an acknowledgement? -/
def isAck : Msg (Fin 3) (Fin 3) V → Bool
  | .ack .. => true
  | _ => false

lemma run_tr : ((run (initState (A := Fin 3) (Ln := Fin 3) fun _ : Fin 3 => (⊥ : V)) tr).elim
    false fun s => decide (Quiescent corr s ∧ (2, 1) ∈ s.initiated ∧
      Msg.proposal 2 1 {3} ∈ s.sent ∧ ∀ m ∈ s.sent, isAck m = false)) = true := by
  decide +kernel

/-- **Lemma 5.13 of [paper] ("every initiated value is eventually included in a chosen value") is
false** without the hypothesis that the initiating proposer is correct: in a fair execution
satisfying the liveness assumptions, `{3}` is initiated but no value is ever chosen. -/
theorem lemma_5_13_false :
    ∃ e : Exec (P := Fin 3) (A := Fin 3) (Ln := Fin 3) (L := V) (fun _ => ⊥),
      e.Fair corr ∧ e.CrashStop corr ∧ LivenessAssumptions corr ∧
      (∃ t, (2, 1) ∈ (e.st t).initiated ∧ Msg.proposal 2 1 {3} ∈ (e.st t).sent) ∧
      ∀ t c, Chosen (e.st t) c → ¬ ({3} : V) ≤ c := by
  have h := run_tr
  cases hr : run (initState (A := Fin 3) (Ln := Fin 3) fun _ : Fin 3 => (⊥ : V)) tr with
  | none => rw [hr] at h; simp at h
  | some s =>
    rw [hr] at h
    simp only [Option.elim, decide_eq_true_eq] at h
    obtain ⟨hq, h1, h2, h3⟩ := h
    set e := Exec.ofRun _ tr s hr
    have hfin : e.st tr.length = s := Exec.ofRun_st_of_le hr le_rfl
    refine ⟨e, Exec.ofRun_fair hr hq, Exec.ofRun_crashStop hr _,
      ⟨by decide, ⟨0, by decide⟩, ⟨0, by decide⟩⟩, ⟨tr.length, hfin ▸ h1, hfin ▸ h2⟩, ?_⟩
    rintro t c ⟨p, n, hc⟩ -
    obtain ⟨a, ha⟩ : (ackers (e.st t) p n c).Nonempty := by
      rw [← Finset.card_pos]; unfold quorum at hc; omega
    have hm : Msg.ack a p n c ∈ (e.st t).sent := by simpa [ackers] using ha
    have hm' := e.sent_mono (le_max_left t tr.length) hm
    rw [Exec.ofRun_st_of_le hr (le_max_right _ _)] at hm'
    simpa [isAck] using h3 _ hm'

end Cex513

end Podc.GeneralizedLatticeAgreement
