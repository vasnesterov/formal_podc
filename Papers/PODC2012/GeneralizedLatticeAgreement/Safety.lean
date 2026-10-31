import Papers.PODC2012.GeneralizedLatticeAgreement.InvStep
import Papers.PODC2012.GeneralizedLatticeAgreement.Runs

/-!
# Safety of Algorithm 2 (Section 5.1)

* Theorem 5.1 / Corollary 5.2 (Validity): every `proposedValue`, `acceptedValue`,
  `learntValue` (and every value carried by a message) is the join of a set of received
  values (`validity`).
* Theorem 5.3 (Stability): `Exec.learnt_mono` (in `Model.lean`).
* Lemma 5.4: acknowledged values of an acceptor increase over time (`lemma_5_4`).
* Lemma 5.5: chosen values are comparable (`lemma_5_5`).
* Theorem 5.6 (Consistency): any two values learnt (at any times, by any learners) are
  comparable (`theorem_5_6`).
-/

namespace Podc.GeneralizedLatticeAgreement

variable {P A Ln L : Type}

/-- The value carried by a message. -/
def Msg.val : Msg P A L → L
  | .proposal _ _ v | .ack _ _ _ v | .nack _ _ _ v | .internal _ v => v

variable [SemilatticeSup L] [OrderBot L] [DecidableEq P] [DecidableEq A] [DecidableEq Ln]
  [DecidableEq L] [DecidableLE L] [Fintype P] [Fintype A]

/-- The invariant behind Theorem 5.1. -/
structure ValidityInv (s : State P A Ln L) : Prop where
  msgs : ∀ m ∈ s.sent, IsJoinOf (↑s.received : Set L) m.val
  proposed : ∀ p, IsJoinOf (↑s.received : Set L) (s.prop p).proposed
  buffered : ∀ p, IsJoinOf (↑s.received : Set L) (s.prop p).buffered
  output : ∀ p, IsJoinOf (↑s.received : Set L) (s.prop p).output
  acc : ∀ a, IsJoinOf (↑s.received : Set L) (s.acc a)
  learnt : ∀ l, IsJoinOf (↑s.received : Set L) (s.learnt l)

lemma validityInv_init (b : P → L) : ValidityInv (initState (A := A) (Ln := Ln) b) where
  msgs := by simp [initState]
  proposed _ := IsJoinOf.bot
  buffered p := IsJoinOf.of_mem (by simp [initState])
  output _ := IsJoinOf.bot
  acc _ := IsJoinOf.bot
  learnt _ := IsJoinOf.bot

lemma ValidityInv.of_set {s : State P A Ln L} (R : Set L) (hR : R = ↑s.received)
    (msgs : ∀ m ∈ s.sent, IsJoinOf R m.val)
    (proposed : ∀ p, IsJoinOf R (s.prop p).proposed)
    (buffered : ∀ p, IsJoinOf R (s.prop p).buffered)
    (output : ∀ p, IsJoinOf R (s.prop p).output)
    (acc : ∀ a, IsJoinOf R (s.acc a))
    (learnt : ∀ l, IsJoinOf R (s.learnt l)) : ValidityInv s := by
  subst hR; exact ⟨msgs, proposed, buffered, output, acc, learnt⟩

lemma ValidityInv.step {s : State P A Ln L} (h : ValidityInv s) {act : Action P A Ln L}
    (he : Enabled s act) : ValidityInv (apply s act) := by
  have hR0 : (↑s.received : Set L) ⊆ ↑(apply s act).received := by
    exact_mod_cast received_subset_apply s act
  obtain ⟨R, hRd⟩ : ∃ R, R = (↑(apply s act).received : Set L) := ⟨_, rfl⟩
  have hR : (↑s.received : Set L) ⊆ R := hRd ▸ hR0
  have hm : ∀ m ∈ s.sent, IsJoinOf R m.val := fun m hm => (h.msgs m hm).mono hR
  have hpr : ∀ p, IsJoinOf R (s.prop p).proposed := fun p => (h.proposed p).mono hR
  have hbu : ∀ p, IsJoinOf R (s.prop p).buffered := fun p => (h.buffered p).mono hR
  have hou : ∀ p, IsJoinOf R (s.prop p).output := fun p => (h.output p).mono hR
  have hac : ∀ a, IsJoinOf R (s.acc a) := fun a => (h.acc a).mono hR
  have hle : ∀ l, IsJoinOf R (s.learnt l) := fun l => (h.learnt l).mono hR
  cases act with
  | receive q v =>
    have hv : IsJoinOf R v := IsJoinOf.of_mem (by rw [hRd]; simp [apply])
    refine ValidityInv.of_set R hRd ?_ ?_ ?_ ?_ hac hle
    · intro m hm'
      simp only [apply, Finset.mem_insert] at hm'
      rcases hm' with rfl | hm'
      · exact hv
      · exact hm m hm'
    all_goals intro p; simp only [apply, State.updP_prop]; split_ifs with hpq
    all_goals (first | (subst p; exact hv.sup (hbu q)) | (subst p; exact hpr q) |
        (subst p; exact hou q) | (exact hpr p) | (exact hbu p) | (exact hou p))
  | buffer q q' v =>
    have hv : IsJoinOf R v := hm _ he.2.1
    refine ValidityInv.of_set R hRd hm ?_ ?_ ?_ hac hle
    all_goals intro p; simp only [apply, State.updP_prop]; split_ifs with hpq
    all_goals (first | (subst p; exact hv.sup (hbu q)) | (subst p; exact hpr q) |
        (subst p; exact hou q) | (exact hpr p) | (exact hbu p) | (exact hou p))
  | propose q =>
    refine ValidityInv.of_set R hRd ?_ ?_ ?_ ?_ hac hle
    · intro m hm'
      simp only [apply, Finset.mem_insert] at hm'
      rcases hm' with rfl | hm'
      · exact (hpr q).sup (hbu q)
      · exact hm m hm'
    all_goals intro p; simp only [apply, State.updP_prop]; split_ifs with hpq
    all_goals (first | (subst p; exact (hpr q).sup (hbu q)) | (subst p; exact IsJoinOf.bot) |
        (subst p; exact hou q) | (exact hpr p) | (exact hbu p) | (exact hou p))
  | processAck q a n v =>
    refine ValidityInv.of_set R hRd hm ?_ ?_ ?_ hac hle
    all_goals intro p; simp only [apply, State.updP_prop]; split_ifs with hpq
    all_goals (first | (subst p; exact hpr q) | (subst p; exact hbu q) |
        (subst p; exact hou q) | (exact hpr p) | (exact hbu p) | (exact hou p))
  | processNack q a n v =>
    have hv : IsJoinOf R v := hm _ he.1
    refine ValidityInv.of_set R hRd hm ?_ ?_ ?_ hac hle
    all_goals intro p; simp only [apply, State.updP_prop]; split_ifs with hpq
    all_goals (first | (subst p; exact (hpr q).sup hv) | (subst p; exact hbu q) |
        (subst p; exact hou q) | (exact hpr p) | (exact hbu p) | (exact hou p))
  | refine q =>
    refine ValidityInv.of_set R hRd ?_ ?_ ?_ ?_ hac hle
    · intro m hm'
      simp only [apply, Finset.mem_insert] at hm'
      rcases hm' with rfl | hm'
      · exact hpr q
      · exact hm m hm'
    all_goals intro p; simp only [apply, State.updP_prop]; split_ifs with hpq
    all_goals (first | (subst p; exact hpr q) | (subst p; exact hbu q) |
        (subst p; exact hou q) | (exact hpr p) | (exact hbu p) | (exact hou p))
  | decide q =>
    refine ValidityInv.of_set R hRd hm ?_ ?_ ?_ hac hle
    all_goals intro p; simp only [apply, State.updP_prop]; split_ifs with hpq
    all_goals (first | (subst p; exact hpr q) | (subst p; exact hbu q) |
        (exact hpr p) | (exact hbu p) | (exact hou p))
  | accept a₀ q n v =>
    have hv : IsJoinOf R v := hm _ he.1
    refine ValidityInv.of_set R hRd ?_ hpr hbu hou ?_ hle
    · intro m hm'
      simp only [apply, Finset.mem_insert] at hm'
      rcases hm' with rfl | hm'
      · exact hv
      · exact hm m hm'
    · intro a; simp only [apply, Function.update_apply]; split_ifs
      · exact hv
      · exact hac a
  | reject a₀ q n v =>
    have hv : IsJoinOf R v := hm _ he.1
    refine ValidityInv.of_set R hRd ?_ hpr hbu hou ?_ hle
    · intro m hm'
      simp only [apply, Finset.mem_insert] at hm'
      rcases hm' with rfl | hm'
      · exact (hac a₀).sup hv
      · exact hm m hm'
    · intro a; simp only [apply, Function.update_apply]; split_ifs with ha
      · subst ha; exact (hac a).sup hv
      · exact hac a
  | learn l₀ a q n v =>
    have hv : IsJoinOf R v := hm _ he.1
    refine ValidityInv.of_set R hRd hm hpr hbu hou hac ?_
    intro l; simp only [apply, Function.update_apply]; split_ifs with h1 h2
    · exact hv
    · subst h1; exact hle l
    · exact hle l

lemma Reachable.validityInv {b : P → L} {s : State P A Ln L} (h : Reachable b s) :
    ValidityInv s := by
  induction h with
  | init => exact validityInv_init b
  | step act _ he ih => exact ih.step he

/-- Theorem 5.1 of [paper]: the values of `proposedValue` (of any proposer), `acceptedValue` (of
any acceptor) and `learntValue` (of any learner) can all be expressed as the join of some subset
of previously received input values. (For Algorithm 1, the initial values count as received.) -/
theorem theorem_5_1 {b : P → L} {s : State P A Ln L} (h : Reachable b s) :
    (∀ p, IsJoinOf (↑s.received : Set L) (s.prop p).proposed) ∧
    (∀ a, IsJoinOf (↑s.received : Set L) (s.acc a)) ∧
    (∀ l, IsJoinOf (↑s.received : Set L) (s.learnt l)) :=
  ⟨h.validityInv.proposed, h.validityInv.acc, h.validityInv.learnt⟩

/-- Corollary 5.2 of [paper] (Validity): any learnt value is a join of a subset of received
values. -/
theorem corollary_5_2 {b : P → L} {s : State P A Ln L} (h : Reachable b s) (l : Ln) :
    IsJoinOf (↑s.received : Set L) (s.learnt l) :=
  h.validityInv.learnt l

/-- Lemma 5.5 of [paper]: any two chosen values are comparable. -/
theorem lemma_5_5 {b : P → L} {s : State P A Ln L} (h : Reachable b s) {u v : L}
    (hu : Chosen s u) (hv : Chosen s v) : u ≤ v ∨ v ≤ u :=
  h.inv.chosen_comparable hu hv

namespace Exec

variable {b : P → L} (e : Exec (A := A) (Ln := Ln) b)

lemma reachable (t : ℕ) : Reachable b (e.st t) := by
  induction t with
  | zero => rw [e.init]; exact .init
  | succ t ih =>
    have := e.step t
    cases h : e.act t with
    | none => rw [h] at this; simp only at this; rw [this]; exact ih
    | some a => rw [h] at this; simp only at this; rw [this.2]; exact ih.step a this.1

lemma sent_mono {t t' : ℕ} (h : t ≤ t') : (e.st t).sent ⊆ (e.st t').sent := by
  induction h with
  | refl => exact subset_rfl
  | step _ ih =>
    refine ih.trans ?_
    obtain ⟨act, hact⟩ := e.step_apply _
    rw [hact]
    cases act with
    | none => exact subset_rfl
    | some a => exact sent_subset_apply _ _

lemma acc_mono (a : A) {t t' : ℕ} (h : t ≤ t') : (e.st t).acc a ≤ (e.st t').acc a := by
  induction h with
  | refl => exact le_rfl
  | @step m _ ih =>
    refine ih.trans ?_
    have := e.step m
    cases hact : e.act m with
    | none => rw [hact] at this; simp only at this; rw [this]
    | some act => rw [hact] at this; simp only at this; rw [this.2]; exact acc_le_apply _ _ this.1 a

end Exec

/-- Lemma 5.4 of [paper]: values acknowledged by an acceptor increase monotonically: if the same
acceptor executes `Accept(n, v, id)` and later `Accept(n', v', id')`, then `v ⊑ v'`. -/
theorem lemma_5_4 {b : P → L} (e : Exec (A := A) (Ln := Ln) b) {a : A} {p p' : P} {n n' : ℕ}
    {v v' : L} {t t' : ℕ} (ht : e.act t = some (.accept a p n v))
    (ht' : e.act t' = some (.accept a p' n' v')) (htt : t < t') : v ≤ v' := by
  have h1 := e.step t
  rw [ht] at h1
  have h2 := e.step t'
  rw [ht'] at h2
  obtain ⟨-, h1⟩ := h1
  obtain ⟨⟨-, -, hle⟩, -⟩ := h2
  have hv : (e.st (t + 1)).acc a = v := by rw [h1]; simp [apply]
  rw [← hv]
  exact (e.acc_mono a htt).trans hle

/-- Theorem 5.6 of [paper] (Consistency): any two values learnt by learners (at any two times)
are comparable. -/
theorem theorem_5_6 {b : P → L} (e : Exec (A := A) (Ln := Ln) b) (l l' : Ln) (t t' : ℕ) :
    (e.st t).learnt l ≤ (e.st t').learnt l' ∨ (e.st t').learnt l' ≤ (e.st t).learnt l := by
  rcases (e.reachable t).inv.learnt_chosen l with h1 | h1
  · left; rw [h1]; exact bot_le
  rcases (e.reachable t').inv.learnt_chosen l' with h2 | h2
  · right; rw [h2]; exact bot_le
  have h1' := h1.mono (e.sent_mono (le_max_left t t'))
  have h2' := h2.mono (e.sent_mono (le_max_right t t'))
  exact (e.reachable _).inv.chosen_comparable h1' h2'

end Podc.GeneralizedLatticeAgreement
