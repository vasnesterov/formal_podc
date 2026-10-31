import Papers.PODC2012.GeneralizedLatticeAgreement.Model

/-!
# Executions: correct processes, fairness, liveness, concrete runs

* `Action.actor`, `Action.sender`: the process taking a step and the sender of the message it
  consumes. A process is identified by its role: `P ⊕ A ⊕ Ln`.
* `Exec.Fair corr`: weak fairness for correct processes. A non-input action of a correct process
  that consumes no message, or a message sent by a correct process, and that is enabled from
  some time on, is eventually taken. For message-consuming actions this is the paper's
  liveness assumption (d) "all messages between correct processes are eventually delivered";
  messages sent by faulty processes may be lost (the paper's failure model includes message
  losses and crashes in the middle of a step).
* `Exec.CrashStop corr`: a faulty process eventually takes no more steps.
* `LivenessAssumptions corr`: the paper's assumptions (a)–(c): a majority (quorum) of acceptors,
  at least one proposer and at least one learner are correct.
* `Exec.GLALiveness corr`: Liveness of generalized lattice agreement (Section 4, item 4): every
  value received by a correct proposer is eventually below the `learntValue` of every correct
  learner.
* `run`: executing a finite list of actions (used to check concrete executions by `decide`);
  `Quiescent`: no action of a correct process on a message of a correct process is enabled;
  `Exec.ofRun`: a finite run followed by stuttering, which is fair if its last state is
  quiescent.
-/

namespace Podc.GeneralizedLatticeAgreement

variable {P A Ln L : Type}

namespace Action

/-- The process (role) that takes the step. -/
def actor : Action P A Ln L → P ⊕ A ⊕ Ln
  | receive p _ | buffer p _ _ | propose p | processAck p _ _ _ | processNack p _ _ _
  | refine p | decide p => .inl p
  | accept a _ _ _ | reject a _ _ _ => .inr (.inl a)
  | learn l _ _ _ _ => .inr (.inr l)

/-- The sender of the message consumed by the step, if any. -/
def sender : Action P A Ln L → Option (P ⊕ A ⊕ Ln)
  | buffer _ q _ => some (.inl q)
  | processAck _ a _ _ | processNack _ a _ _ | learn _ a _ _ _ => some (.inr (.inl a))
  | accept _ p _ _ | reject _ p _ _ => some (.inl p)
  | _ => none

/-- Input actions (`Receive`) are triggered by the environment and not subject to fairness. -/
def IsInput : Action P A Ln L → Prop
  | receive _ _ => True
  | _ => False

instance (act : Action P A Ln L) : Decidable act.IsInput := by
  cases act <;> simp only [IsInput] <;> infer_instance

end Action

section

variable [SemilatticeSup L] [OrderBot L] [DecidableEq P] [DecidableEq A] [DecidableEq Ln]
  [DecidableEq L] [DecidableLE L] [Fintype P] [Fintype A]

namespace Exec

variable {b : P → L} (corr : P ⊕ A ⊕ Ln → Prop) (e : Exec (P := P) (A := A) (Ln := Ln) (L := L) b)

/-- Weak fairness for correct processes and messages between correct processes. -/
def Fair : Prop :=
  ∀ act : Action P A Ln L, ¬ act.IsInput → corr act.actor →
    (∀ r, act.sender = some r → corr r) →
    ∀ T, (∀ t ≥ T, Enabled (e.st t) act) → ∃ t ≥ T, e.act t = some act

/-- Faulty processes eventually stop taking steps. -/
def CrashStop : Prop :=
  ∀ r, ¬ corr r → ∃ T, ∀ t ≥ T, ∀ act, e.act t = some act → act.actor ≠ r

/-- Liveness of generalized lattice agreement (Section 4, condition 4): every value received by
a correct proposer is eventually included in the learnt value of every correct learner. -/
def GLALiveness : Prop :=
  ∀ p v, corr (.inl p) → (∃ t, e.act t = some (.receive p v)) →
    ∀ l, corr (.inr (.inr l)) → ∃ t, v ≤ (e.st t).learnt l

end Exec

/-- The paper's liveness assumptions (a)–(c). -/
def LivenessAssumptions (corr : P ⊕ A ⊕ Ln → Prop) [DecidablePred corr] : Prop :=
  quorum A ≤ (Finset.univ.filter fun a : A => corr (.inr (.inl a))).card ∧
  (∃ p, corr (.inl p)) ∧ (∃ l, corr (.inr (.inr l)))

/-- Run a finite list of actions; `none` if some action is not enabled. -/
def run (s : State P A Ln L) : List (Action P A Ln L) → Option (State P A Ln L)
  | [] => some s
  | a :: as => if Enabled s a then run (apply s a) as else none

lemma run_append (s : State P A Ln L) (l₁ l₂ : List (Action P A Ln L)) :
    run s (l₁ ++ l₂) = (run s l₁).bind fun x => run x l₂ := by
  induction l₁ generalizing s with
  | nil => rfl
  | cons a as ih =>
    simp only [List.cons_append, run]
    split_ifs <;> simp [ih]

lemma reachable_of_run {b : P → L} {s s' : State P A Ln L} {l : List (Action P A Ln L)}
    (hs : Reachable b s) (h : run s l = some s') : Reachable b s' := by
  induction l generalizing s with
  | nil => simp [run] at h; exact h ▸ hs
  | cons a as ih =>
    simp only [run] at h
    split_ifs at h with he
    exact ih (hs.step a he) h

/-- No action of a correct process consuming a message of a correct process (or no message)
is enabled, except inputs. -/
def Quiescent (corr : P ⊕ A ⊕ Ln → Prop) (s : State P A Ln L) : Prop :=
  (∀ p, corr (.inl p) →
    ¬ Enabled s (.propose p) ∧ ¬ Enabled s (.refine p) ∧ ¬ Enabled s (.decide p)) ∧
  ∀ m ∈ s.sent, match m with
    | .proposal p n v => corr (.inl p) → ∀ a, corr (.inr (.inl a)) →
        ¬ Enabled s (.accept a p n v) ∧ ¬ Enabled s (.reject a p n v)
    | .ack a p n v => corr (.inr (.inl a)) →
        (corr (.inl p) → ¬ Enabled s (.processAck p a n v)) ∧
        ∀ l, corr (.inr (.inr l)) → ¬ Enabled s (.learn l a p n v)
    | .nack a p n v => corr (.inr (.inl a)) → corr (.inl p) →
        ¬ Enabled s (.processNack p a n v)
    | .internal q v => corr (.inl q) → ∀ p, corr (.inl p) → ¬ Enabled s (.buffer p q v)

instance [Fintype Ln] (corr : P ⊕ A ⊕ Ln → Prop) [DecidablePred corr]
    (s : State P A Ln L) : Decidable (Quiescent corr s) := by
  unfold Quiescent
  refine instDecidableAnd (dq := ?_)
  refine Finset.decidableDforallFinset (_hp := fun m _ => ?_)
  cases m <;> dsimp only <;> infer_instance

lemma not_enabled_of_quiescent {corr : P ⊕ A ⊕ Ln → Prop} {s : State P A Ln L}
    (hq : Quiescent corr s) (act : Action P A Ln L) (hin : ¬ act.IsInput)
    (hc : corr act.actor) (hs : ∀ r, act.sender = some r → corr r) : ¬ Enabled s act := by
  obtain ⟨h1, h2⟩ := hq
  cases act with
  | receive => exact absurd trivial hin
  | buffer p q v =>
    intro he; exact h2 _ he.2.1 (hs _ rfl) p hc he
  | propose p => exact (h1 p hc).1
  | processAck p a n v =>
    intro he; exact (h2 _ he.1 (hs _ rfl)).1 hc he
  | processNack p a n v =>
    intro he; exact h2 _ he.1 (hs _ rfl) hc he
  | refine p => exact (h1 p hc).2.1
  | decide p => exact (h1 p hc).2.2
  | accept a p n v =>
    intro he; exact (h2 _ he.1 (hs _ rfl) a hc).1 he
  | reject a p n v =>
    intro he; exact (h2 _ he.1 (hs _ rfl) a hc).2 he
  | learn l a p n v =>
    intro he; exact (h2 _ he.1 (hs _ rfl)).2 l hc he

/-- The execution that performs the actions of `tr` and then stutters forever. -/
def Exec.ofRun (b : P → L) (tr : List (Action P A Ln L)) (s' : State P A Ln L)
    (h : run (initState b) tr = some s') : Exec (P := P) (A := A) (Ln := Ln) (L := L) b where
  st t := (run (initState b) (tr.take t)).getD (initState b)
  act t := tr[t]?
  init := by simp [run]
  step t := by
    by_cases ht : t < tr.length
    · have hsplit : tr.take (t + 1) = tr.take t ++ [tr[t]] := by
        exact List.take_succ_eq_append_getElem ht
      have hpre : ∃ x, run (initState b) (tr.take t) = some x := by
        have := h
        rw [← List.take_append_drop t tr, run_append] at this
        cases hx : run (initState b) (tr.take t) with
        | none => simp [hx] at this
        | some x => exact ⟨x, rfl⟩
      obtain ⟨x, hx⟩ := hpre
      have hfull : run (initState b) (tr.take (t + 1)) ≠ none := by
        intro hn
        have := h
        rw [← List.take_append_drop (t + 1) tr, run_append, hn] at this
        simp at this
      simp only [List.getElem?_eq_getElem ht]
      rw [hsplit, run_append, hx] at hfull ⊢
      simp only [Option.bind_some, run] at hfull ⊢
      split_ifs at hfull ⊢ with he
      · simp [hx, he]
      · simp at hfull
    · have h1 : tr.take t = tr := List.take_of_length_le (by omega)
      have h2 : tr.take (t + 1) = tr := List.take_of_length_le (by omega)
      simp only [List.getElem?_eq_none (by omega : tr.length ≤ t), h1, h2]

lemma Exec.ofRun_st_of_le {b : P → L} {tr : List (Action P A Ln L)} {s' : State P A Ln L}
    (h : run (initState b) tr = some s') {t : ℕ} (ht : tr.length ≤ t) :
    (Exec.ofRun b tr s' h).st t = s' := by
  simp [Exec.ofRun, List.take_of_length_le ht, h]

lemma Exec.ofRun_act_of_le {b : P → L} {tr : List (Action P A Ln L)} {s' : State P A Ln L}
    (h : run (initState b) tr = some s') {t : ℕ} (ht : tr.length ≤ t) :
    (Exec.ofRun b tr s' h).act t = none := by
  simp [Exec.ofRun, List.getElem?_eq_none ht]

/-- A finite run ending in a quiescent state, followed by stuttering, is fair. -/
lemma Exec.ofRun_fair [Fintype Ln] {b : P → L} {tr : List (Action P A Ln L)}
    {s' : State P A Ln L} (h : run (initState b) tr = some s') {corr : P ⊕ A ⊕ Ln → Prop}
    (hq : Quiescent corr s') : (Exec.ofRun b tr s' h).Fair corr := by
  intro act hin hc hs T hen
  exfalso
  have := hen (max T tr.length) (le_max_left _ _)
  rw [Exec.ofRun_st_of_le h (le_max_right _ _)] at this
  exact not_enabled_of_quiescent hq act hin hc hs this

/-- In a finite run followed by stuttering, every process eventually stops. -/
lemma Exec.ofRun_crashStop {b : P → L} {tr : List (Action P A Ln L)}
    {s' : State P A Ln L} (h : run (initState b) tr = some s') (corr : P ⊕ A ⊕ Ln → Prop) :
    (Exec.ofRun b tr s' h).CrashStop corr := by
  intro r _
  refine ⟨tr.length, fun t ht act hact => ?_⟩
  rw [Exec.ofRun_act_of_le h ht] at hact
  cases hact

end

end Podc.GeneralizedLatticeAgreement
