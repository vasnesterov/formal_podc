import Mathlib

/-!
# Generalized Lattice Agreement: the model (Algorithms 1 and 2)

Faleiro, Rajamani, Rajan, Ramalingam, Vaswani. *Generalized Lattice Agreement.* PODC 2012.

An interleaving model of Algorithm 2 (generalized lattice agreement: proposers, acceptors,
learners) of [paper], written as guarded actions exactly as in the paper.

* Values form a join-semilattice with a bottom element (`SemilatticeSup L`, `OrderBot L`).
* Proposers `P`, acceptors `A`, learners `Ln` are arbitrary finite types (the paper allows a
  process to play several roles; this is the instance `P = A = Ln`).
* Messages are kept in the set `sent` of all messages ever sent (never removed). Every message
  carries its sender (acknowledgements and rejections carry the acceptor), so a message is
  unique. Each receiver records which messages it has consumed, so a message is processed at
  most once by each receiver; a message that is never consumed is delayed forever or lost.
  Asynchrony, message loss and crashes are expressed by the scheduler: any enabled action may
  be taken at any time; a crashed process simply takes no more steps.
* Proposers keep, for every proposal number, the set of acceptors whose `ACK`/`NACK` they have
  processed (`acks n`, `nacks n`). The paper's counters are `ackCount = (acks apn).card` and
  `nackCount = (nacks apn).card`; the sets for older numbers are ghost history.
  Learners likewise keep `ackCount[id][n]` as the set of acceptors heard from.
* Ghost state: `received` (all received input values), `initiated` (the proposals made by
  `Propose`), `decisions` (all `Decide` steps).

Algorithm 1 (one-shot lattice agreement) is the same system started with `bufferedValues`
equal to the initial values and without `Receive` steps (see `Algorithm1.lean`).
-/

namespace Podc.GeneralizedLatticeAgreement

/-- Messages. `proposal p n v`: `Proposal(n, v, p)` to all acceptors; `ack a p n v`:
`ACK(n, v, p)` sent by acceptor `a` to proposer `p` and to all learners; `nack a p n v`:
`NACK(n, v)` sent by `a` to `p`; `internal p v`: `InternalReceive(v)` sent by `p` to all other
proposers. -/
inductive Msg (P A L : Type) where
  | proposal (p : P) (n : ℕ) (v : L)
  | ack (a : A) (p : P) (n : ℕ) (v : L)
  | nack (a : A) (p : P) (n : ℕ) (v : L)
  | internal (p : P) (v : L)

/-- An injective encoding of messages (used for a kernel-reducible `DecidableEq`). -/
def Msg.toTuple {P A L : Type} : Msg P A L → ℕ × Option P × Option A × ℕ × L
  | .proposal p n v => (0, some p, none, n, v)
  | .ack a p n v => (1, some p, some a, n, v)
  | .nack a p n v => (2, some p, some a, n, v)
  | .internal p v => (3, some p, none, 0, v)

lemma Msg.toTuple_injective {P A L : Type} : Function.Injective (Msg.toTuple (P := P) (A := A) (L := L)) := by
  intro m m' h
  cases m <;> cases m' <;> simp_all [Msg.toTuple]

instance {P A L : Type} [DecidableEq P] [DecidableEq A] [DecidableEq L] : DecidableEq (Msg P A L) :=
  fun m m' => decidable_of_iff (m.toTuple = m'.toTuple) Msg.toTuple_injective.eq_iff

/-- Local state of a proposer. -/
structure PState (P A L : Type) where
  /-- `status = active`. -/
  active : Bool
  /-- `activeProposalNumber`. -/
  apn : ℕ
  /-- Acceptors whose `ACK` for proposal number `n` was processed (`ackCount = (acks apn).card`). -/
  acks : ℕ → Finset A
  /-- Acceptors whose `NACK` for proposal number `n` was processed. -/
  nacks : ℕ → Finset A
  /-- `proposedValue`. -/
  proposed : L
  /-- `bufferedValues`. -/
  buffered : L
  /-- `outputValue` (Algorithm 1). -/
  output : L
  /-- Consumed `InternalReceive` messages `(sender, value)`. -/
  seen : Finset (P × L)

/-- Global state. -/
structure State (P A Ln L : Type) where
  /-- Proposers. -/
  prop : P → PState P A L
  /-- `acceptedValue` of each acceptor. -/
  acc : A → L
  /-- Proposals `(proposer, number)` already processed by each acceptor. -/
  adone : A → Finset (P × ℕ)
  /-- `learntValue` of each learner. -/
  learnt : Ln → L
  /-- `ackCount[id][n]` of each learner, as the set of acceptors heard from. -/
  lacks : Ln → P → ℕ → Finset A
  /-- All messages ever sent. -/
  sent : Finset (Msg P A L)
  /-- Ghost: all input values received so far (and the initial values). -/
  received : Finset L
  /-- Ghost: the proposals `(p, n)` made by a `Propose` step ("initiated"). -/
  initiated : Finset (P × ℕ)
  /-- Ghost: the `Decide` steps `(p, apn, decided value, nackCount = 0 at that moment)`. -/
  decisions : Finset (P × ℕ × L × Bool)

/-- Actions (the guarded actions of Algorithms 1 and 2). -/
inductive Action (P A Ln L : Type) where
  /-- `Receive(v)` at proposer `p` (input from a client). -/
  | receive (p : P) (v : L)
  /-- `Buffer(v)` at `p`, consuming `InternalReceive(v)` sent by `q`. -/
  | buffer (p q : P) (v : L)
  /-- `Propose()` at `p`. -/
  | propose (p : P)
  /-- `ProcessACK(n, v)` at `p`, consuming the `ACK` of acceptor `a`. -/
  | processAck (p : P) (a : A) (n : ℕ) (v : L)
  /-- `ProcessNACK(n, v)` at `p`, consuming the `NACK` of acceptor `a`. -/
  | processNack (p : P) (a : A) (n : ℕ) (v : L)
  /-- `Refine()` at `p`. -/
  | refine (p : P)
  /-- `Decide()` at `p`. -/
  | decide (p : P)
  /-- `Accept(n, v, p)` at acceptor `a`. -/
  | accept (a : A) (p : P) (n : ℕ) (v : L)
  /-- `Reject(n, v, p)` at acceptor `a`. -/
  | reject (a : A) (p : P) (n : ℕ) (v : L)
  /-- `Learn(n, v, p)` at learner `l`, consuming the `ACK` of acceptor `a`. -/
  | learn (l : Ln) (a : A) (p : P) (n : ℕ) (v : L)

variable {P A Ln L : Type}

/-- The quorum size `⌈(N_a + 1)/2⌉` (see `quorum_eq_ceil`). -/
def quorum (A : Type) [Fintype A] : ℕ := Fintype.card A / 2 + 1

lemma quorum_eq_ceil [Fintype A] : quorum A = (Fintype.card A + 1) ⌈/⌉ 2 := by
  rw [quorum, Nat.ceilDiv_eq_add_pred_div]; omega

section Defs

variable [SemilatticeSup L] [OrderBot L] [DecidableEq P] [DecidableEq A] [DecidableEq Ln]
  [DecidableEq L] [DecidableLE L] [Fintype P] [Fintype A]

/-- Initial state; `b p` is the initial `bufferedValues` of `p` (`⊥` in Algorithm 2, the initial
value in Algorithm 1). -/
def initState (b : P → L) : State P A Ln L where
  prop p := ⟨false, 0, fun _ => ∅, fun _ => ∅, ⊥, b p, ⊥, ∅⟩
  acc _ := ⊥
  adone _ := ∅
  learnt _ := ⊥
  lacks _ _ _ := ∅
  sent := ∅
  received := Finset.univ.image b
  initiated := ∅
  decisions := ∅

/-- Guards. -/
def Enabled (s : State P A Ln L) : Action P A Ln L → Prop
  | .receive _ _ => True
  | .buffer p q v => q ≠ p ∧ Msg.internal q v ∈ s.sent ∧ (q, v) ∉ (s.prop p).seen
  | .propose p => (s.prop p).active = false ∧
      ¬ ((s.prop p).proposed ⊔ (s.prop p).buffered ≤ (s.prop p).proposed)
  | .processAck p a n v => Msg.ack a p n v ∈ s.sent ∧ n = (s.prop p).apn ∧
      a ∉ (s.prop p).acks n
  | .processNack p a n v => Msg.nack a p n v ∈ s.sent ∧ n = (s.prop p).apn ∧
      a ∉ (s.prop p).nacks n
  | .refine p => 0 < ((s.prop p).nacks (s.prop p).apn).card ∧
      quorum A ≤ ((s.prop p).acks (s.prop p).apn).card + ((s.prop p).nacks (s.prop p).apn).card ∧
      (s.prop p).active = true
  | .decide p => quorum A ≤ ((s.prop p).acks (s.prop p).apn).card ∧ (s.prop p).active = true
  | .accept a p n v => Msg.proposal p n v ∈ s.sent ∧ (p, n) ∉ s.adone a ∧ s.acc a ≤ v
  | .reject a p n v => Msg.proposal p n v ∈ s.sent ∧ (p, n) ∉ s.adone a ∧ ¬ s.acc a ≤ v
  | .learn l a p n v => Msg.ack a p n v ∈ s.sent ∧ a ∉ s.lacks l p n

instance (s : State P A Ln L) : (act : Action P A Ln L) → Decidable (Enabled s act)
  | .receive _ _ => inferInstanceAs (Decidable True)
  | .buffer _ _ _ => inferInstanceAs (Decidable (_ ∧ _))
  | .propose _ => inferInstanceAs (Decidable (_ ∧ _))
  | .processAck _ _ _ _ => inferInstanceAs (Decidable (_ ∧ _))
  | .processNack _ _ _ _ => inferInstanceAs (Decidable (_ ∧ _))
  | .refine _ => inferInstanceAs (Decidable (_ ∧ _))
  | .decide _ => inferInstanceAs (Decidable (_ ∧ _))
  | .accept _ _ _ _ => inferInstanceAs (Decidable (_ ∧ _))
  | .reject _ _ _ _ => inferInstanceAs (Decidable (_ ∧ _))
  | .learn _ _ _ _ _ => inferInstanceAs (Decidable (_ ∧ _))

/-- Update the state of proposer `p`. -/
def State.updP (s : State P A Ln L) (p : P) (f : PState P A L → PState P A L) :
    State P A Ln L :=
  { s with prop := Function.update s.prop p (f (s.prop p)) }

/-- Effects. -/
def apply (s : State P A Ln L) : Action P A Ln L → State P A Ln L
  | .receive p v =>
    { s.updP p (fun x => { x with buffered := v ⊔ x.buffered }) with
      sent := insert (.internal p v) s.sent,
      received := insert v s.received }
  | .buffer p q v =>
    s.updP p (fun x => { x with buffered := v ⊔ x.buffered, seen := insert (q, v) x.seen })
  | .propose p =>
    let x := s.prop p
    let w := x.proposed ⊔ x.buffered
    { s.updP p (fun x => { x with
        proposed := w, active := true, apn := x.apn + 1,
        acks := Function.update x.acks (x.apn + 1) ∅,
        nacks := Function.update x.nacks (x.apn + 1) ∅, buffered := ⊥ }) with
      sent := insert (.proposal p (x.apn + 1) w) s.sent,
      initiated := insert (p, x.apn + 1) s.initiated }
  | .processAck p a n _ =>
    s.updP p (fun x => { x with acks := Function.update x.acks n (insert a (x.acks n)) })
  | .processNack p a n v =>
    s.updP p (fun x => { x with
        proposed := x.proposed ⊔ v,
        nacks := Function.update x.nacks n (insert a (x.nacks n)) })
  | .refine p =>
    let x := s.prop p
    { s.updP p (fun x => { x with
        apn := x.apn + 1,
        acks := Function.update x.acks (x.apn + 1) ∅,
        nacks := Function.update x.nacks (x.apn + 1) ∅ }) with
      sent := insert (.proposal p (x.apn + 1) x.proposed) s.sent }
  | .decide p =>
    let x := s.prop p
    { s.updP p (fun x => { x with output := x.proposed, active := false }) with
      decisions := insert (p, x.apn, x.proposed, decide (x.nacks x.apn = ∅)) s.decisions }
  | .accept a p n v =>
    { s with
             acc := Function.update s.acc a v,
             adone := Function.update s.adone a (insert (p, n) (s.adone a)),
             sent := insert (.ack a p n v) s.sent }
  | .reject a p n v =>
    { s with
             acc := Function.update s.acc a (s.acc a ⊔ v),
             adone := Function.update s.adone a (insert (p, n) (s.adone a)),
             sent := insert (.nack a p n (s.acc a ⊔ v)) s.sent }
  | .learn l a p n v =>
    let c := insert a (s.lacks l p n)
    { s with
             lacks := Function.update s.lacks l (Function.update (s.lacks l) p
                (Function.update (s.lacks l p) n c)),
             learnt := Function.update s.learnt l
                (if quorum A ≤ c.card ∧ s.learnt l ≤ v ∧ ¬ v ≤ s.learnt l then v else s.learnt l) }

/-- One step. -/
def Step (s s' : State P A Ln L) : Prop := ∃ act, Enabled s act ∧ s' = apply s act

/-- Reachable states from the initial state `initState b`. -/
inductive Reachable (b : P → L) : State P A Ln L → Prop
  | init : Reachable b (initState b)
  | step {s : State P A Ln L} (act : Action P A Ln L) :
      Reachable b s → Enabled s act → Reachable b (apply s act)

/-- The set of acceptors that acknowledged proposal `(p, n)` with value `v`. -/
def ackers (s : State P A Ln L) (p : P) (n : ℕ) (v : L) : Finset A :=
  Finset.univ.filter fun a => Msg.ack a p n v ∈ s.sent

/-- A value is *chosen* if some proposal with this value was accepted by a quorum. -/
def Chosen (s : State P A Ln L) (v : L) : Prop :=
  ∃ p n, quorum A ≤ (ackers s p n v).card

/-- An infinite execution (with stuttering) from `initState b`. -/
structure Exec (b : P → L) where
  /-- States. -/
  st : ℕ → State P A Ln L
  /-- The action taken at time `t` (`none`: stuttering). -/
  act : ℕ → Option (Action P A Ln L)
  init : st 0 = initState b
  step : ∀ t, match act t with
    | none => st (t + 1) = st t
    | some a => Enabled (st t) a ∧ st (t + 1) = apply (st t) a

/-- `learntValue` never decreases (Theorem 5.3, one step). -/
lemma learnt_le_apply (s : State P A Ln L) (act : Action P A Ln L) (l : Ln) :
    s.learnt l ≤ (apply s act).learnt l := by
  cases act with
  | learn l' a p n v =>
    simp only [apply]
    by_cases hl : l = l'
    · subst hl; simp only [Function.update_self]; split_ifs with h
      · exact h.2.1
      · exact le_rfl
    · simp [Function.update_of_ne hl]
  | _ => simp [apply, State.updP]

lemma Exec.step_apply {b : P → L} (e : Exec (A := A) (Ln := Ln) b) (t : ℕ) :
    ∃ act : Option (Action P A Ln L), e.st (t + 1) = act.elim (e.st t) (apply (e.st t)) := by
  have := e.step t
  cases h : e.act t with
  | none => rw [h] at this; exact ⟨none, this⟩
  | some a => rw [h] at this; exact ⟨some a, this.2⟩

/-- Theorem 5.3 (Stability): the `learntValue` of a learner increases monotonically over time. -/
theorem Exec.learnt_mono {b : P → L} (e : Exec (A := A) (Ln := Ln) b) (l : Ln) {t t' : ℕ}
    (h : t ≤ t') : (e.st t).learnt l ≤ (e.st t').learnt l := by
  induction h with
  | refl => exact le_rfl
  | step _ ih =>
    refine ih.trans ?_
    obtain ⟨act, hact⟩ := e.step_apply _
    rw [hact]
    cases act with
    | none => exact le_rfl
    | some a => exact learnt_le_apply _ _ _

end Defs

end Podc.GeneralizedLatticeAgreement
