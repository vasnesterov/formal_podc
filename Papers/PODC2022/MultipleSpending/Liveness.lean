import Papers.PODC2022.MultipleSpending.Safety

/-!
# Liveness of Algorithms 1–2: Agreement and Lemmas 4.5–4.7

Fair executions of the interleaving model of `Protocol.lean` and the liveness properties of the
`k`-spending asset transfer (§4.2 of the paper):

* `Setup.Exec`, `Setup.Exec.Fair`: infinite executions (with stuttering steps) and fairness:
  every message sent by a correct process is eventually received by every correct process, every
  transaction the application of a correct process asks to transfer is eventually issued, and
  the echo / accept / accuse / relay actions of correct processes are *weakly fair* (an action
  that stays enabled from some time on is eventually taken). The enabling conditions
  `IssueEnabled`, `EchoEnabled`, `AcceptEnabled`, `AccuseEnabled`, `RelayEnabled` are literally
  the premises of the constructors of `Step` (`EchoEnabled.step`, …). Executions of the
  paper's code (which echoes right upon reception, keeps `pending`, and relays upon reception)
  are fair in this sense, so the results transfer to them.
* `exists_fair`: fair executions exist (round robin), so the results below are not vacuous.
* `agreement` (Agreement, Theorem 4.8), `lemma_4_5` (Eventual Conviction; the stronger
  `conviction`: both processes end up with the *same* accusation `(tx.s, tx, tx')`),
  `lemma_4_6` (Termination), `lemma_4_7` (Validity).
* `ValidityCex.validity_needs_inputs`: Validity is false without the (implicit) assumption that
  the issuer has accepted the inputs of `tx`.

An accusation `(w, tx, tx')` (the paper's `({w}, {(tx, σ), (tx', σ')})`) *refers to* `tx` and
`tx'` (`RefersTo`). "Correct" is `∉ A.B`, "live" is `A.T.Live A.B`.

Except Agreement, all results assume `A.T.SelfMem` (a process belongs to each of its quorums,
standing assumption of §2): a correct process that accepted `tx` received an echo of `tx` from
itself, i.e. it echoed `tx` (`Inv.echo_of_mem`). This makes the paper's case "`p` did not echo
`tx`" vacuous. Validity needs three assumptions that the paper uses only implicitly (see
`lemma_4_7`).
-/

namespace Podc.MultipleSpending

open Finset

/-- The accusation `(w, tx, tx')`, i.e. `({w}, {(tx, σ), (tx', σ')})`, *refers to* `t` if `t` is
one of its two conflicting transactions. -/
def RefersTo {P Tx : Type*} (a : P × Tx × Tx) (t : Tx) : Prop := a.2.1 = t ∨ a.2.2 = t

/-- `Msg P Tx` as a sum type (used to enumerate events in `exists_fair`). -/
def Msg.equivSum {P Tx : Type*} : Msg P Tx ≃ Tx ⊕ Tx ⊕ (P × Tx × Tx) where
  toFun
    | .req tx => .inl tx
    | .echo tx => .inr (.inl tx)
    | .acc w tx tx' => .inr (.inr (w, tx, tx'))
  invFun
    | .inl tx => .req tx
    | .inr (.inl tx) => .echo tx
    | .inr (.inr (w, tx, tx')) => .acc w tx tx'
  left_inv m := by cases m <;> rfl
  right_inv s := by rcases s with _ | _ | ⟨_, _, _⟩ <;> rfl

instance Msg.instEncodable {P Tx : Type*} [Encodable P] [Encodable Tx] :
    Encodable (Msg P Tx) :=
  Encodable.ofEquiv _ Msg.equivSum

/-- A monotone family of eventual facts over a finite index type holds simultaneously. -/
private theorem exists_forall_of_mono {ι : Type*} [Finite ι] (φ : ι → ℕ → Prop)
    (hmono : ∀ a i j, i ≤ j → φ a i → φ a j) (h : ∀ a, ∃ i, φ a i) : ∃ j, ∀ a, φ a j := by
  classical
  have := Fintype.ofFinite ι
  choose f hf using h
  exact ⟨Finset.univ.sup f, fun a => hmono a _ _ (Finset.le_sup (Finset.mem_univ a)) (hf a)⟩

variable {P Tx : Type*} [Fintype P] [DecidableEq P] [DecidableEq Tx]

namespace Setup

variable (A : Setup P Tx)

/-! ### Enabled actions of correct processes -/

/-- Precondition of `Step.issue` (`transfer(tx)`, lines 1–3). -/
def IssueEnabled (p : P) (tx : Tx) : Prop :=
  p ∉ A.B ∧ tx ∈ A.issue p ∧ A.X.issuer tx = some p

/-- Precondition of `Step.echo` (lines 4–10, 11–19). -/
def EchoEnabled (σ : State P Tx) (p : P) (tx : Tx) : Prop :=
  p ∉ A.B ∧ A.HasReq σ p tx ∧
    ∀ tx', (p, Msg.echo tx') ∈ σ.sent → A.X.issuer tx' = A.X.issuer tx →
      Disjoint (A.X.inputs tx') (A.X.inputs tx)

/-- Precondition of `Step.accept` (lines 20–25, 37–41). -/
def AcceptEnabled (σ : State P Tx) (p : P) (tx : Tx) : Prop :=
  p ∉ A.B ∧ tx ∉ σ.hist p ∧ (∃ Q ∈ A.T.Q p, ∀ q ∈ Q, (p, q, Msg.echo tx) ∈ σ.rcv) ∧
    A.X.inputs tx ⊆ σ.hist p ∧ A.X.Valid tx ∧
    ∀ tx' ∈ σ.hist p, A.X.issuer tx' = A.X.issuer tx → Disjoint (A.X.inputs tx') (A.X.inputs tx)

/-- Precondition of `Step.accuse` (lines 26–32). -/
def AccuseEnabled (σ : State P Tx) (p w : P) (tx tx' : Tx) : Prop :=
  p ∉ A.B ∧ A.HasReq σ p tx ∧ A.HasReq σ p tx' ∧ A.VerifyAcc w tx tx'

/-- Precondition of `Step.relay` (lines 33–36). -/
def RelayEnabled (σ : State P Tx) (p s w : P) (tx tx' : Tx) : Prop :=
  p ∉ A.B ∧ (p, s, Msg.acc w tx tx') ∈ σ.rcv ∧ A.VerifyAcc w tx tx'

variable {A}

theorem IssueEnabled.step {p : P} {tx : Tx} (h : A.IssueEnabled p tx) (σ : State P Tx) :
    A.Step σ { σ with sent := insert (p, .req tx) σ.sent } :=
  Step.issue σ p tx h.1 h.2.1 h.2.2

theorem EchoEnabled.step {σ : State P Tx} {p : P} {tx : Tx} (h : A.EchoEnabled σ p tx) :
    A.Step σ { σ with sent := insert (p, .echo tx) σ.sent } :=
  Step.echo σ p tx h.1 h.2.1 h.2.2

theorem AcceptEnabled.step {σ : State P Tx} {p : P} {tx : Tx} (h : A.AcceptEnabled σ p tx) :
    A.Step σ { σ with hist := Function.update σ.hist p (insert tx (σ.hist p)) } :=
  Step.accept σ p tx h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2

theorem AccuseEnabled.step {σ : State P Tx} {p w : P} {tx tx' : Tx}
    (h : A.AccuseEnabled σ p w tx tx') :
    A.Step σ { σ with sent := insert (p, .acc w tx tx') σ.sent } :=
  Step.accuse σ p w tx tx' h.1 h.2.1 h.2.2.1 h.2.2.2

theorem RelayEnabled.step {σ : State P Tx} {p s w : P} {tx tx' : Tx}
    (h : A.RelayEnabled σ p s w tx tx') :
    A.Step σ { σ with sent := insert (p, .acc w tx tx') σ.sent } :=
  Step.relay σ p s w tx tx' h.1 h.2.1 h.2.2

/-! ### Auxiliary facts about the model -/

omit [Fintype P] [DecidableEq P] [DecidableEq Tx] in
theorem HasReq.mono {σ σ' : State P Tx} (h : σ.rcv ⊆ σ'.rcv) {p : P} {tx : Tx}
    (hr : A.HasReq σ p tx) : A.HasReq σ' p tx :=
  hr.imp (fun ⟨w, hw, hr⟩ => ⟨w, hw, h hr⟩) (fun ⟨s, hs⟩ => ⟨s, h hs⟩)

omit [DecidableEq P] [DecidableEq Tx] in
/-- A valid transaction has an issuer (it is not issued by the originator `⊥`). -/
theorem exists_issuer_of_valid {tx : Tx} (h : A.X.Valid tx) : ∃ w, A.X.issuer tx = some w := by
  obtain ⟨hpos, heq⟩ := h
  cases hw : A.X.issuer tx with
  | none => simp only [TxSystem.inValue, hw] at heq; omega
  | some w => exact ⟨w, rfl⟩

omit [DecidableEq P] [DecidableEq Tx] in
/-- With `SelfMem`, a correct process echoed every transaction it accepted. -/
theorem Inv.echo_of_mem (hself : A.T.SelfMem) {σ : State P Tx} (hI : A.Inv σ) {p : P} {tx : Tx}
    (hp : p ∉ A.B) (htx : tx ∈ σ.hist p) (hne : tx ≠ A.X.init) : (p, Msg.echo tx) ∈ σ.sent := by
  obtain ⟨Q, hQ, hQe⟩ := hI.quorum p tx hp htx hne
  exact hI.genuine _ _ _ hp (hQe p (hself p Q hQ))

/-- A correct process sends a request only for transactions it issues. -/
theorem Reachable.req_issuer {σ : State P Tx} (h : A.Reachable σ) {p : P} {tx : Tx}
    (hs : (p, Msg.req tx) ∈ σ.sent) : A.X.issuer tx = some p := by
  induction h with
  | refl => simp [init] at hs
  | tail _ hst ih =>
    cases hst with
    | issue p' tx' _ _ hown =>
      rcases Set.mem_insert_iff.mp hs with he | hs
      · simp only [Prod.mk.injEq, Msg.req.injEq] at he
        obtain ⟨rfl, rfl⟩ := he; exact hown
      · exact ih hs
    | echo =>
      rcases Set.mem_insert_iff.mp hs with he | hs
      · simp at he
      · exact ih hs
    | accuse =>
      rcases Set.mem_insert_iff.mp hs with he | hs
      · simp at he
      · exact ih hs
    | relay =>
      rcases Set.mem_insert_iff.mp hs with he | hs
      · simp at he
      · exact ih hs
    | _ => exact ih hs

/-- A transaction added to a history by a step had all its inputs in the history before. -/
theorem Step.inputs_subset_of_new {σ σ' : State P Tx} (h : A.Step σ σ') {p : P} {tx : Tx}
    (h' : tx ∈ σ'.hist p) (hn : tx ∉ σ.hist p) : A.X.inputs tx ⊆ σ.hist p := by
  cases h with
  | accept q t _ _ _ hin _ _ =>
    simp only [Function.update_apply] at h'
    split_ifs at h' with hpq
    · subst hpq
      rcases Finset.mem_insert.mp h' with rfl | h'
      · exact hin
      · exact absurd h' hn
    · exact absurd h' hn
  | _ => exact absurd h' hn

/-! ### Executions and fairness -/

variable (A) in
/-- An infinite execution of Algorithms 1–2 (with stuttering steps). -/
structure Exec where
  /-- The state at each time. -/
  σ : ℕ → State P Tx
  zero : σ 0 = A.init
  step : ∀ i, A.Step (σ i) (σ (i + 1)) ∨ σ (i + 1) = σ i

namespace Exec

variable (E : A.Exec)

/-- Fairness of an execution. Byzantine processes and their injections are unconstrained. -/
structure Fair : Prop where
  /-- Every message sent by a correct process is eventually received by every correct
  process. -/
  deliver : ∀ q s m i, q ∉ A.B → s ∉ A.B → (s, m) ∈ (E.σ i).sent →
    ∃ j, (q, s, m) ∈ (E.σ j).rcv
  /-- Every transaction the application of a correct process asks to transfer is issued. -/
  issue : ∀ p tx, A.IssueEnabled p tx → ∃ j, (p, Msg.req tx) ∈ (E.σ j).sent
  /-- Weak fairness of echoing. -/
  echo : ∀ p tx i, (∀ j, i ≤ j → A.EchoEnabled (E.σ j) p tx) →
    ∃ j, (p, Msg.echo tx) ∈ (E.σ j).sent
  /-- Weak fairness of accepting. -/
  accept : ∀ p tx i, (∀ j, i ≤ j → A.AcceptEnabled (E.σ j) p tx) → ∃ j, tx ∈ (E.σ j).hist p
  /-- Weak fairness of accusing. -/
  accuse : ∀ p w tx tx' i, (∀ j, i ≤ j → A.AccuseEnabled (E.σ j) p w tx tx') →
    ∃ j, (p, Msg.acc w tx tx') ∈ (E.σ j).sent
  /-- Weak fairness of relaying accusations. -/
  relay : ∀ p s w tx tx' i, (∀ j, i ≤ j → A.RelayEnabled (E.σ j) p s w tx tx') →
    ∃ j, (p, Msg.acc w tx tx') ∈ (E.σ j).sent

theorem reach_le {i j : ℕ} (hij : i ≤ j) : Relation.ReflTransGen A.Step (E.σ i) (E.σ j) := by
  induction hij with
  | refl => exact Relation.ReflTransGen.refl
  | step _ ih =>
    rcases E.step _ with h | h
    · exact ih.tail h
    · rw [h]; exact ih

theorem reachable (i : ℕ) : A.Reachable (E.σ i) := by
  have := E.reach_le (Nat.zero_le i)
  rwa [E.zero] at this

theorem inv (i : ℕ) : A.Inv (E.σ i) := Reachable.inv A (E.reachable i)

theorem sent_mono {i j : ℕ} (hij : i ≤ j) : (E.σ i).sent ⊆ (E.σ j).sent := by
  induction hij with
  | refl => exact le_rfl
  | step _ ih =>
    rcases E.step _ with h | h
    · exact ih.trans (Step.sent_subset A h)
    · rw [h]; exact ih

theorem rcv_mono {i j : ℕ} (hij : i ≤ j) : (E.σ i).rcv ⊆ (E.σ j).rcv := by
  induction hij with
  | refl => exact le_rfl
  | step _ ih =>
    rcases E.step _ with h | h
    · exact ih.trans (Step.rcv_subset A h)
    · rw [h]; exact ih

theorem hist_mono {i j : ℕ} (hij : i ≤ j) (p : P) : (E.σ i).hist p ⊆ (E.σ j).hist p :=
  Setup.hist_mono A (E.reach_le hij) p

theorem acHist_mono {i j : ℕ} (hij : i ≤ j) (p : P) : acHist (E.σ i) p ⊆ acHist (E.σ j) p :=
  Setup.acHist_mono A (E.reach_le hij) p

theorem inputs_subset_of_new {n : ℕ} {p : P} {tx : Tx} (h' : tx ∈ (E.σ (n + 1)).hist p)
    (hn : tx ∉ (E.σ n).hist p) : A.X.inputs tx ⊆ (E.σ n).hist p := by
  rcases E.step n with h | h
  · exact Step.inputs_subset_of_new h h' hn
  · rw [h] at h'; exact absurd h' hn

/-! ### Eventual actions of correct processes -/

variable {E}

/-- A correct process holding a signed request for `tx` echoes `tx`, unless it echoes a
transaction conflicting with `tx`. -/
theorem eventually_echo (hF : E.Fair) {r : P} (hr : r ∉ A.B) {tx : Tx} {i : ℕ}
    (hreq : A.HasReq (E.σ i) r tx)
    (hno : ∀ j tx', (r, Msg.echo tx') ∈ (E.σ j).sent → tx' ≠ tx →
      A.X.issuer tx' = A.X.issuer tx → Disjoint (A.X.inputs tx') (A.X.inputs tx)) :
    ∃ j, (r, Msg.echo tx) ∈ (E.σ j).sent := by
  by_contra hne
  push Not at hne
  obtain ⟨j, hj⟩ := hF.echo r tx i fun j hij =>
    ⟨hr, hreq.mono (E.rcv_mono hij), fun tx' h1 hiss =>
      hno j tx' h1 (fun e => hne j (e ▸ h1)) hiss⟩
  exact hne j hj

/-- A correct process that has echoes for `tx` from one of its quorums, all inputs of `tx`, and
never accepts a transaction conflicting with `tx`, eventually accepts `tx`. -/
theorem eventually_accept (hF : E.Fair) {q : P} (hq : q ∉ A.B) {tx : Tx} {i : ℕ}
    (hQ : ∃ Q ∈ A.T.Q q, ∀ r ∈ Q, (q, r, Msg.echo tx) ∈ (E.σ i).rcv)
    (hin : A.X.inputs tx ⊆ (E.σ i).hist q) (hval : A.X.Valid tx)
    (hno : ∀ j, ∀ tx' ∈ (E.σ j).hist q, tx' ≠ tx → A.X.issuer tx' = A.X.issuer tx →
      Disjoint (A.X.inputs tx') (A.X.inputs tx)) :
    ∃ j, tx ∈ (E.σ j).hist q := by
  by_contra hne
  push Not at hne
  obtain ⟨Q, hQ, hQe⟩ := hQ
  obtain ⟨j, hj⟩ := hF.accept q tx i fun j hij =>
    ⟨hq, hne j, ⟨Q, hQ, fun r hr => E.rcv_mono hij (hQe r hr)⟩,
      hin.trans (E.hist_mono hij q), hval,
      fun tx' htx' hiss => hno j tx' htx' (fun e => hne j (e ▸ htx')) hiss⟩
  exact hne j hj

/-- A correct process holding signed requests for two conflicting transactions of `w`
eventually accuses `w`. -/
theorem eventually_accuse (hF : E.Fair) {q w : P} (hq : q ∉ A.B) {tx tx' : Tx} {i : ℕ}
    (h1 : A.HasReq (E.σ i) q tx) (h2 : A.HasReq (E.σ i) q tx') (hv : A.VerifyAcc w tx tx') :
    ∃ j, (w, tx, tx') ∈ acHist (E.σ j) q :=
  hF.accuse q w tx tx' i fun _ hij =>
    ⟨hq, h1.mono (E.rcv_mono hij), h2.mono (E.rcv_mono hij), hv⟩

/-- A correct process relays every verifiable accusation it receives. -/
theorem eventually_relay (hF : E.Fair) {q s w : P} (hq : q ∉ A.B) {tx tx' : Tx} {i : ℕ}
    (hr : (q, s, Msg.acc w tx tx') ∈ (E.σ i).rcv) (hv : A.VerifyAcc w tx tx') :
    ∃ j, (w, tx, tx') ∈ acHist (E.σ j) q :=
  hF.relay q s w tx tx' i fun _ hij => ⟨hq, E.rcv_mono hij hr, hv⟩

end Exec

/-! ### Agreement and Eventual Conviction -/

/-- **Agreement** (Theorem 4.8): if a correct process `p` adds an accusation to its accusation
history, every correct process `q` eventually adds it to its accusation history. -/
theorem agreement {E : A.Exec} (hF : E.Fair) {p q : P} (hp : p ∉ A.B) (hq : q ∉ A.B)
    {a : P × Tx × Tx} {i : ℕ} (ha : a ∈ acHist (E.σ i) p) : ∃ j, a ∈ acHist (E.σ j) q := by
  obtain ⟨w, tx, tx'⟩ := a
  obtain ⟨j, hj⟩ := hF.deliver q p _ i hq hp ha
  exact Exec.eventually_relay hF hq hj ((E.inv i).acc_sent p w tx tx' hp ha).1

/-- Eventual Conviction, strong form: if correct processes `p` and `q` accept conflicting
transactions `tx` and `tx'`, then both eventually hold the same accusation `(w, tx, tx')`
against the issuer `w` of `tx` and `tx'`. -/
theorem conviction (hself : A.T.SelfMem) {E : A.Exec} (hF : E.Fair) {p q : P} (hp : p ∉ A.B)
    (hq : q ∉ A.B) {tx tx' : Tx} {i i' : ℕ} (htx : tx ∈ (E.σ i).hist p)
    (htx' : tx' ∈ (E.σ i').hist q) (hc : A.X.Conflict tx tx') :
    ∃ w j, A.X.issuer tx = some w ∧ (w, tx, tx') ∈ acHist (E.σ j) p ∧
      (w, tx, tx') ∈ acHist (E.σ j) q := by
  have hne : tx ≠ A.X.init := fun e =>
    hc.2.2 (by rw [e, A.X.inputs_init]; exact Finset.disjoint_empty_left _)
  have hne' : tx' ≠ A.X.init := fun e =>
    hc.2.2 (by rw [e, A.X.inputs_init]; exact Finset.disjoint_empty_right _)
  obtain ⟨w, hw⟩ := exists_issuer_of_valid (((E.inv i).wf p hp).valid tx htx hne)
  have he := (E.inv i).echo_of_mem hself hp htx hne
  have he' := (E.inv i').echo_of_mem hself hq htx' hne'
  obtain ⟨j1, hj1⟩ := hF.deliver q p _ i hq hp he
  obtain ⟨j2, hj2⟩ := hF.deliver q q _ i' hq hq he'
  have hv : A.VerifyAcc w tx tx' := ⟨hc.1, hw, by rw [← hc.2.1]; exact hw, hc.2.2⟩
  obtain ⟨j3, hj3⟩ := Exec.eventually_accuse hF hq (i := max j1 j2)
    (Or.inr ⟨p, E.rcv_mono (le_max_left _ _) hj1⟩)
    (Or.inr ⟨q, E.rcv_mono (le_max_right _ _) hj2⟩) hv
  obtain ⟨j4, hj4⟩ := agreement hF hq hp hj3
  exact ⟨w, max j3 j4, hw, E.acHist_mono (le_max_right _ _) p hj4,
    E.acHist_mono (le_max_left _ _) q hj3⟩

/-- **Lemma 4.5** (Eventual Conviction): if correct processes `p` and `q` add conflicting
transactions `tx` to `T_p` and `tx'` to `T_q`, then they eventually add an accusation referring
to `tx` and an accusation referring to `tx'` to `A_p` and `A_q`. -/
theorem lemma_4_5 (hself : A.T.SelfMem) {E : A.Exec} (hF : E.Fair) {p q : P} (hp : p ∉ A.B)
    (hq : q ∉ A.B) {tx tx' : Tx} {i i' : ℕ} (htx : tx ∈ (E.σ i).hist p)
    (htx' : tx' ∈ (E.σ i').hist q) (hc : A.X.Conflict tx tx') :
    ∃ j, (∃ a ∈ acHist (E.σ j) p, RefersTo a tx) ∧ (∃ a ∈ acHist (E.σ j) p, RefersTo a tx') ∧
      (∃ a ∈ acHist (E.σ j) q, RefersTo a tx) ∧ (∃ a ∈ acHist (E.σ j) q, RefersTo a tx') := by
  obtain ⟨w, j, -, h1, h2⟩ := conviction hself hF hp hq htx htx' hc
  exact ⟨j, ⟨_, h1, Or.inl rfl⟩, ⟨_, h1, Or.inr rfl⟩, ⟨_, h2, Or.inl rfl⟩, ⟨_, h2, Or.inr rfl⟩⟩

/-! ### Termination and Validity -/

namespace Exec

variable {E : A.Exec}

/-- Either all inputs of `tx` eventually reach `T_q`, or `q` eventually holds an accusation
referring to a transaction on which `tx` depends. -/
theorem inputs_or_acc {q : P} {tx : Tx}
    (h : ∀ t ∈ A.X.inputs tx, ∃ j, t ∈ (E.σ j).hist q ∨
      ∃ a ∈ acHist (E.σ j) q, RefersTo a t ∨ ∃ t', A.X.DependsOn t t' ∧ RefersTo a t') :
    (∃ j, A.X.inputs tx ⊆ (E.σ j).hist q) ∨
      ∃ j, ∃ a ∈ acHist (E.σ j) q, ∃ t, A.X.DependsOn tx t ∧ RefersTo a t := by
  by_cases hacc : ∃ j, ∃ a ∈ acHist (E.σ j) q, ∃ t, A.X.DependsOn tx t ∧ RefersTo a t
  · exact Or.inr hacc
  · left
    have hall : ∀ t : A.X.inputs tx, ∃ j, (t : Tx) ∈ (E.σ j).hist q := by
      rintro ⟨t, ht⟩
      obtain ⟨j, hj | ⟨a, ha, hr | ⟨t', hdep, hr⟩⟩⟩ := h t ht
      · exact ⟨j, hj⟩
      · exact absurd ⟨j, a, ha, t, Relation.TransGen.single ht, hr⟩ hacc
      · exact absurd ⟨j, a, ha, t', Relation.TransGen.tail hdep ht, hr⟩ hacc
    obtain ⟨j, hj⟩ := exists_forall_of_mono (fun (t : A.X.inputs tx) j => (t : Tx) ∈ (E.σ j).hist q)
      (fun _ _ _ hij h => E.hist_mono hij q h) hall
    exact ⟨j, fun t ht => hj ⟨t, ht⟩⟩

/-- Common core of Lemmas 4.6 and 4.7. Let `q` be live and correct, and `tx` a valid transaction
of `w` whose signed request every correct process eventually holds and whose inputs eventually
are in `T_q`. Then `q` eventually accepts `tx`, or accuses `w` with `tx` and a conflicting
transaction. (Either a member of `q`'s correct quorum echoes a conflicting transaction, which
`q` then receives; or all of them echo `tx`, and `q` accepts it.) -/
theorem accept_or_accuse (hself : A.T.SelfMem) (hF : E.Fair) {q : P} (hq : q ∉ A.B)
    (hlive : A.T.Live A.B q) {tx : Tx} {w : P} (hw : A.X.issuer tx = some w)
    (hval : A.X.Valid tx) (hreq : ∀ r ∉ A.B, ∃ j, A.HasReq (E.σ j) r tx)
    (hin : ∃ j, A.X.inputs tx ⊆ (E.σ j).hist q) :
    ∃ j, tx ∈ (E.σ j).hist q ∨
      ∃ tx', A.X.Conflict tx tx' ∧ (w, tx, tx') ∈ acHist (E.σ j) q := by
  obtain ⟨Q, hQ, hQB⟩ := hlive
  have hQc : ∀ r ∈ Q, r ∉ A.B := fun r hr => Finset.disjoint_left.mp hQB hr
  obtain ⟨j0, hj0⟩ := hreq q hq
  by_cases hc : ∃ r ∈ Q, ∃ j tx', (r, Msg.echo tx') ∈ (E.σ j).sent ∧ A.X.Conflict tx tx'
  · obtain ⟨r, hrQ, j1, tx', hj1, hcf⟩ := hc
    obtain ⟨j2, hj2⟩ := hF.deliver q r _ j1 hq (hQc r hrQ) hj1
    have hv : A.VerifyAcc w tx tx' := ⟨hcf.1, hw, by rw [← hcf.2.1]; exact hw, hcf.2.2⟩
    obtain ⟨j, hj⟩ := eventually_accuse hF hq (i := max j0 j2)
      (hj0.mono (E.rcv_mono (le_max_left _ _))) (Or.inr ⟨r, E.rcv_mono (le_max_right _ _) hj2⟩) hv
    exact ⟨j, Or.inr ⟨tx', hcf, hj⟩⟩
  · push Not at hc
    have hech : ∀ r : Q, ∃ j, (q, (r : P), Msg.echo tx) ∈ (E.σ j).rcv := by
      rintro ⟨r, hrQ⟩
      obtain ⟨j1, hj1⟩ := hreq r (hQc r hrQ)
      obtain ⟨j2, hj2⟩ := eventually_echo hF (hQc r hrQ) hj1 fun j tx' h1 hne hiss => by
        by_contra hd
        exact hc r hrQ j tx' h1 ⟨hne.symm, hiss.symm, fun h => hd h.symm⟩
      exact hF.deliver q r _ j2 hq (hQc r hrQ) hj2
    obtain ⟨j3, hj3⟩ := exists_forall_of_mono
      (fun (r : Q) j => (q, (r : P), Msg.echo tx) ∈ (E.σ j).rcv)
      (fun _ _ _ hij h => E.rcv_mono hij h) hech
    obtain ⟨j4, hj4⟩ := hin
    obtain ⟨j, hj⟩ := eventually_accept hF hq (i := max j3 j4)
      ⟨Q, hQ, fun r hr => E.rcv_mono (le_max_left _ _) (hj3 ⟨r, hr⟩)⟩
      (hj4.trans (E.hist_mono (le_max_right _ _) q)) hval fun j tx' htx' hne hiss => by
        by_contra hd
        have hne' : tx' ≠ A.X.init := fun e => by
          rw [e, A.X.issuer_init, hw] at hiss; exact absurd hiss (by simp)
        exact hc q (hself q Q hQ) j tx' ((E.inv j).echo_of_mem hself hq htx' hne')
          ⟨hne.symm, hiss.symm, fun h => hd h.symm⟩
    exact ⟨j, Or.inl hj⟩

end Exec

/-- **Lemma 4.6** (Termination): if a correct process `p` adds a transaction `tx` to `T_p`, then
every live correct process `q` eventually adds `tx` to `T_q` or an accusation referring to `tx`
(or to some transaction on which `tx` depends) to `A_q`. -/
theorem lemma_4_6 (hself : A.T.SelfMem) {E : A.Exec} (hF : E.Fair) {p q : P} (hp : p ∉ A.B)
    (hq : q ∉ A.B) (hlive : A.T.Live A.B q) {tx : Tx} {i : ℕ} (htx : tx ∈ (E.σ i).hist p) :
    ∃ j, tx ∈ (E.σ j).hist q ∨
      ∃ a ∈ acHist (E.σ j) q, RefersTo a tx ∨ ∃ t, A.X.DependsOn tx t ∧ RefersTo a t := by
  -- induction on the time at which `tx` was accepted by `p`: its inputs were accepted before
  induction i generalizing tx with
  | zero =>
    rw [E.zero] at htx
    have : tx = A.X.init := by simpa [init] using htx
    subst this
    exact ⟨0, Or.inl (by rw [E.zero]; simp [init])⟩
  | succ n ih =>
    by_cases hold : tx ∈ (E.σ n).hist p
    · exact ih hold
    · have hin := E.inputs_subset_of_new htx hold
      have hne : tx ≠ A.X.init := fun e => hold (e ▸ ((E.inv n).wf p hp).init_mem)
      rcases Exec.inputs_or_acc (fun t ht => ih (hin ht)) with hin' | ⟨j, a, ha, t, hdep, hr⟩
      · have hval := ((E.inv (n + 1)).wf p hp).valid tx htx hne
        obtain ⟨w, hw⟩ := exists_issuer_of_valid hval
        have hecho := (E.inv (n + 1)).echo_of_mem hself hp htx hne
        obtain ⟨j, hj | ⟨tx', -, hj⟩⟩ := Exec.accept_or_accuse hself hF hq hlive hw hval
          (fun r hr => (hF.deliver r p _ _ hr hp hecho).imp fun _ hj => Or.inr ⟨p, hj⟩) hin'
        · exact ⟨j, Or.inl hj⟩
        · exact ⟨j, Or.inr ⟨_, hj, Or.inl (Or.inl rfl)⟩⟩
      · exact ⟨j, Or.inr ⟨a, ha, Or.inr ⟨t, hdep, hr⟩⟩⟩

/-- **Lemma 4.7** (Validity): if a correct process `p` issues a transaction `tx` (sends its
`REQ`), then every live correct process `q` eventually adds `tx` to `T_q`, or adds an accusation
to `A_q` referring to some transaction on which `tx` depends.

Three hypotheses are implicit in the paper:
* `hhon`: correct processes never issue conflicting transactions ("since `p` is correct, it will
  not send conflicting requests");
* `hval`: `tx` is valid (§4.3: "we assume that transactions issued by correct processes are
  always valid"), otherwise nobody accepts it;
* `hdeps`: the issuer eventually accepts all inputs of `tx` ("`p` must have previously added
  every transaction on which `tx` depends to trHist"), otherwise the inputs may be unknown to
  every correct process. -/
theorem lemma_4_7 (hself : A.T.SelfMem) (hhon : A.HonestIssuers) {E : A.Exec} (hF : E.Fair)
    {p q : P} (hp : p ∉ A.B) (hq : q ∉ A.B) (hlive : A.T.Live A.B q) {tx : Tx} {i : ℕ}
    (hiss : (p, Msg.req tx) ∈ (E.σ i).sent) (hval : A.X.Valid tx)
    (hdeps : ∃ i', A.X.inputs tx ⊆ (E.σ i').hist p) :
    ∃ j, tx ∈ (E.σ j).hist q ∨ ∃ a ∈ acHist (E.σ j) q, ∃ t, A.X.DependsOn tx t ∧ RefersTo a t := by
  obtain ⟨i', hi'⟩ := hdeps
  have hw : A.X.issuer tx = some p := (E.reachable i).req_issuer hiss
  rcases Exec.inputs_or_acc (fun t ht => lemma_4_6 hself hF hp hq hlive (hi' ht)) with hin | hacc
  · obtain ⟨j, hj | ⟨tx', hcf, hj⟩⟩ := Exec.accept_or_accuse hself hF hq hlive hw hval
      (fun r hr => (hF.deliver r p _ i hr hp hiss).imp fun _ hj => Or.inl ⟨p, hw, hj⟩) hin
    · exact ⟨j, Or.inl hj⟩
    · -- an accusation against the correct issuer `p` is impossible
      exfalso
      obtain ⟨-, -, ⟨w', hw', hs⟩⟩ := (E.inv j).acc_sent q p tx tx' hq hj
      rw [← hcf.2.1, hw] at hw'
      obtain rfl := Option.some_injective _ hw'
      exact hhon _ hp tx ((E.inv i).req_issue _ tx hp hiss) tx'
        ((E.inv j).req_issue _ tx' hp (hs.resolve_left hp)) hcf
  · obtain ⟨j, h⟩ := hacc
    exact ⟨j, Or.inr h⟩

/-- **Lemma 4.7** for a transaction `tx` of `p` that the application of `p` asks to transfer
(`transfer(tx)` is eventually executed by fairness). -/
theorem lemma_4_7_of_issue (hself : A.T.SelfMem) (hhon : A.HonestIssuers) {E : A.Exec}
    (hF : E.Fair) {p q : P} (hp : p ∉ A.B) (hq : q ∉ A.B) (hlive : A.T.Live A.B q) {tx : Tx}
    (hiss : tx ∈ A.issue p) (hown : A.X.issuer tx = some p) (hval : A.X.Valid tx)
    (hdeps : ∃ i', A.X.inputs tx ⊆ (E.σ i').hist p) :
    ∃ j, tx ∈ (E.σ j).hist q ∨ ∃ a ∈ acHist (E.σ j) q, ∃ t, A.X.DependsOn tx t ∧ RefersTo a t :=
  let ⟨_, hi⟩ := hF.issue p tx ⟨hp, hiss, hown⟩
  lemma_4_7 hself hhon hF hp hq hlive hi hval hdeps

/-! ### Fair executions exist -/

section RoundRobin

variable [Encodable P] [Encodable Tx]

/-- The events scheduled by the round robin: issue, echo, accept, accuse, relay, deliver. -/
private abbrev Ev (P Tx : Type*) :=
  (P × Tx) ⊕ (P × Tx) ⊕ (P × Tx) ⊕ (P × P × Tx × Tx) ⊕ (P × P × P × Tx × Tx) ⊕ (P × P × Msg P Tx)

open Classical in
/-- Apply an event if it is enabled (Byzantine processes stay silent). -/
private noncomputable def apply (A : Setup P Tx) : Option (Ev P Tx) → State P Tx → State P Tx
  | some (.inl (p, tx)), σ =>
    if A.IssueEnabled p tx then { σ with sent := insert (p, .req tx) σ.sent } else σ
  | some (.inr (.inl (p, tx))), σ =>
    if A.EchoEnabled σ p tx then { σ with sent := insert (p, .echo tx) σ.sent } else σ
  | some (.inr (.inr (.inl (p, tx)))), σ =>
    if A.AcceptEnabled σ p tx then
      { σ with hist := Function.update σ.hist p (insert tx (σ.hist p)) } else σ
  | some (.inr (.inr (.inr (.inl (p, w, tx, tx'))))), σ =>
    if A.AccuseEnabled σ p w tx tx' then { σ with sent := insert (p, .acc w tx tx') σ.sent }
    else σ
  | some (.inr (.inr (.inr (.inr (.inl (p, s, w, tx, tx')))))), σ =>
    if A.RelayEnabled σ p s w tx tx' then { σ with sent := insert (p, .acc w tx tx') σ.sent }
    else σ
  | some (.inr (.inr (.inr (.inr (.inr (q, s, m)))))), σ =>
    if (s, m) ∈ σ.sent then { σ with rcv := insert (q, s, m) σ.rcv } else σ
  | none, σ => σ

/-- The schedule: every event occurs at arbitrarily late positions. -/
private def sched (i : ℕ) : Option (Ev P Tx) := Encodable.decode (Nat.unpair i).1

omit [Fintype P] [DecidableEq P] [DecidableEq Tx] in
private theorem sched_hits (e : Ev P Tx) (i : ℕ) : ∃ j, i ≤ j ∧ sched j = some e :=
  ⟨Nat.pair (Encodable.encode e) i, Nat.right_le_pair _ _, by simp [sched, Nat.unpair_pair]⟩

private noncomputable def rrσ (A : Setup P Tx) : ℕ → State P Tx
  | 0 => A.init
  | i + 1 => apply A (sched i) (rrσ A i)

private theorem rr_step (A : Setup P Tx) (i : ℕ) :
    A.Step (rrσ A i) (rrσ A (i + 1)) ∨ rrσ A (i + 1) = rrσ A i := by
  simp only [rrσ]
  rcases sched (P := P) (Tx := Tx) i with _ | (⟨p, tx⟩ | ⟨p, tx⟩ | ⟨p, tx⟩ | ⟨p, w, tx, tx'⟩ |
    ⟨p, s, w, tx, tx'⟩ | ⟨q, s, m⟩)
  · exact Or.inr rfl
  all_goals
    simp only [apply]
    split_ifs with h
    · first
        | exact Or.inl (h.step _)
        | exact Or.inl h.step
        | exact Or.inl (Step.deliver _ _ _ _ h)
    · exact Or.inr rfl

/-- **Fair executions exist** (round robin over all issue, echo, accept, accuse, relay and
delivery events, Byzantine processes silent), so the liveness results are not vacuous. -/
theorem exists_fair_enc (A : Setup P Tx) : ∃ E : A.Exec, E.Fair := by
  classical
  let E : A.Exec := ⟨rrσ A, rfl, rr_step A⟩
  refine ⟨E, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro q s m i _ _ hm
    obtain ⟨j, hij, hj⟩ := sched_hits (P := P) (Tx := Tx) (.inr (.inr (.inr (.inr (.inr
      (q, s, m)))))) i
    refine ⟨j + 1, ?_⟩
    have hm' : (s, m) ∈ (rrσ A j).sent := E.sent_mono hij hm
    show (q, s, m) ∈ (rrσ A (j + 1)).rcv
    simp only [rrσ, hj, apply, hm', ↓reduceIte]
    exact Set.mem_insert _ _
  · intro p tx hg
    obtain ⟨j, -, hj⟩ := sched_hits (P := P) (Tx := Tx) (.inl (p, tx)) 0
    refine ⟨j + 1, ?_⟩
    show (p, Msg.req tx) ∈ (rrσ A (j + 1)).sent
    simp only [rrσ, hj, apply, hg, ↓reduceIte]
    exact Set.mem_insert _ _
  · intro p tx i hg
    obtain ⟨j, hij, hj⟩ := sched_hits (P := P) (Tx := Tx) (.inr (.inl (p, tx))) i
    refine ⟨j + 1, ?_⟩
    show (p, Msg.echo tx) ∈ (rrσ A (j + 1)).sent
    simp only [rrσ, hj, apply]
    split_ifs with hc
    · exact Set.mem_insert _ _
    · exact absurd (hg j hij) hc
  · intro p tx i hg
    obtain ⟨j, hij, hj⟩ := sched_hits (P := P) (Tx := Tx) (.inr (.inr (.inl (p, tx)))) i
    refine ⟨j + 1, ?_⟩
    show tx ∈ (rrσ A (j + 1)).hist p
    simp only [rrσ, hj, apply]
    split_ifs with hc
    · simp only [Function.update_self]; exact Finset.mem_insert_self _ _
    · exact absurd (hg j hij) hc
  · intro p w tx tx' i hg
    obtain ⟨j, hij, hj⟩ := sched_hits (P := P) (Tx := Tx) (.inr (.inr (.inr (.inl
      (p, w, tx, tx'))))) i
    refine ⟨j + 1, ?_⟩
    show (p, Msg.acc w tx tx') ∈ (rrσ A (j + 1)).sent
    simp only [rrσ, hj, apply]
    split_ifs with hc
    · exact Set.mem_insert _ _
    · exact absurd (hg j hij) hc
  · intro p s w tx tx' i hg
    obtain ⟨j, hij, hj⟩ := sched_hits (P := P) (Tx := Tx) (.inr (.inr (.inr (.inr (.inl
      (p, s, w, tx, tx')))))) i
    refine ⟨j + 1, ?_⟩
    show (p, Msg.acc w tx tx') ∈ (rrσ A (j + 1)).sent
    simp only [rrσ, hj, apply]
    split_ifs with hc
    · exact Set.mem_insert _ _
    · exact absurd (hg j hij) hc

end RoundRobin

/-- **Fair executions exist** for countable sets of processes and transactions. -/
theorem exists_fair [Countable P] [Countable Tx] (A : Setup P Tx) : ∃ E : A.Exec, E.Fair := by
  have := Encodable.ofCountable P
  have := Encodable.ofCountable Tx
  exact exists_fair_enc A

end Setup

/-! ### Validity needs the issuer to have accepted the inputs

The paper's proof of Lemma 4.7 claims that the issuer `p` "must have previously added every
transaction on which `tx` depends to trHist", but `transfer(tx)` (lines 1–3) does not check this.
Without the hypothesis `hdeps` Validity fails: one correct, live process `0` issues a valid `tx`
whose input `t` is never issued by anyone; `t`, hence `tx`, is never accepted, and no accusation
is ever produced. -/

namespace ValidityCex

/-- Transactions `0 = tx_init`, `1 = t` (never issued), `2 = tx` (input `t`), all paying `1`
to process `0`. -/
def X : TxSystem (Fin 1) (Fin 3) where
  issuer i := if i = 0 then none else some 0
  out _ _ := 1
  inputs i := if i = 2 then {1} else if i = 1 then {0} else ∅
  init := 0
  issuer_init := rfl
  inputs_init := rfl

/-- One correct process `0`; its application asks to transfer `tx = 2` only. -/
def A : Setup (Fin 1) (Fin 3) := ⟨X, ⟨fun _ => {{0}}, {∅}⟩, ∅, fun _ => {2}⟩

theorem signed_eq {σ : State (Fin 1) (Fin 3)} (hI : A.Inv σ) {x : Fin 3} (h : A.Signed σ x) :
    x = 2 := by
  obtain ⟨w, -, hw | hw⟩ := h
  · simp [A] at hw
  · simpa [A] using hI.req_issue w x (by simp [A]) hw

theorem not_mem_hist {σ : State (Fin 1) (Fin 3)} (hI : A.Inv σ) : 2 ∉ σ.hist 0 := by
  intro h2
  have h1 : (1 : Fin 3) ∈ σ.hist 0 :=
    (hI.wf 0 (by simp [A])).complete 2 h2 (by simp [A, X])
  obtain ⟨Q, hQ, hQe⟩ := hI.quorum 0 1 (by simp [A]) h1 (by simp [A, X])
  have hQ0 : Q = {0} := by simpa [A] using hQ
  have := signed_eq hI (hI.echo_signed _ _ _ (hQe 0 (by simp [hQ0])))
  exact absurd this (by decide)

theorem acHist_empty {σ : State (Fin 1) (Fin 3)} (hI : A.Inv σ) : Setup.acHist σ 0 = ∅ := by
  ext ⟨w, x, y⟩
  simp only [Set.mem_empty_iff_false, iff_false]
  intro h
  obtain ⟨⟨hne, -⟩, hx, hy⟩ := hI.acc_sent 0 w x y (by simp [A]) h
  exact hne ((signed_eq hI hx).trans (signed_eq hI hy).symm)

/-- **Validity (Lemma 4.7) fails without `hdeps`**: all other hypotheses of `lemma_4_7` hold
(`SelfMem`, honest issuers, `0` live and correct, `tx = 2` valid and issued, fair execution), yet
`0` never accepts `tx` and never holds an accusation. -/
theorem validity_needs_inputs :
    A.T.SelfMem ∧ A.HonestIssuers ∧ A.T.Live A.B 0 ∧ A.X.Valid 2 ∧
      ∃ E : A.Exec, E.Fair ∧ (∃ i, ((0 : Fin 1), Msg.req (2 : Fin 3)) ∈ (E.σ i).sent) ∧
        ∀ j, 2 ∉ (E.σ j).hist 0 ∧ Setup.acHist (E.σ j) 0 = ∅ := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro p Q hQ
    have : Q = {0} := by simpa [A] using hQ
    simp [this, Fin.fin_one_eq_zero p]
  · intro p _ t ht t' ht' hc
    have e1 : t = 2 := by simpa [A] using ht
    have e2 : t' = 2 := by simpa [A] using ht'
    exact hc.1 (e1.trans e2.symm)
  · exact ⟨{0}, by simp [A], by simp [A]⟩
  · exact ⟨by decide, by decide⟩
  · obtain ⟨E, hF⟩ := Setup.exists_fair A
    exact ⟨E, hF, hF.issue 0 2 ⟨by simp [A], by simp [A], by simp [A, X]⟩,
      fun j => ⟨not_mem_hist (E.inv j), acHist_empty (E.inv j)⟩⟩

end ValidityCex

end Podc.MultipleSpending
