import Papers.PODC2022.MultipleSpending.Trust
import Papers.PODC2022.MultipleSpending.Transactions

/-!
# The `k`-spending asset-transfer protocol (Algorithms 1–2): model and invariants

An interleaving model of Algorithms 1–2 in the asynchronous Byzantine model with a **static**
faulty set `B` (the paper's `F` of the run). Correct processes (`p ∉ B`) follow the protocol;
Byzantine processes can make anybody receive any message from them, except that they cannot
forge the signature of an issuer that is not Byzantine (`MsgSigned`).

Message types: `req tx` (`REQ`, signed by the issuer), `echo tx` (`ECHO` carrying the issuer's
signed request), `acc w tx tx'` (`ACC` with the accusation `({w}, {tx, tx'})`). Channels are
authenticated (a reception `(q, s, m)` records the true sender `s`) and fully asynchronous:
a sent message can be received at any time, never, or several times.

The local variables of Algorithm 1–2 are derived from the messages: `usedInp[s]` = inputs of the
transactions from `s` that `p` echoed; `signedRequests` = transactions whose signed request `p`
received (`HasReq`); `acHist` = accusations `p` sent (lines 31–32 and 35–36 add and send
together). `trHist` is the explicit `hist p` (initially `{tx_init}`). The guards are *liberal*:
`p` may echo whenever it has received the request and `usedInp` allows it (in the code it does so
right upon reception; since `usedInp` only grows, this is a superset of the code's behaviours, so
safety results transfer). Line 5 of Algorithm 1 verifies the `REQ` signature with the *sender's*
key; we read it as the issuer's key (the text: "σ is a signature for tx from tx.s"), i.e. a
`REQ` counts only when received from the issuer. Line 26 needs `tx ≠ tx'` (text: "distinct
transactions").
-/

namespace Podc.MultipleSpending

open Finset

/-- Messages of Algorithms 1–2. -/
inductive Msg (P Tx : Type*)
  | req (tx : Tx)
  | echo (tx : Tx)
  | acc (w : P) (tx tx' : Tx)

/-- A global state. -/
structure State (P Tx : Type*) where
  /-- `(p, m)`: correct process `p` sent `m` to all. -/
  sent : Set (P × Msg P Tx)
  /-- `(q, s, m)`: `q` received `m` from `s`. -/
  rcv : Set (P × P × Msg P Tx)
  /-- `trHist` of each process. -/
  hist : P → Finset Tx

variable {P Tx : Type*} [Fintype P] [DecidableEq P] [DecidableEq Tx]

/-- The data of a run: transactions, trust model (only its quorum map is used by the protocol),
the static set `B` of Byzantine processes, and the transactions `issue p` the application of
`p` asks to transfer. -/
structure Setup (P Tx : Type*) where
  X : TxSystem P Tx
  T : TrustModel P
  B : Finset P
  issue : P → Set Tx

namespace Setup

variable (A : Setup P Tx)

/-- The initial state. -/
def init : State P Tx := ⟨∅, ∅, fun _ => {A.X.init}⟩

/-- `tx` carries a valid signature of its issuer: the issuer is Byzantine (it signs anything) or
it sent the request for `tx`. -/
def Signed (σ : State P Tx) (tx : Tx) : Prop :=
  ∃ w, A.X.issuer tx = some w ∧ (w ∈ A.B ∨ (w, Msg.req tx) ∈ σ.sent)

/-- Messages a Byzantine process can produce: it cannot forge signatures of others. -/
def MsgSigned (σ : State P Tx) : Msg P Tx → Prop
  | .req _ => True
  | .echo tx => A.Signed σ tx
  | .acc _ tx tx' => A.Signed σ tx ∧ A.Signed σ tx'

/-- `p` holds a signed request for `tx` (`signedRequests`): a `REQ` from the issuer or an
`ECHO`. -/
def HasReq (σ : State P Tx) (p : P) (tx : Tx) : Prop :=
  (∃ w, A.X.issuer tx = some w ∧ (p, w, Msg.req tx) ∈ σ.rcv) ∨ ∃ s, (p, s, Msg.echo tx) ∈ σ.rcv

/-- `verify-acc` (signatures are checked by `MsgSigned`): two distinct conflicting transactions
of `w`. -/
def VerifyAcc (w : P) (tx tx' : Tx) : Prop :=
  tx ≠ tx' ∧ A.X.issuer tx = some w ∧ A.X.issuer tx' = some w ∧
    ¬ Disjoint (A.X.inputs tx) (A.X.inputs tx')

/-- One step of the system. -/
inductive Step : State P Tx → State P Tx → Prop
  /-- `transfer(tx)` (lines 1–3). -/
  | issue (σ : State P Tx) (p : P) (tx : Tx) :
      p ∉ A.B → tx ∈ A.issue p → A.X.issuer tx = some p →
      Step σ { σ with sent := insert (p, .req tx) σ.sent }
  /-- Echo a received request (lines 4–10, 11–19). -/
  | echo (σ : State P Tx) (p : P) (tx : Tx) :
      p ∉ A.B → A.HasReq σ p tx →
      (∀ tx', (p, Msg.echo tx') ∈ σ.sent → A.X.issuer tx' = A.X.issuer tx →
        Disjoint (A.X.inputs tx') (A.X.inputs tx)) →
      Step σ { σ with sent := insert (p, .echo tx) σ.sent }
  /-- Accept a transaction echoed by a quorum once `ready` holds (lines 20–25, 37–41). -/
  | accept (σ : State P Tx) (p : P) (tx : Tx) :
      p ∉ A.B → tx ∉ σ.hist p → (∃ Q ∈ A.T.Q p, ∀ q ∈ Q, (p, q, Msg.echo tx) ∈ σ.rcv) →
      A.X.inputs tx ⊆ σ.hist p → A.X.Valid tx →
      (∀ tx' ∈ σ.hist p, A.X.issuer tx' = A.X.issuer tx →
        Disjoint (A.X.inputs tx') (A.X.inputs tx)) →
      Step σ { σ with hist := Function.update σ.hist p (insert tx (σ.hist p)) }
  /-- Build an accusation from two conflicting signed requests (lines 26–32). -/
  | accuse (σ : State P Tx) (p w : P) (tx tx' : Tx) :
      p ∉ A.B → A.HasReq σ p tx → A.HasReq σ p tx' → A.VerifyAcc w tx tx' →
      Step σ { σ with sent := insert (p, .acc w tx tx') σ.sent }
  /-- Relay a verified accusation (lines 33–36). -/
  | relay (σ : State P Tx) (p s w : P) (tx tx' : Tx) :
      p ∉ A.B → (p, s, Msg.acc w tx tx') ∈ σ.rcv → A.VerifyAcc w tx tx' →
      Step σ { σ with sent := insert (p, .acc w tx tx') σ.sent }
  /-- A message sent by a correct process is received. -/
  | deliver (σ : State P Tx) (q s : P) (m : Msg P Tx) :
      (s, m) ∈ σ.sent → Step σ { σ with rcv := insert (q, s, m) σ.rcv }
  /-- A Byzantine process makes `q` receive a message it can produce. -/
  | inject (σ : State P Tx) (q b : P) (m : Msg P Tx) :
      b ∈ A.B → A.MsgSigned σ m → Step σ { σ with rcv := insert (q, b, m) σ.rcv }

/-- Reachable states. -/
def Reachable (σ : State P Tx) : Prop := Relation.ReflTransGen A.Step A.init σ

/-- The collection `Γ` of the histories of the correct processes. -/
def Γ (σ : State P Tx) : Set (Finset Tx) := {T | ∃ p ∉ A.B, T = σ.hist p}

/-- The accusation history `acHist` of `p`. -/
def acHist (σ : State P Tx) (p : P) : Set (P × Tx × Tx) :=
  {a | (p, Msg.acc a.1 a.2.1 a.2.2) ∈ σ.sent}

/-! ### Monotonicity -/

theorem Step.sent_subset {σ σ' : State P Tx} (h : A.Step σ σ') : σ.sent ⊆ σ'.sent := by
  cases h <;> first | exact le_rfl | exact Set.subset_insert _ _

theorem Step.rcv_subset {σ σ' : State P Tx} (h : A.Step σ σ') : σ.rcv ⊆ σ'.rcv := by
  cases h <;> first | exact le_rfl | exact Set.subset_insert _ _

theorem Step.hist_subset {σ σ' : State P Tx} (h : A.Step σ σ') (p : P) :
    σ.hist p ⊆ σ'.hist p := by
  cases h with
  | accept q tx =>
    simp only [Function.update_apply]
    split_ifs with hpq
    · subst hpq; exact Finset.subset_insert _ _
    · exact le_rfl
  | _ => exact le_rfl

omit [Fintype P] [DecidableEq P] [DecidableEq Tx] in
theorem Signed.mono {σ σ' : State P Tx} (h : σ.sent ⊆ σ'.sent) {tx : Tx} (hs : A.Signed σ tx) :
    A.Signed σ' tx := by
  obtain ⟨w, hw, hw'⟩ := hs
  exact ⟨w, hw, hw'.imp_right fun h' => h h'⟩

/-! ### The invariant -/

/-- The conjunction of the safety invariants of Algorithms 1–2. -/
structure Inv (σ : State P Tx) : Prop where
  /-- Only correct processes send (Byzantine messages are `inject`ed). -/
  sent_correct : ∀ p m, (p, m) ∈ σ.sent → p ∉ A.B
  /-- Echoes sent carry a valid signature of the issuer. -/
  echo_sent : ∀ p tx, (p, Msg.echo tx) ∈ σ.sent → A.Signed σ tx
  /-- Authenticated channels: what is received from a correct process was sent by it. -/
  genuine : ∀ p q m, q ∉ A.B → (p, q, m) ∈ σ.rcv → (q, m) ∈ σ.sent
  /-- A correct process sends a request only for a transaction its application issued. -/
  req_issue : ∀ p tx, p ∉ A.B → (p, Msg.req tx) ∈ σ.sent → tx ∈ A.issue p
  /-- `usedInp`: a correct process echoes at most one transaction per issuer and input. -/
  echo_excl : ∀ p tx tx', p ∉ A.B → (p, Msg.echo tx) ∈ σ.sent → (p, Msg.echo tx') ∈ σ.sent →
    tx ≠ tx' → A.X.issuer tx = A.X.issuer tx' → Disjoint (A.X.inputs tx) (A.X.inputs tx')
  /-- Every echo carries a valid signature of the issuer. -/
  echo_signed : ∀ p s tx, (p, s, Msg.echo tx) ∈ σ.rcv → A.Signed σ tx
  /-- Accusations received carry valid signatures. -/
  acc_rcv_signed : ∀ p s w tx tx', (p, s, Msg.acc w tx tx') ∈ σ.rcv →
    A.Signed σ tx ∧ A.Signed σ tx'
  /-- Accusations sent by correct processes are verified and signed. -/
  acc_sent : ∀ p w tx tx', p ∉ A.B → (p, Msg.acc w tx tx') ∈ σ.sent →
    A.VerifyAcc w tx tx' ∧ A.Signed σ tx ∧ A.Signed σ tx'
  /-- Histories of correct processes are well formed (Lemma 4.3). -/
  wf : ∀ p, p ∉ A.B → A.X.WellFormed (σ.hist p)
  /-- Every accepted transaction was echoed to its acceptor by one of its quorums. -/
  quorum : ∀ p tx, p ∉ A.B → tx ∈ σ.hist p → tx ≠ A.X.init →
    ∃ Q ∈ A.T.Q p, ∀ q ∈ Q, (p, q, Msg.echo tx) ∈ σ.rcv

omit [Fintype P] [DecidableEq P] [DecidableEq Tx] in
/-- A transitive input of a member of a complete history belongs to it. -/
theorem mem_of_transGen {T : Finset Tx} (hc : ∀ tx ∈ T, A.X.inputs tx ⊆ T) {x y : Tx}
    (h : Relation.TransGen (fun a b => a ∈ A.X.inputs b) x y) (hy : y ∈ T) : x ∈ T := by
  induction h with
  | single h => exact hc _ hy h
  | tail _ h ih => exact ih (hc _ hy h)

omit [DecidableEq Tx] in
theorem HasReq.signed {σ : State P Tx} (hI : A.Inv σ) {p : P} {tx : Tx} (h : A.HasReq σ p tx) :
    A.Signed σ tx := by
  rcases h with ⟨w, hw, hr⟩ | ⟨s, hr⟩
  · by_cases hwB : w ∈ A.B
    · exact ⟨w, hw, Or.inl hwB⟩
    · exact ⟨w, hw, Or.inr (hI.genuine _ _ _ hwB hr)⟩
  · exact hI.echo_signed _ _ _ hr

omit [DecidableEq P] [DecidableEq Tx] in
theorem inv_init : A.Inv A.init := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [init]
  · intro p _
    refine ⟨by simp, ?_, ?_, ?_, ?_⟩
    · simp
    · simp [A.X.inputs_init]
    · intro tx htx tx' htx'
      simp only [Finset.mem_singleton] at htx htx'
      subst htx htx'
      exact fun h => h.1 rfl
    · intro tx htx tx' htx' _
      simp only [Finset.mem_singleton] at htx'
      subst htx'
      simp [A.X.inputs_init]

theorem inv_step {σ σ' : State P Tx} (hI : A.Inv σ) (h : A.Step σ σ') : A.Inv σ' := by
  have hsent := h.sent_subset
  have hS : ∀ tx, A.Signed σ tx → A.Signed σ' tx := fun tx => Signed.mono A hsent
  cases h with
  | issue p tx hp hiss hown =>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hI.wf, hI.quorum⟩
    · intro a m hm
      rcases Set.mem_insert_iff.mp hm with he | hm
      · simp only [Prod.mk.injEq] at he; rw [he.1]; exact hp
      · exact hI.sent_correct a m hm
    · intro a t hm
      simp only [Set.mem_insert_iff, Prod.mk.injEq, reduceCtorEq, and_false, false_or] at hm
      exact hS _ (hI.echo_sent a t hm)
    · intro a b m hb hm; exact Set.mem_insert_of_mem _ (hI.genuine a b m hb hm)
    · intro a t ha hm
      rcases Set.mem_insert_iff.mp hm with he | hm
      · simp only [Prod.mk.injEq, Msg.req.injEq] at he
        obtain ⟨rfl, rfl⟩ := he; exact hiss
      · exact hI.req_issue a t ha hm
    · intro a t t' ha h1 h2
      simp only [Set.mem_insert_iff, Prod.mk.injEq, reduceCtorEq, and_false, false_or] at h1 h2
      exact hI.echo_excl a t t' ha h1 h2
    · intro a s t hm; exact hS _ (hI.echo_signed a s t hm)
    · intro a s w t t' hm
      exact (hI.acc_rcv_signed a s w t t' hm).imp (hS _) (hS _)
    · intro a w t t' ha hm
      simp only [Set.mem_insert_iff, Prod.mk.injEq, reduceCtorEq, and_false, false_or] at hm
      obtain ⟨h1, h2, h3⟩ := hI.acc_sent a w t t' ha hm
      exact ⟨h1, hS _ h2, hS _ h3⟩
  | echo p tx hp hreq hfree =>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hI.wf, hI.quorum⟩
    · intro a m hm
      rcases Set.mem_insert_iff.mp hm with he | hm
      · simp only [Prod.mk.injEq] at he; rw [he.1]; exact hp
      · exact hI.sent_correct a m hm
    · intro a t hm
      rcases Set.mem_insert_iff.mp hm with he | hm
      · simp only [Prod.mk.injEq, Msg.echo.injEq] at he
        obtain ⟨rfl, rfl⟩ := he
        exact hS _ (HasReq.signed A hI hreq)
      · exact hS _ (hI.echo_sent a t hm)
    · intro a b m hb hm; exact Set.mem_insert_of_mem _ (hI.genuine a b m hb hm)
    · intro a t ha hm
      simp only [Set.mem_insert_iff, Prod.mk.injEq, reduceCtorEq, and_false, false_or] at hm
      exact hI.req_issue a t ha hm
    · intro a t t' ha h1 h2 hne hiss
      simp only [Set.mem_insert_iff, Prod.mk.injEq, Msg.echo.injEq] at h1 h2
      rcases h1 with ⟨h1a, rfl⟩ | h1 <;> rcases h2 with ⟨h2a, rfl⟩ | h2
      · exact absurd rfl hne
      · subst h1a; exact (hfree t' h2 hiss.symm).symm
      · subst h2a; exact hfree t h1 hiss
      · exact hI.echo_excl a t t' ha h1 h2 hne hiss
    · intro a s t hm; exact hS _ (hI.echo_signed a s t hm)
    · intro a s w t t' hm
      exact (hI.acc_rcv_signed a s w t t' hm).imp (hS _) (hS _)
    · intro a w t t' ha hm
      simp only [Set.mem_insert_iff, Prod.mk.injEq, reduceCtorEq, and_false, false_or] at hm
      obtain ⟨h1, h2, h3⟩ := hI.acc_sent a w t t' ha hm
      exact ⟨h1, hS _ h2, hS _ h3⟩
  | accept p tx hp hnot hq hin hval hfree =>
    refine ⟨hI.sent_correct, hI.echo_sent, hI.genuine, hI.req_issue, hI.echo_excl,
      hI.echo_signed, hI.acc_rcv_signed, hI.acc_sent, ?_, ?_⟩
    · intro a ha
      simp only [Function.update_apply]
      split_ifs with hap
      · subst hap
        have wf := hI.wf a ha
        refine ⟨Finset.mem_insert_of_mem wf.init_mem, ?_, ?_, ?_, ?_⟩
        · intro t ht hne
          rcases Finset.mem_insert.mp ht with rfl | ht
          · exact hval
          · exact wf.valid t ht hne
        · intro t ht
          rcases Finset.mem_insert.mp ht with rfl | ht
          · exact hin.trans (Finset.subset_insert _ _)
          · exact (wf.complete t ht).trans (Finset.subset_insert _ _)
        · intro t ht t' ht' hc
          rcases Finset.mem_insert.mp ht with h1 | h1
          · rcases Finset.mem_insert.mp ht' with h2 | h2
            · exact hc.1 (h1.trans h2.symm)
            · subst h1; exact hc.2.2 (hfree t' h2 hc.2.1.symm).symm
          · rcases Finset.mem_insert.mp ht' with h2 | h2
            · subst h2; exact hc.2.2 (hfree t h1 hc.2.1)
            · exact wf.noConflict t h1 t' h2 hc
        · intro t ht t' ht' hdep hmem
          rcases Finset.mem_insert.mp ht' with rfl | ht'
          · -- `t` is an input of the new transaction, which depends on it: then `t'` is a
            -- transitive input of `t ∈ hist`, hence already accepted
            exact hnot (mem_of_transGen A wf.complete hdep (hin hmem))
          · exact wf.cycleFree t (wf.complete t' ht' hmem) t' ht' hdep hmem
      · exact hI.wf a ha
    · intro a t ha ht hne
      simp only [Function.update_apply] at ht
      split_ifs at ht with hap
      · subst hap
        rcases Finset.mem_insert.mp ht with rfl | ht
        · exact hq
        · exact hI.quorum a t ha ht hne
      · exact hI.quorum a t ha ht hne
  | accuse p w tx tx' hp h1 h2 hv =>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hI.wf, hI.quorum⟩
    · intro a m hm
      rcases Set.mem_insert_iff.mp hm with he | hm
      · simp only [Prod.mk.injEq] at he; rw [he.1]; exact hp
      · exact hI.sent_correct a m hm
    · intro a t hm
      simp only [Set.mem_insert_iff, Prod.mk.injEq, reduceCtorEq, and_false, false_or] at hm
      exact hS _ (hI.echo_sent a t hm)
    · intro a b m hb hm; exact Set.mem_insert_of_mem _ (hI.genuine a b m hb hm)
    · intro a t ha hm
      simp only [Set.mem_insert_iff, Prod.mk.injEq, reduceCtorEq, and_false, false_or] at hm
      exact hI.req_issue a t ha hm
    · intro a t t' ha h1 h2
      simp only [Set.mem_insert_iff, Prod.mk.injEq, reduceCtorEq, and_false, false_or] at h1 h2
      exact hI.echo_excl a t t' ha h1 h2
    · intro a s t hm; exact hS _ (hI.echo_signed a s t hm)
    · intro a s w t t' hm
      exact (hI.acc_rcv_signed a s w t t' hm).imp (hS _) (hS _)
    · intro a w' t t' ha hm
      rcases Set.mem_insert_iff.mp hm with he | hm
      · simp only [Prod.mk.injEq, Msg.acc.injEq] at he
        obtain ⟨rfl, rfl, rfl, rfl⟩ := he
        exact ⟨hv, hS _ (HasReq.signed A hI h1), hS _ (HasReq.signed A hI h2)⟩
      · obtain ⟨h1, h2, h3⟩ := hI.acc_sent a w' t t' ha hm
        exact ⟨h1, hS _ h2, hS _ h3⟩
  | relay p s w tx tx' hp hr hv =>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hI.wf, hI.quorum⟩
    · intro a m hm
      rcases Set.mem_insert_iff.mp hm with he | hm
      · simp only [Prod.mk.injEq] at he; rw [he.1]; exact hp
      · exact hI.sent_correct a m hm
    · intro a t hm
      simp only [Set.mem_insert_iff, Prod.mk.injEq, reduceCtorEq, and_false, false_or] at hm
      exact hS _ (hI.echo_sent a t hm)
    · intro a b m hb hm; exact Set.mem_insert_of_mem _ (hI.genuine a b m hb hm)
    · intro a t ha hm
      simp only [Set.mem_insert_iff, Prod.mk.injEq, reduceCtorEq, and_false, false_or] at hm
      exact hI.req_issue a t ha hm
    · intro a t t' ha h1 h2
      simp only [Set.mem_insert_iff, Prod.mk.injEq, reduceCtorEq, and_false, false_or] at h1 h2
      exact hI.echo_excl a t t' ha h1 h2
    · intro a s t hm; exact hS _ (hI.echo_signed a s t hm)
    · intro a s w t t' hm
      exact (hI.acc_rcv_signed a s w t t' hm).imp (hS _) (hS _)
    · intro a w' t t' ha hm
      rcases Set.mem_insert_iff.mp hm with he | hm
      · simp only [Prod.mk.injEq, Msg.acc.injEq] at he
        obtain ⟨rfl, rfl, rfl, rfl⟩ := he
        have := hI.acc_rcv_signed _ _ _ _ _ hr
        exact ⟨hv, hS _ this.1, hS _ this.2⟩
      · obtain ⟨h1, h2, h3⟩ := hI.acc_sent a w' t t' ha hm
        exact ⟨h1, hS _ h2, hS _ h3⟩
  | deliver q s m hm =>
    refine ⟨hI.sent_correct, hI.echo_sent, ?_, hI.req_issue, hI.echo_excl, ?_, ?_, hI.acc_sent,
      hI.wf, ?_⟩
    · intro a b m' hb hm'
      rcases Set.mem_insert_iff.mp hm' with he | hm'
      · simp only [Prod.mk.injEq] at he
        obtain ⟨rfl, rfl, rfl⟩ := he; exact hm
      · exact hI.genuine a b m' hb hm'
    · intro a s' t hm'
      rcases Set.mem_insert_iff.mp hm' with he | hm'
      · simp only [Prod.mk.injEq] at he
        obtain ⟨rfl, rfl, rfl⟩ := he
        exact hI.echo_sent _ _ hm
      · exact hI.echo_signed a s' t hm'
    · intro a s' w t t' hm'
      rcases Set.mem_insert_iff.mp hm' with he | hm'
      · simp only [Prod.mk.injEq] at he
        obtain ⟨rfl, rfl, rfl⟩ := he
        exact (hI.acc_sent _ _ _ _ (hI.sent_correct _ _ hm) hm).2
      · exact hI.acc_rcv_signed a s' w t t' hm'
    · intro a t ha ht hne
      obtain ⟨Q, hQ, hQe⟩ := hI.quorum a t ha ht hne
      exact ⟨Q, hQ, fun q hq => Set.mem_insert_of_mem _ (hQe q hq)⟩
  | inject q b m hb hms =>
    refine ⟨hI.sent_correct, hI.echo_sent, ?_, hI.req_issue, hI.echo_excl, ?_, ?_, hI.acc_sent,
      hI.wf, ?_⟩
    · intro a b' m' hb' hm'
      rcases Set.mem_insert_iff.mp hm' with he | hm'
      · simp only [Prod.mk.injEq] at he
        obtain ⟨rfl, rfl, rfl⟩ := he; exact absurd hb hb'
      · exact hI.genuine a b' m' hb' hm'
    · intro a s' t hm'
      rcases Set.mem_insert_iff.mp hm' with he | hm'
      · simp only [Prod.mk.injEq] at he
        obtain ⟨rfl, rfl, rfl⟩ := he; exact hms
      · exact hI.echo_signed a s' t hm'
    · intro a s' w t t' hm'
      rcases Set.mem_insert_iff.mp hm' with he | hm'
      · simp only [Prod.mk.injEq] at he
        obtain ⟨rfl, rfl, rfl⟩ := he; exact hms
      · exact hI.acc_rcv_signed a s' w t t' hm'
    · intro a t ha ht hne
      obtain ⟨Q, hQ, hQe⟩ := hI.quorum a t ha ht hne
      exact ⟨Q, hQ, fun q hq => Set.mem_insert_of_mem _ (hQe q hq)⟩

end Setup

end Podc.MultipleSpending
