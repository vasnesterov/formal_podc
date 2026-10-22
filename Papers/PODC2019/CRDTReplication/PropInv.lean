import Papers.PODC2019.CRDTReplication.Steps

/-!
# Proposer invariants

`ProcInv` relates the proposer part of the local state of a process `p` to the history and to
the messages sent: the current operation, the `ACK`s and `VOTED`s recorded, and the ghost record
of learned states. In particular (`LearnedOK`):

* a state learned by consistent quorum in attempt `i` was received in `ACK`s for round `(·, i)`
  from (a superset of) a quorum;
* a state `s` learned by vote in attempt `i` with round `(n, i)` is above the states of `ACK`s for
  `(n, i)` from a quorum, and `VOTED(s)` for `(n, i)` was sent by a quorum.
-/

set_option linter.unusedSectionVars false

namespace Podc.CRDTReplication

open Cslib.SharedMemory Cslib.AsyncMP

variable {P : Type} [Fintype P] [DecidableEq P] {D : CRDT}
variable {V : Variant D} {QS : Finset (Finset P)}

/-- A quorum sent `ACK`s for round `(n, i)` with states below `s`. -/
def AckQ (QS : Finset (Finset P)) (sent : Multiset (P × P × Msg P D)) (n : ℕ) (i : Rid P)
    (s : D.S) : Prop :=
  ∃ A, HasQuorum QS A ∧ ∀ a ∈ A, ∃ σ, (a, i.1, Msg.ack n i σ) ∈ sent ∧ σ ≤ s

/-- A quorum sent `VOTED(s)` for round `(n, i)`. -/
def VotedQ (QS : Finset (Finset P)) (sent : Multiset (P × P × Msg P D)) (n : ℕ) (i : Rid P)
    (s : D.S) : Prop :=
  ∃ A, HasQuorum QS A ∧ ∀ a ∈ A, (a, i.1, Msg.voted n i s) ∈ sent

/-- A quorum sent `ACK`s with state exactly `s` for attempt `i`. -/
def ConsQ (QS : Finset (Finset P)) (sent : Multiset (P × P × Msg P D)) (i : Rid P) (s : D.S) :
    Prop :=
  ∃ A, HasQuorum QS A ∧ ∀ a ∈ A, ∃ n, (a, i.1, Msg.ack n i s) ∈ sent

/-- What a learned state `(s, v)` of the `k`-th operation of `p` certifies. -/
def LearnedOK (QS : Finset (Finset P)) (sent : Multiset (P × P × Msg P D))
    (h : List (Label P D.spec)) (p : P) (k : ℕ) (s : D.S) (v : Bool) : Prop :=
  (∃ q, opOf h (p, k) = some (CRDT.Cmd.qry q) ∧
    respOf h (p, k) = some (CRDT.Res.val (D.query q s))) ∧
  ∃ i : Rid P, i.1 = p ∧ i.2.1 = k ∧
    (v = true → ∃ n, AckQ QS sent n i s ∧ VotedQ QS sent n i s) ∧
    (v = false → ConsQ QS sent i s)

/-- The invariant of process `p` with local state `l`. -/
structure ProcInv (QS : Finset (Finset P)) (sent : Multiset (P × P × Msg P D))
    (h : List (Label P D.spec)) (p : P) (l : Loc P D) : Prop where
  nOps : l.nOps = (opsOf h p).length
  idle : l.phase = .idle → (respsOf h p).length = (opsOf h p).length
  busy : l.phase ≠ .idle → (respsOf h p).length + 1 = (opsOf h p).length
  ph_upd : ∀ k M, l.phase = .upd k M → k + 1 = (opsOf h p).length ∧
    ∃ u, opOf h (p, k) = some (CRDT.Cmd.upd u)
  ph_prep : ∀ q i acks, l.phase = .prep q i acks → i.1 = p ∧ i.2.1 + 1 = (opsOf h p).length ∧
    opOf h (p, i.2.1) = some (CRDT.Cmd.qry q) ∧
    ∀ a n σ, acks a = some (n, σ) → (a, p, Msg.ack n i σ) ∈ sent
  ph_vote : ∀ q i n s M, l.phase = .vote q i n s M → i.1 = p ∧
    i.2.1 + 1 = (opsOf h p).length ∧ opOf h (p, i.2.1) = some (CRDT.Cmd.qry q) ∧
    AckQ QS sent n i s ∧ ∀ a ∈ M, (a, p, Msg.voted n i s) ∈ sent
  learned : ∀ k s v, l.learned k = some (s, v) → Completed h (p, k) ∧ LearnedOK QS sent h p k s v
  learned_some : ∀ k q, opOf h (p, k) = some (CRDT.Cmd.qry q) → Completed h (p, k) →
    l.learned k ≠ none
  resp_upd : ∀ k u r, opOf h (p, k) = some (CRDT.Cmd.upd u) → respOf h (p, k) = some r →
    r = CRDT.Res.done
  prep_id : ∀ a i n σ, (p, a, Msg.prepare i n σ) ∈ sent → i.1 = p ∧ i.2.1 < (opsOf h p).length
  vote_id : ∀ a n i σ, (p, a, Msg.vote n i σ) ∈ sent → i.1 = p ∧ i.2.1 < (opsOf h p).length
  merge_id : ∀ a k σ, (p, a, Msg.merge k σ) ∈ sent → ∃ u, opOf h (p, k) = some (CRDT.Cmd.upd u)

/-! ## Monotonicity -/

lemma AckQ.mono {sent sent' : Multiset (P × P × Msg P D)} (hs : sent ≤ sent') {n i s}
    (h : AckQ QS sent n i s) : AckQ QS sent' n i s := by
  obtain ⟨A, hA, h⟩ := h
  exact ⟨A, hA, fun a ha => (h a ha).imp fun σ hσ => ⟨Multiset.mem_of_le hs hσ.1, hσ.2⟩⟩

lemma VotedQ.mono {sent sent' : Multiset (P × P × Msg P D)} (hs : sent ≤ sent') {n i s}
    (h : VotedQ QS sent n i s) : VotedQ QS sent' n i s := by
  obtain ⟨A, hA, h⟩ := h
  exact ⟨A, hA, fun a ha => Multiset.mem_of_le hs (h a ha)⟩

lemma ConsQ.mono {sent sent' : Multiset (P × P × Msg P D)} (hs : sent ≤ sent') {i s}
    (h : ConsQ QS sent i s) : ConsQ QS sent' i s := by
  obtain ⟨A, hA, h⟩ := h
  exact ⟨A, hA, fun a ha => (h a ha).imp fun n hn => Multiset.mem_of_le hs hn⟩

lemma LearnedOK.mono {sent sent' : Multiset (P × P × Msg P D)} (hs : sent ≤ sent')
    {h : List (Label P D.spec)} (β : List (Label P D.spec)) {p k s v}
    (hl : LearnedOK QS sent h p k s v) : LearnedOK QS sent' (h ++ β) p k s v := by
  obtain ⟨⟨q, h1, h2⟩, i, hi1, hi2, hv, hc⟩ := hl
  exact ⟨⟨q, opOf_append_of_eq_some h1 β, respOf_append_of_eq_some h2 β⟩, i, hi1, hi2,
    fun e => (hv e).imp fun n hn => ⟨hn.1.mono hs, hn.2.mono hs⟩, fun e => (hc e).mono hs⟩

/-- Labels of process `p`. -/
def OfProc (p : P) (β : List (Label P D.spec)) : Prop := ∀ x ∈ β, Label.proc x = p

lemma opsOf_append_ofProc {p q : P} {β : List (Label P D.spec)} (hβ : OfProc p β) (hq : q ≠ p)
    (h : List (Label P D.spec)) : opsOf (h ++ β) q = opsOf h q := by
  rw [opsOf_append, opsOf_eq_nil_of_proc_ne (α := β) (fun x hx => by rw [hβ x hx]; exact Ne.symm hq),
    List.append_nil]

lemma respsOf_append_ofProc {p q : P} {β : List (Label P D.spec)} (hβ : OfProc p β) (hq : q ≠ p)
    (h : List (Label P D.spec)) : respsOf (h ++ β) q = respsOf h q := by
  rw [respsOf_append, respsOf_eq_nil_of_proc_ne (α := β) (fun x hx => by rw [hβ x hx]; exact Ne.symm hq),
    List.append_nil]

/-- The invariant of a process `q` is preserved by steps of another process `p`. -/
lemma ProcInv.other {sent sent' : Multiset (P × P × Msg P D)} {h : List (Label P D.spec)}
    {β : List (Label P D.spec)} {p q : P} {l : Loc P D} (hI : ProcInv QS sent h q l)
    (hs : sent ≤ sent') (hnew : ∀ x ∈ sent', x ∈ sent ∨ x.1 = p) (hβ : OfProc p β)
    (hq : q ≠ p) : ProcInv QS sent' (h ++ β) q l := by
  have hops := opsOf_append_ofProc hβ hq h
  have hresps := respsOf_append_ofProc hβ hq h
  have hop : ∀ k, opOf (h ++ β) (q, k) = opOf h (q, k) := fun k => by simp [opOf, hops]
  have hresp : ∀ k, respOf (h ++ β) (q, k) = respOf h (q, k) := fun k => by simp [respOf, hresps]
  have hcomp : ∀ k, Completed (h ++ β) (q, k) ↔ Completed h (q, k) := fun k => by
    simp [Completed, hresps]
  have hold : ∀ x, x ∈ sent' → x.1 = q → x ∈ sent := fun x hx hxq =>
    (hnew x hx).resolve_right (fun e => hq (hxq ▸ e))
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hops]; exact hI.nOps
  · rw [hops, hresps]; exact hI.idle
  · rw [hops, hresps]; exact hI.busy
  · intro k M hk; rw [hops, hop]; exact hI.ph_upd k M hk
  · intro q' i acks hp; rw [hops, hop]
    obtain ⟨h1, h2, h3, h4⟩ := hI.ph_prep q' i acks hp
    exact ⟨h1, h2, h3, fun a n σ ha => Multiset.mem_of_le hs (h4 a n σ ha)⟩
  · intro q' i n s M hp; rw [hops, hop]
    obtain ⟨h1, h2, h3, h4, h5⟩ := hI.ph_vote q' i n s M hp
    exact ⟨h1, h2, h3, h4.mono hs, fun a ha => Multiset.mem_of_le hs (h5 a ha)⟩
  · intro k s v hk
    obtain ⟨h1, h2⟩ := hI.learned k s v hk
    exact ⟨h1.mono, h2.mono hs β⟩
  · intro k q' hk hc; rw [hop] at hk; rw [hcomp] at hc; exact hI.learned_some k q' hk hc
  · intro k u r hk hr; rw [hop] at hk; rw [hresp] at hr; exact hI.resp_upd k u r hk hr
  · intro a i n σ hm; rw [hops]; exact hI.prep_id a i n σ (hold _ hm rfl)
  · intro a n i σ hm; rw [hops]; exact hI.vote_id a n i σ (hold _ hm rfl)
  · intro a k σ hm; rw [hop]; exact hI.merge_id a k σ (hold _ hm rfl)

end Podc.CRDTReplication
