import Papers.PODC2020.ConsecutiveBallotsPaxos.Model

/-!
# The TLA+ safety property of Appendix B is vacuous

Appendix B of [paper] defines (rendered from the PDF, page 18)

```
ConsecQ(Q, b, v) ≜ ∀ r ∈ Acceptor : ∧ NotIn(Q, r)
                                    ∧ ∃ m ∈ msgs : ∧ m.type = "2b"
                                                   ∧ m.acc = r
                                                   ⟹ ∨ (∀ q ∈ Q : ∃ n ∈ msgs : … ⟹ m.bal < n.bal)
                                                      ∨ (∀ q ∈ Q : ∃ n ∈ msgs : … ⟹ n.bal < m.bal)
AgreedConsecQ(v, b) ≜ ∃ Q ∈ Quorum : ∧ ∀ a ∈ Q : Sent2bNoBal(a, v)
                                     ∧ ∃ a ∈ Q : Sent2b(a, v, b)
                                     ∧ ConsecQ(Q, b, v)
SafeValue ≜ ∀ v ∈ Value : ∀ b ∈ Ballot : AgreedConsecQ(v, b) ⟹ NoFutureProposal(v, b)
```

`NotIn(Q, r)` is a top-level conjunct of the body of `∀ r ∈ Acceptor`, so `ConsecQ(Q, b, v)`
requires *every* acceptor to lie outside `Q`; it is false for every nonempty `Q`. Quorums are
nonempty (`QuorumAssumption`: any two quorums intersect), so `AgreedConsecQ` never holds and the
checked invariant `SafeValue` is true in every state, independently of the protocol. We transcribe
`ConsecQ` (the second conjunct is kept abstract — it plays no role) and prove this.
-/

namespace Podc.ConsecutiveBallotsPaxos

open Msg

variable {A V : Type*}

/-- `ConsecQ(Q, b, v)` of Appendix B, transcribed literally; the second conjunct (whatever its
exact parse) is an arbitrary predicate `P r`. -/
def TLAConsecQ (Q : Finset A) (P : A → Prop) : Prop :=
  ∀ r : A, r ∉ Q ∧ P r

/-- `AgreedConsecQ(v, b)` of Appendix B. -/
def TLAAgreedConsecQ (QS : QuorumSystem A) (M : Set (Msg A V)) (v : V) (b : ℕ)
    (P : Finset A → A → Prop) : Prop :=
  ∃ Q, QS.IsQuorum Q ∧ (∀ a ∈ Q, ∃ b', accept a b' v ∈ M) ∧ (∃ a ∈ Q, accept a b v ∈ M) ∧
    TLAConsecQ Q (P Q)

/-- The hypothesis of `SafeValue` in Appendix B is never satisfied: the TLA+ check of the combined
protocol proves nothing. -/
theorem tla_agreedConsecQ_false (QS : QuorumSystem A) (M : Set (Msg A V)) (v : V) (b : ℕ)
    (P : Finset A → A → Prop) : ¬ TLAAgreedConsecQ QS M v b P := by
  rintro ⟨Q, hQ, -, -, hc⟩
  obtain ⟨a, ha, -⟩ := QS.inter Q Q hQ hQ
  exact (hc a).1 ha

end Podc.ConsecutiveBallotsPaxos
