import Papers.PODC2019.CRDTReplication.CRDT
import Cslib.Computability.Distributed.MessagePassing.Async

/-!
# Algorithm 2: linearizable state machine replication of state-based CRDTs

The protocol of Section III-B as a CSLib asynchronous message-passing protocol
(`Cslib.AsyncMP.Protocol`): every process is both a proposer and an acceptor.

**Acceptor** (lines 27–49). Local variables: payload `s` and round `r = (rnr, rid)`, initially
`(s₀, (0, ⊥))`.
* `apply_update(u)` (called by the local proposer): `s ← u(s)`, `rid ← ⊥`.
* `MERGE(s')`: `s ← s ⊔ s'`, `rid ← ⊥`, reply `MERGED`.
* `PREPARE(r', s')`: `s ← s ⊔ s'`; an incremental prepare (`r'nr = ⊥`) gets the number
  `rnr + 1`; if `r'nr > rnr` then `r ← r'` and reply `ACK(r, s)`.
* `VOTE(r', s')`: `s ← s ⊔ s'`; if `r' = r` reply `VOTED(s')`.

**Proposer** (lines 1–26).
* Update `u`: apply it on the local acceptor, send `MERGE(s)` to the other acceptors, respond
  once `MERGED` has been received from a quorum (the local acceptor counts as merged).
* Query `q`: `PREPARE((⊥, id), s₀)` to all acceptors. Once `ACK`s from (a superset of) a quorum
  are received, with `s'` the LUB of the received states:
  (a) if all received states are equal to `s'`, `s'` is *learned by consistent quorum*;
  (b) else if all received rounds are equal to `r`, send `VOTE(r, s')` to all acceptors;
  `s'` is *learned by vote* once `VOTED(s')` is received from a quorum (line 24);
  (c) else retry with the fixed prepare `PREPARE((max R + 1, new_id), s')`.
  The query returns `cmd_q` applied to the learned state.
* Retries after a `NACK` (Section III-B, "Retrying Requests") are modelled by the internal action
  `retry n`: at any time, a pending query may abandon its current attempt and start a new one,
  incremental (`n = none`) or fixed (`n = some k`), carrying the LUB of the payloads received.

Message ids: the attempt id `(p, k, j)` (proposer, index of the operation of `p`, attempt
counter) plays the role of the round ID `rid` and of the request id of the paper; the round of an
attempt is `(n, id)`. `VOTED` messages carry the round they answer.

**Variants** (`Variant`): `cons` is the test of line 13 (`sᵢ ≡ s'`; equality in the paper's
intended reading, `Variant.paper`), and `fix` adds our repair: an acceptor answers `VOTED` only
if, in addition, its payload before the merge is `⊑ s'` (`Variant.fixed`).

**Ghost state.** `learned k = some (s, v)`: the `k`-th operation of the process was a query that
learned `s` (`v = true`: by vote). It is written exactly when the query returns.
-/

namespace Podc.CRDTReplication

open Cslib.SharedMemory Cslib.AsyncMP

variable (P : Type) (D : CRDT)

/-- Attempt (request / round) identifiers `(proposer, operation index, attempt counter)`. -/
abbrev Rid := P × ℕ × ℕ

/-- Messages of Algorithm 2. -/
inductive Msg where
  /-- `MERGE(s)` for the `k`-th operation of the sender. -/
  | merge (k : ℕ) (s : D.S)
  /-- `MERGED` for the `k`-th operation of the receiver. -/
  | merged (k : ℕ)
  /-- `PREPARE((n, i), s)`; `n = none` is an incremental prepare. -/
  | prepare (i : Rid P) (n : Option ℕ) (s : D.S)
  /-- `ACK((n, i), s)`. -/
  | ack (n : ℕ) (i : Rid P) (s : D.S)
  /-- `VOTE((n, i), s)`. -/
  | vote (n : ℕ) (i : Rid P) (s : D.S)
  /-- `VOTED(s)` answering `VOTE((n, i), s)`. -/
  | voted (n : ℕ) (i : Rid P) (s : D.S)
  deriving DecidableEq

/-- The control state of the proposer. -/
inductive Phase where
  /-- No pending operation. -/
  | idle
  /-- Pending update (the `k`-th operation), acceptors known to have merged. -/
  | upd (k : ℕ) (merged : Finset P)
  /-- Pending query `q`, attempt `i`, waiting for `ACK`s (received: round number and state). -/
  | prep (q : D.Q) (i : Rid P) (acks : P → Option (ℕ × D.S))
  /-- Pending query `q`, attempt `i`, proposed `VOTE((n, i), s)`, acceptors that voted. -/
  | vote (q : D.Q) (i : Rid P) (n : ℕ) (s : D.S) (voted : Finset P)

/-- Local state of a process (acceptor part, proposer part, ghost). -/
structure Loc where
  /-- Acceptor payload `s`. -/
  s : D.S
  /-- Acceptor round number `rnr`. -/
  rnr : ℕ
  /-- Acceptor round id `rid` (`none` = `⊥`). -/
  rid : Option (Rid P)
  /-- Number of operations invoked so far at this process. -/
  nOps : ℕ
  /-- Attempt counter (for `new_id()`). -/
  nAtt : ℕ
  /-- Proposer control state. -/
  phase : Phase P D
  /-- Ghost: state learned by the `k`-th operation (if a query that returned), and whether it
  was learned by vote. -/
  learned : ℕ → Option (D.S × Bool)

/-- Internal actions of the proposer. -/
inductive Act where
  /-- Act on the messages received so far (the "on receive … from a quorum" handlers). -/
  | advance
  /-- Abandon the current query attempt and retry (incremental if `none`). -/
  | retry (n : Option ℕ)

/-- Variants of the protocol: `cons s' sᵢ` is the test `sᵢ ≡ s'` of line 13; `fix` enables the
repaired `VOTE` handler. -/
structure Variant where
  /-- The consistency test of line 13. -/
  cons : D.S → D.S → Bool
  /-- Whether acceptors vote only if their payload is below the proposal. -/
  fix : Bool

namespace Variant

variable {D}

/-- Algorithm 2 as written (with `≡` read as equality of payloads). -/
def paper : Variant D := ⟨fun s t => decide (s = t), false⟩

/-- Algorithm 2 with the repaired `VOTE` handler. -/
def fixed : Variant D := ⟨fun s t => decide (s = t), true⟩

end Variant

variable {P D}
variable [Fintype P] [DecidableEq P]

/-- The acceptors from which an `ACK` was received. -/
def ackers (acks : P → Option (ℕ × D.S)) : Finset P :=
  Finset.univ.filter fun a => (acks a).isSome

/-- The state received from `a` (`s₀` if none). -/
def ackState (acks : P → Option (ℕ × D.S)) (a : P) : D.S :=
  ((acks a).map Prod.snd).getD D.s₀

/-- The round number received from `a` (`0` if none). -/
def ackNr (acks : P → Option (ℕ × D.S)) (a : P) : ℕ :=
  ((acks a).map Prod.fst).getD 0

/-- The LUB of the received states (line 12). -/
def lub (acks : P → Option (ℕ × D.S)) : D.S :=
  Finset.univ.fold (· ⊔ ·) D.s₀ (ackState acks)

/-- The largest received round number. -/
def maxNr (acks : P → Option (ℕ × D.S)) : ℕ :=
  Finset.univ.sup (ackNr acks)

/-- `A` contains a quorum. -/
def HasQuorum (QS : Finset (Finset P)) (A : Finset P) : Prop := ∃ Q ∈ QS, Q ⊆ A

instance (QS : Finset (Finset P)) (A : Finset P) : Decidable (HasQuorum QS A) := by
  unfold HasQuorum; infer_instance

/-- Send `m` to all processes. -/
def toAll (m : Msg P D) : Multiset (P × Msg P D) := Finset.univ.val.map fun a => (a, m)

/-- Send `m` to all processes but `p`. -/
def toOthers (p : P) (m : Msg P D) : Multiset (P × Msg P D) :=
  (Finset.univ.filter (· ≠ p)).val.map fun a => (a, m)

/-- Start a new attempt of query `q` (the current operation of `p`) with `PREPARE((n, id), s)`. -/
def startAttempt (p : P) (l : Loc P D) (q : D.Q) (n : Option ℕ) (s : D.S) :
    Loc P D × Multiset (P × Msg P D) :=
  let i : Rid P := (p, l.nOps - 1, l.nAtt)
  ({ l with nAtt := l.nAtt + 1, phase := .prep q i fun _ => none }, toAll (.prepare i n s))

/-- Invocation of an operation (lines 1–4 and 7–10). -/
def invokeStep (p : P) (o : D.spec.Op) (l : Loc P D) : Option (Loc P D × Multiset (P × Msg P D)) :=
  match l.phase with
  | .idle => some <| match o with
    | .upd u =>
      ({ l with s := D.app u l.s, rid := none, nOps := l.nOps + 1,
                phase := .upd l.nOps {p} }, toOthers p (.merge l.nOps (D.app u l.s)))
    | .qry q => startAttempt p { l with nOps := l.nOps + 1 } q none D.s₀
  | _ => none

/-- Reception of a message by `p` from `src` (acceptor handlers, lines 34–49; proposers record
the replies). -/
def receiveStep (V : Variant D) (_p src : P) (m : Msg P D) (l : Loc P D) :
    Loc P D × Multiset (P × Msg P D) :=
  match m with
  | .merge k s' => ({ l with s := l.s ⊔ s', rid := none }, {(src, .merged k)})
  | .prepare i n s' =>
    if l.rnr < n.getD (l.rnr + 1) then
      ({ l with s := l.s ⊔ s', rnr := n.getD (l.rnr + 1), rid := some i },
        {(src, .ack (n.getD (l.rnr + 1)) i (l.s ⊔ s'))})
    else ({ l with s := l.s ⊔ s' }, 0)
  | .vote n i s' =>
    if l.rnr = n ∧ l.rid = some i ∧ (V.fix = true → l.s ≤ s') then
      ({ l with s := l.s ⊔ s' }, {(src, .voted n i s')})
    else ({ l with s := l.s ⊔ s' }, 0)
  | .merged k =>
    (match l.phase with
      | .upd k' M => if k = k' then { l with phase := .upd k' (insert src M) } else l
      | _ => l, 0)
  | .ack n i s' =>
    (match l.phase with
      | .prep q i' acks =>
        if i = i' then { l with phase := .prep q i' (Function.update acks src (some (n, s'))) }
        else l
      | _ => l, 0)
  | .voted n i s =>
    (match l.phase with
      | .vote q i' n' s' M =>
        if i = i' ∧ n = n' ∧ s = s' then { l with phase := .vote q i' n' s' (insert src M) } else l
      | _ => l, 0)

/-- Internal actions of the proposer (lines 5–6, 11–26, and retries). -/
def internalStep (V : Variant D) (QS : Finset (Finset P)) (p : P) (a : Act) (l : Loc P D) :
    Option (Loc P D × Multiset (P × Msg P D) × Option (CRDT.Res D)) :=
  match a, l.phase with
  | .advance, .upd _ M =>
    if HasQuorum QS M then some ({ l with phase := .idle }, 0, some .done) else none
  | .advance, .prep q i acks =>
    if HasQuorum QS (ackers acks) then
      if ∀ a ∈ ackers acks, V.cons (lub acks) (ackState acks a) = true then
        some ({ l with phase := .idle,
                       learned := Function.update l.learned i.2.1 (some (lub acks, false)) },
          0, some (.val (D.query q (lub acks))))
      else if ∀ a ∈ ackers acks, ackNr acks a = maxNr acks then
        some ({ l with phase := .vote q i (maxNr acks) (lub acks) ∅ },
          toAll (.vote (maxNr acks) i (lub acks)), none)
      else
        let x := startAttempt p l q (some (maxNr acks + 1)) (lub acks)
        some (x.1, x.2, none)
    else none
  | .advance, .vote q i _ s' M =>
    if HasQuorum QS M then
      some ({ l with phase := .idle, learned := Function.update l.learned i.2.1 (some (s', true)) },
        0, some (.val (D.query q s')))
    else none
  | .retry n, .prep q _ acks =>
    let x := startAttempt p l q n (lub acks)
    some (x.1, x.2, none)
  | .retry n, .vote q _ _ s' _ =>
    let x := startAttempt p l q n s'
    some (x.1, x.2, none)
  | _, _ => none

/-- The initial local state. -/
def initLoc : Loc P D := ⟨D.s₀, 0, none, 0, 0, .idle, fun _ => none⟩

/-- **Algorithm 2** (variant `V`, quorum system `QS`) as a CSLib asynchronous message-passing
implementation of the CRDT object `D.spec`. -/
def alg (V : Variant D) (QS : Finset (Finset P)) :
    Protocol P D.spec (Loc P D) (Msg P D) Act where
  init _ := initLoc
  invoke p o l := invokeStep p o l
  internal p a l := internalStep V QS p a l
  receive p src m l := some ((receiveStep V p src m l).1, (receiveStep V p src m l).2, none)

/-- A quorum system: any two quorums intersect. -/
def IsQuorumSystem (QS : Finset (Finset P)) : Prop :=
  ∀ Q₁ ∈ QS, ∀ Q₂ ∈ QS, (Q₁ ∩ Q₂).Nonempty

/-- The state learned by the operation `x` in configuration `C` (if `x` is a query that has
returned). -/
def learnedOf (C : Config P (Loc P D) (Msg P D)) (x : OpId P) : Option D.S :=
  ((C.loc x.1).learned x.2).map Prod.fst

/-- `s` is a learned state in `C` (learned by vote if `v = true`, by consistent quorum
otherwise). -/
def LearnedBy (C : Config P (Loc P D) (Msg P D)) (s : D.S) (v : Bool) : Prop :=
  ∃ x : OpId P, (C.loc x.1).learned x.2 = some (s, v)

/-- `s` is a learned state in `C`. -/
def Learned (C : Config P (Loc P D) (Msg P D)) (s : D.S) : Prop := ∃ x, learnedOf C x = some s

end Podc.CRDTReplication
