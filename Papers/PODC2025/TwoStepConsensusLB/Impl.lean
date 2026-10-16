import Papers.PODC2025.TwoStepConsensusLB.Model

/-!
# The protocol of Figure 1 as a `Protocol` of the model (upper bounds, §3 and §C)

This file defines the consensus protocol of Figure 1 of Ryabinin–Gotsman–Sutra (PODC 2025) as a
concrete `Protocol P V (Msg P V) (St P V)` of the partially synchronous model of `Model.lean`.
It is parameterized by a configuration `c : Cfg P`: the parameters `e` and `f`, a flag `obj`
(`false`: consensus *task*, red lines of Figure 1 ignored; `true`: consensus *object*, red lines
included) and a ballot-owner function `owner : ℕ → P`.

## Implementation choices (all documented as differences from the paper)

* **Values.** `V` is linearly ordered; the paper's `⊥` (smaller than every value) is `none`.
* **Leader election.** Instead of the `Ω` service of §C.1 we use clock-driven rotating ballots
  (processes know the time): ballot `b ≥ 1` starts at time `ballotStart b = 5b - 3`
  (the first timeout at `2Δ`, then every `5Δ`, as in §C.1), and at that time its owner
  `owner b` sends `1A(b)` to all processes (if `b > bal`). With `owner` hitting every process
  infinitely often (e.g. `rrOwner`, round robin), every correct process eventually leads a
  ballot after GST.
* **Atomic handlers.** A step at time `τ` processes the invocation (if any), then the delivered
  messages in the adversary's order, each by one atomic handler (`handle`), then the timer
  (`timer`). Every message handler is followed by `tryDecide`, the guarded handler of line 9
  ("when received `2B(bal, v)` from all `q ∈ P`"), which fires as soon as its precondition
  (line 10) holds and the process has not decided yet. The received `2B` and `1B` messages are
  kept in the state.
* **The `1B` handler** (line 24) stores at most one `1B(b)` per sender and ballot and fires,
  exactly once per ballot `b`, when the number of distinct senders of `1B(b)` reaches `n - f`;
  `Q` is then exactly these `n - f` messages.
* **Object version fix.** As written, the object protocol of the paper is not wait-free: a value
  known only to a process that voted (line 7) before invoking `propose` (so that line 3 is
  skipped) may never be proposed by any leader. In the object version, the fallback at lines
  37–38 is "else if `initial_val ≠ ⊥` then `initial_val`, **else the process's own `val`**".
  This is safe: line 37 is reached only if `b_max = 0`, no `1B` reports a decision and no value
  can have been decided on the fast path (Lemma 5), so any value that was proposed is safe.
* Lines 33 and 35: among the candidate values, the maximal one is chosen (the paper chooses
  "the" value at line 33, which is unique when it matters).
-/

set_option linter.unusedSectionVars false

namespace TwoStepConsensus.Impl

/-- Contents of a `1B` message besides its ballot: `(vbal, val, proposer, decided)`. -/
structure OneB (P V : Type*) where
  /-- The last ballot in which the sender voted. -/
  vbal : ℕ
  /-- The sender's current vote (`none` = `⊥`). -/
  val : Option V
  /-- The process whose `Propose` the sender accepted (fast ballot). -/
  prop : Option P
  /-- The sender's decision, if any. -/
  dec : Option V

/-- Messages of Figure 1. -/
inductive Msg (P V : Type*)
  /-- `Propose(v)` (line 4). -/
  | propose (v : V)
  /-- `2B(b, v)` (lines 8, 43). -/
  | twoB (b : ℕ) (v : V)
  /-- `Decide(v)` (line 13). The ballot `b` is ghost data (the sender's ballot when deciding),
  never read by the receiver. -/
  | decide (b : ℕ) (v : V)
  /-- `1A(b)` (line 23). -/
  | oneA (b : ℕ)
  /-- `1B(b, vbal, val, proposer, decided)` (line 20). -/
  | oneB (b : ℕ) (d : OneB P V)
  /-- `2A(b, v)` (line 39). -/
  | twoA (b : ℕ) (v : V)

/-- Destination of a message in the outbox. -/
inductive Dest (P : Type*)
  /-- All processes (`Π`). -/
  | all
  /-- All processes but the sender (`Π \ {p_i}`). -/
  | others
  /-- A single process. -/
  | to (q : P)

/-- Whether destination `d` of a message sent by `p` includes `q`. -/
def Dest.incl {P : Type*} [DecidableEq P] (p : P) : Dest P → P → Bool
  | .all, _ => true
  | .others, q => decide (q ≠ p)
  | .to r, q => decide (q = r)

/-- Local state of a process. -/
structure St (P V : Type*) where
  /-- `initial_val` (`none` = `⊥`). -/
  initVal : Option V := none
  /-- `val`: the current vote (`none` = `⊥`). -/
  val : Option V := none
  /-- `proposer`: whose `Propose` was accepted. -/
  proposer : Option P := none
  /-- `bal`: the current ballot. -/
  bal : ℕ := 0
  /-- `vbal`: the last ballot in which the process voted. -/
  vbal : ℕ := 0
  /-- `decided`. -/
  decided : Option V := none
  /-- Received `2B(b, v)` messages: `(sender, b, v)`. -/
  twoBs : List (P × ℕ × V) := []
  /-- Received `1B` messages (at most one per sender and ballot): `(sender, b, contents)`. -/
  oneBs : List (P × ℕ × OneB P V) := []
  /-- Messages sent in the last step. -/
  out : List (Dest P × Msg P V) := []

/-- Parameters of the protocol. -/
structure Cfg (P : Type*) where
  /-- Number of crashes tolerated on the fast path. -/
  e : ℕ
  /-- Number of crashes tolerated. -/
  f : ℕ
  /-- `false`: consensus task; `true`: consensus object (red lines of Figure 1). -/
  obj : Bool
  /-- Owner of each ballot (the process that may start it). -/
  owner : ℕ → P

variable {P V : Type*} [Fintype P] [DecidableEq P] [LinearOrder V]

/-- Start time of ballot `b ≥ 1`: first timeout at `2Δ`, then every `5Δ` (§C.1). -/
def ballotStart (b : ℕ) : ℕ := 5 * b - 3

/-- Number of `1B` votes for `v` in `R`. -/
def votes (R : List (P × OneB P V)) (v : V) : ℕ := (R.filter fun x => x.2.val = some v).length

/-- Lines 26–38: the value proposed by the leader of a slow ballot, given the quorum `Q` of `1B`
messages (with their senders) and the fallback value `fb` of lines 37–38. -/
def proposal (n f e : ℕ) (Q : List (P × OneB P V)) (fb : Option V) : Option V :=
  match Q.findSome? (fun x => x.2.dec) with
  | some d => some d
  | none =>
    let bmax := (Q.map fun x => x.2.vbal).foldr max 0
    if 0 < bmax then (Q.find? fun x => x.2.vbal = bmax).bind fun x => x.2.val
    else
      let R := Q.filter fun x => x.2.prop.all fun r => r ∉ Q.map Prod.fst
      let cands := R.filterMap fun x => x.2.val
      match (cands.filter fun v => n - f - e < votes R v).max? with
      | some v => some v
      | none =>
        match (cands.filter fun v => votes R v = n - f - e).max? with
        | some v => some v
        | none => fb

section Handlers

variable (c : Cfg P) (p : P)

/-- The fallback of lines 37–38: `initial_val` (task); `initial_val`, else the own vote `val`
(object version, our fix). -/
def fallback (s : St P V) : Option V :=
  if c.obj then s.initVal.or s.val else s.initVal

/-- Lines 1–4: invocation of `propose(v)` (for the task: startup with input `v`). -/
def onInv (v : V) (s : St P V) : St P V :=
  if s.val = none then { s with initVal := some v, out := s.out ++ [(.others, .propose v)] }
  else s

/-- The value-related part of the precondition of line 6:
`v ≥ initial_val ∧ (initial_val ≠ ⊥ ⟹ v = initial_val)` (second conjunct: object only). -/
def okProp (obj : Bool) (iv : Option V) (v : V) : Bool :=
  match iv with
  | none => true
  | some w => decide (w ≤ v) && (!obj || decide (v = w))

/-- Lines 5–8: `Propose(v)` from `q`. -/
def onPropose (q : P) (v : V) (s : St P V) : St P V :=
  if s.bal = 0 ∧ s.val = none ∧ okProp c.obj s.initVal v = true then
    { s with val := some v, proposer := some q, out := s.out ++ [(.to q, .twoB 0 v)] }
  else s

/-- Reception of `2B(b, v)` from `q`: it is stored (the decision is taken by `tryDecide`). -/
def onTwoB (q : P) (b : ℕ) (v : V) (s : St P V) : St P V :=
  { s with twoBs := s.twoBs ++ [(q, b, v)] }

/-- Lines 14–16: `Decide(v)`. -/
def onDecide (v : V) (s : St P V) : St P V := { s with val := some v, decided := some v }

/-- Lines 17–20: `1A(b)` from `q`. -/
def onOneA (q : P) (b : ℕ) (s : St P V) : St P V :=
  if s.bal < b then
    { s with bal := b, out := s.out ++ [(.to q, .oneB b ⟨s.vbal, s.val, s.proposer, s.decided⟩)] }
  else s

/-- Senders of the stored `1B(b)` messages. -/
def senders1B (s : St P V) (b : ℕ) : Finset P :=
  ((s.oneBs.filter fun x => x.2.1 = b).map Prod.fst).toFinset

/-- The stored `1B(b)` messages. -/
def quorum1B (s : St P V) (b : ℕ) : List (P × OneB P V) :=
  (s.oneBs.filter fun x => x.2.1 = b).map fun x => (x.1, x.2.2)

/-- Lines 26–39 for ballot `b`: compute the proposal and send `2A(b, val)` if `val ≠ ⊥`. -/
def lead (b : ℕ) (s : St P V) : St P V :=
  match proposal (Fintype.card P) c.f c.e (quorum1B s b) (fallback c s) with
  | some w => { s with out := s.out ++ [(.all, .twoA b w)] }
  | none => s

/-- Line 24: `1B(b, d)` from `q`. Stored if it is the first `1B(b)` from `q`; when the number of
senders of `1B(b)` reaches `n - f`, the leader computes its proposal (`lead`). -/
def onOneB (q : P) (b : ℕ) (d : OneB P V) (s : St P V) : St P V :=
  if q ∈ senders1B s b then s
  else if (senders1B s b).card + 1 = Fintype.card P - c.f then
    lead c b { s with oneBs := s.oneBs ++ [(q, b, d)] }
  else { s with oneBs := s.oneBs ++ [(q, b, d)] }

/-- Lines 40–43: `2A(b, v)` from `q`. -/
def onTwoA (q : P) (b : ℕ) (v : V) (s : St P V) : St P V :=
  if s.bal ≤ b then
    { s with val := some v, bal := b, vbal := b, out := s.out ++ [(.to q, .twoB b v)] }
  else s

/-- Senders of the stored `2B(b, v)` messages. -/
def senders2B (s : St P V) (b : ℕ) (v : V) : Finset P :=
  ((s.twoBs.filter fun x => x.2 = (b, v)).map Prod.fst).toFinset

/-- Line 10, for the current ballot `bal = b`:
`(b = 0 ∧ |P ∪ {p}| ≥ n - e ∧ val ∈ {⊥, v}) ∨ (b ≠ 0 ∧ |P| ≥ n - f)`. -/
def canDecide (s : St P V) (b : ℕ) (v : V) : Bool :=
  if b = 0 then
    decide (Fintype.card P - c.e ≤ (insert p (senders2B s 0 v)).card ∧
      (s.val = none ∨ s.val = some v))
  else decide (Fintype.card P - c.f ≤ (senders2B s b v).card)

/-- Lines 11–13: decide `v`. -/
def decideV (v : V) (s : St P V) : St P V :=
  { s with val := some v, decided := some v, out := s.out ++ [(.others, .decide s.bal v)] }

/-- Lines 9–13: if the process has not decided and has received `2B(bal, v)` from a set `P`
satisfying line 10, it decides `v`. -/
def tryDecide (s : St P V) : St P V :=
  if s.decided = none then
    match s.twoBs.find? (fun x => x.2.1 = s.bal && canDecide c p s s.bal x.2.2) with
    | some x => decideV x.2.2 s
    | none => s
  else s

/-- One message handler (without the decision check). -/
def handleRaw (s : St P V) : P × Msg P V → St P V
  | (q, .propose v) => onPropose c q v s
  | (q, .twoB b v) => onTwoB q b v s
  | (_, .decide _ v) => onDecide v s
  | (q, .oneA b) => onOneA q b s
  | (q, .oneB b d) => onOneB c q b d s
  | (q, .twoA b v) => onTwoA q b v s

/-- Processing of one delivered message: its handler, then the guarded handler of line 9. -/
def handle (s : St P V) (qm : P × Msg P V) : St P V := tryDecide c p (handleRaw c s qm)

/-- The invocation (if any). -/
def invoke (inv : Option V) (s : St P V) : St P V :=
  match inv with
  | some v => onInv v s
  | none => s

/-- Lines 21–23 with rotating leaders: at time `τ = ballotStart b` (`b ≥ 1`) the owner of
ballot `b` sends `1A(b)` to all, if `b > bal`. -/
def timer (τ : ℕ) (s : St P V) : St P V :=
  if 1 ≤ (τ + 3) / 5 ∧ ballotStart ((τ + 3) / 5) = τ ∧ c.owner ((τ + 3) / 5) = p ∧
      s.bal < (τ + 3) / 5 then
    { s with out := s.out ++ [(.all, .oneA ((τ + 3) / 5))] }
  else s

/-- A step at time `τ`: clear the outbox, process the invocation, the delivered messages (in the
given order), and the timer. -/
def stepFn (τ : ℕ) (s : St P V) (inv : Option V) (inbox : List (P × Msg P V)) : St P V :=
  timer c p τ (inbox.foldl (handle c p) (invoke inv { s with out := [] }))

end Handlers

/-- The protocol of Figure 1 (task version if `c.obj = false`, object version otherwise). -/
def fig1 (c : Cfg P) : Protocol P V (Msg P V) (St P V) where
  init _ := {}
  step p τ s inv inbox := stepFn c p τ s inv inbox
  send p s q := (s.out.filter fun dm => dm.1.incl p q).map Prod.snd
  decide _ s := s.decided

/-- Round-robin ballot owners: ballot `b` is owned by the process with index `b mod n`. -/
noncomputable def rrOwner [Nonempty P] (b : ℕ) : P :=
  (Fintype.equivFin P).symm ⟨b % Fintype.card P, Nat.mod_lt _ Fintype.card_pos⟩

/-- Every process owns ballots that start arbitrarily late. -/
theorem rrOwner_surj [Nonempty P] (p : P) (k : ℕ) : ∃ b, k ≤ b ∧ rrOwner b = p := by
  refine ⟨Fintype.card P * k + (Fintype.equivFin P p).1, ?_, ?_⟩
  · have := Fintype.card_pos (α := P)
    nlinarith
  · simp [rrOwner, Nat.mod_eq_of_lt (Fintype.equivFin P p).2]

end TwoStepConsensus.Impl
