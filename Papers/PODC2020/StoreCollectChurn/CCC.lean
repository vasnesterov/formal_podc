import Papers.PODC2020.StoreCollectChurn.Spec

/-!
# The CCC store-collect algorithm (Algorithms 2–3) in a static system

This file models the *Continuous Churn Collect* (CCC) algorithm of Section 4 of
[Attiya, Kumari, Somani, Welch, *Store-Collect in the Presence of Continuous Churn with Application
to Snapshots and Lattice Agreement*, PODC 2020, arXiv 2003.07787v3] for **static executions**:
all `n` nodes (`Fin n`) are initially in the system (`S₀ = Fin n`), and no `ENTER`, `LEAVE` or
`CRASH` event ever occurs. This is a special case of the model of Section 3, enough to refute the
paper's regularity claim (see `CCCCounterexample.lean`).

## Why Algorithm 1 can be omitted

Every handler of Algorithm 1 is triggered either by an `ENTER`/`LEAVE` event or by the receipt of an
`enter`, `enter-echo`, `join`, `join-echo`, `leave` or `leave-echo` message, and these messages are
only broadcast by handlers of Algorithm 1. In a static execution none of them ever fires, so
`Changes` keeps its initial value `{enter(q) | q ∈ S₀} ∪ {join(q) | q ∈ S₀}`, the derived variables are
constant, `Present = Members = S₀`, and `|Members| = n` (`numMembers`).

## Model

* Times are natural numbers; the maximal message delay `D` is a parameter.
* Each event (an invocation `COLLECT_p` / `STORE_p(v)` or the receipt by `p` of the broadcast
  number `k`) is processed atomically by the corresponding handler (Lines 26–54), which may
  broadcast messages (the store handler of Algorithm 3 broadcasts two messages in one step) and may
  produce a response (`ACK_p` / `RETURN_p(V)`).
* Broadcast is reliable and FIFO, every node (including the sender) receives every broadcast, with a
  delay in `(0, D]` (Section 3); see `Admissible`.

## Two charitable repairs of the pseudocode (deviations from the paper)

1. **`is_joined` of the initial members.** Algorithm 1 initializes `is_joined` to `false` for every
   node, and only Line 12 sets it to `true`; read literally, a node of `S₀` would never answer
   collect queries (Line 52) nor acknowledge stores (Line 49), and no operation could ever
   terminate in a static system. Since the nodes of `S₀` are joined from time `0` (Section 3), we
   initialize `is_joined = true` for them.
2. **Messages of a finished phase are ignored.** The client handlers (Lines 30, 43) only test
   `t = tag ∧ q = p`. Since a collect operation uses the same `tag` for its collect phase and its
   store-back, read literally a late `collect-reply` received during the store-back would increment
   the store-ack counter, and late `store-ack`s received after the response would "return" again.
   We let a client act on a `collect-reply` only during the collect phase of a pending collect, and
   on a `store-ack` only during a store phase (store operation or store-back) of a pending
   operation.

Both repairs only make the algorithm better behaved; the counterexample refutes the repaired
algorithm, hence the paper under any reading of the pseudocode.

The local variable `optype` of Algorithm 2 is subsumed by `NodeState.phase`
(`optype = collect` iff the phase is `collect` or `storeBack`).
-/

namespace Podc.StoreCollectChurn.CCC

variable {n : ℕ}

/-! ## Views (Section 4, Definition 1) -/

/-- A view of CCC: a set of triples `⟨q, v, sqno⟩` (node id, value, sequence number) without
repetition of node ids, represented as a list. Values are natural numbers. -/
abbrev View (n : ℕ) := List (Fin n × ℕ × ℕ)

/-- The `(value, sqno)` pair of node `q` in the view `V`, if any. -/
def View.lookup (V : View n) (q : Fin n) : Option (ℕ × ℕ) :=
  match V.find? (fun x => x.1 == q) with
  | some x => some x.2
  | none => none

/-- `V(q)`: the value of `q` in `V`, or `⊥ = none`. This is the client-value view of Section 2 used
by the specification (`Podc.StoreCollectChurn.Regular`). -/
def View.val (V : View n) (q : Fin n) : Option ℕ := (V.lookup q).map Prod.fst

/-- **Definition 1.** `merge(V₁, V₂)`: the triples of node ids occurring in only one of the views,
and, for node ids occurring in both, the triple with the larger sequence number (on a tie, which
never happens for different values in CCC, the triple of `V₁`). -/
def merge (V₁ V₂ : View n) : View n :=
  V₁.map (fun x => match V₂.lookup x.1 with
    | some y => if x.2.2 < y.2 then (x.1, y) else x
    | none => x) ++
  V₂.filter (fun y => (V₁.lookup y.1).isNone)

/-! ## Messages and local states -/

/-- The messages of Algorithms 2–3 (the messages of Algorithm 1 are never sent in a static
execution). -/
inductive Msg (n : ℕ) where
  /-- `⟨collect-query, tag, p⟩` (Line 29). -/
  | collectQuery (tag : ℕ) (p : Fin n)
  /-- `⟨collect-reply, LView, tag, q⟩`: answer to the query of client `q` (Line 53). -/
  | collectReply (rv : View n) (tag : ℕ) (q : Fin n)
  /-- `⟨store, LView, tag, p⟩` (Lines 36, 42). -/
  | store (rv : View n) (tag : ℕ) (p : Fin n)
  /-- `⟨store-ack, tag, q⟩`: acknowledgement to client `q` (Line 50). -/
  | storeAck (tag : ℕ) (q : Fin n)
  /-- `⟨store-echo, LView⟩` (Line 51). -/
  | storeEcho (rv : View n)
  deriving DecidableEq

/-- The phase of the client thread of a node (Section 4: "We define a phase to be ..."). -/
inductive Phase where
  /-- No pending operation (`optype = ⊥`). -/
  | idle
  /-- Collect phase of a collect operation (Lines 26–33). -/
  | collect
  /-- Store-back phase of a collect operation (Lines 34–36, 43–47). -/
  | storeBack
  /-- Store phase of a store operation (Lines 37–46). -/
  | store
  deriving DecidableEq

/-- Local state of a node: the variables of Algorithms 1–2 that are not constant in a static
execution, plus the start time of the current phase (bookkeeping). -/
structure NodeState (n : ℕ) where
  /-- `LView` (Algorithm 1). -/
  lview : View n
  /-- `is_joined` (Algorithm 1). -/
  isJoined : Bool
  /-- The current phase (replaces `optype`, see repair 2). -/
  phase : Phase
  /-- `tag` (Algorithm 2). -/
  tag : ℕ
  /-- `threshold` (Algorithm 2), a rational number `β · |Members|`. -/
  threshold : ℚ
  /-- `counter` (Algorithm 2). -/
  counter : ℕ
  /-- `sqno` (Algorithm 2). -/
  sqno : ℕ
  /-- Start time of the current phase (bookkeeping, not used by the algorithm). -/
  phaseStart : ℕ
  deriving DecidableEq

/-- Initial state of a node of `S₀` (with repair 1: `is_joined = true`). -/
def NodeState.init : NodeState n :=
  { lview := [], isJoined := true, phase := .idle, tag := 0, threshold := 0, counter := 0,
    sqno := 0, phaseStart := 0 }

/-- `|Members|`: constantly `|S₀| = n` in a static execution (see the module docstring). -/
def numMembers (n : ℕ) : ℕ := n

/-- Kinds of completed phases. -/
inductive PhaseKind where
  /-- A collect phase. -/
  | collect
  /-- A store phase (a store-back or a store operation). -/
  | store
  deriving DecidableEq

/-- A completed phase of node `node`, which started at time `start` and finished at time
`finish`. -/
structure PhaseRec (n : ℕ) where
  node : Fin n
  kind : PhaseKind
  start : ℕ
  finish : ℕ
  deriving DecidableEq

/-- Events of the store-collect schedule (Section 2), with views of CCC in responses. -/
inductive SchedEv (n : ℕ) where
  | stInv (p : Fin n) (v : ℕ)
  | ack (p : Fin n)
  | colInv (p : Fin n)
  | ret (p : Fin n) (V : View n)
  deriving DecidableEq

/-- Conversion to the events of the specification (`Spec.lean`): a returned view is turned into the
client-value view `V(·)`. -/
def SchedEv.toSC : SchedEv n → SCEv (Fin n) ℕ
  | .stInv p v => .stInv p v
  | .ack p => .ack p
  | .colInv p => .colInv p
  | .ret p V => .ret p V.val

/-- The effect of one atomic step of a node: new state, broadcast messages (in order), response,
and completed phases. -/
structure Out (n : ℕ) where
  st : NodeState n
  bcasts : List (Msg n) := []
  resp : Option (SchedEv n) := none
  done : List (PhaseRec n) := []

/-! ## Client code (Algorithm 2) -/

section Handlers

variable (β : ℚ) (p : Fin n) (t : ℕ)

/-- `COLLECT_p` (Lines 26–29). -/
def onCollect (s : NodeState n) : Out n :=
  { st := { s with phase := .collect, tag := s.tag + 1, threshold := β * numMembers n,
                   counter := 0, phaseStart := t }
    bcasts := [.collectQuery (s.tag + 1) p] }

/-- `STORE_p(v)` (Lines 37–42). -/
def onStore (v : ℕ) (s : NodeState n) : Out n :=
  let lv := merge s.lview [(p, v, s.sqno + 1)]
  { st := { s with phase := .store, tag := s.tag + 1, sqno := s.sqno + 1, lview := lv,
                   threshold := β * numMembers n, counter := 0, phaseStart := t }
    bcasts := [.store lv (s.tag + 1) p] }

/-- Receipt of `⟨collect-reply, RView, tg, q⟩` (Lines 30–36); with repair 2, only during the
collect phase. When the threshold is reached, the collect phase ends and the store-back starts:
the *current* `LView` is broadcast in a `store` message (Line 36). -/
def onCollectReply (rv : View n) (tg : ℕ) (q : Fin n) (s : NodeState n) : Out n :=
  if tg = s.tag ∧ q = p ∧ s.phase = .collect then
    let lv := merge s.lview rv
    if ((s.counter + 1 : ℕ) : ℚ) ≥ s.threshold then
      { st := { s with lview := lv, counter := 0, threshold := β * numMembers n,
                       phase := .storeBack, phaseStart := t }
        bcasts := [.store lv s.tag p]
        done := [⟨p, .collect, s.phaseStart, t⟩] }
    else { st := { s with lview := lv, counter := s.counter + 1 } }
  else { st := s }

/-- Receipt of `⟨store-ack, tg, q⟩` (Lines 43–47); with repair 2, only during a store phase.
When the threshold is reached, a store returns `ACK` (Line 46) and a collect returns the
**current** value of `LView` (Line 47). -/
def onStoreAck (tg : ℕ) (q : Fin n) (s : NodeState n) : Out n :=
  if tg = s.tag ∧ q = p ∧ (s.phase = .store ∨ s.phase = .storeBack) then
    if ((s.counter + 1 : ℕ) : ℚ) ≥ s.threshold then
      { st := { s with counter := s.counter + 1, phase := .idle }
        resp := some (if s.phase = .store then .ack p else .ret p s.lview)
        done := [⟨p, .store, s.phaseStart, t⟩] }
    else { st := { s with counter := s.counter + 1 } }
  else { st := s }

end Handlers

/-! ## Server code (Algorithm 3) -/

/-- Receipt of `⟨store, RView, tg, q⟩` (Lines 48–51): merge into `LView`, acknowledge to `q` (if
joined) and echo the new `LView`. -/
def onStoreMsg (rv : View n) (tg : ℕ) (q : Fin n) (s : NodeState n) : Out n :=
  let lv := merge s.lview rv
  { st := { s with lview := lv }
    bcasts := (if s.isJoined then [.storeAck tg q] else []) ++ [.storeEcho lv] }

/-- Receipt of `⟨collect-query, tg, q⟩` (Lines 52–53). -/
def onCollectQuery (tg : ℕ) (q : Fin n) (s : NodeState n) : Out n :=
  { st := s, bcasts := if s.isJoined then [.collectReply s.lview tg q] else [] }

/-- Receipt of `⟨store-echo, RView⟩` (Line 54). -/
def onStoreEcho (rv : View n) (s : NodeState n) : Out n :=
  { st := { s with lview := merge s.lview rv } }

/-- Dispatch of a received message to its handler at node `p` at time `t`. -/
def onReceive (β : ℚ) (p : Fin n) (t : ℕ) : Msg n → NodeState n → Out n
  | .collectQuery tg q => onCollectQuery tg q
  | .collectReply rv tg q => onCollectReply β p t rv tg q
  | .store rv tg q => onStoreMsg rv tg q
  | .storeAck tg q => onStoreAck p t tg q
  | .storeEcho rv => onStoreEcho rv

/-! ## Executions -/

/-- Events of an execution: invocations, and receipt by `p` of the broadcast number `k` (broadcasts
are numbered globally in the order they are sent). -/
inductive Ev (n : ℕ) where
  | collect (p : Fin n)
  | store (p : Fin n) (v : ℕ)
  | recv (p : Fin n) (k : ℕ)
  deriving DecidableEq

/-- A timed event. -/
structure TEv (n : ℕ) where
  time : ℕ
  ev : Ev n
  deriving DecidableEq

/-- A broadcast: sender, sending time and message. -/
structure Bcast (n : ℕ) where
  sender : Fin n
  time : ℕ
  msg : Msg n

/-- A global configuration: the local states, all broadcasts sent so far (broadcast number `k` is
`sent[k]`), the broadcasts received by each node, the schedule of invocations and responses
(Section 3: "the restriction of the execution to the store and collect invocations and responses"),
and the completed phases. -/
structure Config (n : ℕ) where
  time : ℕ
  node : Fin n → NodeState n
  sent : List (Bcast n)
  rcvd : Fin n → List ℕ
  sched : List (SchedEv n)
  phases : List (PhaseRec n)

/-- The initial configuration. -/
def Config.init : Config n :=
  { time := 0, node := fun _ => .init, sent := [], rcvd := fun _ => [], sched := [], phases := [] }

/-- Apply the step `o` of node `p` at time `t` (preceded by the invocation `inv`, if any). -/
def Config.apply (c : Config n) (t : ℕ) (p : Fin n) (inv : Option (SchedEv n)) (o : Out n) :
    Config n :=
  { time := t
    node := Function.update c.node p o.st
    sent := c.sent ++ o.bcasts.map (fun m => ⟨p, t, m⟩)
    rcvd := c.rcvd
    sched := c.sched ++ inv.toList ++ o.resp.toList
    phases := c.phases ++ o.done }

/-- One step of the execution. (For an invalid receipt it does nothing; such steps are excluded by
`Admissible`.) -/
def Config.step (β : ℚ) (c : Config n) : TEv n → Config n
  | ⟨t, .collect p⟩ => c.apply t p (some (.colInv p)) (onCollect β p t (c.node p))
  | ⟨t, .store p v⟩ => c.apply t p (some (.stInv p v)) (onStore β p t v (c.node p))
  | ⟨t, .recv p k⟩ =>
    match c.sent[k]? with
    | some b =>
      let c' := c.apply t p none (onReceive β p t b.msg (c.node p))
      { c' with rcvd := Function.update c.rcvd p (k :: c.rcvd p) }
    | none => c

/-- The configuration reached by an execution. -/
def run (β : ℚ) (ex : List (TEv n)) : Config n := ex.foldl (Config.step β) Config.init

/-- Validity of the receipt by `p` at time `t` of broadcast number `k`, which is `b` (if sent):
`p` has not received it yet, its delay is in `(0, D]`, and (FIFO) `p` has already received every
earlier broadcast of the same sender. -/
def Config.RecvOk (D : ℕ) (c : Config n) (t : ℕ) (p : Fin n) (k : ℕ) : Option (Bcast n) → Prop
  | none => False
  | some b => k ∉ c.rcvd p ∧ b.time < t ∧ t ≤ b.time + D ∧
      ∀ k' < k, (c.sent[k']?.map Bcast.sender = some b.sender) → k' ∈ c.rcvd p

instance (D : ℕ) (c : Config n) (t : ℕ) (p : Fin n) (k : ℕ) :
    ∀ ob, Decidable (c.RecvOk D t p k ob)
  | none => inferInstanceAs (Decidable False)
  | some _ => inferInstanceAs (Decidable (_ ∧ _))

/-- Validity of the next event `e` in configuration `c` (Section 3):
* times are nondecreasing;
* an invocation happens only at a node without a pending operation (well-formed interaction; all
  nodes are members);
* a receipt is valid in the sense of `Config.RecvOk` (sent, not yet received, delay in `(0, D]`,
  FIFO). -/
def Config.Valid (D : ℕ) (c : Config n) : TEv n → Prop
  | ⟨t, .collect p⟩ => c.time ≤ t ∧ (c.node p).phase = .idle
  | ⟨t, .store p _⟩ => c.time ≤ t ∧ (c.node p).phase = .idle
  | ⟨t, .recv p k⟩ => c.time ≤ t ∧ c.RecvOk D t p k c.sent[k]?

instance (D : ℕ) (c : Config n) : ∀ e : TEv n, Decidable (c.Valid D e)
  | ⟨_, .collect _⟩ => inferInstanceAs (Decidable (_ ∧ _))
  | ⟨_, .store _ _⟩ => inferInstanceAs (Decidable (_ ∧ _))
  | ⟨_, .recv _ _⟩ => inferInstanceAs (Decidable (_ ∧ _))

/-- Completeness: every broadcast has been received by every node. Since all nodes are active
forever, reliable broadcast (Section 3) requires this of a finite execution after which no more
events occur. -/
def Config.Complete (c : Config n) : Prop :=
  ∀ k < c.sent.length, ∀ p : Fin n, k ∈ c.rcvd p

instance (c : Config n) : Decidable c.Complete := inferInstanceAs (Decidable (∀ k < _, _))

/-- Admissibility of the execution `es` from configuration `c`. -/
def AdmissibleFrom (β : ℚ) (D : ℕ) : Config n → List (TEv n) → Prop
  | c, [] => c.Complete
  | c, e :: es => c.Valid D e ∧ AdmissibleFrom β D (c.step β e) es

instance (β : ℚ) (D : ℕ) : ∀ (c : Config n) (es : List (TEv n)),
    Decidable (AdmissibleFrom β D c es)
  | c, [] => inferInstanceAs (Decidable c.Complete)
  | c, e :: es =>
    have := instDecidableAdmissibleFrom β D (c.step β e) es
    inferInstanceAs (Decidable (_ ∧ _))

/-- An admissible static execution of CCC with parameter `β` and maximal message delay `D`: a
finite sequence of timed events, valid at every step, after which every broadcast has been received
by every node (afterwards nothing happens; all nodes stay active forever). -/
def Admissible (β : ℚ) (D : ℕ) (ex : List (TEv n)) : Prop := AdmissibleFrom β D Config.init ex

instance (β : ℚ) (D : ℕ) (ex : List (TEv n)) : Decidable (Admissible β D ex) :=
  inferInstanceAs (Decidable (AdmissibleFrom β D Config.init ex))

/-- The store-collect schedule of an execution (Section 3). -/
def schedule (β : ℚ) (ex : List (TEv n)) : List (SCEv (Fin n) ℕ) :=
  (run β ex).sched.map SchedEv.toSC

/-- The state of node `p` at time `t` (Section 3: the state after the last step with time `≤ t`). -/
def stateAt (β : ℚ) (ex : List (TEv n)) (t : ℕ) (p : Fin n) : NodeState n :=
  (run β (ex.takeWhile (fun e => e.time ≤ t))).node p

/-- `view(φ)` for a completed phase `φ` (Section 4): the value of `LView` of its node at the time
the phase ends. -/
def phaseView (β : ℚ) (ex : List (TEv n)) (φ : PhaseRec n) : View n :=
  (stateAt β ex φ.finish φ.node).lview

end Podc.StoreCollectChurn.CCC
