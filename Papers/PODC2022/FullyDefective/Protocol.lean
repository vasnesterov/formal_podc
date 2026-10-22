import Mathlib

/-!
# Asynchronous message-passing protocols on a noiseless network

The protocols `π` that the simulators of [CCGS22] run (Section 2, "Networks and protocols"):
deterministic, event-driven protocols. Each node starts from a state given by its input (and its
ID) and sends some messages; afterwards it acts only upon the reception of a message, updating
its state and sending messages, each to one destination. The noiseless network delivers every
message unaltered, after an arbitrary finite delay, in any order (channels are not FIFO).

The *local transcript* of a node is the sequence of its send and receive events. The simulation
theorems state that every execution of the simulator over the fully-defective network produces,
at every node, the local transcript (and state) of a node in some execution of `π` over the
noiseless network.

We do not restrict the destinations of messages: a protocol for a network `G` sends only to
neighbours in `G`, which is a special case.
-/

namespace Podc.FullyDefective

/-- An event of a local transcript. -/
inductive Event (V M : Type*) where
  /-- The node sent `m` to `dst`. -/
  | send (dst : V) (m : M)
  /-- The node received `m` from `src`. -/
  | recv (src : V) (m : M)

/-- A deterministic event-driven asynchronous message-passing protocol on the nodes `V`, with
messages `M`. Inputs (and IDs) are folded into the per-node functions `init` and `recv`. -/
structure Protocol (V M : Type*) where
  /-- Local states. -/
  State : Type
  /-- Initial state and the messages `(destination, content)` sent at start-up. -/
  init : V → State × List (V × M)
  /-- Reaction of node `v` in state `s` to a message `m` from `src`: new state and messages. -/
  recv : V → State → V → M → State × List (V × M)

namespace Protocol

variable {V M : Type*} (P : Protocol V M)

/-- A configuration of the noiseless network: local states, the multiset of messages in transit
`(source, destination, content)`, and the local transcripts. -/
structure Config where
  /-- Local states. -/
  st : V → P.State
  /-- Messages in transit. -/
  net : Multiset (V × V × M)
  /-- Local transcripts. -/
  tr : V → List (Event V M)

/-- The messages sent by `v`, as elements of the network. -/
def tag (v : V) (out : List (V × M)) : Multiset (V × V × M) :=
  ((out.map fun x => (v, x.1, x.2) : List (V × V × M)) : Multiset (V × V × M))

/-- The send events of a list of messages. -/
def sends (out : List (V × M)) : List (Event V M) := out.map fun x => .send x.1 x.2

/-- The initial configuration: every node has performed its start-up action. -/
def initCfg [Fintype V] : P.Config where
  st v := (P.init v).1
  net := ∑ v, tag v (P.init v).2
  tr v := sends (P.init v).2

variable [DecidableEq V] [DecidableEq M]

/-- Delivery of the message `x = (source, destination, content)`. -/
def deliver (c : P.Config) (x : V × V × M) : P.Config :=
  let r := P.recv x.2.1 (c.st x.2.1) x.1 x.2.2
  { st := Function.update c.st x.2.1 r.1
    net := c.net.erase x + tag x.2.1 r.2
    tr := Function.update c.tr x.2.1 (c.tr x.2.1 ++ [.recv x.1 x.2.2] ++ sends r.2) }

/-- One step of an execution: the (adversarial) network delivers a message in transit. -/
inductive Step : P.Config → P.Config → Prop
  | mk (c : P.Config) (x : V × V × M) : x ∈ c.net → Step c (P.deliver c x)

/-- Reachable configurations (prefixes of executions). -/
def Reach [Fintype V] (c : P.Config) : Prop := Relation.ReflTransGen P.Step P.initCfg c

/-- Quiescence: no message is in transit (hence nothing will ever happen again). -/
def Quiescent (c : P.Config) : Prop := c.net = 0

end Protocol

end Podc.FullyDefective
