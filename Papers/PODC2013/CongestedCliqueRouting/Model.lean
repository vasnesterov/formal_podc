import Mathlib

/-!
# The congested clique and the information distribution task

Model of Section 2 and Problem 3.1 of

  C. Lenzen, *Optimal Deterministic Routing and Sorting on the Congested Clique*, PODC 2013.

* `n` nodes with known identifiers; computation proceeds in synchronous rounds.
* In every round every node sends one *packet* to every node (itself included, as in the paper).
  A packet has `B` slots; each slot is empty or carries one *item*: either one of the messages that
  are being routed (an `O(log n)`-bit header plus payload), or a natural number.  The theorems
  bound `B` by an absolute constant and the numbers by `8 n²`, so a packet has `O(log n)` bits.
* Algorithms are deterministic and are given in *full-information form*: in round `t` node `v`
  computes its outgoing packets from its own identifier, its own input and the list of all packet
  vectors it has received so far.  Every deterministic algorithm with arbitrary local computation
  is of this form.
* A message item may only be sent by a node that *holds* the message: it is one of its own input
  messages, or it received the message in an earlier round (`Holds`).  Payloads are opaque: the
  only way to deliver a message is to forward it hop by hop.
-/

namespace CongestedCliqueRouting

/-- Content of one slot of a packet: a routed message or a number. -/
inductive Item (M : Type*) where
  | msg (m : M)
  | num (k : ℕ)
  deriving DecidableEq

/-- A packet with `B` slots. -/
abbrev Packet (M : Type*) (B : ℕ) := Fin B → Option (Item M)

/-- A deterministic algorithm on node set `V`, where nodes have inputs in `K`, routed messages
are in `M`, and packets have `B` slots, in full-information form: `A t v k h w` is the packet that
node `v` with input `k` sends to node `w` in round `t`, given the list `h` of packet vectors it
received in rounds `0, …, t-1` (`h[r] u` is the packet received from `u` in round `r`). -/
def Algorithm (V K M : Type*) (B : ℕ) := ℕ → V → K → List (V → Packet M B) → V → Packet M B

namespace Algorithm

variable {V K M : Type*} {B : ℕ}

/-- The list of packet vectors received by `v` in the first `t` rounds. -/
def hist (A : Algorithm V K M B) (inp : V → K) : ℕ → V → List (V → Packet M B)
  | 0, _ => []
  | t + 1, v => hist A inp t v ++ [fun u => A t u (inp u) (hist A inp t u) v]

/-- The packet sent from `u` to `v` in round `t`. -/
def sent (A : Algorithm V K M B) (inp : V → K) (t : ℕ) (u v : V) : Packet M B :=
  A t u (inp u) (A.hist inp t u) v

end Algorithm

/-! ## The information distribution task (Problem 3.1) -/

/-- Header of a routed message: source `src`, local index `idx` at the source, destination `dst`
(Problem 3.1: "each such message explicitly contains these values"). The payload is not modelled:
it is opaque, and messages can only be moved by forwarding them. -/
structure Header (n : ℕ) where
  src : Fin n
  idx : Fin n
  dst : Fin n
  deriving DecidableEq, Fintype

/-- A routing instance: node `i`'s `j`-th message (if any) has destination `d i j`.
Problem 3.1 is the special case where every node has exactly `n` messages
(`d i j = some _` for all `j`) and every node is the destination of exactly `n` messages. -/
abbrev RoutingInstance (n : ℕ) := Fin n → Fin n → Option (Fin n)

/-- Each node is the destination of at most `n` messages. -/
def RoutingInstance.LoadOK {n : ℕ} (d : RoutingInstance n) : Prop :=
  ∀ k : Fin n, (Finset.univ.filter (fun p : Fin n × Fin n => d p.1 p.2 = some k)).card ≤ n

/-- Node `v` holds message `h` at the beginning of round `t`: it is one of `v`'s own input
messages, or `v` received it in an earlier round. -/
def Holds {n B : ℕ} (A : Algorithm (Fin n) (Fin n → Option (Fin n)) (Header n) B)
    (d : RoutingInstance n) (t : ℕ) (v : Fin n) (h : Header n) : Prop :=
  (h.src = v ∧ d v h.idx = some h.dst) ∨
    ∃ r < t, ∃ u i, A.sent d r u v i = some (Item.msg h)

/-- `A` solves the routing task within `T` rounds on all instances with loads at most `n`:
numbers sent are at most `8 n²` (so every slot carries `O(log n)` bits), only held messages are
forwarded, and after `T` rounds every message is held by its destination. -/
def Solves {n B : ℕ} (A : Algorithm (Fin n) (Fin n → Option (Fin n)) (Header n) B)
    (T : ℕ) : Prop :=
  ∀ d : RoutingInstance n, d.LoadOK →
    (∀ t < T, ∀ u v i k, A.sent d t u v i = some (Item.num k) → k ≤ 8 * n ^ 2) ∧
    (∀ t < T, ∀ u v i h, A.sent d t u v i = some (Item.msg h) → Holds A d t u h) ∧
    (∀ i j k, d i j = some k → Holds A d T k ⟨i, j, k⟩)

end CongestedCliqueRouting
