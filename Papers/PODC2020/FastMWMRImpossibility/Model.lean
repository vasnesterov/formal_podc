import Cslib.Computability.Distributed.MessagePassing.Async
import Mathlib.Data.List.FinRange

/-!
# Round-trip implementations of a multi-writer register (W1R2)

The system model of §2 of Huang–Huang–Wei (PODC 2020): `n` servers `s₀, …, s_{n-1}` (`Fin n`),
writers `W` and readers `R` (disjoint from the servers), communicating by asynchronous,
reliable, unordered message passing (CSLib `Cslib.AsyncMP`); up to `t` servers may crash, so a
client can only wait for `n - t` replies in each round-trip. Servers do not communicate with each
other.

A *round-trip* of a client: the client sends one message to every server; a server, upon
receiving a message, processes it and replies immediately; the client collects the replies of the
current round-trip and, once it has at least `n - t` of them (the scheduler decides exactly when,
possibly after more replies arrived), it continues. A **W1R2 algorithm** (`W1R2Alg`) is an
algorithm in which a write is one round-trip and a read is two round-trips. It is given by
arbitrary deterministic functions:

* servers: `reply s log c m` is the reply of server `s` to message `m` from client `c`, where
  `log` is the list of messages (with senders) that `s` processed before. Every deterministic
  server automaton is of this form (its state is a function of its log), so nothing is lost
  (this is also the paper's "full-info model" of §4.1);
* writers (local state `LW` between operations): `wMsg w st v s` is the message sent to server
  `s` by `write(v)`, `wEnd` the new local state, computed from the replies;
* readers (local state `LR`): `rMsg1 r st s` is the first-round message to `s`, `rMsg2 r st V₁ s`
  the second-round message (`V₁` = the replies of the first round, in arrival order), and
  `rEnd r st V₁ V₂` the returned value and the new local state.

Views are lists of `(server, reply)` in arrival order, so readers may even use the arrival order.

`W1R2Alg.protocol t v₀` is the induced `Cslib.AsyncMP.Protocol` implementing `register V v₀`.
Messages carry the client's operation counter `k` and the round index `i` (`Pkt`), so that late
replies of earlier round-trips are ignored.
-/

namespace Podc.FastMWMR

open Cslib.SharedMemory Cslib.AsyncMP

/-- Processes: servers, writers and readers. -/
inductive Node (n : ℕ) (W R : Type) where
  | srv (s : Fin n)
  | wr (w : W)
  | rd (r : R)
  deriving DecidableEq

/-- Network packets: a request of round-trip `i` of the `k`-th operation of a client, and the
reply to it. -/
inductive Pkt (Msg Rep : Type) where
  | req (k i : ℕ) (m : Msg)
  | rep (k i : ℕ) (r : Rep)
  deriving DecidableEq

/-- What a client learned in one round-trip: the replies, in arrival order. -/
abbrev View (n : ℕ) (Rep : Type) := List (Fin n × Rep)

/-- A W1R2 algorithm (fast write: one round-trip; read: two round-trips) for a multi-writer
multi-reader register with values `V`, messages `Msg`, replies `Rep`, writer states `LW` and
reader states `LR`. -/
structure W1R2Alg (n : ℕ) (W R V Msg Rep LW LR : Type) where
  /-- Reply of server `s` to message `m` from `c`, after having processed `log`. -/
  reply : Fin n → List (Node n W R × Msg) → Node n W R → Msg → Rep
  /-- Initial writer states. -/
  initW : W → LW
  /-- Message of `write(v)` to server `s`. -/
  wMsg : W → LW → V → Fin n → Msg
  /-- Writer state after `write(v)` with replies `acks`. -/
  wEnd : W → LW → V → View n Rep → LW
  /-- Initial reader states. -/
  initR : R → LR
  /-- First round-trip message of a read to server `s`. -/
  rMsg1 : R → LR → Fin n → Msg
  /-- Second round-trip message of a read to server `s`, given the first-round replies. -/
  rMsg2 : R → LR → View n Rep → Fin n → Msg
  /-- Returned value and new reader state, given the replies of both round-trips. -/
  rEnd : R → LR → View n Rep → View n Rep → V × LR

/-- Control position of a reader. -/
inductive RPhase (n : ℕ) (Rep : Type) where
  | idle
  /-- first round-trip, replies so far -/
  | one (acks : View n Rep)
  /-- second round-trip, with the replies `V₁` of the first one and the replies so far -/
  | two (V₁ acks : View n Rep)

/-- Local states of the processes. -/
inductive Loc (n : ℕ) (W R V Msg Rep LW LR : Type) where
  /-- a server: the messages processed so far -/
  | srv (log : List (Node n W R × Msg))
  /-- a writer: local state, operation counter, pending write and its replies so far -/
  | wr (st : LW) (k : ℕ) (cur : Option (V × View n Rep))
  /-- a reader: local state, operation counter, control position -/
  | rd (st : LR) (k : ℕ) (ph : RPhase n Rep)

variable {n : ℕ} {W R V Msg Rep LW LR : Type}

/-- A client collects reply `r` of server `s` to round-trip `i` of its `k`-th operation (ignored
if it does not belong to the current round-trip). -/
def Loc.absorb (l : Loc n W R V Msg Rep LW LR) (s : Fin n) (k i : ℕ) (r : Rep) :
    Loc n W R V Msg Rep LW LR :=
  match l with
  | .wr st k' (some (v, acks)) =>
    if k = k' ∧ i = 1 then .wr st k' (some (v, acks ++ [(s, r)])) else l
  | .rd st k' (.one acks) =>
    if k = k' ∧ i = 1 then .rd st k' (.one (acks ++ [(s, r)])) else l
  | .rd st k' (.two V₁ acks) =>
    if k = k' ∧ i = 2 then .rd st k' (.two V₁ (acks ++ [(s, r)])) else l
  | _ => l

/-- Send `req k i (f s)` to every server `s`. -/
def bcast (k i : ℕ) (f : Fin n → Msg) : Multiset (Node n W R × Pkt Msg Rep) :=
  (((List.finRange n).map fun s => (Node.srv s, Pkt.req k i (f s)) :
    List (Node n W R × Pkt Msg Rep)) : Multiset _)

namespace W1R2Alg

variable (A : W1R2Alg n W R V Msg Rep LW LR)

/-- The asynchronous message-passing protocol induced by a W1R2 algorithm, where clients wait for
`n - t` replies per round-trip. It implements `register V v₀`: writers only invoke writes,
readers only invoke reads (other invocations are not enabled). -/
def protocol (t : ℕ) (v₀ : V) :
    Protocol (Node n W R) (register V v₀) (Loc n W R V Msg Rep LW LR) (Pkt Msg Rep) Unit where
  init
    | .srv _ => .srv []
    | .wr w => .wr (A.initW w) 0 none
    | .rd r => .rd (A.initR r) 0 .idle
  invoke p o l :=
    match p, o, l with
    | .wr w, .write v, .wr st k none =>
      some (.wr st (k + 1) (some (v, [])), bcast (k + 1) 1 (A.wMsg w st v))
    | .rd r, .read, .rd st k .idle =>
      some (.rd st (k + 1) (.one []), bcast (k + 1) 1 (A.rMsg1 r st))
    | _, _, _ => none
  internal p _ l :=
    match p, l with
    | .wr w, .wr st k (some (v, acks)) =>
      if n ≤ acks.length + t then some (.wr (A.wEnd w st v acks) k none, 0, some v) else none
    | .rd r, .rd st k (.one acks) =>
      if n ≤ acks.length + t then some (.rd st k (.two acks []), bcast k 2 (A.rMsg2 r st acks), none)
      else none
    | .rd r, .rd st k (.two V₁ acks) =>
      if n ≤ acks.length + t then
        some (.rd (A.rEnd r st V₁ acks).2 k .idle, 0, some (A.rEnd r st V₁ acks).1)
      else none
    | _, _ => none
  receive p q m l :=
    match p, q, m, l with
    | .srv s, c, .req k i msg, .srv log =>
      some (.srv (log ++ [(c, msg)]), {(c, .rep k i (A.reply s log c msg))}, none)
    | .wr _, .srv s, .rep k i r, l => some (l.absorb s k i r, 0, none)
    | .rd _, .srv s, .rep k i r, l => some (l.absorb s k i r, 0, none)
    | _, _, _, l => some (l, 0, none)

end W1R2Alg

end Podc.FastMWMR
