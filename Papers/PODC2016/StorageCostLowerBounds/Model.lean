import Mathlib
import Podc.Computability.Distributed.MessagePassing.ChannelFailures.Delivery
import Cslib.Computability.Distributed.SharedMemory.SWSRRegister

/-!
# Storage cost of shared-memory emulation: the model

Cadambe, Wang, Lynch, *Information-Theoretic Lower Bounds on the Storage Cost of Shared Memory
Emulation*, PODC 2016 (arXiv 1605.06844v2), Section 3.

We use the asynchronous message-passing model `Cslib.ChannelFailures` (deterministic processes,
reliable FIFO channels, crashes = processes taking finitely many steps; messages sent by a crashed
process need not be delivered). The nodes are `n` servers `srv i`, one writer `wr` and one reader
`rd`; the emulated object is CSLib's `register V v₀`.

* `EvOk e`: the single-writer single-reader environment (only the writer invokes writes, only
  the reader invokes reads, servers invoke nothing).
* `Regular v₀ α`: the history `α` is regular (Lamport): every completed read returns the value
  of a write that does not start after the read returns and is not overwritten by a write that
  completes before the read is invoked (or the initial value).
* `IsRegular Alg`, `IsAtomic Alg`: safety of all finite executions in the SWSR environment.
* `Live Alg f`: in every fair execution with at most `f` server failures (any number of client
  failures), every operation invoked by a non-crashed client returns.
* `StateBound Alg S`: server `i` is always in a state of the finite set `S i`. The storage cost
  of server `i` is `log₂ |S i|`; `maxStorage`, `totalStorage`.
* `NoGossip Alg`: servers never send messages to servers.
* `ReaderQuiet Alg` (our repair, not in the paper): in an execution in which the reader takes
  no step, no server sends a message to the reader.
-/

namespace Podc.StorageCost

open Cslib.ChannelFailures Cslib.SharedMemory

/-- Nodes: servers, the writer and the reader. -/
inductive Node (n : ℕ) where
  | srv (i : Fin n)
  | wr
  | rd
  deriving DecidableEq, Fintype

variable {n : ℕ} {V : Type} {v₀ : V} {M L : Type}

/-- The single-writer single-reader environment. -/
def EvOk (e : Event (Node n) (register V v₀)) : Prop :=
  ∀ p o, e = .invoke p o → RWOp.SWSR (Node.wr : Node n) Node.rd p o

/-- Regularity of a history of `register V v₀` with writer `wr` and reader `rd`: the `k`-th
completed read returns the value of write `m` (`m = 0`: the initial value; `m ≥ 1`: the `m`-th
write), which was invoked before the read returned and was not overwritten before the read was
invoked (write `m + 1` does not precede the read). -/
def Regular (v₀ : V) (α : List (Label (Node n) (register V v₀))) : Prop :=
  ∀ k < (respsOf α .rd).length, ∃ m,
    respOf α (.rd, k) = some (writeVal v₀ (opsOf α .wr) m) ∧
    (0 < m → ¬ Precedes α (.rd, k) (.wr, m - 1)) ∧ ¬ Precedes α (.wr, m) (.rd, k)

variable (Alg : Algorithm (Node n) (register V v₀) M L)

/-- Every finite execution in the SWSR environment is regular. -/
def IsRegular : Prop :=
  ∀ E : List (Event (Node n) (register V v₀)), (∀ e ∈ E, EvOk e) →
    Regular v₀ (Alg.hist Alg.initCfg E)

/-- Every finite execution in the SWSR environment is atomic (linearizable). -/
def IsAtomic : Prop :=
  ∀ E : List (Event (Node n) (register V v₀)), (∀ e ∈ E, EvOk e) →
    ∃ Lin, IsLinearization (Alg.hist Alg.initCfg E) Lin

/-- The servers that may fail in a failure pattern. -/
noncomputable def srvFail (fp : FailurePattern (Node n)) : Finset (Fin n) :=
  by classical exact Finset.univ.filter fun i => Node.srv i ∈ fp.procs

/-- Liveness: in a fair execution (SWSR environment) with at most `f` server failures and any
number of client failures, every operation invoked by a non-crashed process returns. -/
def Live (f : ℕ) : Prop :=
  ∀ fp : FailurePattern (Node n), fp.chans = ∅ → (srvFail fp).card ≤ f →
    ∀ ev, Alg.Fair fp ev → (∀ t, EvOk (ev t)) →
      ∀ p, ¬ Algorithm.Crashed fp ev p → ∀ t₀ o, ev t₀ = .invoke p o →
        (Alg.cfgAt ev t₀).pend p = none → Alg.Returns ev p t₀

/-- The state of server `i` always belongs to `S i`. -/
def StateBound (S : Fin n → Finset L) : Prop :=
  ∀ E : List (Event (Node n) (register V v₀)), (∀ e ∈ E, EvOk e) →
    ∀ i, (Alg.run Alg.initCfg E).loc (.srv i) ∈ S i

/-- Servers do not gossip: every message is sent from a server to a client or from a client
(to anyone; the paper's clients only talk to servers). -/
def NoGossip : Prop :=
  ∀ i inp l, ∀ x ∈ (Alg.handle (.srv i) inp l).2.1, ∀ j, x.1 ≠ .srv j

/-- **Our extra hypothesis.** In an execution in which the reader takes no step, no server
has sent a message to the reader. -/
def ReaderQuiet : Prop :=
  ∀ E : List (Event (Node n) (register V v₀)), (∀ e ∈ E, EvOk e) → (∀ e ∈ E, e.owner ≠ .rd) →
    ∀ i, (Alg.run Alg.initCfg E).chan (.srv i) .rd = []

/-- A simple sufficient condition for `ReaderQuiet`: servers send to the reader only when they
process a message from the reader. -/
def RepliesOnly : Prop :=
  ∀ i inp l, (∀ m, inp ≠ .recv .rd m) → ∀ x ∈ (Alg.handle (.srv i) inp l).2.1, x.1 ≠ .rd

/-- Max-storage cost `max_i log₂ |S i|`. -/
noncomputable def maxStorage (S : Fin n → Finset L) : ℝ := ⨆ i, Real.logb 2 (S i).card

/-- Total-storage cost `∑_i log₂ |S i|`. -/
noncomputable def totalStorage (S : Fin n → Finset L) : ℝ := ∑ i, Real.logb 2 (S i).card

end Podc.StorageCost
