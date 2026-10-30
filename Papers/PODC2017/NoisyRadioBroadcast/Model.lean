import Cslib.Probability.Finite.Bernoulli
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Order.LiminfLimsup
import Mathlib.Data.ENat.Lattice
import Mathlib.Basic.Real.ENatENNReal
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Topology.Instances.ENNReal.Lemmas

-- CSLib candidate: noisy radio network model (synchronous radio networks with random sender or
-- receiver faults, routing and coding schedules, throughput).

/-!
# The noisy radio network model (Section 3 of the paper)

Censor-Hillel, Haeupler, Hershkowitz, Zuzic. *Broadcasting in Noisy Radio Networks.* PODC 2017.

**Radio networks.** A topology is a finite simple graph `G` on the nodes `V` with a source `s`.
Time proceeds in synchronous rounds. In each round every node either listens or broadcasts a
packet. A node `u` *hears* `w` in a round if `u` listens, `w` is a neighbour of `u` that broadcasts,
and `w` is the only broadcasting neighbour of `u` (`Hears`). There is no collision detection: a
collision, silence and noise all sound the same.

**Faults.** Every round, every node flips an independent coin that is *clean* (`true`) with
probability `1 - p` and *faulty* with probability `p`. In the *receiver faults* model a node that
hears `w` receives `w`'s packet iff its own coin is clean; in the *sender faults* model iff `w`'s
coin is clean (a faulty sender transmits noise, which still collides). A run is driven by a coin
sequence `ω : ℕ → V → Bool` (`ω r u` is the coin of `u` in round `r`). The *faultless* model is
the run with all coins clean.

**Routing.** There are `k` messages `Fin k`, initially known only to the source. A node broadcasts
one message it knows (routing). The knowledge state is `K : V → Finset (Fin k)`. An *adaptive
routing schedule* (Definition 14) is a sequence of functions, one per round, mapping the current
knowledge state (all pairs `(u, i)` such that `u` has received `mᵢ`) to an action of every node:
silent (`none`) or broadcast `mᵢ` (`some i`). As in the paper, a node directed to broadcast a
message it does not know stays silent (`effective`). A non-adaptive (*static*) schedule is one that
ignores the knowledge state; in the faultless model this is the paper's notion of routing schedule.

**Coding.** Messages and packets are drawn from a finite alphabet `A` (in the paper both have
`O(log (n k))` bits; we use the same alphabet for both). In a coding schedule each node's action
(silent or a packet) in round `r` is an arbitrary function of its own history of received packets
(and, for the source, of the messages); after the last round every node decodes the messages from
its history.

**Success and throughput** (Definition 1). A schedule *succeeds* with probability at least
`1 - 1/k` within `R` rounds if, under the product law of the coins of rounds `0, …, R - 1`, every
node knows (decodes) all `k` messages after round `R - 1` with probability at least `1 - 1/k` (for
coding: for every message vector). `routingRounds`/`codingRounds` is the least such `R` (`⊤` if
none exists) and the throughput is `limsup_{k → ∞} k / (least number of rounds)`.
-/

namespace Podc.NoisyRadioBroadcast

open Finset Filter
open scoped ENNReal

/-- The two fault models of the paper. -/
inductive FaultModel
  | sender
  | receiver
  deriving DecidableEq

variable {V : Type*} [Fintype V] [DecidableEq V]

section Radio

variable (G : SimpleGraph V) {X : Type*}

/-- `u` hears `w` in a round with actions `a` (`none` = listen, `some x` = broadcast `x`): `u`
listens, and `w` is the unique broadcasting neighbour of `u`. -/
def Hears (a : V → Option X) (u w : V) : Prop :=
  a u = none ∧ G.Adj u w ∧ (a w).isSome ∧ ∀ w', G.Adj u w' → (a w').isSome → w' = w

/-- The coin deciding whether a transmission from `w` to `u` gets through: the receiver's coin
for receiver faults, the sender's coin for sender faults. -/
def faultCoin : FaultModel → (V → Bool) → V → V → Bool
  | .receiver, c, u, _ => c u
  | .sender, c, _, w => c w

open Classical in
/-- The packet that `u` receives in a round with actions `a` and coins `c` under the fault model
`f` (`none`: nothing, i.e. silence, collision or noise). -/
noncomputable def heard (f : FaultModel) (a : V → Option X) (c : V → Bool) (u : V) : Option X :=
  if h : ∃ w, Hears G a u w ∧ faultCoin f c u w = true then a (Classical.choose h) else none

omit [DecidableEq V] in
theorem heard_eq_some_iff {f : FaultModel} {a : V → Option X} {c : V → Bool} {u : V} {x : X} :
    heard G f a c u = some x ↔ ∃ w, Hears G a u w ∧ faultCoin f c u w = true ∧ a w = some x := by
  classical
  unfold heard
  split_ifs with h
  · constructor
    · intro hx
      exact ⟨_, (Classical.choose_spec h).1, (Classical.choose_spec h).2, hx⟩
    · rintro ⟨w, hw, -, hx⟩
      have h1 := (Classical.choose_spec h).1
      have : Classical.choose h = w := hw.2.2.2 _ h1.2.1 h1.2.2.1
      rw [this, hx]
  · simp only [reduceCtorEq, false_iff, not_exists, not_and]
    intro w hw hc _
    exact h ⟨w, hw, hc⟩

end Radio

/-! ### Routing -/

section Routing

variable {k : ℕ}

/-- Knowledge state: the messages known by every node. -/
abbrev Know (V : Type*) (k : ℕ) := V → Finset (Fin k)

/-- Initially only the source knows the messages (all of them). -/
def initKnow (s : V) : Know V k := fun u => if u = s then univ else ∅

/-- An adaptive routing schedule (Definition 14): in round `r`, given the knowledge state, every
node is told to stay silent (`none`) or to broadcast message `i` (`some i`). -/
abbrev AdaptiveSchedule (V : Type*) (k : ℕ) := ℕ → Know V k → V → Option (Fin k)

/-- A non-adaptive routing schedule: the action of every node in every round is fixed in
advance. -/
abbrev StaticSchedule (V : Type*) (k : ℕ) := ℕ → V → Option (Fin k)

/-- A static schedule as an adaptive one. -/
def StaticSchedule.toAdaptive (b : StaticSchedule V k) : AdaptiveSchedule V k := fun r _ => b r

/-- Routing: a node directed to broadcast a message it does not know stays silent. -/
def effective (K : Know V k) (a : V → Option (Fin k)) : V → Option (Fin k) := fun u =>
  match a u with
  | some i => if i ∈ K u then some i else none
  | none => none

variable (G : SimpleGraph V)

/-- One round of routing: every node adds the message it receives (if any). -/
noncomputable def stepKnow (f : FaultModel) (K : Know V k) (a : V → Option (Fin k))
    (c : V → Bool) : Know V k := fun u =>
  match heard G f (effective K a) c u with
  | some i => insert i (K u)
  | none => K u

/-- The knowledge state before round `r` of the run of the adaptive schedule `sch` driven by the
coins `ω`. -/
noncomputable def run (s : V) (f : FaultModel) (sch : AdaptiveSchedule V k) (ω : ℕ → V → Bool) :
    ℕ → Know V k
  | 0 => initKnow s
  | r + 1 => stepKnow G f (run s f sch ω r) (sch r (run s f sch ω r)) (ω r)

/-- Every node knows every message. -/
def Delivered (K : Know V k) : Prop := ∀ u, K u = univ

end Routing

/-! ### Probability of an event of the first `R` rounds -/

section Prob

/-- Extends the coins of rounds `0, …, R - 1` by clean coins. -/
def extendCoins {R : ℕ} (y : Fin R → V → Bool) : ℕ → V → Bool := fun r =>
  if h : r < R then y ⟨r, h⟩ else fun _ => true

open Classical in
/-- The probability of the event `E` (about the coin sequence; only rounds `< R` should matter)
when every coin of rounds `0, …, R - 1` is independently clean with probability `1 - p`. -/
noncomputable def prob (p : ℝ) (R : ℕ) (E : (ℕ → V → Bool) → Prop) : ℝ :=
  ∑ y : Fin R → V → Bool, (∏ r, Cslib.Probability.coinProb (1 - p) (y r)) *
    if E (extendCoins y) then 1 else 0

end Prob

/-! ### Coding -/

section Coding

variable {A : Type*} {k : ℕ}

/-- A (network) coding schedule for `k` messages over the alphabet `A` (Section 3.1). In round `r`,
node `u` stays silent or broadcasts a packet as a function of its input (`some m` for the source,
which knows the message vector `m`, `none` for the other nodes) and of the list of what it received
in the previous rounds; `dec u` decodes the messages from the final history of `u`. -/
structure CodingSchedule (V A : Type*) (k : ℕ) where
  /-- The action of node `u` in round `r`. -/
  act : ℕ → V → Option (Fin k → A) → List (Option A) → Option A
  /-- The decoder of node `u`. -/
  dec : V → List (Option A) → Fin k → A

variable (G : SimpleGraph V) (s : V) (f : FaultModel)

/-- The histories (received packets, one entry per round) before round `r` in the run of the coding
schedule `sch` on the message vector `m`, driven by the coins `ω`. -/
noncomputable def codingHist (sch : CodingSchedule V A k) (m : Fin k → A) (ω : ℕ → V → Bool) :
    ℕ → V → List (Option A)
  | 0 => fun _ => []
  | r + 1 => fun u =>
    let h := codingHist sch m ω r
    h u ++ [heard G f (fun v => sch.act r v (if v = s then some m else none) (h v)) (ω r) u]

/-- After `R` rounds every node other than the source decodes the message vector `m`. -/
def CodingDecodes (sch : CodingSchedule V A k) (m : Fin k → A) (ω : ℕ → V → Bool) (R : ℕ) :
    Prop :=
  ∀ u, u ≠ s → sch.dec u (codingHist G s f sch m ω R u) = m

end Coding

/-! ### Rounds and throughput (Definition 1) -/

section Throughput

variable (G : SimpleGraph V) (s : V) (f : FaultModel) (p : ℝ)

/-- The adaptive routing schedule `sch` delivers the `k` messages within `R` rounds with probability
at least `1 - 1/k`. -/
def RoutingSucceeds (k : ℕ) (sch : AdaptiveSchedule V k) (R : ℕ) : Prop :=
  1 - 1 / (k : ℝ) ≤ prob p R (fun ω => Delivered (run G s f sch ω R))

/-- The least number of rounds of an adaptive routing schedule that delivers `k` messages with
probability at least `1 - 1/k` (`⊤` if there is none). -/
noncomputable def routingRounds (k : ℕ) : ℕ∞ :=
  ⨅ (R : ℕ) (_ : ∃ sch : AdaptiveSchedule V k, RoutingSucceeds G s f p k sch R), (R : ℕ∞)

/-- The adaptive routing throughput `τ^R(G, s)` (Definition 1 with Definition 14). -/
noncomputable def routingThroughput : ℝ≥0∞ :=
  limsup (fun k : ℕ => (k : ℝ≥0∞) / (routingRounds G s f p k : ℝ≥0∞)) atTop

/-- The least number of rounds of a static schedule that delivers `k` messages in the faultless
model (every coin clean). -/
noncomputable def faultlessRounds (k : ℕ) : ℕ∞ :=
  ⨅ (R : ℕ) (_ : ∃ b : StaticSchedule V k,
      Delivered (run G s .receiver b.toAdaptive (fun _ _ => true) R)), (R : ℕ∞)

/-- The routing throughput of the faultless model (Definition 1, faultless setting). -/
noncomputable def faultlessThroughput : ℝ≥0∞ :=
  limsup (fun k : ℕ => (k : ℝ≥0∞) / (faultlessRounds G s k : ℝ≥0∞)) atTop

/-- The coding schedule `sch` over `A` decodes every message vector within `R` rounds with
probability at least `1 - 1/k`. -/
def CodingSucceeds {A : Type*} (k : ℕ) (sch : CodingSchedule V A k) (R : ℕ) : Prop :=
  ∀ m : Fin k → A, 1 - 1 / (k : ℝ) ≤ prob p R (fun ω => CodingDecodes G s f sch m ω R)

/-- The least number of rounds of a coding schedule over `A` for `k` messages that succeeds with
probability at least `1 - 1/k`. -/
noncomputable def codingRounds (A : Type*) (k : ℕ) : ℕ∞ :=
  ⨅ (R : ℕ) (_ : ∃ sch : CodingSchedule V A k, CodingSucceeds G s f p k sch R), (R : ℕ∞)

/-- The coding throughput `τ^NC(G, s)` (Definition 1), where the messages and packets for `k`
messages are drawn from the alphabet `A k`. -/
noncomputable def codingThroughput (A : ℕ → Type*) : ℝ≥0∞ :=
  limsup (fun k : ℕ => (k : ℝ≥0∞) / (codingRounds G s f p (A k) k : ℝ≥0∞)) atTop

end Throughput

/-! ### The star topology -/

/-- The star topology of Section 5.1.1: the source `none` adjacent to the `n` leaves `some i`. -/
def star (n : ℕ) : SimpleGraph (Option (Fin n)) where
  Adj a b := (a = none ∧ b ≠ none) ∨ (a ≠ none ∧ b = none)
  symm := ⟨fun a b h => by tauto⟩
  loopless := ⟨fun a h => by tauto⟩

instance (n : ℕ) : DecidableRel (star n).Adj := fun a b => by
  unfold star; infer_instance

end Podc.NoisyRadioBroadcast
