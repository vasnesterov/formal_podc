import Mathlib

/-!
# Section 5 of [WXMRS23]: multi-shot Byzantine broadcast under dishonest majority — the model

[WXMRS23] J. Wan, Z. Xiang, A. Momose, L. Ren, E. Shi. *On the Amortized Communication Complexity
of Byzantine Broadcast.* PODC 2023.

This file is a lock-step model of Algorithm 5.2 (multi-shot BB, `f < n`), which runs, in every slot,
the simplified TrustCast of Algorithm 5.1 followed by a Dolev–Strong phase on `⟨corrupt, S_k⟩`.

* Nodes: a finite type `N`, `n = Fintype.card N`. A static set `H` of honest nodes; the others are
  Byzantine. The bound `|N \ H| ≤ f` is only needed for consistency (Lemma 5), not for validity.
* Time: global lock-step rounds `r : ℕ`; slot `k` (we index slots from `0`, the paper from `1`)
  consists of the rounds `k T, …, k T + T - 1` with `T = n + f + 3`; `loc r = r % T` is the round
  number inside the slot and `slot r = r / T`. A message multicast in round `r` is received by every
  honest node (including the sender itself) in round `r + 1`.
* Messages are signed atoms (`Msg`): `⟨prop, m, k⟩_{S_k}`, `⟨accuse, v⟩_w`, `⟨corrupt, v⟩_w`.
  Signatures are ideal: the adversary may deliver to an honest node, in round `r`, any atom signed by
  a Byzantine node, and an atom signed by an honest node only if some honest node multicast it in a
  round `< r` (rushing, eavesdropping adversary) — `AdvValid`.
* Honest state (`State`): the cumulative set `know` of received atoms, the trust graph `G`
  (a `SimpleGraph N`; the trust graph `G_u` of the paper is the connected component of `u` in `G`,
  so "remove all vertices unconnected with `u`" is implicit), and the set `out` of atoms multicast
  in the current round. States are computed from the adversary's deliveries (`cfg`).
* The trust graph is shared by all slots (Algorithm 5.2: "each node uses the same trust graph across
  all slots").

## The reading parameter

Algorithm 5.2 invokes `TrustCast(G_u, n, k)`, i.e. the TrustCast rules run in rounds `1..n` of the
slot only. Read literally, accusations and equivocation evidence arriving later are never processed
in that slot, and equivocation evidence for slot `k` is never processed after slot `k`.
`Reading` makes this explicit: `maint t` says in which in-slot rounds the graph-maintenance rules
(process and forward accusations, detect and forward equivocations, remove vertices) run, and
`eqSlot j k` which slots' equivocation evidence is considered during slot `k`.

* `Reading.charitable`: graph maintenance in every round, equivocation evidence of every slot.
  The correctness proofs are for this reading.
* `Reading.literal n`: graph maintenance only in rounds `1..n` of the slot, only evidence of the
  current slot (the text of Algorithms 5.1/5.2).

Prop forwarding and accusing by distance always run in rounds `1..n` only, as in the paper.
-/

namespace Podc.AmortizedByzantineBroadcast.DishonestMajority

open SimpleGraph

/-- Signed atoms of Algorithm 5.2. -/
inductive Msg (N V : Type*) where
  /-- `⟨prop, m, k⟩_{S_k}`: the proposal `m` of the sender of slot `k` (signed by `S k`). -/
  | prop (m : V) (k : ℕ)
  /-- `⟨accuse, v⟩_w`: `w` accuses `v` (signed by `w`). -/
  | accuse (v w : N)
  /-- `⟨corrupt, v⟩_w`: `w` votes for the corruption of `v` (signed by `w`). -/
  | corrupt (v w : N)

variable {N V : Type*}

/-- The signer of an atom (`S` is the sender schedule). -/
def Msg.signer (S : ℕ → N) : Msg N V → N
  | .prop _ k => S k
  | .accuse _ w => w
  | .corrupt _ w => w

/-- Which in-slot rounds run the graph maintenance, and which slots' equivocation evidence counts. -/
structure Reading where
  /-- Graph maintenance (accusations, equivocations) runs in in-slot round `t` iff `maint t`. -/
  maint : ℕ → Prop
  /-- During slot `k`, two different proposals of slot `j` remove `S_j` iff `eqSlot j k`. -/
  eqSlot : ℕ → ℕ → Prop

/-- Graph maintenance in every round, equivocation evidence of all slots. -/
def Reading.charitable : Reading := ⟨fun _ => True, fun _ _ => True⟩

/-- The literal reading of `TrustCast(G_u, n, k)`: rounds `1..n` of the slot, current slot only. -/
def Reading.literal (n : ℕ) : Reading := ⟨fun t => 1 ≤ t ∧ t ≤ n, fun j k => j = k⟩

/-- Parameters of an execution of Algorithm 5.2. -/
structure Setup (N V : Type*) where
  /-- The resilience parameter (slot length is `n + f + 3`). -/
  f : ℕ
  /-- `S k` is the designated sender of slot `k`. -/
  S : ℕ → N
  /-- `input k` is the message the sender of slot `k` broadcasts (if honest). -/
  input : ℕ → V
  /-- The reading of the TrustCast invocation. -/
  R : Reading

/-- Local state of a node after a round. -/
structure State (N V : Type*) where
  /-- All atoms received so far (cumulative). -/
  know : Set (Msg N V)
  /-- The trust graph (edge set); `G_u` is the component of `u`. -/
  G : SimpleGraph N
  /-- The atoms multicast in this round. -/
  out : Set (Msg N V)

/-- Initial state: nothing known, complete trust graph. -/
def State.init : State N V := ⟨∅, ⊤, ∅⟩

variable [Fintype N] (P : Setup N V)

namespace Setup

/-- Number of nodes. -/
abbrev n (_ : Setup N V) : ℕ := Fintype.card N

/-- Slot length `T = n + f + 3`. -/
def T : ℕ := P.n + P.f + 3

/-- The slot of global round `r`. -/
def slot (r : ℕ) : ℕ := r / P.T

/-- The in-slot round number of global round `r`. -/
def loc (r : ℕ) : ℕ := r % P.T

/-- `u` processes (and forwards) `⟨accuse, a⟩_b` in round `r`, given its graph `G` at the start of
the round and its knowledge `K`: maintenance runs and both endpoints are in `G_u`. -/
def processed (u : N) (r : ℕ) (G : SimpleGraph N) (K : Set (Msg N V)) (a b : N) : Prop :=
  P.R.maint (P.loc r) ∧ Msg.accuse a b ∈ K ∧ G.Reachable u a ∧ G.Reachable u b

/-- Edges removed because of processed accusations. -/
def accEdges (u : N) (r : ℕ) (G : SimpleGraph N) (K : Set (Msg N V)) : Set (Sym2 N) :=
  {e | ∃ a b, P.processed u r G K a b ∧ e = s(a, b)}

/-- In round `r`, knowledge `K` contains two different proposals of slot `j` (and this evidence is
considered). -/
def equivocated (r : ℕ) (K : Set (Msg N V)) (j : ℕ) : Prop :=
  P.R.maint (P.loc r) ∧ P.R.eqSlot j (P.slot r) ∧
    ∃ m m', m ≠ m' ∧ Msg.prop m j ∈ K ∧ Msg.prop m' j ∈ K

/-- Edges removed because of equivocations (all edges at an equivocating sender). -/
def eqEdges (r : ℕ) (K : Set (Msg N V)) : Set (Sym2 N) :=
  {e | ∃ j, P.equivocated r K j ∧ P.S j ∈ e}

/-- The graph after processing accusations (used for accusing by distance). -/
def G1 (u : N) (r : ℕ) (G : SimpleGraph N) (K : Set (Msg N V)) : SimpleGraph N :=
  G.deleteEdges (P.accEdges u r G K)

/-- The graph at the end of the round (after removing equivocators). -/
def G2 (u : N) (r : ℕ) (G : SimpleGraph N) (K : Set (Msg N V)) : SimpleGraph N :=
  (P.G1 u r G K).deleteEdges (P.eqEdges r K)

/-- `K` contains some proposal of slot `k`. -/
def HasProp (K : Set (Msg N V)) (k : ℕ) : Prop := ∃ m, Msg.prop m k ∈ K

/-- Number of distinct signers of `⟨corrupt, v⟩_*` in `K`. -/
noncomputable def nSigners (K : Set (Msg N V)) (v : N) : ℕ := {w | Msg.corrupt v w ∈ K}.ncard

/-- The Dolev–Strong condition for `u` to vote (multicast `⟨corrupt, S_k⟩_u`) in round `r`:
`n + 1 ≤ t ≤ n + f + 2`, `S_k ∉ G_u`, and at least `τ = t - (n + 1)` signers of `⟨corrupt, S_k⟩`
are known (trivial for `τ = 0`). -/
def DsVote (u : N) (r : ℕ) (G : SimpleGraph N) (K : Set (Msg N V)) : Prop :=
  P.n + 1 ≤ P.loc r ∧ P.loc r ≤ P.n + P.f + 2 ∧
    ¬ (P.G2 u r G K).Reachable u (P.S (P.slot r)) ∧
    P.loc r - (P.n + 1) ≤ nSigners K (P.S (P.slot r))

/-- The atoms multicast by honest `u` in round `r` (previous graph `G`, knowledge `K`).
"If not yet sent" clauses are dropped: re-sending an atom has no effect on any node. -/
def outSet (u : N) (r : ℕ) (G : SimpleGraph N) (K : Set (Msg N V)) : Set (Msg N V) :=
  {a |
    -- forward processed accusations
    (∃ x y, a = .accuse x y ∧ P.processed u r G K x y) ∨
    -- forward equivocating proposals
    (∃ m j, a = .prop m j ∧ Msg.prop m j ∈ K ∧ P.equivocated r K j) ∨
    -- the sender proposes in round 0
    (a = .prop (P.input (P.slot r)) (P.slot r) ∧ P.loc r = 0 ∧ u = P.S (P.slot r)) ∨
    -- forward proposals of the current slot (TrustCast rounds `1..n`)
    (∃ m, a = .prop m (P.slot r) ∧ Msg.prop m (P.slot r) ∈ K ∧ 1 ≤ P.loc r ∧ P.loc r ≤ P.n) ∨
    -- accuse by distance (TrustCast rounds `1..n`)
    (∃ x, a = .accuse x u ∧ 1 ≤ P.loc r ∧ P.loc r ≤ P.n ∧ ¬ HasProp K (P.slot r) ∧
      (P.G1 u r G K).Reachable u x ∧ (P.G1 u r G K).edist x (P.S (P.slot r)) < P.loc r) ∨
    -- Dolev–Strong: vote
    (a = .corrupt (P.S (P.slot r)) u ∧ P.DsVote u r G K) ∨
    -- Dolev–Strong: forward the known votes (`τ ≥ 1`)
    (∃ w, a = .corrupt (P.S (P.slot r)) w ∧ Msg.corrupt (P.S (P.slot r)) w ∈ K ∧
      P.DsVote u r G K ∧ P.n + 2 ≤ P.loc r)}

/-- One round of honest node `u`: receive `I`, update the graph, multicast. -/
def step (u : N) (r : ℕ) (s : State N V) (I : Set (Msg N V)) : State N V :=
  ⟨s.know ∪ I, P.G2 u r s.G (s.know ∪ I), P.outSet u r s.G (s.know ∪ I)⟩

/-- The execution: `cfg H adv r u` is the state of `u` after rounds `0..r-1`. In round `r`, node `u`
receives `adv r u` from the Byzantine nodes and everything the honest nodes multicast in round
`r - 1`. (States of Byzantine nodes are computed too, but never used.) -/
def cfg (H : Set N) (adv : ℕ → N → Set (Msg N V)) : ℕ → N → State N V
  | 0 => fun _ => State.init
  | r + 1 => fun u => P.step u r (cfg H adv r u) (adv r u ∪ {a | ∃ w ∈ H, a ∈ (cfg H adv r w).out})

/-- Unforgeability of signatures: an atom signed by an honest node is delivered by the adversary in
round `r` only if some honest node multicast it in an earlier round. -/
def AdvValid (H : Set N) (adv : ℕ → N → Set (Msg N V)) : Prop :=
  ∀ r u a, u ∈ H → a ∈ adv r u → a.signer P.S ∈ H →
    ∃ r' < r, ∃ w ∈ H, a ∈ (P.cfg H adv (r' + 1) w).out

/-- `u` voted for the corruption of `v` (multicast `⟨corrupt, v⟩_u`) in some round `≤ r`. -/
def Voted (H : Set N) (adv : ℕ → N → Set (Msg N V)) (u v : N) (r : ℕ) : Prop :=
  ∃ r' ≤ r, Msg.corrupt v u ∈ (P.cfg H adv (r' + 1) u).out

open Classical in
/-- The value committed by `u` for slot `k` in the last round `k T + n + f + 2` of the slot:
`none` (= `⊥`) if `u` has sent `⟨corrupt, S_k⟩_u`, otherwise a proposal of slot `k` received by the
end of round `n` of the slot (`none` if there is none). -/
noncomputable def commit (H : Set N) (adv : ℕ → N → Set (Msg N V)) (u : N) (k : ℕ) : Option V :=
  if P.Voted H adv u (P.S k) (k * P.T + (P.n + P.f + 2)) then none
  else if h : HasProp (P.cfg H adv (k * P.T + P.n + 1) u).know k then some h.choose else none

end Setup

end Podc.AmortizedByzantineBroadcast.DishonestMajority
