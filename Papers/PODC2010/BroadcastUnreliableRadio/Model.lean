import Mathlib

-- CSLib candidate: synchronous dual-graph radio networks (reliable/unreliable links), collision
-- rule CR1, synchronous start, ID-level executions and the broadcast problem.

/-!
# The dual graph radio network model (Sections 2.1 and 3 of the paper)

Kuhn, Lynch, Newport, Oshman, Richa. *Broadcasting in Unreliable Radio Networks.* PODC 2010
(full version: MIT-CSAIL-TR-2010-029).

**Networks.** A dual graph network (`DualGraph V`) has nodes `V`, reliable links `E`, all links
`E' ⊇ E` (both directed relations), and a source `src` from which every node is reachable in `E`.
It is undirected if both relations are symmetric.

**Algorithms.** A deterministic algorithm (`Algorithm I S M`) is a family of automata indexed by
the process identifiers `I`: an initial state `init i b` (`b` says whether the process holds the
broadcast message, i.e. is the source process), a sending function `send : S → Option M` and a
transition `trans : S → Rx M → S` on the value received in a round. The broadcast message itself
is not part of the state: processes treat it as a black box (Section 3).

**Executions.** Processes are placed on nodes by a bijection `π : V ≃ I` (chosen by the adversary).
Rounds are synchronous and all processes start in round 1 (synchronous start). In round `t` every
process `p` with `send (state p) = some m` sends `m`; the message of the process at node `v`
reaches `v` itself, every `E`-out-neighbour of `v`, and an arbitrary further subset of the
`E'`-out-neighbours chosen by the adversary (`Adversary`, `Adversary.Admissible`). The adversary
may base this choice on the round number and on the set of senders; for deterministic algorithms
this is no restriction (an execution is determined by the round, so any history-dependent
adversary coincides with one of this form along its execution).

**Collision rule CR1.** A process reached by no message receives `⊥` (`Rx.silence`), by exactly
one message receives it (`Rx.msg`), and by two or more messages (its own included) receives `⊤`
(`Rx.collision`).

**ID-level executions.** Since an execution only depends on which *processes* a message reaches,
we run algorithms on a `Delivery I` (`D t B j` = processes reached by `j`'s message in round `t`
when the set of sending processes is `B`); a node-level adversary is transported along `π`
(`toDelivery`), and conversely an ID-level delivery is realised by `fromDelivery`.

**Broadcast.** The broadcast message is held initially by the source process. A process becomes
*informed* when it receives (as `Rx.msg`) a message sent by an informed process. This
over-approximates "the broadcast message arrives" (an informed process need not forward the
message), so lower bounds stated with `informed` are at least as strong as the paper's.
-/

namespace Podc.BroadcastUnreliableRadio

open Finset

/-! ## Networks -/

/-- A dual graph network `(G, G')` with a distinguished source (Section 2.1). -/
structure DualGraph (V : Type*) where
  /-- Reliable links `E` (the graph `G`). -/
  E : V → V → Prop
  /-- All links `E'` (the graph `G'`). -/
  E' : V → V → Prop
  le : ∀ u v, E u v → E' u v
  /-- The source node. -/
  src : V
  /-- Every node is reachable from the source in `G`. -/
  reachable : ∀ v, Relation.ReflTransGen E src v

/-- A network is undirected if both `G` and `G'` are symmetric. -/
def DualGraph.Undirected {V : Type*} (N : DualGraph V) : Prop :=
  (∀ u v, N.E u v → N.E v u) ∧ (∀ u v, N.E' u v → N.E' v u)

/-! ## Algorithms and receptions -/

/-- What a process receives in a round: silence `⊥`, collision notification `⊤`, or a message. -/
inductive Rx (M : Type*) where
  | silence
  | collision
  | msg (m : M)
  deriving DecidableEq

/-- A deterministic algorithm: one automaton per process identifier. -/
structure Algorithm (I S M : Type*) where
  /-- Initial state; the flag says whether the process holds the broadcast message (source). -/
  init : I → Bool → S
  /-- The message sent in a round (`none` = listen). -/
  send : S → Option M
  /-- State change on the value received in a round. -/
  trans : S → Rx M → S

/-- ID-level delivery rule: in round `t`, if `B` is the set of sending processes, the message of
`j` reaches the processes `D t B j` (and `j` itself). -/
abbrev Delivery (I : Type*) := ℕ → Finset I → I → Finset I

variable {I S M : Type*} [Fintype I] [DecidableEq I]

namespace Algorithm

variable (A : Algorithm I S M)

/-- The set of processes that send in a configuration. -/
def senders (c : I → S) : Finset I :=
  univ.filter fun j => (A.send (c j)).isSome = true

/-- The processes whose messages reach process `i` in round `t` from configuration `c`. -/
def hearers (D : Delivery I) (t : ℕ) (c : I → S) (i : I) : Finset I :=
  (A.senders c).filter fun j => i ∈ D t (A.senders c) j ∨ i = j

open Classical in
/-- Collision rule CR1: the value received when the messages of the processes `H` reach `p`. -/
noncomputable def rx (c : I → S) (H : Finset I) : Rx M :=
  if h : ∃ j, H = {j} then (A.send (c h.choose)).elim Rx.silence Rx.msg
  else if H = ∅ then Rx.silence else Rx.collision

/-- One synchronous round `t` (state component). -/
noncomputable def step (D : Delivery I) (t : ℕ) (c : I → S) : I → S :=
  fun i => A.trans (c i) (A.rx c (A.hearers D t c i))

/-- The states after `t` rounds, starting from configuration `c₀`; round `t + 1` uses `D (t + 1)`. -/
noncomputable def run (c₀ : I → S) (D : Delivery I) : ℕ → I → S
  | 0 => c₀
  | t + 1 => A.step D (t + 1) (run c₀ D t)

/-- Which processes are informed after `t` rounds, starting from `inf₀`. A process becomes informed
in a round when it receives (`Rx.msg`, i.e. exactly one message reaches it) the message of an
informed process. -/
def informed (c₀ : I → S) (D : Delivery I) (inf₀ : I → Prop) : ℕ → I → Prop
  | 0 => inf₀
  | t + 1 => fun i => informed c₀ D inf₀ t i ∨
      ∃ j, A.hearers D (t + 1) (A.run c₀ D t) i = {j} ∧ informed c₀ D inf₀ t j

/-- Initial configuration: the source process `src` holds the message. -/
def initConf (src : I) : I → S := fun i => A.init i (decide (i = src))

end Algorithm

/-! ## Node-level adversaries -/

/-- A node-level adversary: in round `t`, with set of sending nodes `X`, the message of node `v`
reaches the nodes `R t X v`. -/
abbrev Adversary (V : Type*) := ℕ → Finset V → V → Finset V

/-- The adversary respects the network: every message reaches all `G`-out-neighbours of its
sender and only `G'`-out-neighbours (or the sender itself). -/
def Adversary.Admissible {V : Type*} (N : DualGraph V) (R : Adversary V) : Prop :=
  ∀ t X v w, (N.E v w → w ∈ R t X v) ∧ (w ∈ R t X v → w = v ∨ N.E' v w)

variable {V : Type*} [DecidableEq V]

/-- Transport a node-level adversary to processes along the placement `π`. -/
def toDelivery (π : V ≃ I) (R : Adversary V) : Delivery I :=
  fun t B j => (R t (B.map π.symm.toEmbedding) (π.symm j)).map π.toEmbedding

/-- Realise an ID-level delivery by a node-level adversary for the placement `π`. -/
def fromDelivery (π : V ≃ I) (D : Delivery I) : Adversary V :=
  fun t X v => (D t (X.map π.toEmbedding) (π v)).map π.symm.toEmbedding

omit [Fintype I] in
theorem toDelivery_fromDelivery (π : V ≃ I) (D : Delivery I) :
    toDelivery π (fromDelivery π D) = D := by
  funext t B j
  simp [toDelivery, fromDelivery, Finset.map_map]

omit [Fintype I] in
theorem mem_fromDelivery {π : V ≃ I} {D : Delivery I} {t : ℕ} {X : Finset V} {v w : V} :
    w ∈ fromDelivery π D t X v ↔ π w ∈ D t (X.map π.toEmbedding) (π v) := by
  simp only [fromDelivery, Finset.mem_map_equiv, Equiv.symm_symm]

/-- Admissibility of `fromDelivery π D` when `G'` is complete: it suffices that every message
reaches the images of the `G`-neighbours of its sender. -/
theorem admissible_fromDelivery {N : DualGraph V} (hE' : ∀ u v, u ≠ v → N.E' u v)
    {π : V ≃ I} {D : Delivery I}
    (h : ∀ t B v w, N.E v w → π w ∈ D t B (π v)) : (fromDelivery π D).Admissible N := by
  intro t X v w
  refine ⟨fun hvw => mem_fromDelivery.2 (h _ _ _ _ hvw), fun _ => ?_⟩
  by_cases hvw : w = v
  · exact Or.inl hvw
  · exact Or.inr (hE' _ _ (Ne.symm hvw))

variable [Fintype V]

/-- Whether process `i` is informed after `t` rounds of algorithm `A` on network `N` with placement
`π` and adversary `R`. -/
def informedAt (A : Algorithm I S M) (N : DualGraph V) (π : V ≃ I) (R : Adversary V) (t : ℕ)
    (i : I) : Prop :=
  A.informed (A.initConf (π N.src)) (toDelivery π R) (· = π N.src) t i

/-- The message has arrived at all processes within `k` rounds. -/
def BroadcastWithin (A : Algorithm I S M) (N : DualGraph V) (π : V ≃ I) (R : Adversary V)
    (k : ℕ) : Prop :=
  ∀ i, informedAt A N π R k i

/-- `A` solves broadcast within `k` rounds in `N`: for every placement and admissible adversary
(Section 3). -/
def SolvesWithin (A : Algorithm I S M) (N : DualGraph V) (k : ℕ) : Prop :=
  ∀ (π : V ≃ I) (R : Adversary V), R.Admissible N → BroadcastWithin A N π R k

/-- `N` is `k`-broadcastable (with identifier set `I`): some deterministic algorithm and placement
broadcast within `k` rounds against every admissible adversary, under CR1 and synchronous start
(Section 3). -/
def Broadcastable (N : DualGraph V) (I : Type) [Fintype I] [DecidableEq I] (k : ℕ) : Prop :=
  ∃ (S M : Type) (A : Algorithm I S M) (π : V ≃ I),
    ∀ R : Adversary V, R.Admissible N → BroadcastWithin A N π R k

/-- Probabilistic algorithms are probability distributions over deterministic algorithms
(`A ω` for random choices `ω`; this includes processes with independent private coins). `A`
solves broadcast within `k` rounds with probability `q` against the adversary class `adv` (pairs of
a placement and a node-level adversary) if for every adversary of the class the success event
contains a measurable event of probability at least `q` (Section 3). Using an inner bound makes no
measurability assumption and only makes the lower bound of Theorem 4 stronger. -/
def SolvesWithinWithProb {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    (A : Ω → Algorithm I S M) (N : DualGraph V) (adv : Set ((V ≃ I) × Adversary V)) (k : ℕ)
    (q : ENNReal) : Prop :=
  ∀ p ∈ adv, ∃ T : Set Ω, MeasurableSet T ∧ T ⊆ {ω | BroadcastWithin (A ω) N p.1 p.2 k} ∧
    q ≤ μ T

/-! ## Basic lemmas -/

namespace Algorithm

variable (A : Algorithm I S M)

theorem rx_singleton (c : I → S) (j : I) :
    A.rx c {j} = (A.send (c j)).elim Rx.silence Rx.msg := by
  have h : ∃ k, ({j} : Finset I) = {k} := ⟨j, rfl⟩
  have hc : h.choose = j := (Finset.singleton_inj.1 h.choose_spec).symm
  simp only [rx, dite_cond_eq_true (eq_true h), hc]

theorem rx_empty (c : I → S) : A.rx c (∅ : Finset I) = Rx.silence := by
  have h : ¬ ∃ k, (∅ : Finset I) = {k} := fun ⟨k, hk⟩ => by simp at hk
  simp [rx, h]

theorem rx_of_one_lt_card (c : I → S) {H : Finset I} (hH : 1 < H.card) :
    A.rx c H = Rx.collision := by
  have h : ¬ ∃ k, H = {k} := fun ⟨k, hk⟩ => by simp [hk] at hH
  have h' : H ≠ ∅ := fun h => by simp [h] at hH
  simp [rx, h, h']

/-- The reception only depends on the hearer set and on the states of its members. -/
theorem rx_congr {c c' : I → S} {H : Finset I} (h : ∀ j ∈ H, c j = c' j) :
    A.rx c H = A.rx c' H := by
  rcases Finset.eq_empty_or_nonempty H with rfl | hne
  · simp [rx_empty]
  rcases Nat.lt_or_ge 1 H.card with h1 | h1
  · simp [rx_of_one_lt_card _ _ h1]
  · obtain ⟨j, rfl⟩ : ∃ j, H = {j} := Finset.card_eq_one.1 (by
      have := hne.card_pos; omega)
    simp [rx_singleton, h j (by simp)]

theorem run_zero (c₀ : I → S) (D : Delivery I) : A.run c₀ D 0 = c₀ := rfl

theorem run_succ (c₀ : I → S) (D : Delivery I) (t : ℕ) :
    A.run c₀ D (t + 1) = A.step D (t + 1) (A.run c₀ D t) := rfl

omit [DecidableEq I] in
theorem mem_senders {c : I → S} {j : I} : j ∈ A.senders c ↔ (A.send (c j)).isSome = true := by
  simp [senders]

theorem mem_hearers {D : Delivery I} {t : ℕ} {c : I → S} {i j : I} :
    j ∈ A.hearers D t c i ↔ j ∈ A.senders c ∧ (i ∈ D t (A.senders c) j ∨ i = j) := by
  simp [hearers]

theorem hearers_subset (D : Delivery I) (t : ℕ) (c : I → S) (i : I) :
    A.hearers D t c i ⊆ A.senders c := Finset.filter_subset _ _

/-- If every message reaches everybody, every process hears exactly the senders. -/
theorem hearers_eq_senders {D : Delivery I} {t : ℕ} {c : I → S} {i : I}
    (h : ∀ j ∈ A.senders c, i ∈ D t (A.senders c) j) : A.hearers D t c i = A.senders c := by
  ext j
  simp only [mem_hearers]
  exact ⟨fun h => h.1, fun hj => ⟨hj, Or.inl (h j hj)⟩⟩

/-- A round only depends on the delivery rule for the messages actually sent. -/
theorem step_congr {D D' : Delivery I} {t : ℕ} {c : I → S}
    (h : ∀ x ∈ A.senders c, D t (A.senders c) x = D' t (A.senders c) x) :
    A.step D t c = A.step D' t c := by
  have hH : ∀ i, A.hearers D t c i = A.hearers D' t c i := by
    intro i
    ext j
    simp only [mem_hearers]
    constructor
    · rintro ⟨hj, h'⟩; exact ⟨hj, by rwa [← h j hj]⟩
    · rintro ⟨hj, h'⟩; exact ⟨hj, by rwa [h j hj]⟩
  funext i
  simp only [step, hH]

/-- Executions only depend on the delivery rule of the rounds played so far. -/
theorem run_congr {c₀ : I → S} {D D' : Delivery I} {T : ℕ}
    (h : ∀ t, 1 ≤ t → t ≤ T → D t = D' t) :
    ∀ t, t ≤ T → A.run c₀ D t = A.run c₀ D' t
  | 0, _ => rfl
  | t + 1, ht => by
    rw [run_succ, run_succ, run_congr h t (by omega)]
    funext i
    simp only [step, hearers, h (t + 1) (by omega) ht]

theorem informed_congr {c₀ : I → S} {D D' : Delivery I} {inf₀ : I → Prop} {T : ℕ}
    (h : ∀ t, 1 ≤ t → t ≤ T → D t = D' t) :
    ∀ t, t ≤ T → A.informed c₀ D inf₀ t = A.informed c₀ D' inf₀ t
  | 0, _ => rfl
  | t + 1, ht => by
    funext i
    simp only [informed, hearers]
    rw [informed_congr h t (by omega), run_congr A h t (by omega), h (t + 1) (by omega) ht]

/-- Running `t + r` rounds is running `r` rounds from the configuration after `t` rounds. -/
theorem run_add (c₀ : I → S) (D : Delivery I) (t : ℕ) :
    ∀ r, A.run c₀ D (t + r) = A.run (A.run c₀ D t) (fun u => D (t + u)) r
  | 0 => rfl
  | r + 1 => by
    rw [← add_assoc, run_succ, run_succ, run_add c₀ D t r]
    rfl

theorem informed_add (c₀ : I → S) (D : Delivery I) (inf₀ : I → Prop) (t : ℕ) :
    ∀ r, A.informed c₀ D inf₀ (t + r) =
      A.informed (A.run c₀ D t) (fun u => D (t + u)) (A.informed c₀ D inf₀ t) r
  | 0 => rfl
  | r + 1 => by
    funext i
    rw [← add_assoc]
    simp only [informed]
    rw [informed_add c₀ D inf₀ t r, run_add]
    rfl

theorem informed_mono (c₀ : I → S) (D : Delivery I) (inf₀ : I → Prop) {t t' : ℕ} (h : t ≤ t')
    {i : I} (hi : A.informed c₀ D inf₀ t i) : A.informed c₀ D inf₀ t' i := by
  induction h with
  | refl => exact hi
  | step _ ih => exact Or.inl ih

/-- Invariant principle for informed sets: if `P` holds initially and is preserved by every
reception of a single message from an informed (`P`) process, it holds forever. -/
theorem informed_of_invariant (c₀ : I → S) (D : Delivery I) (inf₀ : I → Prop) (P : ℕ → I → Prop)
    (h0 : ∀ i, inf₀ i → P 0 i) (hmono : ∀ t i, P t i → P (t + 1) i)
    (hstep : ∀ t i j, (∀ k, A.informed c₀ D inf₀ t k → P t k) →
      A.hearers D (t + 1) (A.run c₀ D t) i = {j} → P t j → P (t + 1) i) :
    ∀ t i, A.informed c₀ D inf₀ t i → P t i
  | 0, i, hi => h0 i hi
  | t + 1, i, hi => by
    rcases hi with hi | ⟨j, hj, hjinf⟩
    · exact hmono _ _ (informed_of_invariant c₀ D inf₀ P h0 hmono hstep t i hi)
    · exact hstep t i j (informed_of_invariant c₀ D inf₀ P h0 hmono hstep t) hj
        (informed_of_invariant c₀ D inf₀ P h0 hmono hstep t j hjinf)

end Algorithm

end Podc.BroadcastUnreliableRadio
