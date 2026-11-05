import Mathlib
import Cslib.Computability.Distributed.DynamicNetworks.HeardOf
import Cslib.Computability.Distributed.DynamicNetworks.Journey

/-!
# Synchronous round-based systems weakened by a message adversary

Raynal–Stainer, *Synchrony Weakened by Message Adversaries vs Asynchrony Restricted by Failure
Detectors* (PODC 2013; full version: IRISA PI 2002, hal-00787978), Section 2.

`SMP_n[adv : AD]`: `n` reliable processes execute synchronous rounds; in every round every process
sends a message to every process, and the adversary `AD` suppresses some of them. The graph of
round `r` is `G^r` (edge `j → i` iff the message of `p_j` to `p_i` is not suppressed). We use
CSLib's heard-of model: a communication pattern is `p : ℕ → Graph P` (`p t` is the graph of round
`t + 1`, `p t j i` means that `i` receives the message of `j`; every process receives its own
message), and an adversary is the set of patterns it may produce. Algorithms are deterministic
full-information algorithms (`Cslib.HeardOf.StepFn`): this is no loss of generality for
solvability, since a process that receives the whole state of `p_j` can compute the message `p_j`
sent to it.

* Adversary properties: `TOUR`, `SOURCE`, `QUORUM`, `TP`, `SOURCEtp`, `PAIRS`, `SOURCEpairs`;
  `advInf` is `SMP_n[adv : ∞]`.
* `InfReach p i j` is the paper's `i ⇝∞ j` (Section 2.2) and `SC p` its set of strongly correct
  processes (the unique strongly connected component of `⇝∞` without input edge, or `∅`).
* Tasks (Section 2.4) and two solvability notions:
  - `Alg.Solves`: every process computes an output (the paper's definition: processes of
    `SMP_n[adv : AD]` never crash, and "if no value is computed by `p_j`, it is because `p_j` has
    crashed");
  - `Alg.SolvesSC`: only strongly correct processes are required to output (the reading the
    proofs of Lemmas 2, 4 and 6 use, where weakly correct processes simulate crashed ones).
-/

namespace Podc.MessageAdversariesVsFD

open Cslib.HeardOf (Graph Hears StepFn conf)
open Cslib.DynNet (Journey)
open Relation

variable {P X Y : Type}

/-! ## Message adversaries -/

/-- A message adversary, given by the set of communication patterns it may produce (`p t` is the
graph `G^{t+1}` of round `t + 1`). Several properties constrain an adversary by intersection. -/
abbrev Adversary (P : Type) := Set (ℕ → Graph P)

/-- `SMP_n[adv : ∞]`: the adversary may suppress any set of messages. -/
def advInf : Adversary P := Set.univ

/-- `SMP_n[adv : ∅]`: no message is ever suppressed. -/
def advNone : Adversary P := {p | ∀ t i j, p t i j}

/-- Property TOUR (Afek–Gafni): in every round, for every pair of processes, at least one of the
two messages they send each other is not suppressed. -/
def TOUR : Adversary P := {p | ∀ t i j, i ≠ j → p t i j ∨ p t j i}

/-- Property SOURCE (Section 3.1): there are a process `s` and a round `r₀` from which no message
of `s` is suppressed. -/
def SOURCE : Adversary P := {p | ∃ s r₀, ∀ t ≥ r₀, ∀ i, Hears (p t) i s}

/-- Property TP (Appendix A.1): in every round, for every pair `i, j`, there is a directed path
from `i` to `j` or from `j` to `i` in the graph of that round. -/
def TP : Adversary P := {p | ∀ t i j, ReflTransGen (p t) i j ∨ ReflTransGen (p t) j i}

/-- Property SOURCE_tp (Appendix A.2): from some round on, some process `s` has a directed path
to every process in the graph of every round. -/
def SOURCEtp : Adversary P := {p | ∃ s r₀, ∀ t ≥ r₀, ∀ i, ReflTransGen (p t) s i}

/-- Property PAIRS (Appendix A.1), for a schedule `pair t` of the pair of processes associated with
round `t + 1` (the paper's `σ(r mod C(n,2))`): in round `t + 1` the only messages between distinct
processes that may survive are those exchanged by the pair `pair t`, and at least one of them
survives. -/
def PAIRS (pair : ℕ → Sym2 P) : Adversary P :=
  {p | ∀ t i j, i ≠ j → ((p t i j ∨ p t j i) ↔ pair t = s(i, j))}

/-- Property SOURCE_pairs (Appendix A.2): from some round on, the messages of some process `s` are
not suppressed in the rounds associated with a pair containing `s`. -/
def SOURCEpairs (pair : ℕ → Sym2 P) : Adversary P :=
  {p | ∃ s r₀, ∀ t ≥ r₀, ∀ i, i ≠ s → pair t = s(s, i) → p t s i}

/-! ## Strongly and weakly correct processes (Section 2.2) -/

/-- `i ⇝≥r j`: a directed path in the dynamically defined sequence of message graphs starting at a
round `≥ r` (round `r + 1` in the paper's numbering) leads from `p_i` to `p_j`. Journeys may wait,
so starting at round `r` is no restriction. -/
def ReachFrom (p : ℕ → Graph P) (r : ℕ) (i j : P) : Prop := ∃ t, Journey p r i t j

/-- `i ⇝∞ j`: whatever `r`, there is eventually a path from `p_i` starting at a round `≥ r` and
finishing at `p_j`. -/
def InfReach (p : ℕ → Graph P) (i j : P) : Prop := ∀ r, ReachFrom p r i j

/-- `X` is a strongly connected component of the graph `⇝∞` without input edge. -/
def IsSourceComp (p : ℕ → Graph P) (X : Set P) : Prop :=
  X.Nonempty ∧ (∀ x ∈ X, ∀ y, y ∈ X ↔ InfReach p x y ∧ InfReach p y x) ∧
    ∀ x ∈ X, ∀ y, InfReach p y x → y ∈ X

/-- The strongly correct processes `SC`: the processes of the strongly connected component `X` of
`⇝∞` without input edge, if it is unique; `∅` otherwise (then all processes are weakly
correct). -/
def SC (p : ℕ → Graph P) : Set P :=
  {i | ∃ X, IsSourceComp p X ∧ i ∈ X ∧ ∀ Y, IsSourceComp p Y → Y = X}

/-- Property QUORUM (Section 5.1): any two processes, at any two rounds, receive the message of a
common process (intersection), and the set of strongly correct processes is not empty
(liveness). -/
def QUORUM : Adversary P :=
  {p | (∀ i j t t', ∃ k, Hears (p t) i k ∧ Hears (p t') j k) ∧ (SC p).Nonempty}

/-! ## Tasks and algorithms -/

/-- A task (Section 2.4): a set of valid input vectors and, for each of them, the set `Δ I` of
valid output vectors. -/
structure Task (P X Y : Type) where
  /-- Valid input vectors. -/
  inputs : Set (P → X)
  /-- Valid output vectors for each input vector. -/
  Δ : (P → X) → Set (P → Y)

/-- The values computed by the processes (`none`: no value computed) are valid for the input
vector `x`: they extend to an output vector `O ∈ Δ(x)`. -/
def Task.Valid (T : Task P X Y) (x : P → X) (o : P → Option Y) : Prop :=
  ∃ O ∈ T.Δ x, ∀ i y, o i = some y → O i = y

/-- A task is local if every process can compute its output from its own input only. -/
def Task.IsLocal (T : Task P X Y) : Prop :=
  ∃ f : P → X → Option Y, ∀ x ∈ T.inputs, ∃ O ∈ T.Δ x, ∀ i, f i (x i) = some (O i)

/-- A deterministic full-information synchronous algorithm with inputs `X`, outputs `Y` and local
states `σ`: initial state from the input, transition function (the process receives the states of
the processes it hears, `none` for the others) and output function (`none`: no output yet). The
output of a process is the first value its output function takes (outputs are write-once). -/
structure Alg (P X Y σ : Type) where
  /-- Initial state of process `i` with input `v`. -/
  init : P → X → σ
  /-- Transition function. -/
  step : StepFn P σ
  /-- Output function. -/
  out : σ → Option Y

namespace Alg

variable {σ : Type} (A : Alg P X Y σ)

/-- The configuration after `t` rounds of pattern `p` with input vector `x`. -/
noncomputable def run (x : P → X) (p : ℕ → Graph P) (t : ℕ) : P → σ :=
  conf A.step (fun i => A.init i (x i)) p t

/-- Process `i` computes an output at some round. -/
def Decided (x : P → X) (p : ℕ → Graph P) (i : P) : Prop :=
  ∃ t, (A.out (A.run x p t i)).isSome

open Classical in
/-- The value computed by `i` (the first output), `none` if `i` never outputs. -/
noncomputable def output (x : P → X) (p : ℕ → Graph P) (i : P) : Option Y :=
  if h : A.Decided x p i then A.out (A.run x p (Nat.find h) i) else none

/-- `A` solves `T` in `SMP_n[adv : Adv]` in the sense of Section 2.4: in every run, every
(reliable) process computes an output, and the outputs are valid. -/
def Solves (Adv : Adversary P) (T : Task P X Y) : Prop :=
  ∀ x ∈ T.inputs, ∀ p ∈ Adv, (∀ i, A.Decided x p i) ∧ T.Valid x (A.output x p)

/-- Weaker notion: only the strongly correct processes are required to compute an output; the
computed outputs must be valid. -/
def SolvesSC (Adv : Adversary P) (T : Task P X Y) : Prop :=
  ∀ x ∈ T.inputs, ∀ p ∈ Adv, (∀ i ∈ SC p, A.Decided x p i) ∧ T.Valid x (A.output x p)

end Alg

/-- `T` is solvable in `SMP_n[adv : Adv]` (Section 2.4: every process outputs). -/
def Solvable (Adv : Adversary P) (T : Task P X Y) : Prop :=
  ∃ (σ : Type) (A : Alg P X Y σ), A.Solves Adv T

/-- `T` is solvable in `SMP_n[adv : Adv]` when only strongly correct processes must output. -/
def SolvableSC (Adv : Adversary P) (T : Task P X Y) : Prop :=
  ∃ (σ : Type) (A : Alg P X Y σ), A.SolvesSC Adv T

/-- A weaker adversary (fewer patterns) gives a stronger model. -/
theorem Solvable.mono {Adv Adv' : Adversary P} {T : Task P X Y} (h : Adv' ⊆ Adv)
    (hs : Solvable Adv T) : Solvable Adv' T := by
  obtain ⟨σ, A, hA⟩ := hs
  exact ⟨σ, A, fun x hx p hp => hA x hx p (h hp)⟩

/-- A weaker adversary (fewer patterns) gives a stronger model. -/
theorem SolvableSC.mono {Adv Adv' : Adversary P} {T : Task P X Y} (h : Adv' ⊆ Adv)
    (hs : SolvableSC Adv T) : SolvableSC Adv' T := by
  obtain ⟨σ, A, hA⟩ := hs
  exact ⟨σ, A, fun x hx p hp => hA x hx p (h hp)⟩

end Podc.MessageAdversariesVsFD
