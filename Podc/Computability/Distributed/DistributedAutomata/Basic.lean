import Mathlib

-- CSLib candidate: Cslib/Computability/Distributed/DistributedAutomata/Basic.lean

/-!
# Distributed automata (Esparza–Reiter)

The generic model of *weak* distributed computing of Esparza and Reiter (CONCUR 2020), as used by
Czerner, Guttenberg, Helfrich and Esparza (PODC 2021): every node of a finite, labelled, anonymous
graph runs the same finite-state machine; a selected node updates its state according to its own
state and the number of its neighbours in each state, counted up to a threshold `β`.

* `LGraph Λ`: a finite simple graph with node labels in `Λ`, bundled with its vertex type.
  `LGraph.Admissible k G`: the paper's convention (connected, at least three nodes) plus a degree
  bound `k : ℕ∞` (`k = ⊤`: arbitrary graphs).
* `Machine Λ Q`: counting bound `β ≥ 1`, initialisation `init`, transition function
  `δ : Q → (Q → ℕ) → Q` (only applied to neighbourhood counts cut off at `β`), accepting and
  rejecting states. `Machine.Halting`: accepting/rejecting states are absorbing.
* `step M G C S`: all nodes of the selection `S` move simultaneously; `runFrom`, `runList`.
* `Selection` (liberal / exclusive / synchronous) and `Fairness` (adversarial / pseudo-stochastic);
  `IsFair κ φ σ`: `σ` is a fair schedule (every node selected infinitely often and, for
  pseudo-stochastic fairness, every finite sequence of permitted selections occurs infinitely
  often).
* `Automaton Λ Q`: a machine with a scheduler. `Accepts`, `Consistent k` (the consistency
  condition on admissible graphs), `IsLabelling k` (the decided property is a labelling property).
-/

namespace Cslib.DistributedAutomata

open Set

/-- A finite labelled simple graph, bundled with its vertex type. -/
structure LGraph (Λ : Type*) where
  /-- The nodes. -/
  V : Type
  [finite : Finite V]
  /-- The (undirected, loop-free) edges. -/
  graph : SimpleGraph V
  /-- The labelling. -/
  label : V → Λ

attribute [instance] LGraph.finite

variable {Λ Q : Type*}

namespace LGraph

/-- The label count `L_G`: number of nodes carrying label `ℓ`. -/
noncomputable def count (G : LGraph Λ) (ℓ : Λ) : ℕ := {v | G.label v = ℓ}.ncard

/-- The degree of a node. -/
noncomputable def degree (G : LGraph Λ) (v : G.V) : ℕ := {u | G.graph.Adj v u}.ncard

/-- The paper's convention for input graphs (connected, at least three nodes), together with a
degree bound `k` (`k = ⊤` for arbitrary graphs). -/
structure Admissible (k : ℕ∞) (G : LGraph Λ) : Prop where
  connected : G.graph.Connected
  three_le : 3 ≤ Nat.card G.V
  degree_le : ∀ v, (G.degree v : ℕ∞) ≤ k

end LGraph

/-- A distributed machine with input alphabet `Λ` and states `Q`. The transition function is
applied to neighbourhood counts cut off at the counting bound `β`. -/
structure Machine (Λ Q : Type*) where
  /-- The counting bound. -/
  β : ℕ
  one_le_β : 1 ≤ β
  /-- Initialisation function. -/
  init : Λ → Q
  /-- Neighbourhood transition function. -/
  δ : Q → (Q → ℕ) → Q
  /-- Accepting states. -/
  Y : Set Q
  /-- Rejecting states. -/
  N : Set Q
  disjoint : Disjoint Y N

/-- A halting machine: nodes never leave accepting or rejecting states. -/
def Machine.Halting (M : Machine Λ Q) : Prop := ∀ q, q ∈ M.Y ∪ M.N → ∀ P, M.δ q P = q

section Semantics

variable {V : Type*}

/-- The neighbourhood function `N_v^C`: number of neighbours of `v` in each state, cut off at
`β`. -/
noncomputable def view (β : ℕ) (G : SimpleGraph V) (C : V → Q) (v : V) : Q → ℕ :=
  fun q => min β {u | G.Adj v u ∧ C u = q}.ncard

open Classical in
/-- The successor configuration: the nodes of `S` move simultaneously. -/
noncomputable def step (M : Machine Λ Q) (G : SimpleGraph V) (C : V → Q) (S : Set V) : V → Q :=
  fun v => if v ∈ S then M.δ (C v) (view M.β G C v) else C v

/-- The run from configuration `C` under the schedule `σ`. -/
noncomputable def runFrom (M : Machine Λ Q) (G : SimpleGraph V) (C : V → Q) (σ : ℕ → Set V) :
    ℕ → V → Q
  | 0 => C
  | t + 1 => step M G (runFrom M G C σ t) (σ t)

/-- Executing a finite list of selections. -/
noncomputable def runList (M : Machine Λ Q) (G : SimpleGraph V) (C : V → Q) (l : List (Set V)) :
    V → Q :=
  l.foldl (step M G) C

/-- Eventually, all nodes are forever in states of `Z`. -/
def EventuallyIn (Z : Set Q) (r : ℕ → V → Q) : Prop := ∃ t₀, ∀ t ≥ t₀, ∀ v, r t v ∈ Z

end Semantics

/-- Selection constraints. -/
inductive Selection
  /-- any set of nodes may be selected -/
  | liberal
  /-- exactly one node is selected -/
  | exclusive
  /-- all nodes are selected -/
  | synchronous
  deriving DecidableEq

/-- Permitted selections `s(G)`. -/
def Selection.Permitted {V : Type*} : Selection → Set V → Prop
  | .liberal, _ => True
  | .exclusive, S => ∃ v, S = {v}
  | .synchronous, S => S = univ

/-- Fairness constraints. -/
inductive Fairness
  /-- every node is selected infinitely often -/
  | adversarial
  /-- every finite sequence of permitted selections occurs infinitely often -/
  | pseudoStochastic
  deriving DecidableEq

/-- `σ` is a fair schedule for the scheduler `(κ, φ)`. Every schedule selects every node infinitely
often; pseudo-stochastic schedules contain every finite sequence of permitted selections infinitely
often. -/
def IsFair {V : Type*} (κ : Selection) (φ : Fairness) (σ : ℕ → Set V) : Prop :=
  (∀ t, κ.Permitted (σ t)) ∧ (∀ v N, ∃ t ≥ N, v ∈ σ t) ∧
    (φ = .pseudoStochastic → ∀ w : List (Set V), (∀ S ∈ w, κ.Permitted S) →
      ∀ N, ∃ t ≥ N, ∀ i (h : i < w.length), σ (t + i) = w[i])

/-- A distributed automaton: a machine together with a scheduler. The consistency condition is a
separate predicate (`Automaton.Consistent`), since it depends on the class of input graphs. -/
structure Automaton (Λ Q : Type*) where
  /-- The machine. -/
  M : Machine Λ Q
  /-- The selection constraint. -/
  sel : Selection
  /-- The fairness constraint. -/
  fair : Fairness

namespace Automaton

variable (A : Automaton Λ Q)

/-- The initial configuration on `G`. -/
def init (G : LGraph Λ) : G.V → Q := A.M.init ∘ G.label

/-- The run of `A` on `G` scheduled by `σ`. -/
noncomputable def run (G : LGraph Λ) (σ : ℕ → Set G.V) : ℕ → G.V → Q :=
  runFrom A.M G.graph (A.init G) σ

/-- A fair run of `A` on `G`. -/
def FairSchedule (G : LGraph Λ) (σ : ℕ → Set G.V) : Prop := IsFair A.sel A.fair σ

/-- `A` accepts `G`: some fair run is accepting (stable consensus on `Y`). -/
def Accepts (G : LGraph Λ) : Prop :=
  ∃ σ, A.FairSchedule G σ ∧ EventuallyIn A.M.Y (A.run G σ)

/-- The consistency condition on the admissible graphs of degree at most `k`: either all fair runs
accept or all fair runs reject. -/
def Consistent (k : ℕ∞) : Prop :=
  ∀ G : LGraph Λ, G.Admissible k →
    (∀ σ, A.FairSchedule G σ → EventuallyIn A.M.Y (A.run G σ)) ∨
    (∀ σ, A.FairSchedule G σ → EventuallyIn A.M.N (A.run G σ))

/-- The property decided by `A` (on admissible graphs of degree `≤ k`) is a labelling property. -/
def IsLabelling (k : ℕ∞) : Prop :=
  ∀ G H : LGraph Λ, G.Admissible k → H.Admissible k → G.count = H.count →
    (A.Accepts G ↔ A.Accepts H)

/-- `A` decides the graph property `ϕ` on admissible graphs of degree `≤ k`. -/
def Decides (k : ℕ∞) (ϕ : LGraph Λ → Prop) : Prop :=
  A.Consistent k ∧ ∀ G : LGraph Λ, G.Admissible k → (A.Accepts G ↔ ϕ G)

end Automaton

/-- Cutting off a multiset (a function to `ℕ`) at `K`: `⌈M⌉_K`. -/
def cutoff {α : Type*} (K : ℕ) (f : α → ℕ) : α → ℕ := fun a => min (f a) K

end Cslib.DistributedAutomata
