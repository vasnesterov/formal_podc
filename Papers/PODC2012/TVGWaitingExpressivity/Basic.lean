import Mathlib.Computability.Language
import Mathlib.Computability.DFA
import Mathlib.Computability.RE

/-!
# Time-varying graphs and TVG-automata

Casteigts, Flocchini, Godard, Santoro, Yamashita, *Expressivity of Time-Varying Graphs and the Power
of Waiting in Dynamic Networks* (arXiv:1205.1975v1; brief announcement *Waiting in Dynamic
Networks*, PODC 2012), Section 2.

A time-varying graph `G = (V, E, 𝒯, ρ, ζ)` over the discrete time domain `ℕ`. An edge is a triple
`(u, a, v)` (the paper writes `(u, v, a)`): from `u` to `v` with label `a`. The footprint `E` is
implicit: an edge that is never present plays no role, so we take `E = V × α × V` (finite when
`V` and `Σ` are). The lifetime `𝒯` is also absorbed into `ρ`.

A TVG-automaton additionally has initial states `I`, accepting states `F`, and a start date.
A journey reads a word letter by letter: from node `u` at time `t` it may depart at a time `t₁`
allowed by a *pause rule* `P t t₁` along an edge `e = (u, a, v)` present at `t₁`, arriving at `v`
at time `t₁ + ζ(e, t₁)`:

* no waiting (direct journeys): `t₁ = t`;
* waiting allowed (indirect journeys): `t ≤ t₁`;
* bounded waiting `d`: `t ≤ t₁ ≤ t + d`.
-/

namespace Podc.TVGWaitingExpressivity

/-- A time-varying graph with labelled edges `(u, a, v)` over discrete time `ℕ`:
`present e t` is `ρ(e, t) = 1`, `latency e t` is `ζ(e, t)`. -/
structure TVG (V α : Type*) where
  /-- The presence function `ρ`. -/
  present : V × α × V → ℕ → Prop
  /-- The latency function `ζ`. -/
  latency : V × α × V → ℕ → ℕ

/-- A TVG-automaton `A(G) = (Σ, S = V, I, E, F)`, together with the date at which journeys start. -/
structure TVGAutomaton (V α : Type*) extends TVG V α where
  /-- Initial states `I`. -/
  init : Set V
  /-- Accepting states `F`. -/
  accept : Set V
  /-- The start date of the journeys (`0` in the paper, `1` in its example `G₁`). -/
  start : ℕ := 0

/-- A pause rule: `P t t₁` says that a journey that arrived at a node at time `t` may take its next
edge at time `t₁`. -/
abbrev PauseRule := ℕ → ℕ → Prop

/-- No waiting: direct journeys. -/
def noWait : PauseRule := fun t t₁ => t₁ = t

/-- Unbounded waiting: indirect journeys. -/
def wait : PauseRule := fun t t₁ => t ≤ t₁

/-- Waiting at most `d` time units. -/
def waitAtMost (d : ℕ) : PauseRule := fun t t₁ => t ≤ t₁ ∧ t₁ ≤ t + d

namespace TVG

variable {V α : Type*} (G : TVG V α)

/-- `G.Journey P u t w v t'`: there is a journey with pause rule `P`, labelled by the word `w`,
that is at node `u` at time `t` and arrives at node `v` at time `t'`. -/
inductive Journey (P : PauseRule) : V → ℕ → List α → V → ℕ → Prop
  | nil (u : V) (t : ℕ) : Journey P u t [] u t
  | cons {u : V} {t : ℕ} {a : α} {v : V} {t₁ : ℕ} {w : List α} {x : V} {t' : ℕ} :
      P t t₁ → G.present (u, a, v) t₁ →
      Journey P v (t₁ + G.latency (u, a, v) t₁) w x t' → Journey P u t (a :: w) x t'

end TVG

namespace TVGAutomaton

variable {V α : Type*} (A : TVGAutomaton V α)

/-- The language accepted with pause rule `P`: words labelling a journey from an initial state at
the start date to an accepting state. -/
def lang (P : PauseRule) : Language α :=
  {w | ∃ s ∈ A.init, ∃ f ∈ A.accept, ∃ t', A.Journey P s A.start w f t'}

/-- `L_nowait(G)`: the language accepted by direct journeys. -/
def Lnowait : Language α := A.lang noWait

/-- `L_wait(G)`: the language accepted when journeys may be indirect. -/
def Lwait : Language α := A.lang wait

/-- `L_wait[d](G)`: the language accepted when every pause lasts at most `d` time units. -/
def LwaitAtMost (d : ℕ) : Language α := A.lang (waitAtMost d)

end TVGAutomaton

/-- The family `𝓛_nowait` of languages over `Σ` accepted by finite TVG-automata without waiting. -/
def LnowaitFamily (α : Type) : Set (Language α) :=
  {L | ∃ (V : Type) (_ : Fintype V) (A : TVGAutomaton V α), A.Lnowait = L}

/-- The family `𝓛_wait`. -/
def LwaitFamily (α : Type) : Set (Language α) :=
  {L | ∃ (V : Type) (_ : Fintype V) (A : TVGAutomaton V α), A.Lwait = L}

/-- The family `𝓛_wait[d]`. -/
def LwaitAtMostFamily (α : Type) (d : ℕ) : Set (Language α) :=
  {L | ∃ (V : Type) (_ : Fintype V) (A : TVGAutomaton V α), A.LwaitAtMost d = L}

/-! ### Computable TVGs

The paper requires presence and latency to be "arbitrary computable functions". For the
computability-sensitive statements we take nodes `Fin n` and alphabet `Fin q`. -/

/-- A TVG on `Fin n` over `Fin q` whose presence predicate is decidable by a computable function
and whose latency function is computable. -/
def TVG.IsComputable {n q : ℕ} (G : TVG (Fin n) (Fin q)) : Prop :=
  ComputablePred (fun p : (Fin n × Fin q × Fin n) × ℕ => G.present p.1 p.2) ∧
    Computable (fun p : (Fin n × Fin q × Fin n) × ℕ => G.latency p.1 p.2)

/-- `𝓛_nowait` restricted to computable TVGs. -/
def LnowaitComp (q : ℕ) : Set (Language (Fin q)) :=
  {L | ∃ (n : ℕ) (A : TVGAutomaton (Fin n) (Fin q)), A.IsComputable ∧ A.Lnowait = L}

/-- `𝓛_wait` restricted to computable TVGs. -/
def LwaitComp (q : ℕ) : Set (Language (Fin q)) :=
  {L | ∃ (n : ℕ) (A : TVGAutomaton (Fin n) (Fin q)), A.IsComputable ∧ A.Lwait = L}

/-- `𝓛_wait[d]` restricted to computable TVGs. -/
def LwaitAtMostComp (q d : ℕ) : Set (Language (Fin q)) :=
  {L | ∃ (n : ℕ) (A : TVGAutomaton (Fin n) (Fin q)), A.IsComputable ∧ A.LwaitAtMost d = L}

/-! ### Basic facts -/

namespace TVG

variable {V α : Type*} {G : TVG V α}

theorem Journey.mono {P Q : PauseRule} (hPQ : ∀ t t₁, P t t₁ → Q t t₁) {u t w v t'}
    (h : G.Journey P u t w v t') : G.Journey Q u t w v t' := by
  induction h with
  | nil => exact .nil _ _
  | cons hp hpres _ ih => exact .cons (hPQ _ _ hp) hpres ih

@[simp] theorem journey_nil_iff {P : PauseRule} {u t v t'} :
    G.Journey P u t [] v t' ↔ v = u ∧ t' = t := by
  constructor
  · rintro ⟨⟩; exact ⟨rfl, rfl⟩
  · rintro ⟨rfl, rfl⟩; exact .nil _ _

theorem journey_cons_iff {P : PauseRule} {u t a w x t'} :
    G.Journey P u t (a :: w) x t' ↔ ∃ v t₁, P t t₁ ∧ G.present (u, a, v) t₁ ∧
      G.Journey P v (t₁ + G.latency (u, a, v) t₁) w x t' := by
  constructor
  · rintro (_ | ⟨hp, hpres, h⟩); exact ⟨_, _, hp, hpres, h⟩
  · rintro ⟨v, t₁, hp, hpres, h⟩; exact .cons hp hpres h

end TVG

theorem waitAtMost_zero : waitAtMost 0 = noWait := by
  funext t t₁; simp only [waitAtMost, noWait, Nat.add_zero, eq_iff_iff]; omega

/-- `L_wait[0](G) = L_nowait(G)`. -/
theorem TVGAutomaton.LwaitAtMost_zero {V α : Type*} (A : TVGAutomaton V α) :
    A.LwaitAtMost 0 = A.Lnowait := by
  simp [LwaitAtMost, Lnowait, waitAtMost_zero]

end Podc.TVGWaitingExpressivity
