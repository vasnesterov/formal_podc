import Mathlib

/-!
# Specifications: reliable broadcast, CB-broadcast, adopt-commit, eventual agreement

The abstract layer of the formalization (Sections 2–6 of the paper). It follows the paper's
modular structure: each object is specified by properties of what correct processes observe, and
each algorithm (Figures 1–3) is proved to satisfy its specification from the specifications of
the objects it uses. Reliable broadcast (RB) is a primitive, given by its four properties.

* Processes: a finite type `P` with `n = Fintype.card P`; `B : Finset P` is the set of faulty
  (Byzantine) processes of the execution, `B.card ≤ t`, `3t < n`; correct = `∉ B`.
* Time is `ℕ`. Observations are time-indexed: `del i τ j` is the message RB-delivered by `i` from
  `j` by time `τ` (`none`: not yet); `valid i τ` is the set `cb_valid_i` at time `τ`.
* Inputs are `x : P → Option V` (`none`: the process does not invoke the operation); the
  liveness properties assume that every correct process invokes.

Nothing is assumed about faulty processes beyond what the RB properties say about messages
RB-broadcast by them.
-/

namespace MinimalSynchronyBC

open Finset

variable {P V : Type*} [Fintype P] [DecidableEq P]

/-! ### Reliable broadcast (Section 2.2) -/

/-- Delivery trace of one-shot RB instances, one per sender: `D i τ j` is the message
RB-delivered by `i` from `j` by time `τ`. -/
abbrev RBTrace (P V : Type*) := P → ℕ → P → Option V

/-- The RB-broadcast properties, for the messages `bc j` RB-broadcast by correct processes
(`none`: `j` does not RB-broadcast). RB-Unicity is built into the trace (one message per sender;
once delivered, it stays delivered: `mono`). -/
structure RBSpec (B : Finset P) (bc : P → Option V) (D : RBTrace P V) : Prop where
  /-- RB-Unicity: a delivered message is never replaced. -/
  mono : ∀ {i j τ τ' v}, D i τ j = some v → τ ≤ τ' → D i τ' j = some v
  /-- RB-Validity. -/
  validity : ∀ {i j τ v}, i ∉ B → j ∉ B → D i τ j = some v → bc j = some v
  /-- RB-Termination-1. -/
  term1 : ∀ {i j v}, i ∉ B → j ∉ B → bc j = some v → ∃ τ, D i τ j = some v
  /-- RB-Termination-2. -/
  term2 : ∀ {i k j τ v}, i ∉ B → k ∉ B → D i τ j = some v → ∃ τ', D k τ' j = some v

omit [Fintype P] [DecidableEq P] in
/-- Two correct processes never RB-deliver different messages from the same sender. -/
theorem RBSpec.agree {B : Finset P} {bc : P → Option V} {D : RBTrace P V} (h : RBSpec B bc D)
    {i k j : P} {τ τ' : ℕ} {v v' : V} (hi : i ∉ B) (hk : k ∉ B) (h1 : D i τ j = some v)
    (h2 : D k τ' j = some v') : v = v' := by
  obtain ⟨σ, hσ⟩ := h.term2 hi hk h1
  have a := h.mono hσ (le_max_left σ τ')
  have b := h.mono h2 (le_max_right σ τ')
  rw [a] at b
  exact Option.some_injective _ b

/-! ### Feasibility (`m`-valued objects) -/

variable [DecidableEq V]

/-- Some value is input by at least `t + 1` correct processes (the feasibility condition of
CB-broadcast, Section 2.3). -/
def Feasible (t : ℕ) (B : Finset P) (x : P → Option V) : Prop :=
  ∃ v, t + 1 ≤ (univ.filter fun j => j ∉ B ∧ x j = some v).card

/-- The correct processes input at most `m` different values. -/
def MValued (m : ℕ) (B : Finset P) (x : P → Option V) : Prop :=
  ∃ S : Finset V, S.card ≤ m ∧ ∀ j ∉ B, ∀ v, x j = some v → v ∈ S

/-! ### CB-broadcast (Section 2.3) -/

/-- What correct processes observe of a CB-broadcast instance: the set `cb_valid_i` at time
`τ`, and the return of `CB_broadcast()` (time and value; `none`: no return). -/
structure CBObs (P V : Type*) where
  /-- `cb_valid_i` at time `τ`. -/
  valid : P → ℕ → Set V
  /-- Return time and value of `CB_broadcast()`. -/
  ret : P → Option (ℕ × V)

/-- **The CB-broadcast abstraction** (Section 2.3) with inputs `x`. The termination properties
assume that every correct process cb-broadcasts and that the instance is feasible. The sets
`cb_valid` only grow (`mono`; the paper says values "can still be added"). -/
structure CBSpec (t : ℕ) (B : Finset P) (x : P → Option V) (O : CBObs P V) : Prop where
  /-- `cb_valid_i` only grows. -/
  mono : ∀ {i τ τ'}, τ ≤ τ' → O.valid i τ ⊆ O.valid i τ'
  /-- CB-Operation Termination. -/
  op_termination : (∀ j ∉ B, (x j).isSome) → Feasible t B x → ∀ i ∉ B, (O.ret i).isSome
  /-- CB-Operation Validity. -/
  op_validity : ∀ {i τ v}, i ∉ B → O.ret i = some (τ, v) → v ∈ O.valid i τ
  /-- CB-Set Termination. -/
  set_termination : (∀ j ∉ B, (x j).isSome) → Feasible t B x → ∀ i ∉ B, ∃ τ, (O.valid i τ).Nonempty
  /-- CB-Set Validity. -/
  set_validity : ∀ {i τ v}, i ∉ B → v ∈ O.valid i τ → ∃ j ∉ B, x j = some v
  /-- CB-Set Agreement (eventually equal). -/
  set_agreement : ∀ {i k}, i ∉ B → k ∉ B → ∃ T, ∀ τ ≥ T, O.valid i τ = O.valid k τ

/-! ### Adopt-commit (Section 3) -/

/-- Control tags of adopt-commit. -/
inductive Tag where
  | commit
  | adopt
  deriving DecidableEq

/-- **The (Byzantine) adopt-commit object** (Section 3) with inputs `x`, outputs `out`
(`none`: no return). AC-Obligation is stated for the correct processes that invoke the object
(those with `x j = none` do not), which is how Theorem 4 uses it. -/
structure ACSpec (t : ℕ) (B : Finset P) (x : P → Option V) (out : P → Option (Tag × V)) :
    Prop where
  /-- AC-Termination (every correct process invokes, feasibility). -/
  termination : (∀ j ∉ B, (x j).isSome) → Feasible t B x → ∀ i ∉ B, (out i).isSome
  /-- AC-Output domain. -/
  domain : ∀ {i d v}, i ∉ B → out i = some (d, v) → ∃ j ∉ B, x j = some v
  /-- AC-Obligation. -/
  obligation : ∀ {v i d w}, (∀ j ∉ B, x j = none ∨ x j = some v) → i ∉ B →
    out i = some (d, w) → d = .commit ∧ w = v
  /-- AC-Quasi-agreement. -/
  quasi : ∀ {i k v d w}, i ∉ B → k ∉ B → out i = some (.commit, v) → out k = some (d, w) → w = v

/-! ### Eventual agreement (Section 5.1), per round -/

/-- EA-Validity in round `r`, for inputs `x` and returns `ret` of that round: if every correct
process that invokes `EA_propose(r, -)` proposes `v`, no correct process returns another value. -/
def EAValidity (B : Finset P) (x : P → Option V) (ret : P → Option V) : Prop :=
  ∀ v, (∀ j ∉ B, x j = none ∨ x j = some v) → ∀ i ∉ B, ∀ w, ret i = some w → w = v

/-- EA-Termination in round `r`. -/
def EATermination (B : Finset P) (x : P → Option V) (ret : P → Option V) : Prop :=
  (∀ j ∉ B, (x j).isSome) → ∀ i ∉ B, (ret i).isSome

end MinimalSynchronyBC
