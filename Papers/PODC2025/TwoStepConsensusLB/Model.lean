import Mathlib
import Cslib.Computability.Distributed.CrashPartialSync.Consensus

/-!
# Two-step protocols (Ryabinin–Gotsman–Sutra, PODC 2025, Definitions 3–5)

The model of §2 of the paper — `n = Fintype.card P` deterministic crash-prone processes
communicating over point-to-point links in the partially synchronous model of Dwork, Lynch and
Stockmeyer, with one time unit being the message-delay bound `Δ` (*round `k`* of the paper is
the time step `τ = k - 1`) — lives in CSLib: `Cslib.CrashPartialSync` (`Protocol`, `Run`,
`Run.st`, `Run.inbox`, `Run.Valid`, `Run.DecidesAt`, `Run.RespondsAt`, `Run.WellFormed`,
`IsOrder`, the `E`-faulty synchronous runs `syncRun` of **Definition 2**, in
`Cslib/Computability/Distributed/CrashPartialSync/Model.lean`) and the consensus
specifications `taskInv`, `SolvesTask`, `SolvesObject` (§2 and §A, in `…/Consensus.lean`).

Since the delivery order inside a time step is chosen by the adversary, the paper's "there exists
an `E`-faulty synchronous run" quantifies over this order (the paper's model has instantaneous
local computation, so simultaneous deliveries happen in some order).

This file contains the paper's notion of two-step runs and `e`-two-step protocols
(Definitions 3–5).
-/

set_option linter.unusedSectionVars false

namespace TwoStepConsensus

open _root_.Cslib.CrashPartialSync Finset

variable {P V M S : Type*} [Fintype P] [DecidableEq P]

/-! ### Two-step protocols -/

/-- **Definition 3** (task version): the run is *two-step for `p`*: `p` decides by time `2Δ`, i.e.
in its state after the step at time `2`. -/
def _root_.Cslib.CrashPartialSync.Run.DecidedBy2 (A : Protocol P V M S) (R : Run P V M) (p : P) :
    Prop :=
  ∃ τ ≤ 3, ∃ v, R.DecidesAt A p τ v

/-- **Definition 3** (object version): `p` returns by time `2Δ`. -/
def _root_.Cslib.CrashPartialSync.Run.RespondedBy2 (A : Protocol P V M S) (R : Run P V M)
    (p : P) : Prop :=
  ∃ τ ≤ 3, ∃ v, R.RespondsAt A p τ v

/-- **Definition 4** (`e`-two-step consensus task). For every `E` with `|E| = e`:
(1) from every initial configuration some `E`-faulty synchronous run is two-step for some
process; (2) from every initial configuration in which the processes outside `E` propose the same
value, for every `p ∉ E` some `E`-faulty synchronous run is two-step for `p`. -/
def TwoStepTask (A : Protocol P V M S) (e : ℕ) : Prop :=
  ∀ E : Finset P, E.card = e →
    (∀ I : P → V, ∃ ord, IsOrder ord ∧ ∃ p, (syncRun (M := M) E (taskInv I) ord).DecidedBy2 A p) ∧
    (∀ I : P → V, (∀ p ∉ E, ∀ q ∉ E, I p = I q) →
      ∀ p ∉ E, ∃ ord, IsOrder ord ∧ (syncRun (M := M) E (taskInv I) ord).DecidedBy2 A p)

/-- Only `p` calls `propose(v)`, at time `t₀`. -/
def singleInv (p : P) (t₀ : ℕ) (v : V) : P → ℕ → Option V :=
  fun q τ => if q = p ∧ τ = t₀ then some v else none

/-- All processes outside `E` call `propose(v)` at the beginning of the first round. -/
def allInv (E : Finset P) (v : V) : P → ℕ → Option V :=
  fun q τ => if τ = 0 ∧ q ∉ E then some v else none

/-- **Definition 5** (`e`-two-step consensus object, §A). For every `E` with `|E| = e`, every value
`v` and every `p ∉ E`: (1) some `E`-faulty synchronous run in which only `p` calls `propose(v)`
is two-step for `p`; (2) some `E`-faulty synchronous run in which all processes outside `E` call
`propose(v)` at the beginning is two-step for `p`. (The paper does not say when `p` calls
`propose` in (1); we allow any time.) -/
def TwoStepObject (A : Protocol P V M S) (e : ℕ) : Prop :=
  ∀ E : Finset P, E.card = e →
    (∀ (v : V), ∀ p ∉ E, ∃ t₀ ord, IsOrder ord ∧
      (syncRun (M := M) E (singleInv p t₀ v) ord).RespondedBy2 A p) ∧
    (∀ (v : V), ∀ p ∉ E, ∃ ord, IsOrder ord ∧
      (syncRun (M := M) E (allInv E v) ord).RespondedBy2 A p)

end TwoStepConsensus
