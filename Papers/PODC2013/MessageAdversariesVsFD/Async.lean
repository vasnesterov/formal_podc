import Papers.PODC2013.MessageAdversariesVsFD.Model
import Podc.Computability.Distributed.MessagePassing.FailureDetectors.Sigma

/-!
# Tasks in `AMP_{n,n-1}[fd : D]`

Raynal–Stainer (PODC 2013), Sections 2.3 and 2.4: asynchronous message passing, where up to
`n - 1` processes may crash, enriched with a failure detector `D`.

We reuse the Chandra–Hadzilacos–Toueg model of `Cslib.FailureDetectors` (reliable, non-FIFO
links; a step receives one message or a time-out, queries the failure detector, changes state and
broadcasts at most one message). For tasks:

* the input of a process is fixed in its initial state (`AlgAMP.init : P → X → S`); the input
  events of the CHT model are not used (input type `Empty`);
* the outputs of a process are the outputs of its steps; the value *computed* by `p` is its first
  output (`AlgAMP.output`, `none` if `p` never outputs);
* `AlgAMP.SolvesAMP D T`: for every valid input vector, every failure pattern with at least one
  correct process (at most `n - 1` crashes), every history of `D` and every admissible run, every
  correct process computes a value, and the computed values are valid (`Task.Valid`).
-/

namespace Podc.MessageAdversariesVsFD

open Cslib.FailureDetectors

variable {P R M X Y S : Type} [DecidableEq P]

/-- An algorithm for tasks in `AMP_{n,n-1}[fd : D]` (failure-detector range `R`, messages `M`,
inputs `X`, outputs `Y`, local states `S`): the initial state of a process depends on its input;
steps are those of the CHT model, without input events. -/
structure AlgAMP (P R M X Y S : Type) where
  /-- Initial state of process `p` with input `v`. -/
  init : P → X → S
  /-- One step of `p` with failure-detector value `d`, in state `s`, consuming the event `e`:
  new state, optional broadcast, outputs. -/
  step : P → R → S → Event P M Empty → S × Option M × List Y

namespace AlgAMP

variable (A : AlgAMP P R M X Y S)

/-- The CHT algorithm run by `A` on the input vector `x`. -/
def toAlg (x : P → X) : Algorithm P R M Empty Y S := ⟨fun p => A.init p (x p), A.step⟩

/-- Process `p` produces an output in run `r` (input vector `x`). -/
def Decided (x : P → X) (r : Run P R Empty) (p : P) : Prop :=
  ∃ t y, (A.toAlg x).Out r p y t

open Classical in
/-- The value computed by `p`: its first output (`none` if `p` never outputs). -/
noncomputable def output (x : P → X) (r : Run P R Empty) (p : P) : Option Y :=
  if h : ∃ t, ∃ y, (A.toAlg x).Out r p y t then ((A.toAlg x).outAt r (Nat.find h)).head?
  else none

/-- `A` solves `T` in `AMP_{n,n-1}[fd : D]` (Section 2.4). -/
def SolvesAMP (D : FailureDetector P R) (T : Task P X Y) : Prop :=
  ∀ x ∈ T.inputs, ∀ r : Run P R Empty, (∃ c, r.F.Correct c) → r.H ∈ D r.F →
    (A.toAlg x).Admissible r →
    (∀ p, r.F.Correct p → A.Decided x r p) ∧ T.Valid x (A.output x r)

variable {A}

/-- A computed value is an output of a step of the process. -/
lemma output_spec {x : P → X} {r : Run P R Empty} {p : P} {y : Y}
    (h : A.output x r p = some y) : ∃ t, (A.toAlg x).Out r p y t := by
  classical
  unfold output at h
  split_ifs at h with hd
  · obtain ⟨y', hy'⟩ := Nat.find_spec hd
    refine ⟨Nat.find hd, hy'.1, ?_⟩
    exact List.mem_of_head? h

/-- The computed value of a process is its first output. -/
lemma output_eq_of_first {x : P → X} {r : Run P R Empty} {p : P} {t : ℕ}
    (ht : ∃ y, (A.toAlg x).Out r p y t) (hfirst : ∀ t' < t, ∀ y, ¬ (A.toAlg x).Out r p y t') :
    A.output x r p = ((A.toAlg x).outAt r t).head? := by
  classical
  have hd : ∃ t, ∃ y, (A.toAlg x).Out r p y t := ⟨t, ht⟩
  have heq : Nat.find hd = t :=
    le_antisymm (Nat.find_min' hd ht)
      (not_lt.1 fun hlt => by
        obtain ⟨y, hy⟩ := Nat.find_spec hd
        exact hfirst _ hlt y hy)
  simp [output, hd, heq]

end AlgAMP

/-- `T` is solvable in `AMP_{n,n-1}[fd : D]`. -/
def SolvableAMP {R : Type} (D : FailureDetector P R) (T : Task P X Y) : Prop :=
  ∃ (M S : Type) (A : AlgAMP P R M X Y S), A.SolvesAMP D T

end Podc.MessageAdversariesVsFD
