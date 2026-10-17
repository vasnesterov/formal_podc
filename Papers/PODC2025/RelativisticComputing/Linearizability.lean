import Papers.PODC2025.RelativisticComputing.Central
import Cslib.Computability.Distributed.SharedMemory.HerlihyWing.Defs

/-!
# Linearizability, relativistic and computational linearizability (Jayanti, PODC 2025, §5,
Theorem 6.8, Appendix A)

A distributed implementation of a shared object (Definition 5.1) is an algorithm some of whose
events are invocation events `(π, invoke, op)` or response events `(π, respond, op, r)`. The
history of a finite totally ordered execution is the list of its invocation and response events
in order (Definition A.1). Linearizability of a history (Definition A.3) is taken from CSLib:
`Cslib.SharedMemory.HerlihyWing.Linearizable` (Herlihy–Wing linearizability, in the amended form
of Sela–Herlihy–Petrank; a single object, `X = Unit`).

Following Definition A.3, an implementation is linearizable if the history of every *finite*
classical execution is linearizable. We define relativistic (Definition 5.3 / A.4) and
computational (Definition 6.1) linearizability for finite executions as well; see
`differencies.md` for this choice. Theorem 6.8 is then the Central Theorem for the class of finite
executions, which needs no assumption on the number of processors.
-/

namespace RelativisticComputing

open Cslib.SharedMemory.HerlihyWing (SeqSpec History)

variable {Proc Msg Op Res : Type} [DecidableEq Proc]

/-- **Definition 5.1** (distributed implementation of a shared object): an algorithm together with
the labelling of invocation events (`inl op`) and response events (`inr r`). -/
structure Implementation (Proc Msg Op Res : Type) extends Algorithm Proc Msg where
  /-- `label e = some (inl op)`: `e` invokes `op`; `some (inr r)`: `e` responds with `r`. -/
  label : Event → Option (Op ⊕ Res)

/-- The history event of a step, if it is an invocation or a response. -/
def histEvent (I : Implementation Proc Msg Op Res) (s : Step I.toAlgorithm) :
    Option (Cslib.SharedMemory.HerlihyWing.Event Proc Unit Op Res) :=
  (I.label s.ev).map (Sum.elim (fun o => .inv s.proc () o) (fun r => .res s.proc () r))

/-- **Definition A.1** (history of a totally ordered execution): `h` is the list of invocation and
response events of the steps of `S`, listed in `<_S` order. -/
def IsHistoryOf (I : Implementation Proc Msg Op Res) (S : Set (Step I.toAlgorithm))
    (lt : S → S → Prop) (h : History Proc Unit Op Res) : Prop :=
  ∃ l : List S, l.Nodup ∧ (∀ s, s ∈ l) ∧ l.Pairwise lt ∧
    h = l.filterMap (fun s => histEvent I s.1)

omit [DecidableEq Proc] in
/-- Every finite strict total order has a history. -/
lemma exists_isHistoryOf (I : Implementation Proc Msg Op Res) {S : Set (Step I.toAlgorithm)}
    (hS : S.Finite) {lt : S → S → Prop} (hlt : IsSTO lt) : ∃ h, IsHistoryOf I S lt h := by
  classical
  have : Fintype S := hS.fintype
  have : IsStrictTotalOrder S lt := hlt.toMathlib
  let : LinearOrder S := linearOrderOfSTO lt
  let l : List S := (Finset.univ : Finset S).sort (fun a b : S => a ≤ b)
  have hnd : l.Nodup := Finset.sort_nodup _ _
  have hpw : l.Pairwise (fun a b : S => a ≤ b) := Finset.pairwise_sort _ _
  refine ⟨_, l, hnd, fun s => (Finset.mem_sort _).2 (Finset.mem_univ s), ?_, rfl⟩
  exact (hpw.and hnd).imp fun h => lt_of_le_of_ne h.1 h.2

/-- The property "the history is linearizable" of totally ordered executions. -/
def LinProp (I : Implementation Proc Msg Op Res) (spec : SeqSpec Proc Unit Op Res) :
    Property I.toAlgorithm :=
  fun S lt => ∀ h, IsHistoryOf I S lt h → Cslib.SharedMemory.HerlihyWing.Linearizable spec h

/-- Finite executions. -/
def FiniteExecs (A : Algorithm Proc Msg) : Set (Set (Step A)) := {S | S.Finite}

/-- **Definition A.3**: `I` is (classically) linearizable if the history of every finite classical
execution is linearizable. -/
def IsLinearizable (I : Implementation Proc Msg Op Res) (spec : SeqSpec Proc Unit Op Res) : Prop :=
  ClassicallySatisfies I.toAlgorithm (LinProp I spec) (FiniteExecs _)

/-- **Definition 6.1**: `I` is computationally linearizable if every total ordering of every
(finite) computational execution has a linearizable history. -/
def IsCompLinearizable (I : Implementation Proc Msg Op Res) (spec : SeqSpec Proc Unit Op Res) :
    Prop :=
  ComputationallySatisfies I.toAlgorithm (LinProp I spec) (FiniteExecs _)

/-- **Definitions 5.3 / A.4**: `I` is relativistically linearizable if every (finite) relativistic
execution is linearizable in the reference frame of every observer. -/
def IsRelLinearizable (X : Spacetime) (I : Implementation Proc Msg Op Res)
    (spec : SeqSpec Proc Unit Op Res) : Prop :=
  RelativisticallySatisfies X I.toAlgorithm (LinProp I spec) (FiniteExecs _)

/-- **Theorem 6.8 (Equivalence Theorem).** For any distributed implementation `I` of a shared
object, the following are equivalent: (1) `I` is linearizable; (2) `I` is computationally
linearizable; (3) `I` is relativistically linearizable. -/
theorem theorem_6_8 (X : Spacetime) (I : Implementation Proc Msg Op Res)
    (spec : SeqSpec Proc Unit Op Res) :
    (IsLinearizable I spec ↔ IsCompLinearizable I spec) ∧
      (IsCompLinearizable I spec ↔ IsRelLinearizable X I spec) :=
  theorem_6_7_on X _ _ fun _ hS => hS.countable.to_subtype

end RelativisticComputing
