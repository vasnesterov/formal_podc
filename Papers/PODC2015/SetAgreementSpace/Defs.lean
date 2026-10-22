import Cslib.Computability.Distributed.SharedMemory.Task
import Cslib.Computability.Distributed.SharedMemory.Covering
import Cslib.Computability.Distributed.SharedMemory.FullInfo
import Podc.Computability.Distributed.SharedMemory.MObstructionFree
import Mathlib.Data.Set.Card
import Mathlib.Data.Fintype.Card

/-!
# Set agreement: specifications (Delporte-Gallet, Fauconnier, Kuznetsov, Ruppert, PODC 2015)

Model: CSLib's asynchronous shared-memory model (`Cslib.SharedMemory.Impl`): deterministic
processes, atomic base objects, invocations by the environment, executions are label lists.
The high-level object is `saObj V = taskObj V V`: operation `Propose v`, response the decided value.

* `kSetAgreement P V k` — the one-shot task (validity + `k`-agreement), solved on one-shot
  executions (`Impl.Solves`).
* `inputsAt α i`, `outputsAt α i` — `In_i(α)`, `Out_i(α)` of Section 2.1: the arguments / responses
  of the `i`-th (0-based) `Propose` of every process.
* `Impl.SolvesRepeated k` — repeated `k`-set agreement (validity and `k`-agreement for every
  instance, in every execution).
* `snapObjOpt r X` — an `r`-component atomic snapshot whose components hold `Option X`
  (`none` = `⊥`), initially `⊥` (CSLib's `snapObj` only stores naturals).
* `m`-obstruction-freedom: `Cslib.SharedMemory.Impl.MObstructionFreeOn`
  (`Podc/Computability/Distributed/SharedMemory/MObstructionFree.lean`).
-/

namespace Podc.SetAgreementSpace

open Cslib.SharedMemory

/-- The set-agreement object: operations are proposals, responses are decisions. It is
definitionally `taskObj V V` (`saObj_eq_taskObj`), but reducible, so that `(saObj V).Op` and
`(saObj V).Resp` unfold to `V`. -/
abbrev saObj (V : Type) [Inhabited V] : ObjSpec where
  State := Unit
  Op := V
  Resp := V
  init := ()
  δ _ _ := ((), default)

lemma saObj_eq_taskObj (V : Type) [Inhabited V] : saObj V = taskObj V V := rfl

/-- The one-shot `k`-set agreement task: every output is the input of some process (validity) and
at most `k` different values are output (`k`-agreement). -/
abbrev kSetAgreement (P V : Type) (k : ℕ) : Cslib.SharedMemory.Task P where
  In := V
  Out := V
  Δ ins outs := (∀ p w, outs p = some w → ∃ q, ins q = some w) ∧
    {w | ∃ p, outs p = some w}.encard ≤ k

/-! ### Repeated set agreement -/

section Repeated

variable {P V : Type} [DecidableEq P] [Inhabited V]

/-- `In_i(α)`: the arguments of the `i`-th (0-based) invocation of `Propose` of all processes. -/
def inputsAt (α : List (Label P (saObj V))) (i : ℕ) : Set V := {v | ∃ p, (opsOf α p)[i]? = some v}

/-- `Out_i(α)`: the responses of the `i`-th (0-based) `Propose` of all processes. -/
def outputsAt (α : List (Label P (saObj V))) (i : ℕ) : Set V :=
  {v | ∃ p, (respsOf α p)[i]? = some v}

/-- An algorithm solves **repeated `k`-set agreement** (Section 2.1) if in every execution and for
every instance `i`, `Out_i ⊆ In_i` (validity) and `|Out_i| ≤ k` (`k`-agreement). -/
def _root_.Cslib.SharedMemory.Impl.SolvesRepeated {ι : Type} [DecidableEq ι] {B : ι → ObjSpec}
    {L : Type} (I : Impl (saObj V) B P L) (k : ℕ) : Prop :=
  ∀ α, I.Valid α → ∀ i, outputsAt α i ⊆ inputsAt α i ∧ (outputsAt α i).encard ≤ k

end Repeated

/-! ### Snapshot objects with `⊥` -/

/-- Operations of an `r`-component snapshot over `Option X`. -/
inductive SnapOpOpt (r : ℕ) (X : Type) where
  /-- Write `x` into component `i`. -/
  | update (i : Fin r) (x : X)
  /-- Read all components atomically. -/
  | scan

/-- `r`-component atomic snapshot whose components hold values of `X` or `⊥` (`none`), all
initially `⊥`. `update` returns the current view (ignored by the algorithms). -/
abbrev snapObjOpt (r : ℕ) (X : Type) : ObjSpec where
  State := Fin r → Option X
  Op := SnapOpOpt r X
  Resp := Fin r → Option X
  init := fun _ => none
  δ s
    | .update i x => (Function.update s i (some x), s)
    | .scan => (s, s)

@[simp] lemma snapObjOpt_update (r : ℕ) (X : Type) (s : Fin r → Option X) (i : Fin r) (x : X) :
    (snapObjOpt r X).δ s (.update i x) = (Function.update s i (some x), s) := rfl

@[simp] lemma snapObjOpt_scan (r : ℕ) (X : Type) (s : Fin r → Option X) :
    (snapObjOpt r X).δ s .scan = (s, s) := rfl

end Podc.SetAgreementSpace
