import Papers.PODC2020.IntermediateValueLin.Defs

-- CSLib candidate: Cslib/Computability/Distributed/SharedMemory/ (IVL / skeleton linearizations)

/-!
# The batched counter, SWMR registers and step complexity

Rinberg–Keidar, PODC 2020, Section 6.

* `batchedCounter`: the sequential specification of the batched counter of Section 6.1:
  `update v` (`v ≥ 0`, here `v : ℕ`) adds `v` and returns nothing (the dummy `0`), `read` returns
  the sum of all values passed to preceding updates (`0` initially).
* `Impl.SWMR owner`: the implementation uses its base registers as single-writer registers: every
  write access to register `i` is performed by `owner i` (CSLib base objects cannot see their
  caller, so the discipline is a property of the implementation's code).
* `Impl.StepsLE Q b`: every instance of an operation satisfying `Q` performs at most `b`
  base-object accesses (step complexity).
-/

open Cslib.SharedMemory

set_option linter.unusedSectionVars false

namespace Podc.IntermediateValueLin

/-- Operations of the batched counter. -/
inductive BCOp where
  /-- `update(v)`: add `v ≥ 0`. -/
  | update (v : ℕ)
  /-- `read()`: return the current sum. -/
  | read
  deriving DecidableEq

/-- The batched counter (Section 6.1): a `read` returns the sum of all values passed to the
`update` operations preceding it (`0` if there are none); `update` returns nothing (the dummy
response `0`). -/
abbrev batchedCounter : ObjSpec where
  State := ℕ
  Op := BCOp
  Resp := ℕ
  init := 0
  δ s
    | .update v => (s + v, 0)
    | .read => (s, s)

@[simp] lemma batchedCounter_update (s v : ℕ) : batchedCounter.δ s (.update v) = (s + v, 0) := rfl
@[simp] lemma batchedCounter_read (s : ℕ) : batchedCounter.δ s .read = (s, s) := rfl

/-- The value `v` of an update, `0` for a read. -/
def BCOp.val : BCOp → ℕ
  | .update v => v
  | .read => 0

@[simp] lemma BCOp.val_update (v : ℕ) : (BCOp.update v).val = v := rfl
@[simp] lemma BCOp.val_read : BCOp.read.val = 0 := rfl

/-- The state of the batched counter after a sequential history is the sum of its update values.
-/
lemma batchedCounter_runOps (s : ℕ) (os : List BCOp) :
    batchedCounter.runOps s os = s + (os.map BCOp.val).sum := by
  induction os generalizing s with
  | nil => rfl
  | cons o os ih =>
    rw [ObjSpec.runOps_cons, ih]
    cases o <;> simp [Nat.add_assoc]

section Impl

variable {A : ObjSpec} {P L : Type} [DecidableEq P]

/-- The implementation uses its base registers (of values `V`) as *single-writer multi-reader*
registers: only `owner i` ever writes register `i`. -/
def _root_.Cslib.SharedMemory.Impl.SWMR {ι V : Type} [DecidableEq ι] {v₀ : V}
    (I : Impl A (fun _ : ι => register V v₀) P L) (owner : ι → P) : Prop :=
  ∀ p l i o k, I.act p l = .access i o k → ∀ v, o = .write v → owner i = p

/-- Step complexity: every instance of an operation satisfying `Q` performs at most `b`
base-object accesses (`γ` ranges over continuations in which the instance is still pending). -/
def _root_.Cslib.SharedMemory.Impl.StepsLE {ι : Type} [DecidableEq ι] {B : ι → ObjSpec}
    (I : Impl A B P L) (Q : A.Op → Prop) (b : ℕ) : Prop :=
  ∀ α p o γ, Q o → I.Valid (α ++ .inv p o :: γ) → (∀ r, .ret p r ∉ γ) →
    γ.countP (Label.isTauOf p) ≤ b

end Impl

end Podc.IntermediateValueLin
