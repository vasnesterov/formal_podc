import Cslib.Computability.Distributed.SharedMemory.Progress
import Cslib.Computability.Distributed.SharedMemory.Indist
import Cslib.Computability.Distributed.SharedMemory.Covering
import Cslib.Computability.Distributed.SharedMemory.Linearization

/-!
# Scannable binary objects (Ovens, PODC 2021): definitions

* `BitObj` — an arbitrary 1-bit object (value `Bool`, arbitrary invocations and responses, given
  by a deterministic sequential specification); `BitObj.NonMonotonic` (some invocation changes the
  value from 0 to 1 and some invocation changes it from 1 to 0).
* `scannable O` — the scannable binary object `[O 0, …, O (k-1)]`: `update i o` applies `o` to
  component `i` and returns its response, `scan` returns the vector of all values. Initially all
  components are `0` (`false`).
* `SingleUpdater p₀` — the single-updater discipline: `p₀` performs `update`s, every other process
  performs `scan`s.
* `OneBit S` — a base-object type has at most two states.
* `valAt`, `Absent` — value of the object after `p₀`'s first `i` operations and the paper's
  `𝒱`-absent executions.
* `Lim A k' β` — `β` contains only steps of processes in `A`, single-updater invocations, and
  updates only on components `< k'`.
-/

set_option linter.unusedSectionVars false

namespace Cslib.SharedMemory.Scannable

open Cslib.SharedMemory

/-- An arbitrary 1-bit object: value `Bool`, invocations `Op`, responses `Resp`. -/
structure BitObj where
  /-- Invocations. -/
  Op : Type
  /-- Responses. -/
  Resp : Type
  /-- Sequential specification: new value and response. -/
  δ : Bool → Op → Bool × Resp

/-- A 1-bit object is *non-monotonic* if some invocation changes its value from 0 to 1 and some
invocation changes its value from 1 to 0. -/
def BitObj.NonMonotonic (O : BitObj) : Prop :=
  (∃ o, (O.δ false o).1 = true) ∧ (∃ o, (O.δ true o).1 = false)

/-- The 1-bit object as an `ObjSpec` with initial value `0`. -/
abbrev BitObj.spec (O : BitObj) : ObjSpec where
  State := Bool
  Op := O.Op
  Resp := O.Resp
  init := false
  δ := O.δ

variable {k : ℕ}

/-- Operations of a scannable object. -/
inductive ScanOp (O : Fin k → BitObj) where
  /-- Instantaneous read of all components. -/
  | scan
  /-- Apply invocation `o` to component `i`. -/
  | update (i : Fin k) (o : (O i).Op)

/-- Responses of a scannable object. -/
inductive ScanResp (O : Fin k → BitObj) where
  /-- Response of a `scan`. -/
  | view (v : Fin k → Bool)
  /-- Response of an `update i o`. -/
  | resp (i : Fin k) (r : (O i).Resp)

/-- The scannable binary object `[O 0, …, O (k-1)]`, all components initially `0`. -/
abbrev scannable (O : Fin k → BitObj) : ObjSpec where
  State := Fin k → Bool
  Op := ScanOp O
  Resp := ScanResp O
  init := fun _ => false
  δ v
    | .scan => (v, .view v)
    | .update i o => (Function.update v i ((O i).δ (v i) o).1, .resp i ((O i).δ (v i) o).2)

variable {O : Fin k → BitObj} {P : Type} [DecidableEq P]

/-- The single-updater discipline: `p₀` is the only updater, all other processes only scan. -/
def SingleUpdater (p₀ p : P) : ScanOp O → Prop
  | .scan => p ≠ p₀
  | .update _ _ => p = p₀

/-- The states of a base object fit in one bit. -/
def OneBit (S : Type) : Prop := ∃ f : S → Bool, Function.Injective f

lemma OneBit.eq_of_ne {S : Type} (h : OneBit S) {x y z : S} (hxy : x ≠ y) (hzy : z ≠ y) :
    z = x := by
  obtain ⟨f, hf⟩ := h
  apply hf
  have h1 : f x ≠ f y := fun e => hxy (hf e)
  have h2 : f z ≠ f y := fun e => hzy (hf e)
  revert h1 h2; cases f x <;> cases f y <;> cases f z <;> simp

/-- Value of the scannable object after the first `i` operations of `p₀` in `ε`. -/
def valAt (p₀ : P) (ε : List (Label P (scannable O))) (i : ℕ) : Fin k → Bool :=
  (scannable O).runOps (fun _ => false) ((opsOf ε p₀).take i)

/-- The current value (after all of `p₀`'s invoked operations). -/
def curVal (p₀ : P) (ε : List (Label P (scannable O))) : Fin k → Bool :=
  valAt p₀ ε (opsOf ε p₀).length

/-- `β` (an extension of `ε`) is `𝒱`-absent: in every `p₀`-idle configuration reached during
`β` (including its start, and including the completion of `p₀`'s last operation), the value of
the object is not in `V`. Since only `p₀` changes the object, the values in these configurations
are the values after `i` operations of `p₀`, for `i` from the number of operations invoked by
`p₀` before `β` to the number invoked by the end of `β`. -/
def Absent (p₀ : P) (V : Set (Fin k → Bool)) (ε β : List (Label P (scannable O))) : Prop :=
  ∀ i, (opsOf ε p₀).length ≤ i → i ≤ (opsOf (ε ++ β) p₀).length → valAt p₀ (ε ++ β) i ∉ V

/-- Allowed labels of the restricted executions: single-updater invocations that update only
components `< k'`. -/
def LabOK (p₀ : P) (k' : ℕ) : Label P (scannable O) → Prop
  | .inv p o => SingleUpdater p₀ p o ∧ ∀ i o', o = .update i o' → i.val < k'
  | _ => True

/-- `β` only contains steps of processes in `A`, single-updater invocations and updates of
components `< k'`. -/
def Lim (p₀ : P) (A : Finset P) (k' : ℕ) (β : List (Label P (scannable O))) : Prop :=
  ∀ ℓ ∈ β, ℓ.proc ∈ A ∧ LabOK p₀ k' ℓ

end Cslib.SharedMemory.Scannable
