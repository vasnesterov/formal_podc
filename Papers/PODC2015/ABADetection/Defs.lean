import Cslib.Computability.Distributed.SharedMemory.Covering
import Cslib.Computability.Distributed.SharedMemory.Solo
import Cslib.Computability.Distributed.SharedMemory.Linearization
import Cslib.Computability.Distributed.SharedMemory.LinPoints
import Cslib.Computability.Distributed.SharedMemory.Objects.LLSC
import Mathlib

/-!
# ABA prevention and detection (Aghazadeh–Woelfel, PODC 2015): definitions

Model: CSLib's asynchronous shared-memory model (`Cslib.SharedMemory.Impl`): deterministic
processes, atomic base objects, executions as lists of labels (`inv p o`, `tau p`, `ret p r`).

* `abaObj P V v₀` — the **ABA-detecting register** (paper, Section 1): `DWrite(x)` writes `x`,
  `DRead()` by `p` returns the value and a flag that is `true` iff some `DWrite` happened since
  `p`'s previous `DRead`. Since an `ObjSpec` does not see the caller, `DRead` carries the reader
  (`dread p`); implementations enforce this with `Impl.allowed`.
* `wcasObj V v₀` — a **writable CAS object** (`Read`, `Write`, `CAS(x,y)`); `Read` and `CAS`
  return the old value (the more informative of the two conventions of the paper).

The lower-bound proofs only use *one* property of the implemented object, the distinguishability
of *clean* and *dirty* configurations (paper: Observations 1 and 2). It is stated abstractly for
a designated writer `w0`, a reader operation `rd p` for each reader `p` and a *round* `ws` of
operations of the writer (`[DWrite(x)]` for ABA-detecting registers, `[LL(), SC(x)]` for LL/SC):

* `Std w0 rd ws α` — in `α`, the writer invokes only operations of `ws`, every other process `p`
  only `rd p` (paper: "process 0 repeatedly executes WeakWrite(), the others WeakRead()").
* `Clean w0 rd p α` — `α` contains a complete `rd p` by `p` after which the writer invoked
  nothing (paper: `p`-clean, Section 2).
* `Dirty w0 ws p α` — `α` contains a complete round `ws` of the writer that begins after every
  operation of `p` has returned (paper: `p`-dirty).
* `Separates I w0 rd ws` — for every reader `p`, a `p`-clean and a `p`-dirty reachable
  configuration in which `p` is idle are distinguishable by `p` (Observations 1, 2).
-/

set_option linter.unusedSectionVars false

namespace Cslib.SharedMemory.ABADetection

open Cslib.SharedMemory

/-! ## The ABA-detecting register -/

/-- Operations of an ABA-detecting register over values `V`; `dread p` is a `DRead()` by `p`. -/
inductive ABAOp (P V : Type) where
  /-- `DRead()` invoked by process `p`. -/
  | dread (p : P)
  /-- `DWrite(x)`. -/
  | dwrite (x : V)
  deriving DecidableEq

/-- The **ABA-detecting register** (multi-writer; single-writer implementations restrict
`dwrite` to one process with `Impl.allowed`). The state is the value together with the flags
of all processes; `dwrite x` sets the value to `x` and every flag; `dread p` returns the value and
`p`'s flag, and clears `p`'s flag. Initially no flag is set. The response of `dwrite` is a dummy
(`(x, true)`). -/
abbrev abaObj (P V : Type) [DecidableEq P] (v₀ : V) : ObjSpec where
  State := V × (P → Bool)
  Op := ABAOp P V
  Resp := V × Bool
  init := (v₀, fun _ => false)
  δ s
    | .dread p => ((s.1, Function.update s.2 p false), (s.1, s.2 p))
    | .dwrite x => ((x, fun _ => true), (x, true))

/-! ## Writable CAS objects -/

/-- Operations of a writable CAS object. -/
inductive WCasOp (V : Type) where
  | read
  | write (v : V)
  | cas (x y : V)
  deriving DecidableEq

/-- A **writable CAS object** over `V`. `Read` and `CAS(x,y)` return the old value; `CAS(x,y)`
writes `y` iff the old value is `x`; `Write` returns nothing (`none`). -/
abbrev wcasObj (V : Type) [DecidableEq V] (v₀ : V) : ObjSpec where
  State := V
  Op := WCasOp V
  Resp := Option V
  init := v₀
  δ s
    | .read => (s, some s)
    | .write v => (v, none)
    | .cas x y => (if s = x then y else s, some s)

/-- `WCasOp V` is the image of `Option (V ⊕ V × V)`. -/
def WCasOp.equivOption (V : Type) : WCasOp V ≃ Option (V ⊕ V × V) where
  toFun
    | .read => none
    | .write v => some (.inl v)
    | .cas x y => some (.inr (x, y))
  invFun
    | none => .read
    | some (.inl v) => .write v
    | some (.inr (x, y)) => .cas x y
  left_inv o := by cases o <;> rfl
  right_inv o := by rcases o with _ | _ | ⟨_, _⟩ <;> rfl

instance (V : Type) [Finite V] : Finite (WCasOp V) :=
  Finite.of_equiv _ (WCasOp.equivOption V).symm

/-! ## Standard executions, clean and dirty executions -/

variable {P : Type} {A : ObjSpec} [DecidableEq P]

/-- In `α`, the writer `w0` invokes only operations of its round `ws`, and every other process
`q` only its reader operation `rd q`. -/
def Std (w0 : P) (rd : P → A.Op) (ws : List A.Op) (α : List (Label P A)) : Prop :=
  ∀ q o, Label.inv q o ∈ α → (q = w0 ∧ o ∈ ws) ∨ (q ≠ w0 ∧ o = rd q)

/-- `α` is **`p`-clean** (paper, Section 2): it contains a complete operation `rd p` of `p` such
that every operation of the writer `w0` returned before it was invoked. -/
def Clean (w0 : P) (rd : P → A.Op) (p : P) (α : List (Label P A)) : Prop :=
  ∃ k, opOf α (p, k) = some (rd p) ∧ Completed α (p, k) ∧
    ∀ k', Invoked α (w0, k') → Precedes α (w0, k') (p, k)

/-- `α` is **`p`-dirty** (paper, Section 2): the writer `w0` performs a complete round `ws`
(instances `(w0, j), …, (w0, j + |ws| - 1)`), and every operation of `p` returned before the
round began. -/
def Dirty (w0 : P) (ws : List A.Op) (p : P) (α : List (Label P A)) : Prop :=
  ∃ j, (∀ m (h : m < ws.length), opOf α (w0, j + m) = some ws[m] ∧ Completed α (w0, j + m)) ∧
    ∀ k, Invoked α (p, k) → Precedes α (p, k) (w0, j)

variable {ι : Type} {B : ι → ObjSpec} {L : Type} [DecidableEq ι]

/-- **Clean and dirty configurations are distinguishable** (abstract form of Observations 1
and 2): for every reader `p ≠ w0`, if `α₁` is `p`-clean, `α₂` is `p`-dirty, both standard, and
`p` is idle at their ends, then the final configurations differ in the memory or in `p`'s state. -/
def Separates (I : Impl A B P L) (w0 : P) (rd : P → A.Op) (ws : List A.Op) : Prop :=
  ∀ p, p ≠ w0 → ∀ α₁ α₂ C₁ C₂, I.run α₁ = some C₁ → I.run α₂ = some C₂ →
    Std w0 rd ws α₁ → Std w0 rd ws α₂ → Clean w0 rd p α₁ → Dirty w0 ws p α₂ →
    C₁.pend p = none → C₂.pend p = none → ¬ Impl.Agree p C₁ C₂

/-! ## Step complexity -/

/-- **Worst-case step complexity at most `t`**: in every execution, every operation (complete or
not) has at most `t` internal steps (base-object accesses) of its process. -/
def StepBound (I : Impl A B P L) (t : ℕ) : Prop :=
  ∀ α₁ (p : P) o α₂, I.Valid (α₁ ++ .inv p o :: α₂) → (∀ r, Label.ret p r ∉ α₂) →
    α₂.countP (Label.isTauOf p) ≤ t

end Cslib.SharedMemory.ABADetection
