import Cslib.Computability.Distributed.SharedMemory.Model
import Mathlib

/-!
# Context-aware releasable LL/SC objects (R-LLSC)

Section 6.1 of Attiya, Bender, Farach-Colton, Oshman, Schiller, *History-Independent Concurrent
Objects*, PODC 2024.

The state of an R-LLSC object is a pair `(val, context)` of a value and a set of processes; the
initial state is `(v₀, ∅)`. Process `p` can perform

* `LL`: adds `p` to the context and returns `val`;
* `VL`: returns whether `p ∈ context`;
* `SC(new)`: if `p ∈ context`, sets `val := new`, `context := ∅` and returns `true`; otherwise
  returns `false`;
* `RL`: removes `p` from the context and returns `true`;
* `Load`: returns `val`;
* `Store(new)`: sets `val := new`, `context := ∅` and returns `true`.

Since the behaviour of `LL`, `VL`, `SC` and `RL` depends on the invoking process, these operations
carry the process id as an argument (an `ObjSpec` has no notion of the invoking process). An
implementation uses its own id; for the implemented R-LLSC object (Algorithm 6) this is enforced
with `Impl.allowed` (see `RLLSCOp.proc`). Responses are `V ⊕ Bool`: `LL` and `Load` return
`inl val`, the other operations `inr b`.
-/

namespace Cslib.SharedMemory

/-- Operations of an R-LLSC object over values `V`, for processes `P`. -/
inductive RLLSCOp (P V : Type) where
  | ll (p : P)
  | vl (p : P)
  | sc (p : P) (v : V)
  | rl (p : P)
  | load
  | store (v : V)

/-- The process an operation must be invoked by (`none` for `Load`/`Store`, which any process
may invoke). -/
def RLLSCOp.proc {P V : Type} : RLLSCOp P V → Option P
  | .ll p | .vl p | .sc p _ | .rl p => some p
  | .load | .store _ => none

/-- The R-LLSC object over `V` with initial value `v₀` (context initially empty). -/
@[reducible] def rllsc (P V : Type) [DecidableEq P] (v₀ : V) : ObjSpec where
  State := V × Finset P
  Op := RLLSCOp P V
  Resp := V ⊕ Bool
  init := (v₀, ∅)
  δ s
    | .ll p => ((s.1, insert p s.2), .inl s.1)
    | .vl p => (s, .inr (decide (p ∈ s.2)))
    | .sc p v => if p ∈ s.2 then ((v, ∅), .inr true) else (s, .inr false)
    | .rl p => ((s.1, s.2.erase p), .inr true)
    | .load => (s, .inl s.1)
    | .store v => ((v, ∅), .inr true)

namespace rllsc

variable {P V : Type} [DecidableEq P] {v₀ : V} (s : V × Finset P) (p : P) (v : V)

@[simp] lemma δ_ll : (rllsc P V v₀).δ s (.ll p) = ((s.1, insert p s.2), .inl s.1) := rfl
@[simp] lemma δ_vl : (rllsc P V v₀).δ s (.vl p) = (s, .inr (decide (p ∈ s.2))) := rfl
@[simp] lemma δ_sc : (rllsc P V v₀).δ s (.sc p v) =
    if p ∈ s.2 then ((v, ∅), .inr true) else (s, .inr false) := rfl
@[simp] lemma δ_rl : (rllsc P V v₀).δ s (.rl p) = ((s.1, s.2.erase p), .inr true) := rfl
@[simp] lemma δ_load : (rllsc P V v₀).δ s .load = (s, .inl s.1) := rfl
@[simp] lemma δ_store : (rllsc P V v₀).δ s (.store v) = ((v, ∅), .inr true) := rfl

end rllsc

end Cslib.SharedMemory
