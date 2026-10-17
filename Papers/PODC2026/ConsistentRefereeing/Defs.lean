import Cslib.Computability.Distributed.SharedMemory.Mutex
import Cslib.Computability.Distributed.SharedMemory.Objects.Iface
import Cslib.Computability.Distributed.SharedMemory.StrongLin
import Cslib.Foundations.Data.Nat.Descent

/-!
# Contest objects (Attiya, Castañeda, Enea, PODC 2026)

Definitions shared by the formalization of *Impossibility Results for Strong Linearizability:
The Difficulty of Consistent Refereeing*.

## The (one-shot) contest object (Section 4)

Processes are any finite type `P` with a distinguished *referee* `ref`; all other processes are
*competitors*. `compete` may be invoked by the competitors and always returns `true` (here
`ContestResp.ok`); `decide` may be invoked by the referee and returns the first process that
executed `compete`, or `false` if there is none (here `ContestResp.winner w`, `w : Option P`).
Since base objects and high-level objects cannot see the caller in CSLib's model, `compete`
carries the caller's identifier (`ContestOp.compete i`, invoked by `i`).

The object is one-shot and the paper reasons about executions in which every competitor invokes
`compete` at most once, the referee invokes `decide` at most once, and the referee starts only
after some `compete` has completed. `Adm ref α` collects these conditions; the impossibility
theorems only assume correctness and progress on such executions (`Impl.StrongLinOn`,
`Impl.LockFreeOn`), which is weaker than assuming them on all executions.

## The long-lived contest object (Section 5)

`compete` may be invoked any number of times by each competitor and returns nothing (`ok`);
`decide` may be invoked at most once, by the referee, and returns an integer `x` such that every
competitor has executed at most `x` operations so far. This specification is nondeterministic
(`llSpec`, an `NSpec` whose state counts the `compete` operations of every process);
`llObj` is the interface-only `ObjSpec` (`ObjSpec.iface`) carrying the operation and response
types. `LLAdm ref α`: roles are
respected and the referee invokes at most once.
-/

namespace Cslib.SharedMemory

namespace Referee

/-! ## The one-shot contest object -/

/-- Operations of the contest objects. `compete i` is invoked by competitor `i`. -/
inductive ContestOp (P : Type) where
  | compete (i : P)
  | decide
  deriving DecidableEq

/-- Responses of the one-shot contest object: `ok` (`true`) for `compete`, `winner w` for
`decide` (`winner none` is the paper's `false`). -/
inductive ContestResp (P : Type) where
  | ok
  | winner (w : Option P)
  deriving DecidableEq

/-- The one-shot contest object. The state is the first competitor that executed `compete`. -/
abbrev contestObj (P : Type) : ObjSpec where
  State := Option P
  Op := ContestOp P
  Resp := ContestResp P
  init := none
  δ s
    | .compete i => (s.or (some i), .ok)
    | .decide => (s, .winner s)

/-- Once a competitor has won, the state of the contest object does not change. -/
lemma runOps_some {P : Type} (w : P) (os : List (ContestOp P)) :
    (contestObj P).runOps (some w) os = some w := by
  induction os with
  | nil => rfl
  | cons o os ih => cases o <;> simpa [ObjSpec.runOps] using ih

variable {P : Type} [DecidableEq P]

/-- The operation a process may invoke: `decide` for the referee, `compete p` for a competitor
`p`. -/
def roleOp (ref p : P) : ContestOp P := if p = ref then .decide else .compete p

/-- Admissible executions of the one-shot contest object (the executions considered in the
proof of Theorem 5): every process invokes at most one operation, the operation of its role, and
the referee invokes `decide` only after some competitor completed its `compete`. -/
structure Adm (ref : P) (α : List (Label P (contestObj P))) : Prop where
  oneShot : ∀ p, (opsOf α p).length ≤ 1
  role : ∀ p o, o ∈ opsOf α p → o = roleOp ref p
  late : ∀ β γ o, α = β ++ .inv ref o :: γ → ∃ c, c ≠ ref ∧ respsOf β c ≠ []

lemma Adm.of_append {ref : P} {α β : List (Label P (contestObj P))} (h : Adm ref (α ++ β)) :
    Adm ref α := by
  refine ⟨fun p => ?_, fun p o ho => ?_, fun β' γ o hα => ?_⟩
  · have := h.oneShot p; rw [opsOf_append, List.length_append] at this; omega
  · exact h.role p o (by rw [opsOf_append]; exact List.mem_append_left _ ho)
  · exact h.late β' (γ ++ β) o (by rw [hα]; simp)

lemma Adm.of_prefix {ref : P} {α β : List (Label P (contestObj P))} (h : Adm ref β)
    (hp : α <+: β) : Adm ref α := by
  obtain ⟨γ, rfl⟩ := hp; exact h.of_append

/-! ## The long-lived contest object -/

/-- Responses of the long-lived contest object. -/
inductive LLResp where
  | ok
  | val (x : ℕ)
  deriving DecidableEq

instance : Inhabited LLResp := ⟨.ok⟩

/-- The interface-only specification carrying the operation and response types of the
long-lived contest object (its real, nondeterministic specification is `llSpec`). -/
abbrev llObj (P : Type) : ObjSpec := ObjSpec.iface (ContestOp P) LLResp

example (P : Type) (o : ContestOp P) : (llObj P).δ () o = ((), .ok) := rfl

/-- The long-lived contest object: the state counts the `compete` operations of every process;
`decide` may return any `x` bounding all counts. -/
def llSpec (P : Type) [DecidableEq P] : NSpec (ContestOp P) LLResp where
  State := P → ℕ
  init := fun _ => 0
  Step q o r q' := match o with
    | .compete i => r = .ok ∧ q' = Function.update q i (q i + 1)
    | .decide => (∃ x, r = .val x ∧ ∀ c, q c ≤ x) ∧ q' = q

/-- Admissible executions of the long-lived contest object: competitors `p` only invoke
`compete p`, the referee only invokes `decide`, at most once. -/
structure LLAdm (ref : P) (α : List (Label P (llObj P))) : Prop where
  role : ∀ p o, o ∈ opsOf α p → o = roleOp ref p
  once : (opsOf α ref).length ≤ 1

lemma LLAdm.of_append {ref : P} {α β : List (Label P (llObj P))} (h : LLAdm ref (α ++ β)) :
    LLAdm ref α := by
  refine ⟨fun p o ho => h.role p o (by rw [opsOf_append]; exact List.mem_append_left _ ho), ?_⟩
  have := h.once; rw [opsOf_append, List.length_append] at this; omega

end Referee

end Cslib.SharedMemory
