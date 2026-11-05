import Papers.PODC2019.AbortableMutexAmortized.Model
import Papers.PODC2019.AbortableMutexAmortized.Chain

/-!
# The invariant (internal, pointer-local form)

The paper's invariant `I = I1 ∧ … ∧ I12` (Figure 1) quantifies over the queue `Q = q₁ … q_k` and the
node queue `A = a₀ … a_k`. We prove an equivalent-plus-strengthened form that is easier to
maintain:

* `Struct s Q a₀`: the structural part `I1`–`I4` (`Q` is a chain from `a₀` through `pred`/`mynode`,
  ending at `tail`; `a₀` is nobody's node; `mynode` is injective), plus the characterisation of
  queue membership `InQ` read off `I6`–`I8`: a process is in `Q` iff it is at one of the lines
  3–7, 9, 10, or it is at line 1 or 11 with `*mynode_p = pred_p` (its node is marked aborted).
* `Loc s a₀`: the remaining conjuncts `I6`, `I7`, `I9`–`I12`, stated through pointers: "`y` is the
  successor of `x` in `Q`" is `pred_y = mynode_x`, "`y` is `q₁`" is `pred_y = a₀`.
* `x1`: the **additional conjunct** needed to make the invariant inductive (the paper's `I` is not
  inductive, see `NotInductive.lean`): an aborted process of `Q` (line 1, 10 or 11) does not have
  its own go-address in its predecessor node.
-/

namespace Podc.AbortableMutexAmortized

variable {n : ℕ}

/-- Lines 3–7, 9, 10: a process there is always in the queue. -/
def PC.act : PC → Bool
  | .l3 | .l4 | .l5 | .l6 | .l7 | .l9 | .l10 => true
  | _ => false

/-- Lines 1 and 11: a process there is in the queue iff its node is marked aborted. -/
def PC.ab : PC → Bool
  | .l1 | .l11 => true
  | _ => false

/-- Membership in the abstract process queue `Q`. -/
def InQ (s : State n) (q : Fin n) : Prop :=
  (s.pc q).act = true ∨ ((s.pc q).ab = true ∧ s.node (s.mynode q) = .addr (s.pred q))

/-- Structural part of the invariant (`I1`–`I4`, `I6`/`I8` membership). -/
structure Struct (s : State n) (Q : List (Fin n)) (a0 : Node n) : Prop where
  ok : ChainOK s.pred s.mynode a0 Q
  last : lastN s.mynode a0 Q = s.tail
  mem : ∀ q, q ∈ Q ↔ InQ s q
  a0_ne : ∀ p, s.mynode p ≠ a0

/-- The remaining conjuncts of the invariant, in pointer form, plus the new conjunct `x1`. -/
structure Loc (s : State n) (a0 : Node n) : Prop where
  /-- `I6` (second line) -/
  i6a : ∀ p, s.pc p = .l2 → s.node (s.mynode p) = .nil
  /-- `I6` (third line) -/
  i6b : ∀ p, s.pc p = .l8 → s.node (s.mynode p) = .nil ∨ s.node (s.mynode p) = .go p
  /-- `I7` (first and third line): the node of an active queue member holds `nil` or the
  go-address of its successor. -/
  i7 : ∀ q, (s.pc q).act = true →
    s.node (s.mynode q) = .nil ∨
      ∃ y, InQ s y ∧ s.pred y = s.mynode q ∧ s.node (s.mynode q) = .go y
  /-- `I9`, first case -/
  i9a : (∀ y, s.pred y = a0 → s.pc y ≠ .l7) → s.node a0 = .token
  /-- `I9`, second case -/
  i9b : ∀ y, s.pred y = a0 → s.pc y = .l7 → s.node a0 = .nil ∨ s.node a0 = .go y
  /-- `I10` -/
  i10 : ∀ p, s.pc p = .l7 → s.pred p = a0
  /-- `I11` (first line) -/
  i11a : ∀ y, s.pred y = a0 → s.pc y = .l4 → s.go y = false →
    ∃ p, s.pc p = .l8 ∧ s.v p = .go y
  /-- `I11` (second line) -/
  i11b : ∀ x y, InQ s x → s.pred y = s.mynode x → s.pc y = .l4 → s.go y = false →
    s.node (s.mynode x) = .go y ∨
      (s.node (s.mynode x) = .addr (s.pred x) ∧ s.pc x = .l11 ∧ s.v x = .go y)
  /-- `I11` (third line) -/
  i11c : ∀ p, s.pc p = .l8 ∨ s.pc p = .l11 → ∃ q, s.v p = .go q
  /-- `I12` -/
  i12 : ∀ p, s.pc p = .l5 → s.go p = true
  /-- New conjunct (not in the paper): an aborted queue member's predecessor node does not hold
  its go-address. -/
  x1 : ∀ q, InQ s q → (s.pc q = .l1 ∨ s.pc q = .l10 ∨ s.pc q = .l11) →
    s.node (s.pred q) ≠ .go q

/-- The (strengthened) invariant. -/
def Inv (s : State n) : Prop := ∃ Q a0, Struct s Q a0 ∧ Loc s a0

/-- How a step of `p` changes the queue: unchanged, `p` appended (line 2), `p`'s predecessor
spliced out (lines 3, 6, 9), or `p` removed from the front (line 7). -/
inductive QStep (p : Fin n) : List (Fin n) → List (Fin n) → Prop
  | same (Q : List (Fin n)) : QStep p Q Q
  | enq (Q : List (Fin n)) : QStep p Q (Q ++ [p])
  | splice (L : List (Fin n)) (x : Fin n) (R : List (Fin n)) : QStep p (L ++ x :: p :: R) (L ++ p :: R)
  | deq (R : List (Fin n)) : QStep p (p :: R) R

end Podc.AbortableMutexAmortized
