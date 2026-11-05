import Papers.PODC2011.UnboundedConcurrency.Critical
import Papers.PODC2011.UnboundedConcurrency.IteratorStack

/-!
# Algorithms using read/write-like objects and iterator stacks

The base objects of the algorithms of Section 5.3 of Afek–Morrison–Wertheim (PODC 2011):
read/write-like objects `B r` (`r : R`, e.g. registers) and iterator stacks over value types
`W s` (`s : S`); any number of each (possibly infinitely many), initialized arbitrarily.

* `ST B W`: the object family, indexed by `R ⊕ S`;
* `stk C s`: the state of the iterator stack `s` in the configuration `C`.
-/

namespace Podc.UnboundedConcurrency

open Cslib.SharedMemory Cslib.SharedMemory.Arrival

/-- The base objects: read/write-like objects `B r` and iterator stacks `itStack (W s)`. -/
abbrev ST {R S : Type} (B : R → ObjSpec) (W : S → Type) : R ⊕ S → ObjSpec
  | .inl r => B r
  | .inr s => itStack (W s)

variable {R S : Type} {B : R → ObjSpec} {W : S → Type}

/-- The state of the iterator stack `s` in the memory `M`. -/
def stkM (M : (i : R ⊕ S) → (ST B W i).State) (s : S) : ISState (W s) := M (.inr s)

/-- The state of the iterator stack `s` in the configuration `C`. -/
def stk {L X Y : Type} {A : Alg (ST B W) L X Y} (C : Cfg A) (s : S) : ISState (W s) :=
  stkM C.mem s

end Podc.UnboundedConcurrency
