import Mathlib

/-!
# The formal framework of Section 4 and the correctness predicates of Section 5

Kokociński, Kobus, Wojciechowski, *On Mixing Eventual and Strong Consistency: Bayou Revisited*,
PODC 2019; full version *On Mixing Eventual and Strong Consistency: Acute Cloud Types*,
arXiv:1905.11762v2.

Burckhardt-style histories and abstract executions over an arbitrary type of events `Ev`
(Sections 4.2–4.3), replicated data types and ACT specifications (Sections 4.5–4.6), and the
correctness predicates `EV`, `NCC`, `RVAL`, `BEC`, `FRVAL`, `CPAR`, `FEC` (Sections 5.1–5.4) and
`SinOrd`, `SessArb`, `SEQ`, `RT`, `LIN` (Section 5.5), all in their level-parametrised form.

Conventions.
* `rval e = none` encodes `∇` (the operation is pending).
* Relations are `Ev → Ev → Prop`; `r x y` reads `x −r→ y`.
* An event graph is identified with its events up to isomorphism by quantifying over *every*
  event type; correctness predicates below are invariant under isomorphism, and
  `History.Satisfies` asks for one abstract execution (the paper asks the predicate for all
  isomorphic copies, which is equivalent for these predicates and only stronger in general).
-/

-- CSLib candidate (consistency models for replicated data types)
namespace Podc.BayouRevisited

/-- Consistency levels of operations (Section 3.1). -/
inductive Level
  | weak
  | strong
  deriving DecidableEq

/-- A history `H = (E, op, rval, rb, ss, lvl)` (Section 4.2); the events are the elements of `Ev`. -/
structure History (Ev Op Val : Type) where
  /-- The operation invoked in an event. -/
  op : Ev → Op
  /-- The returned value; `none` is `∇` (pending). -/
  rval : Ev → Option Val
  /-- Returns-before: `rb a b` iff `a` returned before `b` was invoked (real time). -/
  rb : Ev → Ev → Prop
  /-- Same session. -/
  ss : Ev → Ev → Prop
  /-- Consistency level of the event. -/
  lvl : Ev → Level

/-- An abstract execution `A = (H, vis, ar, par)` (Section 4.3), without the well-formedness
conditions (see `AbsExec.WF`). -/
structure AbsExec (Ev Op Val : Type) extends History Ev Op Val where
  /-- Visibility. -/
  vis : Ev → Ev → Prop
  /-- Arbitration. -/
  ar : Ev → Ev → Prop
  /-- Perceived arbitration: `par e` is the arbitration order as perceived by `e`. -/
  par : Ev → Ev → Ev → Prop

/-- A relation is acyclic (Figure 2). -/
def Acyclic {Ev : Type} (r : Ev → Ev → Prop) : Prop := ∀ x, ¬ Relation.TransGen r x x

/-- A relation is natural: every element has finitely many predecessors (Figure 2). -/
def Natural {Ev : Type} (r : Ev → Ev → Prop) : Prop := ∀ x, {y | r y x}.Finite

/-- A strict total order (irreflexive, transitive, total; Figure 2). -/
structure IsStrictTotal {Ev : Type} (r : Ev → Ev → Prop) : Prop where
  irrefl : ∀ x, ¬ r x x
  trans : ∀ x y z, r x y → r y z → r x z
  total : ∀ x y, x ≠ y → r x y ∨ r y x

/-- The conditions of Section 4.3 on an abstract execution: `vis` is acyclic and natural and
`ar` is a total order. -/
structure AbsExec.WF {Ev Op Val : Type} (A : AbsExec Ev Op Val) : Prop where
  vis_acyclic : Acyclic A.vis
  vis_natural : Natural A.vis
  ar_total : IsStrictTotal A.ar

/-- An operation context `(E, op, vis, ar)` (Section 4.5). -/
structure Context (Ev Op : Type) where
  /-- The events of the context. -/
  E : Set Ev
  /-- Operations of events. -/
  op : Ev → Op
  /-- Visibility. -/
  vis : Ev → Ev → Prop
  /-- Arbitration. -/
  ar : Ev → Ev → Prop

/-- A replicated data type `F` (Section 4.5): the expected return value of an operation in a
given operation context, for contexts over any type of events. -/
def RDT (Op Val : Type) : Type 1 := ∀ {Ev : Type}, Op → Context Ev Op → Val

/-- `op` is a read-only operation of `F` (Section 4.5): removing an event of `op` from any
context does not change the result of any operation. -/
def RDT.IsReadOnly {Op Val : Type} (F : RDT Op Val) (op : Op) : Prop :=
  ∀ (Ev : Type) (op' : Op) (C : Context Ev Op) (e : Ev), e ∈ C.E → C.op e = op →
    F op' C = F op' { C with E := C.E \ {e} }

/-- An ACT specification `(F, lvlmap)` (Section 4.6). -/
structure ACTSpec (Op Val : Type) where
  /-- The replicated data type. -/
  F : RDT Op Val
  /-- The consistency levels with which each operation may be invoked. -/
  lvlmap : Op → Set Level

/-- `rank(A, rel, a) = |{x ∈ A : x −rel→ a}|` (Section 4.1). -/
noncomputable def rank {Ev : Type} (S : Set Ev) (rel : Ev → Ev → Prop) (a : Ev) : ℕ :=
  {x ∈ S | rel x a}.ncard

namespace AbsExec

variable {Ev Op Val : Type} (A : AbsExec Ev Op Val)

/-- `context(A, e) = (vis⁻¹(e), op, vis, ar)` (Section 4.5). -/
def context (e : Ev) : Context Ev Op := ⟨{x | A.vis x e}, A.op, A.vis, A.ar⟩

/-- `fcontext(A, e) = (vis⁻¹(e), op, vis, par(e))` (Section 5.3). -/
def fcontext (e : Ev) : Context Ev Op := ⟨{x | A.vis x e}, A.op, A.vis, A.par e⟩

/-- Session order `so = rb ∩ ss` (Section 5.1). -/
def so (x y : Ev) : Prop := A.rb x y ∧ A.ss x y

/-- Happens-before `hb = (so ∪ vis)⁺` (Section 5.1). -/
def hb : Ev → Ev → Prop := Relation.TransGen fun x y => A.so x y ∨ A.vis x y

/-- `EV(l)`: every event is eventually visible to the events of level `l` (Section 5.4). -/
def EV (l : Level) : Prop :=
  ∀ e, {e' | A.lvl e' = l ∧ A.rb e e' ∧ ¬ A.vis e e'}.Finite

/-- `NCC(l) = acyclic(hb ∩ (L × L))` (Section 5.4). -/
def NCC (l : Level) : Prop := Acyclic fun x y => A.hb x y ∧ A.lvl x = l ∧ A.lvl y = l

/-- `RVAL(l, F)` (Section 5.4); a pending event (`rval = ∇`) never satisfies it. -/
def RVAL (l : Level) (F : RDT Op Val) : Prop :=
  ∀ e, A.lvl e = l → A.rval e = some (F (A.op e) (A.context e))

/-- Basic eventual consistency `BEC(l, F) = EV(l) ∧ NCC(l) ∧ RVAL(l, F)` (Section 5.4). -/
def BEC (l : Level) (F : RDT Op Val) : Prop := A.EV l ∧ A.NCC l ∧ A.RVAL l F

/-- `FRVAL(l, F)` (Section 5.4). -/
def FRVAL (l : Level) (F : RDT Op Val) : Prop :=
  ∀ e, A.lvl e = l → A.rval e = some (F (A.op e) (A.fcontext e))

/-- Convergent perceived arbitration `CPAR(l)` (Section 5.4). -/
def CPAR (l : Level) : Prop :=
  ∀ e, {e' | A.lvl e' = l ∧ A.vis e e' ∧
    rank {x | A.vis x e'} (A.par e') e ≠ rank {x | A.vis x e'} A.ar e}.Finite

/-- Fluctuating eventual consistency `FEC(l, F)` (Section 5.4). -/
def FEC (l : Level) (F : RDT Op Val) : Prop := A.EV l ∧ A.NCC l ∧ A.FRVAL l F ∧ A.CPAR l

/-- Single order `SinOrd(l)`: `∃ E' ⊆ rval⁻¹(∇), vis_L = ar_L \ (E' × E)` with
`vis_L = vis ∩ (E × L)`, `ar_L = ar ∩ (E × L)` (Section 5.5). -/
def SinOrd (l : Level) : Prop :=
  ∃ E' : Set Ev, (∀ e ∈ E', A.rval e = none) ∧
    ∀ x y, A.lvl y = l → (A.vis x y ↔ A.ar x y ∧ x ∉ E')

/-- `SessArb(l) = so_L ⊆ ar` (Section 5.5). -/
def SessArb (l : Level) : Prop := ∀ x y, A.so x y → A.lvl y = l → A.ar x y

/-- Sequential consistency `SEQ(l, F)` (Section 5.5). -/
def SEQ (l : Level) (F : RDT Op Val) : Prop := A.SinOrd l ∧ A.SessArb l ∧ A.BEC l F

/-- Real-time order `RT(l) = rb_L ⊆ ar` with `rb_L = rb ∩ (L × L)` (Section 5.5). -/
def RT (l : Level) : Prop := ∀ x y, A.rb x y → A.lvl x = l → A.lvl y = l → A.ar x y

/-- Linearizability `LIN(l, F)` (Section 5.5). -/
def LIN (l : Level) (F : RDT Op Val) : Prop := A.SinOrd l ∧ A.RT l ∧ A.BEC l F

end AbsExec

/-- A history satisfies a consistency guarantee `P` (Section 4.4) if it extends to a
(well-formed) abstract execution satisfying `P`. -/
def History.Satisfies {Ev Op Val : Type} (H : History Ev Op Val)
    (P : AbsExec Ev Op Val → Prop) : Prop :=
  ∃ A : AbsExec Ev Op Val, A.toHistory = H ∧ A.WF ∧ P A

end Podc.BayouRevisited
