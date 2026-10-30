import Papers.PODC2023.PPDoubleExpThresholds.Stable
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card

/-!
# Population programs (Section 4)

A population program `P = (Q, Proc)` has a finite set of registers `Q` (values in `ℕ`) and a list
of procedures built from while-loops, if-statements and the instructions

* `x ↦ y` (move a unit from `x` to `y`; *hangs* if `x` is empty),
* `detect x > 0` (nondeterministically returns `false`, or whether `x > 0`),
* `swap x, y`, `OF := b`, `restart`, procedure calls and `return b`.

Procedure calls are acyclic. A configuration is `(C, OF, σ)` with `C ∈ ℕ^Q`, the output flag `OF`
and the call stack `σ ∈ (Proc × ℕ)*` (names and currently executed instructions). It is initial if
`σ = ((Main, 1))`; `restart` moves to any initial configuration with the same total number of units.
We keep the value of `OF` on a restart: this is how the paper implements `restart` in population
machines (Appendix B.2), and the programs of Section 6 set `OF` before reading it anyway.

## Modelling

We give the *instruction-level* semantics the paper describes: every procedure is a list of flat
instructions (`Instr`), with the conditions of `if`/`while` compiled to conditional jumps. The
structured syntax (`Stmt`, `BExp`) of the paper is compiled to flat code by `Stmt.compile`
(standard, short-circuit evaluation of `∧`, `∨`); the configuration `(C, OF, σ)` is exactly the
paper's, with `σ` storing the procedure and the index of its current flat instruction (0-based).

* A procedure call `call p tT tF` stays on the caller's frame while `p` runs; when `p` executes
  `ret b`, the caller continues at `tT` if `b` and at `tF` otherwise. Calls used as statements
  have `tT = tF`.
* `detect x tT tF` continues at `tF`, or at `tT` if `x > 0`.
* If a configuration has no successor (a move from an empty register, a return of `Main`, a jump
  out of the code), the program hangs: `→` has a self-loop there (Section 3 requires `→` to be
  left-total).

`P` decides `φ` if every fair run started at an initial configuration `(C, OF, ((Main, 0)))`
stabilises to `φ(|C|)` (Section 3; the paper's text omits the word "fair" in Section 4).
-/

namespace Podc.PPDoubleExpThresholds

open Cslib.TransitionSystem

/-! ### Flat instructions and programs -/

/-- Flat instructions of population programs over registers `R` and procedure names `P`. -/
inductive Instr (R P : Type*)
  /-- `x ↦ y`. -/
  | move (x y : R)
  /-- `swap x, y`. -/
  | swap (x y : R)
  /-- `OF := b`. -/
  | setOF (b : Bool)
  /-- `detect x > 0`, continuing at `tT` (only possible if `x > 0`) or at `tF`. -/
  | detect (x : R) (tT tF : ℕ)
  /-- Call `p`; continue at `tT` if it returns `true`, at `tF` if it returns `false`. -/
  | call (p : P) (tT tF : ℕ)
  /-- `return b`. -/
  | ret (b : Bool)
  /-- Unconditional jump. -/
  | goto (t : ℕ)
  /-- `restart`. -/
  | restart
  deriving Repr

/-- A population program: the flat code of every procedure, the main procedure, and the (finite)
list of procedures of the program. -/
structure Program (R P : Type*) where
  /-- The flat code of each procedure. -/
  code : P → List (Instr R P)
  /-- The procedure `Main`. -/
  main : P
  /-- The procedures of the program. -/
  procs : Finset P

/-- Configurations `(C, OF, σ)`. -/
structure Cfg (R P : Type*) where
  /-- The register configuration. -/
  C : R → ℕ
  /-- The output flag. -/
  OF : Bool
  /-- The call stack (innermost frame first). -/
  stk : List (P × ℕ)

variable {R P : Type*} [DecidableEq R]

/-- Move one unit from `x` to `y`. -/
def mv (C : R → ℕ) (x y : R) : R → ℕ :=
  fun r => C r - (if r = x then 1 else 0) + (if r = y then 1 else 0)

/-- Exchange the values of `x` and `y`. -/
def swp (C : R → ℕ) (x y : R) : R → ℕ := fun r => C (Equiv.swap x y r)

namespace Program

variable (prog : Program R P)

/-- The instruction at index `pc` of procedure `p`. -/
def instr (p : P) (pc : ℕ) : Option (Instr R P) := (prog.code p)[pc]?

/-- Steps that execute an instruction other than `restart`. -/
inductive Step₀ : Cfg R P → Cfg R P → Prop
  | move {C OF p pc σ x y} (h : prog.instr p pc = some (.move x y)) (hx : 0 < C x) :
      Step₀ ⟨C, OF, (p, pc) :: σ⟩ ⟨mv C x y, OF, (p, pc + 1) :: σ⟩
  | swap {C OF p pc σ x y} (h : prog.instr p pc = some (.swap x y)) :
      Step₀ ⟨C, OF, (p, pc) :: σ⟩ ⟨swp C x y, OF, (p, pc + 1) :: σ⟩
  | setOF {C OF p pc σ b} (h : prog.instr p pc = some (.setOF b)) :
      Step₀ ⟨C, OF, (p, pc) :: σ⟩ ⟨C, b, (p, pc + 1) :: σ⟩
  | detectT {C OF p pc σ x tT tF} (h : prog.instr p pc = some (.detect x tT tF)) (hx : 0 < C x) :
      Step₀ ⟨C, OF, (p, pc) :: σ⟩ ⟨C, OF, (p, tT) :: σ⟩
  | detectF {C OF p pc σ x tT tF} (h : prog.instr p pc = some (.detect x tT tF)) :
      Step₀ ⟨C, OF, (p, pc) :: σ⟩ ⟨C, OF, (p, tF) :: σ⟩
  | goto {C OF p pc σ t} (h : prog.instr p pc = some (.goto t)) :
      Step₀ ⟨C, OF, (p, pc) :: σ⟩ ⟨C, OF, (p, t) :: σ⟩
  | call {C OF p pc σ q tT tF} (h : prog.instr p pc = some (.call q tT tF)) :
      Step₀ ⟨C, OF, (p, pc) :: σ⟩ ⟨C, OF, (q, 0) :: (p, pc) :: σ⟩
  | ret {C OF q pc p pc' σ b q' tT tF} (h : prog.instr q pc = some (.ret b))
      (h' : prog.instr p pc' = some (.call q' tT tF)) :
      Step₀ ⟨C, OF, (q, pc) :: (p, pc') :: σ⟩ ⟨C, OF, (p, cond b tT tF) :: σ⟩

/-- The configuration is about to execute `restart`. -/
def AtRestart (s : Cfg R P) : Prop :=
  ∃ p pc σ, s.stk = (p, pc) :: σ ∧ prog.instr p pc = some .restart

variable [Fintype R]

/-- The total number of units `|C|`. -/
def total (C : R → ℕ) : ℕ := ∑ r, C r

/-- The initial configuration with registers `C` and output flag `OF`. -/
def init (C : R → ℕ) (OF : Bool) : Cfg R P := ⟨C, OF, [(prog.main, 0)]⟩

/-- A `restart`: any register configuration with the same total; execution continues at the
start of `Main` (the output flag is not changed, as in the paper's implementation of `restart` in
Appendix B.2). -/
def RestartStep (s s' : Cfg R P) : Prop :=
  prog.AtRestart s ∧ total s'.C = total s.C ∧ s'.OF = s.OF ∧ s'.stk = [(prog.main, 0)]

/-- One step `D → D'` of a population program: execute an instruction, or stay if the program
hangs. -/
def Step (s s' : Cfg R P) : Prop :=
  prog.Step₀ s s' ∨ prog.RestartStep s s' ∨
    (s' = s ∧ ∀ s'', ¬ prog.Step₀ s s'' ∧ ¬ prog.RestartStep s s'')

/-- Every configuration has output `OF`. -/
def out (s : Cfg R P) : Option Bool := some s.OF

/-- `P` decides `φ`: every fair run started at an initial configuration `(C, OF, ((Main, 0)))`
stabilises to `φ(|C|)`. -/
def Decides (φ : ℕ → Bool) : Prop :=
  ∀ E : Run prog.Step, (E.st 0).stk = [(prog.main, 0)] → E.GloballyFair →
    StabilisesTo out E (φ (total (E.st 0).C))

/-- Well-formedness of a program: `Main` is one of its procedures, procedures only call
procedures of the program, and procedure calls are acyclic (witnessed by a rank function). The
paper requires acyclic calls as part of the definition of population programs. We also require
moves between distinct registers (as population machines do, Definition 6). -/
structure WellFormed : Prop where
  main_mem : prog.main ∈ prog.procs
  call_mem : ∀ p ∈ prog.procs, ∀ q tT tF, Instr.call q tT tF ∈ prog.code p → q ∈ prog.procs
  acyclic : ∃ rank : P → ℕ, ∀ p ∈ prog.procs, ∀ q tT tF, Instr.call q tT tF ∈ prog.code p →
    rank q < rank p
  move_ne : ∀ p ∈ prog.procs, ∀ x y, Instr.move x y ∈ prog.code p → x ≠ y

/-! ### Size -/

/-- The register pairs that some `swap` instruction of the program exchanges. -/
def SwapEdge (x y : R) : Prop :=
  ∃ p ∈ prog.procs, Instr.swap x y ∈ prog.code p ∨ Instr.swap y x ∈ prog.code p

open Classical in
/-- The swap-size: the number of pairs `(x, y)`, `x ≠ y`, such that `x` can be swapped with `y`
through a sequence of swaps. -/
noncomputable def swapSize : ℕ :=
  Fintype.card {xy : R × R // xy.1 ≠ xy.2 ∧ Relation.TransGen prog.SwapEdge xy.1 xy.2}

/-- The size `|Q| + L + S` of a program: registers, instructions and swap-size. -/
noncomputable def size : ℕ :=
  Fintype.card R + ∑ p ∈ prog.procs, (prog.code p).length + prog.swapSize

end Program

/-! ### Structured syntax and its compilation to flat code -/

/-- Boolean conditions of `if` and `while`. -/
inductive BExp (R P : Type*)
  /-- `detect x > 0`. -/
  | detect (x : R)
  /-- A procedure call used as a condition. -/
  | call (p : P)
  /-- `true`. -/
  | tt
  /-- `¬ e`. -/
  | not (e : BExp R P)
  /-- `e₁ ∧ e₂` (short-circuit). -/
  | and (e₁ e₂ : BExp R P)
  /-- `e₁ ∨ e₂` (short-circuit). -/
  | or (e₁ e₂ : BExp R P)

/-- Structured statements of population programs. -/
inductive Stmt (R P : Type*)
  | skip
  | move (x y : R)
  | swap (x y : R)
  | setOF (b : Bool)
  | restart
  /-- `return b`. -/
  | ret (b : Bool)
  /-- A procedure call used as a statement. -/
  | call (p : P)
  | seq (s t : Stmt R P)
  /-- `if e then s else t`. -/
  | ite (e : BExp R P) (s t : Stmt R P)
  /-- `while e do s`. -/
  | whileDo (e : BExp R P) (s : Stmt R P)

namespace BExp

/-- Length of the compiled code of a condition. -/
def len : BExp R P → ℕ
  | detect _ => 1
  | call _ => 1
  | tt => 1
  | not e => e.len
  | and e₁ e₂ => e₁.len + e₂.len
  | or e₁ e₂ => e₁.len + e₂.len

/-- Compile a condition placed at address `a`: jump to `tT` if it is true, to `tF` if false. -/
def compile : BExp R P → ℕ → ℕ → ℕ → List (Instr R P)
  | detect x, _, tT, tF => [.detect x tT tF]
  | call p, _, tT, tF => [.call p tT tF]
  | tt, _, tT, _ => [.goto tT]
  | not e, a, tT, tF => e.compile a tF tT
  | and e₁ e₂, a, tT, tF => e₁.compile a (a + e₁.len) tF ++ e₂.compile (a + e₁.len) tT tF
  | or e₁ e₂, a, tT, tF => e₁.compile a tT (a + e₁.len) ++ e₂.compile (a + e₁.len) tT tF

end BExp

namespace Stmt

/-- Length of the compiled code of a statement. -/
def len : Stmt R P → ℕ
  | skip => 0
  | seq s t => s.len + t.len
  | ite e s t => e.len + s.len + 1 + t.len
  | whileDo e s => e.len + s.len + 1
  | _ => 1

/-- Compile a statement placed at address `a`; control falls through to `a + s.len`. -/
def compile : Stmt R P → ℕ → List (Instr R P)
  | skip, _ => []
  | move x y, _ => [.move x y]
  | swap x y, _ => [.swap x y]
  | setOF b, _ => [.setOF b]
  | restart, _ => [.restart]
  | ret b, _ => [.ret b]
  | call p, a => [.call p (a + 1) (a + 1)]
  | seq s t, a => s.compile a ++ t.compile (a + s.len)
  | ite e s t, a =>
      e.compile a (a + e.len) (a + e.len + s.len + 1) ++ s.compile (a + e.len) ++
        [.goto (a + e.len + s.len + 1 + t.len)] ++ t.compile (a + e.len + s.len + 1)
  | whileDo e s, a =>
      e.compile a (a + e.len) (a + e.len + s.len + 1) ++ s.compile (a + e.len) ++ [.goto a]

/-- Sequential composition of a list of statements (used for the paper's `for`-loops, which are
macros expanding into copies of their body). -/
def seqs : List (Stmt R P) → Stmt R P
  | [] => skip
  | s :: l => seq s (seqs l)

/-- `if e then s`. -/
def ifThen (e : BExp R P) (s : Stmt R P) : Stmt R P := ite e s skip

/-- The flat code of a procedure body: the compiled body followed by an implicit `return false`
(procedures that do not return a value). -/
def body (s : Stmt R P) : List (Instr R P) := s.compile 0 ++ [.ret false]

end Stmt

end Podc.PPDoubleExpThresholds
