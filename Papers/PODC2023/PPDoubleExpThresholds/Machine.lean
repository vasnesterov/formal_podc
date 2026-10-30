import Papers.PODC2023.PPDoubleExpThresholds.Stable
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Order.Interval.Finset.Nat

/-!
# Population machines (Definitions 6 and 13)

A population machine `A = (Q, F, 𝓕, I)` has a finite set of registers `Q` (values in `ℕ`), a finite
set of pointers `F`, a finite nonempty domain `𝓕_X` for each pointer and a sequence of instructions
`I = (I₁, …, I_L)`. Pointer values of all pointers live in one type `Val Q` (booleans, instruction
addresses `ℕ`, registers `Q`), and `𝓕_X` is a `Finset (Val Q)`.

There are special pointers: the output flag `OF`, the condition flag `CF`, the instruction pointer
`IP`, and a register-map pointer `V x` for every `x ∈ Q ∪ {□}` (we write `V (some x)` for `V_x` and
`V none` for `V_□`). Requirements (Definition 6): `𝓕_OF = 𝓕_CF = {false, true}`,
`𝓕_IP = {1, …, L}`, `x ∈ 𝓕_{V_x} ⊆ Q` (and `𝓕_{V_□} ⊆ Q` nonempty).

Instructions (`x ≠ y`, `f : 𝓕_Y → 𝓕_X`): `x ↦ y`, `detect x > 0`, `X := f(Y)`.

Semantics (Definition 13): a configuration maps registers to `ℕ` and pointers to values; the
instruction executed is `I_{C(IP)}`; registers are accessed through the register map, i.e.
`x ↦ y` moves a unit from register `C(V_x)` to register `C(V_y)`. If no configuration
`C' ≠ C` is a successor, `C → C` (so `→` is left-total; the machine *hangs*).
Initial configurations: `C(IP) = 1` and `C(V_x) = x` for all `x ∈ Q`. The output of `C` is `C(OF)`.
`A` decides `φ` if every fair run from an initial configuration `C` stabilises to
`φ(∑_{q ∈ Q} C(q))`.
-/

namespace Podc.PPDoubleExpThresholds

open Cslib.TransitionSystem

/-- Pointer values: booleans, natural numbers (instruction addresses) and registers. -/
inductive Val (Q : Type*)
  | bool (b : Bool)
  | nat (n : ℕ)
  | reg (q : Q)
  deriving DecidableEq

/-- Instructions of a population machine over registers `Q` and pointers `F`. -/
inductive MInstr (Q F : Type*)
  /-- `x ↦ y`: move one unit from (the register referred to by) `x` to `y`. -/
  | move (x y : Q)
  /-- `detect x > 0`: set `CF` to `false` or to `x > 0`, nondeterministically. -/
  | detect (x : Q)
  /-- `X := f(Y)`. -/
  | assign (X Y : F) (f : Val Q → Val Q)

/-- A population machine (Definition 6). The instruction list `instrs` is `I₁, …, I_L`
(`I_i = instrs[i - 1]`). -/
structure Machine (Q F : Type*) [Fintype Q] [Fintype F] [DecidableEq Q] where
  /-- The pointer domains `𝓕_X`. -/
  dom : F → Finset (Val Q)
  /-- The instructions `I₁, …, I_L`. -/
  instrs : List (MInstr Q F)
  /-- The output flag. -/
  OF : F
  /-- The condition flag. -/
  CF : F
  /-- The instruction pointer. -/
  IP : F
  /-- The register map: `V (some x) = V_x`, `V none = V_□`. -/
  V : Option Q → F
  OF_ne_CF : OF ≠ CF
  OF_ne_IP : OF ≠ IP
  CF_ne_IP : CF ≠ IP
  V_inj : Function.Injective V
  V_ne_OF : ∀ x, V x ≠ OF
  V_ne_CF : ∀ x, V x ≠ CF
  V_ne_IP : ∀ x, V x ≠ IP
  dom_OF : dom OF = {Val.bool false, Val.bool true}
  dom_CF : dom CF = {Val.bool false, Val.bool true}
  dom_IP : dom IP = (Finset.Icc 1 instrs.length).map ⟨Val.nat, fun _ _ h => by cases h; rfl⟩
  dom_V : ∀ x, ∀ v ∈ dom (V x), ∃ q, v = .reg q
  mem_dom_V : ∀ x : Q, Val.reg x ∈ dom (V (some x))
  dom_V_none : (dom (V none)).Nonempty
  /-- Moves are between distinct registers. -/
  move_ne : ∀ x y, MInstr.move x y ∈ instrs → x ≠ y
  /-- `f : 𝓕_Y → 𝓕_X` maps the domain of `Y` into the domain of `X`. -/
  assign_mem : ∀ X Y f, MInstr.assign X Y f ∈ instrs → ∀ v ∈ dom Y, f v ∈ dom X

namespace Machine

variable {Q F : Type*} [Fintype Q] [Fintype F] [DecidableEq Q] [DecidableEq F]
variable (A : Machine Q F)

/-- The size `|Q| + |F| + ∑_X |𝓕_X| + |I|` of a machine. -/
def size : ℕ :=
  Fintype.card Q + Fintype.card F + ∑ X, (A.dom X).card + A.instrs.length

/-- Configurations: register values and pointer values. -/
structure Cfg (Q F : Type*) where
  /-- Register values. -/
  reg : Q → ℕ
  /-- Pointer values. -/
  ptr : F → Val Q

/-- The instruction `I_i` (`none` if `i ∉ {1, …, L}`). -/
def instr (i : ℕ) : Option (MInstr Q F) := if i = 0 then none else A.instrs[i - 1]?

/-- One step `C → C'` of Definition 13 that executes an instruction. -/
inductive Exec : Cfg Q F → Cfg Q F → Prop
  /-- `I_{C(IP)} = (x ↦ y)`: with `C(V_x) = u`, `C(V_y) = w`, a unit moves from `u` to `w`. -/
  | move {C : Cfg Q F} {i : ℕ} {x y u w : Q} (hi : C.ptr A.IP = .nat i)
      (hI : A.instr i = some (.move x y)) (hu : C.ptr (A.V (some x)) = .reg u)
      (hw : C.ptr (A.V (some y)) = .reg w) (hpos : 0 < C.reg u) :
      Exec C ⟨Function.update (Function.update C.reg u (C.reg u - 1)) w
        (Function.update C.reg u (C.reg u - 1) w + 1),
        Function.update C.ptr A.IP (.nat (i + 1))⟩
  /-- `I_{C(IP)} = (detect x > 0)`: `CF` becomes `false` or `C(C(V_x)) > 0`. -/
  | detect {C : Cfg Q F} {i : ℕ} {x u : Q} (hi : C.ptr A.IP = .nat i)
      (hI : A.instr i = some (.detect x)) (hu : C.ptr (A.V (some x)) = .reg u) (b : Bool)
      (hb : b = false ∨ b = decide (0 < C.reg u)) :
      Exec C ⟨C.reg, Function.update (Function.update C.ptr A.CF (.bool b)) A.IP (.nat (i + 1))⟩
  /-- `I_{C(IP)} = (X := f(Y))` with `X ≠ IP`. -/
  | assign {C : Cfg Q F} {i : ℕ} {X Y : F} {f : Val Q → Val Q} (hi : C.ptr A.IP = .nat i)
      (hI : A.instr i = some (.assign X Y f)) (hX : X ≠ A.IP) :
      Exec C ⟨C.reg, Function.update (Function.update C.ptr X (f (C.ptr Y))) A.IP (.nat (i + 1))⟩
  /-- `I_{C(IP)} = (IP := f(Y))`. -/
  | jump {C : Cfg Q F} {i : ℕ} {Y : F} {f : Val Q → Val Q} (hi : C.ptr A.IP = .nat i)
      (hI : A.instr i = some (.assign A.IP Y f)) :
      Exec C ⟨C.reg, Function.update C.ptr A.IP (f (C.ptr Y))⟩

/-- The step relation of Definition 13: an executed instruction, or `C → C` if `C` has no
successor `C' ≠ C`. -/
def Step (C C' : Cfg Q F) : Prop :=
  A.Exec C C' ∨ (C' = C ∧ ∀ C'', A.Exec C C'' → C'' = C)

/-- The output of a configuration is the value of `OF`. -/
def out (C : Cfg Q F) : Option Bool :=
  match C.ptr A.OF with
  | .bool b => some b
  | _ => none

/-- Initial configurations: `C(IP) = 1` and `C(V_x) = x` for all registers `x` (all other pointer
values arbitrary in their domains). -/
def IsInitial (C : Cfg Q F) : Prop :=
  C.ptr A.IP = .nat 1 ∧ (∀ x : Q, C.ptr (A.V (some x)) = .reg x) ∧ ∀ X, C.ptr X ∈ A.dom X

/-- The number of units in registers. -/
def total (C : Cfg Q F) : ℕ := ∑ q, C.reg q

/-- `A` decides `φ` (Definition 13): every fair run from an initial configuration `C` stabilises to
`φ(∑_q C(q))`. -/
def Decides (φ : ℕ → Bool) : Prop :=
  ∀ E : Run A.Step, A.IsInitial (E.st 0) → E.GloballyFair →
    StabilisesTo A.out E (φ (total (E.st 0)))

end Machine

end Podc.PPDoubleExpThresholds
