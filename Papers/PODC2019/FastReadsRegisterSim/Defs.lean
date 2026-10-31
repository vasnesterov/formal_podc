import Cslib.Computability.Distributed.SharedMemory.Covering
import Cslib.Computability.Distributed.SharedMemory.Linearization
import Cslib.Computability.Distributed.SharedMemory.Progress
import Mathlib

/-!
# How fast reads affect multi-valued register simulations (Chaudhuri–Frank–Welch, PODC 2019 BA)

## Model

CSLib's asynchronous shared-memory model (`Cslib.SharedMemory.Impl`): deterministic processes,
atomic base objects, executions as lists of labels `inv p o` / `tau p` / `ret p r`; a `tau` step
is one access to one base object. Here:

* the implemented (high-level) object is a `V`-valued read/write register with initial value
  `v₀` (`register V v₀`), `|V| = k`;
* the base objects are **atomic binary registers** indexed by an arbitrary type `ι`
  (`BinRegs ι`); their initial values are given by the implementation (`memInit`);
* a *simulation* is `I : Sim V v₀ ι P L` (`= Impl (register V v₀) (BinRegs ι) P L`);
* one process `w` writes, the others read (single writer, any number of readers).

## Consistency conditions (Lamport)

Stated on histories (`SafeHist`, `RegularHist`, `AtomicHist`) and for simulations
(`Sim.Safe`, `Sim.Regular`, `Sim.Atomic`): the condition must hold in every finite execution in
which only `w` writes.

* *regular value* of a completed read `x` (`RegularValue`): `v₀` if no write precedes `x`, or the
  value of a write that does not follow `x` and is not overwritten by a write that precedes `x`
  (= the value of an overlapping write or of the latest preceding write);
* *safe*: every read that overlaps no write returns a regular value (then: the value of the latest
  preceding write);
* *regular*: every read returns a regular value;
* *atomic*: the history is linearizable (CSLib `IsLinearization`).

## Costs

`Sim.accesses C α` lists the base accesses `(process, register, primitive)` performed by the
labels `α` run from `C`. `ReadReadsLE I p t` / `ReadStepsLE I p t`: every read operation of `p`
performs at most `t` base reads / steps. `WriteWritesGE I w t`: some write operation of `w`
performs at least `t` base writes.
-/

namespace Podc.FastReadsRegisterSim

open Cslib.SharedMemory

/-- Base objects: binary registers indexed by `ι`. -/
abbrev BinRegs (ι : Type) : ι → ObjSpec := fun _ => binaryRegister

/-- A simulation of a `V`-valued register with initial value `v₀` from binary registers `ι`,
for processes `P` with local states `L`. -/
abbrev Sim (V : Type) (v₀ : V) (ι P L : Type) := Impl (register V v₀) (BinRegs ι) P L

variable {V : Type} {v₀ : V} {ι P L : Type} [DecidableEq P] [DecidableEq ι]

/-! ## Consistency conditions -/

section History

variable (v₀)

/-- `y` is a write instance of value `v` in the history `α`. -/
def IsWrite (α : List (Label P (register V v₀))) (y : OpId P) (v : V) : Prop :=
  opOf α y = some (RWOp.write v)

/-- `x` is a completed read instance of `α` that returned `v`. -/
def ReadReturns (α : List (Label P (register V v₀))) (x : OpId P) (v : V) : Prop :=
  opOf α x = some RWOp.read ∧ respOf α x = some v

/-- Only `w` writes in `α`. -/
def SingleWriter (α : List (Label P (register V v₀))) (w : P) : Prop :=
  ∀ y v, IsWrite v₀ α y v → y.1 = w

/-- `v` is a legal value for the read `x` under regularity: the initial value if no write
precedes `x`, or the value of a write `y` that does not follow `x` and is not overwritten by a
write `y'` with `y → y' → x`. -/
def RegularValue (α : List (Label P (register V v₀))) (x : OpId P) (v : V) : Prop :=
  (v = v₀ ∧ ∀ y u, IsWrite v₀ α y u → ¬ Precedes α y x) ∨
  ∃ y, IsWrite v₀ α y v ∧ ¬ Precedes α x y ∧
    ∀ y' u, IsWrite v₀ α y' u → ¬ (Precedes α y y' ∧ Precedes α y' x)

/-- **Safety**: a read that overlaps no write returns the value of the latest preceding write
(the initial value if there is none). -/
def SafeHist (α : List (Label P (register V v₀))) : Prop :=
  ∀ x v, ReadReturns v₀ α x v → (∀ y u, IsWrite v₀ α y u → Precedes α y x ∨ Precedes α x y) →
    RegularValue v₀ α x v

/-- **Regularity**: every read returns the value of an overlapping write or of the latest
preceding write (the initial value if no write precedes it). -/
def RegularHist (α : List (Label P (register V v₀))) : Prop :=
  ∀ x v, ReadReturns v₀ α x v → RegularValue v₀ α x v

/-- **Atomicity**: the history is linearizable. -/
def AtomicHist (α : List (Label P (register V v₀))) : Prop :=
  ∃ Lin, IsLinearization α Lin

end History

namespace Sim

/-- The simulation is safe (for writer `w`). -/
def Safe (I : Sim V v₀ ι P L) (w : P) : Prop :=
  ∀ α, I.Valid α → SingleWriter v₀ α w → SafeHist v₀ α

/-- The simulation is regular (for writer `w`). -/
def Regular (I : Sim V v₀ ι P L) (w : P) : Prop :=
  ∀ α, I.Valid α → SingleWriter v₀ α w → RegularHist v₀ α

/-- The simulation is atomic (for writer `w`). -/
def Atomic (I : Sim V v₀ ι P L) (w : P) : Prop :=
  ∀ α, I.Valid α → SingleWriter v₀ α w → AtomicHist v₀ α

/-! ## Costs -/

/-- The base access performed by the label `ℓ` from configuration `C` (empty unless `ℓ` is a
`tau` step that accesses a base register). -/
def accessOf (I : Sim V v₀ ι P L) (C : Config (register V v₀) (BinRegs ι) P L) :
    Label P (register V v₀) → List (P × ι × RWOp Bool)
  | .tau p =>
    match I.act p (C.loc p) with
    | .access i o _ => [(p, i, o)]
    | .ret _ _ => []
  | _ => []

/-- The base accesses `(process, register, primitive)` performed by the labels `α` run from
`C`. -/
noncomputable def accesses (I : Sim V v₀ ι P L) :
    Config (register V v₀) (BinRegs ι) P L → List (Label P (register V v₀)) →
      List (P × ι × RWOp Bool)
  | _, [] => []
  | C, ℓ :: α => I.accessOf C ℓ ++ accesses I ((I.step C ℓ).getD C) α

end Sim

/-- Number of base reads of process `p` in a list of accesses. -/
def numReads (p : P) (as : List (P × ι × RWOp Bool)) : ℕ :=
  as.countP (fun a => a.1 = p ∧ a.2.2 = .read)

/-- Number of base writes of process `p` in a list of accesses. -/
def numWrites (p : P) (as : List (P × ι × RWOp Bool)) : ℕ :=
  as.countP (fun a => a.1 = p ∧ a.2.2 ≠ .read)

/-- Number of steps (base accesses) of process `p` in a list of accesses. -/
def numSteps (p : P) (as : List (P × ι × RWOp Bool)) : ℕ :=
  as.countP (fun a => a.1 = p)

namespace Sim

/-- Every read operation of `p` performs at most `t` base reads: whenever `p` invokes a read
after `α₁` (reaching `C`), the labels `α₂` that follow before its response contain at most `t`
base reads of `p`. -/
def ReadReadsLE (I : Sim V v₀ ι P L) (p : P) (t : ℕ) : Prop :=
  ∀ α₁ α₂ C, I.run α₁ = some C → I.Valid (α₁ ++ .inv p .read :: α₂) →
    (∀ v, Label.ret p v ∉ α₂) → numReads p (I.accesses C (.inv p .read :: α₂)) ≤ t

/-- Every read operation of `p` takes at most `t` steps. -/
def ReadStepsLE (I : Sim V v₀ ι P L) (p : P) (t : ℕ) : Prop :=
  ∀ α₁ α₂ C, I.run α₁ = some C → I.Valid (α₁ ++ .inv p .read :: α₂) →
    (∀ v, Label.ret p v ∉ α₂) → numSteps p (I.accesses C (.inv p .read :: α₂)) ≤ t

/-- Some read operation of `p` performs at least `t` base reads. -/
def SomeReadReadsGE (I : Sim V v₀ ι P L) (p : P) (t : ℕ) : Prop :=
  ∃ α₁ α₂ C, I.run α₁ = some C ∧ I.Valid (α₁ ++ .inv p .read :: α₂) ∧
    (∀ v, Label.ret p v ∉ α₂) ∧ t ≤ numReads p (I.accesses C (.inv p .read :: α₂))

/-- Some write operation of `w` performs at least `t` base writes. -/
def SomeWriteWritesGE (I : Sim V v₀ ι P L) (w : P) (t : ℕ) : Prop :=
  ∃ α₁ α₂ C v, I.run α₁ = some C ∧ I.Valid (α₁ ++ .inv w (.write v) :: α₂) ∧
    (∀ u, Label.ret w u ∉ α₂) ∧ t ≤ numWrites w (I.accesses C (.inv w (.write v) :: α₂))

end Sim

end Podc.FastReadsRegisterSim
