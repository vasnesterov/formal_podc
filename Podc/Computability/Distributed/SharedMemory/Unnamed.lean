/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

import Cslib.Computability.Distributed.SharedMemory.FullInfo
import Cslib.Computability.Distributed.SharedMemory.Covering

/-!
# Unnamed (memory-anonymous) read/write registers

Model of Taubenfeld, *Coordination Without Prior Agreement* (PODC 2017): processes communicate
through atomic read/write registers that have no global names. Each process `p` numbers the
registers privately; an adversary chooses the numbering `π p : Equiv.Perm ι`, and a process using
the local name `i` accesses the physical register `π p i`. All registers start with the same value
`v₀` (otherwise the initial values would act as names).

An algorithm is an ordinary read/write algorithm `I : Impl A (RegFamily ι V v₀) P L` written in
local register names; `I.unnamed π` is the implementation actually run under the numbering `π`.
A memory-anonymous algorithm solves a problem iff `I.unnamed π` does for **every** `π`.

Process code may depend on the process (`I.act p`), so non-symmetric algorithms are covered.

## Main definitions

* `Impl.unnamed I π`: run `I` with private register numberings `π`.

## Main results

* `Impl.unnamed_step_congr`, `Impl.unnamed_runFrom_congr`: an execution only depends on the
  numberings of the processes that take steps in it.

CSLib candidate.
-/

set_option linter.unusedSectionVars false

namespace Cslib.SharedMemory

variable {A : ObjSpec} {ι V P L : Type} {v₀ : V}

namespace Impl

/-- Run the read/write algorithm `I` (written in local register names) with the private register
numberings `π`: when `p` uses the local name `i` it accesses the physical register `π p i`. All
registers start with the common value `v₀`. -/
def unnamed (I : Impl A (RegFamily ι V v₀) P L) (π : P → Equiv.Perm ι) :
    Impl A (RegFamily ι V v₀) P L where
  memInit _ := v₀
  locInit := I.locInit
  invoke := I.invoke
  act p l := match I.act p l with
    | .access i o k => .access (π p i) o k
    | .ret r l' => .ret r l'
  allowed := I.allowed

variable (I : Impl A (RegFamily ι V v₀) P L) (π : P → Equiv.Perm ι)

@[simp] lemma unnamed_memInit (i : ι) : (I.unnamed π).memInit i = v₀ := rfl
@[simp] lemma unnamed_locInit : (I.unnamed π).locInit = I.locInit := rfl
@[simp] lemma unnamed_invoke : (I.unnamed π).invoke = I.invoke := rfl
@[simp] lemma unnamed_allowed : (I.unnamed π).allowed = I.allowed := rfl

lemma unnamed_act_access {p : P} {l : L} {i : ι} {o : RWOp V} {k : V → L}
    (h : I.act p l = .access i o k) : (I.unnamed π).act p l = .access (π p i) o k := by
  simp [unnamed, h]

lemma unnamed_act_ret {p : P} {l l' : L} {r : A.Resp} (h : I.act p l = .ret r l') :
    (I.unnamed π).act p l = .ret r l' := by
  simp [unnamed, h]

@[simp] lemma unnamed_initCfg [DecidableEq P] [DecidableEq ι] :
    (I.unnamed π).initCfg = ⟨I.locInit, fun _ => none, fun _ => v₀⟩ := rfl

variable [DecidableEq P] [DecidableEq ι]

/-- The code of a process only depends on its own numbering. -/
lemma unnamed_act_congr {π π' : P → Equiv.Perm ι} {p : P} (h : π p = π' p) :
    (I.unnamed π).act p = (I.unnamed π').act p := by
  funext l; simp only [unnamed]; cases I.act p l <;> simp [h]

/-- A step only depends on the numbering of the stepping process. -/
lemma unnamed_step_congr {π π' : P → Equiv.Perm ι} {ℓ : Label P A} (h : π ℓ.proc = π' ℓ.proc)
    (C : Config A (RegFamily ι V v₀) P L) :
    (I.unnamed π).step C ℓ = (I.unnamed π').step C ℓ := by
  have hact := I.unnamed_act_congr h
  cases ℓ with
  | inv p o => rfl
  | tau p => simp only [Label.proc] at hact; simp only [step, hact]
  | ret p r => simp only [Label.proc] at hact; simp only [step, hact]

/-- An execution only depends on the numberings of the processes that take steps in it. -/
lemma unnamed_runFrom_congr {π π' : P → Equiv.Perm ι} {β : List (Label P A)}
    (h : ∀ ℓ ∈ β, π ℓ.proc = π' ℓ.proc) (C : Config A (RegFamily ι V v₀) P L) :
    (I.unnamed π).runFrom C β = (I.unnamed π').runFrom C β := by
  induction β generalizing C with
  | nil => rfl
  | cons ℓ β ih =>
    simp only [runFrom_cons, I.unnamed_step_congr (h ℓ (by simp)) C]
    congr 1; funext C'; exact ih (fun ℓ' hℓ' => h ℓ' (by simp [hℓ'])) C'

end Impl

end Cslib.SharedMemory
