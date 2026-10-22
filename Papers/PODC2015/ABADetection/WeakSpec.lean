import Papers.PODC2015.ABADetection.Defs
import Cslib.Computability.Distributed.SharedMemory.Atomic

/-!
# The paper's literal `WeakRead()/WeakWrite()` condition is not implied by linearizability

Section 2 of the paper specifies `WeakRead()`/`WeakWrite()` by: *"a `WeakRead()` operation `r` by
process `p` returns `True` if and only if there exists a `WeakWrite()` operation `w` such that
`w` happens before `r` and every other `WeakRead()` operation by `p` happens before `w`"*, and
claims that *"linearizability of an ABA-detecting register `R` guarantees that [`R.DRead()` and
`R.DWrite()` used as `WeakRead()`/`WeakWrite()`] satisfy the correctness properties above"*.

Read literally, this is false, for two independent reasons (`WeakSpecLiteral` is the literal
condition):

1. `weakSpecLiteral_not_of_linearizable_concurrent`: a `DRead()` that is concurrent with a
   `DWrite()` and linearized after it returns flag `true`, although no write *happens before* it.
2. `weakSpecLiteral_not_of_linearizable_later_read`: in the sequential history
   `DWrite(); DRead() → true; DRead() → false`, the first read returns `true`, but "every other
   `WeakRead()` by `p`" includes the *later* read, which does not happen before the write.

Both histories are executions of the trivial atomic implementation of the ABA-detecting register
(`atomicImpl`, which is linearizable and wait-free), with writer `0` and reader `1`.

The proofs of Section 2 only use the special cases of the condition that do hold for
linearizable implementations (the reader's *last* previous read, and operations that are not
concurrent): see `separates_aba` (Observation 1) in `Observation.lean`, which is proved directly
from linearizability. The intended condition is presumably "… every *earlier* `WeakRead()` by `p`
happens before `w`", for reads that are not concurrent with a write.
-/

set_option linter.unusedSectionVars false

namespace Cslib.SharedMemory.ABADetection

open Cslib.SharedMemory

section Def

variable {P V : Type} [DecidableEq P] {v₀ : V}

/-- The paper's literal correctness condition for `WeakRead()`/`WeakWrite()` (Section 2),
for `DRead()`/`DWrite()` of an ABA-detecting register: a completed `DRead()` instance `(p, k)` of
`p` returns flag `true` iff some `DWrite()` instance `w` happens before it and every other
`DRead()` instance of `p` happens before `w`. -/
def WeakSpecLiteral (α : List (Label P (abaObj P V v₀))) : Prop :=
  ∀ p k res, opOf α (p, k) = some (.dread p) → respOf α (p, k) = some res →
    (res.2 = true ↔ ∃ w x, opOf α w = some (.dwrite x) ∧ Completed α w ∧ Precedes α w (p, k) ∧
      ∀ k', k' ≠ k → opOf α (p, k') = some (.dread p) → Precedes α (p, k') w)

end Def

/-! ## The counterexamples -/

/-- The ABA-detecting register over `Bool` for two processes (`0` is the writer, `1` the
reader). -/
abbrev Reg2 : ObjSpec := abaObj (Fin 2) Bool false

/-- The trivial atomic (linearizable, wait-free) implementation of `Reg2`. -/
abbrev atomicReg2 := atomicImpl Reg2 (false, false) (Fin 2)

instance (p : Fin 2) (o : Reg2.Op) : Decidable (atomicReg2.allowed p o) := isTrue trivial

lemma atomicReg2_linearizable : atomicReg2.Linearizable := Atomic.perfectHI.linearizable

lemma atomicReg2_waitFree : atomicReg2.WaitFree := Atomic.waitFree

/-- Execution 1: reader `1` invokes `DRead()`, then writer `0` performs `DWrite(true)`, then the
read takes effect and returns `(true, true)` (it is linearized after the write). -/
def execConcurrent : List (Label (Fin 2) Reg2) :=
  [.inv 1 (.dread 1), .inv 0 (.dwrite true), .tau 0, .ret 0 (true, true), .tau 1,
    .ret 1 (true, true)]

/-- Execution 2: `DWrite(true)`, then two sequential `DRead()`s of process `1`, returning
`(true, true)` and `(true, false)`. -/
def execLaterRead : List (Label (Fin 2) Reg2) :=
  [.inv 0 (.dwrite true), .tau 0, .ret 0 (true, true),
    .inv 1 (.dread 1), .tau 1, .ret 1 (true, true),
    .inv 1 (.dread 1), .tau 1, .ret 1 (true, false)]

lemma execConcurrent_valid : atomicReg2.Valid execConcurrent :=
  Impl.valid_of_crun _ (by decide)

lemma execLaterRead_valid : atomicReg2.Valid execLaterRead :=
  Impl.valid_of_crun _ (by decide)

/-- **The literal `WeakRead()` condition fails for linearizable implementations (1)**: the
first counterexample, a read that is concurrent with a write. -/
theorem weakSpecLiteral_not_of_linearizable_concurrent :
    atomicReg2.Linearizable ∧ atomicReg2.WaitFree ∧ atomicReg2.Valid execConcurrent ∧
      (∃ L, IsLinearization execConcurrent L) ∧ ¬ WeakSpecLiteral execConcurrent := by
  obtain ⟨h, hh⟩ := atomicReg2_linearizable
  refine ⟨⟨h, hh⟩, atomicReg2_waitFree, execConcurrent_valid,
    ⟨_, hh _ execConcurrent_valid⟩, fun hw => ?_⟩
  obtain ⟨w, x, hwo, -, hpre, -⟩ :=
    (hw 1 0 (true, true) (by decide) (by decide)).1 rfl
  have hw0 : w = (0, 0) := by
    obtain ⟨q, i⟩ := w
    fin_cases q <;> rcases i with _ | _ | i <;> simp_all [opOf, execConcurrent]
  subst hw0
  exact Precedes.not_of_invoked (α := execConcurrent.take 1) (β := execConcurrent.drop 1)
    (a := (0, 0)) (b := (1, 0))
    (by simp [Invoked, execConcurrent]) (by simp [Completed, execConcurrent])
    (by rwa [List.take_append_drop])

/-- **The literal `WeakRead()` condition fails for linearizable implementations (2)**: the
second counterexample, a sequential history in which the first read returns `true` but a later
read of the same process does not happen before the write. -/
theorem weakSpecLiteral_not_of_linearizable_later_read :
    atomicReg2.Linearizable ∧ atomicReg2.WaitFree ∧ atomicReg2.Valid execLaterRead ∧
      (∃ L, IsLinearization execLaterRead L) ∧ ¬ WeakSpecLiteral execLaterRead := by
  obtain ⟨h, hh⟩ := atomicReg2_linearizable
  refine ⟨⟨h, hh⟩, atomicReg2_waitFree, execLaterRead_valid,
    ⟨_, hh _ execLaterRead_valid⟩, fun hw => ?_⟩
  obtain ⟨w, x, hwo, -, -, hother⟩ :=
    (hw 1 0 (true, true) (by decide) (by decide)).1 rfl
  have hw0 : w = (0, 0) := by
    obtain ⟨q, i⟩ := w
    fin_cases q <;> rcases i with _ | _ | i <;> simp_all [opOf, execLaterRead]
  subst hw0
  have hpre := hother 1 (by decide) (by decide)
  exact Precedes.not_of_invoked (α := execLaterRead.take 1) (β := execLaterRead.drop 1)
    (a := (1, 1)) (b := (0, 0))
    (by simp [Invoked, execLaterRead]) (by simp [Completed, execLaterRead])
    (by rwa [List.take_append_drop])

end Cslib.SharedMemory.ABADetection
