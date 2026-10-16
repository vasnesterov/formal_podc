import Papers.PODC2021.ScannableBinaryObjects.Main
import Cslib.Computability.Distributed.SharedMemory.Atomic

/-!
# Degenerate case `k = 1`

With a single component, the scannable object itself is a 1-bit object, so the trivial atomic
implementation (one base object of the object's own type, CSLib `atomicImpl`) is a wait-free,
linearizable, multi-updater, multi-scanner implementation from **one** 1-bit base object, for any
number of processes. Hence:

* the hypothesis `k ≥ 2` of Lemma 6 is necessary (it would claim `k + 1 = 2` objects);
* the abstract's claim "when `n ≤ 2^(k-1) + 2`, a lower bound of `n + k - 2` base objects" fails
  for `k = 1`, `n = 3` (it would claim `2`). The body of the paper (Theorem 8, Corollary 9)
  assumes `k ≥ 3`, so this only affects the abstract/introduction.

`regBit` is a readable, non-monotonic 1-bit object (read / write), so the example satisfies all
hypotheses of the paper, including readability of the components.
-/

set_option linter.unusedSectionVars false

namespace Cslib.SharedMemory.Scannable

open Cslib.SharedMemory

/-- A binary read/write register as a 1-bit object: `none` reads, `some b` writes `b`; the
response is the old value. -/
def regBit : BitObj where
  Op := Option Bool
  Resp := Bool
  δ v o := (o.getD v, v)

lemma regBit_nonMonotonic : regBit.NonMonotonic :=
  ⟨⟨some true, rfl⟩, ⟨some false, rfl⟩⟩

/-- **`k = 1`: one base object suffices** for any set of processes: the atomic implementation of
the one-component scannable object is linearizable, obstruction-free (even wait-free), allows
every invocation, and its single base object stores one bit. -/
theorem one_component_one_object (P : Type) [DecidableEq P] (p₀ : P) :
    let O : Fin 1 → BitObj := fun _ => regBit
    let I := atomicImpl (scannable O) (.view fun _ => false) P
    (∀ c, (O c).NonMonotonic) ∧ (∀ p o, SingleUpdater p₀ p o → I.allowed p o) ∧
      I.Linearizable ∧ I.ObstructionFree ∧ (∀ i, OneBit ((fun _ : Unit => scannable O) i).State) ∧
      Fintype.card Unit = 1 := by
  intro O I
  refine ⟨fun _ => regBit_nonMonotonic, fun _ _ _ => trivial, ?_, ?_, ?_, rfl⟩
  · exact Impl.HIwrt.linearizable _ Atomic.perfectHI
  · exact Impl.WaitFree.obstructionFree _ Atomic.waitFree
  · intro _
    exact ⟨fun v => v 0, fun v w h => funext fun c => by
      rw [Subsingleton.elim c 0]; exact h⟩

/-- Consequently the bound `n + k - 2` of the abstract fails for `k = 1`, `n = 3`, and Lemma 6's
bound `k + 1` fails for `k = 1`. -/
theorem abstract_bound_fails_k1 :
    ∃ (P : Type) (_ : DecidableEq P) (_ : Fintype P) (p₀ : P) (O : Fin 1 → BitObj)
      (I : Impl (scannable O) (fun _ : Unit => scannable O) P
        (AtomicLoc (scannable O))),
      Fintype.card P = 3 ∧ (∀ c, (O c).NonMonotonic) ∧
      (∀ p o, SingleUpdater p₀ p o → I.allowed p o) ∧ I.Linearizable ∧ I.ObstructionFree ∧
      (∀ i, OneBit ((fun _ : Unit => scannable O) i).State) ∧
      Fintype.card Unit < Fintype.card P + 1 - 2 ∧ Fintype.card Unit < 1 + 1 := by
  obtain ⟨h1, h2, h3, h4, h5, -⟩ := one_component_one_object (Fin 3) 0
  exact ⟨Fin 3, inferInstance, inferInstance, 0, _, _, rfl, h1, h2, h3, h4, h5, by decide,
    by decide⟩

end Cslib.SharedMemory.Scannable
