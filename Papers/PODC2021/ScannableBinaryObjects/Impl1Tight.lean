import Papers.PODC2021.ScannableBinaryObjects.Impl1LockFree
import Papers.PODC2021.ScannableBinaryObjects.Main

/-!
# Theorem 2 of Ovens (PODC 2021) and tightness of Lemma 6 for two processes

* `impl1_theorem2`: Implementation 1 is a linearizable, lock-free (hence obstruction-free)
  `s`-scanner `u`-updater implementation from `s + k` one-bit base objects.
* `impl1_nScanner_nUpdater`: every process scans and updates, `n + k` base objects.
* `impl1_singleScanner`: one scanner, any updaters, `k + 1` base objects.
* `impl1_singleUpdater`: the single-updater setting of the lower bounds (`p₀` updates, everybody
  else scans), `(n - 1) + k` base objects.
* `two_process_tight`: for two processes, `k ≥ 2` readable non-monotonic components, the
  minimum number of one-bit base objects of an obstruction-free linearizable single-updater
  implementation is exactly `k + 1` (Implementation 1 vs. Lemma 6).
-/

set_option linter.unusedSectionVars false

namespace Cslib.SharedMemory.Scannable

open Impl1

variable {k : ℕ} {O : Fin k → BitObj} {P : Type} [DecidableEq P]

/-- Implementation 1 uses `s + k` base objects. -/
theorem impl1_card (Sc : Finset P) : Fintype.card (Fin k ⊕ Sc) = Sc.card + k := by
  simp [Fintype.card_sum, add_comm]

/-- Every base object of Implementation 1 stores one bit. -/
theorem impl1_oneBit (Sc : Finset P) (x : Fin k ⊕ Sc) : OneBit (Obj O Sc x).State := by
  cases x with
  | inl i => exact ⟨id, Function.injective_id⟩
  | inr j => exact ⟨id, Function.injective_id⟩

/-- The access discipline of Implementation 1: scanners scan, updaters update. -/
theorem impl1_allowed (R : ∀ i, (O i).Readable) (Sc Up : Finset P) (h₀ : Sc → Bool) (p : P)
    (o : ScanOp O) : (impl1 R Sc Up h₀).allowed p o ↔
      (o.isScan = true → p ∈ Sc) ∧ (o.isScan = false → p ∈ Up) := by
  cases o <;> simp [impl1, ScanOp.isScan]

/-- **Theorem 2 of Ovens (PODC 2021).** Implementation 1 is a lock-free, linearizable,
`s`-scanner, `u`-updater implementation of `[O 0, …, O (k-1)]` from `s + k` one-bit base
objects (`s = |Sc|`; `u = |Up|` enters only the algorithm). -/
theorem impl1_theorem2 [Fintype P] (R : ∀ i, (O i).Readable) (Sc Up : Finset P)
    (h₀ : Sc → Bool) :
    (impl1 R Sc Up h₀).Linearizable ∧ (impl1 R Sc Up h₀).LockFree ∧
      (impl1 R Sc Up h₀).ObstructionFree ∧ (∀ x, OneBit (Obj O Sc x).State) ∧
      Fintype.card (Fin k ⊕ Sc) = Sc.card + k :=
  ⟨impl1_linearizable R Sc Up h₀, impl1_lockFree R Sc Up h₀, impl1_obstructionFree R Sc Up h₀,
    impl1_oneBit Sc, impl1_card Sc⟩

/-- `n`-scanner, `n`-updater implementation from `n + k` one-bit base objects. -/
theorem impl1_nScanner_nUpdater [Fintype P] (R : ∀ i, (O i).Readable) (h₀ : _ → Bool) :
    let I := impl1 R (Finset.univ : Finset P) Finset.univ h₀
    (∀ p o, I.allowed p o) ∧ I.Linearizable ∧ I.LockFree ∧
      (∀ x, OneBit (Obj O (Finset.univ : Finset P) x).State) ∧
      Fintype.card (Fin k ⊕ (Finset.univ : Finset P)) = Fintype.card P + k := by
  refine ⟨fun p o => by cases o <;> simp [impl1], impl1_linearizable _ _ _ _,
    impl1_lockFree _ _ _ _, impl1_oneBit _, by rw [impl1_card, Finset.card_univ]⟩

/-- Single-scanner implementation (scanner `p₁`, any updaters) from `k + 1` one-bit base
objects. -/
theorem impl1_singleScanner [Fintype P] (R : ∀ i, (O i).Readable) (p₁ : P) (Up : Finset P)
    (h₀ : _ → Bool) :
    let I := impl1 R {p₁} Up h₀
    (∀ p o, (o.isScan = true → p = p₁) → (o.isScan = false → p ∈ Up) → I.allowed p o) ∧
      I.Linearizable ∧ I.LockFree ∧ (∀ x, OneBit (Obj O {p₁} x).State) ∧
      Fintype.card (Fin k ⊕ ({p₁} : Finset P)) = k + 1 := by
  refine ⟨fun p o h1 h2 => (impl1_allowed _ _ _ _ p o).2 ⟨fun h => by simp [h1 h], h2⟩,
    impl1_linearizable _ _ _ _, impl1_lockFree _ _ _ _, impl1_oneBit _, ?_⟩
  rw [impl1_card]; simp [add_comm]

/-- The single-updater setting of the lower bounds: `p₀` is the only updater and every other
process is a scanner; `(n - 1) + k` one-bit base objects. -/
theorem impl1_singleUpdater [Fintype P] (R : ∀ i, (O i).Readable) (p₀ : P) (h₀ : _ → Bool) :
    let I := impl1 R (Finset.univ.erase p₀) {p₀} h₀
    (∀ p o, SingleUpdater p₀ p o → I.allowed p o) ∧ I.Linearizable ∧ I.LockFree ∧
      I.ObstructionFree ∧ (∀ x, OneBit (Obj O (Finset.univ.erase p₀) x).State) ∧
      Fintype.card (Fin k ⊕ (Finset.univ.erase p₀ : Finset P)) = (Fintype.card P - 1) + k := by
  refine ⟨fun p o h => ?_, impl1_linearizable _ _ _ _, impl1_lockFree _ _ _ _,
    impl1_obstructionFree _ _ _ _, impl1_oneBit _, ?_⟩
  · cases o <;> simp_all [impl1, SingleUpdater]
  · rw [impl1_card, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]

/-- **Tightness for two processes.** With two processes, `k ≥ 2` readable non-monotonic
components and updater `p₀`: (1) Implementation 1 is an obstruction-free (even lock-free),
linearizable implementation allowing the single-updater invocations from `k + 1` one-bit base
objects; (2) by Lemma 6, every such implementation needs at least `k + 1` base objects. -/
theorem two_process_tight [Fintype P] (hP : Fintype.card P = 2) (R : ∀ i, (O i).Readable)
    (hnm : ∀ c, (O c).NonMonotonic) (hk : 2 ≤ k) (p₀ : P) :
    (∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι) (B : ι → ObjSpec) (L : Type)
      (I : Impl (scannable O) B P L),
      (∀ p o, SingleUpdater p₀ p o → I.allowed p o) ∧ I.Linearizable ∧ I.LockFree ∧
        I.ObstructionFree ∧ (∀ i, OneBit (B i).State) ∧ Fintype.card ι = k + 1) ∧
    (∀ (ι : Type) [Fintype ι] [DecidableEq ι] (B : ι → ObjSpec) (L : Type)
      (I : Impl (scannable O) B P L),
      (∀ p o, SingleUpdater p₀ p o → I.allowed p o) → I.Linearizable → I.ObstructionFree →
        (∀ i, OneBit (B i).State) → k + 1 ≤ Fintype.card ι) := by
  refine ⟨?_, fun ι _ _ B L I hall hlin hof hbit =>
    lemma6 I p₀ hall hlin hof hbit hnm hk (by omega)⟩
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := impl1_singleUpdater R p₀ (fun _ => false)
  exact ⟨_, inferInstance, inferInstance, _, _, _, h1, h2, h3, h4, h5, by rw [h6, hP]; omega⟩

end Cslib.SharedMemory.Scannable
