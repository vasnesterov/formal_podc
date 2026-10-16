import Papers.PODC2021.ScannableBinaryObjects.Lemma6

/-!
# Main lower bounds of Ovens (PODC 2021): Lemma 6, Theorem 8, Corollary 9

Model (see `README.md`): asynchronous shared memory (CSLib `Cslib.SharedMemory`), deterministic
processes `P` (`n = |P|`), base objects `ι` (`m = |ι|`) each storing at most one bit (`OneBit`,
arbitrary invocations, arbitrary initial values), an implementation `I` of the scannable binary
object `[O 0, …, O (k-1)]` (`scannable O`, all components initially `0`, every component an
arbitrary non-monotonic 1-bit object) that

* allows at least the single-updater invocations (`p₀` updates, every other process scans) —
  this covers single-updater as well as multi-updater/multi-scanner implementations,
* is linearizable (`Impl.Linearizable`) and obstruction-free (`Impl.ObstructionFree`).

All lower bounds are stated as `… ≤ Fintype.card ι`.
-/

set_option linter.unusedSectionVars false

namespace Cslib.SharedMemory.Scannable

open Cslib.SharedMemory

variable {k : ℕ} {O : Fin k → BitObj} {P : Type} [DecidableEq P]
  {ι : Type} [DecidableEq ι] {B : ι → ObjSpec} {L : Type} {I : Impl (scannable O) B P L} {p₀ : P}

section Stage

variable (hnm : ∀ c, (O c).NonMonotonic) (hof : I.ObstructionFree)
  (hall : ∀ p o, SingleUpdater p₀ p o → I.allowed p o) (hlin : I.Linearizable)
  (hbit : ∀ i, OneBit (B i).State) [Fintype ι]

include hnm hof hall hlin hbit in
/-- Theorem 8 for stages (induction on `r`, as in the paper). -/
theorem theorem8_stage (r : ℕ) : ∀ {ε X A F k'}, Stage I p₀ ε X A F k' → r + 3 ≤ k' →
    2 ^ k' - 2 ^ (k' - r) < A.card - 2 → A.card - 2 ≤ 2 ^ k' - 2 ^ (k' - r - 1) →
    F.card + A.card + k' - r - 2 ≤ Fintype.card ι := by
  induction r with
  | zero =>
    intro ε X A F k' hS hk h1 h2
    have hp : 2 ^ k' = 2 * 2 ^ (k' - 1) := by rw [← pow_succ']; congr 1; omega
    simp only [Nat.sub_zero] at h1 h2
    obtain ⟨ε', X', A', F', hS', hA', hF'⟩ :=
      reduce_stage hnm hof hall hlin hbit hS (by omega) (h := A.card - 2) (by omega) (by omega)
    have := lemma6_stage hnm hof hall hlin hbit hS' (by omega) (by omega)
    omega
  | succ r ih =>
    intro ε X A F k' hS hk h1 h2
    have hp : 2 ^ k' = 2 * 2 ^ (k' - 1) := by rw [← pow_succ']; congr 1; omega
    have e1 : k' - (r + 1) = k' - 1 - r := by omega
    have e2 : k' - (r + 1) - 1 = k' - 1 - r - 1 := by omega
    have hle1 : 2 ^ (k' - 1 - r) ≤ 2 ^ (k' - 1) := Nat.pow_le_pow_right (by omega) (by omega)
    have hle2 : 2 ^ (k' - 1 - r - 1) ≤ 2 ^ (k' - 1) := Nat.pow_le_pow_right (by omega) (by omega)
    have hpos : 0 < 2 ^ (k' - 1 - r - 1) := Nat.two_pow_pos _
    have hdbl : 2 ^ (k' - 1 - r) = 2 * 2 ^ (k' - 1 - r - 1) := by
      rw [← pow_succ']; congr 1; omega
    rw [e1] at h1; rw [e2] at h2
    obtain ⟨ε', X', A', F', hS', hA', hF'⟩ :=
      reduce_stage hnm hof hall hlin hbit hS (by omega) (h := 2 ^ (k' - 1)) (by omega) le_rfl
    have := ih hS' (by omega) (by omega) (by omega)
    omega

include hnm hof hall hlin hbit in
/-- Corollary 9 (c) for stages: `|A| ≥ 2^k' - 2` active processes force `2^k' - 1` objects
outside the frozen set (by induction on `k'`, which also covers all larger `|A|`). -/
theorem cor9c_stage : ∀ k', 2 ≤ k' → ∀ {ε X A F}, Stage I p₀ ε X A F k' →
    2 ^ k' - 2 ≤ A.card → F.card + 2 ^ k' - 1 ≤ Fintype.card ι := by
  intro k' hk
  induction k', hk using Nat.le_induction with
  | base =>
    intro ε X A F hS hA
    have := lemma6_stage hnm hof hall hlin hbit hS le_rfl (by simpa using hA)
    simp only [show (2 : ℕ) ^ 2 = 4 by rfl]; omega
  | succ k' hk ih =>
    intro ε X A F hS hA
    have hp : 2 ^ (k' + 1) = 2 * 2 ^ k' := by rw [pow_succ']
    have h4 : 4 ≤ 2 ^ k' := by
      calc 4 = 2 ^ 2 := rfl
        _ ≤ 2 ^ k' := Nat.pow_le_pow_right (by omega) hk
    obtain ⟨ε', X', A', F', hS', hA', hF'⟩ :=
      reduce_stage hnm hof hall hlin hbit hS (by omega) (h := 2 ^ k') (by omega) (by simp)
    have := ih (by simpa using hS') (by omega)
    omega

end Stage

/-! ### The paper's statements -/

section Paper

variable [Fintype P] [Fintype ι]

/-- **Lemma 6** (Ovens, PODC 2021). Any obstruction-free, linearizable, single-updater implementation
of a scannable binary object with `k ≥ 2` non-monotonic components for `n ≥ 2` processes from 1-bit
base objects uses at least `k + 1` base objects. -/
theorem lemma6 (I : Impl (scannable O) B P L) (p₀ : P)
    (hall : ∀ p o, SingleUpdater p₀ p o → I.allowed p o) (hlin : I.Linearizable)
    (hof : I.ObstructionFree) (hbit : ∀ i, OneBit (B i).State)
    (hnm : ∀ c, (O c).NonMonotonic) (hk : 2 ≤ k) (hn : 2 ≤ Fintype.card P) :
    k + 1 ≤ Fintype.card ι := by
  have := lemma6_stage hnm hof hall hlin hbit (stage_init I p₀ (by omega)) hk
    (by simpa using hn)
  simpa using this

/-- **Theorem 8** (Ovens, PODC 2021). Let `r ≥ 0`. For all `k, n` with `k ≥ r + 3` and
`2^k - 2^(k-r) < n - 2 ≤ 2^k - 2^(k-r-1)`, any obstruction-free, linearizable, single-updater,
`n`-process implementation of a scannable binary object with `k` non-monotonic components
requires at least `n + k - r - 2` instances of 1-bit base objects. -/
theorem theorem8 (I : Impl (scannable O) B P L) (p₀ : P)
    (hall : ∀ p o, SingleUpdater p₀ p o → I.allowed p o) (hlin : I.Linearizable)
    (hof : I.ObstructionFree) (hbit : ∀ i, OneBit (B i).State)
    (hnm : ∀ c, (O c).NonMonotonic) (r : ℕ) (hk : r + 3 ≤ k)
    (hn1 : 2 ^ k - 2 ^ (k - r) < Fintype.card P - 2)
    (hn2 : Fintype.card P - 2 ≤ 2 ^ k - 2 ^ (k - r - 1)) :
    Fintype.card P + k - r - 2 ≤ Fintype.card ι := by
  have := theorem8_stage hnm hof hall hlin hbit r (stage_init I p₀ (by omega)) hk
    (by simpa using hn1) (by simpa using hn2)
  simpa using this

/-- **Corollary 9** (Ovens, PODC 2021). For `k ≥ 3`, any obstruction-free, linearizable,
single-updater, `n`-process implementation of a scannable binary object with `k` non-monotonic
components from 1-bit base objects requires at least
(a) `k + 1` base objects when `n = 2` (in fact for all `n ≥ 2` and `k ≥ 2`, see `lemma6`),
(b) `n + k - 2` base objects when `2 < n ≤ 2^(k-1) + 2`, and
(c) `2^k - 1` base objects when `n ≥ 2^k - 2` (in fact for all `k ≥ 2`). -/
theorem corollary9 (I : Impl (scannable O) B P L) (p₀ : P)
    (hall : ∀ p o, SingleUpdater p₀ p o → I.allowed p o) (hlin : I.Linearizable)
    (hof : I.ObstructionFree) (hbit : ∀ i, OneBit (B i).State)
    (hnm : ∀ c, (O c).NonMonotonic) (hk : 3 ≤ k) :
    (Fintype.card P = 2 → k + 1 ≤ Fintype.card ι) ∧
    (2 < Fintype.card P → Fintype.card P ≤ 2 ^ (k - 1) + 2 →
      Fintype.card P + k - 2 ≤ Fintype.card ι) ∧
    (2 ^ k - 2 ≤ Fintype.card P → 2 ^ k - 1 ≤ Fintype.card ι) := by
  refine ⟨fun hn => lemma6 I p₀ hall hlin hof hbit hnm (by omega) (by omega), ?_, ?_⟩
  · intro h1 h2
    have hp : 2 ^ k = 2 * 2 ^ (k - 1) := by rw [← pow_succ']; congr 1; omega
    have := theorem8 I p₀ hall hlin hof hbit hnm 0 (by omega) (by simp; omega) (by simp; omega)
    simpa using this
  · intro hn
    have := cor9c_stage hnm hof hall hlin hbit k (by omega) (stage_init I p₀ (by omega))
      (by simpa using hn)
    simpa using this

/-- Corollary 9 (c) for every `k ≥ 2` (the paper states it for `k ≥ 3`; for `k = 2` it is
Lemma 6). -/
theorem corollary9c (I : Impl (scannable O) B P L) (p₀ : P)
    (hall : ∀ p o, SingleUpdater p₀ p o → I.allowed p o) (hlin : I.Linearizable)
    (hof : I.ObstructionFree) (hbit : ∀ i, OneBit (B i).State)
    (hnm : ∀ c, (O c).NonMonotonic) (hk : 2 ≤ k) (hn : 2 ^ k - 2 ≤ Fintype.card P) :
    2 ^ k - 1 ≤ Fintype.card ι := by
  have := cor9c_stage hnm hof hall hlin hbit k hk (stage_init I p₀ (by omega))
    (by simpa using hn)
  simpa using this

end Paper

end Cslib.SharedMemory.Scannable
