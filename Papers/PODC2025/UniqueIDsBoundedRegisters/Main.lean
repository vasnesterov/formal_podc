import Papers.PODC2025.UniqueIDsBoundedRegisters.LowerBound
import Papers.PODC2025.UniqueIDsBoundedRegisters.NonAnonymous
import Papers.PODC2025.UniqueIDsBoundedRegisters.AlgCorrect
import Papers.PODC2025.UniqueIDsBoundedRegisters.AlgWaitFree
import Papers.PODC2025.UniqueIDsBoundedRegisters.AlgTight

/-!
# Main results with `w`-bit registers (`m = 2^w`)

Anoprenko, Kuznetsov, Aksenov, *Brief Announcement: Optimal Construction of Unique Identifiers
from Bounded Registers*, PODC 2025.
-/

set_option linter.unusedSectionVars false

namespace Cslib.SharedMemory.UniqueIDs

open Cslib.SharedMemory Impl

variable {P L : Type} [DecidableEq P]

/-- **Theorem 3.1.** Algorithm 1 with `k = 2^x + 1 ≤ 2^w + 1` registers of `w` bits is an anonymous
wait-free UniqueID implementation, correct as long as `get()` is called at most `(k − 1)·2^w`
times; all identifiers lie in `[0, (k − 1)·2^w)`. -/
theorem theorem_3_1 (x w : ℕ) (hxw : x ≤ w) :
    Anonymous (alg (P := P) (2 ^ x) (2 ^ x) (2 ^ w)) ∧
    (alg (P := P) (2 ^ x) (2 ^ x) (2 ^ w)).WaitFree ∧
    CorrectUpTo (alg (P := P) (2 ^ x) (2 ^ x) (2 ^ w)) (2 ^ x * 2 ^ w) ∧
    ∀ α, (alg (P := P) (2 ^ x) (2 ^ x) (2 ^ w)).Valid α →
      ∀ y v, respOf α y = some v → v < 2 ^ x * 2 ^ w :=
  ⟨alg_anonymous _ _ _, alg1_waitFree _ _ (Nat.one_le_two_pow),
    alg_correct _ _ _ le_rfl (pow_dvd_pow 2 hxw), fun α hα y v h => alg_resp_lt _ _ _ α hα y v h⟩

/-- **Algorithm 2.** For `2 ≤ k ≤ 2^w + 1` registers of `w` bits, Algorithm 2 (`k' − 1 =
2^⌈log₂(k − 1)⌉`) is anonymous, wait-free in executions with boundedly many calls, and correct
as long as `get()` is called at most `(k − 1)·2^w` times. -/
theorem algorithm_2 (k w : ℕ) (hk : 2 ≤ k) (hkw : k ≤ 2 ^ w + 1) :
    Anonymous (alg (P := P) (k - 1) (2 ^ Nat.clog 2 (k - 1)) (2 ^ w)) ∧
    (∀ N, WaitFreeUpTo (alg (P := P) (k - 1) (2 ^ Nat.clog 2 (k - 1)) (2 ^ w)) N) ∧
    CorrectUpTo (alg (P := P) (k - 1) (2 ^ Nat.clog 2 (k - 1)) (2 ^ w)) ((k - 1) * 2 ^ w) := by
  have h1 : k - 1 ≤ 2 ^ Nat.clog 2 (k - 1) := Nat.le_pow_clog (by norm_num) _
  have h2 : 2 ^ Nat.clog 2 (k - 1) ∣ 2 ^ w :=
    pow_dvd_pow 2 ((Nat.clog_le_iff_le_pow (by norm_num)).2 (by omega))
  exact ⟨alg_anonymous _ _ _, fun N => alg_waitFreeUpTo _ _ _ (by omega) h1 h2 N,
    alg_correct _ _ _ h1 h2⟩

/-- Algorithm 1 cannot do better than `(k − 1)·2^w` calls. -/
theorem theorem_3_1_tight [Nonempty P] (x w : ℕ) (hxw : x ≤ w) :
    ¬ CorrectUpTo (alg (P := P) (2 ^ x) (2 ^ x) (2 ^ w)) (2 ^ x * 2 ^ w + 1) :=
  alg_not_correctUpTo_succ _ _ Nat.one_le_two_pow (pow_dvd_pow 2 hxw)

/-- **Theorem 4.1.** In a system with at least `k·2^w + k + 2` processes, no anonymous
obstruction-free implementation of UniqueID from `k` `w`-bit registers (read, write, FAI) is
correct when `get()` is called more than `k·2^w + k + 1` times. -/
theorem theorem_4_1_bits {k w : ℕ} (I : Impl uidObj (fun _ : Fin k => bReg (2 ^ w)) P L)
    (hA : Anonymous I) (hall : ∀ p, I.allowed p ()) (hof : I.ObstructionFree)
    (e : Fin (k * 2 ^ w + k + 2) ↪ P) {B : ℕ} (hB : CorrectUpTo I B) :
    B ≤ k * 2 ^ w + k + 1 :=
  theorem_4_1 I hA hall hof e hB

/-- **Asymptotic optimality** (`k = 2^x + 1 ≤ 2^w + 1`, at least `k·2^w + k + 2` processes): the
largest number of calls `B` for which an anonymous obstruction-free (here even wait-free) UniqueID
implementation exists satisfies `(k − 1)·2^w ≤ B ≤ k·2^w + k + 1`. -/
theorem optimal (x w : ℕ) (hxw : x ≤ w) (e : Fin ((2 ^ x + 1) * 2 ^ w + (2 ^ x + 1) + 2) ↪ P) :
    (∃ (L : Type) (I : Impl uidObj (fun _ : Fin (2 ^ x + 1) => bReg (2 ^ w)) P L),
      Anonymous I ∧ (∀ p, I.allowed p ()) ∧ I.WaitFree ∧ CorrectUpTo I (2 ^ x * 2 ^ w)) ∧
    ∀ (L : Type) (I : Impl uidObj (fun _ : Fin (2 ^ x + 1) => bReg (2 ^ w)) P L),
      Anonymous I → (∀ p, I.allowed p ()) → I.ObstructionFree → ∀ B, CorrectUpTo I B →
        B ≤ (2 ^ x + 1) * 2 ^ w + (2 ^ x + 1) + 1 := by
  obtain ⟨hA, hW, hC, -⟩ := theorem_3_1 (P := P) x w hxw
  exact ⟨⟨_, alg (2 ^ x) (2 ^ x) (2 ^ w), hA, fun _ => trivial, hW, hC⟩,
    fun L I hA hall hof B hB => theorem_4_1_bits I hA hall hof e hB⟩

/-- Non-vacuity of Theorem 4.1: Algorithm 1 satisfies all its hypotheses, so it is correct for
at most `k·2^w + k + 1` calls (indeed for exactly `(k − 1)·2^w`, `theorem_3_1_tight`). -/
example (x w : ℕ) (hxw : x ≤ w) (e : Fin ((2 ^ x + 1) * 2 ^ w + (2 ^ x + 1) + 2) ↪ P) :
    2 ^ x * 2 ^ w ≤ (2 ^ x + 1) * 2 ^ w + (2 ^ x + 1) + 1 := by
  obtain ⟨⟨L, I, hA, hall, hW, hC⟩, hlb⟩ := optimal x w hxw e
  exact hlb L I hA hall (WaitFree.obstructionFree I hW) _ hC

/-- The first variation of Algorithm 1 (§3): with `k' - 1` the largest power of two `≤ k - 1`,
`(k' - 1) · 2^w ≥ k/2 · 2^w`, i.e. `k ≤ 2 (k' - 1)`. -/
theorem variation_bound (k : ℕ) (hk : 2 ≤ k) : k ≤ 2 * 2 ^ Nat.log 2 (k - 1) := by
  have := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) (k - 1)
  rw [pow_succ] at this
  omega

end Cslib.SharedMemory.UniqueIDs
