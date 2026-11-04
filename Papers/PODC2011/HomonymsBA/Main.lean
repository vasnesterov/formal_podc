import Papers.PODC2011.HomonymsBA.SyncLowerBound
import Papers.PODC2011.HomonymsBA.PsyncLowerBound
import Papers.PODC2011.HomonymsBA.Valency
import Papers.PODC2011.HomonymsBA.SyncAlgorithm
import Papers.PODC2011.HomonymsBA.PsyncLiveness
import Papers.PODC2011.HomonymsBA.RestrictedProp18

/-!
# Byzantine agreement with homonyms: main theorems

Standing assumptions of the paper: `n > 3t`, `t > 0`, `1 ≤ ℓ ≤ n`; values with at least two
elements (`v₀ ≠ v₁`).
-/

namespace Podc.HomonymsBA

/-- **Theorem 3.** Synchronous Byzantine agreement is solvable iff `ℓ > 3t`, for numerate and
for innumerate processes. -/
theorem thm3 {n ℓ t : ℕ} (hn : 3 * t < n) (hℓ : 0 < ℓ) {V : Type} {v₀ v₁ : V} (hv : v₀ ≠ v₁) :
    (Solvable .sync .unrestricted .numerate n ℓ t V ↔ 3 * t < ℓ) ∧
      (Solvable .sync .unrestricted .innumerate n ℓ t V ↔ 3 * t < ℓ) := by
  have : Nonempty V := ⟨v₀⟩
  refine ⟨⟨fun h => ?_, fun h => (prop2 h V).numerate_of_innumerate⟩,
    ⟨fun h => ?_, fun h => prop2 h V⟩⟩
  · by_contra h'; exact prop1 hn hℓ (by omega) hv h
  · by_contra h'; exact prop1 hn hℓ (by omega) hv h.numerate_of_innumerate

/-- **Theorem 19.** Synchronous Byzantine agreement with innumerate processes against restricted
Byzantine processes is solvable iff `ℓ > 3t`. -/
theorem thm19 {n ℓ t : ℕ} (hn : 3 * t < n) (hℓ : 0 < ℓ) {V : Type} {v₀ v₁ : V} (hv : v₀ ≠ v₁) :
    Solvable .sync .restricted .innumerate n ℓ t V ↔ 3 * t < ℓ := by
  have : Nonempty V := ⟨v₀⟩
  refine ⟨fun h => ?_, fun h => (prop2 h V).restricted_of_unrestricted⟩
  by_contra h'
  exact thm19_lower hn hℓ (by omega) hv h

/-- **Theorem 13.** Partially synchronous Byzantine agreement is solvable iff `ℓ > (n + 3t) / 2`
(i.e. `n + 3t < 2ℓ`), for numerate and for innumerate processes. -/
theorem thm13 {n ℓ t : ℕ} (hn : 3 * t < n) (ht : 0 < t) (hℓ : 0 < ℓ) {V : Type} {v₀ v₁ : V}
    (hv : v₀ ≠ v₁) :
    (Solvable .psync .unrestricted .numerate n ℓ t V ↔ n + 3 * t < 2 * ℓ) ∧
      (Solvable .psync .unrestricted .innumerate n ℓ t V ↔ n + 3 * t < 2 * ℓ) := by
  refine ⟨⟨fun h => ?_, fun h => (Psync.prop5 hn h V).numerate_of_innumerate⟩,
    ⟨fun h => ?_, fun h => Psync.prop5 hn h V⟩⟩
  · by_contra h'; exact prop4 hn ht hℓ (by omega) hv h
  · by_contra h'; exact prop4 hn ht hℓ (by omega) hv h.numerate_of_innumerate

/-- **Theorem 20.** Partially synchronous Byzantine agreement with innumerate processes against
restricted Byzantine processes is solvable iff `ℓ > (n + 3t) / 2`. -/
theorem thm20 {n ℓ t : ℕ} (hn : 3 * t < n) (ht : 0 < t) (hℓ : 0 < ℓ) {V : Type} {v₀ v₁ : V}
    (hv : v₀ ≠ v₁) : Solvable .psync .restricted .innumerate n ℓ t V ↔ n + 3 * t < 2 * ℓ := by
  refine ⟨fun h => ?_, fun h => (Psync.prop5 hn h V).restricted_of_unrestricted⟩
  by_contra h'
  exact thm20_lower hn ht hℓ (by omega) hv h

/-- **Theorem 14.** Synchronous Byzantine agreement with numerate processes against restricted
Byzantine processes is solvable iff `ℓ > t`. -/
theorem thm14 {n ℓ t : ℕ} (hn : 3 * t < n) (hℓ : 0 < ℓ) {V : Type} {v₀ v₁ : V} (hv : v₀ ≠ v₁) :
    Solvable .sync .restricted .numerate n ℓ t V ↔ t < ℓ := by
  refine ⟨fun h => ?_, fun h => (prop18 hn h V).sync_of_psync⟩
  by_contra h'
  exact prop16 hn hℓ (by omega) hv h

/-- **Theorem 15.** Partially synchronous Byzantine agreement with numerate processes against
restricted Byzantine processes is solvable iff `ℓ > t`. -/
theorem thm15 {n ℓ t : ℕ} (hn : 3 * t < n) (hℓ : 0 < ℓ) {V : Type} {v₀ v₁ : V} (hv : v₀ ≠ v₁) :
    Solvable .psync .restricted .numerate n ℓ t V ↔ t < ℓ := by
  refine ⟨fun h => ?_, fun h => prop18 hn h V⟩
  by_contra h'
  exact prop16 hn hℓ (by omega) hv h.sync_of_psync

/-- The example of the introduction (solvable half): with `t = 1` and `ℓ = 4`, partially
synchronous agreement is solvable for `n = 4` processes (even innumerate). -/
theorem intro_example_four : Solvable .psync .unrestricted .innumerate 4 4 1 Bool :=
  Psync.prop5 (by norm_num) (by norm_num) Bool

/-- The example of the introduction (unsolvable half): with `t = 1` and `ℓ = 4`, partially
synchronous agreement is not solvable for `n = 5` processes. -/
theorem intro_example_five : ¬ Solvable .psync .unrestricted .numerate 5 4 1 Bool :=
  prop4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) Bool.false_ne_true

end Podc.HomonymsBA
