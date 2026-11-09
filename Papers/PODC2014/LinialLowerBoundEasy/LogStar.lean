import Papers.PODC2014.LinialLowerBoundEasy.ColouringFunctions

/-!
# The paper's iterated logarithm and the main bound `k + 1 ≥ log* n`

The paper defines, for real `x`, `log* x = 0` if `x ≤ 1` and `log* x = 1 + log* (log₂ x)`
otherwise. We define `logStar x` as the least `m` with `x ≤ ^m2` (`Nat.tower m`) and prove the two
defining equations (`logStar_of_le_one`, `logStar_of_one_lt`), which determine the function.

This is **not** CSLib's `Nat.logStar`, which uses the floor `Nat.log 2` and is the *largest* `m`
with `^m2 ≤ n`: e.g. `logStar 3 = 2` but `Nat.logStar 3 = 1`. For `n ≥ 2`,
`logStar n = Nat.logStar (n - 1) + 1` (`logStar_natCast`).

## Main statements

* `logStar_le_iff`: `log* x ≤ m ↔ x ≤ ^m2`.
* `logStar_le_of_isColouringFunction`: §3–§4 of the paper, any `k`-ary `3`-colouring function
  has `k + 1 ≥ log* n`.
-/

namespace Podc.LinialLowerBoundEasy

open Finset

-- CSLib candidate: the real-valued (ceiling-type) `log*` next to `Nat.logStar`.
theorem exists_le_tower (x : ℝ) : ∃ m : ℕ, x ≤ Nat.tower m := by
  obtain ⟨m, hm⟩ := exists_nat_ge x
  exact ⟨m, hm.trans (by exact_mod_cast Nat.tower_strictMono.id_le m)⟩

/-- The iterated logarithm of [Laurinharju–Suomela, §2]: the least `m` with `x ≤ ^m2`.
Its defining equations are `logStar_of_le_one` and `logStar_of_one_lt`. -/
noncomputable def logStar (x : ℝ) : ℕ := Nat.find (exists_le_tower x)

/-- `log* x ≤ m ↔ x ≤ ^m2`. -/
theorem logStar_le_iff {x : ℝ} {m : ℕ} : logStar x ≤ m ↔ x ≤ Nat.tower m := by
  rw [logStar, Nat.find_le_iff]
  constructor
  · rintro ⟨j, hj, hx⟩
    exact hx.trans (by exact_mod_cast Nat.tower_mono hj)
  · exact fun h => ⟨m, le_rfl, h⟩

/-- `log* x = 0` if `x ≤ 1`. -/
theorem logStar_of_le_one {x : ℝ} (hx : x ≤ 1) : logStar x = 0 :=
  Nat.le_zero.1 (logStar_le_iff.2 (by simpa using hx))

/-- `log* x = 1 + log* (log₂ x)` if `x > 1`. -/
theorem logStar_of_one_lt {x : ℝ} (hx : 1 < x) : logStar x = 1 + logStar (Real.logb 2 x) := by
  have key : ∀ m : ℕ, x ≤ Nat.tower (m + 1) ↔ Real.logb 2 x ≤ Nat.tower m := by
    intro m
    rw [Real.logb_le_iff_le_rpow one_lt_two (by linarith), Real.rpow_natCast, Nat.tower_succ]
    push_cast; rfl
  apply le_antisymm
  · rw [add_comm, logStar_le_iff, key]
    exact logStar_le_iff.1 le_rfl
  · obtain ⟨j, hj⟩ : ∃ j, logStar x = j := ⟨_, rfl⟩
    rw [hj]
    obtain _ | i := j
    · have := logStar_le_iff.1 hj.le
      simp at this; linarith
    · have := (key i).1 (logStar_le_iff.1 hj.le)
      have := logStar_le_iff.2 this
      omega

/-- For identifiers `n ≥ 2`, the paper's `log* n` is CSLib's (floor-based) `Nat.logStar (n - 1)`
plus one. -/
theorem logStar_natCast {n : ℕ} (hn : 2 ≤ n) : logStar n = Nat.logStar (n - 1) + 1 := by
  apply le_antisymm
  · rw [logStar_le_iff]
    have := Nat.lt_tower_logStar_succ (n - 1)
    exact_mod_cast (by omega : n ≤ Nat.tower (Nat.logStar (n - 1) + 1))
  · by_contra hlt
    push Not at hlt
    have h1 : Nat.tower (logStar n) ≤ n - 1 :=
      (Nat.le_logStar_iff (by omega)).1 (by omega)
    have h2 : (n : ℝ) ≤ Nat.tower (logStar n) := logStar_le_iff.1 le_rfl
    have h2' : n ≤ Nat.tower (logStar n) := by exact_mod_cast h2
    omega

/-- The paper's `log*` differs from CSLib's `Nat.logStar`: `log* 3 = 2`, `Nat.logStar 3 = 1`. -/
example : logStar 3 = 2 ∧ Nat.logStar 3 = 1 := by
  refine ⟨?_, by decide +kernel⟩
  have h := logStar_natCast (n := 3) (by norm_num)
  have h2 : Nat.logStar 2 = 1 := by decide +kernel
  simpa [h2] using h

/-- **§3–§4 of [Laurinharju–Suomela]**: if `A` is a `k`-ary `3`-colouring function for identifiers
`1, …, n`, then `k + 1 ≥ log* n`. -/
theorem logStar_le_of_isColouringFunction {n k : ℕ} {A : (Fin k → ℕ) → ℕ}
    (h : IsColouringFunction n k 3 A) : logStar n ≤ k + 1 := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [logStar_of_le_one]
    · exact absurd h (not_isColouringFunction_zero hn)
  · rw [logStar_le_iff]
    exact_mod_cast le_tower_of_isColouringFunction_three hk h

end Podc.LinialLowerBoundEasy
