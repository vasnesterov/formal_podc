import Cslib.Computability.Distributed.Local.Linial

-- CSLib candidate: Cslib/Foundations/Data/Nat/LogStar.lean (together with the definitions of
-- `Nat.tower`, `Nat.logStar` and the lemmas `lt_tower_logStar_succ`, `clog_le_tower_logStar`,
-- currently in `Cslib/Computability/Distributed/Local/Linial.lean`)

/-!
# The tower function and the iterated logarithm

API for `Nat.tower` (`tower 0 = 1`, `tower (k + 1) = 2 ^ tower k`) and `Nat.logStar` (the iterated
binary logarithm `log*`), both defined in CSLib's `Local/Linial.lean`:

* `Nat.tower_succ`, `Nat.lt_tower_succ`, `Nat.tower_strictMono`, `Nat.tower_mono`,
  `Nat.tower_pos`;
* `Nat.logStar_of_le_one`, `Nat.logStar_of_one_lt`: the defining equations of `log*`;
* `Nat.le_logStar_iff`: `m ≤ log* n ↔ tower m ≤ n` for `n ≠ 0` (the Galois connection between
  `tower` and `log*`), with `Nat.tower_logStar_le`, `Nat.tower_le_of_le_logStar` and
  `Nat.logStar_mono`;
* `Nat.iterate_log_logStar_le`: `log₂` iterated `log* n` times brings `n` down to at most `1`.
-/

namespace Nat

/-- `tower 0 = 1`. -/
@[simp]
theorem tower_zero : tower 0 = 1 := rfl

/-- `tower (k + 1) = 2 ^ tower k`. -/
theorem tower_succ (k : ℕ) : tower (k + 1) = 2 ^ tower k := rfl

/-- `tower k < tower (k + 1)`. -/
theorem lt_tower_succ (k : ℕ) : tower k < tower (k + 1) := Nat.lt_two_pow_self

/-- The tower function is strictly monotone. -/
theorem tower_strictMono : StrictMono tower := strictMono_nat_of_lt_succ lt_tower_succ

/-- The tower function is monotone. -/
theorem tower_mono : Monotone tower := tower_strictMono.monotone

/-- `tower k ≥ 1`. -/
theorem tower_pos (k : ℕ) : 0 < tower k := tower_mono (Nat.zero_le k)

/-- `log* n = 0` for `n ≤ 1`. -/
theorem logStar_of_le_one {n : ℕ} (hn : n ≤ 1) : logStar n = 0 := by
  rw [logStar, dite_eq_left_of_eq_true (eq_true hn)]

/-- `log* n = log* (log₂ n) + 1` for `n > 1`. -/
theorem logStar_of_one_lt {n : ℕ} (hn : 1 < n) : logStar n = logStar (log 2 n) + 1 := by
  rw [logStar, dite_eq_right_of_eq_false (eq_false (by omega))]

/-- `tower (log* n) ≤ n` for `n ≠ 0`. -/
theorem tower_logStar_le {n : ℕ} (hn : n ≠ 0) : tower (logStar n) ≤ n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases le_or_gt n 1 with h | h
    · rw [logStar_of_le_one h]; simp; omega
    · rw [logStar_of_one_lt h, tower_succ]
      have hlog : log 2 n ≠ 0 := (log_pos (by norm_num) h).ne'
      calc 2 ^ tower (logStar (log 2 n)) ≤ 2 ^ log 2 n :=
            Nat.pow_le_pow_right (by norm_num) (ih _ (log_lt_self 2 hn) hlog)
        _ ≤ n := pow_log_le_self 2 hn

/-- `m ≤ log* n ↔ tower m ≤ n` for `n ≠ 0`. -/
theorem le_logStar_iff {m n : ℕ} (hn : n ≠ 0) : m ≤ logStar n ↔ tower m ≤ n := by
  refine ⟨fun h => (tower_mono h).trans (tower_logStar_le hn), fun h => ?_⟩
  have := h.trans_lt (Cslib.LocallyIterative.Linial.lt_tower_logStar_succ n)
  exact Nat.lt_succ_iff.1 (tower_strictMono.lt_iff_lt.1 this)

/-- `tower m ≤ n` whenever `m ≤ log* n` and `n ≠ 0`. -/
theorem tower_le_of_le_logStar {m n : ℕ} (hn : n ≠ 0) (h : m ≤ logStar n) : tower m ≤ n :=
  (le_logStar_iff hn).1 h

/-- The iterated logarithm is monotone. -/
theorem logStar_mono : Monotone logStar := by
  intro m n h
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [logStar_of_le_one]
  · exact (le_logStar_iff (by omega)).2 ((tower_logStar_le hm.ne').trans h)

/-- `log₂` iterated `log* n` times maps `n` to a number `≤ 1`. -/
theorem iterate_log_logStar_le (n : ℕ) : (log 2)^[logStar n] n ≤ 1 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases le_or_gt n 1 with h | h
    · rwa [logStar_of_le_one h]
    · rw [logStar_of_one_lt h, Function.iterate_succ_apply]
      exact ih _ (log_lt_self 2 (by omega))

end Nat
