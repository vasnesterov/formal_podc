import Papers.PODC2021.ContentionPredictions.Model
import Podc.Foundations.Combinatorics.SelectiveFamily

/-!
# Deterministic lower bounds with perfect advice (Theorems 3.3, 3.4, 3.5)

All three lower bounds follow from one counting fact
(`Cslib.card_le_of_forall_exists_card_inter_eq_one`): a family of subsets of `Fin n` that meets every
nonempty set in exactly one point has at least `n` members (parity argument over `ZMod 2`).

* Without collision detection, the transmitter set of round `r` depends only on the advice and on
  `r`, so the `|A| · t` sets "advice `a`, round `r < t`" form such a family: `n ≤ |A| · t`.
* With collision detection it depends on the advice and the feedback history, and there are
  `2^t - 1` histories of length `< t`: `n ≤ |A| · (2^t - 1)`.

The paper instead claims that the `2^b` first-round transmitter sets form an `(n, n)`-strongly
selective family and invokes Theorem 3.2 (Clementi–Monti–Silvestri); that claim is false
(`not_stronglySelective_example` in `Counterexamples.lean`), but the theorems hold.
-/

namespace Podc.ContentionPredictions

open Finset

variable {n : ℕ} {A : Type*} [Fintype A]

/-- Counting core, no collision detection: `n ≤ |A| · t`. -/
theorem card_le_mul_of_solvesIn_noCD {alg : DetAlg n A} {f : Finset (Fin n) → A} {t : ℕ}
    (h : SolvesIn false alg f t) : n ≤ Fintype.card A * t := by
  classical
  have := Cslib.card_le_of_forall_exists_card_inter_eq_one
    (fun x : A × Fin t => univ.filter fun v => alg x.1 (List.replicate x.2 false) v)
    (fun P hP => by
      obtain ⟨r, hr, hs⟩ := h P hP
      refine ⟨(f P, ⟨r, hr⟩), ?_⟩
      simp only [SolvedAt, transmitters, history_false] at hs
      rw [← hs, Finset.filter_inter, Finset.univ_inter])
  simpa using this

/-- Counting core, with collision detection: `n ≤ |A| · (2^t - 1)`. -/
theorem card_le_mul_of_solvesIn_CD {alg : DetAlg n A} {f : Finset (Fin n) → A} {t : ℕ}
    (h : SolvesIn true alg f t) : n ≤ Fintype.card A * (2 ^ t - 1) := by
  classical
  have := Cslib.card_le_of_forall_exists_card_inter_eq_one
    (fun x : A × (Σ r : Fin t, List.Vector Bool r) => univ.filter fun v => alg x.1 x.2.2.toList v)
    (fun P hP => by
      obtain ⟨r, hr, hs⟩ := h P hP
      refine ⟨(f P, ⟨⟨r, hr⟩,
        (⟨history true alg (f P) P r, history_length ..⟩ : List.Vector Bool r)⟩), ?_⟩
      simp only [SolvedAt, transmitters] at hs
      rw [← hs]
      congr 1
      ext v
      simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and]
      exact and_comm)
  rwa [Fintype.card_prod, card_sigma_vector, Fintype.card_fin] at this

/-- Counting core for any channel: `n ≤ |A| · (2^t - 1)` (a no-CD algorithm is in particular
covered by `card_le_mul_of_solvesIn_noCD`). For `t = 1` this is `n ≤ |A|`. -/
theorem card_le_of_nonInteractive {alg : DetAlg n A} {f : Finset (Fin n) → A}
    (h : NonInteractive alg f) : n ≤ Fintype.card A := by
  simpa using card_le_mul_of_solvesIn_noCD h

/-- **Theorem 3.3** of [Gilbert–Newport–Vaidya–Weaver, PODC 2021]. A deterministic algorithm with
`b`-bit advice solving non-interactive contention resolution on `n` players needs `b ≥ log₂ n`. -/
theorem theorem_3_3 {b : ℕ} {alg : DetAlg n (Bits b)} {f : Finset (Fin n) → Bits b}
    (h : NonInteractive alg f) : Real.logb 2 n ≤ b := by
  have hn : n ≤ 2 ^ b := by simpa using card_le_of_nonInteractive h
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · simp
  · rw [Real.logb_le_iff_le_rpow (by norm_num) (by exact_mod_cast hpos)]
    rw [Real.rpow_natCast]; exact_mod_cast hn

/-- Theorem 3.3, sharp counting form, for any finite advice alphabet: `n ≤ |A|`. With advice
strings of length *at most* `b` (`|A| = 2^{b+1} - 1`) this gives only `n < 2^{b+1}`, and indeed
`log₂ n ≤ b` fails then (`theorem_3_3_false_variable_length`). -/
theorem theorem_3_3_card {alg : DetAlg n A} {f : Finset (Fin n) → A}
    (h : NonInteractive alg f) : n ≤ Fintype.card A :=
  card_le_of_nonInteractive h

/-- **Theorem 3.4** of [Gilbert–Newport–Vaidya–Weaver, PODC 2021]. A deterministic algorithm with
at most `α log₂ n` bits of advice (`0 < α < 1`) solving contention resolution without collision
detection in `t` rounds needs `t ≥ n^{1-α}/2`. -/
theorem theorem_3_4 {α : ℝ} (_hα0 : 0 < α) (hα1 : α < 1) {b : ℕ} (hb : (b : ℝ) ≤ α * Real.logb 2 n)
    {alg : DetAlg n (Bits b)} {f : Finset (Fin n) → Bits b} {t : ℕ}
    (h : SolvesIn false alg f t) : (n : ℝ) ^ (1 - α) / 2 ≤ t := by
  have hcount : n ≤ 2 ^ b * t := by simpa using card_le_mul_of_solvesIn_noCD h
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · rw [Nat.cast_zero, Real.zero_rpow (by linarith)]; simp
  have hn : (0 : ℝ) < n := by exact_mod_cast hpos
  -- `2^b ≤ n^α`
  have h2b : (2 : ℝ) ^ b ≤ (n : ℝ) ^ α := by
    rw [← Real.rpow_natCast]
    calc (2 : ℝ) ^ (b : ℝ) ≤ 2 ^ (α * Real.logb 2 n) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) hb
      _ = (n : ℝ) ^ α := by
          rw [mul_comm, Real.rpow_mul (by norm_num), Real.rpow_logb (by norm_num) (by norm_num) hn]
  have hcountR : (n : ℝ) ≤ (n : ℝ) ^ α * t := by
    calc (n : ℝ) ≤ (2 ^ b * t : ℕ) := by exact_mod_cast hcount
      _ = (2 : ℝ) ^ b * t := by push_cast; ring
      _ ≤ (n : ℝ) ^ α * t := by gcongr
  have hnα : (0 : ℝ) < (n : ℝ) ^ α := Real.rpow_pos_of_pos hn α
  have : (n : ℝ) ^ (1 - α) ≤ t := by
    rw [Real.rpow_sub hn, Real.rpow_one, div_le_iff₀ hnα]
    linarith
  have ht : (0 : ℝ) ≤ t := by positivity
  linarith

/-- Theorem 3.4, sharp counting form: without collision detection, `n ≤ 2^b · t`, i.e.
`t ≥ n / 2^b` (with `2^b ≤ n^α` this is `t ≥ n^{1-α}`, twice the paper's bound). -/
theorem theorem_3_4_card {b : ℕ} {alg : DetAlg n (Bits b)} {f : Finset (Fin n) → Bits b} {t : ℕ}
    (h : SolvesIn false alg f t) : n ≤ 2 ^ b * t := by
  simpa using card_le_mul_of_solvesIn_noCD h

/-- **Theorem 3.5** of [Gilbert–Newport–Vaidya–Weaver, PODC 2021]. A deterministic algorithm with
`b` bits of advice solving contention resolution with collision detection in `t` rounds needs
`t ≥ log₂ n - b`. -/
theorem theorem_3_5 {b : ℕ} {alg : DetAlg n (Bits b)} {f : Finset (Fin n) → Bits b} {t : ℕ}
    (h : SolvesIn true alg f t) : Real.logb 2 n - b ≤ t := by
  have hcount : n ≤ 2 ^ b * (2 ^ t - 1) := by simpa using card_le_mul_of_solvesIn_CD h
  have hcount' : n ≤ 2 ^ (b + t) := by
    rw [pow_add]; exact hcount.trans (Nat.mul_le_mul_left _ (Nat.sub_le _ _))
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · have : (0 : ℝ) ≤ b + t := by positivity
    simp only [CharP.cast_eq_zero, Real.logb_zero, zero_sub]
    linarith
  have : Real.logb 2 n ≤ (b + t : ℕ) := by
    rw [Real.logb_le_iff_le_rpow (by norm_num) (by exact_mod_cast hpos), Real.rpow_natCast]
    exact_mod_cast hcount'
  push_cast at this
  linarith

/-- Theorem 3.5, sharp counting form: with collision detection, `n ≤ 2^b · (2^t - 1)`. -/
theorem theorem_3_5_card {b : ℕ} {alg : DetAlg n (Bits b)} {f : Finset (Fin n) → Bits b} {t : ℕ}
    (h : SolvesIn true alg f t) : n ≤ 2 ^ b * (2 ^ t - 1) := by
  simpa using card_le_mul_of_solvesIn_CD h

end Podc.ContentionPredictions
