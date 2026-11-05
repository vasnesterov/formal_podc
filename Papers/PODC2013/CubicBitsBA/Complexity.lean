import Mathlib

/-!
# Section 6 of Kowalski–Mostéfaoui: bits sent by the basic protocol

We count the bits of the messages of a correct process of the basic protocol of Section 4 under the
natural fixed-length encoding: a proposal costs `b` bits (`b = ⌈log₂ k⌉` for `k` proposable values),
an entry that may be `⊥` costs one more bit, a suspicion set costs `n` bits (a bit vector).

* round 1: one proposal, `b` bits;
* round 2: the echo of the `n` received proposals, `n (b + 1)` bits;
* round 3: the suspicion set and the echo of the `n` received round-2 arrays,
  `n + n (1 + n (b + 1))` bits;
* round `r ≥ 4`: the suspicion set and the echo of the `n` received suspicion sets,
  `n + n (1 + n)` bits.

`totalBits_le`: over the `t + 1 ≤ n` rounds a correct process sends at most `5 n³ + 3 n² (b + 1)`
bits, i.e. `O(n³ + n² log k)` per process and `O(max(n⁴, n³ log k))` in total, as claimed in the
first two paragraphs of Section 6. The improved, incremental protocol (`O(n³ log n)` bits in
total, the bound of the abstract) is only sketched in the paper and is not formalized.
-/

namespace Podc.CubicBitsBA

/-- Bits of the round-`r` message of a correct process (`b` bits per proposal). -/
def roundBits (n b : ℕ) : ℕ → ℕ
  | 0 => 0
  | 1 => b
  | 2 => n * (b + 1)
  | 3 => n + n * (1 + n * (b + 1))
  | _ + 4 => n + n * (1 + n)

/-- Bits sent by a correct process in rounds `1..R`. -/
def totalBits (n b : ℕ) : ℕ → ℕ
  | 0 => 0
  | R + 1 => totalBits n b R + roundBits n b (R + 1)

lemma totalBits_eq (n b : ℕ) : ∀ R, totalBits n b (R + 3) = totalBits n b 3 + R * (n + n * (1 + n))
  | 0 => by simp
  | R + 1 => by
    rw [show R + 1 + 3 = (R + 3) + 1 by omega, totalBits, totalBits_eq n b R]
    simp only [roundBits]
    ring

/-- **Section 6** (basic protocol): with `t + 1 ≤ n` rounds (in particular for `t < n/3`), a correct
process sends at most `5 n³ + 3 n² (b + 1)` bits. -/
theorem totalBits_le (n b t : ℕ) (ht : t + 1 ≤ n) :
    totalBits n b (t + 1) ≤ 5 * n ^ 3 + 3 * n ^ 2 * (b + 1) := by
  have h3 : totalBits n b 3 = b + n * (b + 1) + (n + n * (1 + n * (b + 1))) := by
    simp [totalBits, roundBits]
  have hmono : ∀ R ≤ 3, totalBits n b R ≤ totalBits n b 3 :=
    fun R hR => monotone_nat_of_le_succ (fun R => Nat.le_add_right _ _) hR
  have hn : 1 ≤ n := by omega
  have e1 : n ≤ n ^ 2 := by nlinarith
  have e2 : n ^ 2 ≤ n ^ 3 := by nlinarith
  have e3 : b ≤ n ^ 2 * b := Nat.le_mul_of_pos_left _ (by positivity)
  have e4 : n * b ≤ n ^ 2 * b := Nat.mul_le_mul_right _ e1
  have hb3 : totalBits n b 3 ≤ 2 * n ^ 3 + 3 * n ^ 2 * (b + 1) := by
    rw [h3]; nlinarith
  by_cases h : t + 1 ≤ 3
  · exact (hmono _ h).trans (hb3.trans (by nlinarith))
  · obtain ⟨R, hR⟩ : ∃ R, t + 1 = R + 3 := ⟨t + 1 - 3, by omega⟩
    rw [hR, totalBits_eq]
    have hRn : R ≤ n := by omega
    have : R * (n + n * (1 + n)) ≤ n * (n + n * (1 + n)) := Nat.mul_le_mul_right _ hRn
    nlinarith

/-- **Section 6** (basic protocol), total over all correct processes: at most
`n (5 n³ + 3 n² (b + 1))`, i.e. `O(max(n⁴, n³ log k))` bits. -/
theorem allBits_le (n b t : ℕ) (ht : t + 1 ≤ n) :
    n * totalBits n b (t + 1) ≤ n * (5 * n ^ 3 + 3 * n ^ 2 * (b + 1)) :=
  Nat.mul_le_mul_left _ (totalBits_le n b t ht)

end Podc.CubicBitsBA
