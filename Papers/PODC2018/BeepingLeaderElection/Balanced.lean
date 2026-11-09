import Mathlib

/-!
# `k`-balanced messages (Section 3.1.2)

Dufoulon, Burman, Beauquier. *Beeping a Deterministic Time-Optimal Leader Election.* DISC 2018
(full version of the PODC 2018 brief announcement), Section 3.1.2 and Table 2.

A variable is *`k`-balanced* if neighbouring values differ by at most `k`. To send a `k`-balanced
message `m_u` it suffices to send its remainder `r_u = m_u mod M`, `M = 2k + 1`; the receiver `v`,
knowing its own message `m_v` (and remainder `r_v`), decodes
`m_u = m_v + r_u − r_v − ⌊(r_u − r_v)/(k+1)⌋ · M`.

* `decodeTrunc_correct` — the decoding formula is correct when the rounding `⌊·⌋` is read as
  rounding **toward zero** (`Int.tdiv`);
* `decodeFloor_table2` / `decodeFloor_false` — read literally with the floor, the formula is wrong:
  in the paper's own Table 2 (`k = 4`, `m_v = 19`, `m_u = 18`, so `r_u = 0`, `r_v = 1`) it decodes `27`
  instead of `18`; `decodeFloor_eq` shows that the floor formula is correct iff `r_v ≤ r_u` or
  `r_u − r_v = −(k+1)`, and decodes `m_u + M` otherwise (also for some `m_u > m_v`, `decodeFloor_wrap`);
* `balancedDecode` — a clean decoder (the unique `m ≡ r_u (mod M)` with `|m − m_v| ≤ k`), with its
  correctness (`balancedDecode_eq`), specification and uniqueness, and a natural-number variant
  `decodeNat` (the paper uses it for prefix lengths with `k = 6`, `M = 13`).
-/

namespace Podc.BeepingLeaderElection

/-! ### The paper's decoding formula -/

/-- The paper's decoding formula of Section 3.1.2, with the rounding read as truncation toward
zero: `m_v + r_u − r_v − tdiv(r_u − r_v, k+1) · (2k+1)`. -/
def decodeTrunc (k : ℕ) (mv ru rv : ℤ) : ℤ :=
  mv + ru - rv - (ru - rv).tdiv (k + 1) * (2 * k + 1)

/-- The paper's decoding formula of Section 3.1.2, read literally with the floor:
`m_v + r_u − r_v − ⌊(r_u − r_v)/(k+1)⌋ · (2k+1)` (the division is in `ℚ`). -/
def decodeFloor (k : ℕ) (mv ru rv : ℤ) : ℤ :=
  mv + ru - rv - ⌊((ru - rv : ℤ) : ℚ) / (k + 1)⌋ * (2 * k + 1)

/-- The floor formula with integer floor division (`Int.ediv`, which is floor division for a
positive divisor). -/
theorem decodeFloor_eq_ediv (k : ℕ) (mv ru rv : ℤ) :
    decodeFloor k mv ru rv = mv + ru - rv - (ru - rv) / (k + 1) * (2 * k + 1) := by
  have := Rat.floor_intCast_div_natCast (ru - rv) (k + 1)
  simp only [Nat.cast_add, Nat.cast_one] at this
  rw [decodeFloor, this]

/-- The floor formula with `Int.fdiv` (floor division). -/
theorem decodeFloor_eq_fdiv (k : ℕ) (mv ru rv : ℤ) :
    decodeFloor k mv ru rv = mv + ru - rv - (ru - rv).fdiv (k + 1) * (2 * k + 1) := by
  rw [decodeFloor_eq_ediv, Int.fdiv_eq_ediv]
  simp [show (0 : ℤ) ≤ k + 1 by positivity]

private theorem ediv_eq_of_bounds {x c q : ℤ} (hc : 0 < c) (h1 : c * q ≤ x)
    (h2 : x < c * (q + 1)) : x / c = q := by
  have a := (Int.le_ediv_iff_mul_le hc).2 (by linarith : q * c ≤ x)
  have b := (Int.ediv_lt_iff_lt_mul hc).2 (by linarith : x < (q + 1) * c)
  omega

private theorem tdiv_eq_zero_of_abs_lt {x c : ℤ} (h1 : -c < x) (h2 : x < c) : x.tdiv c = 0 := by
  rcases le_or_gt 0 x with hx | hx
  · exact Int.tdiv_eq_zero_of_lt hx h2
  · rw [← neg_neg x, Int.neg_tdiv, Int.tdiv_eq_zero_of_lt (by omega) (by omega), neg_zero]

/-- The key arithmetic fact: with `d = m_u − m_v`, `|d| ≤ k`, the remainder difference `r_u − r_v`
is `d + t·M` for some `t ∈ {−1, 0, 1}`. -/
private theorem rem_sub_rem (k : ℕ) {mu mv : ℤ} (h : |mu - mv| ≤ k) :
    ∃ t : ℤ, (t = -1 ∨ t = 0 ∨ t = 1) ∧
      mu % (2 * k + 1) - mv % (2 * k + 1) = mu - mv + (2 * k + 1) * t ∧
      0 ≤ mu % (2 * k + 1) ∧ mu % (2 * k + 1) < 2 * k + 1 ∧
      0 ≤ mv % (2 * k + 1) ∧ mv % (2 * k + 1) < 2 * k + 1 := by
  have hM : (0 : ℤ) < 2 * k + 1 := by positivity
  have hu := Int.emod_add_mul_ediv mu (2 * k + 1)
  have hv := Int.emod_add_mul_ediv mv (2 * k + 1)
  have hu0 := Int.emod_nonneg mu hM.ne'
  have hv0 := Int.emod_nonneg mv hM.ne'
  have hu1 := Int.emod_lt_of_pos mu hM
  have hv1 := Int.emod_lt_of_pos mv hM
  rw [abs_le] at h
  set t := mv / (2 * k + 1) - mu / (2 * k + 1)
  have ht : mu % (2 * k + 1) - mv % (2 * k + 1) = mu - mv + (2 * k + 1) * t := by
    simp only [t]; linarith
  refine ⟨t, ?_, ht, hu0, hu1, hv0, hv1⟩
  have h1 : (2 * k + 1 : ℤ) * t < 2 * (2 * k + 1) := by linarith
  have h2 : -(2 * (2 * k + 1)) < (2 * k + 1 : ℤ) * t := by linarith
  have h3 : t < 2 := by nlinarith
  have h4 : -2 < t := by nlinarith
  omega

/-- Section 3.1.2 of the paper, decoding of `k`-balanced messages (cf. Table 2), **with the rounding
read as truncation toward zero**: if `|m_u − m_v| ≤ k` and `r = m mod (2k+1)`, then
`m_u = m_v + r_u − r_v − tdiv(r_u − r_v, k+1) · (2k+1)`. Holds for every `k` (for `k = 0`, `M = 1`). -/
theorem decodeTrunc_correct (k : ℕ) {mu mv : ℤ} (h : |mu - mv| ≤ k) :
    decodeTrunc k mv (mu % (2 * k + 1)) (mv % (2 * k + 1)) = mu := by
  obtain ⟨t, ht, hx, hu0, hu1, hv0, hv1⟩ := rem_sub_rem k h
  rw [abs_le] at h
  unfold decodeTrunc
  have hq : (mu % (2 * k + 1) - mv % (2 * k + 1)).tdiv (k + 1) = t := by
    rw [hx]
    rcases ht with rfl | rfl | rfl
    · rw [← neg_neg (mu - mv + _), Int.neg_tdiv, Int.tdiv_eq_ediv_of_nonneg (by linarith),
        ediv_eq_of_bounds (q := 1) (by positivity) (by linarith) (by linarith)]
    · exact tdiv_eq_zero_of_abs_lt (by linarith) (by linarith)
    · rw [Int.tdiv_eq_ediv_of_nonneg (by linarith),
        ediv_eq_of_bounds (q := 1) (by positivity) (by linarith) (by linarith)]
  rw [hq]; linear_combination hx

/-- Section 3.1.2 of the paper, Table 2 (`k = 4`, `M = 9`, `m_v = 19`): the sender with `m_u = 18`
transmits `r_u = 18 mod 9 = 0`, the receiver has `r_v = 19 mod 9 = 1`, and the printed formula
`m_v + r_u − r_v − ⌊(r_u − r_v)/(k+1)⌋ · M` (with the floor) decodes `19 − 1 − ⌊−1/5⌋ · 9 = 27`,
not `18` as in the table. -/
theorem decodeFloor_table2 :
    (18 : ℤ) % 9 = 0 ∧ (19 : ℤ) % 9 = 1 ∧ decodeFloor 4 19 0 1 = 27 := by
  refine ⟨by norm_num, by norm_num, ?_⟩
  rw [decodeFloor_eq_ediv]; norm_num

/-- The truncating formula gives the value `18` of Table 2 on the same input. -/
theorem decodeTrunc_table2 : decodeTrunc 4 19 0 1 = 18 := by
  decide

/-- Section 3.1.2 of the paper: the decoding formula **with the floor**, as printed, is false
(counterexample from Table 2: `k = 4`, `m_u = 18`, `m_v = 19`). -/
theorem decodeFloor_false :
    ¬ ∀ (k : ℕ) (mu mv : ℤ), |mu - mv| ≤ k →
      decodeFloor k mv (mu % (2 * k + 1)) (mv % (2 * k + 1)) = mu := by
  intro h
  have := h 4 18 19 (by norm_num)
  rw [decodeFloor_eq_ediv] at this
  norm_num at this

/-- Exactly when the floor formula of Section 3.1.2 is correct: for `|m_u − m_v| ≤ k`, it decodes
`m_u` if `r_v ≤ r_u` or `r_u − r_v = −(k+1)`, and `m_u + (2k+1)` otherwise. (So it fails both for
`m_u < m_v` without wrap-around of the remainders, as in Table 2, and for `m_u > m_v` with
wrap-around, except at `r_u − r_v = −(k+1)`.) -/
theorem decodeFloor_eq (k : ℕ) {mu mv : ℤ} (h : |mu - mv| ≤ k) :
    decodeFloor k mv (mu % (2 * k + 1)) (mv % (2 * k + 1)) =
      if mv % (2 * k + 1) ≤ mu % (2 * k + 1) ∨ mu % (2 * k + 1) + (k + 1) = mv % (2 * k + 1)
      then mu else mu + (2 * k + 1) := by
  obtain ⟨t, ht, hx, hu0, hu1, hv0, hv1⟩ := rem_sub_rem k h
  rw [abs_le] at h
  rw [decodeFloor_eq_ediv]
  have hM : (0 : ℤ) < k + 1 := by positivity
  split_ifs with hc
  · have hq : (mu % (2 * k + 1) - mv % (2 * k + 1)) / (k + 1) = t := by
      rw [hx]
      rcases ht with rfl | rfl | rfl
      · rcases hc with hc | hc
        · linarith
        · exact ediv_eq_of_bounds hM (by linarith) (by linarith)
      · rcases hc with hc | hc
        · exact ediv_eq_of_bounds hM (by linarith) (by linarith)
        · linarith
      · exact ediv_eq_of_bounds hM (by linarith) (by linarith)
    rw [hq]; linear_combination hx
  · push Not at hc
    have hq : (mu % (2 * k + 1) - mv % (2 * k + 1)) / (k + 1) = t - 1 := by
      have hne : mu % (2 * k + 1) - mv % (2 * k + 1) ≠ -(k + 1) := by
        intro he; exact hc.2 (by linarith)
      rw [hx] at hne ⊢
      rcases ht with rfl | rfl | rfl
      · have hlt : mu - mv + (2 * k + 1) * -1 < -(k + 1) :=
          lt_of_le_of_ne (by linarith) hne
        exact ediv_eq_of_bounds hM (by linarith) (by linarith)
      · exact ediv_eq_of_bounds hM (by linarith) (by linarith)
      · linarith
    rw [hq]; linear_combination hx

/-- Section 3.1.2 of the paper: the floor formula decodes `m_u` iff `r_v ≤ r_u` or
`r_u − r_v = −(k+1)` (see `decodeFloor_eq`). -/
theorem decodeFloor_eq_iff (k : ℕ) {mu mv : ℤ} (h : |mu - mv| ≤ k) :
    decodeFloor k mv (mu % (2 * k + 1)) (mv % (2 * k + 1)) = mu ↔
      (mv % (2 * k + 1) ≤ mu % (2 * k + 1) ∨ mu % (2 * k + 1) + (k + 1) = mv % (2 * k + 1)) := by
  rw [decodeFloor_eq k h]
  split_ifs with hc
  · simpa using hc
  · simp only [hc, iff_false]; intro he; linarith

/-- The floor formula also fails for a sender *above* the receiver with wrap-around of the
remainders: `k = 4`, `m_v = 17` (`r_v = 8`), `m_u = 19` (`r_u = 1`) decodes `28`. -/
theorem decodeFloor_wrap : decodeFloor 4 17 (19 % 9) (17 % 9) = 28 := by
  rw [decodeFloor_eq_ediv]; norm_num

/-! ### A clean decoder -/

/-- Decoding of `k`-balanced messages (Section 3.1.2 of the paper): given the receiver's message
`m_v` and the received remainder `r_u`, the unique `m ≡ r_u (mod 2k+1)` with `|m − m_v| ≤ k`. -/
def balancedDecode (k : ℕ) (mv ru : ℤ) : ℤ :=
  mv - k + (ru - mv + k) % (2 * k + 1)

/-- The decoded value is congruent to the received remainder. -/
theorem balancedDecode_modEq (k : ℕ) (mv ru : ℤ) :
    balancedDecode k mv ru ≡ ru [ZMOD 2 * k + 1] := by
  unfold balancedDecode
  have := Int.mod_modEq (ru - mv + k) (2 * k + 1)
  calc mv - k + (ru - mv + k) % (2 * k + 1) ≡ mv - k + (ru - mv + k) [ZMOD 2 * k + 1] :=
        this.add_left _
    _ = ru := by ring

/-- The decoded value is within `k` of the receiver's message. -/
theorem abs_balancedDecode_sub_le (k : ℕ) (mv ru : ℤ) : |balancedDecode k mv ru - mv| ≤ k := by
  unfold balancedDecode
  have hM : (0 : ℤ) < 2 * k + 1 := by positivity
  have h0 := Int.emod_nonneg (ru - mv + k) hM.ne'
  have h1 := Int.emod_lt_of_pos (ru - mv + k) hM
  rw [abs_le]; constructor <;> linarith

/-- Section 3.1.2 of the paper (cf. Table 2): if `|m_u − m_v| ≤ k` and `r_u ≡ m_u (mod 2k+1)`
(e.g. `r_u = m_u mod (2k+1)`), then the receiver decodes `m_u`. -/
theorem balancedDecode_eq (k : ℕ) {mu mv ru : ℤ} (h : |mu - mv| ≤ k)
    (hr : ru ≡ mu [ZMOD 2 * k + 1]) : balancedDecode k mv ru = mu := by
  unfold balancedDecode
  rw [abs_le] at h
  have : (ru - mv + k) % (2 * k + 1) = mu - mv + k := by
    rw [show (ru - mv + k) % (2 * k + 1) = (mu - mv + k) % (2 * k + 1) from
      ((hr.sub_right mv).add_right _)]
    exact Int.emod_eq_of_lt (by linarith) (by linarith)
  rw [this]; ring

/-- Section 3.1.2 of the paper: decoding the transmitted remainder `m_u mod (2k+1)`. -/
theorem balancedDecode_emod (k : ℕ) {mu mv : ℤ} (h : |mu - mv| ≤ k) :
    balancedDecode k mv (mu % (2 * k + 1)) = mu :=
  balancedDecode_eq k h (Int.mod_modEq _ _)

/-- Uniqueness: two values congruent modulo `2k+1` and both within `k` of `m_v` are equal. -/
theorem balanced_unique (k : ℕ) {m m' mv : ℤ} (h : |m - mv| ≤ k) (h' : |m' - mv| ≤ k)
    (hm : m ≡ m' [ZMOD 2 * k + 1]) : m = m' := by
  rw [← balancedDecode_eq k h hm.symm, balancedDecode_eq k h' rfl]

/-- The paper's (truncating) formula agrees with `balancedDecode`. -/
theorem decodeTrunc_eq_balancedDecode (k : ℕ) {mu mv : ℤ} (h : |mu - mv| ≤ k) :
    decodeTrunc k mv (mu % (2 * k + 1)) (mv % (2 * k + 1)) =
      balancedDecode k mv (mu % (2 * k + 1)) := by
  rw [decodeTrunc_correct k h, balancedDecode_emod k h]

/-! ### Natural-number messages -/

/-- Decoding of `k`-balanced natural-number messages (e.g. prefix lengths, Section 3.1.3 of the
paper, with `k = 6`, `M = 13`). -/
def decodeNat (k mv ru : ℕ) : ℕ := (balancedDecode k mv ru).toNat

/-- Section 3.1.2 of the paper for natural-number messages: if `m_u ≤ m_v + k` and `m_v ≤ m_u + k`,
the receiver decodes `m_u` from `m_u mod (2k+1)`. -/
theorem decodeNat_correct (k : ℕ) {mu mv : ℕ} (h1 : mu ≤ mv + k) (h2 : mv ≤ mu + k) :
    decodeNat k mv (mu % (2 * k + 1)) = mu := by
  unfold decodeNat
  have h : |(mu : ℤ) - mv| ≤ k := by rw [abs_le]; constructor <;> omega
  have := balancedDecode_emod k h
  push_cast
  rw [this, Int.toNat_natCast]

/-- The instance used for prefix lengths in the paper: `k = 6`, `M = 13`. -/
example : decodeNat 6 20 (14 % 13) = 14 := decodeNat_correct 6 (by omega) (by omega)

end Podc.BeepingLeaderElection
