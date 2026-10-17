import Mathlib.Data.Nat.Size
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Nat.Log
import Podc.Foundations.Data.Nat.Log
import Podc.Foundations.Data.Nat.LogStar

/-!
# The identifier-reduction function `f` (Section 4.1)

For `Z ∈ ℕ` with binary digits `Z_k`, `|Z| = ⌈log₂(Z + 1)⌉` is the bit length (`Nat.size Z`).
The paper sets (Equation (6))

  `f(X, Y) = 2 i + X_i`  where  `i = min ({min(|X|, |Y|)} ∪ { k | X_k ≠ Y_k })`.

`cvIdx x y` is this `i`, computed by a structural recursion so that the kernel can evaluate it.

## Main results

* `cvIdx_le`, `testBit_eq_of_lt_cvIdx`, `testBit_cvIdx_ne`: specification of `cvIdx`.
* `cvF_le`: `f(x, y) ≤ 2 min(|x|, |y|) + 1` (the paper states `f(x, y) ≤ 2|x| + 1`).
* `lemma_4_2`: `y < x`, `y ≥ 10` ⟹ `f(x, y) < y`.
* `lemma_4_3`: `x > y > z` ⟹ `f(x, y) ≠ f(y, z)` (the Cole–Vishkin property).
* `lemma_4_1`: iterating `F(x) = 2⌈log₂(x + 1)⌉ + 1` from `x ≥ 1` falls below `10` within
  `O(log* x)` steps (stated over `ℕ`, see its docstring).
-/

namespace AsyncCycle

/-- `lowDiff x y m = min ({m} ∪ { k < m | x_k ≠ y_k })`. -/
def lowDiff (x y : ℕ) : ℕ → ℕ
  | 0 => 0
  | m + 1 =>
    if lowDiff x y m < m then lowDiff x y m
    else if x.testBit m ≠ y.testBit m then m else m + 1

/-- The index `i` of Equation (6). -/
def cvIdx (x y : ℕ) : ℕ := lowDiff x y (min x.size y.size)

/-- The identifier-reduction function `f` of Equation (6). -/
def cvF (x y : ℕ) : ℕ := 2 * cvIdx x y + (x.testBit (cvIdx x y)).toNat

/-! ### Specification of `cvIdx` -/

lemma lowDiff_spec (x y : ℕ) : ∀ m, lowDiff x y m ≤ m ∧
    (∀ k < lowDiff x y m, x.testBit k = y.testBit k) ∧
    (lowDiff x y m < m → x.testBit (lowDiff x y m) ≠ y.testBit (lowDiff x y m)) := by
  intro m
  induction m with
  | zero => simp [lowDiff]
  | succ m ih =>
    obtain ⟨ih1, ih2, ih3⟩ := ih
    simp only [lowDiff]
    split_ifs with h1 h2
    · exact ⟨by omega, ih2, fun _ => ih3 h1⟩
    · have he : lowDiff x y m = m := by omega
      exact ⟨by omega, fun k hk => ih2 k (by omega), fun _ => h2⟩
    · have he : lowDiff x y m = m := by omega
      refine ⟨le_rfl, fun k hk => ?_, fun h => absurd h (lt_irrefl _)⟩
      rcases Nat.lt_or_ge k m with hkm | hkm
      · exact ih2 k (by omega)
      · obtain rfl : k = m := by omega
        simpa using h2

/-- `i ≤ min(|x|, |y|)`. -/
lemma cvIdx_le (x y : ℕ) : cvIdx x y ≤ min x.size y.size :=
  (lowDiff_spec x y _).1

/-- The bits of `x` and `y` agree below `i`. -/
lemma testBit_eq_of_lt_cvIdx {x y k : ℕ} (hk : k < cvIdx x y) : x.testBit k = y.testBit k :=
  (lowDiff_spec x y _).2.1 k hk

/-- If `i < min(|x|, |y|)`, then `i` is a position where the bits of `x` and `y` differ. -/
lemma testBit_cvIdx_ne {x y : ℕ} (h : cvIdx x y < min x.size y.size) :
    x.testBit (cvIdx x y) ≠ y.testBit (cvIdx x y) :=
  (lowDiff_spec x y _).2.2 h

/-- `f(x, y) ≤ 2 min(|x|, |y|) + 1`; in particular `f(x, y) ≤ 2|x| + 1` as stated in the
paper (Section 4.1). -/
lemma cvF_le (x y : ℕ) : cvF x y ≤ 2 * min x.size y.size + 1 := by
  have h1 := cvIdx_le x y
  have h2 := Bool.toNat_le (x.testBit (cvIdx x y))
  unfold cvF; omega

lemma two_mul_add_three_lt_two_pow : ∀ m, 4 ≤ m → 2 * m + 3 < 2 ^ m := by
  intro m hm
  induction m, hm using Nat.le_induction with
  | base => norm_num
  | succ m hm ih => rw [pow_succ]; omega

/-- `2|y| + 1 < y` for `y ≥ 10`. -/
lemma two_mul_size_add_one_lt {y : ℕ} (hy : 10 ≤ y) : 2 * y.size + 1 < y := by
  have hpos : 0 < y.size := Nat.size_pos.2 (by omega)
  have hle : 2 ^ (y.size - 1) ≤ y := Nat.lt_size.1 (by omega)
  rcases Nat.lt_or_ge y.size 5 with hs | hs
  · omega
  · have := two_mul_add_three_lt_two_pow (y.size - 1) (by omega)
    omega

/-- **Lemma 4.2** of [Fraigniaud, Lambein-Monette, Rabie, PODC 2022]: if `x > y ≥ 10`, then
`f(x, y) < y`. -/
theorem lemma_4_2 {x y : ℕ} (hxy : y < x) (hy : 10 ≤ y) : cvF x y < y := by
  have h1 := cvF_le x y
  have h2 : min x.size y.size = y.size := min_eq_right (Nat.size_le_size hxy.le)
  have h3 := two_mul_size_add_one_lt hy
  omega

/-- **Lemma 4.3** of [Fraigniaud, Lambein-Monette, Rabie, PODC 2022] (the Cole–Vishkin
property): if `x > y > z`, then `f(x, y) ≠ f(y, z)`. -/
theorem lemma_4_3 {x y z : ℕ} (hxy : y < x) (hyz : z < y) : cvF x y ≠ cvF y z := by
  intro h
  have hx := Bool.toNat_le (x.testBit (cvIdx x y))
  have hy := Bool.toNat_le (y.testBit (cvIdx y z))
  unfold cvF at h
  have hij : cvIdx x y = cvIdx y z := by omega
  have hb : x.testBit (cvIdx x y) = y.testBit (cvIdx x y) := by
    have hb' : (x.testBit (cvIdx x y)).toNat = (y.testBit (cvIdx y z)).toNat := by omega
    rw [← hij] at hb'
    cases h1 : x.testBit (cvIdx x y) <;> cases h2 : y.testBit (cvIdx x y) <;> simp_all
  have hmxy : min x.size y.size = y.size := min_eq_right (Nat.size_le_size hxy.le)
  have hmyz : min y.size z.size = z.size := min_eq_right (Nat.size_le_size hyz.le)
  have hi := cvIdx_le x y
  have hj := cvIdx_le y z
  rcases Nat.lt_or_ge (cvIdx x y) y.size with hlt | hge
  · exact testBit_cvIdx_ne (by omega) hb
  · -- `i = |y| = |z|` and `y`, `z` agree on all bits: `y = z`.
    have hzs : z.size = y.size := by omega
    have : y = z := by
      apply Nat.eq_of_testBit_eq
      intro k
      rcases Nat.lt_or_ge k y.size with hk | hk
      · exact testBit_eq_of_lt_cvIdx (by omega)
      · rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (Nat.lt_size_self y)
            (Nat.pow_le_pow_right (by norm_num) hk)),
          Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (Nat.lt_size_self z)
            (Nat.pow_le_pow_right (by norm_num) (by omega)))]
    omega

/-! ### Lemma 4.1 -/

/-- The function `F(x) = 2⌈log₂(x + 1)⌉ + 1` of Lemma 4.1 (on natural numbers). -/
def bigF (x : ℕ) : ℕ := 2 * Nat.clog 2 (x + 1) + 1

lemma bigF_eq (x : ℕ) : bigF x = 2 * x.size + 1 := by
  rw [bigF, Nat.size_eq_clog_two]

/-- `f(x, y) ≤ F(x)`. -/
lemma cvF_le_bigF (x y : ℕ) : cvF x y ≤ bigF x := by
  have := cvF_le x y
  have := min_le_left x.size y.size
  rw [bigF_eq]; omega

lemma bigF_mono : Monotone bigF := fun x y h => by
  rw [bigF_eq, bigF_eq]; have := Nat.size_le_size h; omega

/-- `F(x) < x` for `x ≥ 10`. -/
lemma bigF_lt {x : ℕ} (hx : 10 ≤ x) : bigF x < x := by
  rw [bigF_eq]; exact two_mul_size_add_one_lt hx

lemma four_mul_add_nine_lt_two_pow : ∀ m, 5 ≤ m → 4 * m + 9 < 2 ^ m := by
  intro m hm
  induction m, hm using Nat.le_induction with
  | base => norm_num
  | succ m hm ih => rw [pow_succ]; omega

/-- `F(F(x)) ≤ max 11 (log₂ x)`. -/
lemma bigF_bigF_le (x : ℕ) : bigF (bigF x) ≤ max 11 (Nat.log 2 x) := by
  rw [bigF_eq (bigF x), bigF_eq x]
  rcases Nat.eq_zero_or_pos x with rfl | hx
  · have : Nat.size 1 = 1 := by decide
    simp [this]
  rw [Nat.size_eq_log_two_add_one hx.ne']
  set ℓ := Nat.log 2 x
  rcases Nat.lt_or_ge ℓ 12 with hℓ | hℓ
  · have : (2 * (ℓ + 1) + 1).size ≤ 5 := Nat.size_le.2 (by norm_num; omega)
    omega
  · have hm := four_mul_add_nine_lt_two_pow ((ℓ - 2) / 2) (by omega)
    have : (2 * (ℓ + 1) + 1).size ≤ (ℓ - 2) / 2 := Nat.size_le.2 (by omega)
    omega

lemma iterate_bigF_two_le (k x : ℕ) : bigF^[2]^[k] x ≤ max 11 ((Nat.log 2)^[k] x) := by
  induction k with
  | zero => exact le_max_right _ _
  | succ k ih =>
    set L := (Nat.log 2)^[k] x
    calc bigF^[2]^[k + 1] x = bigF (bigF (bigF^[2]^[k] x)) := by
          rw [Function.iterate_succ_apply']; rfl
      _ ≤ bigF (bigF (max 11 L)) := bigF_mono (bigF_mono ih)
      _ ≤ max 11 (Nat.log 2 (max 11 L)) := bigF_bigF_le _
      _ ≤ max 11 (Nat.log 2 L) := by
        rcases le_total L 11 with h | h
        · rw [max_eq_left h]
          have : Nat.log 2 11 ≤ 11 := (Nat.log_lt_self 2 (by norm_num)).le
          omega
        · rw [max_eq_right h]
      _ = max 11 ((Nat.log 2)^[k + 1] x) := by rw [Function.iterate_succ_apply']

/-- **Lemma 4.1** of [Fraigniaud, Lambein-Monette, Rabie, PODC 2022], over `ℕ`: for
`F(x) = 2⌈log₂(x + 1)⌉ + 1`, there is a constant `α` such that for every `x ≥ 1` some
`t ≤ α log* x` satisfies `F^{(t)}(x) < 10`.

The paper states it for `F : [1, ∞) → [1, ∞)` on the reals; we use the integer version (the
identifiers are integers, and `F` takes odd integer values after one step anyway). The proof
gives `α = 3`. -/
theorem lemma_4_1 : ∃ α : ℕ, ∀ x ≥ 1, ∃ t ≤ α * Nat.logStar x, bigF^[t] x < 10 := by
  refine ⟨3, fun x _ => ?_⟩
  rcases Nat.lt_or_ge x 10 with hx | hx
  · exact ⟨0, Nat.zero_le _, hx⟩
  have hL : 1 ≤ Nat.logStar x := by
    unfold Nat.logStar; split_ifs <;> omega
  refine ⟨2 * Nat.logStar x + 1, by omega, ?_⟩
  rw [Function.iterate_succ_apply', Function.iterate_mul]
  have h1 := iterate_bigF_two_le (Nat.logStar x) x
  have h2 := Nat.iterate_log_logStar_le x
  have h3 : bigF^[2]^[Nat.logStar x] x ≤ 11 := by omega
  have h11 : bigF 11 < 10 := by
    rw [bigF_eq, show Nat.size 11 = 4 from le_antisymm (Nat.size_le.2 (by norm_num))
      (Nat.lt_size.2 (by norm_num))]
    norm_num
  exact lt_of_le_of_lt (bigF_mono h3) h11

end AsyncCycle
