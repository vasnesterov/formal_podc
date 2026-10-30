import Mathlib.Algebra.Order.Ring.Basic
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.GCongr

/-!
# Arithmetic for the proof of Theorem 4.3 (Section 8 of Leroux)

The constants of Section 8: `E₁ = (d−1)^(d−1) (1 + (2 + (d−1)^(d−1))^d)` (the exponent of Theorem 6.1
for `d − 1` places), `B = (4 + 4M + 2L)^E₁`, `h = d (1 + M) B`. The final estimate is
`h^(2^d + 4d + 9) ≤ (4 + 4M + 2L)^(d^((d+2)^2))`.
-/

namespace Podc.PPLeadersStateComplexity.Arith

/-- The exponent of Theorem 6.1 for `d − 1` places. -/
def E1 (d : ℕ) : ℕ := (d - 1) ^ (d - 1) * (1 + (2 + (d - 1) ^ (d - 1)) ^ d)

theorem two_add_le (d : ℕ) (hd : 2 ≤ d) : 2 + (d - 1) ^ (d - 1) + 1 ≤ d ^ d := by
  obtain ⟨j, rfl⟩ : ∃ j, d = j + 2 := ⟨d - 2, by omega⟩
  simp only [show j + 2 - 1 = j + 1 by omega]
  have h1 : (j + 2) ^ (j + 2) = (j + 2) * (j + 2) ^ (j + 1) := by rw [pow_succ']
  have h2 : (j + 1) ^ (j + 1) ≤ (j + 2) ^ (j + 1) := Nat.pow_le_pow_left (by omega) _
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · norm_num
  · have h3 : 2 ≤ (j + 1) ^ (j + 1) := by
      calc 2 ≤ (j + 1) ^ 1 := by simp; omega
        _ ≤ (j + 1) ^ (j + 1) := Nat.pow_le_pow_right (by omega) (by omega)
    nlinarith

theorem two_mul_le (d : ℕ) (hd : 2 ≤ d) : 2 * (d - 1) ^ (d - 1) ≤ d ^ d := by
  obtain ⟨j, rfl⟩ : ∃ j, d = j + 1 := ⟨d - 1, by omega⟩
  simp only [show j + 1 - 1 = j by omega]
  have h1 : (j + 1) ^ (j + 1) = (j + 1) * (j + 1) ^ j := by rw [pow_succ']
  have h2 : j ^ j ≤ (j + 1) ^ j := Nat.pow_le_pow_left (by omega) _
  have h3 : 2 * (j + 1) ^ j ≤ (j + 1) * (j + 1) ^ j := Nat.mul_le_mul_right _ (by omega)
  rw [h1]; omega

theorem one_add_pow_le (d : ℕ) (hd : 2 ≤ d) : 1 + (2 + (d - 1) ^ (d - 1)) ^ d ≤ d ^ (d ^ 2) := by
  have h := two_add_le d hd
  set x := d ^ d with hx
  have hx1 : 1 ≤ x := by omega
  have hle : (2 + (d - 1) ^ (d - 1)) ^ d ≤ (x - 1) ^ d := Nat.pow_le_pow_left (by omega) _
  have hd' : d ^ (d ^ 2) = x ^ d := by rw [hx, ← pow_mul, sq]
  rw [hd']
  have aux : ∀ y e : ℕ, 1 + y ^ (e + 1) ≤ (y + 1) ^ (e + 1) := by
    intro y e
    rw [pow_succ, pow_succ]
    have : y ^ e ≤ (y + 1) ^ e := Nat.pow_le_pow_left (by omega) _
    have : 1 ≤ (y + 1) ^ e := Nat.one_le_pow _ _ (by omega)
    nlinarith
  have := aux (x - 1) (d - 1)
  rw [show d - 1 + 1 = d by omega, show x - 1 + 1 = x by omega] at this
  omega

theorem two_pow_add_le (d : ℕ) (hd : 2 ≤ d) : 2 ^ d + 4 * d + 9 ≤ d ^ (3 * d + 4) := by
  have h1 : 2 ^ (3 * d + 4) ≤ d ^ (3 * d + 4) := Nat.pow_le_pow_left hd _
  have h2 : 2 ^ (3 * d + 4) = 2 ^ d * 2 ^ (2 * d) * 16 := by
    rw [show 3 * d + 4 = d + 2 * d + 4 by ring, pow_add, pow_add]; norm_num
  have h3 : d < 2 ^ d := Nat.lt_two_pow_self
  have h4 : 1 ≤ 2 ^ (2 * d) := Nat.one_le_two_pow
  have h5 : 2 ^ d ≤ 2 ^ (2 * d) := Nat.pow_le_pow_right (by omega) (by omega)
  nlinarith

/-- `2 E₁ (2^d + 4d + 9) ≤ d^((d+2)^2)`. -/
theorem exponent_le (d : ℕ) (hd : 2 ≤ d) : 2 * E1 d * (2 ^ d + 4 * d + 9) ≤ d ^ ((d + 2) ^ 2) := by
  have h1 := two_mul_le d hd
  have h2 := one_add_pow_le d hd
  have h3 := two_pow_add_le d hd
  have e : d ^ ((d + 2) ^ 2) = d ^ d * d ^ (d ^ 2) * d ^ (3 * d + 4) := by
    rw [← pow_add, ← pow_add]; congr 1; ring
  rw [e, E1]
  calc 2 * ((d - 1) ^ (d - 1) * (1 + (2 + (d - 1) ^ (d - 1)) ^ d)) * (2 ^ d + 4 * d + 9)
      = (2 * (d - 1) ^ (d - 1)) * (1 + (2 + (d - 1) ^ (d - 1)) ^ d) * (2 ^ d + 4 * d + 9) := by
        ring
    _ ≤ d ^ d * d ^ (d ^ 2) * d ^ (3 * d + 4) := by gcongr

theorem le_E1 (d : ℕ) (hd : 2 ≤ d) : d ^ d ≤ E1 d := by
  have h1 : 1 ≤ (d - 1) ^ (d - 1) := Nat.one_le_pow _ _ (by omega)
  have h2 : d ≤ 2 + (d - 1) ^ (d - 1) := by
    have : d - 1 ≤ (d - 1) ^ (d - 1) := by
      calc d - 1 = (d - 1) ^ 1 := (pow_one _).symm
        _ ≤ (d - 1) ^ (d - 1) := Nat.pow_le_pow_right (by omega) (by omega)
    omega
  have h3 : d ^ d ≤ (2 + (d - 1) ^ (d - 1)) ^ d := Nat.pow_le_pow_left h2 _
  unfold E1
  calc d ^ d ≤ 1 + (2 + (d - 1) ^ (d - 1)) ^ d := by omega
    _ ≤ (d - 1) ^ (d - 1) * (1 + (2 + (d - 1) ^ (d - 1)) ^ d) := Nat.le_mul_of_pos_left _ h1

theorem d_lt_E1 (d : ℕ) (hd : 2 ≤ d) : d < E1 d := by
  have := le_E1 d hd
  have : d < d ^ d := by
    calc d < 2 ^ d := Nat.lt_two_pow_self
      _ ≤ d ^ d := Nat.pow_le_pow_left hd _
  omega

/-- `d (1 + M) ≤ B`, hence `h ≤ B²`. -/
theorem mul_le_B (d M L : ℕ) (hd : 2 ≤ d) : d * (1 + M) ≤ (4 + 4 * M + 2 * L) ^ E1 d := by
  have h1 := d_lt_E1 d hd
  have h2 : (4 + 4 * M) ^ E1 d ≤ (4 + 4 * M + 2 * L) ^ E1 d := Nat.pow_le_pow_left (by omega) _
  obtain ⟨e, he⟩ : ∃ e, E1 d = e + 1 := ⟨E1 d - 1, by omega⟩
  have h3 : (4 + 4 * M) ^ (e + 1) = (4 + 4 * M) ^ e * (4 + 4 * M) := pow_succ _ _
  have h4 : d < 4 ^ e := by
    calc d < 2 ^ d := Nat.lt_two_pow_self
      _ ≤ 4 ^ d := Nat.pow_le_pow_left (by omega) _
      _ ≤ 4 ^ e := Nat.pow_le_pow_right (by omega) (by omega)
  have h5 : 4 ^ e ≤ (4 + 4 * M) ^ e := Nat.pow_le_pow_left (by omega) _
  rw [he] at h2 ⊢
  have h6 : d * (4 + 4 * M) ≤ (4 + 4 * M) ^ e * (4 + 4 * M) :=
    Nat.mul_le_mul_right _ (by omega)
  have h7 : d * (1 + M) ≤ d * (4 + 4 * M) := Nat.mul_le_mul_left _ (by omega)
  omega

/-- `M (1 + M)^(d^d) ≤ d (1 + M) B` (the hypothesis of Lemma 5.4 for `h`). -/
theorem lemma_5_4_hyp (d M L : ℕ) (hd : 2 ≤ d) :
    M * (1 + M) ^ (d ^ d) ≤ d * (1 + M) * (4 + 4 * M + 2 * L) ^ E1 d := by
  have h1 : (1 + M) ^ (d ^ d) ≤ (4 + 4 * M + 2 * L) ^ E1 d :=
    calc (1 + M) ^ (d ^ d) ≤ (4 + 4 * M + 2 * L) ^ (d ^ d) := Nat.pow_le_pow_left (by omega) _
      _ ≤ (4 + 4 * M + 2 * L) ^ E1 d := Nat.pow_le_pow_right (by omega) (le_E1 d hd)
  have h2 : M ≤ d * (1 + M) := by nlinarith
  exact Nat.mul_le_mul h2 h1

/-- The final estimate: `h^(2^d + 4d + 9) ≤ (4 + 4M + 2L)^(d^((d+2)^2))`. -/
theorem final (d M L : ℕ) (hd : 2 ≤ d) :
    (d * (1 + M) * (4 + 4 * M + 2 * L) ^ E1 d) ^ (2 ^ d + 4 * d + 9) ≤
      (4 + 4 * M + 2 * L) ^ (d ^ ((d + 2) ^ 2)) := by
  set B := (4 + 4 * M + 2 * L) ^ E1 d with hB
  have h1 : d * (1 + M) * B ≤ (4 + 4 * M + 2 * L) ^ (2 * E1 d) := by
    rw [show 2 * E1 d = E1 d + E1 d by ring, pow_add]; exact Nat.mul_le_mul_right _ (mul_le_B d M L hd)
  calc (d * (1 + M) * B) ^ (2 ^ d + 4 * d + 9)
      ≤ ((4 + 4 * M + 2 * L) ^ (2 * E1 d)) ^ (2 ^ d + 4 * d + 9) := Nat.pow_le_pow_left h1 _
    _ = (4 + 4 * M + 2 * L) ^ (2 * E1 d * (2 ^ d + 4 * d + 9)) := by rw [← pow_mul]
    _ ≤ (4 + 4 * M + 2 * L) ^ (d ^ ((d + 2) ^ 2)) :=
        Nat.pow_le_pow_right (by omega) (exponent_le d hd)

/-! ### The inequalities used in Section 8

`h` is any number with `2 ≤ d`, `2 B (1 + M) ≤ h`, `d ≤ h`, `2 ≤ h`. We use
`a = h^(2d+3)`, `ℓ = h^(2^d+2d+4)`, `k = d h^(2^d+1)` and the threshold `h^(2d+5) ℓ`. -/

section Section8

variable {d M B h : ℕ} (hd : 2 ≤ d) (hB1 : 1 ≤ B) (hB : 2 * B * (1 + M) ≤ h) (hdh : d ≤ h)
  (h2 : 2 ≤ h)
include hd hB1 hB hdh h2

theorem B_le : B ≤ h := by nlinarith
theorem M_le : M + 1 ≤ h := by nlinarith

theorem f3 : M * (B * B * (M + 1) ^ (2 * d)) ≤ h ^ (2 * d + 3) := by
  have hBh := B_le hd hB1 hB hdh h2
  have hMh := M_le hd hB1 hB hdh h2
  have : (M + 1) ^ (2 * d) ≤ h ^ (2 * d) := Nat.pow_le_pow_left hMh _
  calc M * (B * B * (M + 1) ^ (2 * d)) ≤ h * (h * h * h ^ (2 * d)) := by gcongr; omega
    _ = h ^ (2 * d + 3) := by ring

theorem f4 {a ℓ : ℕ} (ha : 1 ≤ a) (hℓ : 1 ≤ ℓ) :
    (B + a * ℓ * B) * M + ℓ * a + ℓ ≤ h ^ 2 * a * ℓ := by
  have h1 : 1 ≤ a * ℓ := Nat.one_le_iff_ne_zero.2 (by positivity)
  have h4 : 4 * (a * ℓ * B * (1 + M)) ≤ 2 * (a * ℓ) * h := by nlinarith
  have h5 : 2 * (a * ℓ) * h ≤ h * (a * ℓ) * h := by gcongr
  have hZ : 1 ≤ B * (1 + M) := Nat.one_le_iff_ne_zero.2 (by positivity)
  have e0 : a * ℓ * B * (1 + M) = (a * ℓ) * (B * (1 + M)) := by ring
  have e1 : B * M ≤ a * ℓ * B * (1 + M) := by
    rw [e0]; calc B * M ≤ B * (1 + M) := by gcongr; omega
      _ ≤ (a * ℓ) * (B * (1 + M)) := Nat.le_mul_of_pos_left _ h1
  have e2 : a * ℓ * B * M ≤ a * ℓ * B * (1 + M) := by gcongr; omega
  have e3 : ℓ * a ≤ a * ℓ * B * (1 + M) := by
    rw [e0, mul_comm ℓ a]; exact Nat.le_mul_of_pos_right _ hZ
  have e4 : ℓ ≤ a * ℓ * B * (1 + M) := by
    rw [e0]; calc ℓ ≤ a * ℓ := Nat.le_mul_of_pos_left _ ha
      _ ≤ (a * ℓ) * (B * (1 + M)) := Nat.le_mul_of_pos_right _ hZ
  nlinarith

theorem f5 : M * ((B * (M + 1) ^ (2 * d) + d) * B * h ^ (2 ^ d - 1)) ≤ h ^ (2 ^ d + 2 * d + 4) := by
  have hBh := B_le hd hB1 hB hdh h2
  have hMh := M_le hd hB1 hB hdh h2
  have e1 : B * (M + 1) ^ (2 * d) ≤ h ^ (2 * d + 1) := by
    rw [pow_succ']; exact Nat.mul_le_mul hBh (Nat.pow_le_pow_left hMh _)
  have e2 : d ≤ h ^ (2 * d + 1) :=
    hdh.trans (by simpa using Nat.pow_le_pow_right (by omega : 1 ≤ h) (by omega : 1 ≤ 2 * d + 1))
  have e3 : 1 ≤ 2 ^ d := Nat.one_le_two_pow
  calc M * ((B * (M + 1) ^ (2 * d) + d) * B * h ^ (2 ^ d - 1))
      ≤ h * ((h ^ (2 * d + 1) + h ^ (2 * d + 1)) * h * h ^ (2 ^ d - 1)) := by gcongr; omega
    _ = 2 * h ^ (2 ^ d + 2 * d + 2) := by
        rw [show 2 ^ d + 2 * d + 2 = (2 ^ d - 1) + (2 * d + 1) + 1 + 1 by omega]
        ring
    _ ≤ h * h ^ (2 ^ d + 2 * d + 2) := Nat.mul_le_mul_right _ h2
    _ = h ^ (2 ^ d + 2 * d + 3) := by ring
    _ ≤ h ^ (2 ^ d + 2 * d + 4) := Nat.pow_le_pow_right (by omega) (by omega)

theorem f6 : d * h ^ (2 ^ d + 1) + B ≤ h ^ (2 ^ d + 2 * d + 4) := by
  have hBh := B_le hd hB1 hB hdh h2
  have e1 : B ≤ h ^ (2 ^ d + 1) :=
    hBh.trans (by simpa using Nat.pow_le_pow_right (by omega : 1 ≤ h) (Nat.le_add_left 1 (2 ^ d)))
  have e2 : d + 1 ≤ h ^ (2 * d + 3) := by
    calc d + 1 ≤ 2 ^ (2 * d + 3) := by
          have : 2 * d + 3 < 2 ^ (2 * d + 3) := Nat.lt_two_pow_self
          omega
      _ ≤ h ^ (2 * d + 3) := Nat.pow_le_pow_left h2 _
  calc d * h ^ (2 ^ d + 1) + B ≤ (d + 1) * h ^ (2 ^ d + 1) := by nlinarith
    _ ≤ h ^ (2 * d + 3) * h ^ (2 ^ d + 1) := Nat.mul_le_mul_right _ e2
    _ = h ^ (2 ^ d + 2 * d + 4) := by rw [← pow_add]; congr 1; ring

theorem f7 : 3 * h + d * h ^ (2 ^ d + 1) ≤ h ^ (2 * d + 5) * h ^ (2 ^ d + 2 * d + 4) := by
  have e1 : h ≤ h ^ (2 ^ d + 1) := by
    simpa using Nat.pow_le_pow_right (by omega : 1 ≤ h) (Nat.le_add_left 1 (2 ^ d))
  have e2 : d + 3 ≤ h ^ (4 * d + 8) := by
    calc d + 3 ≤ 2 ^ (4 * d + 8) := by
          have : 4 * d + 8 < 2 ^ (4 * d + 8) := Nat.lt_two_pow_self
          omega
      _ ≤ h ^ (4 * d + 8) := Nat.pow_le_pow_left h2 _
  calc 3 * h + d * h ^ (2 ^ d + 1) ≤ (d + 3) * h ^ (2 ^ d + 1) := by nlinarith
    _ ≤ h ^ (4 * d + 8) * h ^ (2 ^ d + 1) := Nat.mul_le_mul_right _ e2
    _ = h ^ (2 * d + 5) * h ^ (2 ^ d + 2 * d + 4) := by rw [← pow_add, ← pow_add]; congr 1; ring

theorem f8 {X s : ℕ} (hX : X ≤ d * h) (hs : s ≤ B) :
    X * s * (1 + M) * (2 * s * (1 + M)) ^ (2 ^ d - 1) < d * h ^ (2 ^ d + 1) := by
  have e1 : 2 * s * (1 + M) ≤ h := le_trans (by gcongr) hB
  have e2 : (2 * s * (1 + M)) ^ (2 ^ d - 1) ≤ h ^ (2 ^ d - 1) := Nat.pow_le_pow_left e1 _
  have e3 : s * (1 + M) < h := by nlinarith
  have e4 : 0 < d * h := by positivity
  have e5 : 1 ≤ 2 ^ d := Nat.one_le_two_pow
  calc X * s * (1 + M) * (2 * s * (1 + M)) ^ (2 ^ d - 1)
      ≤ d * h * (s * (1 + M)) * h ^ (2 ^ d - 1) := by rw [mul_assoc X s]; gcongr
    _ < d * h * h * h ^ (2 ^ d - 1) := by
        apply Nat.mul_lt_mul_of_pos_right _ (by positivity)
        exact Nat.mul_lt_mul_of_pos_left e3 e4
    _ = d * h ^ (2 ^ d + 1) := by
        rw [show 2 ^ d + 1 = (2 ^ d - 1) + 1 + 1 by omega]; ring

end Section8

end Podc.PPLeadersStateComplexity.Arith
