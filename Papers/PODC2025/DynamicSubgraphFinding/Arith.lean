import Mathlib

/-!
# Arithmetic for the asymptotic forms of Theorems 1.3 and 1.6
-/

namespace Podc.DynamicSubgraphFinding

/-- `(B + 1) · 10 q² (2^{B+1})² < L` as soon as `2^{8B} ≤ L` and `(40 q²)³ < L`. -/
lemma key_bound (q B L : ℕ) (hL1 : 2 ^ (8 * B) ≤ L) (hL2 : (40 * q ^ 2) ^ 3 < L) :
    (B + 1) * (10 * q ^ 2 * (2 ^ (B + 1)) ^ 2) < L := by
  set X := 2 ^ B with hX
  have hX1 : 1 ≤ X := Nat.one_le_two_pow
  have hBX : B + 1 ≤ X := Nat.lt_two_pow_self
  have h8 : 2 ^ (8 * B) = X ^ 8 := by rw [hX, ← pow_mul, mul_comm]
  have h2 : 2 ^ (B + 1) = 2 * X := by rw [pow_succ, mul_comm]
  rw [h8] at hL1
  rw [h2]
  have hle : (B + 1) * (10 * q ^ 2 * (2 * X) ^ 2) ≤ 40 * q ^ 2 * X ^ 3 := by
    have : (B + 1) * (10 * q ^ 2 * (2 * X) ^ 2) = (B + 1) * (40 * q ^ 2 * X ^ 2) := by ring
    rw [this]
    calc (B + 1) * (40 * q ^ 2 * X ^ 2) ≤ X * (40 * q ^ 2 * X ^ 2) := Nat.mul_le_mul_right _ hBX
      _ = 40 * q ^ 2 * X ^ 3 := by ring
  refine lt_of_le_of_lt hle ?_
  by_cases hc : 40 * q ^ 2 < X ^ 2
  · calc 40 * q ^ 2 * X ^ 3 < X ^ 2 * X ^ 3 := Nat.mul_lt_mul_of_pos_right hc (by positivity)
      _ = X ^ 5 := by ring
      _ ≤ X ^ 8 := Nat.pow_le_pow_right hX1 (by norm_num)
      _ ≤ L := hL1
  · push_neg at hc
    calc 40 * q ^ 2 * X ^ 3 ≤ 40 * q ^ 2 * X ^ 4 :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hX1 (by norm_num))
      _ = 40 * q ^ 2 * (X ^ 2) ^ 2 := by ring
      _ ≤ 40 * q ^ 2 * (40 * q ^ 2) ^ 2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hc 2)
      _ = (40 * q ^ 2) ^ 3 := by ring
      _ < L := hL2

/-- `(W^a + 1)(1 + 2 W W^b) + W q ≤ W^{a+b+5}` for `W ≥ 2` and `q ≤ W^a`. -/
lemma sum_bound (W a b q : ℕ) (hW : 2 ≤ W) (hq : q ≤ W ^ a) :
    (W ^ a + 1) + (W ^ a + 1) * (W * (2 * W ^ b)) + W * q ≤ W ^ (a + b + 5) := by
  have hW1 : 1 ≤ W := by omega
  have ha1 : 1 ≤ W ^ a := Nat.one_le_pow _ _ (by omega)
  have hb1 : 1 ≤ W ^ b := Nat.one_le_pow _ _ (by omega)
  have e : W ^ (a + b + 5) = W ^ a * W ^ b * W ^ 5 := by rw [pow_add, pow_add]
  rw [e]
  have hW5 : 32 ≤ W ^ 5 := by
    calc 32 = 2 ^ 5 := by norm_num
      _ ≤ W ^ 5 := Nat.pow_le_pow_left hW 5
  have : W ^ 5 = W * W ^ 4 := by ring
  have hW4 : 16 ≤ W ^ 4 := by
    calc 16 = 2 ^ 4 := by norm_num
      _ ≤ W ^ 4 := Nat.pow_le_pow_left hW 4
  rw [this]
  generalize W ^ a = A at *
  generalize W ^ b = C at *
  generalize W ^ 4 = D at *
  have h1 : A + 1 ≤ 2 * A := by omega
  have hAC : 1 ≤ A * C := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hP : 1 ≤ A * C * W := by nlinarith
  calc A + 1 + (A + 1) * (W * (2 * C)) + W * q
      ≤ 2 * A + (2 * A) * (W * (2 * C)) + W * A := by
        gcongr
    _ ≤ 2 * (A * C * W) + 4 * (A * C * W) + A * C * W := by
        have : A ≤ A * C * W := by nlinarith
        have : W * A ≤ A * C * W := by nlinarith
        nlinarith
    _ = 7 * (A * C * W) := by ring
    _ ≤ D * (A * C * W) := Nat.mul_le_mul_right _ (by omega)
    _ = A * C * (W * D) := by ring

/-- `19 q² (4^{B+1})² (B + 1) ≤ L` as soon as `2^{16B} ≤ L` and `(304 q²)⁴ ≤ L`. -/
lemma key_bound16 (q B L : ℕ) (hL1 : 2 ^ (16 * B) ≤ L) (hL2 : (304 * q ^ 2) ^ 4 ≤ L) :
    19 * q ^ 2 * (4 ^ (B + 1)) ^ 2 * (B + 1) ≤ L := by
  set Z := 2 ^ B with hZ
  have hZ1 : 1 ≤ Z := Nat.one_le_two_pow
  have hBZ : B + 1 ≤ Z := Nat.lt_two_pow_self
  have h16 : 2 ^ (16 * B) = Z ^ 16 := by rw [hZ, ← pow_mul, mul_comm]
  have h4 : 4 ^ (B + 1) = 4 * Z ^ 2 := by
    rw [hZ, pow_succ, ← pow_mul, show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul, mul_comm B 2]
    ring
  rw [h16] at hL1
  rw [h4]
  have hle : 19 * q ^ 2 * (4 * Z ^ 2) ^ 2 * (B + 1) ≤ 304 * q ^ 2 * Z ^ 5 := by
    calc 19 * q ^ 2 * (4 * Z ^ 2) ^ 2 * (B + 1) ≤ 19 * q ^ 2 * (4 * Z ^ 2) ^ 2 * Z :=
          Nat.mul_le_mul_left _ hBZ
      _ = 304 * q ^ 2 * Z ^ 5 := by ring
  refine le_trans hle ?_
  by_cases hc : 304 * q ^ 2 < Z ^ 2
  · calc 304 * q ^ 2 * Z ^ 5 ≤ Z ^ 2 * Z ^ 5 := Nat.mul_le_mul_right _ hc.le
      _ = Z ^ 7 := by ring
      _ ≤ Z ^ 16 := Nat.pow_le_pow_right hZ1 (by norm_num)
      _ ≤ L := hL1
  · push_neg at hc
    calc 304 * q ^ 2 * Z ^ 5 ≤ 304 * q ^ 2 * Z ^ 6 :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hZ1 (by norm_num))
      _ = 304 * q ^ 2 * (Z ^ 2) ^ 3 := by ring
      _ ≤ 304 * q ^ 2 * (304 * q ^ 2) ^ 3 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hc 3)
      _ = (304 * q ^ 2) ^ 4 := by ring
      _ ≤ L := hL2

lemma pow_combo (W q R t : ℕ) :
    ((W ^ q) ^ (R + 1) * ((W ^ q) ^ (R + 1) * (W ^ q * W ^ q))) ^ t =
      W ^ (t * (2 * (q * (R + 1)) + 2 * q)) := by
  simp only [← pow_mul, ← pow_add]
  ring_nf

lemma G_bound (q t B : ℕ) (hq : 1 ≤ q) (ht : 4 ≤ t) :
    2 * ((B + 1) * (t * (2 * (q * (2 * q * t + 1)) + 2 * q) + 1)) + 1 ≤
      19 * q ^ 2 * t ^ 2 * (B + 1) := by
  have hu : 4 ≤ q * t := by nlinarith
  have e : 2 * ((B + 1) * (t * (2 * (q * (2 * q * t + 1)) + 2 * q) + 1)) + 1 =
      (B + 1) * (8 * (q * t) ^ 2 + 8 * (q * t) + 2) + 1 := by ring
  have e2 : 19 * q ^ 2 * t ^ 2 * (B + 1) = (B + 1) * (19 * (q * t) ^ 2) := by ring
  rw [e, e2]
  generalize q * t = u at *
  have h1 : 8 * u + 3 ≤ 11 * u ^ 2 := by nlinarith
  nlinarith

lemma size_bound (X G tq n : ℕ) (hX1 : X + 1 ≤ 2 ^ G) (htq : tq ≤ 2 ^ G)
    (h : 2 ^ (2 ^ (2 * G + 1)) ≤ n) : (X + 1) ^ (2 * X + 1) + tq < n := by
  have h1 : (X + 1) ^ (2 * X + 1) ≤ 2 ^ (G * (2 * X + 1)) := by
    rw [pow_mul]; exact Nat.pow_le_pow_left hX1 _
  have h2 : tq ≤ 2 ^ (G * (2 * X + 1)) :=
    le_trans htq (Nat.pow_le_pow_right (by norm_num) (Nat.le_mul_of_pos_right _ (by omega)))
  have hGlt : G < 2 ^ G := Nat.lt_two_pow_self
  have h3 : G * (2 * X + 1) + 1 < 2 ^ (2 * G + 1) := by
    have hX2 : 2 * X + 1 ≤ 2 * 2 ^ G - 1 := by omega
    have : G * (2 * X + 1) + 1 ≤ G * (2 * 2 ^ G) + 1 :=
      Nat.add_le_add_right (Nat.mul_le_mul_left _ (by omega)) 1
    have h4 : G * (2 * 2 ^ G) + 1 ≤ 2 ^ (2 * G + 1) := by
      have : 2 ^ (2 * G + 1) = 2 ^ G * (2 * 2 ^ G) := by ring
      rw [this]
      have : (G + 1) * (2 * 2 ^ G) ≤ 2 ^ G * (2 * 2 ^ G) := Nat.mul_le_mul_right _ hGlt
      have : 1 ≤ 2 * 2 ^ G := by have := Nat.one_le_two_pow (n := G); omega
      nlinarith
    by_cases hG0 : G = 0
    · subst hG0; simp at hX1; subst hX1; norm_num
    · have : G * (2 * X + 1) + 1 < G * (2 * 2 ^ G) + 1 := by
        have : 2 * X + 1 < 2 * 2 ^ G := by omega
        have := Nat.mul_lt_mul_of_pos_left this (Nat.pos_of_ne_zero hG0)
        omega
      omega
  have h5 : 2 ^ (G * (2 * X + 1) + 1) < 2 ^ (2 ^ (2 * G + 1)) :=
    Nat.pow_lt_pow_right (by norm_num) h3
  rw [pow_succ] at h5
  omega

end Podc.DynamicSubgraphFinding
