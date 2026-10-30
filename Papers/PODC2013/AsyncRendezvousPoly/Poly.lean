import Papers.PODC2013.AsyncRendezvousPoly.Trajectories

/-!
# Polynomiality of the cost bound (part of Theorem 3.1)

Dieudonné, Pelc, Villain, *How to meet asynchronously at polynomial cost*, PODC 2013
(arXiv:1301.7119v2), §3.

All the lengths `|X(k)|, …, |Ω(k)|` and the cost bound `Π` are monotone in `k` (for monotone `P`)
and polynomially bounded when `P` is. Consequently the bound `piBound P (2(n + l) + 1)` with
`l = 2m + 2` (the length of the modified label) is polynomial in `n` and `m`.
-/

namespace Podc.AsyncRendezvousPoly

open Finset

/-- Polynomially bounded functions. -/
def PolyBounded (f : ℕ → ℕ) : Prop := ∃ C d : ℕ, ∀ k, f k ≤ C * (k + 1) ^ d

namespace PolyBounded

theorem const (c : ℕ) : PolyBounded (fun _ => c) := ⟨c, 0, fun k => by simp⟩

theorem of_le {f g : ℕ → ℕ} (hg : PolyBounded g) (h : ∀ k, f k ≤ g k) : PolyBounded f := by
  obtain ⟨C, d, hC⟩ := hg
  exact ⟨C, d, fun k => (h k).trans (hC k)⟩

private theorem pow_le_pow_add_left (k a b : ℕ) : (k + 1) ^ a ≤ (k + 1) ^ (a + b) :=
  Nat.pow_le_pow_right (by omega) (by omega)

private theorem pow_le_pow_add_right (k a b : ℕ) : (k + 1) ^ b ≤ (k + 1) ^ (a + b) :=
  Nat.pow_le_pow_right (by omega) (by omega)

theorem add {f g : ℕ → ℕ} (hf : PolyBounded f) (hg : PolyBounded g) :
    PolyBounded (fun k => f k + g k) := by
  obtain ⟨C₁, d₁, h₁⟩ := hf
  obtain ⟨C₂, d₂, h₂⟩ := hg
  refine ⟨C₁ + C₂, d₁ + d₂, fun k => ?_⟩
  have a := pow_le_pow_add_left k d₁ d₂
  have b := pow_le_pow_add_right k d₁ d₂
  calc f k + g k ≤ C₁ * (k + 1) ^ d₁ + C₂ * (k + 1) ^ d₂ := Nat.add_le_add (h₁ k) (h₂ k)
    _ ≤ C₁ * (k + 1) ^ (d₁ + d₂) + C₂ * (k + 1) ^ (d₁ + d₂) := by gcongr
    _ = (C₁ + C₂) * (k + 1) ^ (d₁ + d₂) := by ring

theorem mul {f g : ℕ → ℕ} (hf : PolyBounded f) (hg : PolyBounded g) :
    PolyBounded (fun k => f k * g k) := by
  obtain ⟨C₁, d₁, h₁⟩ := hf
  obtain ⟨C₂, d₂, h₂⟩ := hg
  refine ⟨C₁ * C₂, d₁ + d₂, fun k => ?_⟩
  calc f k * g k ≤ (C₁ * (k + 1) ^ d₁) * (C₂ * (k + 1) ^ d₂) := Nat.mul_le_mul (h₁ k) (h₂ k)
    _ = C₁ * C₂ * (k + 1) ^ (d₁ + d₂) := by ring

theorem const_mul (c : ℕ) {f : ℕ → ℕ} (hf : PolyBounded f) : PolyBounded (fun k => c * f k) :=
  (const c).mul hf

theorem id : PolyBounded (fun k => k) := ⟨1, 1, fun k => by simp⟩

theorem comp_mul {f : ℕ → ℕ} (hf : PolyBounded f) (c : ℕ) : PolyBounded (fun k => f (c * k)) := by
  obtain ⟨C, d, h⟩ := hf
  refine ⟨C * (c + 1) ^ d, d, fun k => ?_⟩
  have hle : c * k + 1 ≤ (c + 1) * (k + 1) := by nlinarith
  calc f (c * k) ≤ C * (c * k + 1) ^ d := h _
    _ ≤ C * ((c + 1) * (k + 1)) ^ d := by gcongr
    _ = C * (c + 1) ^ d * (k + 1) ^ d := by rw [mul_pow, mul_assoc]

/-- `k ↦ ∑_{i < k} f (i + 1)` is polynomially bounded when `f` is. -/
theorem sum_range_succ {f : ℕ → ℕ} (hf : PolyBounded f) :
    PolyBounded (fun k => ∑ i ∈ range k, f (i + 1)) := by
  obtain ⟨C, d, h⟩ := hf
  refine ⟨C, d + 1, fun k => ?_⟩
  have hterm : ∀ i ∈ range k, f (i + 1) ≤ C * (k + 1) ^ d := by
    intro i hi
    have hi : i + 1 + 1 ≤ k + 1 := by simp at hi; omega
    calc f (i + 1) ≤ C * (i + 1 + 1) ^ d := h _
      _ ≤ C * (k + 1) ^ d := by gcongr
  calc ∑ i ∈ range k, f (i + 1) ≤ (range k).card • (C * (k + 1) ^ d) :=
        Finset.sum_le_card_nsmul _ _ _ hterm
    _ = k * (C * (k + 1) ^ d) := by simp
    _ ≤ (k + 1) * (C * (k + 1) ^ d) := by gcongr; omega
    _ = C * (k + 1) ^ (d + 1) := by ring

theorem two_mul_sub_one : PolyBounded (fun k => 2 * k - 1) :=
  (const_mul 2 id).of_le (fun k => by omega)

end PolyBounded

/-! ### Monotonicity -/

section Mono

variable {P : ℕ → ℕ}

private theorem sum_range_mono (f : ℕ → ℕ) : Monotone (fun k => ∑ i ∈ range k, f i) :=
  fun _ _ h => Finset.sum_le_sum_of_subset (Finset.range_subset_range.2 h)

theorem lenX_mono (hP : Monotone P) : Monotone (lenX P) :=
  fun _ _ h => Nat.mul_le_mul_left 2 (hP h)

theorem lenQ_mono : Monotone (lenQ P) := sum_range_mono _

theorem lenY'_mono (hP : Monotone P) : Monotone (lenY' P) := fun _ _ h => by
  unfold lenY'
  exact Nat.add_le_add (Nat.mul_le_mul (Nat.add_le_add_right (hP h) 1) (lenQ_mono h)) (hP h)

theorem lenY_mono (hP : Monotone P) : Monotone (lenY P) :=
  fun _ _ h => Nat.mul_le_mul_left 2 (lenY'_mono hP h)

theorem lenZ_mono : Monotone (lenZ P) := sum_range_mono _

theorem lenA'_mono (hP : Monotone P) : Monotone (lenA' P) := fun _ _ h => by
  unfold lenA'
  exact Nat.add_le_add (Nat.mul_le_mul (Nat.add_le_add_right (hP h) 1) (lenZ_mono h)) (hP h)

theorem lenA_mono (hP : Monotone P) : Monotone (lenA P) :=
  fun _ _ h => Nat.mul_le_mul_left 2 (lenA'_mono hP h)

theorem lenB_mono (hP : Monotone P) : Monotone (lenB P) := fun a b h => by
  unfold lenB
  exact Nat.mul_le_mul (Nat.mul_le_mul_left 2 (lenA_mono hP (by omega : 4 * a ≤ 4 * b)))
    (lenY_mono hP h)

theorem lenK_mono (hP : Monotone P) : Monotone (lenK P) := fun a b h => by
  unfold lenK
  exact Nat.mul_le_mul (Nat.mul_le_mul_left 2 (Nat.add_le_add
    (lenB_mono hP (by omega : 4 * a ≤ 4 * b)) (lenA_mono hP (by omega : 8 * a ≤ 8 * b))))
    (lenX_mono hP h)

theorem lenOm_mono (hP : Monotone P) : Monotone (lenOm P) := fun a b h => by
  unfold lenOm
  exact Nat.mul_le_mul (Nat.mul_le_mul (by omega) (lenK_mono hP h)) (lenX_mono hP h)

/-- `piBound` is a sum of nonnegative terms, hence monotone in the number of iterations. -/
theorem piBound_mono : Monotone (piBound P) := sum_range_mono _

end Mono

/-! ### Polynomial bounds -/

section Poly

variable {P : ℕ → ℕ}

theorem lenX_poly (hpoly : PolyBounded P) : PolyBounded (lenX P) :=
  PolyBounded.const_mul 2 hpoly

theorem lenQ_poly (hpoly : PolyBounded P) : PolyBounded (lenQ P) :=
  (lenX_poly hpoly).sum_range_succ

theorem lenY'_poly (hpoly : PolyBounded P) : PolyBounded (lenY' P) :=
  ((hpoly.add (PolyBounded.const 1)).mul (lenQ_poly hpoly)).add hpoly

theorem lenY_poly (hpoly : PolyBounded P) : PolyBounded (lenY P) :=
  PolyBounded.const_mul 2 (lenY'_poly hpoly)

theorem lenZ_poly (hpoly : PolyBounded P) : PolyBounded (lenZ P) :=
  (lenY_poly hpoly).sum_range_succ

theorem lenA'_poly (hpoly : PolyBounded P) : PolyBounded (lenA' P) :=
  ((hpoly.add (PolyBounded.const 1)).mul (lenZ_poly hpoly)).add hpoly

theorem lenA_poly (hpoly : PolyBounded P) : PolyBounded (lenA P) :=
  PolyBounded.const_mul 2 (lenA'_poly hpoly)

theorem lenB_poly (hpoly : PolyBounded P) : PolyBounded (lenB P) :=
  (PolyBounded.const_mul 2 ((lenA_poly hpoly).comp_mul 4)).mul (lenY_poly hpoly)

theorem lenK_poly (hpoly : PolyBounded P) : PolyBounded (lenK P) :=
  (PolyBounded.const_mul 2
    (((lenB_poly hpoly).comp_mul 4).add ((lenA_poly hpoly).comp_mul 8))).mul (lenX_poly hpoly)

theorem lenOm_poly (hpoly : PolyBounded P) : PolyBounded (lenOm P) :=
  (PolyBounded.two_mul_sub_one.mul (lenK_poly hpoly)).mul (lenX_poly hpoly)

theorem piBound_polyBounded (hpoly : PolyBounded P) : PolyBounded (piBound P) :=
  ((PolyBounded.two_mul_sub_one.mul (lenK_poly hpoly)).add (lenOm_poly hpoly)).sum_range_succ

/-- Part of Theorem 3.1: the bound is polynomial in `n` and `m` (here `n` is the size of the
graph and `m` the length of the smaller label; `2m + 2` is the length of the modified label). -/
theorem piBound_poly (hpoly : PolyBounded P) :
    ∃ C d : ℕ, ∀ n m : ℕ, piBound P (2 * (n + (2 * m + 2)) + 1) ≤ C * (n + m + 1) ^ d := by
  obtain ⟨C, d, h⟩ := piBound_polyBounded hpoly
  refine ⟨C * 6 ^ d, d, fun n m => ?_⟩
  calc piBound P (2 * (n + (2 * m + 2)) + 1) ≤ piBound P (5 * (n + m + 1)) :=
        piBound_mono (by omega)
    _ ≤ C * (5 * (n + m + 1) + 1) ^ d := h _
    _ ≤ C * (6 * (n + m + 1)) ^ d := by gcongr; omega
    _ = C * 6 ^ d * (n + m + 1) ^ d := by rw [mul_pow, mul_assoc]

end Poly

end Podc.AsyncRendezvousPoly
