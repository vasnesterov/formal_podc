import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Algebra.BigOperators.Intervals

/-!
# The Self-Excluding Median law is a shifted beta-binomial distribution

Pure-math identities behind Theorem 8 / Corollary 4 of

* G. D'Archivio, M. AlMahmoud, E. Natale, F. Mallmann-Trenn,
  *Order Statistics in Population Protocols via Simple Dynamics*, PODC 2026.

The stationary law of the Self-Excluding Median dynamics (Theorem 8) is
`π_k = Γ(n+2) / (Γ(2n+1) Γ(n/2+1)^2) · C(n-1,k-1) Γ(n/2+k) Γ(3n/2-k+1)` for `1 ≤ k ≤ n`.
We prove:

* `sxLaw_ratio`: the detailed-balance ratio `π_{m+1}/π_m = (n-m)(n+2m) / (m(3n-2m))`;
* `sxLaw_eq_betaBinomial`: `π_k = BB(n-1, n/2+1, n/2+1)(k-1)`;
* `sum_betaBinomial`: the beta-binomial pmf sums to one (via the rising-factorial
  Chu–Vandermonde identity `risingVandermonde`);
* `sum_sxLaw`: `∑_{k=1}^n π_k = 1`;
* `betaBinomial_symm`, `sxLaw_pos`.
-/

open Finset

namespace OrderStatisticsPP

/-- Unnormalised weight of rank `k` in the Self-Excluding Median law (Theorem 8). -/
noncomputable def sxWeight (n k : ℕ) : ℝ :=
  (Nat.choose (n - 1) (k - 1) : ℝ) * Real.Gamma (n / 2 + k) * Real.Gamma (3 * n / 2 - k + 1)

/-- The law of Theorem 8: `π_k = Γ(n+2) / (Γ(2n+1) Γ(n/2+1)^2) · C(n-1,k-1) Γ(n/2+k) Γ(3n/2-k+1)`. -/
noncomputable def sxLaw (n k : ℕ) : ℝ :=
  Real.Gamma (n + 2) / (Real.Gamma (2 * n + 1) * Real.Gamma (n / 2 + 1) ^ 2) * sxWeight n k

/-- Beta-binomial pmf `BB(N, a, b)(x) = C(N,x) B(x+a, N-x+b) / B(a,b)`, with
`B(a,b) = Γ(a)Γ(b)/Γ(a+b)`. -/
noncomputable def betaBinomial (N : ℕ) (a b : ℝ) (x : ℕ) : ℝ :=
  (Nat.choose N x : ℝ) * (Real.Gamma (x + a) * Real.Gamma (((N - x : ℕ) : ℝ) + b) /
    Real.Gamma (N + a + b)) / (Real.Gamma a * Real.Gamma b / Real.Gamma (a + b))

/-! ### Rising factorials -/

/-- Rising factorial `(a)_i = a (a+1) ⋯ (a+i-1)`. -/
def risingFac (a : ℝ) (i : ℕ) : ℝ := ∏ j ∈ range i, (a + j)

@[simp] lemma risingFac_zero (a : ℝ) : risingFac a 0 = 1 := by simp [risingFac]

lemma risingFac_succ (a : ℝ) (i : ℕ) : risingFac a (i + 1) = risingFac a i * (a + i) := by
  simp [risingFac, prod_range_succ]

lemma risingFac_succ' (a : ℝ) (i : ℕ) : risingFac a (i + 1) = a * risingFac (a + 1) i := by
  unfold risingFac
  rw [prod_range_succ', mul_comm]
  congr 1
  · simp
  · refine prod_congr rfl fun j _ => ?_
    push_cast; ring

/-- `Γ(a + i) = Γ(a) (a)_i` for `a > 0`. -/
lemma Gamma_add_nat_eq (a : ℝ) (ha : 0 < a) (i : ℕ) :
    Real.Gamma (i + a) = Real.Gamma a * risingFac a i := by
  induction i with
  | zero => simp
  | succ i ih =>
    have hpos : (i : ℝ) + a ≠ 0 := by positivity
    rw [risingFac_succ, show ((i + 1 : ℕ) : ℝ) + a = ((i : ℝ) + a) + 1 by push_cast; ring,
      Real.Gamma_add_one hpos, ih]
    ring

/-- Rising-factorial Chu–Vandermonde identity:
`∑_{x=0}^{N} C(N,x) (a)_x (b)_{N-x} = (a+b)_N`. -/ -- CSLib candidate
theorem risingVandermonde (N : ℕ) (a b : ℝ) :
    ∑ x ∈ range (N + 1), (N.choose x : ℝ) * (risingFac a x * risingFac b (N - x)) =
      risingFac (a + b) N := by
  induction N generalizing a b with
  | zero => simp
  | succ N ih =>
    rw [sum_choose_succ_mul (fun i j => risingFac a i * risingFac b j)]
    have h1 : ∑ i ∈ range (N + 1), (N.choose i : ℝ) * (risingFac a i * risingFac b (N + 1 - i)) =
        b * ∑ i ∈ range (N + 1), (N.choose i : ℝ) * (risingFac a i * risingFac (b + 1) (N - i)) := by
      rw [mul_sum]
      refine sum_congr rfl fun i hi => ?_
      have : N + 1 - i = (N - i) + 1 := by
        have := mem_range.mp hi; omega
      rw [this, risingFac_succ']
      ring
    have h2 : ∑ i ∈ range (N + 1), (N.choose i : ℝ) * (risingFac a (i + 1) * risingFac b (N - i)) =
        a * ∑ i ∈ range (N + 1), (N.choose i : ℝ) * (risingFac (a + 1) i * risingFac b (N - i)) := by
      rw [mul_sum]
      refine sum_congr rfl fun i _ => ?_
      rw [risingFac_succ']
      ring
    rw [h1, h2, ih, ih, risingFac_succ']
    rw [show a + (b + 1) = a + b + 1 by ring, show a + 1 + b = a + b + 1 by ring]
    ring

/-! ### Beta-binomial -/

/-- The beta-binomial pmf sums to one. -/
theorem sum_betaBinomial (N : ℕ) (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    ∑ x ∈ range (N + 1), betaBinomial N a b x = 1 := by
  have hGa := Real.Gamma_pos_of_pos ha
  have hGb := Real.Gamma_pos_of_pos hb
  have hGab := Real.Gamma_pos_of_pos (add_pos ha hb)
  have hR : 0 < risingFac (a + b) N := by
    unfold risingFac
    exact prod_pos fun j _ => by positivity
  have hN : Real.Gamma (N + a + b) = Real.Gamma (a + b) * risingFac (a + b) N := by
    rw [add_assoc, Gamma_add_nat_eq _ (add_pos ha hb)]
  have key : ∀ x ∈ range (N + 1), betaBinomial N a b x =
      (N.choose x : ℝ) * (risingFac a x * risingFac b (N - x)) / risingFac (a + b) N := by
    intro x _
    unfold betaBinomial
    rw [Gamma_add_nat_eq _ ha, Gamma_add_nat_eq _ hb, hN]
    field_simp
  rw [sum_congr rfl key, ← sum_div, risingVandermonde, div_self hR.ne']

/-- Symmetry of the beta-binomial law with equal parameters. -/
theorem betaBinomial_symm (N : ℕ) (a : ℝ) (x : ℕ) (hx : x ≤ N) :
    betaBinomial N a a (N - x) = betaBinomial N a a x := by
  unfold betaBinomial
  rw [Nat.choose_symm hx, Nat.sub_sub_self hx]
  ring

/-! ### The Self-Excluding Median law -/

/-- Detailed-balance ratio of the law of Theorem 8:
`π_{m+1} / π_m = (n-m)(n+2m) / (m(3n-2m))` for `1 ≤ m < n`. -/
theorem sxLaw_ratio (n m : ℕ) (hm1 : 1 ≤ m) (hmn : m + 1 ≤ n) :
    sxLaw n m * (((n : ℝ) - m) * (n + 2 * m)) = sxLaw n (m + 1) * (m * (3 * n - 2 * m)) := by
  have hcN : (n - 1).choose m * m = (n - 1).choose (m - 1) * (n - m) := by
    have := Nat.choose_succ_right_eq (n - 1) (m - 1)
    rwa [Nat.sub_add_cancel hm1, show n - 1 - (m - 1) = n - m by omega] at this
  have hc : ((n - 1).choose m : ℝ) * m = ((n - 1).choose (m - 1) : ℝ) * ((n : ℝ) - m) := by
    have := congrArg (fun t : ℕ => (t : ℝ)) hcN
    push_cast [Nat.cast_sub (show m ≤ n by omega)] at this
    exact this
  have hmn' : (m : ℝ) + 1 ≤ n := by exact_mod_cast hmn
  have g1 : Real.Gamma ((n : ℝ) / 2 + (m + 1)) = ((n : ℝ) / 2 + m) * Real.Gamma (n / 2 + m) := by
    rw [← add_assoc, Real.Gamma_add_one (by positivity)]
  have g2 : Real.Gamma (3 * (n : ℝ) / 2 - m + 1) =
      (3 * (n : ℝ) / 2 - m) * Real.Gamma (3 * n / 2 - (m + 1) + 1) := by
    rw [show 3 * (n : ℝ) / 2 - (m + 1) + 1 = 3 * n / 2 - m by ring]
    exact Real.Gamma_add_one (by linarith)
  unfold sxLaw sxWeight
  rw [Nat.add_sub_cancel]
  push_cast
  rw [g1, g2]
  linear_combination
    (-(Real.Gamma (n + 2) / (Real.Gamma (2 * n + 1) * Real.Gamma (n / 2 + 1) ^ 2)) *
      Real.Gamma (n / 2 + m) * Real.Gamma (3 * n / 2 - (m + 1) + 1) *
      ((n : ℝ) / 2 + m) * (3 * n - 2 * m)) * hc

/-- Theorem 8's law is `BetaBinomial(n-1, n/2+1, n/2+1)` shifted by one. -/
theorem sxLaw_eq_betaBinomial (n k : ℕ) (hn : 0 < n) (hk1 : 1 ≤ k) (hkn : k ≤ n) :
    sxLaw n k = betaBinomial (n - 1) (n / 2 + 1) (n / 2 + 1) (k - 1) := by
  have e1 : Real.Gamma (((k - 1 : ℕ) : ℝ) + ((n : ℝ) / 2 + 1)) = Real.Gamma (n / 2 + k) := by
    congr 1; rw [Nat.cast_sub hk1]; push_cast; ring
  have e2 : Real.Gamma (((n - 1 - (k - 1) : ℕ) : ℝ) + ((n : ℝ) / 2 + 1)) =
      Real.Gamma (3 * n / 2 - k + 1) := by
    congr 1; rw [show n - 1 - (k - 1) = n - k by omega, Nat.cast_sub hkn]; ring
  have e3 : Real.Gamma (((n - 1 : ℕ) : ℝ) + ((n : ℝ) / 2 + 1) + ((n : ℝ) / 2 + 1)) =
      Real.Gamma (2 * n + 1) := by
    congr 1; rw [Nat.cast_sub (by omega : 1 ≤ n)]; push_cast; ring
  have e4 : Real.Gamma (((n : ℝ) / 2 + 1) + ((n : ℝ) / 2 + 1)) = Real.Gamma (n + 2) := by
    congr 1; ring
  unfold sxLaw sxWeight betaBinomial
  rw [e1, e2, e3, e4]
  simp only [div_eq_mul_inv, mul_inv, inv_inv]
  ring

lemma sum_Ioc_zero_eq_sum_range (f : ℕ → ℝ) (n : ℕ) :
    ∑ k ∈ Ioc 0 n, f k = ∑ x ∈ range n, f (x + 1) := by
  induction n with
  | zero => simp
  | succ n ih => rw [sum_Ioc_succ_top (Nat.zero_le _), ih, sum_range_succ]

/-- Normalisation of the law of Theorem 8 (Corollary 4). -/
theorem sum_sxLaw (n : ℕ) (hn : 0 < n) : ∑ k ∈ Ioc 0 n, sxLaw n k = 1 := by
  obtain ⟨N, rfl⟩ : ∃ N, n = N + 1 := ⟨n - 1, by omega⟩
  rw [sum_Ioc_zero_eq_sum_range, ← sum_betaBinomial N (((N + 1 : ℕ) : ℝ) / 2 + 1)
    (((N + 1 : ℕ) : ℝ) / 2 + 1) (by positivity) (by positivity)]
  refine sum_congr rfl fun x hx => ?_
  have := mem_range.mp hx
  rw [sxLaw_eq_betaBinomial (N + 1) (x + 1) hn (by omega) (by omega)]
  simp

/-- The law of Theorem 8 is strictly positive on `1 ≤ k ≤ n`. -/
theorem sxLaw_pos (n k : ℕ) (hn : 0 < n) (hk1 : 1 ≤ k) (hkn : k ≤ n) : 0 < sxLaw n k := by
  have hkn' : (k : ℝ) ≤ n := by exact_mod_cast hkn
  have hc : (0 : ℝ) < (n - 1).choose (k - 1) := by
    exact_mod_cast Nat.choose_pos (by omega)
  unfold sxLaw sxWeight
  have h1 := Real.Gamma_pos_of_pos (show (0 : ℝ) < n + 2 by positivity)
  have h2 := Real.Gamma_pos_of_pos (show (0 : ℝ) < 2 * n + 1 by positivity)
  have h3 := Real.Gamma_pos_of_pos (show (0 : ℝ) < n / 2 + 1 by positivity)
  have h4 := Real.Gamma_pos_of_pos (show (0 : ℝ) < n / 2 + k by positivity)
  have h5 := Real.Gamma_pos_of_pos (show (0 : ℝ) < 3 * n / 2 - k + 1 by linarith)
  positivity

end OrderStatisticsPP
