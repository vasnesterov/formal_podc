import Mathlib.Data.Int.GCD
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.LinearCombination

/-!
# Section 4: playing with Bezout's identity

Godard, Imbs, Raynal, Taubenfeld, PODC 2020, Section 4 (Theorem 3 and the discussion after it).

* `theorem_3`: Bezout's identity `u m + v n = gcd(m, n)` (Mathlib: `Nat.gcd_eq_gcd_ab`).
* `paper_rewrite`: the paper's case analysis turning an arbitrary Bezout pair `(u, v)` into
  `u' m = v' n + gcd(m, n)` with `u' > 0` and `v' ≥ 0` (for `n ≥ 2`). The paper claims that in its
  third case "both `u'` and `v'` are positive"; `v' = 0` happens (`v_prime_zero_example`).
* `exists_bezout_nat`: hence natural numbers `u ≥ 1`, `v` with `u m = v n + gcd(m, n)` exist, and
  the constants of Algorithm 2 ("the smallest non-negative integers with `u m = v n + gcd(m, n)`")
  are well defined; `bezout_count`: the counting identity `u ℓ m = v ℓ n + d` for
  `d = gcd(m, n) ℓ` on which Algorithm 2 rests (after each process won `v ℓ` of the `u ℓ m`
  competitions, exactly `d` remain).
-/

namespace BezoutElection

/-- **Theorem 3** (Bezout): `u m + v n = gcd(m, n)` for some integers `u, v`. -/
theorem theorem_3 (m n : ℕ) : ∃ u v : ℤ, u * m + v * n = Nat.gcd m n :=
  ⟨Nat.gcdA m n, Nat.gcdB m n, by rw [Nat.gcd_eq_gcd_ab]; ring⟩

/-- The paper's rewriting of a Bezout pair `(u, v)` (Section 4, "Playing with Bezout's identity"):
* if `v ≤ 0`: `u' = u`, `v' = -v`;
* if `u = 0`: `u' = 1`, `v' = m/n - 1`;
* if `u < 0`, with `w = -u`: `u' = (v n - 1) w`, `v' = (w m - 1) v`. -/
def rewrite (m n : ℕ) (u v : ℤ) : ℤ × ℤ :=
  if v ≤ 0 then (u, -v)
  else if u = 0 then (1, (m / n : ℕ) - 1)
  else ((v * n - 1) * (-u), ((-u) * m - 1) * v)

/-- The paper's rewriting is correct: for `m ≥ 1`, `n ≥ 2` and any Bezout pair `(u, v)`, it
gives `u' m = v' n + gcd(m, n)` with `u' > 0` and `v' ≥ 0`. -/
theorem paper_rewrite (m n : ℕ) (hm : 1 ≤ m) (hn : 2 ≤ n) (u v : ℤ)
    (h : u * m + v * n = Nat.gcd m n) :
    let r := rewrite m n u v
    r.1 * m = r.2 * n + Nat.gcd m n ∧ 0 < r.1 ∧ 0 ≤ r.2 := by
  have hg : (0 : ℤ) < Nat.gcd m n := by exact_mod_cast Nat.gcd_pos_of_pos_left n (by omega)
  have hm' : (1 : ℤ) ≤ m := by exact_mod_cast hm
  have hn' : (2 : ℤ) ≤ n := by exact_mod_cast hn
  simp only [rewrite]
  split_ifs with hv hu
  · refine ⟨by linarith, ?_, by linarith⟩
    by_contra hu; push Not at hu
    nlinarith
  · -- u = 0: then n = gcd(m, n) divides m
    subst hu
    have hgn : (Nat.gcd m n : ℤ) ≤ n := by exact_mod_cast Nat.gcd_le_right m (by omega)
    have hv1 : v = 1 := by
      have : v * n = Nat.gcd m n := by linarith
      nlinarith
    subst hv1
    have hgn' : Nat.gcd m n = n := by exact_mod_cast (by linarith : (Nat.gcd m n : ℤ) = n)
    have hdvd : n ∣ m := hgn' ▸ Nat.gcd_dvd_left m n
    obtain ⟨c, rfl⟩ := hdvd
    have hc : 1 ≤ c := by
      rcases Nat.eq_zero_or_pos c with h0 | h0
      · subst h0; simp at hm
      · exact h0
    rw [hgn', Nat.mul_div_cancel_left c (by omega)]
    refine ⟨?_, by norm_num, by push_cast; linarith⟩
    push_cast; ring
  · push Not at hv
    have hu' : u < 0 := by
      rcases lt_trichotomy u 0 with h1 | h1 | h1
      · exact h1
      · exact absurd h1 hu
      · have hgm : (Nat.gcd m n : ℤ) ≤ m := by exact_mod_cast Nat.gcd_le_left n (by omega)
        nlinarith
    have hvn : 2 ≤ v * n := by nlinarith
    refine ⟨by simp only; linear_combination h, ?_, ?_⟩
    · nlinarith
    · have : 1 ≤ -u * m := by nlinarith
      nlinarith

/-- The paper says that in its third case "both `u'` and `v'` are positive"; this fails for
`m = 1`, `n = 2`, `(u, v) = (-1, 1)`: then `v' = 0`. -/
theorem v_prime_zero_example :
    (-1 : ℤ) * 1 + 1 * 2 = Nat.gcd 1 2 ∧ rewrite 1 2 (-1) 1 = (1, 0) := by
  refine ⟨by norm_num, ?_⟩
  simp [rewrite]

/-- Natural numbers `u ≥ 1`, `v` with `u m = v n + gcd(m, n)` exist (`m, n ≥ 1`). -/
theorem exists_bezout_nat (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) :
    ∃ u v : ℕ, 1 ≤ u ∧ u * m = v * n + Nat.gcd m n := by
  rcases Nat.lt_or_ge n 2 with h1 | h2
  · have : n = 1 := by omega
    subst this
    exact ⟨1, m - 1, le_rfl, by simp; omega⟩
  obtain ⟨u, v, h⟩ := theorem_3 m n
  obtain ⟨h1, h2, h3⟩ := paper_rewrite m n hm h2 u v h
  refine ⟨(rewrite m n u v).1.toNat, (rewrite m n u v).2.toNat, by omega, ?_⟩
  have := Int.toNat_of_nonneg h3
  have := Int.toNat_of_nonneg h2.le
  zify
  rw [Int.toNat_of_nonneg h3, Int.toNat_of_nonneg h2.le]
  exact h1

/-- The counting identity of Algorithm 2: with `d = gcd(m, n) ℓ`, the `u ℓ m` competitions are
`v ℓ n` competitions (`v ℓ` per process) plus `d` final ones. -/
theorem bezout_count (m n u v ℓ : ℕ) (h : u * m = v * n + Nat.gcd m n) :
    u * ℓ * m = v * ℓ * n + Nat.gcd m n * ℓ := by
  calc u * ℓ * m = (u * m) * ℓ := by ring
    _ = (v * n + Nat.gcd m n) * ℓ := by rw [h]
    _ = v * ℓ * n + Nat.gcd m n * ℓ := by ring

end BezoutElection
