import Mathlib

/-!
# Lemma 3.1 as stated is unsatisfiable

Klasing, Kosowski, Pająk, Sauerwald, PODC 2013, Lemma 3.1: for any `k > 3` there is a sequence
of positive numbers `a₀, …, a_{k+1}` with
(1) `a₀ = +∞`, (2) `a_{k+1} = a_k < a_{k-1} < … < a₁`, (3) `Σ_{i=1}^k a_i = 1`,
(4) `a_i · a₁ = 2/a_i - 1/a_{i-1} - 1/a_{i+1}` for `1 ≤ i ≤ k`, (5), (6) (bounds on `a₁`, `a_i`).

Summing (4) over `i = 1, …, k` telescopes (with `1/a₀ = 0` and `a_{k+1} = a_k`) to
`a₁ · Σ a_i = 1/a₁`, so (3) forces `a₁ = 1`, contradicting (3) and positivity for `k ≥ 2`
(`lemma_3_1_false`, which uses only (1)–(4)).

The intended identity is `a_i / a₁ = 2/a_i - 1/a_{i-1} - 1/a_{i+1}`: the proof defines
`a_i = 1/(c b_i)` with `b_{i+1} = 2 b_i - b_{i-1} - 1/b_i`, which gives
`c² a_i = 2/a_i - 1/a_{i-1} - 1/a_{i+1}` and `a₁ = 1/c²`. The proof of Theorem 3.2 uses the
misprinted form (`g_i ≈ 2 a_i a_k k⁴ a₁`, `S_{j+1} = S_j + k⁴ a₁ a_k + 12k`) and then a second slip
(`B₁ ∈ Θ(n²/a₁)` together with `a₁ = Θ(1/H_k)` is said to give `Θ(n²/log k)`); with the corrected
identity the same computation gives `B₁ ∈ Θ(n² a₁) = Θ(n²/log k)`, as claimed.
-/

open Finset

namespace Podc.RotorRouterRing

/-- Telescoping sum of the right-hand sides of (4) (with `g i = 1/a_i`, `g 0 = 0`). -/
lemma telescope (g : ℕ → ℝ) (hg : g 0 = 0) (k : ℕ) :
    ∑ i ∈ Icc 1 k, (2 * g i - g (i - 1) - g (i + 1)) = g 1 + g k - g (k + 1) := by
  induction k with
  | zero => simp [hg]
  | succ k ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih]
    simp only [Nat.add_sub_cancel]
    ring

/-- **Lemma 3.1 is false as stated**: for every `k ≥ 2` there is no sequence of positive reals
satisfying (2) `a_{k+1} = a_k`, (3) `Σ_{i=1}^k a_i = 1` and (4) `a_i a₁ = 2/a_i - 1/a_{i-1} -
1/a_{i+1}` for `1 ≤ i ≤ k`, where (1) `a₀ = +∞` is encoded as `1/a₀ = 0`. -/
theorem lemma_3_1_false (k : ℕ) (hk : 2 ≤ k) :
    ¬ ∃ a : ℕ → ℝ, (∀ i, 1 ≤ i → i ≤ k + 1 → 0 < a i) ∧ a (k + 1) = a k ∧
      (∑ i ∈ Icc 1 k, a i = 1) ∧
      ∀ i ∈ Icc 1 k, a i * a 1 = 2 / a i - (if i = 1 then 0 else 1 / a (i - 1)) - 1 / a (i + 1) := by
  rintro ⟨a, hpos, hlast, hsum, h4⟩
  set g : ℕ → ℝ := fun i => if i = 0 then 0 else 1 / a i with hg
  have h4' : ∀ i ∈ Icc 1 k, a i * a 1 = 2 * g i - g (i - 1) - g (i + 1) := by
    intro i hi
    rw [h4 i hi]
    simp only [Finset.mem_Icc] at hi
    simp only [hg]
    rcases Nat.eq_or_lt_of_le hi.1 with h | h
    · subst h; simp; ring
    · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]; ring
  have hs : a 1 * 1 = g 1 + g k - g (k + 1) := by
    rw [← hsum, Finset.mul_sum, ← telescope g (by simp [hg]) k]
    apply Finset.sum_congr rfl; intro i hi; rw [mul_comm, h4' i hi]
  have hgk : g k = g (k + 1) := by simp only [hg]; rw [if_neg (by omega), if_neg (by omega), hlast]
  have ha1 : 0 < a 1 := hpos 1 le_rfl (by omega)
  have ha2 : 0 < a 2 := hpos 2 (by norm_num) (by omega)
  have h1 : a 1 * a 1 = 1 := by
    have : g 1 = 1 / a 1 := by simp [hg]
    rw [hgk, this] at hs; field_simp at hs; linarith
  have hlt : a 1 < 1 := by
    have hsplit : ∑ i ∈ Icc 1 k, a i ≥ a 1 + a 2 := by
      have hsub : ({1, 2} : Finset ℕ) ⊆ Icc 1 k := by
        intro i hi; simp at hi; simp; omega
      calc ∑ i ∈ Icc 1 k, a i ≥ ∑ i ∈ ({1, 2} : Finset ℕ), a i :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i hi _ => by
              simp only [Finset.mem_Icc] at hi; exact (hpos i hi.1 (by omega)).le)
        _ = a 1 + a 2 := by simp
    linarith
  nlinarith

end Podc.RotorRouterRing
