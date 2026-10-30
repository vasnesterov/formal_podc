import Papers.PODC2019.MinimalSymmetryBreaking.FiniteTree

/-!
# Theorem 6 / Theorem 13: weak 2-colouring needs `Ω(log* n)` rounds

On trees of maximum degree `Δ = 2k` that contain a complete `Δ`-regular ball of radius
`Kn k n ≈ log_{Δ+1} n / 3` (with a consistent orientation, identifiers exactly `Fin n`, private
randomness from any finite probability space), every algorithm running in
`t ≤ (log* n − C)/2` rounds produces a weak 2-colouring with probability `< 1/2` for some
identifier assignment.
-/

namespace Podc.MinimalSymmetryBreaking

open Finset Function
open scoped Classical

noncomputable section

variable {k : ℕ}

lemma palT_eq_iterate (k t : ℕ) : palT k t = (nodePal k)^[t] 2 := rfl

/-- **Claims 11/12, anonymous part.** Every anonymous `t`-round weak 2-colouring algorithm on the
oriented `2k`-regular tree fails locally with probability at least `qT k t`. -/
theorem qT_le_failProb (hk : 0 < k) {Ω' : Type} [Fintype Ω'] [Inhabited Ω'] (μ' : FinDist Ω')
    {t : ℕ} {β : Type} [Fintype β] (hβ : Fintype.card β ≤ 2) (B : NodeAlg k Ω' t β) :
    qT k t ≤ B.failProb μ' := by
  have h := claim_16 (μ := μ') hk (c := 2) (c₀ := palT k t) (by norm_num) le_rfl hβ B
  have hp : (0 : ℝ) < palT k t := by exact_mod_cast palT_pos k t
  have : qT k t = ((1 / (palT k t : ℝ) ^ (2 * k)) / ((2 * k + 1) * palT k t)) ^
      ((2 * k + 1) ^ (2 * t + 1)) := by
    unfold qT; congr 1; field_simp; ring
  rw [this]; exact h

/-- **Theorem 6** (Theorem 13 for `Δ = 4`). Weak 2-colouring on trees of even maximum degree
`Δ = 2k` requires `Ω(log* n)` rounds: there are constants `C, N₀` such that for every `n ≥ N₀`,
every `t` with `2t + C ≤ log* n`, every finite randomness space, every instance `V` (an
`n`-node subtree of the oriented `Δ`-regular tree containing the ball of radius `Kn k n`) and every
`t`-round algorithm with identifiers, some assignment of the identifiers `Fin n` makes the
algorithm produce a weak 2-colouring with probability less than `1/2`. -/
theorem theorem_6 (hk : 0 < k) : ∃ C N₀ : ℕ, ∀ n ≥ N₀, ∀ t : ℕ, 2 * t + C ≤ Nat.logStar n →
    ∀ [NeZero n] (Ω : Type) [Fintype Ω] [Inhabited Ω] (μ : FinDist Ω) (V : Finset (Tree k)),
      Ball (Kn k n) ⊆ V → V.card = n → ∀ A : IdAlg k n Ω t,
        ∃ id : Tree k → Fin n, Set.InjOn id V ∧ A.succProb μ V id < 1 / 2 := by
  obtain ⟨C, N₀, hmain⟩ := qT_mul_large k hk
  refine ⟨C, N₀, fun n hn t ht _ Ω _ _ μ V hKV hVn A => ?_⟩
  obtain ⟨hK3, hineq⟩ := hmain n hn t ht
  set K := Kn k n
  set q := qT k t
  have hq0 : 0 < q := qT_pos k t
  have hq1 : q ≤ 1 := qT_le_one k t
  have hpow0 : (0 : ℝ) < (2 * k + 1 : ℝ) ^ (2 * t + 2) := by positivity
  have htK : t + 1 ≤ K := by
    by_contra h
    push_neg at h
    have : (K : ℝ) - t - 1 < 0 := by
      have : (K : ℝ) ≤ t := by exact_mod_cast Nat.lt_succ_iff.1 h
      linarith
    nlinarith
  obtain ⟨S, hST, hsep, hcard⟩ := exists_separated (Ball (K - (t + 1)) : Finset (Tree k)) (t + 1)
  have hT := le_card_Ball (k := k) hk (K - (t + 1))
  have hB := card_Ball_le (k := k) (2 * (t + 1))
  have hS : 2 ≤ q * S.card := by
    have h1 : ((K - (t + 1) + 1 : ℕ) : ℝ) ≤ S.card * (2 * k + 1 : ℝ) ^ (2 * t + 2) := by
      have : K - (t + 1) + 1 ≤ S.card * (2 * k + 1) ^ (2 * (t + 1)) :=
        hT.trans (hcard.trans (Nat.mul_le_mul_left _ hB))
      rw [show 2 * (t + 1) = 2 * t + 2 by ring] at this
      exact_mod_cast this
    have h2 : (K : ℝ) - t - 1 ≤ ((K - (t + 1) + 1 : ℕ) : ℝ) := by
      rw [Nat.cast_add, Nat.cast_sub htK]; push_cast; linarith
    have h3 : 2 * (2 * k + 1 : ℝ) ^ (2 * t + 2) ≤ q * S.card * (2 * k + 1 : ℝ) ^ (2 * t + 2) := by
      calc 2 * (2 * k + 1 : ℝ) ^ (2 * t + 2) ≤ q * ((K : ℝ) - t - 1) := hineq
        _ ≤ q * (S.card * (2 * k + 1 : ℝ) ^ (2 * t + 2)) :=
            mul_le_mul_of_nonneg_left (h2.trans h1) hq0.le
        _ = _ := by ring
    exact le_of_mul_le_mul_right h3 hpow0
  obtain ⟨id, hid, hsucc⟩ := succProb_le (μ := μ) A hVn htK hKV hST hsep
    (qT_le_failProb hk _ (by simp) A.anon)
  refine ⟨id, hid, lt_of_le_of_lt hsucc ?_⟩
  -- `(1 - q)^|S| ≤ e^{-2} ≤ 1/3`
  have e1 : (1 - q) ^ S.card ≤ 1 / 3 := by
    calc (1 - q) ^ S.card ≤ Real.exp (-q) ^ S.card :=
          pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp (-q)]) _
      _ = Real.exp (S.card * (-q)) := (Real.exp_nat_mul _ _).symm
      _ ≤ Real.exp (-2) := Real.exp_le_exp.2 (by linarith)
      _ ≤ 1 / 3 := by
          rw [Real.exp_neg, ← one_div]
          apply one_div_le_one_div_of_le (by norm_num)
          linarith [Real.add_one_le_exp (2 : ℝ)]
  -- `|B_K|² / n ≤ 1/27`
  have e2 : ((Ball K : Finset (Tree k)).card : ℝ) ^ 2 / n ≤ 1 / 27 := by
    have hn0 : n ≠ 0 := NeZero.ne n
    have hb : 3 ≤ 2 * k + 1 := by omega
    have h27 : 27 ≤ (2 * k + 1) ^ K :=
      (show 27 = 3 ^ 3 by norm_num) ▸ (Nat.pow_le_pow_left hb 3).trans
        (Nat.pow_le_pow_right (by omega) hK3)
    have hlog : (2 * k + 1) ^ (3 * K) ≤ n :=
      (Nat.pow_le_pow_right (by omega) (by simp only [K, Kn]; omega)).trans
        (Nat.pow_log_le_self _ hn0)
    have hcB := card_Ball_le (k := k) K
    have hnat : 27 * (Ball K : Finset (Tree k)).card ^ 2 ≤ n := by
      calc 27 * (Ball K : Finset (Tree k)).card ^ 2 ≤ (2 * k + 1) ^ K * ((2 * k + 1) ^ K) ^ 2 :=
            Nat.mul_le_mul h27 (Nat.pow_le_pow_left hcB 2)
        _ = (2 * k + 1) ^ (3 * K) := by ring
        _ ≤ n := hlog
    have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn0
    rw [div_le_div_iff₀ hnpos (by norm_num)]
    have : (27 * (Ball K : Finset (Tree k)).card ^ 2 : ℝ) ≤ n := by exact_mod_cast hnat
    linarith
  linarith

end

end Podc.MinimalSymmetryBreaking
