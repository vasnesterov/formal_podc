import Papers.PODC2024.PPGameDynamics.IGT

/-!
# Average stationary generosity (Proposition 2.8)

* `sum_mul_multinomialPMF`: the mean of a multinomial coordinate, `E[x_j] = m p_j`;
* `proposition_2_8`: the average stationary generosity `g̃ = (1/m) ∑_j g_j E[π_j]` of the
  `k`-IGT dynamics, with `g_j = ĝ (j-1)/(k-1)` and `λ = (1-β)/β`, is
  `ĝ (λ^k/(λ^k-1) - (1/(k-1)) (λ/(λ-1)) ((λ^{k-1}-1)/(λ^k-1)))` for `β ≠ 1/2` and `ĝ/2` for
  `β = 1/2`.
-/

open Finset Matrix Cslib.Probability.Markov

namespace Podc.PPGameDynamics

variable {k m : ℕ}

/-- Add one ball to urn `j`. -/
def Simplex.add (y : Simplex k m) (j : Fin k) : Simplex k (m + 1) :=
  ⟨fun l => y.1 l + if l = j then 1 else 0, by
    simp [Finset.sum_add_distrib, y.2]⟩

lemma multinomialPMF_add (p : Fin k → ℝ) (y : Simplex k m) (j : Fin k) :
    ((y.add j).1 j : ℝ) * multinomialPMF p (y.add j) = (m + 1) * p j * multinomialPMF p y := by
  rw [multinomialPMF_eq, multinomialPMF_eq]
  let f : Fin k → ℕ → ℝ := fun l n => p l ^ n / n.factorial
  have hpt : ∀ l, f l ((y.add j).1 l) * (if l = j then ((y.1 j : ℝ) + 1) else 1) =
      f l (y.1 l) * (if l = j then p j else 1) := by
    intro l
    by_cases hl : l = j
    · subst hl
      simp only [Simplex.add, ↓reduceIte, f, pow_succ, Nat.factorial_succ]
      push_cast
      field_simp
    · simp [Simplex.add, hl, f]
  have hprod := congrArg (fun g => ∏ l, g l) (funext hpt)
  simp only [Finset.prod_mul_distrib, Finset.prod_ite_eq', Finset.mem_univ, ↓reduceIte, f]
    at hprod
  have hj : ((y.add j).1 j : ℝ) = y.1 j + 1 := by simp [Simplex.add]
  rw [hj, Nat.factorial_succ]
  push_cast
  calc ((y.1 j : ℝ) + 1) * (((m : ℝ) + 1) * m.factorial *
        ∏ l, p l ^ (y.add j).1 l / ((y.add j).1 l).factorial)
      = ((m : ℝ) + 1) * m.factorial *
        ((∏ l, p l ^ (y.add j).1 l / ((y.add j).1 l).factorial) * ((y.1 j : ℝ) + 1)) := by ring
    _ = ((m : ℝ) + 1) * m.factorial * ((∏ l, p l ^ y.1 l / (y.1 l).factorial) * p j) := by
        rw [hprod]
    _ = _ := by ring

/-- **Mean of the multinomial distribution**: `∑_x x_j ν(x) = (m+1) p_j (∑ p)^m` on
`Δ_k^{m+1}`. -/
theorem sum_mul_multinomialPMF_succ (p : Fin k → ℝ) (j : Fin k) :
    ∑ x : Simplex k (m + 1), (x.1 j : ℝ) * multinomialPMF p x = (m + 1) * p j * (∑ i, p i) ^ m := by
  rw [← sum_multinomialPMF (m := m), Finset.mul_sum]
  have hfilt : ∑ x : Simplex k (m + 1), (x.1 j : ℝ) * multinomialPMF p x =
      ∑ x ∈ univ.filter (fun x : Simplex k (m + 1) => 0 < x.1 j),
        (x.1 j : ℝ) * multinomialPMF p x := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun x _ => ?_
    split_ifs with h
    · rfl
    · have : x.1 j = 0 := by omega
      simp [this]
  rw [hfilt]
  symm
  refine Finset.sum_bij (fun y _ => y.add j) ?_ ?_ ?_ ?_
  · intro y _; simp [Simplex.add]
  · intro y₁ _ y₂ _ h
    apply Subtype.ext; funext l
    have := congrFun (congrArg Subtype.val h) l
    simp only [Simplex.add] at this
    omega
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    refine ⟨⟨fun l => x.1 l - if l = j then 1 else 0, ?_⟩, Finset.mem_univ _, ?_⟩
    · have h2 : ∀ l, (x.1 l - if l = j then 1 else 0) + (if l = j then 1 else 0) = x.1 l := by
        intro l; split_ifs with h <;> [subst h; skip] <;> omega
      have := Finset.sum_congr (s₁ := (univ : Finset (Fin k))) rfl fun l _ => h2 l
      rw [Finset.sum_add_distrib, x.2] at this
      simp at this
      omega
    · apply Subtype.ext; funext l
      simp only [Simplex.add]
      split_ifs with h
      · subst h; omega
      · omega
  · intro y _
    rw [multinomialPMF_add]

/-- **Mean of the multinomial distribution**: `∑_x x_j ν(x) = m p_j` when `∑ p = 1`. -/
theorem sum_mul_multinomialPMF {p : Fin k → ℝ} (hp : ∑ i, p i = 1) (j : Fin k) :
    ∑ x : Simplex k m, (x.1 j : ℝ) * multinomialPMF p x = m * p j := by
  rcases m with _ | m
  · refine (Finset.sum_eq_zero fun x _ => ?_).trans (by simp)
    have : x.1 j = 0 := by
      have h := Finset.single_le_sum (f := x.1) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
      rw [x.2] at h; omega
    simp [this]
  · rw [sum_mul_multinomialPMF_succ, hp, one_pow, mul_one]
    push_cast; ring

/-! ### Geometric sums -/

lemma sum_range_mul_pow (L : ℝ) (n : ℕ) :
    (L - 1) ^ 2 * ∑ i ∈ range n, (i : ℝ) * L ^ i = (n - 1) * L ^ (n + 1) - n * L ^ n + L := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, mul_add, ih]
    push_cast
    ring

/-- The closed form of Proposition 2.8 (for `λ ≠ 1`). -/
lemma generosity_closed_form {L : ℝ} (hL : 0 < L) (hL1 : L ≠ 1) (hk : 2 ≤ k) :
    (∑ i ∈ range k, (i : ℝ) * L ^ i) / ((k - 1) * ∑ i ∈ range k, L ^ i) =
      L ^ k / (L ^ k - 1) - (1 / (k - 1)) * (L / (L - 1)) * ((L ^ (k - 1) - 1) / (L ^ k - 1)) := by
  have h1 : L - 1 ≠ 0 := sub_ne_zero.2 hL1
  have hk0 : k ≠ 0 := by omega
  have h2 : L ^ k - 1 ≠ 0 := by
    rw [sub_ne_zero]; intro h; exact hL1 ((pow_eq_one_iff_of_nonneg hL.le hk0).1 h)
  have h3 : (k : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have hS0 : ∑ i ∈ range k, L ^ i = (L ^ k - 1) / (L - 1) := geom_sum_eq hL1 k
  have hS1 : ∑ i ∈ range k, (i : ℝ) * L ^ i =
      ((k - 1) * L ^ (k + 1) - k * L ^ k + L) / (L - 1) ^ 2 := by
    rw [← sum_range_mul_pow]; field_simp
  rw [hS0, hS1]
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at *
  push_cast at *
  field_simp
  ring

/-! ### Proposition 2.8 -/

variable {A : Type*} [Fintype A] [DecidableEq A] {τ : A → Kind}

/-- **Proposition 2.8.** Let `π` be the stationary distribution of the `k`-IGT dynamics
(Theorem 2.7; with `0 < β` and `m > 0` GTFT agents), `g_j = ĝ (j-1)/(k-1)` the generosity values
(index `j - 1` here), `g̃ = (1/m) ∑_j g_j E[π_j]` and `λ = (1-β)/β`. Then
`g̃ = ĝ (λ^k/(λ^k-1) - (1/(k-1)) (λ/(λ-1)) ((λ^{k-1}-1)/(λ^k-1)))` if `β ≠ 1/2`, and
`g̃ = ĝ/2` if `β = 1/2`. -/
theorem proposition_2_8 (hk : 2 ≤ k) (hAD : 0 < numAD τ) (hm : 0 < numGTFT τ) (ghat : ℝ)
    (π : Simplex k (numGTFT τ) → ℝ) (hπ : IsDistribution π)
    (hst : IsStationary (ehrenfest k (fracGTFT τ * (1 - fracAD τ)) (fracGTFT τ * fracAD τ)
      (numGTFT τ)) π) :
    let β := fracAD τ
    let L := (1 - β) / β
    let gtilde := (1 / (numGTFT τ : ℝ)) *
      ∑ j : Fin k, (ghat * (j.val / (k - 1 : ℝ))) * ∑ x, π x * x.1 j
    (β ≠ 1 / 2 → gtilde = ghat * (L ^ k / (L ^ k - 1) -
        (1 / (k - 1)) * (L / (L - 1)) * ((L ^ (k - 1) - 1) / (L ^ k - 1)))) ∧
    (β = 1 / 2 → gtilde = ghat / 2) := by
  intro β L gtilde
  obtain ⟨-, -, huniq⟩ := theorem_2_7_stationary (k := k) (τ := τ) hk hAD hm
  have hπeq := huniq π hπ hst
  have hle := numAD_add_numGTFT_le (τ := τ)
  have hn' : (0 : ℝ) < Fintype.card A := by exact_mod_cast (show 0 < Fintype.card A by omega)
  have hβ0 : 0 < β := div_pos (by exact_mod_cast hAD) hn'
  have hβ1 : β < 1 := by
    show fracAD τ < 1
    rw [fracAD, div_lt_one hn']; exact_mod_cast (show numAD τ < Fintype.card A by omega)
  have hL0 : 0 < L := div_pos (by linarith) hβ0
  have hLeq : 1 / fracAD τ - 1 = L := by
    show 1 / β - 1 = (1 - β) / β; field_simp
  rw [hLeq] at hπeq
  have hk0 : 0 < k := by omega
  have hm' : (numGTFT τ : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  -- the mean
  have hmean : ∀ j : Fin k, ∑ x, π x * x.1 j = numGTFT τ * ehrParam k L j := by
    intro j
    rw [hπeq, ← sum_mul_multinomialPMF (sum_ehrParam hk0 hL0) j]
    exact Finset.sum_congr rfl fun x _ => mul_comm _ _
  have hS0 : 0 < ∑ i : Fin k, L ^ i.val :=
    Finset.sum_pos (fun i _ => pow_pos hL0 _) ⟨⟨0, hk0⟩, Finset.mem_univ _⟩
  have hg : gtilde = ghat * ((∑ i ∈ range k, (i : ℝ) * L ^ i) /
      ((k - 1) * ∑ i ∈ range k, L ^ i)) := by
    simp only [gtilde, hmean, ehrParam]
    rw [← Fin.sum_univ_eq_sum_range (fun i => (i : ℝ) * L ^ i),
      ← Fin.sum_univ_eq_sum_range (fun i => L ^ i)]
    have h3 : (k : ℝ) - 1 ≠ 0 := by
      have : (2 : ℝ) ≤ k := by exact_mod_cast hk
      linarith
    set S := ∑ i : Fin k, L ^ i.val
    have e : ∀ j : Fin k, ghat * ((j.val : ℝ) / (k - 1)) * ((numGTFT τ : ℝ) * (L ^ j.val / S)) =
        (numGTFT τ : ℝ) * (ghat / ((k - 1) * S)) * ((j.val : ℝ) * L ^ j.val) := by
      intro j; field_simp
    simp_rw [e]
    rw [← Finset.mul_sum]
    field_simp
  refine ⟨fun hne => ?_, fun heq => ?_⟩
  · have hL1 : L ≠ 1 := by
      intro h
      apply hne
      have : (1 - β) / β = 1 := h
      field_simp at this
      linarith
    rw [hg, generosity_closed_form hL0 hL1 hk]
  · have hL1 : L = 1 := by show (1 - β) / β = 1; rw [heq]; norm_num
    rw [hg, hL1]
    simp only [one_pow, mul_one, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have h2 := Finset.sum_range_id_mul_two k
    have h2' : (∑ i ∈ range k, (i : ℝ)) = k * (k - 1) / 2 := by
      have : (((∑ i ∈ range k, (i : ℕ)) : ℕ) : ℝ) * 2 = k * ((k - 1 : ℕ) : ℝ) := by
        exact_mod_cast h2
      push_cast at this
      rw [Nat.cast_sub (by omega)] at this
      push_cast at this
      linarith
    rw [h2']
    have h3 : (k : ℝ) - 1 ≠ 0 := by
      have : (2 : ℝ) ≤ k := by exact_mod_cast hk
      linarith
    have h4 : (k : ℝ) ≠ 0 := by positivity
    field_simp

end Podc.PPGameDynamics
