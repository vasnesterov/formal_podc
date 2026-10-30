import Papers.PODC2026.DemandAwareThroughput.TwoNodes
import Papers.PODC2026.DemandAwareThroughput.Rounding

/-!
# Weak throughput: Observation 4, Theorem 6, Proposition 4

Bentert, Avin, Schmid, PODC 2026, §4.

* **Observation 4**: `(M, κ)` is a yes-instance of Demand-Aware Weak Direct Throughput iff some
  `ℕ`-matrix `N` with all line sums `2n-1` has `∑ min((2n-1)a_ij, N_ij) ≥ (2n-1)nκ`.
* **Theorem 6**: weak direct throughput `(7n-4)/(8n-4)` is always achievable, from Lemma 1
  (`Lemma1`, the rounding lemma, proved in `Lemma1.lean`).
* **Proposition 4**: the upper bounds `8/9` (weak, `n = 2`) and `(7n-4)/(8n-4)` resp.
  `(7n-3)/(8n-4)` (weak direct, `n` even resp. odd).
-/

namespace Podc.DemandAwareThroughput

open Finset

variable {n : ℕ}

/-- The statement of **Lemma 1** of the paper: a matrix with entries in `[0, 1]` and integer row
and column sums can be rounded to a `0/1` matrix with the same line sums such that
`∑ a_ij b_ij ≥ X²/n²`, `X = ∑ a_ij`. -/
def Lemma1 (n : ℕ) : Prop :=
  ∀ x : Fin n → Fin n → ℝ, (∀ i j, 0 ≤ x i j ∧ x i j ≤ 1) →
    (∀ i, ∃ s : ℤ, ∑ j, x i j = s) → (∀ j, ∃ t : ℤ, ∑ i, x i j = t) →
    ∃ b : Fin n → Fin n → Bool,
      (∀ i, ∑ j, bval (b i j) = ∑ j, x i j) ∧ (∀ j, ∑ i, bval (b i j) = ∑ i, x i j) ∧
      (∑ i, ∑ j, x i j) ^ 2 / (n : ℝ) ^ 2 ≤ ∑ i, ∑ j, x i j * bval (b i j)

/-- **Observation 4.** For `n ≥ 1` and doubly stochastic `M`, `(M, κ)` is a yes-instance of
Demand-Aware Weak Direct Throughput iff there is a non-negative integer matrix `N` with all row
and column sums `2n-1` and `∑ min((2n-1) a_ij, N_ij) ≥ (2n-1) n κ`. -/
theorem observation_4 (hn : 1 ≤ n) {M : Matrix (Fin n) (Fin n) ℝ}
    (hM : M ∈ doublyStochastic ℝ (Fin n)) (κ : ℝ) :
    DAWeakDirectThroughput M κ ↔ ∃ N : Matrix (Fin n) (Fin n) ℕ, IsRegular (deg n) N ∧
      (2 * n - 1) * n * κ ≤ ∑ i, ∑ j, min ((2 * n - 1) * M i j) (N i j : ℝ) := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h2n : (0 : ℝ) < 2 * n - 1 := by linarith
  have hnpos : (0 : ℝ) < n := by linarith
  constructor
  · rintro ⟨A, hA, M', hle, hκ, hhost⟩
    unfold CanDirectlyHost at hhost
    rw [canRouteDirectly_iff] at hhost
    refine ⟨A, hA, ?_⟩
    rw [le_div_iff₀ hnpos] at hκ
    calc (2 * n - 1) * n * κ = (2 * n - 1) * (κ * n) := by ring
      _ ≤ (2 * n - 1) * ∑ i, ∑ j, M' i j := mul_le_mul_of_nonneg_left hκ h2n.le
      _ = ∑ i, ∑ j, (2 * n - 1) * M' i j := by simp [mul_sum]
      _ ≤ _ := by
        refine sum_le_sum fun i _ => sum_le_sum fun j _ => le_min ?_ ?_
        · exact mul_le_mul_of_nonneg_left (hle i j) h2n.le
        · have := (hhost i j).2
          simpa [Matrix.smul_apply, deg_cast hn] using this
  · rintro ⟨N, hN, hsum⟩
    have h0 := fun i j => nonneg_of_mem_doublyStochastic hM (i := i) (j := j)
    refine ⟨N, hN, fun i j => min (M i j) (N i j / (2 * n - 1)), fun i j => min_le_left _ _,
      ?_, ?_⟩
    · rw [le_div_iff₀ hnpos]
      have e : ∀ i j, min ((2 * n - 1) * M i j) (N i j : ℝ) =
          (2 * n - 1) * min (M i j) (N i j / (2 * n - 1)) := by
        intro i j
        rw [mul_min_of_nonneg _ _ h2n.le, mul_div_cancel₀ _ h2n.ne']
      simp only [e, ← mul_sum] at hsum
      nlinarith
    · unfold CanDirectlyHost
      rw [canRouteDirectly_iff]
      intro u v
      simp only [Matrix.smul_apply, smul_eq_mul, deg_cast hn]
      refine ⟨mul_nonneg h2n.le (le_min (h0 u v) (div_nonneg (Nat.cast_nonneg _) h2n.le)), ?_⟩
      calc (2 * n - 1) * min (M u v) (N u v / (2 * n - 1))
          ≤ (2 * n - 1) * (N u v / (2 * n - 1)) :=
            mul_le_mul_of_nonneg_left (min_le_right _ _) h2n.le
        _ = N u v := mul_div_cancel₀ _ h2n.ne'

/-- **Theorem 6** (from Lemma 1). For `n ≥ 1`, `κ ≤ (7n-4)/(8n-4)` and every doubly stochastic
`M`, `(M, κ)` is a yes-instance of Demand-Aware Weak Direct Throughput. -/
theorem theorem_6_of_lemma1 (hL : Lemma1 n) (hn : 1 ≤ n) {κ : ℝ}
    (hκ : κ ≤ (7 * n - 4) / (8 * n - 4)) {M : Matrix (Fin n) (Fin n) ℝ}
    (hM : M ∈ doublyStochastic ℝ (Fin n)) : DAWeakDirectThroughput M κ := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h2n : (0 : ℝ) < 2 * n - 1 := by linarith
  rw [observation_4 hn hM]
  have hM' := hM
  rw [mem_doublyStochastic_iff_sum] at hM'
  obtain ⟨h0, hr, hc⟩ := hM'
  -- `a' = (2n-1) a`, `p = ⌊a'⌋`, `x = a' - p`
  set a' : Fin n → Fin n → ℝ := fun i j => (2 * n - 1) * M i j
  have ha'0 : ∀ i j, 0 ≤ a' i j := fun i j => mul_nonneg h2n.le (h0 i j)
  set p : Fin n → Fin n → ℕ := fun i j => ⌊a' i j⌋₊
  set x : Fin n → Fin n → ℝ := fun i j => a' i j - p i j
  have hx : ∀ i j, 0 ≤ x i j ∧ x i j ≤ 1 := fun i j =>
    ⟨by simp only [x, p]; linarith [Nat.floor_le (ha'0 i j)],
      by simp only [x, p]; linarith [Nat.lt_floor_add_one (a' i j)]⟩
  have hrow : ∀ i, ∑ j, a' i j = 2 * n - 1 := fun i => by
    simp only [a', ← mul_sum, hr i, mul_one]
  have hcol : ∀ j, ∑ i, a' i j = 2 * n - 1 := fun j => by
    simp only [a', ← mul_sum, hc j, mul_one]
  obtain ⟨b, hbr, hbc, hbX⟩ := hL x hx
    (fun i => ⟨2 * n - 1 - ∑ j, (p i j : ℤ), by
      simp only [x, sum_sub_distrib, hrow i]; push_cast; ring⟩)
    (fun j => ⟨2 * n - 1 - ∑ i, (p i j : ℤ), by
      simp only [x, sum_sub_distrib, hcol j]; push_cast; ring⟩)
  set N : Matrix (Fin n) (Fin n) ℕ := fun i j => p i j + if b i j then 1 else 0
  have hbv : ∀ i j, ((if b i j then 1 else 0 : ℕ) : ℝ) = bval (b i j) := fun i j => by
    unfold bval; split_ifs <;> simp
  refine ⟨N, ⟨fun i => ?_, fun j => ?_⟩, ?_⟩
  · apply Nat.cast_injective (R := ℝ)
    simp only [N, Nat.cast_sum, Nat.cast_add, hbv, sum_add_distrib, hbr i, deg_cast hn]
    simp only [x, sum_sub_distrib, hrow i]; ring
  · apply Nat.cast_injective (R := ℝ)
    simp only [N, Nat.cast_sum, Nat.cast_add, hbv, sum_add_distrib, hbc j, deg_cast hn]
    simp only [x, sum_sub_distrib, hcol j]; ring
  · -- `min(a', N) = p + b x`
    have e : ∀ i j, min ((2 * n - 1) * M i j) (N i j : ℝ) = p i j + x i j * bval (b i j) := by
      intro i j
      change min (a' i j) _ = _
      simp only [N, Nat.cast_add, hbv]
      have h1 := (hx i j).1; have h2 := (hx i j).2
      have ha : a' i j = p i j + x i j := by simp only [x]; ring
      unfold bval; split_ifs
      · rw [min_eq_left (by rw [ha]; push_cast; linarith)]; rw [ha]; ring
      · rw [min_eq_right (by rw [ha]; push_cast; linarith)]; push_cast; ring
    simp only [e, sum_add_distrib]
    set X := ∑ i, ∑ j, x i j with hX
    have hp : ∑ i, ∑ j, (p i j : ℝ) = (2 * n - 1) * n - X := by
      rw [hX]
      have : ∀ i, ∑ j, (p i j : ℝ) = (2 * n - 1) - ∑ j, x i j := fun i => by
        simp only [x, sum_sub_distrib, hrow i]; ring
      simp only [this, sum_sub_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring
    rw [hp]
    have hnpos : (0 : ℝ) < n := by linarith
    have hκ' : (2 * n - 1) * n * κ ≤ n * (7 * n - 4) / 4 := by
      have h84 : (0 : ℝ) < 8 * n - 4 := by linarith
      rw [le_div_iff₀ h84] at hκ
      nlinarith
    have hsq : n * (7 * n - 4) / 4 ≤ (2 * n - 1) * n - X + X ^ 2 / (n : ℝ) ^ 2 := by
      have : X ^ 2 / (n : ℝ) ^ 2 - X + (n : ℝ) ^ 2 / 4 = (X / n - n / 2) ^ 2 := by
        field_simp; ring
      nlinarith [sq_nonneg (X / n - n / 2)]
    linarith

/-! ### Proposition 4 -/

/-- The matrix `N = (1/9)·[[5, 4], [4, 5]]` of Proposition 4. -/
noncomputable def prop4Matrix : Matrix (Fin 2) (Fin 2) ℝ := !![5 / 9, 4 / 9; 4 / 9, 5 / 9]

lemma prop4Matrix_mem : prop4Matrix ∈ doublyStochastic ℝ (Fin 2) := by
  rw [mem_doublyStochastic_iff_sum]
  refine ⟨fun i j => ?_, fun i => ?_, fun j => ?_⟩
  · fin_cases i <;> fin_cases j <;> simp [prop4Matrix] <;> norm_num
  · fin_cases i <;> simp [prop4Matrix, Fin.sum_univ_two] <;> norm_num
  · fin_cases j <;> simp [prop4Matrix, Fin.sum_univ_two] <;> norm_num

/-- **Proposition 4**, first part: for the doubly stochastic `2 × 2` matrix
`N = (1/9)[[5, 4], [4, 5]]`, `(N, κ)` is a no-instance of Demand-Aware Weak Throughput for every
`κ > 8/9`, even in the relaxed capacity semantics. -/
theorem proposition_4_weak_rel {κ : ℝ} (hκ : 8 / 9 < κ) :
    ¬ DAWeakThroughputRel prop4Matrix κ := by
  rintro ⟨A, ⟨hAr, hAc⟩, M', hle, hκ', hhost⟩
  have hdeg : ((deg 2 : ℕ) : ℝ) = 3 := by norm_num [deg]
  obtain ⟨b1, b2⟩ := two_node_bounds_rel hhost
  obtain ⟨b3, b4⟩ := two_node_bounds_rel (hhost.perm (Equiv.swap 0 1))
  simp only [Matrix.smul_apply, smul_eq_mul, hdeg, Equiv.symm_swap, Equiv.swap_apply_left,
    Equiv.swap_apply_right] at b1 b2 b3 b4
  have r0 := hAr 0; have r1 := hAr 1; have c0 := hAc 0; have c1 := hAc 1
  simp only [Fin.sum_univ_two, deg] at r0 r1 c0 c1 hκ'
  have l00 := hle 0 0; have l01 := hle 0 1; have l10 := hle 1 0; have l11 := hle 1 1
  simp only [prop4Matrix, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons] at l00 l01 l10 l11
  norm_num at hκ'
  have hA01 : A 0 1 ≤ 3 := by omega
  have e10 : A 1 0 = A 0 1 := by omega
  have e00 : A 0 0 = 3 - A 0 1 := by omega
  have e11 : A 1 1 = 3 - A 0 1 := by omega
  rw [e10] at b3 b4
  rw [e00, e11] at b2 b4
  interval_cases h : A 0 1 <;> norm_num at b1 b2 b3 b4 <;> linarith

/-- **Proposition 4**, first part (original semantics). -/
theorem proposition_4_weak {κ : ℝ} (hκ : 8 / 9 < κ) : ¬ DAWeakThroughput prop4Matrix κ :=
  fun h => proposition_4_weak_rel hκ h.rel

/-- Number of `j < n` of parity `q`. -/
lemma card_parity (n q : ℕ) (hq : q < 2) :
    ∑ j ∈ range n, (if j % 2 = q then 1 else 0 : ℕ) = if q = 0 then (n + 1) / 2 else n / 2 := by
  induction n with
  | zero => split_ifs <;> simp
  | succ m ih =>
    rw [sum_range_succ, ih]
    split_ifs <;> omega

lemma sum_parity (n : ℕ) (i : Fin n) :
    ∑ j : Fin n, (if (j : ℕ) % 2 = (i : ℕ) % 2 then (1 : ℝ) else 0) =
      ((if (i : ℕ) % 2 = 0 then (n + 1) / 2 else n / 2 : ℕ) : ℝ) := by
  rw [← card_parity n _ (Nat.mod_lt _ (by norm_num))]
  rw [← Fin.sum_univ_eq_sum_range (fun j => if j % 2 = (i : ℕ) % 2 then 1 else 0 : ℕ → ℕ)]
  push_cast
  rfl

/-- Diagonal correction of the matrix `M_n` of Proposition 4: `a = b = 1` for even `n`,
`a = 3/2` (paper's odd rows = our even indices) and `b = 1/2` for odd `n`. -/
noncomputable def dsub (n : ℕ) (i : Fin n) : ℝ :=
  if n % 2 = 0 then 1 else if (i : ℕ) % 2 = 0 then 3 / 2 else 1 / 2

/-- The scaled matrix `(2n-1)·M_n` of Proposition 4: `2.5` on entries of equal index parity,
`1.5` elsewhere, minus `a`/`b` on the diagonal. -/
noncomputable def prop4Entry (n : ℕ) (i j : Fin n) : ℝ :=
  (if (i : ℕ) % 2 = (j : ℕ) % 2 then 5 / 2 else 3 / 2) - (if i = j then dsub n i else 0)

/-- The matrix `M_n` of Proposition 4. -/
noncomputable def prop4MatrixN (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => prop4Entry n i j / (2 * n - 1)

lemma prop4Entry_comm (i j : Fin n) : prop4Entry n i j = prop4Entry n j i := by
  unfold prop4Entry
  by_cases h : i = j
  · subst h; rfl
  · rw [ite_eq_right h, ite_eq_right (Ne.symm h)]
    simp only [eq_comm (a := (i : ℕ) % 2)]

lemma prop4Entry_row_sum (hn : 1 ≤ n) (i : Fin n) : ∑ j, prop4Entry n i j = 2 * n - 1 := by
  have : ∀ j, prop4Entry n i j = 3 / 2 + (if (j : ℕ) % 2 = (i : ℕ) % 2 then 1 else 0)
      - (if i = j then dsub n i else 0) := by
    intro j; unfold prop4Entry
    simp only [eq_comm (a := (i : ℕ) % 2)]
    split_ifs <;> ring
  simp only [this, sum_sub_distrib, sum_add_distrib, sum_parity, sum_ite_eq, mem_univ, ite_true,
    sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  unfold dsub
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' n
  · have h1 : (2 * m) % 2 = 0 := by omega
    have h2 : (2 * m + 1) / 2 = m := by omega
    have h3 : 2 * m / 2 = m := by omega
    simp only [h1, ite_true, h2, h3, ite_self]; push_cast; ring
  · have h1 : (2 * m + 1) % 2 ≠ 0 := by omega
    have h2 : (2 * m + 1 + 1) / 2 = m + 1 := by omega
    have h3 : (2 * m + 1) / 2 = m := by omega
    simp only [h1, ite_false, h2, h3]
    split_ifs <;> push_cast <;> ring

lemma prop4MatrixN_mem (hn : 1 ≤ n) : prop4MatrixN n ∈ doublyStochastic ℝ (Fin n) := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h2n : (0 : ℝ) < 2 * n - 1 := by linarith
  rw [mem_doublyStochastic_iff_sum]
  refine ⟨fun i j => div_nonneg ?_ h2n.le, fun i => ?_, fun j => ?_⟩
  · unfold prop4Entry dsub
    by_cases h : i = j
    · subst h; simp only [ite_true]; split_ifs <;> norm_num
    · rw [ite_eq_right h]; split_ifs <;> norm_num
  · simp only [prop4MatrixN, ← sum_div, prop4Entry_row_sum hn, div_self h2n.ne']
  · simp only [prop4MatrixN, ← sum_div]
    simp only [prop4Entry_comm _ j, prop4Entry_row_sum hn, div_self h2n.ne']

/-- One-entry bound: the direct flow through an entry of value `e ∈ {1, 3/2, 2, 5/2}` using
`A` arcs is at most `A/2 + e/2 - 1/4 + c`. -/
lemma entry_bound {A : ℕ} {x e c : ℝ} (h1 : x ≤ e) (h2 : x ≤ A)
    (he : (e = 5 / 2 ∧ c = 0) ∨ (e = 3 / 2 ∧ c = 0) ∨ (e = 1 ∧ c = 1 / 4) ∨ (e = 2 ∧ c = 1 / 4)) :
    x ≤ A / 2 + e / 2 - 1 / 4 + c := by
  rcases Nat.lt_or_ge A 3 with h | h
  · interval_cases A <;> simp at h2 <;>
      rcases he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> linarith
  · have : (3 : ℝ) ≤ A := by exact_mod_cast h
    rcases he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> linarith

/-- `1/4` for odd `n`, `0` for even `n`. -/
noncomputable def codd (n : ℕ) : ℝ := if n % 2 = 0 then 0 else 1 / 4

lemma prop4Entry_cases (i j : Fin n) :
    let c : ℝ := if i = j then codd n else 0
    (prop4Entry n i j = 5 / 2 ∧ c = 0) ∨ (prop4Entry n i j = 3 / 2 ∧ c = 0) ∨
      (prop4Entry n i j = 1 ∧ c = 1 / 4) ∨ (prop4Entry n i j = 2 ∧ c = 1 / 4) := by
  intro c
  simp only [c, prop4Entry, dsub, codd]
  by_cases h : i = j
  · subst h; simp only [ite_true]; split_ifs <;> norm_num
  · simp only [ite_eq_right h]; split_ifs <;> norm_num

/-- **Proposition 4**, second part: for each `n ≥ 1` the doubly stochastic matrix `M_n` is a
no-instance of Demand-Aware Weak Direct Throughput for every `κ > (7n-4)/(8n-4)` (`n` even)
resp. `κ > (7n-3)/(8n-4)` (`n` odd). -/
theorem proposition_4_direct (hn : 1 ≤ n) {κ : ℝ}
    (hκ : (if n % 2 = 0 then (7 * n - 4 : ℝ) / (8 * n - 4) else (7 * n - 3) / (8 * n - 4)) < κ) :
    ¬ DAWeakDirectThroughput (prop4MatrixN n) κ := by
  rintro ⟨A, ⟨hAr, -⟩, M', hle, hκ', hhost⟩
  unfold CanDirectlyHost at hhost
  rw [canRouteDirectly_iff] at hhost
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h2n : (0 : ℝ) < 2 * n - 1 := by linarith
  have hnpos : (0 : ℝ) < n := by linarith
  -- per-row bound
  have hrow : ∀ i, (2 * n - 1) * ∑ j, M' i j ≤ (2 * n - 1) - n / 4 + codd n := by
    intro i
    have hb : ∀ j, (2 * n - 1) * M' i j ≤
        (A i j : ℝ) / 2 + prop4Entry n i j / 2 - 1 / 4 + (if i = j then codd n else 0) := by
      intro j
      apply entry_bound _ _ (prop4Entry_cases i j)
      · have := hle i j
        simp only [prop4MatrixN] at this
        rw [le_div_iff₀ h2n] at this; linarith
      · have := (hhost i j).2
        simpa [Matrix.smul_apply, deg_cast hn] using this
    calc (2 * n - 1) * ∑ j, M' i j = ∑ j, (2 * n - 1) * M' i j := by rw [mul_sum]
      _ ≤ ∑ j, ((A i j : ℝ) / 2 + prop4Entry n i j / 2 - 1 / 4 +
            (if i = j then codd n else 0)) := sum_le_sum fun j _ => hb j
      _ = (2 * n - 1) - n / 4 + codd n := by
          simp only [sum_add_distrib, sum_sub_distrib, ← sum_div, sum_ite_eq, mem_univ, ite_true,
            prop4Entry_row_sum hn, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
          have : (∑ j, (A i j : ℝ)) = 2 * n - 1 := by
            rw [← deg_cast hn, ← hAr i]; push_cast; rfl
          rw [this]; ring
  have htot : (2 * n - 1) * ∑ i, ∑ j, M' i j ≤ n * ((2 * n - 1) - n / 4 + codd n) := by
    rw [mul_sum]
    calc _ ≤ ∑ _i : Fin n, ((2 * n - 1) - n / 4 + codd n) := sum_le_sum fun i _ => hrow i
      _ = _ := by simp; ring
  rw [le_div_iff₀ hnpos] at hκ'
  have h84 : (0 : ℝ) < 8 * n - 4 := by linarith
  unfold codd at htot
  split_ifs at hκ htot with hpar
  · rw [div_lt_iff₀ h84] at hκ; nlinarith
  · rw [div_lt_iff₀ h84] at hκ; nlinarith

end Podc.DemandAwareThroughput
