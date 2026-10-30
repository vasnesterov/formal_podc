import Papers.PODC2026.DemandAwareThroughput.Model
import Cslib.Foundations.Combinatorics.Matrix.Birkhoff

/-!
# Direct throughput: Propositions 2 and 3, Observation 3

Bentert, Avin, Schmid, PODC 2026, §2 and §3.2.

* **Proposition 2**: every doubly stochastic `M` has demand-aware direct throughput at least
  `n/(2n-1)`. The paper proves this with a greedy algorithm; we use a shorter existence argument:
  the matrix `⌈n·M⌉` has row and column sums `< 2n`, hence `≤ 2n-1`, and can be padded to a
  `(2n-1)`-regular `ℕ`-matrix (CSLib's `Matrix.exists_regular_above`).
* **Proposition 3**: for every `κ > n/(2n-1)` some doubly stochastic `M` has direct throughput
  `< κ` (the paper's matrix with diagonal `1-δ`).
* **Observation 3**: `n/(2n-1)` is achievable for the (multi-hop) throughput, here derived from
  Proposition 2 and Observation 1 instead of the external Theorem 1 of Keslassy et al.
-/

namespace Podc.DemandAwareThroughput

open Finset

variable {n : ℕ}

lemma deg_cast (hn : 1 ≤ n) : ((deg n : ℕ) : ℝ) = 2 * n - 1 := by
  unfold deg
  rw [Nat.cast_sub (by omega)]
  push_cast; ring

lemma sum_ceil_le {M : Fin n → ℝ} (hn : 1 ≤ n) (h0 : ∀ j, 0 ≤ M j)
    (hs : ∑ j, M j = 1) : ∑ j, ⌈(n : ℝ) * M j⌉₊ ≤ deg n := by
  have hlt : ((∑ j, ⌈(n : ℝ) * M j⌉₊ : ℕ) : ℝ) < 2 * n := by
    push_cast
    calc ∑ j, (⌈(n : ℝ) * M j⌉₊ : ℝ) < ∑ j : Fin n, ((n : ℝ) * M j + 1) := by
          apply Finset.sum_lt_sum_of_nonempty
          · exact ⟨⟨0, by omega⟩, mem_univ _⟩
          · intro j _
            exact Nat.ceil_lt_add_one (mul_nonneg (Nat.cast_nonneg _) (h0 j))
      _ = 2 * n := by
          rw [sum_add_distrib, ← mul_sum, hs]; simp; ring
  have : ∑ j, ⌈(n : ℝ) * M j⌉₊ < 2 * n := by exact_mod_cast hlt
  unfold deg; omega

/-- **Proposition 2.** For `n ≥ 1`, `κ ≤ n/(2n-1)` and every doubly stochastic `n × n` matrix
`M`, `(M, κ)` is a yes-instance of Demand-Aware Direct Throughput. -/
theorem proposition_2 (hn : 1 ≤ n) {κ : ℝ} (hκ : κ ≤ n / (2 * n - 1))
    {M : Matrix (Fin n) (Fin n) ℝ} (hM : M ∈ doublyStochastic ℝ (Fin n)) :
    DADirectThroughput M κ := by
  rw [mem_doublyStochastic_iff_sum] at hM
  obtain ⟨h0, hr, hc⟩ := hM
  set C : Matrix (Fin n) (Fin n) ℕ := fun i j => ⌈(n : ℝ) * M i j⌉₊
  obtain ⟨A, hCA, hAr, hAc⟩ := Matrix.exists_regular_above C (deg n)
    (fun i => sum_ceil_le hn (h0 i) (hr i))
    (fun j => sum_ceil_le (M := fun i => M i j) hn (fun i => h0 i j) (hc j))
  refine ⟨A, ⟨hAr, hAc⟩, max κ 0, le_max_left _ _, ?_⟩
  unfold CanDirectlyHost
  rw [canRouteDirectly_iff]
  intro u v
  have h2n : (0 : ℝ) < 2 * n - 1 := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hθ : (2 * n - 1) * max κ 0 ≤ n := by
    rcases le_total κ 0 with h | h
    · rw [max_eq_right h]; simp
    · rw [max_eq_left h]
      rwa [le_div_iff₀ h2n, mul_comm] at hκ
  simp only [Matrix.smul_apply, smul_eq_mul, deg_cast hn]
  refine ⟨mul_nonneg h2n.le (mul_nonneg (le_max_right _ _) (h0 u v)), ?_⟩
  calc (2 * n - 1) * (max κ 0 * M u v) = ((2 * n - 1) * max κ 0) * M u v := by ring
    _ ≤ n * M u v := mul_le_mul_of_nonneg_right hθ (h0 u v)
    _ ≤ (C u v : ℝ) := Nat.le_ceil _
    _ ≤ A u v := by exact_mod_cast hCA u v

/-- **Observation 3.** For `n ≥ 1`, `κ ≤ n/(2n-1)` and every doubly stochastic `M`, `(M, κ)` is
a yes-instance of Demand-Aware Throughput. (The paper derives this from Theorem 1 of Keslassy et
al.; we derive it from Proposition 2 and Observation 1.) -/
theorem observation_3 (hn : 1 ≤ n) {κ : ℝ} (hκ : κ ≤ n / (2 * n - 1))
    {M : Matrix (Fin n) (Fin n) ℝ} (hM : M ∈ doublyStochastic ℝ (Fin n)) :
    DAThroughput M κ :=
  observation_1_direct (proposition_2 hn hκ hM)

/-- The matrix of Proposition 3: `1 - δ` on the diagonal and `δ/(n-1)` elsewhere. -/
noncomputable def prop3Matrix (n : ℕ) (δ : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => if i = j then 1 - δ else δ / (n - 1)

lemma prop3Matrix_mem (hn : 1 ≤ n) {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (h1 : n = 1 → δ = 0) :
    prop3Matrix n δ ∈ doublyStochastic ℝ (Fin n) := by
  have hrow : ∀ i : Fin n, ∑ j, (if i = j then 1 - δ else δ / (n - 1)) = 1 := by
    intro i
    have : ∀ j : Fin n, (if i = j then 1 - δ else δ / (n - 1)) =
        δ / (n - 1) + (if i = j then 1 - δ - δ / (n - 1) else 0) := by
      intro j; split_ifs <;> ring
    simp only [this, sum_add_distrib, sum_ite_eq, mem_univ, ite_true, sum_const, card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    rcases eq_or_lt_of_le hn with h | h
    · subst h; simp [h1 rfl]
    · have : (n : ℝ) - 1 ≠ 0 := by
        have : (2 : ℝ) ≤ n := by exact_mod_cast h
        linarith
      field_simp; ring
  rw [mem_doublyStochastic_iff_sum]
  refine ⟨fun i j => ?_, hrow, fun j => ?_⟩
  · unfold prop3Matrix; split_ifs
    · linarith
    · apply div_nonneg hδ0; have : (1 : ℝ) ≤ n := by exact_mod_cast hn
      linarith
  · rw [← hrow j]; unfold prop3Matrix
    exact sum_congr rfl fun i _ => by simp only [eq_comm]

/-- **Proposition 3.** For `n ≥ 1` and every `κ > n/(2n-1)` there is a doubly stochastic
`n × n` matrix `M_κ` such that `(M_κ, κ)` is a no-instance of Demand-Aware Direct Throughput. -/
theorem proposition_3 (hn : 1 ≤ n) {κ : ℝ} (hκ : n / (2 * n - 1) < κ) :
    ∃ M ∈ doublyStochastic ℝ (Fin n), ¬ DADirectThroughput M κ := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h2n : (0 : ℝ) < 2 * n - 1 := by linarith
  set ε := κ - n / (2 * n - 1) with hε
  have hεpos : 0 < ε := by linarith
  set δ : ℝ := if n = 1 then 0 else min (ε / 2) (1 / (2 * n - 1)) with hδ
  have hδ0 : 0 ≤ δ := by
    rw [hδ]; split_ifs
    · exact le_rfl
    · exact le_min (by linarith) (by positivity)
  have hδ1 : δ ≤ 1 / (2 * n - 1) := by
    rw [hδ]; split_ifs
    · positivity
    · exact min_le_right _ _
  have hδ2 : n = 1 → δ = 0 := fun h => by rw [hδ, ite_eq_left h]
  have hδle1 : δ < 1 := by
    rcases eq_or_lt_of_le hn with h | h
    · rw [hδ2 h.symm]; norm_num
    · have : (2 : ℝ) ≤ n := by exact_mod_cast h
      calc δ ≤ 1 / (2 * n - 1) := hδ1
        _ < 1 := by rw [div_lt_one h2n]; linarith
  refine ⟨prop3Matrix n δ, prop3Matrix_mem hn hδ0 hδle1.le hδ2, ?_⟩
  rintro ⟨A, ⟨hAr, -⟩, θ, hθ, hhost⟩
  unfold CanDirectlyHost at hhost
  rw [canRouteDirectly_iff] at hhost
  set v : Fin n := ⟨0, by omega⟩
  have hθpos : 0 < θ := by
    have : 0 < n / (2 * (n : ℝ) - 1) := by positivity
    linarith
  -- the diagonal entry
  have hdiag : (2 * n - 1) * (θ * (1 - δ)) ≤ A v v := by
    have := (hhost v v).2
    simpa [Matrix.smul_apply, prop3Matrix, deg_cast hn] using this
  -- off-diagonal arcs are present
  have hoff : ∀ w ∈ univ.erase v, 1 ≤ A v w := by
    intro w hw
    have hwv : v ≠ w := fun h => (mem_erase.1 hw).1 h.symm
    have := (hhost v w).2
    simp only [Matrix.smul_apply, smul_eq_mul, prop3Matrix, ite_eq_right hwv, deg_cast hn] at this
    have hn2 : 2 ≤ n := by
      by_contra h
      have : n = 1 := by omega
      subst this
      exact hwv (Subsingleton.elim _ _)
    have hn2' : (2 : ℝ) ≤ n := by exact_mod_cast hn2
    have hδpos : 0 < δ := by
      rw [hδ, ite_eq_right (by omega)]
      exact lt_min (by linarith) (by positivity)
    have hpos : (0 : ℝ) < A v w := by
      refine lt_of_lt_of_le ?_ this
      have : (0 : ℝ) < (n : ℝ) - 1 := by linarith
      positivity
    exact_mod_cast hpos
  have hsum : n - 1 + A v v ≤ deg n := by
    rw [← hAr v, ← add_sum_erase _ _ (mem_univ v)]
    have : n - 1 ≤ ∑ w ∈ univ.erase v, A v w := by
      calc n - 1 = ∑ w ∈ univ.erase v, 1 := by simp [card_erase_of_mem]
        _ ≤ _ := sum_le_sum hoff
    omega
  have hAvv : (A v v : ℝ) ≤ n := by
    have : A v v ≤ n := by unfold deg at hsum; omega
    exact_mod_cast this
  -- contradiction with `(2n-1) θ (1-δ) > n`
  have hkey : (n : ℝ) < (2 * n - 1) * (κ * (1 - δ)) := by
    have hκ' : κ = n / (2 * n - 1) + ε := by rw [hε]; ring
    rw [hκ']
    have e1 : (2 * n - 1) * ((n / (2 * n - 1) + ε) * (1 - δ)) =
        n + (2 * n - 1) * ε - δ * n - (2 * n - 1) * ε * δ := by
      field_simp; ring
    rw [e1]
    rcases eq_or_lt_of_le hn with h | h
    · rw [hδ2 h.symm]; nlinarith
    · have hn2' : (2 : ℝ) ≤ n := by exact_mod_cast h
      have hδε : δ ≤ ε / 2 := by rw [hδ, ite_eq_right (by omega)]; exact min_le_left _ _
      have hδn : (2 * n - 1) * δ ≤ 1 := by rwa [le_div_iff₀ h2n, mul_comm] at hδ1
      nlinarith
  have : (2 * n - 1) * (κ * (1 - δ)) ≤ (2 * n - 1) * (θ * (1 - δ)) := by
    apply mul_le_mul_of_nonneg_left _ h2n.le
    exact mul_le_mul_of_nonneg_right hθ (by linarith)
  linarith

end Podc.DemandAwareThroughput
