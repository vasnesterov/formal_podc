import Papers.PODC2026.TaskCompletion.Algorithm
import Papers.PODC2026.TaskCompletion.Covering
import Papers.PODC2026.TaskCompletion.LowerBound

/-!
# Theorem 4.1: deterministic `M`-task completion in `O(R ⌈M/n⌉ log n)` rounds (Section 4.3)

Fischer, Gelles, *The Task Completion Problem and its Application to Crash-Resilient
Computation* (PODC 2026, arXiv:2605.17961).

The `M` tasks are split into `⌈M/m⌉` batches of `m = Θ(n)` tasks (task `t` is task `t mod m` of
batch `⌊t/m⌋`, the last batch padded with dummy tasks). Batch `b` is completed by Algorithm 1
(`Alg.C`, `Alg.Done`) in the global iterations `[b K, (b+1) K)`, `K = numIter P`, against one global
crash adversary (nodes crashed in earlier batches stay crashed). Every iteration takes `2BR + 1`
rounds.

Parameters: `ε = (1-α)/8`, `c = ε³/8`, `B = ⌈72/c⌉` (Lemma 3.1), `m = ⌊cn⌋` for large `n`
(`m = 1` otherwise), and the covering families of Lemma 3.1.
-/

open Finset

namespace Podc.TaskCompletion

open Alg

/-- The parameter `ε = (1-α)/8` satisfies the progress condition of the analysis. -/
lemma prog_of_eps {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) :
    4 * ((1 - α) / 8) ≤ (1 - (1 - α) / 8 - α) * (1 - (1 - α) / 8) := by
  nlinarith

/-- **Theorem 4.1.** For any `α ∈ [0, 1)` there is a constant `C` such that for all `n ≥ 2`,
`M` and `R ≥ 1` there is a deterministic algorithm (Algorithm 1 run on `⌈M/m⌉` batches of `m`
tasks, with parameters `P`) that completes every one of the `M` tasks against every adversary
crashing at most `αn` nodes, using `⌈M/m⌉ · K · (2BR + 1) ≤ C R ⌈M/n⌉ log n` rounds. -/
theorem theorem_4_1 {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) :
    ∃ Cst : ℝ, ∀ n : ℕ, 2 ≤ n → ∀ M R : ℕ, 1 ≤ R →
      ∃ (m : ℕ) (P : Params n m), 1 ≤ m ∧
        (∀ adv : Adversary n, adv.Admissible α → ∀ t : Fin M,
          ∃ b < ⌈(M : ℝ) / m⌉₊, ∃ t' : Fin m, (t : ℕ) = b * m + t' ∧
            t' ∈ Done P adv (b * numIter P) (numIter P)) ∧
        (⌈(M : ℝ) / m⌉₊ * numIter P * (2 * P.B * R + 1) : ℝ) ≤
          Cst * R * ⌈(M : ℝ) / n⌉₊ * Real.log n := by
  classical
  set ε : ℝ := (1 - α) / 8 with hεdef
  have hε0 : 0 < ε := by rw [hεdef]; linarith
  have hε1 : ε < 1 := by rw [hεdef]; linarith
  set c : ℝ := ε ^ 3 / 8 with hcdef
  have hc0 : 0 < c := by positivity
  have hc1 : c < 1 := by
    have : ε ^ 3 < 1 := pow_lt_one₀ hε0.le hε1 (by norm_num)
    rw [hcdef]; linarith
  set B : ℕ := ⌈72 / c⌉₊ with hBdef
  have hB1 : 1 ≤ B := Nat.one_le_iff_ne_zero.mpr (Nat.ceil_pos.mpr (by positivity)).ne'
  obtain ⟨N, hN⟩ := lemma_3_1 hε0 hε1
  set L : ℝ := -Real.log (1 - ε) with hL
  have hLpos : 0 < L := by
    have : Real.log (1 - ε) < 0 := Real.log_neg (by linarith) (by linarith)
    linarith
  set K0 : ℝ := N + 2 / c + 1 with hK0
  refine ⟨3 * B * K0 * (1 / L + 3), fun n hn M R hR => ?_⟩
  set cond : Prop := N ≤ n ∧ 1 ≤ ⌊c * n⌋₊ with hcond
  set m : ℕ := if cond then ⌊c * n⌋₊ else 1 with hmdef
  let P : Params n m := ⟨B, ε, fun k =>
    if h : ∃ A, IsLBCF n m k B ε A then h.choose else fun _ => ∅⟩
  have hm1 : 1 ≤ m := by
    rw [hmdef]; split_ifs with h
    · exact h.2
    · exact le_rfl
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : 0 < n := by omega
  have hGood : Good P α := by
    refine ⟨hB1, hε0, hε1, prog_of_eps hα0 hα1, fun k hk hkm => ?_⟩
    have hk' : 2 * B < k := hk
    have hex : ∃ A, IsLBCF n m k B ε A := by
      by_cases h : cond
      · have hm : m = ⌊c * n⌋₊ := by simp [hmdef, h]
        have hBeq : ⌈72 / (ε ^ 3 / 8)⌉₊ = B := rfl
        refine hN n h.1 m k ?_ (by omega) hkm
        rw [hm]
        exact Nat.floor_le (by positivity)
      · have hm : m = 1 := by simp [hmdef, h]
        omega
    change IsLBCF n m k B ε (if h : ∃ A, IsLBCF n m k B ε A then h.choose else fun _ => ∅)
    simp only [hex, dite_true]
    exact hex.choose_spec
  refine ⟨m, P, hm1, fun adv hadv t => ?_, ?_⟩
  · -- correctness: every task is completed by its batch
    have hmpos : 0 < m := hm1
    refine ⟨t / m, ?_, ⟨t % m, Nat.mod_lt _ hmpos⟩, (Nat.div_add_mod' (t : ℕ) m).symm, ?_⟩
    · apply Nat.lt_ceil.mpr
      have h1 : t / m * m ≤ (t : ℕ) := Nat.div_mul_le_self _ _
      have h2 : ((t / m * m : ℕ) : ℝ) < M := by exact_mod_cast lt_of_le_of_lt h1 t.2
      have hmR : (0 : ℝ) < m := by exact_mod_cast hmpos
      rw [lt_div_iff₀ hmR]
      exact_mod_cast h2
    · rw [(lemma_4_3_1 (s := t / m * numIter P) hGood hα1 hadv hn0).2]
      exact mem_univ _
  · -- round complexity
    have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm1
    have hmn : (m : ℝ) ≤ n := by
      by_cases h : cond
      · have hm : m = ⌊c * n⌋₊ := by simp [hmdef, h]
        rw [hm]
        calc (⌊c * n⌋₊ : ℝ) ≤ c * n := Nat.floor_le (by positivity)
          _ ≤ n := by nlinarith
      · have hm : m = 1 := by simp [hmdef, h]
        rw [hm]; push_cast; linarith
    have hlogn : Real.log 2 ≤ Real.log n := Real.log_le_log (by norm_num) hnR
    have hlog2 : (2 : ℝ) / 3 < Real.log 2 := by
      have := Real.log_two_gt_d9; linarith
    -- iterations
    have hiter : (numIter P : ℝ) ≤ (1 / L + 3) * Real.log n := by
      have h1 := lemma_4_3_2 (P := P) ⟨hε0, hε1⟩ hB1 hm1
      have h2 : Real.log m ≤ Real.log n := Real.log_le_log (by linarith) hmn
      have h3 : Real.log m / L ≤ Real.log n / L := div_le_div_of_nonneg_right h2 hLpos.le
      change (numIter P : ℝ) ≤ Real.log m / L + 2 at h1
      have : Real.log n / L = 1 / L * Real.log n := by ring
      nlinarith
    -- rounds per iteration
    have hRR : (1 : ℝ) ≤ R := by exact_mod_cast hR
    have hBR : (1 : ℝ) ≤ B := by exact_mod_cast hB1
    have hper : (2 * (B : ℝ) * R + 1) ≤ 3 * B * R := by nlinarith
    -- batches
    have hbatch : (⌈(M : ℝ) / m⌉₊ : ℝ) ≤ K0 * ⌈(M : ℝ) / n⌉₊ := by
      rcases Nat.eq_zero_or_pos M with hM | hM
      · subst hM; simp
      have hnR0 : (0 : ℝ) < n := by linarith
      have hceil1 : (1 : ℝ) ≤ ⌈(M : ℝ) / n⌉₊ := by
        have : 0 < ⌈(M : ℝ) / n⌉₊ := Nat.ceil_pos.mpr (by positivity)
        exact_mod_cast this
      have hMn : (M : ℝ) / n ≤ ⌈(M : ℝ) / n⌉₊ := Nat.le_ceil _
      have hK0c : 0 ≤ (N : ℝ) := by positivity
      by_cases h : cond
      · have hm : m = ⌊c * n⌋₊ := by simp [hmdef, h]
        have hfl : c * n / 2 ≤ m := by
          have h1 : c * n < ⌊c * n⌋₊ + 1 := Nat.lt_floor_add_one _
          have h2 : (1 : ℝ) ≤ ⌊c * n⌋₊ := by exact_mod_cast h.2
          rw [hm]; linarith
        have hcn : 0 < c * n := by positivity
        have h1 : (⌈(M : ℝ) / m⌉₊ : ℝ) < M / m + 1 := Nat.ceil_lt_add_one (by positivity)
        have h2 : (M : ℝ) / m ≤ 2 / c * (M / n) := by
          rw [div_le_iff₀ (by linarith)]
          have : 2 / c * (M / n) * m ≥ 2 / c * (M / n) * (c * n / 2) := by
            apply mul_le_mul_of_nonneg_left hfl; positivity
          have e : 2 / c * (M / n) * (c * n / 2) = M := by field_simp
          linarith
        have h3 : 2 / c * ((M : ℝ) / n) ≤ 2 / c * ⌈(M : ℝ) / n⌉₊ :=
          mul_le_mul_of_nonneg_left hMn (by positivity)
        rw [hK0]; nlinarith
      · have hm : m = 1 := by simp [hmdef, h]
        have hnK : (n : ℝ) ≤ K0 := by
          rw [hcond, not_and_or] at h
          rcases h with h | h
          · have : (n : ℝ) ≤ N := by exact_mod_cast (not_le.mp h).le
            have : 0 ≤ 2 / c := by positivity
            rw [hK0]; linarith
          · have h' : ⌊c * n⌋₊ < 1 := not_le.mp h
            have : c * n < 1 := by
              rw [Nat.floor_lt (by positivity)] at h'; exact_mod_cast h'
            have : (n : ℝ) < 1 / c := by rw [lt_div_iff₀ hc0]; linarith
            have : 1 / c ≤ 2 / c := by gcongr; norm_num
            rw [hK0]; linarith
        rw [hm]
        simp only [Nat.cast_one, div_one, Nat.ceil_natCast]
        have : (M : ℝ) ≤ n * ⌈(M : ℝ) / n⌉₊ := by
          rw [div_le_iff₀ hnR0] at hMn; linarith
        have : (n : ℝ) * ⌈(M : ℝ) / n⌉₊ ≤ K0 * ⌈(M : ℝ) / n⌉₊ :=
          mul_le_mul_of_nonneg_right hnK (by positivity)
        linarith
    have hP_B : P.B = B := rfl
    rw [hP_B]
    have hA : (0 : ℝ) ≤ ⌈(M : ℝ) / m⌉₊ := by positivity
    have hI : (0 : ℝ) ≤ numIter P := by positivity
    have step1 : (⌈(M : ℝ) / m⌉₊ * numIter P * (2 * B * R + 1) : ℝ) ≤
        (K0 * ⌈(M : ℝ) / n⌉₊) * ((1 / L + 3) * Real.log n) * (3 * B * R) := by
      apply mul_le_mul _ hper (by positivity) (by positivity)
      exact mul_le_mul hbatch hiter hI (by positivity)
    calc _ ≤ (K0 * ⌈(M : ℝ) / n⌉₊) * ((1 / L + 3) * Real.log n) * (3 * B * R) := step1
      _ = _ := by ring

end Podc.TaskCompletion
