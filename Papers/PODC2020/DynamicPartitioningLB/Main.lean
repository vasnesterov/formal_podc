import Papers.PODC2020.DynamicPartitioningLB.LowerBound

/-!
# Theorem 2.1: deterministic lower bound `Ω(k ℓ)`

Pacut, Parham, Schmid, PODC 2020, Theorem 2.1. The nodes are `Fin ℓ × Fin k` (cluster of origin,
index) and the initial partition is `Prod.fst`; any initial balanced partition is of this form up
to renaming, and a lower bound for one instance is a lower bound for the problem.

* `theorem_2_1`: finite learning-model inputs, `1 ≤ OPT ≤ 4α` and
  `ALG ≥ 2α ((k - 2)(ℓ - 1) - 2)`.
* `theorem_2_1_ratio`, `theorem_2_1_competitive`: the competitive-ratio forms
  (`c ≥ ((k-2)(ℓ-1)-2)/2 - β/(4α)` for every `(c, β)`-competitive algorithm), the paper's constant
  `((k-2)(ℓ-1)-4)/2` (`theorem_2_1_paper`) and an explicit `Ω(k ℓ)` form (`theorem_2_1_omega`).
* `theorem_2_1_static`: the same with an infinite static input in which every communicating pair
  communicates forever (the learning model as defined in Section 2).
* The bound holds a fortiori in the general model (`theorem_2_1_general`), whose inputs are all
  request sequences.
-/

set_option linter.unusedSectionVars false

namespace Papers.PODC2020.DynamicPartitioningLB

open Finset

/-- **Theorem 2.1** (Pacut, Parham, Schmid, PODC 2020). For `k ≥ 3`, `ℓ ≥ 2` and every
deterministic online algorithm `A` for the learning model of dynamic balanced graph partitioning
(`ℓ` clusters of capacity `k`, migration cost `α ≥ 1`), there is an input admitting a perfect
partition on which `1 ≤ OPT ≤ 4α` while `A` pays at least `2α · ((k - 2)(ℓ - 1) - 2)`. -/
theorem theorem_2_1 {k ℓ α : ℕ} (hk : 3 ≤ k) (hℓ : 2 ≤ ℓ) (hα : 1 ≤ α)
    (A : OnlineAlg (Fin ℓ × Fin k) ℓ k Prod.fst) :
    ∃ σ, IsLearningInput ℓ k σ ∧ 1 ≤ optCost k α Prod.fst σ ∧ optCost k α Prod.fst σ ≤ 4 * α ∧
      2 * α * ((k - 2) * (ℓ - 1) - 2) ≤ algCost α A σ := by
  obtain ⟨K, rfl⟩ : ∃ K, k = K + 3 := ⟨k - 3, by omega⟩
  obtain ⟨L, rfl⟩ : ∃ L, ℓ = L + 2 := ⟨ℓ - 2, by omega⟩
  obtain ⟨σ, h1, h2, h3, h4⟩ := LB.lower_bound (A := A) hα
  exact ⟨σ, h1, h2, h3, by simpa using h4⟩

/-- The real-valued bound is below the truncated natural one. -/
lemma real_bound_le {k ℓ : ℕ} (hk : 3 ≤ k) (hℓ : 2 ≤ ℓ) :
    ((k : ℝ) - 2) * ((ℓ : ℝ) - 1) - 2 ≤ (((k - 2) * (ℓ - 1) - 2 : ℕ) : ℝ) := by
  have e : (((k - 2) * (ℓ - 1) : ℕ) : ℝ) = ((k : ℝ) - 2) * ((ℓ : ℝ) - 1) := by
    rw [Nat.cast_mul, Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; norm_num
  rcases le_or_gt 2 ((k - 2) * (ℓ - 1)) with h | h
  · rw [Nat.cast_sub h, e]; simp
  · have : (((k - 2) * (ℓ - 1) : ℕ) : ℝ) < 2 := by exact_mod_cast h
    rw [e] at this
    have := Nat.cast_nonneg (α := ℝ) ((k - 2) * (ℓ - 1) - 2)
    linarith

/-- `A` is `(c, β)`-competitive on the inputs satisfying `Adm`: `ALG(σ) ≤ c · OPT(σ) + β`. -/
def IsCompetitive {V : Type*} [Fintype V] [DecidableEq V] {ℓ k : ℕ} {init : Config V ℓ}
    (Adm : List (Req V) → Prop) (α : ℕ) (A : OnlineAlg V ℓ k init) (c β : ℝ) : Prop :=
  ∀ σ, Adm σ → (algCost α A σ : ℝ) ≤ c * optCost k α init σ + β

/-- Theorem 2.1, ratio form: on the adversarial input,
`ALG ≥ ((k - 2)(ℓ - 1) - 2) / 2 · OPT` with `OPT ≥ 1`. -/
theorem theorem_2_1_ratio {k ℓ α : ℕ} (hk : 3 ≤ k) (hℓ : 2 ≤ ℓ) (hα : 1 ≤ α)
    (A : OnlineAlg (Fin ℓ × Fin k) ℓ k Prod.fst) :
    ∃ σ, IsLearningInput ℓ k σ ∧ 1 ≤ optCost k α Prod.fst σ ∧
      (((k : ℝ) - 2) * ((ℓ : ℝ) - 1) - 2) / 2 * optCost k α Prod.fst σ ≤ algCost α A σ := by
  obtain ⟨σ, hσ, h1, h2, h3⟩ := theorem_2_1 hk hℓ hα A
  refine ⟨σ, hσ, h1, ?_⟩
  have h3' : (2 * α * ((k - 2) * (ℓ - 1) - 2) : ℝ) ≤ algCost α A σ := by
    have := (Nat.cast_le (α := ℝ)).2 h3
    push_cast at this
    refine le_trans ?_ this
    have hS := real_bound_le hk hℓ
    have : (0 : ℝ) ≤ 2 * α := by positivity
    nlinarith
  have h2' : (optCost k α Prod.fst σ : ℝ) ≤ 4 * α := by exact_mod_cast h2
  have h1' : (0 : ℝ) ≤ optCost k α Prod.fst σ := by positivity
  rcases le_or_gt 0 (((k : ℝ) - 2) * ((ℓ : ℝ) - 1) - 2) with hS | hS
  · nlinarith
  · have : (((k : ℝ) - 2) * ((ℓ : ℝ) - 1) - 2) / 2 * optCost k α Prod.fst σ ≤ 0 := by
      apply mul_nonpos_of_nonpos_of_nonneg _ h1'; linarith
    exact this.trans (Nat.cast_nonneg _)

/-- Theorem 2.1, competitive-ratio form: every deterministic online algorithm that is
`(c, β)`-competitive on the learning model, `c ≥ 0`, satisfies
`c ≥ ((k - 2)(ℓ - 1) - 2) / 2 - β / (4α)`. In particular (`β = 0`, or `α → ∞` with `β` fixed)
the competitive ratio is at least `((k - 2)(ℓ - 1) - 2) / 2`. -/
theorem theorem_2_1_competitive {k ℓ α : ℕ} (hk : 3 ≤ k) (hℓ : 2 ≤ ℓ) (hα : 1 ≤ α)
    (A : OnlineAlg (Fin ℓ × Fin k) ℓ k Prod.fst) {c β : ℝ} (hc : 0 ≤ c)
    (hA : IsCompetitive (IsLearningInput ℓ k) α A c β) :
    (((k : ℝ) - 2) * ((ℓ : ℝ) - 1) - 2) / 2 - β / (4 * α) ≤ c := by
  obtain ⟨σ, hσ, h1, h2, h3⟩ := theorem_2_1 hk hℓ hα A
  have hle := hA σ hσ
  have h2' : (optCost k α Prod.fst σ : ℝ) ≤ 4 * α := by exact_mod_cast h2
  have hαr : (1 : ℝ) ≤ α := by exact_mod_cast hα
  have h3' : 2 * (α : ℝ) * (((k : ℝ) - 2) * ((ℓ : ℝ) - 1) - 2) ≤ algCost α A σ := by
    have := (Nat.cast_le (α := ℝ)).2 h3
    push_cast at this
    refine le_trans ?_ this
    have hS := real_bound_le hk hℓ
    have : (0 : ℝ) ≤ 2 * α := by positivity
    nlinarith
  have hmain : 2 * (α : ℝ) * (((k : ℝ) - 2) * ((ℓ : ℝ) - 1) - 2) ≤ c * (4 * α) + β := by
    have : c * (optCost k α Prod.fst σ : ℝ) ≤ c * (4 * α) := mul_le_mul_of_nonneg_left h2' hc
    linarith
  have h4 : (0 : ℝ) < 4 * α := by linarith
  have key : ((((k : ℝ) - 2) * ((ℓ : ℝ) - 1) - 2) / 2 - β / (4 * α)) * (4 * α) =
      2 * (α : ℝ) * (((k : ℝ) - 2) * ((ℓ : ℝ) - 1) - 2) - β := by
    field_simp; ring
  refine le_of_mul_le_mul_right ?_ h4
  rw [key]; linarith

/-- The paper's constant: a strictly competitive (`β = 0`) algorithm has ratio
`c ≥ ((k - 2)(ℓ - 1) - 4) / 2`. -/
theorem theorem_2_1_paper {k ℓ α : ℕ} (hk : 3 ≤ k) (hℓ : 2 ≤ ℓ) (hα : 1 ≤ α)
    (A : OnlineAlg (Fin ℓ × Fin k) ℓ k Prod.fst) {c : ℝ} (hc : 0 ≤ c)
    (hA : IsCompetitive (IsLearningInput ℓ k) α A c 0) :
    (((k : ℝ) - 2) * ((ℓ : ℝ) - 1) - 4) / 2 ≤ c := by
  have := theorem_2_1_competitive hk hℓ hα A hc hA
  simp only [zero_div, sub_zero] at this
  linarith

/-- `Ω(k ℓ)` with explicit constants: `c ≥ k ℓ / 12 - 1 - β / (4α)`. -/
theorem theorem_2_1_omega {k ℓ α : ℕ} (hk : 3 ≤ k) (hℓ : 2 ≤ ℓ) (hα : 1 ≤ α)
    (A : OnlineAlg (Fin ℓ × Fin k) ℓ k Prod.fst) {c β : ℝ} (hc : 0 ≤ c)
    (hA : IsCompetitive (IsLearningInput ℓ k) α A c β) :
    (k : ℝ) * ℓ / 12 - 1 - β / (4 * α) ≤ c := by
  have h := theorem_2_1_competitive hk hℓ hα A hc hA
  have hk' : (3 : ℝ) ≤ k := by exact_mod_cast hk
  have hℓ' : (2 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have : (k : ℝ) * ℓ / 12 - 1 ≤ (((k : ℝ) - 2) * ((ℓ : ℝ) - 1) - 2) / 2 := by nlinarith
  linarith

/-- The general partitioning model accepts every request sequence, so the lower bound holds there
too ("that holds also in the general partitioning model"). -/
theorem theorem_2_1_general {k ℓ α : ℕ} (hk : 3 ≤ k) (hℓ : 2 ≤ ℓ) (hα : 1 ≤ α)
    (A : OnlineAlg (Fin ℓ × Fin k) ℓ k Prod.fst) {c β : ℝ} (hc : 0 ≤ c)
    (hA : IsCompetitive (fun _ => True) α A c β) :
    (((k : ℝ) - 2) * ((ℓ : ℝ) - 1) - 2) / 2 - β / (4 * α) ≤ c :=
  theorem_2_1_competitive hk hℓ hα A hc fun σ _ => hA σ trivial

/-- **Theorem 2.1, static-pattern version.** The adversarial input can be continued forever so
that every communicating pair communicates infinitely often: there is an infinite static
learning-model input and an offline schedule paying at most `4α` on every prefix, while `A` pays at
least `2α · ((k - 2)(ℓ - 1) - 2)` on all long enough prefixes. -/
theorem theorem_2_1_static {k ℓ α : ℕ} (hk : 3 ≤ k) (hℓ : 2 ≤ ℓ) (hα : 1 ≤ α)
    (A : OnlineAlg (Fin ℓ × Fin k) ℓ k Prod.fst) :
    ∃ σ : ℕ → Req (Fin ℓ × Fin k), IsStaticLearningInput ℓ k σ ∧
      (∃ O, IsSchedule k Prod.fst O ∧ ∀ T, schedCost α (prefixOf σ T) O ≤ 4 * α) ∧
      ∃ T₀, ∀ T, T₀ ≤ T → 2 * α * ((k - 2) * (ℓ - 1) - 2) ≤ algCost α A (prefixOf σ T) := by
  obtain ⟨K, rfl⟩ : ∃ K, k = K + 3 := ⟨k - 3, by omega⟩
  obtain ⟨L, rfl⟩ : ∃ L, ℓ = L + 2 := ⟨ℓ - 2, by omega⟩
  obtain ⟨σ₀, P, hPb, hPc, hPd, ⟨r, τ, hσ₀, -⟩, hcost⟩ := LB.lower_bound_core (A := A) hα
  have hn : 0 < σ₀.length := by rw [hσ₀]; simp
  set n := σ₀.length
  let σ : ℕ → Req (LB.Node L K) := fun t => σ₀[t % n]'(Nat.mod_lt _ hn)
  have hσmem : ∀ t, σ t ∈ σ₀ := fun t => List.getElem_mem _
  have hpre : prefixOf σ n = σ₀ := by
    apply List.ext_getElem (by simp [prefixOf, n])
    intro i h1 h2
    simp only [prefixOf, List.getElem_map, List.getElem_range, σ]
    congr 1
    exact Nat.mod_eq_of_lt h2
  refine ⟨σ, ⟨⟨P, hPb, fun t => hPc _ (hσmem t)⟩, fun t T => ⟨t + n * T, ?_, ?_⟩⟩,
    ⟨fun t => if t = 0 then LB.init else P, ⟨ite_eq_left rfl, fun t => ?_⟩, fun T => ?_⟩, n,
    fun T hT => ?_⟩
  · nlinarith
  · simp only [σ, Nat.add_mul_mod_self_left]
  · by_cases ht : t = 0
    · simp only [ht, ite_eq_left]; exact LB.init_balanced
    · simp only [ht, ite_false]; exact hPb
  · refine (schedCost_switch_le α _ P _ fun r hr => ?_).trans ?_
    · obtain ⟨t, rfl⟩ := mem_prefixOf hr; exact hPc _ (hσmem t)
    · rw [mul_comm 4]; exact Nat.mul_le_mul_left _ hPd
  · obtain ⟨τ', hτ'⟩ := prefixOf_prefix σ hT
    rw [← hτ', hpre]
    simpa using hcost.trans (algCost_le_append A σ₀ τ')

end Papers.PODC2020.DynamicPartitioningLB
