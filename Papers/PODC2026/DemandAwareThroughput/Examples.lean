import Papers.PODC2026.DemandAwareThroughput.Weak

/-!
# The two examples of §2 (Figure 2)

Bentert, Avin, Schmid, PODC 2026, §2: demand-aware throughput and demand-aware weak direct
throughput are incomparable. For `M₁ = [[1/2, 1/2], [1/2, 1/2]]`, `(M₁, 8/9)` is a yes-instance
of Demand-Aware Throughput but a no-instance of Demand-Aware Weak Direct Throughput (the paper's
text says `9/8`, a typo for the `8/9` of Figure 2); for `M₂ = [[9/10, 1/10], [1/10, 9/10]]`,
`(M₂, 9/10)` is a yes-instance of Demand-Aware Weak Direct Throughput but a no-instance of
Demand-Aware Throughput.
-/

namespace Podc.DemandAwareThroughput

open Finset

/-- `M₁` of §2. -/
noncomputable def exM1 : Matrix (Fin 2) (Fin 2) ℝ := !![1 / 2, 1 / 2; 1 / 2, 1 / 2]

/-- `M₂` of §2. -/
noncomputable def exM2 : Matrix (Fin 2) (Fin 2) ℝ := !![9 / 10, 1 / 10; 1 / 10, 9 / 10]

lemma exM1_mem : exM1 ∈ doublyStochastic ℝ (Fin 2) := by
  rw [mem_doublyStochastic_iff_sum]
  refine ⟨fun i j => ?_, fun i => ?_, fun j => ?_⟩
  · fin_cases i <;> fin_cases j <;> simp [exM1]
  · fin_cases i <;> simp [exM1, Fin.sum_univ_two] <;> norm_num
  · fin_cases j <;> simp [exM1, Fin.sum_univ_two] <;> norm_num

lemma exM2_mem : exM2 ∈ doublyStochastic ℝ (Fin 2) := by
  rw [mem_doublyStochastic_iff_sum]
  refine ⟨fun i j => ?_, fun i => ?_, fun j => ?_⟩
  · fin_cases i <;> fin_cases j <;> simp [exM2] <;> norm_num
  · fin_cases i <;> simp [exM2, Fin.sum_univ_two] <;> norm_num
  · fin_cases j <;> simp [exM2, Fin.sum_univ_two] <;> norm_num

/-- §2, Figure 2(a): `(M₁, 8/9)` is a yes-instance of Demand-Aware Throughput (graph with one
self-loop per node and two arcs each way). -/
theorem example_M1_throughput : DAThroughput exM1 (8 / 9) := by
  let A : Matrix (Fin 2) (Fin 2) ℕ := !![1, 2; 2, 1]
  let o : Fin 2 → Fin 2 := fun u => if u = 0 then 1 else 0
  let P : Fin 2 × Fin 3 → Path 2 := fun q =>
    if q.2 = 0 then Path.arc q.1 q.1 else if q.2 = 1 then Path.two q.1 (o q.1) q.1
    else Path.arc q.1 (o q.1)
  let d : Fin 2 × Fin 3 → ℝ := fun q => if q.2 = 0 then 1 else if q.2 = 1 then 1 / 3 else 4 / 3
  refine ⟨A, ⟨fun i => ?_, fun j => ?_⟩, 8 / 9, le_rfl,
    ⟨Fin 2 × Fin 3, inferInstance, P, d, fun k => ?_, fun u v => ?_, fun u v => ?_⟩⟩
  · fin_cases i <;> simp [A, Fin.sum_univ_two, deg]
  · fin_cases j <;> simp [A, Fin.sum_univ_two, deg]
  · simp only [d]; split_ifs <;> norm_num
  · unfold served
    simp only [Fintype.sum_prod_type, Fin.sum_univ_two, Fin.sum_univ_three, P, d, o]
    fin_cases u <;> fin_cases v <;> simp [exM1, Path.tgt, Path.arc, Path.two, deg] <;> norm_num
  · unfold load
    simp only [Fintype.sum_prod_type, Fin.sum_univ_two, Fin.sum_univ_three, P, d, o]
    fin_cases u <;> fin_cases v <;> simp [A, Path.arcs, Path.arc, Path.two] <;> norm_num

/-- §2: `(M₁, 8/9)` is a no-instance of Demand-Aware Weak Direct Throughput (the best weak direct
throughput for `M₁` is `5/6`). -/
theorem example_M1_not_weakDirect : ¬ DAWeakDirectThroughput exM1 (8 / 9) := by
  rw [observation_4 (by norm_num) exM1_mem]
  rintro ⟨N, ⟨hr, -⟩, h⟩
  have key : ∀ i, ∑ j, min ((2 * (2 : ℕ) - 1 : ℝ) * exM1 i j) (N i j : ℝ) ≤ 5 / 2 := by
    intro i
    have hi := hr i
    simp only [Fin.sum_univ_two, deg] at hi ⊢
    have h0 : N i 1 = 3 - N i 0 := by omega
    have hle : N i 0 ≤ 3 := by omega
    have e : ∀ j, (2 * (2 : ℕ) - 1 : ℝ) * exM1 i j = 3 / 2 := by
      intro j; fin_cases i <;> fin_cases j <;> simp [exM1] <;> norm_num
    rw [e, e, h0]
    interval_cases N i 0 <;> norm_num
  have := sum_le_sum fun i (_ : i ∈ univ) => key i
  simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] at this
  push_cast at h this
  linarith

/-- §2, Figure 2(d): `(M₂, 9/10)` is a yes-instance of Demand-Aware Weak Direct Throughput
(three self-loops per node). -/
theorem example_M2_weakDirect : DAWeakDirectThroughput exM2 (9 / 10) := by
  refine ⟨!![3, 0; 0, 3], ⟨fun i => ?_, fun j => ?_⟩, !![9 / 10, 0; 0, 9 / 10], fun i j => ?_,
    ?_, ?_⟩
  · fin_cases i <;> simp [Fin.sum_univ_two, deg]
  · fin_cases j <;> simp [Fin.sum_univ_two, deg]
  · fin_cases i <;> fin_cases j <;> simp [exM2]
  · simp [Fin.sum_univ_two]
  · unfold CanDirectlyHost; rw [canRouteDirectly_iff]
    intro u v
    fin_cases u <;> fin_cases v <;> simp [deg] <;> norm_num

/-- §2: `(M₂, 9/10)` is a no-instance of Demand-Aware Throughput (its best throughput is
`100/114`), even in the relaxed capacity semantics. -/
theorem example_M2_not_throughput_rel : ¬ DAThroughputRel exM2 (9 / 10) := by
  rintro ⟨A, ⟨hAr, hAc⟩, θ, hθ, hhost⟩
  obtain ⟨b1, b2⟩ := two_node_bounds_rel hhost
  have hdeg : ((deg 2 : ℕ) : ℝ) = 3 := by norm_num [deg]
  simp only [Matrix.smul_apply, smul_eq_mul, hdeg, exM2, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
    Matrix.head_cons] at b1 b2
  have r0 := hAr 0; have c1 := hAc 1
  simp only [Fin.sum_univ_two, deg] at r0 c1
  have e00 : A 0 0 = 3 - A 0 1 := by omega
  have e11 : A 1 1 = 3 - A 0 1 := by omega
  have hle : A 0 1 ≤ 3 := by omega
  rw [e00, e11] at b2
  interval_cases h : A 0 1 <;> norm_num at b1 b2 <;> nlinarith

/-- §2: `(M₂, 9/10)` is a no-instance of Demand-Aware Throughput. -/
theorem example_M2_not_throughput : ¬ DAThroughput exM2 (9 / 10) :=
  fun h => example_M2_not_throughput_rel h.rel

end Podc.DemandAwareThroughput
