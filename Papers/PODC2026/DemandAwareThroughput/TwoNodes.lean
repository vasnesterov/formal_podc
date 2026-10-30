import Papers.PODC2026.DemandAwareThroughput.Direct

/-!
# Two nodes: Proposition 1 (the upper bound `5/6` for demand-aware throughput)

Bentert, Avin, Schmid, PODC 2026, §3.1, Proposition 1.

For `n = 2` every directed `3`-regular graph has adjacency matrix `[[c, 3-c], [3-c, c]]`. Any path
from `a` to `b` uses the arc `(a, b)`; a path from `a` to `a` uses `(a, a)` or `(a, b)`; a path from
`b` to `b` uses `(b, b)` or `(a, b)`. Summing over a flow gives the two cut-type inequalities
`D a b ≤ A a b` and `D a b + D a a + D b b ≤ A a b + A a a + A b b` (`two_node_bounds`), from which
Proposition 1 follows by arithmetic. (The paper argues graph by graph; the conclusion is the same.)
-/

namespace Podc.DemandAwareThroughput

open Finset

/-- A walk that visits a set `S` and ends outside `S` has an arc leaving `S`. -/
lemma exists_arc_leaving {V : Type} (S : V → Prop) :
    ∀ (x : V) (l : List V) (hl : l ≠ []), (∃ y ∈ x :: l, S y) → ¬ S (l.getLast hl) →
      ∃ e ∈ (x :: l).zip l, S e.1 ∧ ¬ S e.2
  | x, [z], _, hy, hlast => by
    simp only [List.getLast_singleton] at hlast
    simp only [List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp, exists_eq_left]
      at hy
    rcases hy with hx | hz
    · exact ⟨(x, z), by simp, hx, hlast⟩
    · exact absurd hz hlast
  | x, z :: w :: l, _, hy, hlast => by
    by_cases hx : S x
    · by_cases hz : S z
      · obtain ⟨e, he, h⟩ := exists_arc_leaving S z (w :: l) (by simp) ⟨z, by simp, hz⟩
          (by simpa using hlast)
        exact ⟨e, by simp only [List.zip_cons_cons, List.mem_cons] at he ⊢; tauto, h⟩
      · exact ⟨(x, z), by simp, hx, hz⟩
    · have hy' : ∃ y ∈ z :: w :: l, S y := by
        obtain ⟨y, hy, hSy⟩ := hy
        rcases List.mem_cons.1 hy with rfl | hy
        · exact absurd hSy hx
        · exact ⟨y, hy, hSy⟩
      obtain ⟨e, he, h⟩ := exists_arc_leaving S z (w :: l) (by simp) hy' (by simpa using hlast)
      exact ⟨e, by simp only [List.zip_cons_cons, List.mem_cons] at he ⊢; tauto, h⟩

lemma fin2_eq_one {i : Fin 2} (h : i ≠ 0) : i = 1 := by omega

/-- In a path `0 → 1` the arc `(0, 1)` occurs. -/
lemma Path.mem_arcs_01 (p : Path 2) (hs : p.src = 0) (ht : p.tgt = 1) : (0, 1) ∈ p.arcs := by
  obtain ⟨e, he, h1, h2⟩ := exists_arc_leaving (fun v => v = 0) p.src p.rest p.rest_ne
    ⟨p.src, by simp, hs⟩ (by change ¬ p.tgt = 0; rw [ht]; decide)
  have : e = (0, 1) := Prod.ext h1 (fin2_eq_one h2)
  exact this ▸ he

lemma Path.first_mem_arcs (p : Path 2) : (p.src, p.rest.head p.rest_ne) ∈ p.arcs := by
  obtain ⟨s, r, hr⟩ := p
  cases r with
  | nil => exact absurd rfl hr
  | cons h t => simp [Path.arcs]

/-- Indicator that the path traverses the pair `e`. -/
noncomputable def Path.ind {n : ℕ} (p : Path n) (e : Fin n × Fin n) : ℝ :=
  if e ∈ p.arcs then 1 else 0

lemma Path.ind_nonneg {n : ℕ} (p : Path n) (e : Fin n × Fin n) : 0 ≤ p.ind e := by
  unfold Path.ind; split_ifs <;> norm_num

lemma Path.one_le_ind {n : ℕ} (p : Path n) {e : Fin n × Fin n} (h : e ∈ p.arcs) :
    1 ≤ p.ind e := by
  unfold Path.ind; rw [ite_eq_left h]

/-- Pointwise inequalities for one path on two nodes. -/
lemma Path.two_node_ineq (p : Path 2) :
    ((if p.src = 0 ∧ p.tgt = 1 then 1 else 0 : ℝ) ≤ p.ind (0, 1)) ∧
    ((if p.src = 0 ∧ p.tgt = 1 then 1 else 0 : ℝ) + (if p.src = 0 ∧ p.tgt = 0 then 1 else 0)
      + (if p.src = 1 ∧ p.tgt = 1 then 1 else 0) ≤
      p.ind (0, 1) + p.ind (0, 0) + p.ind (1, 1)) := by
  have c0 : ∀ e, (0 : ℝ) ≤ p.ind e := p.ind_nonneg
  have h01 : p.src = 0 → p.tgt = 1 → (1 : ℝ) ≤ p.ind (0, 1) :=
    fun hs ht => p.one_le_ind (p.mem_arcs_01 hs ht)
  refine ⟨?_, ?_⟩
  · split_ifs with h
    · exact h01 h.1 h.2
    · exact c0 _
  · have hfirst := p.first_mem_arcs
    by_cases hs : p.src = 0
    · by_cases ht : p.tgt = 1
      · have := h01 hs ht
        simp only [hs, ht, true_and, ite_true, show (1 : Fin 2) ≠ 0 by decide, ite_false,
          and_true, show (0 : Fin 2) ≠ 1 by decide, false_and]
        linarith [c0 (0, 0), c0 (1, 1)]
      · have ht0 : p.tgt = 0 := by
          by_contra h; exact ht (fin2_eq_one h)
        simp only [hs, ht0, ite_true, and_true, show (0 : Fin 2) ≠ 1 by decide, and_false,
          ite_false, false_and, zero_add, add_zero]
        rw [hs] at hfirst
        rcases (show p.rest.head p.rest_ne = 0 ∨ p.rest.head p.rest_ne = 1 by omega) with h | h
        · rw [h] at hfirst; linarith [p.one_le_ind hfirst, c0 (0, 1), c0 (1, 1)]
        · rw [h] at hfirst; linarith [p.one_le_ind hfirst, c0 (0, 0), c0 (1, 1)]
    · have hs1 : p.src = 1 := fin2_eq_one hs
      by_cases ht : p.tgt = 1
      · simp only [hs1, ht, show (1 : Fin 2) ≠ 0 by decide, ite_false, false_and, and_self,
          ite_true, zero_add]
        rw [hs1] at hfirst
        rcases (show p.rest.head p.rest_ne = 0 ∨ p.rest.head p.rest_ne = 1 by omega) with h | h
        · -- the walk visits `0` and ends at `1`
          obtain ⟨e, he, h1, h2⟩ := exists_arc_leaving (fun v => v = 0) p.src p.rest p.rest_ne
            ⟨p.rest.head p.rest_ne, List.mem_cons_of_mem _ (List.head_mem _), h⟩
            (by change ¬ p.tgt = 0; rw [ht]; decide)
          have : e = (0, 1) := Prod.ext h1 (fin2_eq_one h2)
          have he' : (0, 1) ∈ p.arcs := this ▸ he
          linarith [p.one_le_ind he', c0 (0, 0), c0 (1, 1)]
        · rw [h] at hfirst; linarith [p.one_le_ind hfirst, c0 (0, 0), c0 (0, 1)]
      · simp only [hs1, ht, show (1 : Fin 2) ≠ 0 by decide, ite_false, false_and, and_false]
        linarith [c0 (0, 0), c0 (1, 1), c0 (0, 1)]

/-- Cut-type bounds for (relaxed) routing on two nodes. -/
theorem two_node_bounds_rel {A : Matrix (Fin 2) (Fin 2) ℕ} {D : Matrix (Fin 2) (Fin 2) ℝ}
    (h : CanRouteRel A D) :
    D 0 1 ≤ A 0 1 ∧ D 0 1 + D 0 0 + D 1 1 ≤ A 0 1 + A 0 0 + A 1 1 := by
  obtain ⟨ι, _, P, d, hd, hs, hl⟩ := h
  have e : ∀ u v, D u v = ∑ k, d k * (if (P k).src = u ∧ (P k).tgt = v then 1 else 0) := by
    intro u v; rw [← hs u v]; unfold served
    exact sum_congr rfl fun k _ => by split_ifs <;> simp
  refine ⟨?_, ?_⟩
  · refine le_trans ?_ (hl 0 1)
    rw [e]; unfold loadInd
    exact sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (P k).two_node_ineq.1 (hd k)
  · refine le_trans ?_ (add_le_add (add_le_add (hl 0 1) (hl 0 0)) (hl 1 1))
    rw [e, e, e]; unfold loadInd
    simp only [← sum_add_distrib, ← mul_add]
    exact sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (P k).two_node_ineq.2 (hd k)

/-- Cut-type bounds for routing on two nodes. -/
theorem two_node_bounds {A : Matrix (Fin 2) (Fin 2) ℕ} {D : Matrix (Fin 2) (Fin 2) ℝ}
    (h : CanRoute A D) :
    D 0 1 ≤ A 0 1 ∧ D 0 1 + D 0 0 + D 1 1 ≤ A 0 1 + A 0 0 + A 1 1 :=
  two_node_bounds_rel h.rel

/-- The matrix `M_κ = [[1-ε, ε], [ε, 1-ε]]` of Proposition 1. -/
noncomputable def prop1Matrix (ε : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![1 - ε, ε; ε, 1 - ε]

lemma prop1Matrix_mem {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) :
    prop1Matrix ε ∈ doublyStochastic ℝ (Fin 2) := by
  rw [mem_doublyStochastic_iff_sum]
  refine ⟨fun i j => ?_, fun i => ?_, fun j => ?_⟩
  · fin_cases i <;> fin_cases j <;> simp [prop1Matrix] <;> linarith
  · fin_cases i <;> simp [prop1Matrix, Fin.sum_univ_two]
  · fin_cases j <;> simp [prop1Matrix, Fin.sum_univ_two]

/-- **Proposition 1.** For each `κ > 5/6` there is a doubly stochastic `2 × 2` matrix `M_κ` such
that `(M_κ, κ)` is a no-instance of Demand-Aware Throughput, even in the relaxed capacity
semantics `DAThroughputRel` (see `proposition_1`). The paper takes `κ ≤ 1`, the range of the
problem; for `κ > 1` we use the matrix for `κ = 1`. -/
theorem proposition_1_rel {κ : ℝ} (hκ : 5 / 6 < κ) :
    ∃ M ∈ doublyStochastic ℝ (Fin 2), ¬ DAThroughputRel M κ := by
  set ε := min κ 1 - 5 / 6 with hε
  have hε0 : 0 < ε := by rw [hε]; exact sub_pos.2 (lt_min hκ (by norm_num))
  have hε1 : ε ≤ 1 / 6 := by rw [hε]; linarith [min_le_right κ 1]
  refine ⟨prop1Matrix ε, prop1Matrix_mem hε0.le (by linarith), ?_⟩
  rintro ⟨A, ⟨hAr, hAc⟩, θ, hθ, hhost⟩
  have hθ' : 5 / 6 + ε ≤ θ := by rw [hε]; linarith [min_le_left κ 1]
  obtain ⟨b1, b2⟩ := two_node_bounds_rel hhost
  have hdeg : ((deg 2 : ℕ) : ℝ) = 3 := by norm_num [deg]
  simp only [Matrix.smul_apply, smul_eq_mul, hdeg, prop1Matrix, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.head_cons] at b1 b2
  have r0 := hAr 0
  have c1 := hAc 1
  simp only [Fin.sum_univ_two, deg] at r0 c1
  have hA11 : (A 1 1 : ℝ) = 3 - A 0 1 := by
    have : A 1 1 = 3 - A 0 1 := by omega
    rw [this, Nat.cast_sub (by omega)]; norm_num
  have hA00 : (A 0 0 : ℝ) = 3 - A 0 1 := by
    have : A 0 0 = 3 - A 0 1 := by omega
    rw [this, Nat.cast_sub (by omega)]; norm_num
  rw [hA11, hA00] at b2
  rcases Nat.eq_zero_or_pos (A 0 1) with h0 | hpos
  · rw [h0] at b1; simp at b1; nlinarith
  · have : (1 : ℝ) ≤ A 0 1 := by exact_mod_cast hpos
    nlinarith

/-- **Proposition 1.** For each `κ > 5/6` there is a doubly stochastic `2 × 2` matrix `M_κ` such
that `(M_κ, κ)` is a no-instance of Demand-Aware Throughput. -/
theorem proposition_1 {κ : ℝ} (hκ : 5 / 6 < κ) :
    ∃ M ∈ doublyStochastic ℝ (Fin 2), ¬ DAThroughput M κ := by
  obtain ⟨M, hM, h⟩ := proposition_1_rel hκ
  exact ⟨M, hM, fun h' => h h'.rel⟩

end Podc.DemandAwareThroughput
