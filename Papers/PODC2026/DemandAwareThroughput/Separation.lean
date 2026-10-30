import Papers.PODC2026.DemandAwareThroughput.Direct
import Papers.PODC2026.DemandAwareThroughput.Chernoff
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# The separation result: Theorem 5 (and Theorem 2)

Bentert, Avin, Schmid, PODC 2026, §3.1, Theorem 5: for every `κ < 5/8` there is `n_κ` such that
for all `n ≥ n_κ` every doubly stochastic `n × n` matrix `M` admits a directed `(2n-1)`-regular
graph of throughput at least `κ` for `M`.

The proof follows the paper. With `ε = 5/8 - κ` (the paper writes `ε = κ - 5/8 > 0`, a sign
typo) and `b = (n-1)·M`, the fractional parts `b' = b - ⌊b⌋` have integer row and column sums and
are rounded by dependent rounding (Theorem 3, the hypothesis `DependentRounding`). The graph has
`⌊b_ij⌋ + β_ij + 1` arcs from `i` to `j` (`β` the rounding). Stage 1 sends `b_ij` directly; the
excess capacity `η_ij = (1 - b'_ij) + b'_ij β_ij` has expected row/column sums `≥ 3n/4`, and by
Theorem 4 (proved in `Chernoff.lean`) and a union bound some rounding has all row and column
excess sums `> (3/4 - ε)n`. Stage 2 routes the remaining demand `σ_ij` over two-hop paths
`i → h → j` proportionally to `min(η_ih, η_hj)`.

The paper applies Theorem 4 "with `t = n + Y_i` variables", where `Y_i = ∑_j (1 - b'_ij)` need not
be an integer; we instead add `n` constant variables with weights `1 - b'_ij ∈ [0, 1]`
(`line_bad_prob_le`).
-/

namespace Podc.DemandAwareThroughput

open Finset

namespace FinDist

variable {Ω : Type} [Fintype Ω] (μ : FinDist Ω)

lemma prob_nonneg (E : Ω → Prop) : 0 ≤ μ.prob E := by
  unfold prob; exact sum_nonneg fun ω _ => by split_ifs <;> simp [μ.nonneg ω]

lemma prob_mono {E F : Ω → Prop} (h : ∀ ω, E ω → F ω) : μ.prob E ≤ μ.prob F := by
  unfold prob
  refine sum_le_sum fun ω _ => ?_
  by_cases hE : E ω
  · rw [ite_eq_left hE, ite_eq_left (h ω hE)]
  · rw [ite_eq_right hE]; split_ifs <;> simp [μ.nonneg ω]

lemma prob_or_le (E F : Ω → Prop) : μ.prob (fun ω => E ω ∨ F ω) ≤ μ.prob E + μ.prob F := by
  unfold prob
  rw [← sum_add_distrib]
  refine sum_le_sum fun ω _ => ?_
  have := μ.nonneg ω
  by_cases hE : E ω <;> by_cases hF : F ω <;> simp [hE, hF, this]

lemma prob_exists_le {ι : Type} [Fintype ι] (E : ι → Ω → Prop) :
    μ.prob (fun ω => ∃ i, E i ω) ≤ ∑ i, μ.prob (E i) := by
  classical
  unfold prob
  rw [sum_comm]
  refine sum_le_sum fun ω _ => ?_
  have := μ.nonneg ω
  by_cases h : ∃ i, E i ω
  · rw [ite_eq_left h]
    obtain ⟨i, hi⟩ := h
    calc μ.w ω = (if E i ω then μ.w ω else 0) := by rw [ite_eq_left hi]
      _ ≤ ∑ j, (if E j ω then μ.w ω else 0) :=
        single_le_sum (f := fun j => if E j ω then μ.w ω else 0)
          (fun j _ => by split_ifs <;> simp [this]) (mem_univ i)
  · rw [ite_eq_right h]; exact sum_nonneg fun j _ => by split_ifs <;> simp [this]

/-- If an event has probability `< 1`, some outcome of positive weight avoids it. -/
lemma exists_not_of_prob_lt_one {E : Ω → Prop} (h : μ.prob E < 1) :
    ∃ ω, μ.w ω ≠ 0 ∧ ¬ E ω := by
  by_contra hc
  push Not at hc
  apply lt_irrefl (1 : ℝ)
  calc (1 : ℝ) = ∑ ω, μ.w ω := μ.sum_eq_one.symm
    _ = μ.prob E := by
        unfold prob
        refine sum_congr rfl fun ω _ => ?_
        by_cases hw : μ.w ω = 0
        · simp [hw]
        · rw [ite_eq_left (hc ω hw)]
    _ < 1 := h

lemma prob_true : μ.prob (fun _ => True) = 1 := by
  simp [prob, μ.sum_eq_one]

lemma prob_false : μ.prob (fun _ => False) = 0 := by
  simp [prob]

end FinDist

/-! ### The probabilistic estimate for one row or column -/

/-- For one row (or column) of the rounding: the excess sum `∑ⱼ ((1 - xⱼ) + xⱼ Xⱼ)` is at most
`(3/4 - ε) n` with probability at most `exp(-2nε²/3)`. -/
theorem line_bad_prob_le {Ω : Type} [Fintype Ω] (μ : FinDist Ω) {n : ℕ}
    (X : Fin n → Ω → Bool) (x : Fin n → ℝ) (hx : ∀ k, 0 ≤ x k ∧ x k ≤ 1)
    (hmarg : ∀ k, μ.prob (fun ω => X k ω = true) = x k)
    (hneg : ∀ S : Finset (Fin n), μ.prob (fun ω => ∀ k ∈ S, X k ω = false) ≤ ∏ k ∈ S, (1 - x k))
    {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 3 / 4) :
    μ.prob (fun ω => ∑ k, ((1 - x k) + x k * bval (X k ω)) ≤ (3 / 4 - ε) * n) ≤
      Real.exp (-(2 * n * ε ^ 2 / 3)) := by
  classical
  -- variables: `inl k` is `X k` with weight `x k`; `inr k` is the constant `1` with weight `1 - x k`
  let X' : Fin n ⊕ Fin n → Ω → Bool := fun k ω => Sum.elim (fun k => X k ω) (fun _ => true) k
  let a : Fin n ⊕ Fin n → ℝ := Sum.elim x (fun k => 1 - x k)
  let x' : Fin n ⊕ Fin n → ℝ := Sum.elim x (fun _ => 1)
  set δ : ℝ := 4 * ε / 3 with hδ
  have hδ0 : 0 ≤ δ := by positivity
  have hδ1 : δ ≤ 1 := by rw [hδ]; linarith
  have hC := negCorrChernoff Ω (Fin n ⊕ Fin n) μ X' a x'
    (fun k => by cases k <;> simp [a, hx])
    (fun k => by cases k <;> simp [x', hx])
    (fun k => by
      cases k with
      | inl k => exact hmarg k
      | inr k => simpa [X', x'] using μ.prob_true)
    (fun S => by
      by_cases hS : S.toRight = ∅
      · have hE : (fun ω => ∀ k ∈ S, X' k ω = false) =
            (fun ω => ∀ k ∈ S.toLeft, X k ω = false) := by
          funext ω
          apply propext
          constructor
          · intro h k hk; exact h (Sum.inl k) (Finset.mem_toLeft.1 hk)
          · intro h k hk
            cases k with
            | inl k => exact h k (Finset.mem_toLeft.2 hk)
            | inr k =>
              have : k ∈ S.toRight := Finset.mem_toRight.2 hk
              rw [hS] at this; simp at this
        rw [hE]
        calc _ ≤ ∏ k ∈ S.toLeft, (1 - x k) := hneg _
          _ = ∏ k ∈ S, (1 - x' k) := by
            conv_rhs => rw [← Finset.toLeft_disjSum_toRight (u := S)]
            rw [Finset.prod_disjSum, hS]; simp [x']
      · obtain ⟨k, hk⟩ := Finset.nonempty_iff_ne_empty.2 hS
        have hE : (fun ω => ∀ k ∈ S, X' k ω = false) = (fun _ => False) := by
          funext ω
          apply propext
          constructor
          · intro h; have := h (Sum.inr k) (Finset.mem_toRight.1 hk); simp [X'] at this
          · intro h; exact h.elim
        rw [hE, μ.prob_false]
        apply le_of_eq
        symm
        apply Finset.prod_eq_zero (Finset.mem_toRight.1 hk)
        simp [x'])
    δ hδ0 hδ1
  -- the mean
  set m : ℝ := ∑ k, a k * x' k with hm
  have hm_eq : m = ∑ k, (x k ^ 2 + (1 - x k)) := by
    rw [hm, Fintype.sum_sum_type, ← sum_add_distrib]
    exact sum_congr rfl fun k _ => by simp [a, x']; ring
  have hm_ge : 3 / 4 * (n : ℝ) ≤ m := by
    rw [hm_eq]
    have : ∀ k, 3 / 4 ≤ x k ^ 2 + (1 - x k) := fun k => by nlinarith [sq_nonneg (x k - 1 / 2)]
    calc 3 / 4 * (n : ℝ) = ∑ _k : Fin n, (3 / 4 : ℝ) := by simp; ring
      _ ≤ _ := sum_le_sum fun k _ => this k
  have hsum : ∀ ω, ∑ k, a k * bval (X' k ω) = ∑ k, ((1 - x k) + x k * bval (X k ω)) := by
    intro ω
    rw [Fintype.sum_sum_type, ← sum_add_distrib]
    exact sum_congr rfl fun k _ => by cases h : X k ω <;> simp [a, X', bval, h]
  calc _ ≤ μ.prob (fun ω => ∑ k, a k * bval (X' k ω) ≤ m * (1 - δ)) := by
        apply μ.prob_mono
        intro ω hω
        rw [hsum]
        refine hω.trans ?_
        have : (3 / 4 - ε) * (n : ℝ) = 3 / 4 * n * (1 - δ) := by rw [hδ]; ring
        rw [this]
        exact mul_le_mul_of_nonneg_right hm_ge (by linarith)
    _ ≤ Real.exp (-(m * δ ^ 2 / 2)) := hC
    _ ≤ Real.exp (-(2 * n * ε ^ 2 / 3)) := by
        apply Real.exp_le_exp.2
        have : 2 * (n : ℝ) * ε ^ 2 / 3 = 3 / 4 * n * δ ^ 2 / 2 := by rw [hδ]; ring
        rw [this]
        have := mul_le_mul_of_nonneg_right hm_ge (sq_nonneg δ)
        linarith

/-! ### The deterministic construction for a good rounding -/

section Construction

variable {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (β : Fin n → Fin n → Bool)

/-- `b_ij = (n - 1) a_ij`. -/
noncomputable def bb (i j : Fin n) : ℝ := ((n : ℝ) - 1) * M i j

/-- `⌊b_ij⌋`. -/
noncomputable def fl (i j : Fin n) : ℕ := ⌊bb M i j⌋₊

/-- The fractional part `b'_ij = b_ij - ⌊b_ij⌋`. -/
noncomputable def fr (i j : Fin n) : ℝ := bb M i j - fl M i j

/-- The excess capacity `η_ij = min(d_ij - b_ij, 1) = (1 - b'_ij) + b'_ij β_ij`. -/
noncomputable def eta (i j : Fin n) : ℝ := (1 - fr M i j) + fr M i j * bval (β i j)

/-- The common excess `ζ_ij = ∑_h min(η_ih, η_hj)`. -/
noncomputable def zeta (i j : Fin n) : ℝ := ∑ h, min (eta M β i h) (eta M β h j)

/-- The graph: `d_ij = c_ij + 1 = ⌊b_ij⌋ + β_ij + 1` arcs from `i` to `j`. -/
noncomputable def graphOf : Matrix (Fin n) (Fin n) ℕ :=
  fun i j => fl M i j + (if β i j then 1 else 0) + 1

variable {M}

lemma bb_nonneg (hn : 1 ≤ n) (h0 : ∀ i j, 0 ≤ M i j) (i j : Fin n) : 0 ≤ bb M i j := by
  unfold bb
  have : (1 : ℝ) ≤ n := by exact_mod_cast hn
  exact mul_nonneg (by linarith) (h0 i j)

lemma fr_nonneg (hn : 1 ≤ n) (h0 : ∀ i j, 0 ≤ M i j) (i j : Fin n) : 0 ≤ fr M i j := by
  unfold fr fl; linarith [Nat.floor_le (bb_nonneg hn h0 i j)]

lemma fr_lt_one (i j : Fin n) : fr M i j < 1 := by
  unfold fr fl; linarith [Nat.lt_floor_add_one (bb M i j)]

lemma eta_nonneg (hn : 1 ≤ n) (h0 : ∀ i j, 0 ≤ M i j) (i j : Fin n) : 0 ≤ eta M β i j := by
  unfold eta bval
  have := fr_nonneg hn h0 i j; have := fr_lt_one (M := M) i j
  split_ifs <;> nlinarith

lemma eta_le_one (hn : 1 ≤ n) (h0 : ∀ i j, 0 ≤ M i j) (i j : Fin n) : eta M β i j ≤ 1 := by
  unfold eta bval
  have := fr_nonneg hn h0 i j
  split_ifs <;> nlinarith

lemma bb_add_eta_le (i j : Fin n) : bb M i j + eta M β i j ≤ graphOf M β i j := by
  unfold eta graphOf bval
  have h1 := fr_lt_one (M := M) i j
  unfold fr at h1 ⊢
  split_ifs <;> push_cast <;> nlinarith

lemma min_ge_add_sub_one {x y : ℝ} (hx : x ≤ 1) (hy : y ≤ 1) : x + y - 1 ≤ min x y := by
  rcases le_total x y with h | h
  · rw [min_eq_left h]; linarith
  · rw [min_eq_right h]; linarith

/-- Rows of `graphOf` sum to `2n - 1` when the rounding preserves the row sums of `b'`. -/
lemma graphOf_row (hn : 1 ≤ n) (hr : ∀ i, ∑ j, M i j = 1)
    (hrow : ∀ i, ∑ j, bval (β i j) = ∑ j, fr M i j) (i : Fin n) :
    ∑ j, graphOf M β i j = deg n := by
  apply Nat.cast_injective (R := ℝ)
  rw [deg_cast hn]
  push_cast [graphOf]
  have e1 : ∑ j, ((if β i j then (1 : ℝ) else 0)) = ∑ j, fr M i j := hrow i
  simp only [sum_add_distrib, e1]
  have : ∑ j, (fl M i j : ℝ) + ∑ j, fr M i j = n - 1 := by
    rw [← sum_add_distrib]
    simp only [fr, add_sub_cancel, bb, ← mul_sum, hr i, mul_one]
  simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  linarith

lemma graphOf_col (hn : 1 ≤ n) (hc : ∀ j, ∑ i, M i j = 1)
    (hcol : ∀ j, ∑ i, bval (β i j) = ∑ i, fr M i j) (j : Fin n) :
    ∑ i, graphOf M β i j = deg n := by
  apply Nat.cast_injective (R := ℝ)
  rw [deg_cast hn]
  push_cast [graphOf]
  have e1 : ∑ i, ((if β i j then (1 : ℝ) else 0)) = ∑ i, fr M i j := hcol j
  simp only [sum_add_distrib, e1]
  have : ∑ i, (fl M i j : ℝ) + ∑ i, fr M i j = n - 1 := by
    rw [← sum_add_distrib]
    simp only [fr, add_sub_cancel, bb, ← mul_sum, hc j, mul_one]
  simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  linarith

/-- The common excess is at least `(1/2 - 2ε) n`. -/
lemma zeta_ge (hn : 1 ≤ n) (h0 : ∀ i j, 0 ≤ M i j) {ε : ℝ}
    (hR : ∀ i, (3 / 4 - ε) * n < ∑ j, eta M β i j)
    (hC : ∀ j, (3 / 4 - ε) * n < ∑ i, eta M β i j) (i j : Fin n) :
    (1 / 2 - 2 * ε) * n ≤ zeta M β i j := by
  unfold zeta
  calc (1 / 2 - 2 * ε) * (n : ℝ) ≤ ∑ h, eta M β i h + ∑ h, eta M β h j - n := by
        linarith [hR i, hC j]
    _ = ∑ h, (eta M β i h + eta M β h j - 1) := by
        simp [sum_add_distrib, sum_sub_distrib]
    _ ≤ _ := sum_le_sum fun h _ =>
        min_ge_add_sub_one (eta_le_one β hn h0 i h) (eta_le_one β hn h0 h j)

end Construction

section Flow

variable {n : ℕ} {M : Matrix (Fin n) (Fin n) ℝ} (β : Fin n → Fin n → Bool)

lemma count_arc (i j u v : Fin n) :
    (((Path.arc i j).arcs.count (u, v) : ℕ) : ℝ) = if i = u ∧ j = v then 1 else 0 := by
  simp [List.count_singleton, Prod.mk.injEq]

lemma count_two (i h j u v : Fin n) :
    (((Path.two i h j).arcs.count (u, v) : ℕ) : ℝ) =
      (if i = u ∧ h = v then 1 else 0) + (if h = u ∧ j = v then 1 else 0) := by
  simp only [Path.two_arcs, List.count_cons, List.count_nil, beq_iff_eq, Prod.mk.injEq]
  push_cast
  split_ifs <;> simp

/-- **The second stage.** For a rounding `β` that preserves the row and column sums of `b'` and
whose row and column excess sums all exceed `(3/4 - ε) n`, the graph `graphOf M β` is
`(2n-1)`-regular and hosts `κ • M` for `κ = 5/8 - ε`. -/
theorem canHost_of_good (hn : 1 ≤ n) (hM : M ∈ doublyStochastic ℝ (Fin n)) {κ ε : ℝ}
    (hκ : κ = 5 / 8 - ε) (hε0 : 0 < ε) (hε1 : ε < 1 / 4)
    (hs : (n : ℝ) - 1 ≤ (2 * n - 1) * κ) (hN : 3 / 4 + 2 * ε ≤ 2 * n * ε)
    (hrow : ∀ i, ∑ j, bval (β i j) = ∑ j, fr M i j)
    (hcol : ∀ j, ∑ i, bval (β i j) = ∑ i, fr M i j)
    (hR : ∀ i, (3 / 4 - ε) * n < ∑ j, eta M β i j)
    (hC : ∀ j, (3 / 4 - ε) * n < ∑ i, eta M β i j) :
    IsRegular (deg n) (graphOf M β) ∧ CanHost (deg n) (graphOf M β) (κ • M) := by
  rw [mem_doublyStochastic_iff_sum] at hM
  obtain ⟨h0, hr, hc⟩ := hM
  refine ⟨⟨graphOf_row β hn hr hrow, graphOf_col β hn hc hcol⟩, ?_⟩
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  set Z : ℝ := (1 / 2 - 2 * ε) * n with hZ
  have hZpos : 0 < Z := by rw [hZ]; apply mul_pos <;> linarith
  have hζ : ∀ i j, Z ≤ zeta M β i j := zeta_ge β hn h0 hR hC
  have hζpos : ∀ i j, 0 < zeta M β i j := fun i j => hZpos.trans_le (hζ i j)
  set s : ℝ := (2 * n - 1) * κ - (n - 1) with hsdef
  have hs0 : 0 ≤ s := by rw [hsdef]; linarith
  have h2s : 2 * s ≤ Z := by rw [hsdef, hZ, hκ]; nlinarith
  -- the flow
  let σ : Fin n → Fin n → ℝ := fun i j => s * M i j
  let d2 : Fin n × Fin n × Fin n → ℝ := fun q =>
    σ q.1 q.2.2 * min (eta M β q.1 q.2.1) (eta M β q.2.1 q.2.2) / zeta M β q.1 q.2.2
  let P : (Fin n × Fin n) ⊕ (Fin n × Fin n × Fin n) → Path n :=
    Sum.elim (fun p => Path.arc p.1 p.2) (fun q => Path.two q.1 q.2.1 q.2.2)
  let d : (Fin n × Fin n) ⊕ (Fin n × Fin n × Fin n) → ℝ :=
    Sum.elim (fun p => bb M p.1 p.2) d2
  have hd2 : ∀ q, 0 ≤ d2 q := fun q => div_nonneg
    (mul_nonneg (mul_nonneg hs0 (h0 _ _)) (le_min (eta_nonneg β hn h0 _ _) (eta_nonneg β hn h0 _ _)))
    (hζpos _ _).le
  refine ⟨_, inferInstance, P, d, ⟨fun k => ?_, fun u v => ?_, fun u v => ?_⟩⟩
  · cases k with
    | inl p => exact bb_nonneg hn h0 _ _
    | inr q => exact hd2 q
  · -- demand
    have e : served P d u v = ∑ p : Fin n × Fin n, (if p.1 = u ∧ p.2 = v then bb M p.1 p.2 else 0)
        + ∑ q : Fin n × Fin n × Fin n, (if q.1 = u ∧ q.2.2 = v then d2 q else 0) := by
      unfold served; rw [Fintype.sum_sum_type]; rfl
    rw [e]
    simp only [Fintype.sum_prod_type, ite_and]
    simp only [sum_ite_eq', mem_univ, ite_true, sum_ite_irrel, sum_const_zero]
    have hz := (hζpos u v).ne'
    have : ∑ h, d2 (u, h, v) = σ u v := by
      simp only [d2]
      rw [← sum_div, ← mul_sum]
      change σ u v * zeta M β u v / zeta M β u v = σ u v
      field_simp
    rw [this]
    simp only [σ, bb, Matrix.smul_apply, smul_eq_mul, deg_cast hn, hsdef]
    ring
  · -- capacity
    have e : load P d u v = bb M u v + (∑ j, d2 (u, v, j) + ∑ i, d2 (i, u, v)) := by
      unfold load
      rw [Fintype.sum_sum_type]
      simp only [P, d, Sum.elim_inl, Sum.elim_inr, count_arc, count_two, mul_add,
        sum_add_distrib, Fintype.sum_prod_type, ite_and, mul_ite, mul_one, mul_zero]
      simp only [sum_ite_eq', mem_univ, ite_true, sum_ite_irrel, sum_const_zero]
      congr 2
      rw [sum_comm]
      simp only [sum_ite_eq', mem_univ, ite_true]
    rw [e]
    refine le_trans ?_ (bb_add_eta_le β u v)
    gcongr
    have hη := eta_nonneg β hn h0
    have b1 : ∑ j, d2 (u, v, j) ≤ eta M β u v / Z * s := by
      calc ∑ j, d2 (u, v, j) ≤ ∑ j, eta M β u v / Z * σ u j := by
            refine sum_le_sum fun j _ => ?_
            simp only [d2]
            rw [div_mul_eq_mul_div, div_le_div_iff₀ (hζpos _ _) hZpos]
            have := hζ u j
            have hσ : 0 ≤ σ u j := mul_nonneg hs0 (h0 _ _)
            have hm := min_le_left (eta M β u v) (eta M β v j)
            have hm0 := le_min (hη u v) (hη v j)
            calc σ u j * min (eta M β u v) (eta M β v j) * Z ≤ σ u j * eta M β u v * Z := by
                  gcongr
              _ ≤ σ u j * eta M β u v * zeta M β u j := by
                  apply mul_le_mul_of_nonneg_left this (mul_nonneg hσ (hη u v))
              _ = _ := by ring
        _ = eta M β u v / Z * s := by simp only [σ, ← mul_sum, hr u]; ring
    have b2 : ∑ i, d2 (i, u, v) ≤ eta M β u v / Z * s := by
      calc ∑ i, d2 (i, u, v) ≤ ∑ i, eta M β u v / Z * σ i v := by
            refine sum_le_sum fun i _ => ?_
            simp only [d2]
            rw [div_mul_eq_mul_div, div_le_div_iff₀ (hζpos _ _) hZpos]
            have := hζ i v
            have hσ : 0 ≤ σ i v := mul_nonneg hs0 (h0 _ _)
            have hm := min_le_right (eta M β i u) (eta M β u v)
            calc σ i v * min (eta M β i u) (eta M β u v) * Z ≤ σ i v * eta M β u v * Z := by
                  gcongr
              _ ≤ σ i v * eta M β u v * zeta M β i v := by
                  apply mul_le_mul_of_nonneg_left this (mul_nonneg hσ (hη u v))
              _ = _ := by ring
        _ = eta M β u v / Z * s := by simp only [σ, ← mul_sum, hc v]; ring
    have b3 : eta M β u v / Z * s + eta M β u v / Z * s ≤ eta M β u v := by
      have : eta M β u v / Z * s + eta M β u v / Z * s = eta M β u v * (2 * s / Z) := by ring
      rw [this]
      exact mul_le_of_le_one_right (hη u v) ((div_le_one hZpos).2 h2s)
    linarith

end Flow

/-! ### Theorem 5 -/

/-- The integer-sum condition of Theorem 3 for the fractional parts `b'`. -/
lemma fr_row_int {n : ℕ} {M : Matrix (Fin n) (Fin n) ℝ} (hr : ∀ i, ∑ j, M i j = 1) (i : Fin n) :
    ∃ z : ℤ, ∑ j, fr M i j = z := by
  refine ⟨(n : ℤ) - 1 - ∑ j, (fl M i j : ℤ), ?_⟩
  push_cast
  simp only [fr, sum_sub_distrib, bb, ← mul_sum, hr i, mul_one]

lemma fr_col_int {n : ℕ} {M : Matrix (Fin n) (Fin n) ℝ} (hc : ∀ j, ∑ i, M i j = 1) (j : Fin n) :
    ∃ z : ℤ, ∑ i, fr M i j = z := by
  refine ⟨(n : ℤ) - 1 - ∑ i, (fl M i j : ℤ), ?_⟩
  push_cast
  simp only [fr, sum_sub_distrib, bb, ← mul_sum, hc j, mul_one]

/-- The size conditions on `n` used in the proof of Theorem 5 hold for all large `n`. -/
lemma eventually_large {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N, 1 ≤ n ∧ 3 / 4 + 2 * ε ≤ 2 * n * ε ∧
      2 * n * Real.exp (-(2 * n * ε ^ 2 / 3)) < 1 := by
  have hT := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 (2 * ε ^ 2 / 3)
    (by positivity)).comp tendsto_natCast_atTop_atTop
  have h3 := hT.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  have h2 := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop
    ((3 / 4 + 2 * ε) / (2 * ε))
  have h1 := Filter.eventually_ge_atTop (1 : ℕ)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (h1.and (h2.and h3))
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨a, b, c⟩ := hN n hn
  refine ⟨a, ?_, ?_⟩
  · rw [div_le_iff₀ (by positivity)] at b; linarith
  · simp only [Function.comp, Real.rpow_one] at c
    have : Real.exp (-(2 * ε ^ 2 / 3) * n) = Real.exp (-(2 * n * ε ^ 2 / 3)) := by
      congr 1; ring
    rw [this] at c
    linarith

/-- **Theorem 5** of the paper, from the dependent-rounding theorem (Theorem 3) of Gandhi et
al. as a hypothesis (Theorem 4 is `negCorrChernoff`; Theorem 3 is proved in
`DependentRounding.lean`, and the unconditional statement is `theorem_5` in `Main.lean`). For each `κ < 5/8` there is `n_κ` such that for
all `n ≥ n_κ` and every doubly stochastic `n × n` matrix `M`, `(M, κ)` is a yes-instance of
Demand-Aware Throughput. -/
theorem theorem_5_of_rounding (hDR : ∀ n, DependentRounding n) {κ : ℝ} (hκ : κ < 5 / 8) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ M : Matrix (Fin n) (Fin n) ℝ, M ∈ doublyStochastic ℝ (Fin n) →
      DAThroughput M κ := by
  set ε := 5 / 8 - κ with hεdef
  have hε0 : 0 < ε := by rw [hεdef]; linarith
  obtain ⟨N, hN⟩ := eventually_large hε0
  refine ⟨N, fun n hn M hM => ?_⟩
  obtain ⟨hn1, hnε, hexp⟩ := hN n hn
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have h2n : (0 : ℝ) < 2 * n - 1 := by linarith
  by_cases hle : κ ≤ n / (2 * n - 1)
  · exact observation_3 hn1 hle hM
  push Not at hle
  have hhalf : 1 / 2 < (n : ℝ) / (2 * n - 1) := by
    rw [lt_div_iff₀ h2n]; linarith
  have hε1 : ε < 1 / 4 := by rw [hεdef]; linarith
  have hs : (n : ℝ) - 1 ≤ (2 * n - 1) * κ := by
    have := (div_lt_iff₀ h2n).1 hle
    linarith
  have hM' := hM
  rw [mem_doublyStochastic_iff_sum] at hM'
  obtain ⟨h0, hr, hc⟩ := hM'
  have hx : ∀ i j, 0 ≤ fr M i j ∧ fr M i j ≤ 1 :=
    fun i j => ⟨fr_nonneg hn1 h0 i j, (fr_lt_one i j).le⟩
  obtain ⟨μ, hmarg, hsum, hrowneg, hcolneg⟩ :=
    hDR n (fr M) hx (fr_row_int hr) (fr_col_int hc)
  -- the bad events and the union bound
  let B : (Fin n → Fin n → Bool) → Prop := fun ω =>
    (∃ i, ∑ j, eta M ω i j ≤ (3 / 4 - ε) * n) ∨ (∃ j, ∑ i, eta M ω i j ≤ (3 / 4 - ε) * n)
  have hrowb : ∀ i, μ.prob (fun ω => ∑ j, eta M ω i j ≤ (3 / 4 - ε) * n) ≤
      Real.exp (-(2 * n * ε ^ 2 / 3)) := fun i =>
    line_bad_prob_le μ (fun j ω => ω i j) (fun j => fr M i j) (hx i) (hmarg i) (hrowneg i)
      hε0.le (by linarith)
  have hcolb : ∀ j, μ.prob (fun ω => ∑ i, eta M ω i j ≤ (3 / 4 - ε) * n) ≤
      Real.exp (-(2 * n * ε ^ 2 / 3)) := fun j =>
    line_bad_prob_le μ (fun i ω => ω i j) (fun i => fr M i j) (fun i => hx i j)
      (fun i => hmarg i j) (hcolneg j) hε0.le (by linarith)
  have hB : μ.prob B < 1 := by
    calc μ.prob B ≤ μ.prob (fun ω => ∃ i, ∑ j, eta M ω i j ≤ (3 / 4 - ε) * n) +
          μ.prob (fun ω => ∃ j, ∑ i, eta M ω i j ≤ (3 / 4 - ε) * n) := μ.prob_or_le _ _
      _ ≤ ∑ i : Fin n, μ.prob (fun ω => ∑ j, eta M ω i j ≤ (3 / 4 - ε) * n) +
          ∑ j : Fin n, μ.prob (fun ω => ∑ i, eta M ω i j ≤ (3 / 4 - ε) * n) :=
        add_le_add (μ.prob_exists_le _) (μ.prob_exists_le _)
      _ ≤ ∑ _i : Fin n, Real.exp (-(2 * n * ε ^ 2 / 3)) +
          ∑ _j : Fin n, Real.exp (-(2 * n * ε ^ 2 / 3)) :=
        add_le_add (sum_le_sum fun i _ => hrowb i) (sum_le_sum fun j _ => hcolb j)
      _ = 2 * n * Real.exp (-(2 * n * ε ^ 2 / 3)) := by simp; ring
      _ < 1 := hexp
  obtain ⟨β, hβw, hβB⟩ := μ.exists_not_of_prob_lt_one hB
  obtain ⟨hrow, hcol⟩ := hsum β hβw
  simp only [B, not_or, not_exists, not_le] at hβB
  obtain ⟨hR, hC⟩ := hβB
  obtain ⟨hreg, hhost⟩ := canHost_of_good β hn1 hM (by rw [hεdef]; ring) hε0 hε1 hs hnε
    hrow hcol hR hC
  exact ⟨graphOf M β, hreg, κ, le_rfl, hhost⟩

end Podc.DemandAwareThroughput
