import Papers.PODC2026.OrderStatisticsPP.Instances

/-!
# The rank-ancestry process (Lemmas 4.2, 4.3, 4.4)

`IsOrderStat s i x` says that `x` is the `i`-th smallest opinion `X_(i)` of `s` (with
multiplicity): fewer than `i` agents hold an opinion `< x` and at least `i` hold an opinion `≤ x`
(`isOrderStat_existsUnique`: for `1 ≤ i ≤ n` there is exactly one such `x`).

For every Order-Based dynamics (intended reading of Definition 4.2; this covers Copy-or-Max, Biased-Median
and Self-Excluding Median by `Instances.lean`), from *every* configuration (ties allowed):
* `orderStat_step` (**Lemma 4.2**, distributional form):
  `P[X'_(i) = x] = f_i 1[X_(i-1) = x] + g_i 1[X_(i) = x] + h_i 1[X_(i+1) = x]`;
* `orderStat_ancestry` (**Lemma 4.4**): `P[X^t_(i) = x] = ∑_j (Pᵗ)_{j,i} 1[X^0_(j) = x]`, where
  `(Pᵗ)_{j,i} = ancestry f h t i j` is the `t`-step kernel of the birth–death chain on ranks
  (`i → i-1` w.p. `f_i`, `i → i+1` w.p. `h_i`); for distinct initial opinions this is
  `P[X^t_(i) = X^0_(j)] = (Pᵗ)_{j,i}`;
* `orderStat_expectation` (**Lemma 4.3**): `E[v(X^t_(i))] = ∑_j (Pᵗ)_{j,i} v(X^0_(j))` for any
  real valuation `v` of the opinions.
-/

set_option linter.unusedSectionVars false

namespace OrderStatisticsPP

open Finset Matrix Filter Topology Cslib.Probability.Markov

variable {n : ℕ} {α : Type*} [LinearOrder α] [Fintype α] {Ω : Type*} [Fintype Ω]

/-- `x` is the `i`-th smallest opinion of `s` (counted with multiplicity). -/
def IsOrderStat (s : Config n α) (i : ℕ) (x : α) : Prop :=
  cnt (Set.Iio x) s < i ∧ i ≤ cnt (Set.Iic x) s

/-- Indicator of `IsOrderStat`. -/
noncomputable def osInd (i : ℕ) (x : α) (s : Config n α) : ℝ := by
  classical exact if IsOrderStat s i x then 1 else 0

lemma cnt_congr {D E : Set α} (c : Config n α) (h : ∀ u, c u ∈ D ↔ c u ∈ E) :
    cnt D c = cnt E c :=
  Nat.card_congr (Equiv.subtypeEquivRight h)

lemma isOrderStat_existsUnique (s : Config n α) {i : ℕ} (hi1 : 1 ≤ i) (hin : i ≤ n) :
    ∃! x, IsOrderStat s i x := by
  classical
  set S := (univ.image s).filter fun y => i ≤ cnt (Set.Iic y) s
  have hne : S.Nonempty := by
    obtain ⟨u, -, hu⟩ := Finset.exists_max_image univ s ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
    refine ⟨s u, Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem _ (Finset.mem_univ _), ?_⟩⟩
    rw [(cnt_eq_n_iff _ s).mpr fun v => hu v (Finset.mem_univ v)]
    exact hin
  set x := S.min' hne
  have hxS : x ∈ S := S.min'_mem hne
  have hx : IsOrderStat s i x := by
    refine ⟨?_, (Finset.mem_filter.mp hxS).2⟩
    by_contra hge
    push Not at hge
    -- the largest opinion below `x` would be a smaller element of `S`
    have hpos : 0 < cnt (Set.Iio x) s := by omega
    obtain ⟨v, hv⟩ := (cnt_pos_iff _ s).mp hpos
    set T := univ.filter fun u => s u < x
    have hT : T.Nonempty := ⟨v, by simpa [T] using hv⟩
    obtain ⟨w, hwT, hw⟩ := Finset.exists_max_image T s hT
    have hwx : s w < x := by simpa [T] using hwT
    have hc : cnt (Set.Iic (s w)) s = cnt (Set.Iio x) s := cnt_congr s fun u => by
      simp only [Set.mem_Iic, Set.mem_Iio]
      constructor
      · intro h; exact lt_of_le_of_lt h hwx
      · intro h; exact hw u (by simpa [T] using h)
    have : s w ∈ S := Finset.mem_filter.mpr
      ⟨Finset.mem_image_of_mem _ (Finset.mem_univ _), by rw [hc]; exact hge⟩
    exact absurd (S.min'_le _ this) (not_le.mpr hwx)
  refine ⟨x, hx, fun x' ⟨h1, h2⟩ => ?_⟩
  obtain ⟨h1', h2'⟩ := hx
  rcases lt_trichotomy x' x with h | h | h
  · have := cnt_mono (Set.Iic_subset_Iio.mpr h) s; omega
  · exact h
  · have := cnt_mono (Set.Iic_subset_Iio.mpr h) s; omega

lemma g_cnt_update (g : ℕ → ℝ) (D : Set α) (c : Config n α) (u : Fin n) (y : α) :
    g (cnt D (Function.update c u y)) = g (cnt D c)
      + (1 - ind D (c u)) * ind D y * (g (cnt D c + 1) - g (cnt D c))
      - ind D (c u) * (1 - ind D y) * (g (cnt D c) - g (cnt D c - 1)) := by
  have h := cnt_update_int D c u y
  by_cases hu : c u ∈ D <;> by_cases hy : y ∈ D <;>
    simp only [hu, hy, ite_true, ite_false, ind_mem, ind_not_mem, not_false_eq_true] at h ⊢
  · have : cnt D (Function.update c u y) = cnt D c := by omega
    rw [this]; ring
  · have : cnt D (Function.update c u y) = cnt D c - 1 := by omega
    rw [this]; ring
  · have : cnt D (Function.update c u y) = cnt D c + 1 := by omega
    rw [this]; ring
  · have : cnt D (Function.update c u y) = cnt D c := by omega
    rw [this]; ring

/-- One-step expectation of `g (cnt D ·)` for single-agent update dynamics. -/
lemma randomMap_mulVec_g (μ : Ω → ℝ) (h1 : ∑ ω, μ ω = 1) (a : Ω → Config n α → Fin n)
    (y : Ω → Config n α → α) (g : ℕ → ℝ) (D : Set α) (c : Config n α) :
    (randomMap μ (fun ω c => Function.update c (a ω c) (y ω c)) *ᵥ (fun c => g (cnt D c))) c =
      g (cnt D c) + (g (cnt D c + 1) - g (cnt D c)) * upMass μ a y D c
        - (g (cnt D c) - g (cnt D c - 1)) * downMass μ a y D c := by
  rw [randomMap_mulVec]
  simp_rw [g_cnt_update]
  unfold upMass downMass
  have e : ∀ ω, μ ω * (g (cnt D c) + (1 - ind D (c (a ω c))) * ind D (y ω c) *
      (g (cnt D c + 1) - g (cnt D c)) - ind D (c (a ω c)) * (1 - ind D (y ω c)) *
        (g (cnt D c) - g (cnt D c - 1))) =
      μ ω * g (cnt D c) + (g (cnt D c + 1) - g (cnt D c)) * (μ ω * ((1 - ind D (c (a ω c))) *
        ind D (y ω c))) - (g (cnt D c) - g (cnt D c - 1)) *
          (μ ω * (ind D (c (a ω c)) * (1 - ind D (y ω c)))) := by
    intro ω; ring
  simp_rw [e, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul,
    h1, one_mul]

/-- Threshold indicator `1[i ≤ cnt D s]`. -/
noncomputable def thrInd (i : ℕ) (D : Set α) (s : Config n α) : ℝ :=
  if i ≤ cnt D s then 1 else 0

set_option linter.unnecessarySeqFocus false in
lemma osInd_eq (i : ℕ) (x : α) (s : Config n α) :
    osInd i x s = thrInd i (Set.Iic x) s - thrInd i (Set.Iio x) s := by
  have hle := cnt_mono (Set.Iio_subset_Iic_self (a := x)) s
  unfold osInd thrInd IsOrderStat
  by_cases h1 : i ≤ cnt (Set.Iio x) s <;> by_cases h2 : i ≤ cnt (Set.Iic x) s <;>
    simp [h1, h2] <;> omega

variable {μ : Ω → ℝ} {a : Ω → Config n α → Fin n} {y : Ω → Config n α → α} {f h : ℕ → ℝ}

lemma OrderBased.f_one (hO : OrderBased μ a y f h) (c : Config n α) : f 1 = 0 := by
  have := hO.up ∅ isLowerSet_empty c
  rw [(cnt_eq_zero_iff _ c).mpr fun u => Set.notMem_empty _] at this
  rw [← this]
  unfold upMass
  simp [ind_not_mem]

lemma OrderBased.h_n (hO : OrderBased μ a y f h) (c : Config n α) : h n = 0 := by
  have := hO.down Set.univ isLowerSet_univ c
  rw [(cnt_eq_n_iff _ c).mpr fun u => Set.mem_univ _] at this
  rw [← this]
  unfold downMass
  simp [ind_mem]

/-- One step of the threshold indicator. -/
lemma thrInd_step (hO : OrderBased μ a y f h) {D : Set α} (hD : IsLowerSet D) (s : Config n α)
    {i : ℕ} (hi : 1 ≤ i) :
    (randomMap μ (fun ω c => Function.update c (a ω c) (y ω c)) *ᵥ thrInd i D) s =
      f i * thrInd (i - 1) D s + (1 - f i - h i) * thrInd i D s + h i * thrInd (i + 1) D s := by
  have key := randomMap_mulVec_g μ hO.sum_one a y (fun k => if i ≤ k then (1 : ℝ) else 0) D s
  have e : thrInd i D = fun c : Config n α => if i ≤ cnt D c then (1 : ℝ) else 0 := rfl
  rw [e, key, hO.up D hD s, hO.down D hD s]
  simp only [thrInd]
  generalize cnt D s = m
  rcases (show i = m + 1 ∨ i = m ∨ i + 1 ≤ m ∨ m + 2 ≤ i by omega) with h1 | h1 | h1 | h1
  · subst h1
    simp only [show ¬ m + 1 ≤ m by omega, le_refl, show ¬ m + 1 ≤ m - 1 by omega,
      show m + 1 - 1 ≤ m by omega, show ¬ m + 1 + 1 ≤ m by omega, ite_true, ite_false]
    ring
  · subst h1
    simp only [le_refl, show ¬ i ≤ i - 1 by omega, show i ≤ i + 1 by omega,
      show i - 1 ≤ i by omega, show ¬ i + 1 ≤ i by omega, ite_true, ite_false]
    ring
  · simp only [show i ≤ m by omega, show i ≤ m + 1 by omega, show i ≤ m - 1 by omega,
      show i - 1 ≤ m by omega, h1, ite_true]
    ring
  · simp only [show ¬ i ≤ m by omega, show ¬ i ≤ m + 1 by omega, show ¬ i ≤ m - 1 by omega,
      show ¬ i - 1 ≤ m by omega, show ¬ i + 1 ≤ m by omega, ite_false]
    ring

/-- **Lemma 4.2** (distributional form, all configurations): after one step, the `i`-th order
statistic equals `x` with probability
`f_i 1[X_(i-1) = x] + g_i 1[X_(i) = x] + h_i 1[X_(i+1) = x]`, `g_i = 1 - f_i - h_i`. -/
theorem orderStat_step (hO : OrderBased μ a y f h) (s : Config n α) {i : ℕ} (hi : 1 ≤ i)
    (x : α) :
    (randomMap μ (fun ω c => Function.update c (a ω c) (y ω c)) *ᵥ osInd i x) s =
      f i * osInd (i - 1) x s + (1 - f i - h i) * osInd i x s + h i * osInd (i + 1) x s := by
  have e : ∀ k, (osInd k x : Config n α → ℝ) = thrInd k (Set.Iic x) - thrInd k (Set.Iio x) :=
    fun k => funext fun s => osInd_eq k x s
  rw [e, Matrix.mulVec_sub, Pi.sub_apply, thrInd_step hO (isLowerSet_Iic x) s hi,
    thrInd_step hO (isLowerSet_Iio x) s hi]
  simp only [e, Pi.sub_apply]
  ring

/-- `t`-step kernel of the rank chain (`(Pᵗ)_{j,i}` in the paper): from rank `i`, move to `i-1`
w.p. `f_i`, to `i+1` w.p. `h_i`, stay otherwise. -/
noncomputable def ancestry (f h : ℕ → ℝ) : ℕ → ℕ → ℕ → ℝ
  | 0, i, j => if i = j then 1 else 0
  | t + 1, i, j => f i * ancestry f h t (i - 1) j + (1 - f i - h i) * ancestry f h t i j +
      h i * ancestry f h t (i + 1) j

/-- **Lemma 4.4** (with ties): `P[X^t_(i) = x] = ∑_{j=1}^{n} (Pᵗ)_{j,i} 1[X^0_(j) = x]`. -/
theorem orderStat_ancestry (hO : OrderBased μ a y f h) (c : Config n α) (x : α) (t : ℕ) :
    ∀ i, 1 ≤ i → i ≤ n →
      ((randomMap μ (fun ω c => Function.update c (a ω c) (y ω c))) ^ t *ᵥ osInd i x) c =
        ∑ j ∈ Icc 1 n, ancestry f h t i j * osInd j x c := by
  set T := randomMap μ (fun ω c => Function.update c (a ω c) (y ω c))
  induction t with
  | zero =>
    intro i hi1 hin
    simp only [pow_zero, Matrix.one_mulVec, ancestry]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj; simp [Ne.symm hj]
    · intro hi; exact absurd (Finset.mem_Icc.mpr ⟨hi1, hin⟩) hi
  | succ t ih =>
    intro i hi1 hin
    rw [pow_succ, ← Matrix.mulVec_mulVec]
    have hstep : T *ᵥ osInd i x = f i • osInd (i - 1) x + (1 - f i - h i) • osInd i x +
        h i • osInd (i + 1) x := by
      funext s; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      exact orderStat_step hO s hi1 x
    rw [hstep, Matrix.mulVec_add, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul,
      Matrix.mulVec_smul]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have hlo : f i * (T ^ t *ᵥ osInd (i - 1) x) c =
        f i * ∑ j ∈ Icc 1 n, ancestry f h t (i - 1) j * osInd j x c := by
      by_cases h1 : i = 1
      · subst h1; rw [hO.f_one c]; ring
      · rw [ih (i - 1) (by omega) (by omega)]
    have hhi : h i * (T ^ t *ᵥ osInd (i + 1) x) c =
        h i * ∑ j ∈ Icc 1 n, ancestry f h t (i + 1) j * osInd j x c := by
      by_cases h1 : i = n
      · subst h1; rw [hO.h_n c]; ring
      · rw [ih (i + 1) (by omega) (by omega)]
    rw [hlo, hhi, ih i hi1 hin]
    simp only [ancestry, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring

/-- **Lemma 4.4** (distinct initial opinions): `P[X^t_(i) = X^0_(j)] = (Pᵗ)_{j,i}`. -/
theorem orderStat_ancestry_injective (hO : OrderBased μ a y f h) (c : Config n α)
    (hc : Function.Injective c) (u : Fin n) (t : ℕ) {i : ℕ} (hi1 : 1 ≤ i) (hin : i ≤ n) :
    ((randomMap μ (fun ω c => Function.update c (a ω c) (y ω c))) ^ t *ᵥ osInd i (c u)) c =
      ancestry f h t i (rank c (c u)) := by
  rw [orderStat_ancestry hO c (c u) t i hi1 hin]
  have hr := cnt_Iic_injective hc u
  have hrn : rank c (c u) ≤ n := cnt_le _ c
  rw [Finset.sum_eq_single (rank c (c u))]
  · simp [osInd, IsOrderStat, rank, hr]
  · intro j _ hj
    have : ¬ IsOrderStat c j (c u) := by
      unfold IsOrderStat rank at *; omega
    simp [osInd, this]
  · intro hne; exact absurd (Finset.mem_Icc.mpr ⟨by unfold rank; omega, hrn⟩) hne

/-- **Lemma 4.3**: expected (valuated) order statistics evolve by the rank chain:
`E[v(X^t_(i))] = ∑_j (Pᵗ)_{j,i} v(X^0_(j))`, where `v(X_(i)) = ∑_x v x 1[X_(i) = x]`. -/
theorem orderStat_expectation (hO : OrderBased μ a y f h) (c : Config n α) (v : α → ℝ) (t : ℕ)
    {i : ℕ} (hi1 : 1 ≤ i) (hin : i ≤ n) :
    ∑ x, v x * ((randomMap μ (fun ω c => Function.update c (a ω c) (y ω c))) ^ t *ᵥ
        osInd i x) c =
      ∑ j ∈ Icc 1 n, ancestry f h t i j * ∑ x, v x * osInd j x c := by
  simp_rw [orderStat_ancestry hO c _ t i hi1 hin, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun x _ => by ring

end OrderStatisticsPP
