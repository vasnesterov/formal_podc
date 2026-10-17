import Papers.PODC2025.MinimalistLE.PairChain
import Podc.Probability.CoinField

/-!
# The pair chain leaves the strip `|Δ| ≤ D` within `O(D²)` steps with probability `≥ 1/2`

The pair chain is started at time `t` from `y₀` and driven by the coins `ω (t+j, u)`, `ω (t+j, v)`.
`Alive j` = `|Δ_i| ≤ D` for all `i ≤ j`. With `S_j = Σ_y P(Alive j, Y_j = y)·g(y)` (`g = lyap`),
the drift identity gives `S_{j+1} ≤ S_j − P(Alive j)`, hence `T·P(Alive T) ≤ g(y₀) ≤ G_max`
(`alive_bound`). This replaces the anti-concentration argument (Lemmas 14, 15, Theorem 13 /
Berry–Esseen) of the paper.
-/

set_option linter.unusedSectionVars false

open MeasureTheory unitInterval Cslib.Probability

namespace MinimalistLE

variable {V : Type*} [DecidableEq V]

/-- The pair chain started at time `t` from `y₀`. -/
def pchain (t : ℕ) (u v : V) (y0 : PS) (ω : ℕ × V → Bool) : ℕ → PS
  | 0 => y0
  | j + 1 => pstep (pchain t u v y0 ω j) (ω (t + j, u)) (ω (t + j, v))

variable (t : ℕ) (u v : V) (y0 : PS) (D : ℕ)

/-- The chain stayed in the strip `|Δ| ≤ D` during steps `0..j`. -/
def Alive (j : ℕ) : Set (ℕ × V → Bool) :=
  {ω | ∀ i ≤ j, |(pchain t u v y0 ω i).2.2| ≤ D}

/-- Alive at step `j` and in state `y`. -/
def AliveAt (j : ℕ) (y : PS) : Set (ℕ × V → Bool) :=
  Alive t u v y0 D j ∩ {ω | pchain t u v y0 ω j = y}

/-- The coins used in steps `0..j-1`. -/
def wc (j : ℕ) : Finset (ℕ × V) :=
  (Finset.range j).image (fun i => (t + i, u)) ∪ (Finset.range j).image (fun i => (t + i, v))

/-- The strip. -/
def Ys : Finset PS := Finset.univ ×ˢ Finset.univ ×ˢ Finset.Icc (-(D : ℤ)) D

variable {t u v y0 D}

theorem mem_Ys {y : PS} : y ∈ Ys D ↔ |y.2.2| ≤ D := by
  simp [Ys, abs_le]

theorem wc_mono {j k : ℕ} (h : j ≤ k) : wc t u v j ⊆ wc t u v k := by
  intro i hi
  simp only [wc, Finset.mem_union, Finset.mem_image, Finset.mem_range] at hi ⊢
  rcases hi with ⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩
  · exact Or.inl ⟨a, by omega, rfl⟩
  · exact Or.inr ⟨a, by omega, rfl⟩

theorem coin_mem_wc_u {i j : ℕ} (h : i < j) : (t + i, u) ∈ wc t u v j :=
  Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_range.2 h))

theorem coin_mem_wc_v {i j : ℕ} (h : i < j) : (t + i, v) ∈ wc t u v j :=
  Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_range.2 h))

theorem pchain_congr {ω ω' : ℕ × V → Bool} {j : ℕ} (h : ∀ i ∈ wc t u v j, ω i = ω' i) :
    ∀ i ≤ j, pchain t u v y0 ω i = pchain t u v y0 ω' i := by
  intro i hi
  induction i with
  | zero => rfl
  | succ i ih =>
    simp only [pchain]
    rw [ih (by omega), h (t + i, u) (coin_mem_wc_u (by omega)),
      h (t + i, v) (coin_mem_wc_v (by omega))]

theorem determined_alive (j : ℕ) : Determined (Alive t u v y0 D j) (wc t u v j) :=
  fun ω ω' h => by
    simp only [Alive, Set.mem_ofPred_eq]
    exact forall₂_congr fun i hi => by rw [pchain_congr h i hi]

theorem determined_pchain (j : ℕ) (y : PS) :
    Determined {ω | pchain t u v y0 ω j = y} (wc t u v j) :=
  fun ω ω' h => by simp only [Set.mem_ofPred_eq, pchain_congr h j le_rfl]

theorem determined_aliveAt (j : ℕ) (y : PS) : Determined (AliveAt t u v y0 D j y) (wc t u v j) := by
  simpa [AliveAt] using (determined_alive (t := t) (u := u) (v := v) (y0 := y0) (D := D) j).inter
    (determined_pchain (t := t) (u := u) (v := v) (y0 := y0) j y)

variable (t u v) in
/-- The coins of step `j`. -/
def stepCoins (j : ℕ) (bu bv : Bool) : Set (ℕ × V → Bool) :=
  {ω | ω (t + j, u) = bu} ∩ {ω | ω (t + j, v) = bv}

theorem determined_stepCoins (j : ℕ) (bu bv : Bool) :
    Determined (stepCoins t u v j bu bv) (({(t + j, u)} : Finset (ℕ × V)) ∪ {(t + j, v)}) :=
  (determined_coord _ _).inter (determined_coord _ _)

theorem disjoint_wc (j : ℕ) :
    Disjoint (wc t u v j) (({(t + j, u)} : Finset (ℕ × V)) ∪ {(t + j, v)}) := by
  rw [Finset.disjoint_left]
  intro i hi hi'
  simp only [wc, Finset.mem_union, Finset.mem_image, Finset.mem_range, Finset.mem_singleton] at hi hi'
  rcases hi with ⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩ <;> rcases hi' with h | h <;>
    simp only [Prod.mk.injEq] at h <;> omega

theorem coinMeasure_stepCoins (p : I) (huv : u ≠ v) (j : ℕ) (bu bv : Bool) :
    (coinMeasure p).real (stepCoins t u v j bu bv) = wt p bu * wt p bv := by
  rw [stepCoins, coinMeasure_real_inter p (determined_coord _ _) (determined_coord _ _),
    coinMeasure_real_coord, coinMeasure_real_coord]
  · simp [wt]
  · simp [huv]

theorem aliveAt_stepCoins (p : I) (huv : u ≠ v) (j : ℕ) (y : PS) (bu bv : Bool) :
    (coinMeasure p).real (AliveAt t u v y0 D j y ∩ stepCoins t u v j bu bv) =
      (coinMeasure p).real (AliveAt t u v y0 D j y) * (wt p bu * wt p bv) := by
  rw [coinMeasure_real_inter p (determined_aliveAt j y) (determined_stepCoins j bu bv) (disjoint_wc j),
    coinMeasure_stepCoins p huv]

theorem alive_succ {ω : ℕ × V → Bool} {j : ℕ} :
    ω ∈ Alive t u v y0 D (j + 1) ↔ ω ∈ Alive t u v y0 D j ∧
      |(pchain t u v y0 ω (j + 1)).2.2| ≤ D := by
  simp only [Alive, Set.mem_ofPred_eq]
  constructor
  · intro h; exact ⟨fun i hi => h i (by omega), h _ le_rfl⟩
  · rintro ⟨h1, h2⟩ i hi
    rcases Nat.lt_or_ge i (j + 1) with h | h
    · exact h1 i (by omega)
    · rwa [show i = j + 1 by omega]

theorem pchain_mem_Ys {ω : ℕ × V → Bool} {j : ℕ} (h : ω ∈ Alive t u v y0 D j) :
    pchain t u v y0 ω j ∈ Ys D := mem_Ys.2 (h j le_rfl)

/-- Probability of being alive at `j` is the sum over the strip. -/
theorem alive_eq_sum (p : I) (j : ℕ) :
    (coinMeasure p).real (Alive t u v y0 D j) =
      ∑ y ∈ Ys D, (coinMeasure p).real (AliveAt t u v y0 D j y) :=
  coinMeasure_real_partition p (determined_alive j) _ (determined_pchain j) _ fun _ h => pchain_mem_Ys h

/-- One step of the chain (Chapman–Kolmogorov), for a target `y'` in the strip. -/
theorem aliveAt_succ (p : I) (huv : u ≠ v) (j : ℕ) (y' : PS) (hy' : y' ∈ Ys D) :
    (coinMeasure p).real (AliveAt t u v y0 D (j + 1) y') =
      ∑ y ∈ Ys D, ∑ bu : Bool, ∑ bv : Bool, if pstep y bu bv = y' then
        (coinMeasure p).real (AliveAt t u v y0 D j y) * (wt p bu * wt p bv) else 0 := by
  classical
  let F : (ℕ × V → Bool) → PS × Bool × Bool := fun ω =>
    (pchain t u v y0 ω j, ω (t + j, u), ω (t + j, v))
  have hF : ∀ z, Determined {ω | F ω = z} (wc t u v (j + 1)) := by
    intro z ω ω' h
    simp only [Set.mem_ofPred_eq, F]
    rw [pchain_congr (fun i hi => h i (wc_mono (Nat.le_succ j) hi)) j le_rfl,
      h _ (coin_mem_wc_u (Nat.lt_succ_self j)), h _ (coin_mem_wc_v (Nat.lt_succ_self j))]
  have hA : Determined (AliveAt t u v y0 D (j + 1) y') (wc t u v (j + 1)) := determined_aliveAt _ _
  rw [coinMeasure_real_partition p hA F hF (Ys D ×ˢ (Finset.univ ×ˢ Finset.univ))]
  · rw [Finset.sum_product]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [Finset.sum_product]
    refine Finset.sum_congr rfl fun bu _ => Finset.sum_congr rfl fun bv _ => ?_
    split_ifs with hst
    · rw [← aliveAt_stepCoins p huv]
      congr 1
      ext ω
      simp only [AliveAt, stepCoins, F, Set.mem_inter_iff, Set.mem_ofPred_eq, Prod.mk.injEq]
      constructor
      · rintro ⟨⟨h1, -⟩, h2, h3, h4⟩
        exact ⟨⟨(alive_succ.1 h1).1, h2⟩, h3, h4⟩
      · rintro ⟨⟨h1, h2⟩, h3, h4⟩
        have hstep : pchain t u v y0 ω (j + 1) = y' := by
          simp only [pchain]; rw [h2, h3, h4, hst]
        exact ⟨⟨alive_succ.2 ⟨h1, by rw [hstep]; exact mem_Ys.1 hy'⟩, hstep⟩, h2, h3, h4⟩
    · convert measureReal_empty (μ := coinMeasure p)
      ext ω
      simp only [AliveAt, F, Set.mem_inter_iff, Set.mem_ofPred_eq, Prod.mk.injEq,
        Set.mem_empty_iff_false, iff_false, not_and]
      rintro ⟨-, h2⟩ h3 h4 h5
      apply hst
      rw [← h2]; simp only [pchain]; rw [h3, h4, h5]
  · rintro ω ⟨h1, -⟩
    simp only [F, Finset.mem_product, Finset.mem_univ, and_true]
    exact pchain_mem_Ys (alive_succ.1 h1).1

/-- The Lyapunov sum `S_j`. -/
noncomputable def lsum (p : I) (j : ℕ) : ℝ :=
  ∑ y ∈ Ys D, (coinMeasure p).real (AliveAt t u v y0 D j y) * lyap p D y

theorem lsum_succ (p : I) (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) (huv : u ≠ v) (j : ℕ) :
    lsum (t := t) (u := u) (v := v) (y0 := y0) (D := D) p (j + 1) ≤
      lsum (t := t) (u := u) (v := v) (y0 := y0) (D := D) p j -
        (coinMeasure p).real (Alive t u v y0 D j) := by
  classical
  set P := fun y => (coinMeasure p).real (AliveAt t u v y0 D j y)
  have hw : ∀ b, 0 ≤ wt p b := fun b => by cases b <;> simp [wt] <;> linarith
  calc lsum p (j + 1)
      = ∑ y' ∈ Ys D, (∑ y ∈ Ys D, ∑ bu : Bool, ∑ bv : Bool,
          if pstep y bu bv = y' then P y * (wt p bu * wt p bv) else 0) * lyap p D y' := by
        unfold lsum
        exact Finset.sum_congr rfl fun y' hy' => by rw [aliveAt_succ p huv j y' hy']
    _ = ∑ y ∈ Ys D, ∑ bu : Bool, ∑ bv : Bool, P y * (wt p bu * wt p bv) *
          (if pstep y bu bv ∈ Ys D then lyap p D (pstep y bu bv) else 0) := by
        simp_rw [Finset.sum_mul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun bu _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun bv _ => ?_
        simp_rw [ite_mul, zero_mul]
        rw [Finset.sum_ite_eq]
        split_ifs <;> simp
    _ ≤ ∑ y ∈ Ys D, ∑ bu : Bool, ∑ bv : Bool, P y * (wt p bu * wt p bv) *
          lyap p D (pstep y bu bv) := by
        refine Finset.sum_le_sum fun y hy => Finset.sum_le_sum fun bu _ =>
          Finset.sum_le_sum fun bv _ => ?_
        have hP : 0 ≤ P y := measureReal_nonneg
        split_ifs
        · exact le_rfl
        · rw [mul_zero]
          apply mul_nonneg (mul_nonneg hP (mul_nonneg (hw _) (hw _)))
          apply lyap_nonneg hp0 hp1
          have := mem_Ys.1 hy
          obtain ⟨xu, xv, δ⟩ := y
          simp only [pstep, ind] at this ⊢
          rw [abs_le] at this ⊢
          constructor <;> split_ifs <;> omega
    _ = ∑ y ∈ Ys D, P y * (lyap p D y - 1) := by
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [← lyap_drift hp0 hp1 D y, Finset.mul_sum]
        refine Finset.sum_congr rfl fun bu _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun bv _ => ?_
        ring
    _ = _ := by
        rw [alive_eq_sum p j]
        simp only [lsum, P, mul_sub, mul_one, Finset.sum_sub_distrib]

theorem lsum_nonneg (p : I) (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) (j : ℕ) :
    0 ≤ lsum (t := t) (u := u) (v := v) (y0 := y0) (D := D) p j :=
  Finset.sum_nonneg fun y hy => mul_nonneg measureReal_nonneg
    (lyap_nonneg hp0 hp1 D y (by have := mem_Ys.1 hy; omega))

theorem lsum_zero (p : I) (hy0 : |y0.2.2| ≤ D) :
    lsum (t := t) (u := u) (v := v) (y0 := y0) (D := D) p 0 = lyap p D y0 := by
  classical
  unfold lsum
  rw [Finset.sum_eq_single y0]
  · have : AliveAt t u v y0 D 0 y0 = Set.univ := by
      ext ω; simp [AliveAt, Alive, pchain, hy0]
    simp [this]
  · intro y _ hy
    have : AliveAt t u v y0 D 0 y = ∅ := by
      ext ω; simp [AliveAt, pchain, Ne.symm hy]
    simp [this]
  · intro h; exact absurd (mem_Ys.2 hy0) h

theorem alive_anti {i j : ℕ} (h : i ≤ j) : Alive t u v y0 D j ⊆ Alive t u v y0 D i :=
  fun _ hω k hk => hω k (by omega)

/-- **Exit bound.** `T·P(Alive T) ≤ g(y₀)` for a start in the strip. -/
theorem alive_bound (p : I) (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) (huv : u ≠ v)
    (hy0 : |y0.2.2| ≤ D) (T : ℕ) :
    T * (coinMeasure p).real (Alive t u v y0 D T) ≤ lyap p D y0 := by
  have hsum : ∀ k, ∑ j ∈ Finset.range k, (coinMeasure p).real (Alive t u v y0 D j) ≤
      lyap p D y0 - lsum (t := t) (u := u) (v := v) (y0 := y0) (D := D) p k := by
    intro k
    induction k with
    | zero => simp [lsum_zero p hy0]
    | succ k ih =>
      rw [Finset.sum_range_succ]
      have := lsum_succ (t := t) (u := u) (v := v) (y0 := y0) (D := D) p hp0 hp1 huv k
      linarith
  have h1 := hsum T
  have h2 := lsum_nonneg (t := t) (u := u) (v := v) (y0 := y0) (D := D) p hp0 hp1 T
  have h3 : ∑ j ∈ Finset.range T, (coinMeasure p).real (Alive t u v y0 D T) ≤
      ∑ j ∈ Finset.range T, (coinMeasure p).real (Alive t u v y0 D j) :=
    Finset.sum_le_sum fun j hj =>
      measureReal_mono (alive_anti (by simp at hj; omega))
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h3
  linarith

end MinimalistLE
