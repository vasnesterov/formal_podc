import Papers.PODC2019.MinimalSymmetryBreaking.Field

/-!
# Product and uniform distributions; collision probability

Helpers for the step from anonymous algorithms to algorithms with identifiers (Claim 10):
independent pairs `(identifier, random value)`, the probability that i.i.d. uniform identifiers on
a finite set collide, and averaging.
-/

-- CSLib candidate
namespace Podc.MinimalSymmetryBreaking

open Finset Function
open scoped Classical

noncomputable section

variable {ι : Type*}

/-- The product of two finite distributions. -/
def FinDist.prod {A B : Type*} [Fintype A] [Fintype B] (μ₁ : FinDist A) (μ₂ : FinDist B) :
    FinDist (A × B) where
  w p := μ₁.w p.1 * μ₂.w p.2
  nonneg p := mul_nonneg (μ₁.nonneg _) (μ₂.nonneg _)
  sum_eq_one := by
    rw [Fintype.sum_prod_type]
    simp only [← mul_sum, μ₂.sum_eq_one, mul_one, μ₁.sum_eq_one]

/-- The uniform distribution on `Fin n`, `n ≥ 1`. -/
def FinDist.uniform (n : ℕ) [NeZero n] : FinDist (Fin n) where
  w _ := 1 / n
  nonneg _ := by positivity
  sum_eq_one := by
    simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    have : (n : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne n
    field_simp

/-- Expectations under a product distribution can be computed coordinatewise. -/
theorem expect_prod {A B : Type*} [Fintype A] [Fintype B] [Inhabited A] [Inhabited B]
    (μ₁ : FinDist A) (μ₂ : FinDist B) (F : Finset ι) (g : (ι → A × B) → ℝ) :
    expect (μ₁.prod μ₂) F g =
      expect μ₁ F (fun y => expect μ₂ F (fun x => g (fun i => (y i, x i)))) := by
  unfold expect wt
  let e := Equiv.arrowProdEquivProdArrow (F : Type _) (fun _ => A) (fun _ => B)
  rw [← e.symm.sum_comp, Fintype.sum_prod_type]
  refine sum_congr rfl fun y _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun x _ => ?_
  have hw : ∏ i, (μ₁.prod μ₂).w (e.symm (y, x) i) = (∏ i, μ₁.w (y i)) * ∏ i, μ₂.w (x i) := by
    rw [← prod_mul_distrib]; rfl
  have hx : ext F (e.symm (y, x)) = fun i => (ext F y i, ext F x i) := by
    funext i; by_cases hi : i ∈ F <;> simp [ext, hi, e, Equiv.arrowProdEquivProdArrow]; rfl
  rw [hw, hx]; ring

variable {Ω : Type*} [Fintype Ω] [Inhabited Ω] {μ : FinDist Ω}

/-- The probability that one coordinate takes a given value. -/
lemma prob_coord {F : Finset ι} {j : ι} (hj : j ∈ F) (c : Ω) :
    prob μ F (fun z => z j = c) = μ.w c := by
  unfold prob
  rw [expect_eq_of_subset (F₀ := {j}) (by simpa using hj) (by
    intro x x' h; simp only [ind, h j (by simp)])]
  unfold expect wt
  have hu : Unique ({j} : Finset ι) :=
    ⟨⟨⟨j, by simp⟩⟩, fun a => Subtype.ext (Finset.mem_singleton.1 a.2)⟩
  rw [← (Equiv.funUnique ({j} : Finset ι) Ω).symm.sum_comp]
  rw [Finset.sum_eq_single c]
  · simp [ext, ind, Equiv.funUnique]
  · intro b _ hb
    simp [ext, ind, Equiv.funUnique, hb]
  · simp

/-- Two distinct coordinates of an i.i.d. uniform field coincide with probability `1/n`. -/
lemma prob_coord_eq {n : ℕ} [NeZero n] {F : Finset ι} {i j : ι} (hi : i ∈ F) (hj : j ∈ F)
    (hij : i ≠ j) : prob (FinDist.uniform n) F (fun z => z i = z j) = 1 / n := by
  unfold prob
  rw [← expect_condE F {j}]
  have : ∀ x : ι → Fin n, condE (FinDist.uniform n) F {j} (ind fun z => z i = z j) x = 1 / n := by
    intro x
    rw [condE_congr (h' := ind fun z => z i = x j) (by intro z; simp [ind, Set.piecewise])]
    rw [condE_eq_of_dependsOn (T := ∅) (D := {i}) (by
        intro z z' h; unfold ind; beta_reduce; rw [h i (by simp)]) (Set.empty_subset _)
      (by simpa using hij)]
    unfold condE; simp only [Set.piecewise_empty]
    exact prob_coord hi _
  rw [show condE (FinDist.uniform n) F {j} (ind fun z => z i = z j) = fun _ => 1 / (n : ℝ) from
    funext this, expect_const]

/-- **Collision bound.** i.i.d. uniform values in `Fin n` on a finite set `R` are injective except
with probability at most `|R|² / n`. -/
theorem prob_not_injOn_le {n : ℕ} [NeZero n] (F R : Finset ι) (hRF : R ⊆ F) :
    prob (FinDist.uniform n) F (fun z => ¬ Set.InjOn z R) ≤ (R.card : ℝ) ^ 2 / n := by
  have hpt : ∀ z : ι → Fin n, ind (fun z => ¬ Set.InjOn z R) z ≤
      ∑ p ∈ (R ×ˢ R).filter (fun p => p.1 ≠ p.2), ind (fun z => z p.1 = z p.2) z := by
    intro z
    by_cases h : Set.InjOn z R
    · simp only [ind, h, not_true_eq_false, if_false]
      exact sum_nonneg fun _ _ => by split_ifs <;> norm_num
    · simp only [Set.InjOn, not_forall] at h
      obtain ⟨a, ha, b, hb, hab, hne⟩ := h
      have h1 : ind (fun z => ¬ Set.InjOn z R) z = 1 := by
        simp only [ind]; rw [if_pos]; intro hinj; exact hne (hinj ha hb hab)
      rw [h1]
      have hmem : (a, b) ∈ (R ×ˢ R).filter (fun p => p.1 ≠ p.2) := by
        simp [Finset.mem_coe.1 ha, Finset.mem_coe.1 hb, hne]
      calc (1 : ℝ) = ind (fun z => z (a, b).1 = z (a, b).2) z := by simp [ind, hab]
        _ ≤ _ := single_le_sum (f := fun p => ind (fun z => z p.1 = z p.2) z)
            (fun _ _ => ind_nonneg _ _) hmem
  calc prob (FinDist.uniform n) F (fun z => ¬ Set.InjOn z R)
      ≤ expect (FinDist.uniform n) F (fun z =>
          ∑ p ∈ (R ×ˢ R).filter (fun p => p.1 ≠ p.2), ind (fun z => z p.1 = z p.2) z) :=
        expect_mono hpt
    _ = ∑ p ∈ (R ×ˢ R).filter (fun p => p.1 ≠ p.2), (1 / n : ℝ) := by
        rw [expect_sum]
        refine sum_congr rfl fun p hp => ?_
        simp only [mem_filter, mem_product] at hp
        exact prob_coord_eq (hRF hp.1.1) (hRF hp.1.2) hp.2
    _ ≤ ∑ _p ∈ R ×ˢ R, (1 / n : ℝ) :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => by positivity)
    _ = (R.card : ℝ) ^ 2 / n := by
        rw [sum_const, card_product, nsmul_eq_mul]; push_cast; ring

/-- **Averaging.** If `Pr[good] > 0`, some outcome `y` with `good y` has `h y ≤ E[1_good · h] / Pr[good]`. -/
theorem exists_le_of_expect {F : Finset ι} {good : (ι → Ω) → Prop} {h : (ι → Ω) → ℝ}
    (hpos : 0 < prob μ F good) :
    ∃ y, good y ∧ h y * prob μ F good ≤ expect μ F (fun x => ind good x * h x) := by
  by_contra hcon
  push_neg at hcon
  -- every good configuration has a large value
  have hlt : expect μ F (fun x => ind good x * h x) * prob μ F good <
      expect μ F (fun x => ind good x * h x) * prob μ F good + 0 := by
    have : prob μ F good * expect μ F (fun x => ind good x * h x) <
        prob μ F good * expect μ F (fun x => ind good x * h x) * 1 := by
      have hsum : ∃ y : F → Ω, 0 < wt μ y ∧ good (ext F y) := by
        by_contra hno
        push_neg at hno
        have : prob μ F good = 0 := by
          unfold prob expect
          refine sum_eq_zero fun y _ => ?_
          by_cases hg : good (ext F y)
          · have := le_antisymm (hno y |> fun h => by
              by_contra hpos'; push_neg at hpos'; exact absurd hg (h hpos')) (wt_nonneg y)
            simp [this]
          · simp [ind, hg]
        linarith
      obtain ⟨y, hy, hg⟩ := hsum
      have key : prob μ F good * expect μ F (fun x => ind good x * h x) <
          expect μ F (fun x => ind good x * h x) * prob μ F good := by
        -- strictness comes from the good outcome `ext F y`
        have h1 : ∀ x, ind good x * (expect μ F (fun x => ind good x * h x)) ≤
            ind good x * (h x * prob μ F good) := by
          intro x
          by_cases hx : good x
          · simp only [ind, hx, if_true, one_mul]; exact (hcon x hx).le
          · simp [ind, hx]
        have h2 : ind good (ext F y) * (expect μ F (fun x => ind good x * h x)) <
            ind good (ext F y) * (h (ext F y) * prob μ F good) := by
          simp only [ind, hg, if_true, one_mul]; exact hcon _ hg
        have : expect μ F (fun x => ind good x * expect μ F (fun x => ind good x * h x)) <
            expect μ F (fun x => ind good x * (h x * prob μ F good)) := by
          unfold expect
          apply sum_lt_sum
          · intro z _; exact mul_le_mul_of_nonneg_left (h1 _) (wt_nonneg z)
          · exact ⟨y, mem_univ _, mul_lt_mul_of_pos_left h2 hy⟩
        rw [expect_mul_const] at this
        have e2 : expect μ F (fun x => ind good x * (h x * prob μ F good)) =
            expect μ F (fun x => ind good x * h x) * prob μ F good := by
          rw [← expect_mul_const]; congr 1; funext x; ring
        rw [e2] at this
        unfold prob at this ⊢
        linarith
      linarith
    linarith
  linarith

end

end Podc.MinimalSymmetryBreaking
