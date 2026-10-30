import Mathlib

/-!
# MultiKrum and the robustness coefficient `κ⋆` — definitions (Section 2)

Bareilles, Bouaziz, Fageot, El Mhamdi, *Byzantine Machine Learning: MultiKrum and an Optimal
Notion of Robustness* (PODC 2026, brief announcement; full version arXiv:2602.03899).

The `n` input vectors live in an arbitrary real inner product space `E` (the paper uses `ℝ^d`).
Indices are `Fin n`; subsets of indices are `Finset (Fin n)`.

* `mean x A` = `x̄_A`, `variance x A` = `Σ_A` (Section 4.1).
* `nearestSum x k y` — the sum of the `k` smallest squared distances `‖y - x j‖²`, defined as a
  minimum over all `k`-subsets; `IsNearest` is the paper's "`N(y)` = indices of the `k` closest
  points, ties broken arbitrarily", and `IsNearest.sum_eq_nearestSum` shows the two agree for
  every tie-breaking.
* `score f x y` = `s(y) = (n - f)⁻¹ ∑_{i ∈ N(y)} ‖y - x_i‖²`.
* `IsSelection f m x S` — `S` is a valid `S⋆_m` (Definition 1): `m` indices with smallest scores.
* `IsMultiKrum f m F` — `F` is an `m`-MultiKrum aggregation rule (for some tie-breaking rule).
* `ratio a b` — `a / b` in `EReal` with the paper's convention `0/0 = -∞` (and `a/0 = +∞` for
  `a > 0`).
* `kappaStar f F` — the robustness coefficient `κ⋆(F)` (Definition 2), as an `EReal`.
-/

open Finset

namespace Podc.MultiKrumRobustness

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}

/-- Empirical mean `x̄_A = |A|⁻¹ ∑_{i ∈ A} x_i`. -/
noncomputable def mean (x : Fin n → E) (A : Finset (Fin n)) : E :=
  (A.card : ℝ)⁻¹ • ∑ i ∈ A, x i

/-- Empirical variance `Σ_A = |A|⁻¹ ∑_{i ∈ A} ‖x_i - x̄_A‖²`. -/
noncomputable def variance (x : Fin n → E) (A : Finset (Fin n)) : ℝ :=
  (A.card : ℝ)⁻¹ * ∑ i ∈ A, ‖x i - mean x A‖ ^ 2

/-- The sum of the `k` smallest squared distances from `y` to the points `x j`
(a minimum over all `k`-subsets of indices). -/
noncomputable def nearestSum (x : Fin n → E) (k : ℕ) (y : E) : ℝ :=
  sInf ((fun T : Finset (Fin n) => ∑ j ∈ T, ‖y - x j‖ ^ 2) '' {T | T.card = k})

/-- `T` is a set of indices of `k` points of `x` closest to `y` (ties broken arbitrarily):
the paper's `N(y)` for `k = n - f`. -/
def IsNearest (x : Fin n → E) (k : ℕ) (y : E) (T : Finset (Fin n)) : Prop :=
  T.card = k ∧ ∀ i ∈ T, ∀ j ∉ T, ‖y - x i‖ ≤ ‖y - x j‖

/-- The MultiKrum score `s(y) = (n - f)⁻¹ ∑_{i ∈ N(y)} ‖y - x_i‖²`. -/
noncomputable def score (f : ℕ) (x : Fin n → E) (y : E) : ℝ :=
  ((n - f : ℕ) : ℝ)⁻¹ * nearestSum x (n - f) y

/-- `S` is a valid choice of `S⋆_m` (Definition 1): `m` indices whose scores are no larger than
the scores of all other indices. -/
def IsSelection (f m : ℕ) (x : Fin n → E) (S : Finset (Fin n)) : Prop :=
  S.card = m ∧ ∀ i ∈ S, ∀ j ∉ S, score f x (x i) ≤ score f x (x j)

/-- `F` is an `m`-MultiKrum aggregation rule (Definition 1), for *some* tie-breaking rule:
on every input it outputs the mean of a valid selection `S⋆_m`. Krum is `m = 1`. -/
def IsMultiKrum (f m : ℕ) (F : (Fin n → E) → E) : Prop :=
  ∀ x, ∃ S, IsSelection f m x S ∧ F x = mean x S

/-- `a / b` in `EReal`, with the paper's convention `0 / 0 = -∞` (and `a / 0 = +∞` if `a ≠ 0`). -/
noncomputable def ratio (a b : ℝ) : EReal :=
  if b = 0 then (if a = 0 then ⊥ else ⊤) else ((a / b : ℝ) : EReal)

/-- **Definition 2.** The robustness coefficient
`κ⋆(F) = sup_{x, S ∈ P^n_{n-f}} ‖F(x) - x̄_S‖² / Σ_S ∈ ℝ ∪ {±∞}`. -/
noncomputable def kappaStar (f : ℕ) (F : (Fin n → E) → E) : EReal :=
  ⨆ (x : Fin n → E) (S : Finset (Fin n)) (_ : S.card = n - f),
    ratio (‖F x - mean x S‖ ^ 2) (variance x S)

/-- `F` is `f`-robust (Definition 2): `κ⋆(F) < ∞`. -/
def IsRobust (f : ℕ) (F : (Fin n → E) → E) : Prop :=
  kappaStar f F < ⊤

/-! ### Basic facts -/

lemma variance_nonneg (x : Fin n → E) (A : Finset (Fin n)) : 0 ≤ variance x A := by
  unfold variance; positivity

lemma ratio_le_coe_iff {a b : ℝ} (c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ratio a b ≤ c ↔ a ≤ c * b := by
  unfold ratio
  split_ifs with h1 h2
  · subst h1 h2; simp
  · subst h1
    simp only [top_le_iff, EReal.coe_ne_top, false_iff, mul_zero, not_le]
    exact lt_of_le_of_ne ha (Ne.symm h2)
  · rw [EReal.coe_le_coe_iff, div_le_iff₀ (lt_of_le_of_ne hb (Ne.symm h1))]

/-- Upper bounds on `κ⋆`: `κ⋆(F) ≤ c` iff `‖F(x) - x̄_S‖² ≤ c Σ_S` for all `x` and all `S`. -/
theorem kappaStar_le_iff (f : ℕ) (F : (Fin n → E) → E) (c : ℝ) :
    kappaStar f F ≤ c ↔
      ∀ (x : Fin n → E) (S : Finset (Fin n)), S.card = n - f →
        ‖F x - mean x S‖ ^ 2 ≤ c * variance x S := by
  unfold kappaStar
  simp only [iSup_le_iff]
  refine forall_congr' fun x => forall_congr' fun S => forall_congr' fun _ => ?_
  exact ratio_le_coe_iff c (by positivity) (variance_nonneg x S)

/-- Every instance gives a lower bound on `κ⋆`. -/
lemma ratio_le_kappaStar (f : ℕ) (F : (Fin n → E) → E) (x : Fin n → E) (S : Finset (Fin n))
    (hS : S.card = n - f) :
    ratio (‖F x - mean x S‖ ^ 2) (variance x S) ≤ kappaStar f F := by
  unfold kappaStar
  exact le_iSup_of_le x (le_iSup_of_le S (le_iSup_of_le hS le_rfl))

/-- Lower bound on `κ⋆` from an instance with positive variance. -/
lemma div_le_kappaStar (f : ℕ) (F : (Fin n → E) → E) (x : Fin n → E) (S : Finset (Fin n))
    (hS : S.card = n - f) (hv : 0 < variance x S) :
    (((‖F x - mean x S‖ ^ 2 / variance x S : ℝ)) : EReal) ≤ kappaStar f F := by
  have := ratio_le_kappaStar f F x S hS
  unfold ratio at this
  simpa only [hv.ne', ↓reduceIte] using this

/-! ### Nearest neighbours and scores -/

section nearest

omit [InnerProductSpace ℝ E]

variable (x : Fin n → E)

private lemma image_finite (k : ℕ) (y : E) :
    ((fun T : Finset (Fin n) => ∑ j ∈ T, ‖y - x j‖ ^ 2) '' {T | T.card = k}).Finite :=
  (Set.toFinite _).image _

lemma nearestSum_le {k : ℕ} (y : E) {T : Finset (Fin n)} (hT : T.card = k) :
    nearestSum x k y ≤ ∑ j ∈ T, ‖y - x j‖ ^ 2 :=
  csInf_le (image_finite x k y).bddBelow ⟨T, hT, rfl⟩

lemma exists_nearestSum_eq {k : ℕ} (hk : k ≤ n) (y : E) :
    ∃ T : Finset (Fin n), T.card = k ∧ nearestSum x k y = ∑ j ∈ T, ‖y - x j‖ ^ 2 := by
  have hne : ((fun T : Finset (Fin n) => ∑ j ∈ T, ‖y - x j‖ ^ 2) '' {T | T.card = k}).Nonempty := by
    obtain ⟨T, -, hT⟩ := Finset.exists_subset_card_eq (s := (univ : Finset (Fin n)))
      (by simpa using hk)
    exact ⟨_, T, hT, rfl⟩
  obtain ⟨T, hT, h⟩ := hne.csInf_mem (image_finite x k y)
  exact ⟨T, hT, h.symm⟩

lemma nearestSum_nonneg {k : ℕ} (hk : k ≤ n) (y : E) : 0 ≤ nearestSum x k y := by
  obtain ⟨T, -, h⟩ := exists_nearestSum_eq x hk y
  rw [h]; positivity

/-- Counting lower bound: if fewer than `r` points are at squared distance `< c` from `y`, then the
sum of the `k` smallest squared distances is at least `(k - r) c`. -/
lemma le_nearestSum {k r : ℕ} (hk : k ≤ n) (y : E) {c : ℝ} (hc : 0 ≤ c)
    (hr : (univ.filter fun j => ‖y - x j‖ ^ 2 < c).card ≤ r) :
    ((k : ℝ) - r) * c ≤ nearestSum x k y := by
  obtain ⟨T, hTk, h⟩ := exists_nearestSum_eq x hk y
  rw [h]
  have h1 : ∑ j ∈ T.filter (fun j => c ≤ ‖y - x j‖ ^ 2), ‖y - x j‖ ^ 2 ≤ ∑ j ∈ T, ‖y - x j‖ ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => by positivity)
  have h2 : ((T.filter (fun j => c ≤ ‖y - x j‖ ^ 2)).card : ℝ) * c ≤
      ∑ j ∈ T.filter (fun j => c ≤ ‖y - x j‖ ^ 2), ‖y - x j‖ ^ 2 := by
    rw [← nsmul_eq_mul]
    exact Finset.card_nsmul_le_sum _ _ _ (fun j hj => (mem_filter.1 hj).2)
  have h3 : (k : ℝ) - r ≤ (T.filter (fun j => c ≤ ‖y - x j‖ ^ 2)).card := by
    have e := Finset.card_filter_add_card_filter_not (s := T)
      (fun j => c ≤ ‖y - x j‖ ^ 2)
    have hsub : (T.filter (fun j => ¬ c ≤ ‖y - x j‖ ^ 2)).card ≤ r := by
      refine le_trans (Finset.card_le_card ?_) hr
      intro j hj
      simp only [mem_filter, not_le] at hj
      simp [hj.2]
    rw [hTk] at e
    have : (k : ℝ) = (T.filter (fun j => c ≤ ‖y - x j‖ ^ 2)).card +
        (T.filter (fun j => ¬ c ≤ ‖y - x j‖ ^ 2)).card := by exact_mod_cast e.symm
    have : ((T.filter (fun j => ¬ c ≤ ‖y - x j‖ ^ 2)).card : ℝ) ≤ r := by exact_mod_cast hsub
    linarith
  nlinarith

-- CSLib candidate (sum of the `k` smallest values is attained by any `k` nearest points)
/-- The paper's score is independent of tie-breaking: for any choice `N(y)` of `k` closest points,
`∑_{j ∈ N(y)} ‖y - x_j‖²` equals `nearestSum x k y`. -/
theorem IsNearest.sum_eq_nearestSum {k : ℕ} {y : E} {T : Finset (Fin n)}
    (hT : IsNearest x k y T) : ∑ j ∈ T, ‖y - x j‖ ^ 2 = nearestSum x k y := by
  refine le_antisymm ?_ (nearestSum_le x y hT.1)
  have hk : k ≤ n := by simpa [hT.1] using card_le_univ T
  obtain ⟨T', hT', h⟩ := exists_nearestSum_eq x hk y
  rw [h]
  set d : Fin n → ℝ := fun j => ‖y - x j‖ ^ 2
  have hd : ∀ i ∈ T, ∀ j ∉ T, d i ≤ d j := fun i hi j hj => by
    have := hT.2 i hi j hj
    simp only [d]; gcongr
  have hcard : (T \ T').card = (T' \ T).card := by
    have e1 := Finset.card_inter_add_card_sdiff T T'
    have e2 := Finset.card_inter_add_card_sdiff T' T
    rw [Finset.inter_comm] at e2
    have := hT.1
    omega
  obtain ⟨c, hc1, hc2⟩ : ∃ c : ℝ, (∀ i ∈ T \ T', d i ≤ c) ∧ (∀ j ∈ T' \ T, c ≤ d j) := by
    by_cases hne : (T \ T').Nonempty
    · refine ⟨(T \ T').sup' hne d, fun i hi => le_sup' d hi, fun j hj => ?_⟩
      rw [sup'_le_iff]
      intro i hi
      exact hd i (mem_sdiff.1 hi).1 j (mem_sdiff.1 hj).2
    · rw [not_nonempty_iff_eq_empty] at hne
      have : T' \ T = ∅ := by
        rw [← card_eq_zero, ← hcard, hne, card_empty]
      exact ⟨0, by simp [hne], by simp [this]⟩
  have s1 := Finset.sum_inter_add_sum_sdiff T T' d
  have s2 := Finset.sum_inter_add_sum_sdiff T' T d
  rw [Finset.inter_comm] at s2
  have b1 : ∑ i ∈ T \ T', d i ≤ (T \ T').card * c := by
    rw [← nsmul_eq_mul]; exact Finset.sum_le_card_nsmul _ _ _ hc1
  have b2 : ((T' \ T).card : ℝ) * c ≤ ∑ i ∈ T' \ T, d i := by
    rw [← nsmul_eq_mul]; exact Finset.card_nsmul_le_sum _ _ _ hc2
  rw [hcard] at b1
  show ∑ j ∈ T, d j ≤ ∑ j ∈ T', d j
  linarith

/-- A valid nearest-neighbour choice `N(y)` always exists. -/
lemma exists_isNearest {k : ℕ} (hk : k ≤ n) (y : E) : ∃ T, IsNearest x k y T := by
  -- take a `k`-set minimising the sum; a strict improvement by swapping would contradict minimality
  obtain ⟨T, hT, h⟩ := exists_nearestSum_eq x hk y
  refine ⟨T, hT, fun i hi j hj => ?_⟩
  by_contra hlt
  replace hlt := lt_of_not_ge hlt
  have hlt2 : ‖y - x j‖ ^ 2 < ‖y - x i‖ ^ 2 := by gcongr
  have hcard : (insert j (T.erase i)).card = k := by
    rw [card_insert_of_notMem (fun h' => hj (mem_of_mem_erase h')), card_erase_of_mem hi, hT]
    have : 0 < T.card := card_pos.2 ⟨i, hi⟩
    omega
  have := nearestSum_le x y hcard
  rw [sum_insert (fun h' => hj (mem_of_mem_erase h'))] at this
  have e := Finset.sum_erase_add T (fun j => ‖y - x j‖ ^ 2) hi
  linarith

end nearest

omit [InnerProductSpace ℝ E] in
lemma score_nonneg (f : ℕ) (x : Fin n → E) (y : E) : 0 ≤ score f x y := by
  unfold score
  exact mul_nonneg (by positivity) (nearestSum_nonneg x (Nat.sub_le n f) y)

omit [InnerProductSpace ℝ E] in
/-- A valid MultiKrum selection `S⋆_m` exists for every `m ≤ n`. -/
lemma exists_isSelection (f : ℕ) {m : ℕ} (hm : m ≤ n) (x : Fin n → E) :
    ∃ S, IsSelection f m x S := by
  set s : Fin n → ℝ := fun i => score f x (x i)
  have hne : (univ.powersetCard m : Finset (Finset (Fin n))).Nonempty :=
    powersetCard_nonempty.2 (by simpa using hm)
  obtain ⟨S, hS, hmin⟩ := Finset.exists_min_image _ (fun S => ∑ i ∈ S, s i) hne
  rw [mem_powersetCard] at hS
  refine ⟨S, hS.2, fun i hi j hj => ?_⟩
  by_contra hlt
  replace hlt := lt_of_not_ge hlt
  have hcard : insert j (S.erase i) ∈ (univ.powersetCard m : Finset (Finset (Fin n))) := by
    rw [mem_powersetCard]
    refine ⟨subset_univ _, ?_⟩
    rw [card_insert_of_notMem (fun h' => hj (mem_of_mem_erase h')), card_erase_of_mem hi, hS.2]
    have : 0 < S.card := card_pos.2 ⟨i, hi⟩
    omega
  have := hmin _ hcard
  rw [sum_insert (fun h' => hj (mem_of_mem_erase h'))] at this
  have e := Finset.sum_erase_add S s hi
  change s j < s i at hlt
  linarith

/-- Non-vacuity: an `m`-MultiKrum rule exists for every `m ≤ n`. -/
lemma exists_isMultiKrum (f : ℕ) {m : ℕ} (hm : m ≤ n) :
    ∃ F : (Fin n → E) → E, IsMultiKrum f m F := by
  choose S hS using fun x : Fin n → E => exists_isSelection f hm x
  exact ⟨fun x => mean x (S x), fun x => ⟨S x, hS x, rfl⟩⟩

/-! ### The constants of Section 3 -/

/-- `(√2 + 1)²`, the constant of Theorem 5 (`κ₁ = (√2+1)² (n-f)/(n-2f)`). -/
noncomputable def cKrum : ℝ := (Real.sqrt 2 + 1) ^ 2

/-- `κ^<_2(m) = (√(n-2f)/√m + √2 + 1)²` (Theorem 6, case `m ≤ f`). -/
noncomputable def kappaLt (n f m : ℝ) : ℝ :=
  (Real.sqrt (n - 2 * f) / Real.sqrt m + Real.sqrt 2 + 1) ^ 2

/-- `κ^>_2(m) = (√(n-2f)/√m + √(2f)/√m + f/m)²` (Theorems 1, 2 and 6). -/
noncomputable def kappaGt (n f m : ℝ) : ℝ :=
  (Real.sqrt (n - 2 * f) / Real.sqrt m + Real.sqrt (2 * f) / Real.sqrt m + f / m) ^ 2

end Podc.MultiKrumRobustness
