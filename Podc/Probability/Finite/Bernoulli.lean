import Podc.Probability.Finite.Product

-- CSLib candidate: Cslib/Probability/Finite/Bernoulli.lean

/-!
# Independent Bernoulli coins and random subsets

Every element `u` of a finite type `ι` flips an independent coin that comes up `true` with
probability `p`. An outcome is a coin vector `c : ι → Bool`, or equivalently the random subset
`S = {u | c u}`. Probabilities and expectations are explicit finite sums; no measure theory is
needed (`coinProb_eq_measure_pi` is the bridge to `MeasureTheory.Measure.pi` of
`PMF.bernoulli`).

## Main definitions

* `Cslib.Probability.coinProb p c = ∏ u, (if c u then p else 1 - p)`: the probability of the coin
  vector `c`; `coinExpect p g = ∑ c, coinProb p c * g c` (a special case of `piExpect`).
* `Cslib.Probability.bernWeight p S = p ^ |S| (1 - p) ^ (|ι| - |S|)`: the probability of the
  random subset `S` (`bernWeight_eq_coinProb`).

## Main statements

* `sum_coinProb`, `coinExpect_prod` (independence), linearity and monotonicity of `coinExpect`;
* `coinExpect_allFalse` (`Pr[no coin of A] = (1-p)^|A|`), `coinExpect_coin` (`Pr[c u] = p`);
* `sum_bernWeight_indicator` (`Pr[In ⊆ S ∧ S ∩ Out = ∅] = p^|In| (1-p)^|Out|` for disjoint
  `In`, `Out`), `sum_bernWeight`, `sum_bernWeight_mul_card` (`E|S| = p |ι|`).
-/

open Finset

namespace Cslib.Probability

variable {ι : Type*} [Fintype ι]

/-! ### Coin vectors -/

/-- Probability of the coin vector `c` when every element independently flips a `p`-coin. -/
noncomputable def coinProb (p : ℝ) (c : ι → Bool) : ℝ := ∏ u, if c u then p else 1 - p

/-- Expectation of `g` over one coin vector in which every coin is `true` with probability `p`. -/
noncomputable def coinExpect [DecidableEq ι] (p : ℝ) (g : (ι → Bool) → ℝ) : ℝ :=
  ∑ c, coinProb p c * g c

/-- Coin-vector probabilities are nonnegative for `0 ≤ p ≤ 1`. -/
theorem coinProb_nonneg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (c : ι → Bool) :
    0 ≤ coinProb p c :=
  prod_nonneg fun u _ => by split_ifs <;> linarith

/-- With `p = 1`, only the all-`true` coin vector has positive weight. -/
theorem coinProb_one_ne_zero {c : ι → Bool} (hc : coinProb 1 c ≠ 0) (u : ι) : c u = true := by
  by_contra h
  exact hc (prod_eq_zero (mem_univ u) (by simp [h]))

variable [DecidableEq ι]

/-- `coinExpect` is the expectation under the product of `Bernoulli(p)` weights. -/
theorem coinExpect_eq_piExpect (p : ℝ) (g : (ι → Bool) → ℝ) :
    coinExpect p g = piExpect (fun (_ : ι) (b : Bool) => if b then p else 1 - p) g := rfl

/-- **Independence.** `E[∏ u, g u (c u)] = ∏ u, (p g u true + (1 - p) g u false)`. -/
theorem coinExpect_prod (p : ℝ) (g : ι → Bool → ℝ) :
    coinExpect p (fun c => ∏ u, g u (c u)) = ∏ u, (p * g u true + (1 - p) * g u false) := by
  rw [coinExpect_eq_piExpect, piExpect_prod]
  simp

/-- The probabilities of all coin vectors sum to `1`. -/
theorem sum_coinProb (p : ℝ) : ∑ c : ι → Bool, coinProb p c = 1 := by
  simpa [coinExpect] using coinExpect_prod (ι := ι) p (fun _ _ => 1)

/-- The expectation of a constant is the constant. -/
theorem coinExpect_const (p a : ℝ) : coinExpect (ι := ι) p (fun _ => a) = a := by
  rw [coinExpect, ← sum_mul, sum_coinProb, one_mul]

/-- Linearity of `coinExpect`: additivity. -/
theorem coinExpect_add (p : ℝ) (g h : (ι → Bool) → ℝ) :
    coinExpect p (fun c => g c + h c) = coinExpect p g + coinExpect p h :=
  piExpect_add (fun (_ : ι) (b : Bool) => if b then p else 1 - p) g h

/-- Linearity of `coinExpect`: scalar multiples. -/
theorem coinExpect_mul_left (p a : ℝ) (g : (ι → Bool) → ℝ) :
    coinExpect p (fun c => a * g c) = a * coinExpect p g :=
  piExpect_mul_left (fun (_ : ι) (b : Bool) => if b then p else 1 - p) a g

/-- Linearity of `coinExpect`: finite sums. -/
theorem coinExpect_sum {κ : Type*} (p : ℝ) (s : Finset κ) (g : κ → (ι → Bool) → ℝ) :
    coinExpect p (fun c => ∑ k ∈ s, g k c) = ∑ k ∈ s, coinExpect p (g k) :=
  piExpect_sum (fun (_ : ι) (b : Bool) => if b then p else 1 - p) s g

/-- Monotonicity of `coinExpect` for `0 ≤ p ≤ 1`. -/
theorem coinExpect_mono {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {g h : (ι → Bool) → ℝ}
    (hgh : ∀ c, g c ≤ h c) : coinExpect p g ≤ coinExpect p h :=
  piExpect_mono (μ := fun (_ : ι) (b : Bool) => if b then p else 1 - p)
    (fun _ b => by cases b <;> simp <;> linarith) hgh

/-- Only coin vectors of nonzero probability matter. -/
theorem coinExpect_congr {p : ℝ} {g h : (ι → Bool) → ℝ}
    (hgh : ∀ c, coinProb p c ≠ 0 → g c = h c) : coinExpect p g = coinExpect p h :=
  piExpect_congr (μ := fun (_ : ι) (b : Bool) => if b then p else 1 - p) hgh

/-- `Pr[c u = false for all u ∈ A] = (1 - p) ^ |A|`. -/
theorem coinExpect_allFalse (p : ℝ) (A : Finset ι) :
    coinExpect p (fun c => if ∀ u ∈ A, c u = false then 1 else 0) = (1 - p) ^ #A := by
  have : (fun c : ι → Bool => if ∀ u ∈ A, c u = false then (1 : ℝ) else 0) =
      fun c => ∏ u, if u ∈ A then (if c u then 0 else 1) else 1 := by
    ext c
    rw [prod_ite_mem, univ_inter]
    by_cases h : ∀ u ∈ A, c u = false
    · rw [ite_eq_left h, prod_eq_one fun u hu => by simp [h u hu]]
    · push Not at h
      obtain ⟨u, hu, hcu⟩ := h
      rw [ite_eq_right (fun h' => hcu (h' u hu)),
        prod_eq_zero hu (by simp [Bool.eq_false_iff.not.1 hcu |> fun h => by simpa using hcu])]
  rw [this, coinExpect_prod p (fun u b => if u ∈ A then (if b then 0 else 1) else 1)]
  rw [prod_congr rfl fun u _ => (show (p * (if u ∈ A then (if true then 0 else 1) else 1) +
    (1 - p) * (if u ∈ A then (if false then 0 else 1) else 1) : ℝ) = if u ∈ A then 1 - p else 1
      by by_cases hu : u ∈ A <;> simp [hu])]
  rw [prod_ite_mem, univ_inter, prod_const]

/-- `Pr[c u = true] = p`. -/
theorem coinExpect_coin (p : ℝ) (u : ι) :
    coinExpect p (fun c => if c u = true then 1 else 0) = p := by
  have : (fun c : ι → Bool => if c u = true then (1 : ℝ) else 0) =
      fun c => ∏ v, if v = u then (if c v then 1 else 0) else 1 := by
    ext c
    rw [prod_ite_eq']
    simp
  rw [this, coinExpect_prod p (fun v b => if v = u then (if b then 1 else 0) else 1)]
  rw [prod_congr rfl fun v _ => (show (p * (if v = u then (if true then 1 else 0) else 1) +
    (1 - p) * (if v = u then (if false then 1 else 0) else 1) : ℝ) = if v = u then p else 1
      by by_cases hv : v = u <;> simp [hv])]
  simp

omit [DecidableEq ι] in
/-- Bridge to measure theory: `coinProb p c` is the probability of `{c}` under the product of
`Bernoulli(p)` measures `Ber(true, false, p)`. -/
theorem coinProb_eq_measure_pi (p : unitInterval) (c : ι → Bool) :
    coinProb (p : ℝ) c = (MeasureTheory.Measure.pi fun _ : ι =>
      ProbabilityTheory.bernoulliMeasure true false p).real {c} := by
  rw [MeasureTheory.measureReal_def, MeasureTheory.Measure.pi_singleton, ENNReal.toReal_prod,
    coinProb]
  refine prod_congr rfl fun u _ => ?_
  cases c u <;> simp

/-! ### Random subsets -/

omit [DecidableEq ι] in
/-- The probability of the set `S` when each element of `ι` is included independently with
probability `p`. -/
def bernWeight (p : ℝ) (S : Finset ι) : ℝ := p ^ #S * (1 - p) ^ (Fintype.card ι - #S)

/-- The random subset is the set of `true` coins. -/
theorem bernWeight_eq_coinProb (p : ℝ) (S : Finset ι) :
    bernWeight p S = coinProb p (fun u => decide (u ∈ S)) := by
  rw [bernWeight, coinProb, prod_ite (p := fun u => decide (u ∈ S) = true)]
  simp only [decide_eq_true_eq, prod_const, filter_mem_eq_inter, univ_inter]
  congr
  rw [filter_not, card_sdiff_of_subset (by simp)]
  simp [card_univ]

omit [DecidableEq ι] in
/-- Subset weights are nonnegative for `0 ≤ p ≤ 1`. -/
theorem bernWeight_nonneg {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) (S : Finset ι) :
    0 ≤ bernWeight p S :=
  mul_nonneg (pow_nonneg h0 _) (pow_nonneg (by linarith) _)

/-- `Pr[In ⊆ S ∧ S ∩ Out = ∅] = p ^ |In| * (1 - p) ^ |Out|` for disjoint `In`, `Out`. -/
theorem sum_bernWeight_indicator (p : ℝ) (In Out : Finset ι) (h : Disjoint In Out) :
    ∑ S ∈ univ.powerset, bernWeight p S * (if In ⊆ S ∧ Disjoint S Out then 1 else 0) =
      p ^ #In * (1 - p) ^ #Out := by
  set f : ι → ℝ := fun i => if i ∈ Out then 0 else p
  set g : ι → ℝ := fun i => if i ∈ In then 0 else 1 - p
  have key := Finset.prod_add f g (univ : Finset ι)
  have hl : ∏ i, (f i + g i) = p ^ #In * (1 - p) ^ #Out := by
    have : ∀ i, f i + g i = (if i ∈ In then p else 1) * (if i ∈ Out then 1 - p else 1) := by
      intro i
      by_cases hi : i ∈ In
      · have : i ∉ Out := Finset.disjoint_left.1 h hi
        simp [f, g, hi, this]
      · by_cases ho : i ∈ Out <;> simp [f, g, hi, ho]
    simp_rw [this, Finset.prod_mul_distrib, Finset.prod_ite_mem, univ_inter, prod_const]
  rw [hl] at key
  rw [key]
  refine Finset.sum_congr rfl fun t _ => ?_
  unfold bernWeight
  by_cases hIn : In ⊆ t
  · by_cases hOut : Disjoint t Out
    · rw [ite_eq_left ⟨hIn, hOut⟩, mul_one]
      have h1 : ∏ i ∈ t, f i = p ^ #t := by
        rw [Finset.prod_congr rfl (g := fun _ => p), prod_const]
        intro i hi; simp [f, Finset.disjoint_left.1 hOut hi]
      have h2 : ∏ i ∈ univ \ t, g i = (1 - p) ^ (Fintype.card ι - #t) := by
        rw [Finset.prod_congr rfl (g := fun _ => 1 - p), prod_const, card_sdiff_of_subset
          (subset_univ _), card_univ]
        intro i hi
        have : i ∉ In := fun h' => (mem_sdiff.1 hi).2 (hIn h')
        simp [g, this]
      rw [h1, h2]
    · rw [ite_eq_right (fun h' => hOut h'.2), mul_zero]
      obtain ⟨i, hit, hio⟩ := Finset.not_disjoint_iff.1 hOut
      have : ∏ i ∈ t, f i = 0 := Finset.prod_eq_zero hit (by simp [f, hio])
      rw [this, zero_mul]
  · rw [ite_eq_right (fun h' => hIn h'.1), mul_zero]
    obtain ⟨i, hii, hit⟩ := Finset.not_subset.1 hIn
    have : ∏ i ∈ univ \ t, g i = 0 :=
      Finset.prod_eq_zero (mem_sdiff.2 ⟨mem_univ _, hit⟩) (by simp [g, hii])
    rw [this, mul_zero]

/-- The weights of all subsets sum to `1`. -/
theorem sum_bernWeight (p : ℝ) : ∑ S ∈ (univ : Finset ι).powerset, bernWeight p S = 1 := by
  simpa using sum_bernWeight_indicator (ι := ι) p ∅ ∅ (disjoint_empty_left _)

/-- The expected size of the random subset is `p |ι|`. -/
theorem sum_bernWeight_mul_card (p : ℝ) :
    ∑ S ∈ (univ : Finset ι).powerset, bernWeight p S * (#S : ℝ) = Fintype.card ι * p := by
  have : ∀ S : Finset ι, (#S : ℝ) = ∑ i, if {i} ⊆ S ∧ Disjoint S ∅ then 1 else 0 := by
    intro S; simp
  simp_rw [this, mul_sum]
  rw [sum_comm]
  simp_rw [sum_bernWeight_indicator p {_} ∅ (disjoint_empty_right _)]
  simp

end Cslib.Probability
