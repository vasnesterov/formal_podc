import Mathlib

/-!
# Finite uniform probability for the sampling argument of Section 2

The conversion of Theorem 2.1 puts every vertex into the "fault set" `J` independently with
probability `p = 1 - 1/m` (the paper uses `m = r`, and `m = 2` when `r = 1`). We realise this
exactly on a *finite uniform* sample space: every vertex draws a uniform label in `Fin m` and
survives (is not in `J`) iff its label is `0`. Repeating `α` times independently is the uniform
distribution on `Fin α → V → Fin m`. Probabilities are then ratios of cardinalities (`uprob`), and no
measure theory is needed.

Main facts:
* `uprob_pi` — independence: on a product space, a "coordinatewise" event has probability equal to
  the product of the coordinate probabilities.
* `uprob_exists_le` — union bound.
* `uprob_card_zero_gt` — a Chernoff bound for the number of survivors:
  `Pr[#{v : s v = 0} > c] ≤ (1 + 1/m)^n / 2^c`, and `uprob_card_zero_gt_two_mul` —
  `Pr[#{v : s v = 0} > 2n/m] ≤ exp(-n/(3m))` (the paper's `e^{-(1/3) n/r}`).
-/

open Finset

namespace DinitzKrauthgamer

-- CSLib candidate (finite uniform probability toolkit: `uprob`, union bound, `uprob_pi`)
section uprob

variable {Ω : Type*} [Fintype Ω]

/-- Probability of an event under the uniform distribution on a finite type. -/
noncomputable def uprob (E : Ω → Prop) : ℝ := (Nat.card {ω // E ω} : ℝ) / Fintype.card Ω

lemma uprob_eq_card_filter (E : Ω → Prop) [DecidablePred E] :
    uprob E = (#(univ.filter E) : ℝ) / Fintype.card Ω := by
  rw [uprob, Nat.card_eq_fintype_card, Fintype.card_subtype]

lemma uprob_nonneg (E : Ω → Prop) : 0 ≤ uprob E := by unfold uprob; positivity

lemma uprob_mono {E E' : Ω → Prop} (h : ∀ ω, E ω → E' ω) : uprob E ≤ uprob E' := by
  classical
  rw [uprob_eq_card_filter, uprob_eq_card_filter]
  gcongr
  exact h _

lemma uprob_le_one (E : Ω → Prop) : uprob E ≤ 1 := by
  classical
  rw [uprob_eq_card_filter]
  rcases (Fintype.card Ω).eq_zero_or_pos with h | h
  · simp [h]
  · rw [div_le_one (by exact_mod_cast h)]
    exact_mod_cast (card_filter_le _ _).trans (by simp)

lemma uprob_not [Nonempty Ω] (E : Ω → Prop) : uprob (fun ω => ¬ E ω) = 1 - uprob E := by
  classical
  rw [uprob_eq_card_filter, uprob_eq_card_filter]
  have hpos : (0 : ℝ) < Fintype.card Ω := by exact_mod_cast Fintype.card_pos
  have := Finset.card_filter_add_card_filter_not (s := (univ : Finset Ω)) E
  rw [card_univ] at this
  rw [eq_sub_iff_add_eq, ← add_div, div_eq_one_iff_eq hpos.ne']
  exact_mod_cast (add_comm _ _).trans this

lemma uprob_true : uprob (fun _ : Ω => True) = if Fintype.card Ω = 0 then 0 else 1 := by
  classical
  rw [uprob_eq_card_filter]
  split_ifs with h
  · simp [h]
  · simp [filter_true_of_mem, div_self (by exact_mod_cast h : (Fintype.card Ω : ℝ) ≠ 0)]

/-- **Union bound.** -/
lemma uprob_exists_le {ι : Type*} (s : Finset ι) (E : ι → Ω → Prop) :
    uprob (fun ω => ∃ i ∈ s, E i ω) ≤ ∑ i ∈ s, uprob (E i) := by
  classical
  simp only [uprob_eq_card_filter, ← Finset.sum_div]
  gcongr
  have : univ.filter (fun ω => ∃ i ∈ s, E i ω) = s.biUnion fun i => univ.filter (E i) := by
    ext ω; simp
  rw [this]
  exact_mod_cast card_biUnion_le

lemma uprob_or_le (E E' : Ω → Prop) : uprob (fun ω => E ω ∨ E' ω) ≤ uprob E + uprob E' := by
  classical
  have h := uprob_exists_le (Ω := Ω) (univ : Finset Bool) (fun b ω => if b then E ω else E' ω)
  simp only [mem_univ, true_and, Fintype.sum_bool, ite_true] at h
  refine le_trans (uprob_mono fun ω hω => ?_) h
  rcases hω with h1 | h1
  · exact ⟨true, by simpa using h1⟩
  · exact ⟨false, by simpa using h1⟩

/-- `Pr[A ∧ B] ≥ 1 - Pr[¬A] - Pr[¬B]`. -/
lemma one_sub_sub_le_uprob_and [Nonempty Ω] (A B : Ω → Prop) :
    1 - uprob (fun ω => ¬ A ω) - uprob (fun ω => ¬ B ω) ≤ uprob (fun ω => A ω ∧ B ω) := by
  have h1 := uprob_or_le (fun ω => ¬ A ω) (fun ω => ¬ B ω)
  have h2 : uprob (fun ω => A ω ∧ B ω) = 1 - uprob (fun ω => ¬ A ω ∨ ¬ B ω) := by
    rw [← uprob_not]; congr 1; ext ω; tauto
  linarith

end uprob

/-- **Independence on product spaces.** Under the uniform distribution on `ι → X`, the coordinates
are independent: `Pr[∀ i, P i (ω i)] = ∏ i, Pr[P i]`. -/
lemma uprob_pi {ι X : Type*} [Fintype ι] [DecidableEq ι] [Fintype X] (P : ι → X → Prop) :
    uprob (fun ω : ι → X => ∀ i, P i (ω i)) = ∏ i, uprob (P i) := by
  classical
  unfold uprob
  rw [Finset.prod_div_distrib]
  have e : {ω : ι → X // ∀ i, P i (ω i)} ≃ ∀ i, {x // P i x} := Equiv.subtypePiEquivPi
  rw [Nat.card_congr e, Nat.card_pi, Fintype.card_pi]
  push_cast
  rfl

/-! ### Survivors and a Chernoff bound -/

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The vertices that survive a sample `s : V → Fin m` (label `0`), i.e. `V \ J`. -/
def surv {m : ℕ} (s : V → Fin m) [NeZero m] : Finset V := univ.filter fun v => s v = 0

/-- `∑_s 2^{#survivors(s)} = (m + 1)^n`. -/
lemma sum_two_pow_card_surv (m : ℕ) [NeZero m] :
    ∑ s : V → Fin m, (2 : ℝ) ^ #(surv s) = ((m : ℝ) + 1) ^ Fintype.card V := by
  have h1 : ∀ s : V → Fin m, (2 : ℝ) ^ #(surv s) = ∏ v, (if s v = 0 then (2 : ℝ) else 1) := by
    intro s
    rw [Finset.prod_ite, prod_const, prod_const_one, mul_one]
    rfl
  simp_rw [h1]
  rw [← Fintype.prod_sum (fun (_ : V) (a : Fin m) => if a = 0 then (2 : ℝ) else 1)]
  rw [prod_const, card_univ]
  congr 1
  rw [Finset.sum_ite, sum_const, sum_const, filter_eq' univ (0 : Fin m)]
  simp only [mem_univ, ite_true, card_singleton, nsmul_eq_mul, Nat.cast_one, mul_one]
  rw [Finset.filter_ne' univ (0 : Fin m), card_erase_of_mem (mem_univ _), card_univ,
    Fintype.card_fin]
  have : 1 ≤ m := Nat.pos_of_ne_zero (NeZero.ne m)
  push_cast [this]
  ring

/-- **Chernoff bound (counting form).** For a uniform sample `s : V → Fin m` and any real `c`,
`Pr[#survivors > c] ≤ (1 + 1/m)^n / 2^c`. -/
lemma uprob_card_surv_gt (m : ℕ) [NeZero m] (c : ℝ) :
    uprob (fun s : V → Fin m => c < #(surv s)) ≤
      (1 + 1 / (m : ℝ)) ^ Fintype.card V / (2 : ℝ) ^ c := by
  classical
  have hm : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne m)
  rw [uprob_eq_card_filter, Fintype.card_fun, Fintype.card_fin]
  have h2c : (0 : ℝ) < (2 : ℝ) ^ c := by positivity
  set A := univ.filter fun s : V → Fin m => c < #(surv s)
  -- Markov: `#A · 2^c ≤ ∑ 2^X`
  have hmarkov : (#A : ℝ) * (2 : ℝ) ^ c ≤ ((m : ℝ) + 1) ^ Fintype.card V := by
    rw [← sum_two_pow_card_surv m]
    calc (#A : ℝ) * (2 : ℝ) ^ c = ∑ s ∈ A, (2 : ℝ) ^ c := by rw [sum_const, nsmul_eq_mul]
      _ ≤ ∑ s ∈ A, (2 : ℝ) ^ #(surv s) := by
          refine Finset.sum_le_sum fun s hs => ?_
          rw [← Real.rpow_natCast]
          exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (mem_filter.mp hs).2.le
      _ ≤ ∑ s, (2 : ℝ) ^ #(surv s) :=
          Finset.sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => by positivity)
  rw [div_le_div_iff₀ (by have := Nat.pos_of_ne_zero (NeZero.ne m); positivity) h2c]
  calc (#A : ℝ) * (2 : ℝ) ^ c ≤ ((m : ℝ) + 1) ^ Fintype.card V := hmarkov
    _ = (1 + 1 / (m : ℝ)) ^ Fintype.card V * ((m ^ Fintype.card V : ℕ) : ℝ) := by
        push_cast
        rw [← mul_pow]; congr 1; field_simp

/-- **Chernoff bound used in Theorem 2.1.** `Pr[#survivors > 2n/m] ≤ exp(-n/(3m))`. -/
lemma uprob_card_surv_gt_two_mul (m : ℕ) [NeZero m] :
    uprob (fun s : V → Fin m => 2 * (Fintype.card V : ℝ) / m < #(surv s)) ≤
      Real.exp (-((Fintype.card V : ℝ) / (3 * m))) := by
  refine (uprob_card_surv_gt m _).trans ?_
  set n := Fintype.card V
  have hm : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne m)
  have h1 : (1 + 1 / (m : ℝ)) ^ n ≤ Real.exp ((n : ℝ) / m) := by
    calc (1 + 1 / (m : ℝ)) ^ n ≤ Real.exp (1 / (m : ℝ)) ^ n := by
          gcongr
          linarith [Real.add_one_le_exp (1 / (m : ℝ))]
      _ = Real.exp ((n : ℝ) / m) := by rw [← Real.exp_nat_mul]; ring_nf
  have h2 : (2 : ℝ) ^ (2 * (n : ℝ) / m) = Real.exp (2 * (n : ℝ) / m * Real.log 2) := by
    rw [Real.rpow_def_of_pos (by norm_num), mul_comm]
  rw [h2, div_le_iff₀ (Real.exp_pos _), ← Real.exp_add]
  refine h1.trans (Real.exp_le_exp.mpr ?_)
  have hlog : (2 : ℝ) / 3 ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hn : (0 : ℝ) ≤ n / m := by positivity
  have : -((n : ℝ) / (3 * m)) + 2 * n / m * Real.log 2 = (n / m) * (2 * Real.log 2 - 1 / 3) := by
    field_simp
    ring
  rw [this]
  nlinarith

/-- The number of fault sets of size at most `r` is at most `(n + 1)^r`. -/
lemma card_faultSets_le (r : ℕ) :
    #(univ.filter fun F : Finset V => #F ≤ r) ≤ (Fintype.card V + 1) ^ r := by
  set n := Fintype.card V
  have hsub : (univ.filter fun F : Finset V => #F ≤ r) ⊆
      (range (r + 1)).biUnion fun i => powersetCard i univ := by
    intro F hF
    rw [mem_filter] at hF
    simp only [mem_biUnion, mem_range, mem_powersetCard]
    exact ⟨#F, by omega, subset_univ _, rfl⟩
  refine (card_le_card hsub).trans (card_biUnion_le.trans ?_)
  simp only [card_powersetCard, card_univ]
  rw [add_pow]
  refine Finset.sum_le_sum fun i hi => ?_
  simp only [one_pow, mul_one]
  have hi' : i ≤ r := Nat.lt_succ_iff.mp (mem_range.mp hi)
  calc n.choose i ≤ n ^ i := Nat.choose_le_pow n i
    _ ≤ n ^ i * r.choose i := Nat.le_mul_of_pos_right _ (Nat.choose_pos hi')

end DinitzKrauthgamer
