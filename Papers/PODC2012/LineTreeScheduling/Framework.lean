import Papers.PODC2012.LineTreeScheduling.Basic

/-!
# The two-phase primal–dual framework (Sections 3.2 and 6.1)

The first phase starts from the zero dual assignment and performs a sequence of iterations
`t = 0, 1, …, T-1`; iteration `t` raises every demand instance of a set `Is t`. Raising `d` at the
current dual assignment `y` (Section 3.2, and its height variant in Section 6.1):

* `δ(d) = s / (1 + h(d) c(d) |π(d)|)` where `s = p(d) - lhs(d)` is the slackness;
* `α(a_d) += δ(d)` and `β(e) += c(d) δ(d)` for every critical edge `e ∈ π(d)`.

With `h = c = 1` this is the rule of Section 3.2 (`δ(d) = s/(|π(d)|+1)`); with `h` the heights and
`c(d) = 2|π(d)|` it is the rule of Section 6.1 (`δ(d) = s/(1 + 2h(d)|π(d)|²)`, `β(e) += 2|π(d)|δ(d)`).
In both cases the dual constraint of `d` becomes tight. A `Rule` packages `h`, `c` and `π`.

All instances of an iteration are raised simultaneously, each with the `δ` computed from the dual
assignment at the beginning of the iteration; the paper does the same (its sets are independent,
so the raises do not interact).

Main results of this file:
* `lhs_run`, `val_run` — closed forms of the dual constraints and of the dual objective after `t`
  iterations as sums over the earlier raises.
* `profit_le_lhs_of_mem` and `not_mem_of_mem_of_lt` — a raised instance is satisfied afterwards and
  is never raised again.
* `sum_raise_le_profitOf` — the charging argument of Lemmas 3.1 and 6.1: if every raised instance
  not in the final solution `S` is "covered" by later raises of instances of `S` (with total
  weight `≥ 1`), then `∑_{raised} δ ≤ p(S)`.
* `lam_mul_lpValue_le` — the resulting approximation bound `λ · LP ≤ M · p(S)`.
* `phase2` — the second phase (pop the stack, add an instance if an acceptance test passes), with its
  generic invariants.
-/

-- CSLib candidate: abstract two-phase primal–dual framework for packing problems

set_option linter.unusedSectionVars false

namespace Podc.LineTreeScheduling

open Finset

variable {A D E : Type*} [DecidableEq A] [DecidableEq D] [DecidableEq E]

/-- The parameters of the raising rule: the heights `h` used in the dual constraints, the
multiplier `c` of the raise of the edge variables, and the critical edges `π(d)`. -/
structure Rule (D E : Type*) where
  /-- Heights (`1` in the unit-height case). -/
  h : D → ℝ
  /-- The edge variables of `π(d)` are raised by `c(d) δ(d)`. -/
  c : D → ℝ
  /-- The critical edges `π(d)`. -/
  crit : D → Finset E

/-- A rule is well-formed if `h, c ≥ 0` and `π(d) ⊆ path(d)`. -/
structure Rule.WF (R : Rule D E) (I : Inst A D E) : Prop where
  h_nonneg : ∀ d, 0 ≤ R.h d
  c_nonneg : ∀ d, 0 ≤ R.c d
  crit_subset : ∀ d, R.crit d ⊆ I.path d

/-- The denominator `1 + h(d) c(d) |π(d)|` of the raise amount. -/
def Rule.denom (R : Rule D E) (d : D) : ℝ := 1 + R.h d * R.c d * (R.crit d).card

noncomputable section

namespace Inst

variable (I : Inst A D E) (R : Rule D E)

/-- The raise amount `δ(d) = (p(d) - lhs(d)) / (1 + h(d) c(d) |π(d)|)`. -/
def amt (y : Duals A E) (d : D) : ℝ := (I.profit d - I.lhs R.h y d) / R.denom d

/-- One iteration: raise every instance of `S`. -/
def raise (y : Duals A E) (S : Finset D) : Duals A E :=
  ⟨fun a => y.α a + ∑ d ∈ S with I.dem d = a, I.amt R y d,
   fun e => y.β e + ∑ d ∈ S with e ∈ R.crit d, R.c d * I.amt R y d⟩

/-- The dual assignment after the first `t` iterations, raising `Is 0, Is 1, …`. -/
def run (Is : ℕ → Finset D) : ℕ → Duals A E
  | 0 => 0
  | t + 1 => I.raise R (run Is t) (Is t)

/-- The contribution factor of a raise of `d'` to the dual constraint of `d`:
`[a_{d'} = a_d] + h(d) c(d') |π(d') ∩ path(d)|`. -/
def weight (d' d : D) : ℝ :=
  (if I.dem d' = I.dem d then 1 else 0) + R.h d * R.c d' * (R.crit d' ∩ I.path d).card

@[simp] lemma run_zero (Is : ℕ → Finset D) : I.run R Is 0 = 0 := rfl

lemma run_succ (Is : ℕ → Finset D) (t : ℕ) :
    I.run R Is (t + 1) = I.raise R (I.run R Is t) (Is t) := rfl

lemma lhs_raise (y : Duals A E) (S : Finset D) (d : D) :
    I.lhs R.h (I.raise R y S) d = I.lhs R.h y d + ∑ d' ∈ S, I.amt R y d' * I.weight R d' d := by
  have hβ : ∑ e ∈ I.path d, ∑ d' ∈ S with e ∈ R.crit d', R.c d' * I.amt R y d' =
      ∑ d' ∈ S, R.c d' * I.amt R y d' * ((R.crit d' ∩ I.path d).card : ℝ) := by
    simp_rw [Finset.sum_filter]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun d' _ => ?_
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, Finset.filter_mem_eq_inter,
      Finset.inter_comm]
    ring
  have hα : ∑ d' ∈ S with I.dem d' = I.dem d, I.amt R y d' =
      ∑ d' ∈ S, I.amt R y d' * (if I.dem d' = I.dem d then 1 else 0) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun d' _ => ?_
    split_ifs <;> simp
  simp only [lhs, raise, Finset.sum_add_distrib, hβ, hα, weight, mul_add, Finset.mul_sum]
  have : ∀ x ∈ S, R.h d * (R.c x * I.amt R y x * ((R.crit x ∩ I.path d).card : ℝ)) =
      I.amt R y x * (R.h d * R.c x * ((R.crit x ∩ I.path d).card : ℝ)) := fun _ _ => by ring
  rw [Finset.sum_congr rfl this]
  ring

lemma val_raise [Fintype A] [Fintype E] (y : Duals A E) (S : Finset D) :
    (I.raise R y S).val = y.val + ∑ d' ∈ S, I.amt R y d' * (1 + R.c d' * (R.crit d').card) := by
  simp only [Duals.val, raise, Finset.sum_add_distrib, mul_add, mul_one]
  have h1 : ∑ a, ∑ d ∈ S with I.dem d = a, I.amt R y d = ∑ d' ∈ S, I.amt R y d' := by
    simp_rw [Finset.sum_filter]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun d' _ => ?_
    simp
  have h2 : ∑ e, ∑ d ∈ S with e ∈ R.crit d, R.c d * I.amt R y d =
      ∑ d' ∈ S, I.amt R y d' * (R.c d' * (R.crit d').card) := by
    simp_rw [Finset.sum_filter]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun d' _ => ?_
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    simp only [Finset.filter_mem_eq_inter, Finset.univ_inter]
    ring
  rw [h1, h2]; ring

/-- Closed form of the left-hand side of a dual constraint after `t` iterations. -/
lemma lhs_run (Is : ℕ → Finset D) (t : ℕ) (d : D) :
    I.lhs R.h (I.run R Is t) d =
      ∑ s ∈ range t, ∑ d' ∈ Is s, I.amt R (I.run R Is s) d' * I.weight R d' d := by
  induction t with
  | zero => simp [lhs]
  | succ t ih => rw [run_succ, lhs_raise, ih, Finset.sum_range_succ]

/-- Closed form of the dual objective after `t` iterations. -/
lemma val_run [Fintype A] [Fintype E] (Is : ℕ → Finset D) (t : ℕ) :
    (I.run R Is t).val =
      ∑ s ∈ range t, ∑ d' ∈ Is s, I.amt R (I.run R Is s) d' * (1 + R.c d' * (R.crit d').card) := by
  induction t with
  | zero => simp [Duals.val]
  | succ t ih => rw [run_succ, val_raise, ih, Finset.sum_range_succ]

/-- A valid run of the first phase with `T` iterations: every set `Is t` is independent and
consists of instances whose dual constraint is unsatisfied at the beginning of iteration `t`
(Section 3.2: `I ⊆ U`). -/
structure ValidRun (Is : ℕ → Finset D) (T : ℕ) : Prop where
  indep : ∀ t < T, I.IsIndep (Is t)
  unsat : ∀ t < T, ∀ d ∈ Is t, I.lhs R.h (I.run R Is t) d < I.profit d

/-- The interference property (Section 3.2): if overlapping instances `d₁, d₂` are raised in this
order, then `path(d₂)` contains a critical edge of `d₁`. -/
def Interference (Is : ℕ → Finset D) (T : ℕ) : Prop :=
  ∀ s t, s < t → t < T → ∀ d₁ ∈ Is s, ∀ d₂ ∈ Is t, I.Overlap d₁ d₂ →
    (R.crit d₁ ∩ I.path d₂).Nonempty

variable {I R}

lemma denom_pos (hR : R.WF I) (d : D) : 0 < R.denom d := by
  unfold Rule.denom
  have := mul_nonneg (mul_nonneg (hR.h_nonneg d) (hR.c_nonneg d)) (Nat.cast_nonneg (R.crit d).card)
  linarith

lemma one_le_denom (hR : R.WF I) (d : D) : 1 ≤ R.denom d := by
  unfold Rule.denom
  have := mul_nonneg (mul_nonneg (hR.h_nonneg d) (hR.c_nonneg d)) (Nat.cast_nonneg (R.crit d).card)
  linarith

lemma weight_nonneg (hR : R.WF I) (d' d : D) : 0 ≤ I.weight R d' d := by
  unfold weight
  have := mul_nonneg (mul_nonneg (hR.h_nonneg d) (hR.c_nonneg d'))
    (Nat.cast_nonneg (R.crit d' ∩ I.path d).card)
  have : (0 : ℝ) ≤ if I.dem d' = I.dem d then 1 else 0 := by split_ifs <;> norm_num
  linarith

lemma weight_self (hR : R.WF I) (d : D) : I.weight R d d = R.denom d := by
  unfold weight Rule.denom
  rw [Finset.inter_eq_left.2 (hR.crit_subset d)]
  simp

/-- `δ(d) · (1 + h c |π|)` is the slackness: after the raise the constraint is tight. -/
lemma amt_mul_denom (hR : R.WF I) (y : Duals A E) (d : D) :
    I.amt R y d * R.denom d = I.profit d - I.lhs R.h y d := by
  unfold amt; field_simp [(denom_pos hR d).ne']

variable {Is : ℕ → Finset D} {T : ℕ}

lemma amt_pos (hR : R.WF I) (hv : I.ValidRun R Is T) {t : ℕ} (ht : t < T) {d : D}
    (hd : d ∈ Is t) : 0 < I.amt R (I.run R Is t) d := by
  unfold amt
  exact div_pos (by linarith [hv.unsat t ht d hd]) (denom_pos hR d)

lemma lhs_mono (hR : R.WF I) (hv : I.ValidRun R Is T) {s t : ℕ} (hst : s ≤ t) (htT : t ≤ T)
    (d : D) : I.lhs R.h (I.run R Is s) d ≤ I.lhs R.h (I.run R Is t) d := by
  rw [lhs_run, lhs_run]
  refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hst) fun u hu _ => ?_
  refine Finset.sum_nonneg fun d' hd' => ?_
  have hu : u < T := by have := Finset.mem_range.1 hu; omega
  exact mul_nonneg (amt_pos hR hv hu hd').le (weight_nonneg hR d' d)

/-- After `d` is raised at iteration `t`, its dual constraint is satisfied. -/
lemma profit_le_lhs_of_mem (hR : R.WF I) (hv : I.ValidRun R Is T) {t : ℕ} (ht : t < T) {d : D}
    (hd : d ∈ Is t) : I.profit d ≤ I.lhs R.h (I.run R Is (t + 1)) d := by
  rw [run_succ, lhs_raise, ← Finset.add_sum_erase _ _ hd, weight_self hR, amt_mul_denom hR]
  have : 0 ≤ ∑ d' ∈ (Is t).erase d, I.amt R (I.run R Is t) d' * I.weight R d' d :=
    Finset.sum_nonneg fun d' hd' =>
      mul_nonneg (amt_pos hR hv ht (Finset.mem_of_mem_erase hd')).le (weight_nonneg hR d' d)
  linarith

/-- An instance is raised at most once. -/
lemma not_mem_of_mem_of_lt (hR : R.WF I) (hv : I.ValidRun R Is T) {s t : ℕ} (hst : s < t)
    (ht : t < T) {d : D} (hd : d ∈ Is s) : d ∉ Is t := by
  intro hd'
  have h1 := profit_le_lhs_of_mem hR hv (hst.trans ht) hd
  have h2 := lhs_mono hR hv (Nat.succ_le_of_lt hst) ht.le d
  have h3 := hv.unsat t ht d hd'
  linarith

lemma disjoint_of_ne (hR : R.WF I) (hv : I.ValidRun R Is T) {s t : ℕ} (hs : s < T) (ht : t < T)
    (hst : s ≠ t) : Disjoint (Is s) (Is t) := by
  rw [Finset.disjoint_left]
  intro d h1 h2
  rcases lt_or_gt_of_ne hst with h | h
  · exact not_mem_of_mem_of_lt hR hv h ht h1 h2
  · exact not_mem_of_mem_of_lt hR hv h hs h2 h1

lemma run_α_nonneg (hR : R.WF I) (hv : I.ValidRun R Is T) {t : ℕ} (ht : t ≤ T) (a : A) :
    0 ≤ (I.run R Is t).α a := by
  induction t with
  | zero => simp
  | succ t ih =>
    simp only [run_succ, raise]
    exact add_nonneg (ih (by omega)) (Finset.sum_nonneg fun d hd =>
      (amt_pos hR hv (by omega) (Finset.mem_filter.1 hd).1).le)

lemma run_β_nonneg (hR : R.WF I) (hv : I.ValidRun R Is T) {t : ℕ} (ht : t ≤ T) (e : E) :
    0 ≤ (I.run R Is t).β e := by
  induction t with
  | zero => simp
  | succ t ih =>
    simp only [run_succ, raise]
    exact add_nonneg (ih (by omega)) (Finset.sum_nonneg fun d hd =>
      mul_nonneg (hR.c_nonneg d) (amt_pos hR hv (by omega) (Finset.mem_filter.1 hd).1).le)

/-- The set `R` of all instances raised in the first phase. -/
def raised (Is : ℕ → Finset D) (T : ℕ) : Finset D := (range T).biUnion Is

/-- Sum over the instances of `S` raised at some iteration in `[0, T)`, split by iteration. -/
lemma sum_filter_raised (hR : R.WF I) (hv : I.ValidRun R Is T) (P : ℕ → Prop) [DecidablePred P]
    (S : Finset D) (f : D → ℝ) :
    ∑ t ∈ (range T).filter P, ∑ d ∈ (Is t).filter (· ∈ S), f d =
      ∑ d ∈ ((range T).filter P).biUnion (fun t => (Is t).filter (· ∈ S)), f d := by
  rw [Finset.sum_biUnion]
  intro s hs t ht hst
  have hs' := Finset.mem_range.1 (Finset.mem_filter.1 hs).1
  have ht' := Finset.mem_range.1 (Finset.mem_filter.1 ht).1
  exact Finset.disjoint_filter_filter (disjoint_of_ne hR hv hs' ht' hst)

/-- **Charging argument** of Lemmas 3.1 and 6.1. Let `S ⊆ R` and suppose every raised instance
`d' ∉ S` (raised at iteration `s`) is covered: the raises... more precisely the weights
`weight d' d` towards the instances `d ∈ S` raised after `s` sum to at least `1`. Then
`∑_{d ∈ R} δ(d) ≤ p(S)`. -/
theorem sum_raise_le_profitOf (hR : R.WF I) (hv : I.ValidRun R Is T) {S : Finset D}
    (hS : S ⊆ raised Is T)
    (hcov : ∀ s < T, ∀ d' ∈ Is s, d' ∉ S →
      1 ≤ ∑ t ∈ (range T).filter (s < ·), ∑ d ∈ (Is t).filter (· ∈ S), I.weight R d' d) :
    ∑ s ∈ range T, ∑ d' ∈ Is s, I.amt R (I.run R Is s) d' ≤ I.profitOf S := by
  set δ : ℕ → D → ℝ := fun s d => I.amt R (I.run R Is s) d with hδ
  -- split `p(S)` by iterations
  have hsplit : I.profitOf S = ∑ t ∈ range T, ∑ d ∈ (Is t).filter (· ∈ S), I.profit d := by
    rw [show range T = (range T).filter (fun _ => True) by simp, sum_filter_raised hR hv]
    unfold profitOf
    congr 1
    ext d
    simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_range, and_true]
    constructor
    · intro hd
      obtain ⟨t, ht, hdt⟩ := Finset.mem_biUnion.1 (hS hd)
      exact ⟨t, Finset.mem_range.1 ht, hdt, hd⟩
    · rintro ⟨t, _, _, hd⟩; exact hd
  -- each selected instance pays for its own raise and for all earlier raises
  have hpay : ∀ t < T, ∀ d ∈ Is t, δ t d + ∑ s ∈ range t, ∑ d' ∈ Is s, δ s d' * I.weight R d' d ≤
      I.profit d := by
    intro t ht d hd
    have h1 := amt_mul_denom hR (I.run R Is t) d
    have h2 := one_le_denom hR (R := R) (I := I) d
    have h3 := amt_pos hR hv ht hd
    rw [← lhs_run]
    have : δ t d ≤ δ t d * R.denom d := le_mul_of_one_le_right h3.le h2
    simp only [hδ] at this ⊢
    linarith
  have hge : ∑ t ∈ range T, ∑ d ∈ (Is t).filter (· ∈ S),
      (δ t d + ∑ s ∈ range t, ∑ d' ∈ Is s, δ s d' * I.weight R d' d) ≤ I.profitOf S := by
    rw [hsplit]
    exact Finset.sum_le_sum fun t ht => Finset.sum_le_sum fun d hd =>
      hpay t (Finset.mem_range.1 ht) d (Finset.mem_filter.1 hd).1
  -- swap the order of summation in the second part
  have hswap : ∑ t ∈ range T, ∑ d ∈ (Is t).filter (· ∈ S),
      ∑ s ∈ range t, ∑ d' ∈ Is s, δ s d' * I.weight R d' d =
      ∑ s ∈ range T, ∑ d' ∈ Is s, δ s d' *
        ∑ t ∈ (range T).filter (s < ·), ∑ d ∈ (Is t).filter (· ∈ S), I.weight R d' d := by
    have e1 : ∀ t ∈ range T, ∑ d ∈ (Is t).filter (· ∈ S),
        ∑ s ∈ range t, ∑ d' ∈ Is s, δ s d' * I.weight R d' d =
        ∑ s ∈ range T, ∑ d' ∈ Is s, ∑ d ∈ (Is t).filter (· ∈ S),
          (if s < t then δ s d' * I.weight R d' d else 0) := by
      intro t ht
      rw [Finset.sum_comm]
      have : range t = (range T).filter (· < t) := by
        ext s; simp only [Finset.mem_range, Finset.mem_filter]
        have := Finset.mem_range.1 ht; constructor <;> intro h <;> omega
      rw [this, Finset.sum_filter]
      refine Finset.sum_congr rfl fun s _ => ?_
      split_ifs with hst
      · rw [Finset.sum_comm]
      · simp
    rw [Finset.sum_congr rfl e1, Finset.sum_comm]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun d' _ => ?_
    rw [Finset.mul_sum, Finset.sum_filter]
    refine Finset.sum_congr rfl fun t _ => ?_
    split_ifs with hst
    · rw [Finset.mul_sum]
    · simp
  have hfirst : ∑ t ∈ range T, ∑ d ∈ (Is t).filter (· ∈ S), δ t d =
      ∑ s ∈ range T, ∑ d' ∈ Is s, (if d' ∈ S then δ s d' else 0) := by
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Finset.sum_filter]
  rw [Finset.sum_congr rfl fun t _ => Finset.sum_add_distrib, Finset.sum_add_distrib, hswap,
    hfirst, ← Finset.sum_add_distrib] at hge
  refine le_trans (Finset.sum_le_sum fun s hs => ?_) hge
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun d' hd' => ?_
  have hsT := Finset.mem_range.1 hs
  have hpos := (amt_pos hR hv hsT hd').le
  have hC : 0 ≤ ∑ t ∈ (range T).filter (s < ·), ∑ d ∈ (Is t).filter (· ∈ S), I.weight R d' d :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => weight_nonneg hR _ _
  by_cases hmem : d' ∈ S
  · simp only [hmem, ↓reduceIte]
    have := mul_nonneg hpos hC
    simp only [hδ] at this ⊢
    linarith
  · simp only [hmem, ↓reduceIte, zero_add]
    have := mul_le_mul_of_nonneg_left (hcov s hsT d' hd' hmem) hpos
    simp only [hδ] at this ⊢
    linarith

/-- **Approximation bound of the framework** (common core of Lemmas 3.1 and 6.1): if all dual
constraints are `λ`-satisfied at the end of the first phase, every raise increases the dual
objective by at most `M δ(d)`, and the coverage condition of `sum_raise_le_profitOf` holds, then
`λ · LP(x) ≤ M · p(S)` for every feasible LP solution `x`. -/
theorem lam_mul_lpValue_le [Fintype D] [Fintype A] [Fintype E] (hR : R.WF I)
    (hv : I.ValidRun R Is T) {S : Finset D} (hS : S ⊆ raised Is T)
    (hcov : ∀ s < T, ∀ d' ∈ Is s, d' ∉ S →
      1 ≤ ∑ t ∈ (range T).filter (s < ·), ∑ d ∈ (Is t).filter (· ∈ S), I.weight R d' d)
    {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ s < T, ∀ d ∈ Is s, 1 + R.c d * (R.crit d).card ≤ M)
    {lam : ℝ} (hlam : ∀ d, lam * I.profit d ≤ I.lhs R.h (I.run R Is T) d)
    {x : D → ℝ} (hx : I.IsLPFeasible R.h x) :
    lam * I.lpValue x ≤ M * I.profitOf S := by
  have h1 := I.weak_duality hx (run_α_nonneg hR hv le_rfl) (run_β_nonneg hR hv le_rfl) hlam
  have h2 : (I.run R Is T).val ≤ M * ∑ s ∈ range T, ∑ d' ∈ Is s, I.amt R (I.run R Is s) d' := by
    rw [val_run, Finset.mul_sum]
    refine Finset.sum_le_sum fun s hs => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun d hd => ?_
    have := mul_le_mul_of_nonneg_left (hM s (Finset.mem_range.1 hs) d hd)
      (amt_pos hR hv (Finset.mem_range.1 hs) hd).le
    linarith
  have h3 := sum_raise_le_profitOf hR hv hS hcov
  calc lam * I.lpValue x ≤ (I.run R Is T).val := h1
    _ ≤ M * ∑ s ∈ range T, ∑ d' ∈ Is s, I.amt R (I.run R Is s) d' := h2
    _ ≤ M * I.profitOf S := mul_le_mul_of_nonneg_left h3 hM0

/-! ### The second phase -/

variable (Is T)

/-- The second phase, generic in the acceptance test `acc S d` ("adding `d` to the current
solution `S` keeps it feasible"). The stack holds `Is 0, …, Is (T-1)` with `Is (T-1)` on top;
`phase2 n` is the solution after popping the top `n` sets. All members of a popped set are tested
against the solution built before that set was popped (for independent sets this is the same as
testing them one by one). -/
def phase2 (acc : Finset D → D → Prop) [∀ S d, Decidable (acc S d)] : ℕ → Finset D
  | 0 => ∅
  | n + 1 => phase2 acc n ∪ (Is (T - 1 - n)).filter (acc (phase2 acc n))

variable {Is T}
variable (acc : Finset D → D → Prop) [∀ S d, Decidable (acc S d)]

lemma phase2_mono {m n : ℕ} (h : m ≤ n) : phase2 Is T acc m ⊆ phase2 Is T acc n := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => exact ih.trans Finset.subset_union_left

/-- The solution after popping `n` sets consists of instances raised at iterations `≥ T - n`. -/
lemma mem_phase2 {n : ℕ} (hn : n ≤ T) {d : D} (hd : d ∈ phase2 Is T acc n) :
    ∃ t, t < T ∧ T - n ≤ t ∧ d ∈ Is t := by
  induction n with
  | zero => simp [phase2] at hd
  | succ n ih =>
    rcases Finset.mem_union.1 hd with h | h
    · obtain ⟨t, h1, h2, h3⟩ := ih (by omega) h; exact ⟨t, h1, by omega, h3⟩
    · exact ⟨T - 1 - n, by omega, by omega, (Finset.mem_filter.1 h).1⟩

/-- The solution `S` produced by the second phase. -/
abbrev sol (Is : ℕ → Finset D) (T : ℕ) (acc : Finset D → D → Prop) [∀ S d, Decidable (acc S d)] :
    Finset D := phase2 Is T acc T

lemma sol_subset_raised : sol Is T acc ⊆ raised Is T := by
  intro d hd
  obtain ⟨t, ht, -, hdt⟩ := mem_phase2 acc le_rfl hd
  exact Finset.mem_biUnion.2 ⟨t, Finset.mem_range.2 ht, hdt⟩

/-- Every instance raised at iteration `t` is either in the final solution, or it failed the
acceptance test against the solution built from the iterations after `t`. -/
lemma mem_sol_or_not_acc {t : ℕ} (ht : t < T) {d : D} (hd : d ∈ Is t) :
    d ∈ sol Is T acc ∨ ¬ acc (phase2 Is T acc (T - 1 - t)) d := by
  by_cases hacc : acc (phase2 Is T acc (T - 1 - t)) d
  · left
    refine phase2_mono acc (show T - 1 - t + 1 ≤ T by omega) ?_
    refine Finset.mem_union_right _ (Finset.mem_filter.2 ⟨?_, hacc⟩)
    rwa [show T - 1 - (T - 1 - t) = t by omega]
  · exact Or.inr hacc

/-- The solution against which iteration `t` is tested consists of instances raised later. -/
lemma mem_phase2_later {t : ℕ} (ht : t < T) {d : D} (hd : d ∈ phase2 Is T acc (T - 1 - t)) :
    ∃ t', t < t' ∧ t' < T ∧ d ∈ Is t' := by
  obtain ⟨t', h1, h2, h3⟩ := mem_phase2 acc (by omega) hd
  exact ⟨t', by omega, h1, h3⟩

lemma phase2_subset_sol {t : ℕ} :
    phase2 Is T acc (T - 1 - t) ⊆ sol Is T acc :=
  phase2_mono acc (by omega)

/-- Coverage by a single later instance of the solution. -/
lemma one_le_cover_of_mem (hR : R.WF I) (_hv : I.ValidRun R Is T) {S : Finset D} {s : ℕ}
    {d' d₀ : D} {t₀ : ℕ} (hst : s < t₀) (ht₀ : t₀ < T) (hd₀ : d₀ ∈ Is t₀) (hd₀S : d₀ ∈ S)
    (hw : 1 ≤ I.weight R d' d₀) :
    1 ≤ ∑ t ∈ (range T).filter (s < ·), ∑ d ∈ (Is t).filter (· ∈ S), I.weight R d' d := by
  refine hw.trans ?_
  have h1 : I.weight R d' d₀ ≤ ∑ d ∈ (Is t₀).filter (· ∈ S), I.weight R d' d :=
    Finset.single_le_sum (f := fun d => I.weight R d' d) (fun d _ => weight_nonneg hR d' d)
      (Finset.mem_filter.2 ⟨hd₀, hd₀S⟩)
  refine h1.trans (Finset.single_le_sum (f := fun t => ∑ d ∈ (Is t).filter (· ∈ S),
    I.weight R d' d) (fun t _ => Finset.sum_nonneg fun d _ => weight_nonneg hR d' d)
    (Finset.mem_filter.2 ⟨Finset.mem_range.2 ht₀, hst⟩))

end Inst

end

end Podc.LineTreeScheduling
