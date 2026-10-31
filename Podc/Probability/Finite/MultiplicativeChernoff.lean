import Cslib.Probability.Finite.Uniform
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

-- CSLib candidate: Cslib/Probability/Finite/MultiplicativeChernoff.lean

/-!
# Multiplicative Chernoff bounds by counting

Two-sided multiplicative Chernoff bounds `Pr[|S - μ| ≥ β μ] ≤ 2 exp (-β² μ / 3)` (`0 ≤ β ≤ 1`)
on finite sample spaces with the uniform distribution, i.e. "probability by counting" as in
`Cslib.Probability.Finite.Uniform` (no measure theory). The bounds are stated as counting
inequalities `#{bad outcomes} ≤ 2 exp (-β² μ / 3) · #{outcomes}`.

## Main statements

* `sum_pow_card_filter_mem`: the exponential moment of a binomial count,
  `∑_{x : ι → X} a^{#{i | x i ∈ B}} = (|X| + (a - 1) |B|)^|ι|`.
* Analytic inequalities: `two_mul_div_two_add_le_log_one_add` (`2β/(2+β) ≤ log (1+β)`),
  `sub_mul_log_one_add_le` (`β - (1+β) log (1+β) ≤ -β²/3` on `[0,1]`),
  `neg_sub_mul_log_one_sub_le` (`-β - (1-β) log (1-β) ≤ -β²/2` on `[0,1)`).
* `card_filter_abs_sub_ge_le_of_mgf`: the abstract two-sided tail — if
  `∑_{ω ∈ G} a^{S ω} ≤ M exp (μ (a - 1))` for `0 < a ≤ 2`, then
  `#{ω ∈ G | |S ω - μ| ≥ β μ} ≤ 2 exp (-β² μ / 3) M`.
* `card_filter_abs_card_filter_mem_sub_ge_le`, `uprob_abs_card_filter_mem_sub_ge_le`: the
  multiplicative Chernoff bound for the binomial count `#{i | x i ∈ B}` of a uniform
  `x : ι → X`, with mean `μ = |B|/|X| · |ι|`.
* `sum_pow_card_firstHits_le`, `sum_pow_card_firstHits_le_exp`, `card_firstHits_abs_sub_ge_le`:
  sequential sampling. Among `K` uniform samples, the number of samples in `B ⊆ A` among the
  *first `N` samples that fall into `A`* is, on the event that there are at least `N` such
  samples, concentrated around `q N` with `q = |B|/|A|`.

## Proofs

Markov's inequality for `a^S` with `a = 1 + β` (upper tail) and `a = 1 - β` (lower tail; for
`β = 1` the lower tail is `S = 0` and `a = 2/3` is used). The analytic inequalities come from
Mathlib's `Real.sum_range_le_log_div` and `Real.log_div_le_sum_range_add` (bounds on
`log ((1 + x)/(1 - x))`). For the first `N` hits, the exponential-moment bound is proved by
induction on the number of samples, splitting off the first sample (a martingale argument in
counting form): an `A`-hit contributes a factor `a` (if in `B`) or `1`, which averages to
`|A| (1 + (a - 1) q)`, and a miss leaves the state unchanged.
-/

open Finset

namespace Cslib.Probability

/-- The moment generating function of the number of coordinates in `B`:
`∑_x a^{#{i | x i ∈ B}} = (|X| + (a - 1) |B|)^|ι|`. -/
theorem sum_pow_card_filter_mem {ι X : Type*} [Fintype ι] [DecidableEq ι] [Fintype X]
    [DecidableEq X]
    (a : ℝ) (B : Finset X) :
    ∑ x : ι → X, a ^ #(univ.filter fun i => x i ∈ B) =
      ((Fintype.card X : ℝ) + (a - 1) * #B) ^ Fintype.card ι := by
  classical
  have h1 : ∀ x : ι → X, a ^ #(univ.filter fun i => x i ∈ B) =
      ∏ i, (if x i ∈ B then a else 1) := by
    intro x
    rw [Finset.prod_ite, prod_const, prod_const_one, mul_one]
  simp_rw [h1]
  rw [← Fintype.prod_sum (fun (_ : ι) (b : X) => if b ∈ B then a else 1), prod_const, card_univ]
  congr 1
  rw [Finset.sum_ite, sum_const, sum_const, nsmul_eq_mul, nsmul_eq_mul, filter_mem_eq_inter,
    univ_inter]
  have := card_filter_add_card_filter_not (s := (univ : Finset X)) (· ∈ B)
  rw [filter_mem_eq_inter, univ_inter, card_univ] at this
  have h : ((#(univ.filter fun b => b ∉ B) : ℕ) : ℝ) = Fintype.card X - #B := by
    rw [eq_sub_iff_add_eq]; exact_mod_cast by omega
  rw [h]; ring

/-- `2β / (2 + β) ≤ log (1 + β)` for `β ≥ 0`. -/
theorem two_mul_div_two_add_le_log_one_add {β : ℝ} (hβ : 0 ≤ β) :
    2 * β / (2 + β) ≤ Real.log (1 + β) := by
  have hx0 : 0 ≤ β / (2 + β) := by positivity
  have hx1 : β / (2 + β) < 1 := by rw [div_lt_one (by positivity)]; linarith
  have h := Real.sum_range_le_log_div hx0 hx1 1
  have he : (1 + β / (2 + β)) / (1 - β / (2 + β)) = 1 + β := by
    field_simp; ring
  rw [he] at h
  simp at h
  rw [mul_div_assoc]
  linarith

/-- The analytic inequality behind the upper multiplicative Chernoff tail:
`β - (1 + β) log (1 + β) ≤ -β² / 3` for `0 ≤ β ≤ 1`. -/
theorem sub_mul_log_one_add_le {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) :
    β - (1 + β) * Real.log (1 + β) ≤ -(β ^ 2 / 3) := by
  have h := two_mul_div_two_add_le_log_one_add hβ0
  have h2 : (1 + β) * (2 * β / (2 + β)) ≤ (1 + β) * Real.log (1 + β) :=
    mul_le_mul_of_nonneg_left h (by linarith)
  have h3 : β - (1 + β) * (2 * β / (2 + β)) = -(β ^ 2 / (2 + β)) := by
    field_simp; ring
  have h4 : β ^ 2 / 3 ≤ β ^ 2 / (2 + β) :=
    div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
  linarith

/-- The analytic inequality behind the lower multiplicative Chernoff tail:
`-β - (1 - β) log (1 - β) ≤ -β² / 2` for `0 ≤ β < 1`. -/
theorem neg_sub_mul_log_one_sub_le {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    -β - (1 - β) * Real.log (1 - β) ≤ -(β ^ 2 / 2) := by
  set x := β / (2 - β) with hx
  have hx0 : 0 ≤ x := div_nonneg hβ0 (by linarith)
  have hx1 : x < 1 := by rw [hx, div_lt_one (by linarith)]; linarith
  have h := Real.log_div_le_sum_range_add hx0 hx1 0
  have he : (1 + x) / (1 - x) = (1 - β)⁻¹ := by
    have h2 : 2 - β ≠ 0 := by linarith
    have h3 : 1 - β ≠ 0 := by linarith
    have h4 : 1 - β / (2 - β) = 2 * (1 - β) / (2 - β) := by field_simp; ring
    rw [hx, h4]
    field_simp
    ring
  rw [he, Real.log_inv] at h
  simp at h
  have hlhs : -(1 - β) * Real.log (1 - β) ≤ (1 - β) * (2 * (x / (1 - x ^ 2))) := by
    have := mul_le_mul_of_nonneg_left (show -Real.log (1 - β) ≤ 2 * (x / (1 - x ^ 2)) by
      linarith) (show 0 ≤ 1 - β by linarith)
    linarith
  have hr : (1 - β) * (2 * (x / (1 - x ^ 2))) = β - β ^ 2 / 2 := by
    rw [hx]
    have : (2 - β) ≠ 0 := by linarith
    have : (2 - β) ^ 2 - β ^ 2 ≠ 0 := by nlinarith
    field_simp
    ring
  linarith

/-! ### Two-sided tail from an exponential-moment bound -/

section Tail

variable {Ω : Type*} [Fintype Ω]

/-- Markov's inequality for the exponential moment `a ^ S`, on a subevent `E` of `G`. -/
private theorem card_mul_le_of_le_pow (S : Ω → ℕ) (G E : Ω → Prop)
    [DecidablePred G] [DecidablePred E] (hEG : ∀ ω, E ω → G ω) {a c R : ℝ} (ha : 0 ≤ a)
    (hsum : ∑ ω ∈ univ.filter G, a ^ S ω ≤ R) (hc : ∀ ω, E ω → c ≤ a ^ S ω) :
    (#(univ.filter E) : ℝ) * c ≤ R := by
  calc (#(univ.filter E) : ℝ) * c = ∑ ω ∈ univ.filter E, c := by rw [sum_const, nsmul_eq_mul]
    _ ≤ ∑ ω ∈ univ.filter E, a ^ S ω := sum_le_sum fun ω hω => hc ω (mem_filter.1 hω).2
    _ ≤ ∑ ω ∈ univ.filter G, a ^ S ω := sum_le_sum_of_subset_of_nonneg
        (fun ω hω => mem_filter.2 ⟨mem_univ _, hEG ω (mem_filter.1 hω).2⟩)
        (fun _ _ _ => by positivity)
    _ ≤ R := hsum

/-- From `#E · exp t ≤ M · exp s` and `s - t ≤ u` get `#E ≤ exp u · M`. -/
private theorem le_exp_mul_of_mul_exp_le {n M s t u : ℝ} (h : n * Real.exp t ≤ M * Real.exp s)
    (hu : s - t ≤ u) (hM : 0 ≤ M) : n ≤ Real.exp u * M := by
  calc n = n * Real.exp t * Real.exp (-t) := by rw [mul_assoc, ← Real.exp_add]; simp
    _ ≤ M * Real.exp s * Real.exp (-t) := by gcongr
    _ = Real.exp (s - t) * M := by rw [mul_assoc, ← Real.exp_add, sub_eq_add_neg, mul_comm]
    _ ≤ Real.exp u * M := by gcongr

/-- **Multiplicative Chernoff bound from an exponential-moment bound (counting form).**
Let `S : Ω → ℕ` and an event `G` on a finite type, and suppose the exponential moments of `S`
restricted to `G` satisfy the Poisson-type bound `∑_{ω ∈ G} a ^ S ω ≤ M · exp (μ (a - 1))` for
`0 < a ≤ 2` (as for a sum of independent Bernoulli variables with mean `μ`, where `M` is the
number of outcomes). Then for `0 ≤ β ≤ 1` at most `2 exp (-β² μ / 3) · M` outcomes in `G` have
`|S - μ| ≥ β μ`. -/
theorem card_filter_abs_sub_ge_le_of_mgf (S : Ω → ℕ) (G : Ω → Prop) [DecidablePred G]
    {μ M : ℝ} (hμ : 0 ≤ μ)
    (hmgf : ∀ a : ℝ, 0 < a → a ≤ 2 → ∑ ω ∈ univ.filter G, a ^ S ω ≤ M * Real.exp (μ * (a - 1)))
    {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) :
    (#(univ.filter fun ω => G ω ∧ β * μ ≤ |(S ω : ℝ) - μ|) : ℝ) ≤
      2 * Real.exp (-(β ^ 2 * μ / 3)) * M := by
  classical
  have hM : 0 ≤ M := by
    have h := hmgf 1 one_pos one_le_two
    simp only [one_pow, sum_const, nsmul_eq_mul, mul_one, sub_self, mul_zero, Real.exp_zero] at h
    exact le_trans (by positivity) h
  -- upper tail: Markov with `a = 1 + β`
  have hU : (#(univ.filter fun ω => G ω ∧ (1 + β) * μ ≤ (S ω : ℝ)) : ℝ) ≤
      Real.exp (-(β ^ 2 * μ / 3)) * M := by
    have ha : 0 < 1 + β := by linarith
    have hl : 0 ≤ Real.log (1 + β) := Real.log_nonneg (by linarith)
    have h := card_mul_le_of_le_pow S G (fun ω => G ω ∧ (1 + β) * μ ≤ (S ω : ℝ))
      (fun ω h => h.1) ha.le (hmgf (1 + β) ha (by linarith))
      (c := Real.exp ((1 + β) * μ * Real.log (1 + β))) (fun ω h => by
        rw [← Real.exp_log (pow_pos ha (S ω)), Real.log_pow]
        exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right h.2 hl))
    refine le_exp_mul_of_mul_exp_le h ?_ hM
    have := mul_le_mul_of_nonneg_left (sub_mul_log_one_add_le hβ0 hβ1) hμ
    nlinarith
  -- lower tail: Markov with `a = 1 - β` (or `a = 2/3` if `β = 1`)
  have hL : (#(univ.filter fun ω => G ω ∧ (S ω : ℝ) ≤ (1 - β) * μ) : ℝ) ≤
      Real.exp (-(β ^ 2 * μ / 3)) * M := by
    rcases hβ1.lt_or_eq with hβ1 | rfl
    · have ha : 0 < 1 - β := by linarith
      have hl : Real.log (1 - β) ≤ 0 := Real.log_nonpos (by linarith) (by linarith)
      have h := card_mul_le_of_le_pow S G (fun ω => G ω ∧ (S ω : ℝ) ≤ (1 - β) * μ)
        (fun ω h => h.1) ha.le (hmgf (1 - β) ha (by linarith))
        (c := Real.exp ((1 - β) * μ * Real.log (1 - β))) (fun ω h => by
          rw [← Real.exp_log (pow_pos ha (S ω)), Real.log_pow]
          exact Real.exp_le_exp.2 (mul_le_mul_of_nonpos_right h.2 hl))
      refine le_exp_mul_of_mul_exp_le h ?_ hM
      have := mul_le_mul_of_nonneg_left (neg_sub_mul_log_one_sub_le hβ0 hβ1) hμ
      have : 0 ≤ β ^ 2 * μ := by positivity
      nlinarith
    · have ha : (0 : ℝ) < 2 / 3 := by norm_num
      have h := card_mul_le_of_le_pow S G (fun ω => G ω ∧ (S ω : ℝ) ≤ (1 - 1) * μ)
        (fun ω h => h.1) ha.le (hmgf (2 / 3) ha (by norm_num)) (c := Real.exp 0) (fun ω h => by
          have : S ω = 0 := by
            have := h.2; simp only [sub_self, zero_mul] at this; exact_mod_cast this.antisymm
              (Nat.cast_nonneg _)
          simp [this])
      refine le_exp_mul_of_mul_exp_le h ?_ hM
      linarith
  -- the event is contained in the union of the two tails
  have hsub : univ.filter (fun ω => G ω ∧ β * μ ≤ |(S ω : ℝ) - μ|) ⊆
      univ.filter (fun ω => G ω ∧ (1 + β) * μ ≤ (S ω : ℝ)) ∪
        univ.filter (fun ω => G ω ∧ (S ω : ℝ) ≤ (1 - β) * μ) := by
    intro ω hω
    simp only [mem_filter, mem_univ, true_and, mem_union] at hω ⊢
    rcases le_abs'.1 hω.2 with h | h
    · right; exact ⟨hω.1, by linarith⟩
    · left; exact ⟨hω.1, by linarith⟩
  have h1 := card_le_card hsub
  have h2 := card_union_le (univ.filter (fun ω => G ω ∧ (1 + β) * μ ≤ (S ω : ℝ)))
    (univ.filter (fun ω => G ω ∧ (S ω : ℝ) ≤ (1 - β) * μ))
  have h3 : (#(univ.filter fun ω => G ω ∧ β * μ ≤ |(S ω : ℝ) - μ|) : ℝ) ≤
      (#(univ.filter (fun ω => G ω ∧ (1 + β) * μ ≤ (S ω : ℝ))) : ℝ) +
        #(univ.filter (fun ω => G ω ∧ (S ω : ℝ) ≤ (1 - β) * μ)) := by
    exact_mod_cast h1.trans h2
  linarith

end Tail

/-! ### Independent uniform coordinates (binomial counts) -/

section Binomial

variable {ι X : Type*} [Fintype ι] [DecidableEq ι] [Fintype X] [DecidableEq X]

/-- Exponential-moment bound for the number of coordinates in `B`:
`∑_x a^{#{i | x i ∈ B}} ≤ |X|^|ι| · exp (μ (a - 1))` with `μ = |B| / |X| · |ι|`. -/
theorem sum_pow_card_filter_mem_le_exp [Nonempty X] (B : Finset X) {a : ℝ} (ha : 0 ≤ a) :
    ∑ x : ι → X, a ^ #(univ.filter fun i => x i ∈ B) ≤
      (Fintype.card X : ℝ) ^ Fintype.card ι *
        Real.exp ((#B / Fintype.card X : ℝ) * Fintype.card ι * (a - 1)) := by
  have hX : (0 : ℝ) < Fintype.card X := by exact_mod_cast Fintype.card_pos
  have hp0 : (0 : ℝ) ≤ #B / Fintype.card X := by positivity
  have hp1 : (#B / Fintype.card X : ℝ) ≤ 1 := by
    rw [div_le_one hX]; exact_mod_cast card_le_univ B
  rw [sum_pow_card_filter_mem]
  have he : (Fintype.card X : ℝ) + (a - 1) * #B =
      Fintype.card X * (1 + (a - 1) * (#B / Fintype.card X)) := by
    field_simp
  have hexp : Real.exp ((#B / Fintype.card X : ℝ) * Fintype.card ι * (a - 1)) =
      Real.exp ((a - 1) * (#B / Fintype.card X)) ^ Fintype.card ι := by
    rw [← Real.exp_nat_mul]; ring_nf
  rw [he, mul_pow, hexp]
  gcongr
  · nlinarith
  · linarith [Real.add_one_le_exp ((a - 1) * (#B / Fintype.card X))]

/-- **Multiplicative Chernoff bound for a binomial count (counting form).** For `x : ι → X`
uniform, the number `#{i | x i ∈ B}` of coordinates in `B` has mean `μ = |B| / |X| · |ι|`, and
for `0 ≤ β ≤ 1` it deviates from `μ` by at least `β μ` for at most `2 exp (-β² μ / 3) · |X|^|ι|`
of the `x`. -/
theorem card_filter_abs_card_filter_mem_sub_ge_le [Nonempty X] (B : Finset X) {μ : ℝ}
    (hμ : μ = #B / Fintype.card X * Fintype.card ι) {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) :
    (#(univ.filter fun x : ι → X => β * μ ≤ |(#(univ.filter fun i => x i ∈ B) : ℝ) - μ|) : ℝ) ≤
      2 * Real.exp (-(β ^ 2 * μ / 3)) * (Fintype.card X : ℝ) ^ Fintype.card ι := by
  have hμ0 : 0 ≤ μ := by rw [hμ]; positivity
  have h := card_filter_abs_sub_ge_le_of_mgf (fun x : ι → X => #(univ.filter fun i => x i ∈ B))
    (fun _ => True) hμ0 (M := (Fintype.card X : ℝ) ^ Fintype.card ι) (fun a ha _ => by
      rw [filter_true, hμ, mul_comm]
      exact (sum_pow_card_filter_mem_le_exp B ha.le).trans_eq (by ring_nf)) hβ0 hβ1
  simpa only [true_and] using h

/-- **Multiplicative Chernoff bound for a binomial count**, probability form: for `x : ι → X`
uniform and `μ = |B| / |X| · |ι|`, `Pr[|#{i | x i ∈ B} - μ| ≥ β μ] ≤ 2 exp (-β² μ / 3)` for
`0 ≤ β ≤ 1`. -/
theorem uprob_abs_card_filter_mem_sub_ge_le [Nonempty X] (B : Finset X) {μ : ℝ}
    (hμ : μ = #B / Fintype.card X * Fintype.card ι) {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) :
    uprob (fun x : ι → X => β * μ ≤ |(#(univ.filter fun i => x i ∈ B) : ℝ) - μ|) ≤
      2 * Real.exp (-(β ^ 2 * μ / 3)) := by
  classical
  have hX : (0 : ℝ) < (Fintype.card X : ℝ) ^ Fintype.card ι := by
    have : (0 : ℝ) < Fintype.card X := by exact_mod_cast Fintype.card_pos
    positivity
  rw [uprob_eq_card_filter, Fintype.card_fun, Nat.cast_pow, div_le_iff₀ hX]
  convert card_filter_abs_card_filter_mem_sub_ge_le B hμ hβ0 hβ1

end Binomial

/-! ### Sequential sampling: the first `N` hits of `A` -/

section FirstHits

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- The number of samples falling into `A`. -/
private def nHits (A : Finset X) {K : ℕ} (x : Fin K → X) : ℕ := #(univ.filter fun i => x i ∈ A)

/-- The number of samples falling into `B` among the first `N` samples that fall into `A`. -/
private def nFirst (A B : Finset X) (N : ℕ) {K : ℕ} (x : Fin K → X) : ℕ :=
  #(univ.filter fun i => x i ∈ B ∧ #(univ.filter fun k => k < i ∧ x k ∈ A) < N)

omit [DecidableEq X] in
/-- Splitting a sum over `(k+1)`-tuples into the first entry and the rest. -/
private lemma sum_fun_succ' {M : Type*} [AddCommMonoid M] {k : ℕ} (F : (Fin (k + 1) → X) → M) :
    ∑ g, F g = ∑ y, ∑ g : Fin k → X, F (Fin.cons y g) := by
  rw [← (Fin.consEquiv fun _ => X).sum_comp, Fintype.sum_prod_type]
  rfl

omit [Fintype X] in
private lemma nHits_cons (A : Finset X) {K : ℕ} (v : X) (x : Fin K → X) :
    nHits A (Fin.cons v x : Fin (K + 1) → X) = (if v ∈ A then 1 else 0) + nHits A x := by
  unfold nHits
  rw [Fin.card_filter_univ_succ']
  simp

omit [Fintype X] in
private lemma nFirst_cons (A B : Finset X) (N : ℕ) {K : ℕ} (v : X) (x : Fin K → X) :
    nFirst A B N (Fin.cons v x : Fin (K + 1) → X) = (if v ∈ B ∧ 0 < N then 1 else 0) +
      #(univ.filter fun i => x i ∈ B ∧
        (if v ∈ A then 1 else 0) + #(univ.filter fun k => k < i ∧ x k ∈ A) < N) := by
  unfold nFirst
  rw [Fin.card_filter_univ_succ']
  congr 1
  · simp
  · congr 1
    apply filter_congr
    intro i _
    rw [Fin.card_filter_univ_succ']
    simp [Fin.succ_lt_succ_iff]

omit [Fintype X] in
private lemma nFirst_zero (A B : Finset X) {K : ℕ} (x : Fin K → X) : nFirst A B 0 x = 0 := by
  simp [nFirst]

private lemma sum_ite_pow_nFirst_le {A B : Finset X} (hBA : B ⊆ A) (hA : A.Nonempty) {a : ℝ}
    (ha : 0 < a) (K N : ℕ) :
    ∑ x : Fin K → X, (if N ≤ nHits A x then a ^ nFirst A B N x else 0) ≤
      (Fintype.card X : ℝ) ^ K * (1 + (a - 1) * (#B / #A)) ^ N := by
  set c : ℝ := 1 + (a - 1) * (#B / #A) with hc
  have hApos : (0 : ℝ) < #A := by exact_mod_cast hA.card_pos
  have hq0 : (0 : ℝ) ≤ #B / #A := by positivity
  have hq1 : (#B / #A : ℝ) ≤ 1 := by rw [div_le_one hApos]; exact_mod_cast card_le_card hBA
  have hc0 : 0 ≤ c := by nlinarith
  induction K generalizing N with
  | zero =>
    rcases N with _ | N
    · simp [nFirst_zero]
    · simp [nHits]
      positivity
  | succ K ih =>
    rcases N with _ | N
    · simp [nFirst_zero]
    rw [sum_fun_succ']
    -- the bound for each first sample `v`
    have hv : ∀ v : X, ∑ x : Fin K → X, (if N + 1 ≤ nHits A (Fin.cons v x : Fin (K + 1) → X)
        then a ^ nFirst A B (N + 1) (Fin.cons v x : Fin (K + 1) → X) else 0) ≤
        (Fintype.card X : ℝ) ^ K * c ^ N *
          (c + (a - 1) * (if v ∈ B then 1 else 0) + (1 - c) * (if v ∈ A then 1 else 0)) := by
      intro v
      simp only [nHits_cons, nFirst_cons]
      by_cases hvA : v ∈ A
      · by_cases hvB : v ∈ B
        · have : ∀ x : Fin K → X, (if N + 1 ≤ (if v ∈ A then 1 else 0) + nHits A x then
              (a : ℝ) ^ ((if v ∈ B ∧ 0 < N + 1 then 1 else 0) + #(univ.filter fun i => x i ∈ B ∧
                (if v ∈ A then 1 else 0) + #(univ.filter fun k => k < i ∧ x k ∈ A) < N + 1))
              else 0) = a * (if N ≤ nHits A x then a ^ nFirst A B N x else 0) := by
            intro x
            simp only [hvA, hvB, ite_true, true_and, Nat.succ_pos]
            simp only [nFirst, add_comm 1, Nat.add_lt_add_iff_right, Nat.add_le_add_iff_right]
            split_ifs <;> ring
          rw [sum_congr rfl fun x _ => this x, ← mul_sum]
          simp only [hvA, hvB, ite_true]
          nlinarith [ih N, pow_nonneg hc0 N,
            pow_nonneg (show (0 : ℝ) ≤ Fintype.card X by positivity) K]
        · have : ∀ x : Fin K → X, (if N + 1 ≤ (if v ∈ A then 1 else 0) + nHits A x then
              (a : ℝ) ^ ((if v ∈ B ∧ 0 < N + 1 then 1 else 0) + #(univ.filter fun i => x i ∈ B ∧
                (if v ∈ A then 1 else 0) + #(univ.filter fun k => k < i ∧ x k ∈ A) < N + 1))
              else 0) = (if N ≤ nHits A x then a ^ nFirst A B N x else 0) := by
            intro x
            simp only [hvA, hvB, ite_true, false_and, ite_false, zero_add]
            simp only [nFirst, add_comm 1, Nat.add_lt_add_iff_right, Nat.add_le_add_iff_right]
          rw [sum_congr rfl fun x _ => this x]
          simp only [hvA, hvB, ite_true, ite_false]
          linarith [ih N]
      · have hvB : v ∉ B := fun h => hvA (hBA h)
        have : ∀ x : Fin K → X, (if N + 1 ≤ (if v ∈ A then 1 else 0) + nHits A x then
            (a : ℝ) ^ ((if v ∈ B ∧ 0 < N + 1 then 1 else 0) + #(univ.filter fun i => x i ∈ B ∧
              (if v ∈ A then 1 else 0) + #(univ.filter fun k => k < i ∧ x k ∈ A) < N + 1))
            else 0) = (if N + 1 ≤ nHits A x then a ^ nFirst A B (N + 1) x else 0) := by
          intro x
          simp only [hvA, hvB, ite_false, false_and, zero_add]
          rfl
        rw [sum_congr rfl fun x _ => this x]
        simp only [hvA, hvB, ite_false]
        have := ih (N + 1)
        rw [pow_succ] at this
        linarith
    refine (sum_le_sum fun v _ => hv v).trans_eq ?_
    rw [← mul_sum, sum_add_distrib, sum_add_distrib, ← mul_sum, ← mul_sum, sum_boole, sum_boole,
      sum_const, card_univ, filter_mem_eq_inter, filter_mem_eq_inter, univ_inter, univ_inter,
      pow_succ, pow_succ]
    simp only [nsmul_eq_mul]
    have : (1 - c) * (#A : ℝ) = -((a - 1) * #B) := by
      rw [hc]; field_simp; ring
    linear_combination (Fintype.card X : ℝ) ^ K * c ^ N * this

/-- **Exponential moment of the first `N` hits.** Draw `K` independent uniform samples
`x : Fin K → X` and look at the samples that fall into `A`; let `Z x = #{i | x i ∈ A}` be their
number and `Y x = #{i | x i ∈ B ∧ #{k < i | x k ∈ A} < N}` the number of samples in `B ⊆ A` among
the first `N` of them. Conditioned on the `A`-hits, each is in `B` with probability `q = |B|/|A|`,
so on the event `N ≤ Z` the count `Y` is a sum of `N` independent Bernoulli(`q`) variables:
`∑_{x, N ≤ Z x} a ^ Y x ≤ |X|^K (1 + (a - 1) q)^N` for `a > 0`. -/
theorem sum_pow_card_firstHits_le {A B : Finset X} (hBA : B ⊆ A) (hA : A.Nonempty) {a : ℝ}
    (ha : 0 < a) (N K : ℕ) :
    ∑ x ∈ univ.filter (fun x : Fin K → X => N ≤ #(univ.filter fun i => x i ∈ A)),
        a ^ #(univ.filter fun i => x i ∈ B ∧ #(univ.filter fun k => k < i ∧ x k ∈ A) < N) ≤
      (Fintype.card X : ℝ) ^ K * (1 + (a - 1) * (#B / #A)) ^ N := by
  rw [sum_filter]
  exact sum_ite_pow_nFirst_le hBA hA ha K N

/-- `sum_pow_card_firstHits_le` with `1 + t ≤ exp t`:
`∑_{x, N ≤ Z x} a ^ Y x ≤ |X|^K exp (q N (a - 1))`. -/
theorem sum_pow_card_firstHits_le_exp {A B : Finset X} (hBA : B ⊆ A) (hA : A.Nonempty) {a : ℝ}
    (ha : 0 < a) (N K : ℕ) :
    ∑ x ∈ univ.filter (fun x : Fin K → X => N ≤ #(univ.filter fun i => x i ∈ A)),
        a ^ #(univ.filter fun i => x i ∈ B ∧ #(univ.filter fun k => k < i ∧ x k ∈ A) < N) ≤
      (Fintype.card X : ℝ) ^ K * Real.exp ((#B / #A : ℝ) * N * (a - 1)) := by
  refine (sum_pow_card_firstHits_le hBA hA ha N K).trans ?_
  have hApos : (0 : ℝ) < #A := by exact_mod_cast hA.card_pos
  have hq0 : (0 : ℝ) ≤ #B / #A := by positivity
  have hq1 : (#B / #A : ℝ) ≤ 1 := by rw [div_le_one hApos]; exact_mod_cast card_le_card hBA
  have hexp : Real.exp ((#B / #A : ℝ) * N * (a - 1)) = Real.exp ((a - 1) * (#B / #A)) ^ N := by
    rw [← Real.exp_nat_mul]; ring_nf
  rw [hexp]
  gcongr
  · nlinarith
  · linarith [Real.add_one_le_exp ((a - 1) * (#B / #A))]

/-- **Chernoff bound for the first `N` hits (counting form).** With `K` uniform samples
`x : Fin K → X`, `Z x = #{i | x i ∈ A}` and `Y x = #{i | x i ∈ B ∧ #{k < i | x k ∈ A} < N}` (the
number of samples in `B ⊆ A` among the first `N` samples that fall into `A`), and
`q = |B| / |A|`: for `0 ≤ β ≤ 1`, at most `2 exp (-β² q N / 3) · |X|^K` of the `x` have at least
`N` hits in `A` and `|Y x - q N| ≥ β q N`. -/
theorem card_firstHits_abs_sub_ge_le {A B : Finset X} (hBA : B ⊆ A) (hA : A.Nonempty)
    (N K : ℕ) {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) :
    (#(univ.filter fun x : Fin K → X => N ≤ #(univ.filter fun i => x i ∈ A) ∧
        β * ((#B / #A : ℝ) * N) ≤
          |(#(univ.filter fun i => x i ∈ B ∧ #(univ.filter fun k => k < i ∧ x k ∈ A) < N) : ℝ)
            - (#B / #A : ℝ) * N|) : ℝ) ≤
      2 * Real.exp (-(β ^ 2 * ((#B / #A : ℝ) * N) / 3)) * (Fintype.card X : ℝ) ^ K :=
  card_filter_abs_sub_ge_le_of_mgf _ _ (by positivity)
    (fun a ha _ => (sum_pow_card_firstHits_le_exp hBA hA ha N K).trans_eq (by ring_nf)) hβ0 hβ1

end FirstHits

end Cslib.Probability
