import Papers.PODC2018.LocalSamplingCounting.Basic

-- CSLib candidate: sequential sampling from approximate marginals, coupling bound
-- (`Cslib/Probability/Finite/SequentialSampler.lean`).

/-!
# Sequential sampling from (approximate) marginals (§3, Claim 4.5)

The sequential sampler scans the vertices in an order `l` (provided by an adversary) and, at a
free vertex `v` with current pinning `ρ` (the instance `τ ∧ σ_{i-1}`), draws `σ(v)` from the
distribution `A ρ v` returned by an inference algorithm. `seqProb A l ρ σ` is the probability
that it outputs the configuration `σ` (the product formula (10)).

* `seqProb_marg`: with the exact marginals the sampler outputs exactly `μ^τ` (chain rule).
* `theorem_3_2_tv`: per-step TV error `ε` ⇒ output TV error `≤ |l| ε`; with `ε = δ/n` this is
  the bound `d_TV(μ̂, μ^τ) ≤ δ` of the proof of Theorem 3.2.
* `claim_4_5`: per-step multiplicative error `ε` ⇒ pointwise multiplicative error `|l| ε`.
* `theorem_3_4_tv`: the inequality chain of the proof of Theorem 3.4.
-/

set_option linter.unusedSectionVars false

namespace Podc.LocalSamplingCounting

open Finset

open scoped Classical

variable {V S : Type*} [Fintype V] [DecidableEq V] [Fintype S] [DecidableEq S]

/-- Probability that the sequential sampler, run with the marginal oracle `A` along the vertex
list `l` starting from the pinning `ρ`, outputs the configuration `σ`. At the end every vertex must
be pinned. -/
noncomputable def seqProb (A : Pin V S → V → S → ℝ) : List V → Pin V S → (V → S) → ℝ
  | [], ρ, σ => if ∀ v, ρ v = some (σ v) then 1 else 0
  | v :: l, ρ, σ =>
    if ρ v = none then A ρ v (σ v) * seqProb A l (Function.update ρ v (some (σ v))) σ
    else seqProb A l ρ σ

variable {w : (V → S) → ℝ}

lemma seqProb_nonneg {A : Pin V S → V → S → ℝ} (hA : ∀ ρ v c, 0 ≤ A ρ v c) :
    ∀ (l : List V) (ρ : Pin V S) (σ : V → S), 0 ≤ seqProb A l ρ σ
  | [], ρ, σ => by unfold seqProb; split_ifs <;> norm_num
  | v :: l, ρ, σ => by
    unfold seqProb; split_ifs
    · exact mul_nonneg (hA _ _ _) (seqProb_nonneg hA l _ σ)
    · exact seqProb_nonneg hA l ρ σ

/-- The output vanishes off the configurations consistent with the starting pinning. -/
lemma seqProb_eq_zero_of_not_cons {A : Pin V S → V → S → ℝ} :
    ∀ (l : List V) (ρ : Pin V S) (σ : V → S), ¬ Cons σ ρ → seqProb A l ρ σ = 0
  | [], ρ, σ, h => by
    unfold seqProb
    rw [if_neg]; intro h'; exact h fun v c hv => by rw [h' v] at hv; exact Option.some_inj.1 hv
  | v :: l, ρ, σ, h => by
    unfold seqProb; split_ifs with hv
    · rw [seqProb_eq_zero_of_not_cons l _ σ (fun h' => h ((cons_update_of_none hv).1 h').1),
        mul_zero]
    · exact seqProb_eq_zero_of_not_cons l ρ σ h

/-- The sampler's output is a sub-probability distribution. -/
lemma sum_seqProb_le {A : Pin V S → V → S → ℝ} (hA : ∀ ρ v c, 0 ≤ A ρ v c)
    (hA1 : ∀ ρ v, ∑ c, A ρ v c ≤ 1) :
    ∀ (l : List V) (ρ : Pin V S), ∑ σ, seqProb A l ρ σ ≤ 1
  | [], ρ => by
    unfold seqProb
    by_cases h : ∃ σ₀ : V → S, ∀ v, ρ v = some (σ₀ v)
    · obtain ⟨σ₀, h₀⟩ := h
      rw [Finset.sum_eq_single σ₀]
      · simp [h₀]
      · intro σ _ hne; rw [if_neg]; intro h'
        exact hne (funext fun v => Option.some_inj.1 ((h' v).symm.trans (h₀ v)))
      · simp
    · push_neg at h
      rw [Finset.sum_eq_zero]; · norm_num
      intro σ _; rw [if_neg]; push_neg; exact h σ
  | v :: l, ρ => by
    unfold seqProb
    by_cases hv : ρ v = none
    · simp only [hv, if_true]
      rw [← Finset.sum_fiberwise (g := fun σ => σ v)]
      refine le_trans (sum_le_sum fun c _ => ?_) (hA1 ρ v)
      calc ∑ σ ∈ univ.filter (fun σ => σ v = c),
            A ρ v (σ v) * seqProb A l (Function.update ρ v (some (σ v))) σ
          = A ρ v c * ∑ σ ∈ univ.filter (fun σ => σ v = c),
              seqProb A l (Function.update ρ v (some c)) σ := by
            rw [Finset.mul_sum]
            exact sum_congr rfl fun σ hσ => by rw [(mem_filter.1 hσ).2]
        _ ≤ A ρ v c * 1 := by
            gcongr
            · exact hA _ _ _
            · exact (sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
                (fun σ _ _ => seqProb_nonneg hA l _ σ)).trans (sum_seqProb_le hA hA1 l _)
        _ = A ρ v c := mul_one _
    · simp only [hv, if_false]; exact sum_seqProb_le hA hA1 l ρ

/-- **Chain rule.** Run with the exact conditional marginals, the sequential sampler outputs
exactly `μ^ρ`, for every order `l` that visits all free vertices. -/
theorem seqProb_marg (hw : ∀ σ, 0 ≤ w σ) :
    ∀ (l : List V) (ρ : Pin V S), Feasible w ρ → (∀ v, ρ v = none → v ∈ l) →
      ∀ σ, seqProb (marg w) l ρ σ = cond w ρ σ
  | [], ρ, hf, hl, σ => by
    have htot : ∀ v, ρ v ≠ none := fun v h => by simpa using hl v h
    unfold seqProb cond
    by_cases hc : Cons σ ρ
    · have h1 : ∀ v, ρ v = some (σ v) := fun v => by
        obtain ⟨c, hc'⟩ := Option.ne_none_iff_exists'.1 (htot v); rw [hc', hc v c hc']
      have hZ : Z w ρ = w σ := by
        unfold Z
        rw [Finset.sum_eq_single σ]
        · simp [hc]
        · intro σ' _ hne; rw [if_neg]; intro h'
          exact hne (funext fun v => by
            have := h' v (σ v) (h1 v); exact this)
        · simp
      have hpos : 0 < w σ := hZ ▸ hf
      simp [h1, hc, hZ, hpos.ne']
    · rw [if_neg hc, if_neg]; intro h'; exact hc fun v c hv => by
        rw [h' v] at hv; exact Option.some_inj.1 hv
  | v :: l, ρ, hf, hl, σ => by
    unfold seqProb
    by_cases hv : ρ v = none
    · simp only [hv, if_true]
      have hl' : ∀ u, Function.update ρ v (some (σ v)) u = none → u ∈ l := by
        intro u hu
        by_cases huv : u = v
        · subst huv; simp at hu
        · rw [Function.update_of_ne huv] at hu
          rcases List.mem_cons.1 (hl u hu) with h | h
          · exact absurd h huv
          · exact h
      by_cases hf' : Feasible w (Function.update ρ v (some (σ v)))
      · rw [seqProb_marg hw l _ hf' hl' σ, marg_eq_div hv]
        unfold cond
        by_cases hc : Cons σ ρ
        · have hc' : Cons σ (Function.update ρ v (some (σ v))) :=
            (cons_update_of_none hv).2 ⟨hc, rfl⟩
          rw [if_pos hc', if_pos hc]
          field_simp [hf'.ne', hf.ne']
        · have hc' : ¬ Cons σ (Function.update ρ v (some (σ v))) :=
            fun h => hc ((cons_update_of_none hv).1 h).1
          rw [if_neg hc', if_neg hc, mul_zero]
      · rw [marg_eq_zero_of_not_feasible hw hv hf', zero_mul]
        unfold cond
        split_ifs with hc
        · have hc' : Cons σ (Function.update ρ v (some (σ v))) :=
            (cons_update_of_none hv).2 ⟨hc, rfl⟩
          have := le_Z_of_cons hw hc'
          rw [(not_feasible_iff hw).1 hf'] at this
          rw [le_antisymm this (hw σ), zero_div]
        · rfl
    · simp only [hv, if_false]
      refine seqProb_marg hw l ρ hf (fun u hu => ?_) σ
      rcases List.mem_cons.1 (hl u hu) with h | h
      · subst h; exact absurd hu hv
      · exact h

/-- One step of the coupling argument: `|a x - b y| ≤ |a - b| x + b |x - y|`. -/
private lemma abs_mul_sub_mul_le {a b x y : ℝ} (hx : 0 ≤ x) (hb : 0 ≤ b) :
    |a * x - b * y| ≤ |a - b| * x + b * |x - y| := by
  have : a * x - b * y = (a - b) * x + b * (x - y) := by ring
  rw [this]
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_mul, abs_of_nonneg hx, abs_of_nonneg hb]

/-- The ℓ¹ form of the coupling bound (induction on the scan). -/
lemma sum_abs_seqProb_sub_le (hw : ∀ σ, 0 ≤ w σ) {A : Pin V S → V → S → ℝ}
    (hA : ∀ ρ v c, 0 ≤ A ρ v c) (hA1 : ∀ ρ v, ∑ c, A ρ v c ≤ 1) {ε : ℝ} (hε : 0 ≤ ε)
    (hacc : ∀ ρ v, Feasible w ρ → ρ v = none → tv (A ρ v) (marg w ρ v) ≤ ε) :
    ∀ (l : List V) (ρ : Pin V S), Feasible w ρ →
      ∑ σ, |seqProb A l ρ σ - seqProb (marg w) l ρ σ| ≤ 2 * (l.length * ε)
  | [], ρ, _ => by simp [seqProb]
  | v :: l, ρ, hf => by
    unfold seqProb
    by_cases hv : ρ v = none
    · simp only [hv, if_true]
      set μ := marg w ρ v
      have key : ∀ c, ∑ σ ∈ univ.filter (fun σ => σ v = c),
          |A ρ v (σ v) * seqProb A l (Function.update ρ v (some (σ v))) σ -
            μ (σ v) * seqProb (marg w) l (Function.update ρ v (some (σ v))) σ|
          ≤ |A ρ v c - μ c| + μ c * (2 * (l.length * ε)) := by
        intro c
        set ρc := Function.update ρ v (some c)
        calc _ = ∑ σ ∈ univ.filter (fun σ => σ v = c),
              |A ρ v c * seqProb A l ρc σ - μ c * seqProb (marg w) l ρc σ| :=
              sum_congr rfl fun σ hσ => by rw [(mem_filter.1 hσ).2]
          _ ≤ ∑ σ ∈ univ.filter (fun σ => σ v = c),
              (|A ρ v c - μ c| * seqProb A l ρc σ +
                μ c * |seqProb A l ρc σ - seqProb (marg w) l ρc σ|) :=
              sum_le_sum fun σ _ => abs_mul_sub_mul_le (seqProb_nonneg hA l ρc σ)
                (marg_nonneg hw ρ v c)
          _ = |A ρ v c - μ c| * ∑ σ ∈ univ.filter (fun σ => σ v = c), seqProb A l ρc σ +
                μ c * ∑ σ ∈ univ.filter (fun σ => σ v = c),
                  |seqProb A l ρc σ - seqProb (marg w) l ρc σ| := by
              rw [sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
          _ ≤ |A ρ v c - μ c| * 1 + μ c * (2 * (l.length * ε)) := by
              gcongr ?_ + ?_
              · exact mul_le_mul_of_nonneg_left ((sum_le_sum_of_subset_of_nonneg
                  (filter_subset _ _) (fun σ _ _ => seqProb_nonneg hA l _ σ)).trans
                  (sum_seqProb_le hA hA1 l _)) (abs_nonneg _)
              · rcases (marg_nonneg hw ρ v c).lt_or_eq with hpos | hzero
                · exact mul_le_mul_of_nonneg_left ((sum_le_sum_of_subset_of_nonneg
                    (filter_subset _ _) (fun σ _ _ => abs_nonneg _)).trans
                    (sum_abs_seqProb_sub_le hw hA hA1 hε hacc l ρc
                      ((feasible_update_iff hw hf hv c).2 hpos))) hpos.le
                · show marg w ρ v c * _ ≤ marg w ρ v c * _
                  rw [← hzero]; simp
          _ = |A ρ v c - μ c| + μ c * (2 * (l.length * ε)) := by rw [mul_one]
      rw [← Finset.sum_fiberwise (g := fun σ => σ v)]
      refine (sum_le_sum fun c _ => key c).trans ?_
      rw [sum_add_distrib, ← Finset.sum_mul, sum_marg hf v, one_mul]
      have htv : ∑ c, |A ρ v c - μ c| ≤ 2 * ε := by
        have := hacc ρ v hf hv; unfold tv at this; linarith
      simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
      linarith
    · simp only [hv, if_false]
      refine (sum_abs_seqProb_sub_le hw hA hA1 hε hacc l ρ hf).trans ?_
      simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
      nlinarith

/-- **Theorem 3.2 (sampler accuracy).** If at every feasible pinning the oracle `A` returns, at
every free vertex, a (sub-)distribution within total variation `ε` of the true conditional
marginal, then the sequential sampler along any order `l` visiting all free vertices outputs a
distribution within total variation `|l| ε` of the target `μ^τ`. (The oracle may behave
arbitrarily on infeasible pinnings, which the sampler can reach after an approximation error.) -/
theorem theorem_3_2_tv (hw : ∀ σ, 0 ≤ w σ) {A : Pin V S → V → S → ℝ}
    (hA : ∀ ρ v c, 0 ≤ A ρ v c) (hA1 : ∀ ρ v, ∑ c, A ρ v c ≤ 1) {ε : ℝ} (hε : 0 ≤ ε)
    (hacc : ∀ ρ v, Feasible w ρ → ρ v = none → tv (A ρ v) (marg w ρ v) ≤ ε)
    {τ : Pin V S} (hτ : Feasible w τ) (l : List V) (hl : ∀ v, τ v = none → v ∈ l) :
    tv (seqProb A l τ) (cond w τ) ≤ l.length * ε := by
  have h := sum_abs_seqProb_sub_le hw hA hA1 hε hacc l τ hτ
  unfold tv
  have : (fun σ => seqProb (marg w) l τ σ) = cond w τ := funext (seqProb_marg hw l τ hτ hl)
  rw [← this]
  linarith

/-- **Theorem 3.2**, in the paper's parameters: scanning all `n` vertices in an arbitrary order
with an inference oracle of TV error `δ / n` yields a sample within TV distance `δ` of `μ^τ`. -/
theorem theorem_3_2 (hw : ∀ σ, 0 ≤ w σ) {A : Pin V S → V → S → ℝ}
    (hA : ∀ ρ v, IsDist (A ρ v)) {δ : ℝ} (hδ : 0 ≤ δ)
    (hacc : ∀ ρ v, Feasible w ρ → ρ v = none →
      tv (A ρ v) (marg w ρ v) ≤ δ / Fintype.card V)
    {τ : Pin V S} (hτ : Feasible w τ) (l : List V) (hnd : l.Nodup) (hall : ∀ v, v ∈ l) :
    tv (seqProb A l τ) (cond w τ) ≤ δ := by
  have hlen : l.length = Fintype.card V := by
    rw [← List.toFinset_card_of_nodup hnd]
    congr 1; ext v; simp [hall v]
  have := theorem_3_2_tv hw (fun ρ v c => (hA ρ v).1 c) (fun ρ v => (hA ρ v).2.le)
    (div_nonneg hδ (Nat.cast_nonneg _)) hacc hτ l (fun v _ => hall v)
  rw [hlen] at this
  rcases Nat.eq_zero_or_pos (Fintype.card V) with h0 | hpos
  · rw [h0] at this; simp at this; linarith
  · rwa [mul_div_cancel₀ _ (by exact_mod_cast hpos.ne')] at this

/-- Pointwise multiplicative comparison of the sampler with the exact chain rule. -/
lemma seqProb_multClose (hw : ∀ σ, 0 ≤ w σ) {A : Pin V S → V → S → ℝ} {ε : ℝ} (hε : 0 ≤ ε)
    (hacc : ∀ ρ v, Feasible w ρ → ρ v = none → MultClose (A ρ v) (marg w ρ v) ε) :
    ∀ (l : List V) (ρ : Pin V S), Feasible w ρ → ∀ σ,
      Real.exp (-(l.length * ε)) * seqProb (marg w) l ρ σ ≤ seqProb A l ρ σ ∧
      seqProb A l ρ σ ≤ Real.exp (l.length * ε) * seqProb (marg w) l ρ σ
  | [], ρ, _, σ => by simp [seqProb]
  | v :: l, ρ, hf, σ => by
    have hP0 : ∀ ρ' σ', 0 ≤ seqProb (marg w) l ρ' σ' := seqProb_nonneg (marg_nonneg hw) l
    unfold seqProb
    simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
    by_cases hv : ρ v = none
    · simp only [hv, if_true]
      set c := σ v
      obtain ⟨h1, h2⟩ := hacc ρ v hf hv c
      rcases (marg_nonneg hw ρ v c).lt_or_eq with hpos | hzero
      · obtain ⟨h3, h4⟩ := seqProb_multClose hw hε hacc l _
          ((feasible_update_iff hw hf hv c).2 hpos) σ
        have e1 : Real.exp (-((l.length + 1) * ε)) =
            Real.exp (-ε) * Real.exp (-(l.length * ε)) := by
          rw [← Real.exp_add]; ring_nf
        have e2 : Real.exp ((l.length + 1) * ε) = Real.exp ε * Real.exp (l.length * ε) := by
          rw [← Real.exp_add]; ring_nf
        have hA0 : 0 ≤ A ρ v c :=
          le_trans (mul_nonneg (Real.exp_pos _).le (marg_nonneg hw ρ v c)) h1
        constructor
        · rw [e1]
          calc Real.exp (-ε) * Real.exp (-(l.length * ε)) *
                (marg w ρ v c * seqProb (marg w) l (Function.update ρ v (some c)) σ)
              = (Real.exp (-ε) * marg w ρ v c) *
                (Real.exp (-(l.length * ε)) *
                  seqProb (marg w) l (Function.update ρ v (some c)) σ) := by ring
            _ ≤ A ρ v c * seqProb A l (Function.update ρ v (some c)) σ :=
                mul_le_mul h1 h3 (mul_nonneg (Real.exp_pos _).le (hP0 _ _)) hA0
        · rw [e2]
          calc A ρ v c * seqProb A l (Function.update ρ v (some c)) σ
              ≤ (Real.exp ε * marg w ρ v c) *
                (Real.exp (l.length * ε) *
                  seqProb (marg w) l (Function.update ρ v (some c)) σ) :=
                mul_le_mul h2 h4 (le_trans (mul_nonneg (Real.exp_pos _).le (hP0 _ _)) h3)
                  (mul_nonneg (Real.exp_pos _).le (marg_nonneg hw ρ v c))
            _ = _ := by ring
      · have hA0 : A ρ v c = 0 := by
          rw [← hzero] at h1 h2; simp at h1 h2; linarith
        rw [hA0, ← hzero]; simp
    · simp only [hv, if_false]
      obtain ⟨h3, h4⟩ := seqProb_multClose hw hε hacc l ρ hf σ
      have hP := hP0 ρ σ
      constructor
      · refine le_trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 ?_) hP) h3
        nlinarith
      · refine h4.trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 ?_) hP)
        nlinarith

/-- **Claim 4.5.** If every oracle answer has multiplicative error `ε` (the paper: `1/n³`), the
sampler's output distribution `μ̂^τ` satisfies `e^{-|l|ε} μ^τ ≤ μ̂^τ ≤ e^{|l|ε} μ^τ` pointwise
(the paper: `e^{∓1/n²}` for `|l| = n`). -/
theorem claim_4_5 (hw : ∀ σ, 0 ≤ w σ) {A : Pin V S → V → S → ℝ} {ε : ℝ} (hε : 0 ≤ ε)
    (hacc : ∀ ρ v, Feasible w ρ → ρ v = none → MultClose (A ρ v) (marg w ρ v) ε)
    {τ : Pin V S} (hτ : Feasible w τ) (l : List V) (hl : ∀ v, τ v = none → v ∈ l) :
    MultClose (seqProb A l τ) (cond w τ) (l.length * ε) := by
  intro σ
  rw [← seqProb_marg hw l τ hτ hl σ]
  exact seqProb_multClose hw hε hacc l τ hτ σ

/-- **Theorem 3.4 (the inequality chain).** Let the sampler succeed with probability `1 - p`,
output `μ̂` on success and `ν` on failure, so that its unconditional output is
`μ̃ = (1 - p) μ̂ + p ν`. Then for every vertex `v`,
`d_TV(μ̃_v, μ^τ_v) ≤ d_TV(μ̃, μ^τ) ≤ d_TV(μ̂, μ^τ) + p`. -/
theorem theorem_3_4_tv {μhat ν μ : (V → S) → ℝ} (hμhat : IsDist μhat) (hν : IsDist ν)
    (hμ : IsDist μ) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (v : V) :
    tv (pmarg (fun σ => (1 - p) * μhat σ + p * ν σ) v) (pmarg μ v) ≤
      tv (fun σ => (1 - p) * μhat σ + p * ν σ) μ ∧
    tv (fun σ => (1 - p) * μhat σ + p * ν σ) μ ≤ tv μhat μ + p := by
  refine ⟨tv_pmarg_le _ _ v, ?_⟩
  have hmix := tv_mix_le (Finset.univ : Finset (Fin 2)) ![1 - p, p] ![μhat, ν] μ
    (fun i _ => by fin_cases i <;> simp [hp0, hp1]) (by simp)
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at hmix
  have hνμ : tv ν μ ≤ 1 := by
    unfold tv
    have : ∑ x, |ν x - μ x| ≤ ∑ x, (ν x + μ x) := sum_le_sum fun x _ => by
      rw [abs_le]; constructor <;> linarith [hν.1 x, hμ.1 x]
    rw [sum_add_distrib, hν.2, hμ.2] at this; linarith
  have := tv_nonneg μhat μ
  calc _ ≤ (1 - p) * tv μhat μ + p * tv ν μ := hmix
    _ ≤ tv μhat μ + p := by nlinarith
