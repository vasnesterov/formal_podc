import Papers.PODC2018.LocalSamplingCounting.Basic

/-!
# The distributed JVV sampler: correctness of the local rejection sampling (§4.2)

Abstract setting of §4.2.3. `μhat` is the distribution of the configuration `Y` produced by the
second pass (by Claim 4.5 it has multiplicative error `δ = 1/n²` w.r.t. the target `μ^τ`); `σ₀` is
the ground state of the first pass; for every `σ` the third pass builds configurations
`path σ 0 = σ₀, path σ 1, …, path σ n = σ`, all feasible when `σ` is (Claim 4.6), and node `vᵢ`
*accepts* with probability

  `q_{vᵢ}(σ) = μ̂(σ_{i-1}) w(σᵢ) / (μ̂(σᵢ) w(σ_{i-1})) · e^{-3δ}`   (eq. (9)).

* `claim_4_7_bounds`: `e^{-5δ} ≤ q_{vᵢ} ≤ e^{-δ} ≤ 1` (the bounds of Claim 4.7);
* `lemma_4_8_success`: the algorithm succeeds (all nodes accept) with probability `≥ e^{-5nδ}`;
* `lemma_4_8_joint`: `Pr[Y = σ ∧ success] = K · μ^τ(σ)` for a constant `K > 0`;
* `lemma_4_8`: conditioned on success, `Y` is distributed exactly as `μ^τ`.

**Typo in the paper.** The paper lets `vᵢ` set `F'_{vᵢ} = 1` *with probability `q_{vᵢ}`* and fail
when `F'_{vᵢ} = 1`, and states that the algorithm "fails with probability at most
`∑ E[F'_{vᵢ}] = 1 - O(1/n)`". Since `q_{vᵢ} ≥ e^{-5/n²}` is close to `1`, this would make the
algorithm fail almost surely. Its proof uses `Pr[success | Y = σ] = ∏ q_{vᵢ}(σ)`, i.e. `q_{vᵢ}` is
the *acceptance* probability, and the failure probability is `O(1/n)`. We formalize the intended
version.
-/

set_option linter.unusedSectionVars false

namespace Podc.LocalSamplingCounting

open Finset

open scoped Classical

variable {V S : Type*} [Fintype V] [DecidableEq V] [Fintype S] [DecidableEq S]

/-- Acceptance probability of the `i`-th node (eq. (9), with `δ = 1/n²`). -/
noncomputable def accProb (w μhat : (V → S) → ℝ) (δ : ℝ) (path : (V → S) → ℕ → V → S)
    (σ : V → S) (i : ℕ) : ℝ :=
  μhat (path σ i) * w (path σ (i + 1)) / (μhat (path σ (i + 1)) * w (path σ i)) *
    Real.exp (-(3 * δ))

/-- Probability that all `n` nodes accept, given `Y = σ`. -/
noncomputable def succProb (w μhat : (V → S) → ℝ) (δ : ℝ) (path : (V → S) → ℕ → V → S)
    (n : ℕ) (σ : V → S) : ℝ :=
  ∏ i ∈ range n, accProb w μhat δ path σ i

variable {w μhat : (V → S) → ℝ} {τ : Pin V S} {δ : ℝ} {path : (V → S) → ℕ → V → S} {n : ℕ}

/-- A configuration feasible for the target `μ^τ`. -/
def FeasibleCfg (w : (V → S) → ℝ) (τ : Pin V S) (σ : V → S) : Prop := Cons σ τ ∧ 0 < w σ

lemma cond_pos_of_feasibleCfg (hτ : Feasible w τ) {σ : V → S} (h : FeasibleCfg w τ σ) :
    0 < cond w τ σ := by
  unfold cond; rw [if_pos h.1]; exact div_pos h.2 hτ

/-- **Claim 4.7 (bounds).** If `μ̂` has multiplicative error `δ ≥ 0` w.r.t. `μ^τ` and both
`σ_{i}` and `σ_{i+1}` are feasible, then `e^{-5δ} ≤ q ≤ e^{-δ}`; in particular `q ≤ 1`. -/
theorem claim_4_7_bounds (hτ : Feasible w τ) (hmc : MultClose μhat (cond w τ) δ)
    {σ : V → S} {i : ℕ} (h0 : FeasibleCfg w τ (path σ i))
    (h1 : FeasibleCfg w τ (path σ (i + 1))) :
    Real.exp (-(5 * δ)) ≤ accProb w μhat δ path σ i ∧
      accProb w μhat δ path σ i ≤ Real.exp (-δ) := by
  set a := path σ i
  set b := path σ (i + 1)
  have ca : cond w τ a = w a / Z w τ := by unfold cond; rw [if_pos h0.1]
  have cb : cond w τ b = w b / Z w τ := by unfold cond; rw [if_pos h1.1]
  obtain ⟨ha1, ha2⟩ := hmc a
  obtain ⟨hb1, hb2⟩ := hmc b
  rw [ca] at ha1 ha2
  rw [cb] at hb1 hb2
  have hZ := hτ
  unfold Feasible at hZ
  have wa := h0.2
  have wb := h1.2
  have hμa : 0 < μhat a := lt_of_lt_of_le (mul_pos (Real.exp_pos _) (div_pos wa hZ)) ha1
  have hμb : 0 < μhat b := lt_of_lt_of_le (mul_pos (Real.exp_pos _) (div_pos wb hZ)) hb1
  -- the ratio `r = μ̂(a) w(b) / (μ̂(b) w(a))` lies in `[e^{-2δ}, e^{2δ}]`
  have hr1 : Real.exp (-(2 * δ)) ≤ μhat a * w b / (μhat b * w a) := by
    rw [le_div_iff₀ (mul_pos hμb wa)]
    have e : Real.exp (-(2 * δ)) = Real.exp (-δ) * Real.exp (-δ) := by
      rw [← Real.exp_add]; ring_nf
    rw [e]
    -- `μ̂(b) ≤ e^δ w(b)/Z` and `μ̂(a) ≥ e^{-δ} w(a)/Z`
    have := mul_le_mul ha1 hb2 hμb.le (by linarith)
    have hed : Real.exp (-δ) * Real.exp δ = 1 := by rw [← Real.exp_add]; simp
    calc Real.exp (-δ) * Real.exp (-δ) * (μhat b * w a)
        ≤ Real.exp (-δ) * Real.exp (-δ) * (Real.exp δ * (w b / Z w τ) * w a) := by
          gcongr
      _ = Real.exp (-δ) * (w a / Z w τ) * w b * (Real.exp (-δ) * Real.exp δ) := by
          field_simp
      _ = Real.exp (-δ) * (w a / Z w τ) * w b := by rw [hed, mul_one]
      _ ≤ μhat a * w b := by gcongr
  have hr2 : μhat a * w b / (μhat b * w a) ≤ Real.exp (2 * δ) := by
    rw [div_le_iff₀ (mul_pos hμb wa)]
    have e : Real.exp (2 * δ) = Real.exp δ * Real.exp δ := by
      rw [← Real.exp_add]; ring_nf
    rw [e]
    have hed : Real.exp (-δ) * Real.exp δ = 1 := by rw [← Real.exp_add]; simp
    calc μhat a * w b ≤ Real.exp δ * (w a / Z w τ) * w b := by gcongr
      _ = Real.exp δ * Real.exp δ * (Real.exp (-δ) * (w b / Z w τ) * w a) := by
          field_simp
          rw [← Real.exp_add]; simp
      _ ≤ Real.exp δ * Real.exp δ * (μhat b * w a) := by gcongr
  unfold accProb
  constructor
  · calc Real.exp (-(5 * δ)) = Real.exp (-(2 * δ)) * Real.exp (-(3 * δ)) := by
          rw [← Real.exp_add]; ring_nf
      _ ≤ _ := by gcongr
  · calc _ ≤ Real.exp (2 * δ) * Real.exp (-(3 * δ)) := by gcongr
      _ = Real.exp (-δ) := by rw [← Real.exp_add]; ring_nf

/-- Hypotheses of §4.2.3 on the third pass: the configurations `σ₀ = path σ 0`, …,
`σₙ = path σ n = σ` start at the fixed ground state and are all feasible (Claim 4.6). -/
structure PathSpec (w : (V → S) → ℝ) (τ : Pin V S) (path : (V → S) → ℕ → V → S) (n : ℕ)
    (σ₀ : V → S) : Prop where
  start : ∀ σ, path σ 0 = σ₀
  finish : ∀ σ, path σ n = σ
  feasible : ∀ σ, FeasibleCfg w τ σ → ∀ i ≤ n, FeasibleCfg w τ (path σ i)

/-- **Lemma 4.8 (success probability).** Given `Y = σ` feasible, all `n` nodes accept with
probability at least `e^{-5nδ}` (`= e^{-5/n}` for `δ = 1/n²`, i.e. failure probability
`O(1/n)`). -/
theorem lemma_4_8_success (hτ : Feasible w τ) (hmc : MultClose μhat (cond w τ) δ) {σ₀ : V → S}
    (hp : PathSpec w τ path n σ₀) {σ : V → S} (hσ : FeasibleCfg w τ σ) :
    Real.exp (-(5 * n * δ)) ≤ succProb w μhat δ path n σ := by
  unfold succProb
  have : Real.exp (-(5 * n * δ)) = ∏ _i ∈ range n, Real.exp (-(5 * δ)) := by
    rw [prod_const, card_range, ← Real.exp_nat_mul]; ring_nf
  rw [this]
  exact Finset.prod_le_prod₀ (fun _ _ => (Real.exp_pos _).le) fun i hi =>
    (claim_4_7_bounds hτ hmc (hp.feasible σ hσ i (by simp at hi; omega))
      (hp.feasible σ hσ (i + 1) (by simp at hi; omega))).1

/-- Telescoping product. -/
lemma prod_range_div_telescope (g : ℕ → ℝ) (hg : ∀ i ≤ n, g i ≠ 0) :
    ∏ i ∈ range n, g (i + 1) / g i = g n / g 0 := by
  induction n with
  | zero => simp [div_self (hg 0 le_rfl)]
  | succ k ih =>
    rw [prod_range_succ, ih (fun i hi => hg i (by omega))]
    have h1 := hg k (by omega)
    field_simp

/-- **Lemma 4.8 (joint probability).** `Pr[Y = σ ∧ success] = μ̂(σ) ∏ᵢ q_{vᵢ}(σ)` is
proportional to `μ^τ(σ)`, with a constant independent of `σ`. -/
theorem lemma_4_8_joint (hw : ∀ σ, 0 ≤ w σ) (hτ : Feasible w τ)
    (hmc : MultClose μhat (cond w τ) δ) {σ₀ : V → S} (hσ₀ : FeasibleCfg w τ σ₀)
    (hp : PathSpec w τ path n σ₀) (σ : V → S) :
    μhat σ * succProb w μhat δ path n σ =
      (μhat σ₀ / w σ₀ * Real.exp (-(3 * n * δ)) * Z w τ) * cond w τ σ := by
  by_cases hσ : FeasibleCfg w τ σ
  · have hfe := hp.feasible σ hσ
    have hZ : 0 < Z w τ := hτ
    have hpos : ∀ i ≤ n, 0 < μhat (path σ i) := fun i hi => by
      have := (hmc (path σ i)).1
      exact lt_of_lt_of_le (mul_pos (Real.exp_pos _) (cond_pos_of_feasibleCfg hτ (hfe i hi)))
        this
    unfold succProb accProb
    rw [prod_mul_distrib, prod_const, card_range]
    have htel : ∏ i ∈ range n, μhat (path σ i) * w (path σ (i + 1)) /
        (μhat (path σ (i + 1)) * w (path σ i)) =
        (w (path σ n) / μhat (path σ n)) / (w (path σ 0) / μhat (path σ 0)) := by
      rw [← prod_range_div_telescope (fun i => w (path σ i) / μhat (path σ i))
        (fun i hi => div_ne_zero (hfe i hi).2.ne' (hpos i hi).ne')]
      refine prod_congr rfl fun i hi => ?_
      have := hpos i (by simp at hi; omega)
      have := hpos (i + 1) (by simp at hi; omega)
      have := (hfe i (by simp at hi; omega)).2
      field_simp
    rw [htel, hp.start, hp.finish]
    have hcσ : cond w τ σ = w σ / Z w τ := by unfold cond; rw [if_pos hσ.1]
    rw [hcσ, ← Real.exp_nat_mul]
    have h1 := hpos n le_rfl
    rw [hp.finish] at h1
    have h2 := hσ₀.2
    have h3 : 0 < μhat σ₀ := by have := hpos 0 (Nat.zero_le _); rwa [hp.start] at this
    field_simp
  · -- infeasible `σ`: both sides vanish
    have hc : cond w τ σ = 0 := by
      unfold cond
      split_ifs with h
      · have : w σ = 0 := le_antisymm (not_lt.1 fun h' => hσ ⟨h, h'⟩) (hw σ)
        rw [this, zero_div]
      · rfl
    have hm : μhat σ = 0 := by
      obtain ⟨h1, h2⟩ := hmc σ
      rw [hc, mul_zero] at h1 h2
      exact le_antisymm h2 h1
    rw [hm, hc]; ring

/-- **Lemma 4.8.** Conditioned on success, the output `Y` of the local-JVV algorithm follows
precisely the target distribution `μ^τ`:
`Pr[Y = σ | success] = Pr[Y = σ ∧ success] / Pr[success] = μ^τ(σ)`. -/
theorem lemma_4_8 (hw : ∀ σ, 0 ≤ w σ) (hτ : Feasible w τ)
    (hmc : MultClose μhat (cond w τ) δ) {σ₀ : V → S} (hσ₀ : FeasibleCfg w τ σ₀)
    (hp : PathSpec w τ path n σ₀) (σ : V → S) :
    μhat σ * succProb w μhat δ path n σ /
      (∑ σ', μhat σ' * succProb w μhat δ path n σ') = cond w τ σ := by
  simp_rw [lemma_4_8_joint hw hτ hmc hσ₀ hp]
  rw [← mul_sum, sum_cond hτ, mul_one]
  have hK : 0 < μhat σ₀ / w σ₀ * Real.exp (-(3 * n * δ)) * Z w τ := by
    have := lt_of_lt_of_le (mul_pos (Real.exp_pos _) (cond_pos_of_feasibleCfg hτ hσ₀))
      (hmc σ₀).1
    have : (0 : ℝ) < Z w τ := hτ
    have := hσ₀.2
    positivity
  exact mul_div_cancel_left₀ _ hK.ne'

/-- **Claim 4.6 (core step).** Let `ρ₁ = σ_{i-1}(Γ)` and `ρ₂ = Y(Γ)` be feasible pinnings on which
the oracle answers identically at the free vertex `u = vᵢ` (they agree on `B_t(vᵢ)`), with
multiplicative error `ε` in both cases. If `Y(vᵢ) = c` has positive probability under `ρ₂`, then
some feasible configuration extends `ρ₁` and takes the value `c` at `vᵢ`; this is the `σᵢ`
required by the invariants (6)–(8). -/
theorem claim_4_6_core (hw : ∀ σ, 0 ≤ w σ) {A : Pin V S → V → S → ℝ} {ε : ℝ}
    {ρ₁ ρ₂ : Pin V S} (h₁ : Feasible w ρ₁) {u : V} (hu : ρ₁ u = none)
    (hA : A ρ₁ u = A ρ₂ u) (hm₁ : MultClose (A ρ₁ u) (marg w ρ₁ u) ε)
    (hm₂ : MultClose (A ρ₂ u) (marg w ρ₂ u) ε) {c : S} (hc : 0 < marg w ρ₂ u c) :
    ∃ σ, Cons σ ρ₁ ∧ σ u = c ∧ 0 < w σ := by
  have hA2 : 0 < A ρ₂ u c := lt_of_lt_of_le (mul_pos (Real.exp_pos _) hc) (hm₂ c).1
  rw [← hA] at hA2
  have hpos : 0 < marg w ρ₁ u c := by
    have := (hm₁ c).2
    by_contra h; push_neg at h
    nlinarith [Real.exp_pos ε]
  have hf := (feasible_update_iff hw h₁ hu c).2 hpos
  by_contra h; push_neg at h
  have : Z w (Function.update ρ₁ u (some c)) ≤ 0 := sum_nonpos fun σ _ => by
    split_ifs with hσ
    · obtain ⟨h1, h2⟩ := (cons_update_of_none hu).1 hσ
      exact h σ h1 h2
    · rfl
  exact absurd hf (not_lt.2 this)

end Podc.LocalSamplingCounting
