import Papers.PODC2012.LineTreeScheduling.Framework

/-!
# The distributed algorithm of Section 5 (epochs, stages, steps) and Lemma 5.1

The first phase of the algorithm of Figure 7, generic in the raising rule (so that it covers the
unit-height algorithm of Section 5, the narrow-instance algorithm of Lemma 6.2 and the
line-network algorithms of Section 7). The demand instances are partitioned into groups
`grp d ∈ {0, …, ℓ-1}` (a layered decomposition; group `0` is the paper's `G₁`). The first phase
has `ℓ` epochs; epoch `k` has `b` stages; stage `j` (0-based, the paper's stage `j+1`) consists of
`K` steps. In step `t` of stage `j` of epoch `k`, let `U` be the set of instances of group `k` that
are `(1 - ξ^{j+1})`-unsatisfied; an arbitrary maximal independent set `I ⊆ U` (supplied by an
adversarial MIS oracle `mis`) is raised.

The paper runs each stage "until `U = ∅`"; its distributed implementation runs a fixed number of
iterations per stage. We run `K` steps per stage and prove (`lemma_5_1`, `stage_complete`) that
`U = ∅` after `K` steps as soon as `p_max < 2^K p_min`, so the two versions coincide (once
`U = ∅` the remaining steps raise nothing).

Main results:
* `claim_5_2`: if `d₁ ∈ I` kills `d₂` (conflicting, `d₂` still unsatisfied after the step), then
  `p(d₂) > 2 p(d₁)`.
* `lemma_5_1`: if `U` is nonempty at the `L`-th step of a stage then `2^L p_min ≤ p_max`.
* `alg_sat`: at the end of the first phase all dual constraints are `(1-ξ^b)`-satisfied.
* `alg_validRun`, `alg_interference`: the run is a valid run of the framework with the
  interference property, so Lemmas 3.1 / 6.1 apply.
-/

set_option linter.unusedSectionVars false

namespace Podc.LineTreeScheduling

open Finset

variable {A D E : Type*} [DecidableEq A] [DecidableEq D] [DecidableEq E]

noncomputable section

namespace Inst

variable (I : Inst A D E)

/-- `J` is a maximal independent set contained in `U` (w.r.t. the conflict graph). -/
structure IsMIS (U J : Finset D) : Prop where
  subset : J ⊆ U
  indep : I.IsIndep J
  maximal : ∀ d ∈ U, ∃ d' ∈ J, I.Conflict d d'

/-- Non-vacuity of the MIS oracle: every set of instances contains a maximal independent set. -/
lemma exists_isMIS (U : Finset D) : ∃ J, I.IsMIS U J := by
  classical
  obtain ⟨J, hJ, hmax⟩ := (U.powerset.filter (fun J => I.IsIndep J)).exists_maximal
    ⟨∅, Finset.mem_filter.2 ⟨Finset.empty_mem_powerset U, fun d h => by simp at h⟩⟩
  simp only [Finset.mem_filter, Finset.mem_powerset] at hJ hmax
  refine ⟨J, hJ.1, hJ.2, fun d hd => ?_⟩
  by_contra hno
  push Not at hno
  have hdJ : d ∉ J := fun h => hno d h (I.conflict_self d)
  have hind : I.IsIndep (insert d J) := by
    intro d₁ h₁ d₂ h₂ hne
    rcases Finset.mem_insert.1 h₁ with e₁ | h₁' <;> rcases Finset.mem_insert.1 h₂ with e₂ | h₂'
    · exact absurd (e₁.trans e₂.symm) hne
    · subst e₁; exact hno d₂ h₂'
    · subst e₂; exact fun hc => hno d₁ h₁' ((I.conflict_comm).1 hc)
    · exact hJ.2 d₁ h₁' d₂ h₂' hne
  have := hmax ⟨Finset.insert_subset hd hJ.1, hind⟩ (Finset.subset_insert d J)
  exact hdJ (this (Finset.mem_insert_self d J))

/-- Non-vacuity: an MIS oracle (for every step and every candidate set) exists. -/
lemma exists_misOracle : ∃ mis : ℕ → Finset D → Finset D, ∀ t U, I.IsMIS U (mis t U) :=
  ⟨fun _ U => (I.exists_isMIS U).choose, fun _ U => (I.exists_isMIS U).choose_spec⟩

/-- The schedule parameters of the first phase: groups, number of stages per epoch, number of
steps per stage, and the progress factor `ξ`. -/
structure Sched (D : Type*) where
  /-- The group (layer) of a demand instance; group `k` is processed in epoch `k`. -/
  grp : D → ℕ
  /-- Number of stages per epoch. -/
  b : ℕ
  /-- Number of steps per stage. -/
  K : ℕ
  /-- The stage-progress factor (`14/15` in Section 5). -/
  ξ : ℝ

variable (R : Rule D E) (P : Sched D) (mis : ℕ → Finset D → Finset D) [Fintype D]

/-- The epoch of step `t`. -/
def Sched.epoch (P : Sched D) (t : ℕ) : ℕ := t / P.K / P.b

/-- The (0-based) stage of step `t` within its epoch. -/
def Sched.stage (P : Sched D) (t : ℕ) : ℕ := t / P.K % P.b

/-- The set `U` of step `t`: instances of the current group that are
`(1 - ξ^{j+1})`-unsatisfied, `j` the current stage. -/
def cand (t : ℕ) (y : Duals A E) : Finset D :=
  univ.filter fun d => P.grp d = P.epoch t ∧
    I.lhs R.h y d < (1 - P.ξ ^ (P.stage t + 1)) * I.profit d

/-- The dual assignment of the algorithm after `t` steps. -/
def algState : ℕ → Duals A E
  | 0 => 0
  | t + 1 => I.raise R (algState t) (mis t (I.cand R P t (algState t)))

/-- The independent set raised at step `t`. -/
def algI (t : ℕ) : Finset D := mis t (I.cand R P t (I.algState R P mis t))

lemma algState_eq_run (t : ℕ) : I.algState R P mis t = I.run R (I.algI R P mis) t := by
  induction t with
  | zero => rfl
  | succ t ih => simp only [algState, run_succ, algI, ih]

variable {I R P mis}

/-- Hypotheses on the algorithm: the rule is well formed, profits are positive, `0 < ξ < 1`, and the
oracle returns maximal independent sets. -/
structure AlgHyp (I : Inst A D E) (R : Rule D E) (P : Sched D)
    (mis : ℕ → Finset D → Finset D) : Prop where
  wf : R.WF I
  profit_pos : ∀ d, 0 < I.profit d
  ξ_pos : 0 < P.ξ
  ξ_lt_one : P.ξ < 1
  mis : ∀ t U, I.IsMIS U (mis t U)

lemma mem_cand {t : ℕ} {y : Duals A E} {d : D} :
    d ∈ I.cand R P t y ↔ P.grp d = P.epoch t ∧
      I.lhs R.h y d < (1 - P.ξ ^ (P.stage t + 1)) * I.profit d := by
  simp [cand]

lemma algI_subset (H : AlgHyp I R P mis) (t : ℕ) :
    I.algI R P mis t ⊆ I.cand R P t (I.algState R P mis t) := (H.mis _ _).subset

/-- The first phase of the algorithm is a valid run of the framework (for any horizon). -/
lemma alg_validRun (H : AlgHyp I R P mis) (T : ℕ) : I.ValidRun R (I.algI R P mis) T := by
  refine ⟨fun t _ => (H.mis _ _).indep, fun t _ d hd => ?_⟩
  have h := (mem_cand.1 (algI_subset H t hd)).2
  rw [← algState_eq_run]
  have : 0 < P.ξ ^ (P.stage t + 1) * I.profit d := mul_pos (pow_pos H.ξ_pos _) (H.profit_pos d)
  nlinarith

/-- The run satisfies the interference property whenever the groups and critical sets form a
layered decomposition (instances of earlier-or-equal groups are raised earlier-or-equal). -/
lemma alg_interference (H : AlgHyp I R P mis)
    (hlay : ∀ d₁ d₂, P.grp d₁ ≤ P.grp d₂ → I.Overlap d₁ d₂ → (R.crit d₁ ∩ I.path d₂).Nonempty)
    (T : ℕ) : I.Interference R (I.algI R P mis) T := by
  intro s t hst _ d₁ h₁ d₂ h₂ hov
  refine hlay d₁ d₂ ?_ hov
  rw [(mem_cand.1 (algI_subset H s h₁)).1, (mem_cand.1 (algI_subset H t h₂)).1]
  exact Nat.div_le_div_right (Nat.div_le_div_right hst.le)

lemma lhs_nonneg_alg (H : AlgHyp I R P mis) (t : ℕ) (d : D) :
    0 ≤ I.lhs R.h (I.algState R P mis t) d := by
  rw [algState_eq_run]
  have hv := alg_validRun H t
  exact add_nonneg (run_α_nonneg H.wf hv le_rfl _)
    (mul_nonneg (H.wf.h_nonneg d) (Finset.sum_nonneg fun e _ => run_β_nonneg H.wf hv le_rfl e))

lemma lhs_mono_alg (H : AlgHyp I R P mis) {s t : ℕ} (hst : s ≤ t) (d : D) :
    I.lhs R.h (I.algState R P mis s) d ≤ I.lhs R.h (I.algState R P mis t) d := by
  rw [algState_eq_run, algState_eq_run]
  exact lhs_mono H.wf (alg_validRun H t) hst le_rfl d

/-- **Claim 5.2.** Let `d₁` be raised at step `t` (stage `j`, epoch `k`) and let `d₂` be an
instance of group `k` conflicting with `d₁` that is still `(1-ξ^{j+1})`-unsatisfied after the step
("`d₁` kills `d₂`"). Suppose all instances of group `k` were `(1-ξ^j)`-satisfied at the beginning
of the step, every raise of `d₁` contributes at least `κ δ(d₁)` to the constraint of a conflicting
instance of its group, all denominators are `≤ M`, and `2M(1-ξ) ≤ κξ`. Then `p(d₂) > 2 p(d₁)`.
(Section 5: `κ = 1`, `M = Δ+1`, `ξ = 2(Δ+1)/(2(Δ+1)+1)`.) -/
theorem claim_5_2 (H : AlgHyp I R P mis) {κ M : ℝ} (hκ : 0 < κ)
    (hkill : ∀ d₁ d₂, P.grp d₁ = P.grp d₂ → I.Conflict d₁ d₂ → κ ≤ I.weight R d₁ d₂)
    (hden : ∀ d, R.denom d ≤ M) (hratio : 2 * M * (1 - P.ξ) ≤ κ * P.ξ) {t : ℕ}
    (hpre : ∀ d, P.grp d = P.epoch t →
      (1 - P.ξ ^ P.stage t) * I.profit d ≤ I.lhs R.h (I.algState R P mis t) d)
    {d₁ d₂ : D} (h₁ : d₁ ∈ I.algI R P mis t) (hg₂ : P.grp d₂ = P.epoch t)
    (hc : I.Conflict d₁ d₂)
    (h₂ : I.lhs R.h (I.algState R P mis (t + 1)) d₂ < (1 - P.ξ ^ (P.stage t + 1)) * I.profit d₂) :
    2 * I.profit d₁ < I.profit d₂ := by
  have hR := H.wf
  have hv := alg_validRun H (t + 1)
  set y := I.algState R P mis t
  set j := P.stage t
  obtain ⟨hg₁, hu₁⟩ := mem_cand.1 (algI_subset H t h₁)
  have hw := hkill d₁ d₂ (hg₁.trans hg₂.symm) hc
  -- the raise of `d₁`
  set δ := I.amt R y d₁
  have hδ : δ * R.denom d₁ = I.profit d₁ - I.lhs R.h y d₁ := amt_mul_denom hR y d₁
  have hδpos : 0 < δ := by
    have := amt_pos hR hv (Nat.lt_succ_self t) h₁
    rwa [← algState_eq_run] at this
  have hξj : 0 < P.ξ ^ j := pow_pos H.ξ_pos j
  have hp₁ := H.profit_pos d₁
  have hp₂ := H.profit_pos d₂
  -- `δ(d₁) ≥ ξ^{j+1} p(d₁) / M`
  have hδM : P.ξ ^ (j + 1) * I.profit d₁ < δ * M := by
    have hden1 := hden d₁
    have : P.ξ ^ (j + 1) * I.profit d₁ < δ * R.denom d₁ := by rw [hδ]; linarith
    nlinarith
  -- the constraint of `d₂` grows by at least `κ δ(d₁)`
  have hgrow : I.lhs R.h y d₂ + δ * κ ≤ I.lhs R.h (I.algState R P mis (t + 1)) d₂ := by
    show _ ≤ I.lhs R.h (I.raise R y (mis t (I.cand R P t y))) d₂
    rw [lhs_raise]
    have hnn : ∀ d' ∈ mis t (I.cand R P t y), 0 ≤ I.amt R y d' * I.weight R d' d₂ := by
      intro d' hd'
      have := amt_pos hR hv (Nat.lt_succ_self t) hd'
      rw [← algState_eq_run] at this
      exact mul_nonneg this.le (weight_nonneg hR d' d₂)
    have := Finset.single_le_sum hnn h₁
    have : δ * κ ≤ δ * I.weight R d₁ d₂ := mul_le_mul_of_nonneg_left hw hδpos.le
    linarith
  have hpre₂ := hpre d₂ hg₂
  -- `κ δ(d₁) < (ξ^j - ξ^{j+1}) p(d₂)`
  have hgap : δ * κ < P.ξ ^ j * (1 - P.ξ) * I.profit d₂ := by
    have : P.ξ ^ (j + 1) = P.ξ ^ j * P.ξ := pow_succ _ _
    nlinarith
  have hM : 0 < M := lt_of_lt_of_le (denom_pos hR d₁) (hden d₁)
  -- combine: `κ ξ p(d₁) < M (1-ξ) p(d₂)`
  have hcomb : κ * P.ξ * I.profit d₁ < M * (1 - P.ξ) * I.profit d₂ := by
    have e1 : P.ξ ^ (j + 1) = P.ξ ^ j * P.ξ := pow_succ _ _
    have h3 : κ * (P.ξ ^ (j + 1) * I.profit d₁) < κ * (δ * M) := mul_lt_mul_of_pos_left hδM hκ
    have h4 : M * (δ * κ) < M * (P.ξ ^ j * (1 - P.ξ) * I.profit d₂) :=
      mul_lt_mul_of_pos_left hgap hM
    have : P.ξ ^ j * (κ * P.ξ * I.profit d₁) < P.ξ ^ j * (M * (1 - P.ξ) * I.profit d₂) := by
      rw [e1] at h3; nlinarith
    exact lt_of_mul_lt_mul_left this hξj.le
  have h1ξ : 0 < 1 - P.ξ := by linarith [H.ξ_lt_one]
  have : 2 * M * (1 - P.ξ) * I.profit d₁ < M * (1 - P.ξ) * I.profit d₂ := by
    have := mul_le_mul_of_nonneg_right hratio hp₁.le
    linarith
  have hMξ : 0 < M * (1 - P.ξ) := mul_pos hM h1ξ
  nlinarith

/-- Index arithmetic: steps `(k b + j) K + i` with `i < K`, `j < b` lie in epoch `k`, stage `j`. -/
lemma epoch_stage_eq {k j i : ℕ} (hj : j < P.b) (hi : i < P.K) :
    P.epoch ((k * P.b + j) * P.K + i) = k ∧ P.stage ((k * P.b + j) * P.K + i) = j := by
  have hK : 0 < P.K := by omega
  have hq : ((k * P.b + j) * P.K + i) / P.K = k * P.b + j := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hK, Nat.div_eq_of_lt hi, Nat.zero_add]
  have hb : 0 < P.b := by omega
  refine ⟨?_, ?_⟩
  · simp only [Sched.epoch, hq]
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hb, Nat.div_eq_of_lt hj, Nat.zero_add]
  · simp only [Sched.stage, hq]
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj]

/-- **Lemma 5.1** (the step bound of a stage). Consider stage `j` of epoch `k` and suppose that at
its beginning all instances of group `k` are `(1-ξ^j)`-satisfied. If after `L ≤ K` steps of the
stage some instance of group `k` is still `(1-ξ^{j+1})`-unsatisfied, then
`2^L p_min ≤ p_max` (for any bounds `p_min ≤ p(d) ≤ p_max`). Equivalently, a stage has at most
`1 + log₂(p_max/p_min)` steps with `U ≠ ∅`. -/
theorem lemma_5_1 (H : AlgHyp I R P mis) {κ M : ℝ} (hκ : 0 < κ)
    (hkill : ∀ d₁ d₂, P.grp d₁ = P.grp d₂ → I.Conflict d₁ d₂ → κ ≤ I.weight R d₁ d₂)
    (hden : ∀ d, R.denom d ≤ M) (hratio : 2 * M * (1 - P.ξ) ≤ κ * P.ξ)
    {pmin pmax : ℝ} (hpmin : ∀ d, pmin ≤ I.profit d) (hpmax : ∀ d, I.profit d ≤ pmax)
    {k j : ℕ} (hj : j < P.b)
    (hstart : ∀ d, P.grp d = k →
      (1 - P.ξ ^ j) * I.profit d ≤ I.lhs R.h (I.algState R P mis ((k * P.b + j) * P.K)) d)
    {L : ℕ} (hL : L ≤ P.K) {d : D} (hd : P.grp d = k)
    (hunsat : I.lhs R.h (I.algState R P mis ((k * P.b + j) * P.K + L)) d <
      (1 - P.ξ ^ (j + 1)) * I.profit d) :
    2 ^ L * pmin ≤ pmax := by
  obtain ⟨t₀, ht₀⟩ : ∃ t₀, t₀ = (k * P.b + j) * P.K := ⟨_, rfl⟩
  rw [← ht₀] at hstart hunsat
  -- chain: an unsatisfied instance after `L` steps has profit `≥ 2^L` times some profit
  suffices h : ∀ L ≤ P.K, ∀ d, P.grp d = k →
      I.lhs R.h (I.algState R P mis (t₀ + L)) d < (1 - P.ξ ^ (j + 1)) * I.profit d →
      ∃ d₀, 2 ^ L * I.profit d₀ ≤ I.profit d by
    obtain ⟨d₀, h₀⟩ := h L hL d hd hunsat
    have := mul_le_mul_of_nonneg_left (hpmin d₀) (pow_nonneg (zero_le_two (α := ℝ)) L)
    linarith [hpmax d]
  intro L
  induction L with
  | zero => intro _ d _ _; exact ⟨d, by simp⟩
  | succ L ih =>
    intro hL d hd hu
    have hLK : L < P.K := by omega
    obtain ⟨hep, hst⟩ := epoch_stage_eq (P := P) (k := k) hj hLK
    rw [← ht₀] at hep hst
    -- `d` is in `U` at step `t₀ + L`
    have hu' : I.lhs R.h (I.algState R P mis (t₀ + L)) d < (1 - P.ξ ^ (j + 1)) * I.profit d :=
      lt_of_le_of_lt (lhs_mono_alg H (by omega) d) hu
    have hdU : d ∈ I.cand R P (t₀ + L) (I.algState R P mis (t₀ + L)) := by
      rw [mem_cand, hep, hst]; exact ⟨hd, hu'⟩
    obtain ⟨d₁, hd₁, hc⟩ := (H.mis (t₀ + L) _).maximal d hdU
    have hd₁' : d₁ ∈ I.algI R P mis (t₀ + L) := hd₁
    obtain ⟨hg₁, hu₁⟩ := mem_cand.1 (algI_subset H _ hd₁')
    rw [hep] at hg₁; rw [hst] at hu₁
    -- Claim 5.2 for `d₁` killing `d`
    have hpre : ∀ d', P.grp d' = P.epoch (t₀ + L) →
        (1 - P.ξ ^ P.stage (t₀ + L)) * I.profit d' ≤ I.lhs R.h (I.algState R P mis (t₀ + L)) d' := by
      intro d' hd'
      rw [hep] at hd'; rw [hst]
      exact (hstart d' hd').trans (lhs_mono_alg H (by omega) d')
    have hkl := claim_5_2 H hκ hkill hden hratio hpre hd₁' (by rw [hep]; exact hd)
      ((I.conflict_comm).1 hc) (by rw [hst]; exact hu)
    obtain ⟨d₀, h₀⟩ := ih (by omega) d₁ hg₁ hu₁
    refine ⟨d₀, ?_⟩
    rw [pow_succ]
    linarith

/-- Each stage completes: if all instances of group `k` are `(1-ξ^j)`-satisfied at the beginning of
stage `j` and `p_max < 2^K p_min`, they are all `(1-ξ^{j+1})`-satisfied at its end. -/
theorem stage_complete (H : AlgHyp I R P mis) {κ M : ℝ} (hκ : 0 < κ)
    (hkill : ∀ d₁ d₂, P.grp d₁ = P.grp d₂ → I.Conflict d₁ d₂ → κ ≤ I.weight R d₁ d₂)
    (hden : ∀ d, R.denom d ≤ M) (hratio : 2 * M * (1 - P.ξ) ≤ κ * P.ξ)
    {pmin pmax : ℝ} (hpmin : ∀ d, pmin ≤ I.profit d) (hpmax : ∀ d, I.profit d ≤ pmax)
    (hK : pmax < 2 ^ P.K * pmin) {k j : ℕ} (hj : j < P.b)
    (hstart : ∀ d, P.grp d = k →
      (1 - P.ξ ^ j) * I.profit d ≤ I.lhs R.h (I.algState R P mis ((k * P.b + j) * P.K)) d)
    (d : D) (hd : P.grp d = k) :
    (1 - P.ξ ^ (j + 1)) * I.profit d ≤
      I.lhs R.h (I.algState R P mis ((k * P.b + (j + 1)) * P.K)) d := by
  by_contra hc
  push Not at hc
  have := lemma_5_1 H hκ hkill hden hratio hpmin hpmax hj hstart le_rfl hd
    (by rw [show (k * P.b + j) * P.K + P.K = (k * P.b + (j + 1)) * P.K by ring]; exact hc)
  linarith

/-- At the end of the first phase (`ℓ b K` steps, all groups `< ℓ`) every dual constraint is
`(1-ξ^b)`-satisfied: the slackness parameter is `λ ≥ 1 - ξ^b`. -/
theorem alg_sat (H : AlgHyp I R P mis) {κ M : ℝ} (hκ : 0 < κ)
    (hkill : ∀ d₁ d₂, P.grp d₁ = P.grp d₂ → I.Conflict d₁ d₂ → κ ≤ I.weight R d₁ d₂)
    (hden : ∀ d, R.denom d ≤ M) (hratio : 2 * M * (1 - P.ξ) ≤ κ * P.ξ)
    {pmin pmax : ℝ} (hpmin : ∀ d, pmin ≤ I.profit d) (hpmax : ∀ d, I.profit d ≤ pmax)
    (hK : pmax < 2 ^ P.K * pmin) {ℓ : ℕ} (hℓ : ∀ d, P.grp d < ℓ) (d : D) :
    (1 - P.ξ ^ P.b) * I.profit d ≤ I.lhs R.h (I.algState R P mis (ℓ * P.b * P.K)) d := by
  set k := P.grp d
  have hstages : ∀ j ≤ P.b, ∀ d', P.grp d' = k →
      (1 - P.ξ ^ j) * I.profit d' ≤ I.lhs R.h (I.algState R P mis ((k * P.b + j) * P.K)) d' := by
    intro j
    induction j with
    | zero => intro _ d' _; simp only [pow_zero, sub_self, zero_mul]; exact lhs_nonneg_alg H _ d'
    | succ j ih =>
      intro hj d' hd'
      exact stage_complete H hκ hkill hden hratio hpmin hpmax hK (by omega) (ih (by omega)) d' hd'
  refine (hstages P.b le_rfl d rfl).trans (lhs_mono_alg H ?_ d)
  have : k + 1 ≤ ℓ := hℓ d
  calc (k * P.b + P.b) * P.K = (k + 1) * P.b * P.K := by ring
    _ ≤ ℓ * P.b * P.K := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ this)

end Inst

end

end Podc.LineTreeScheduling
