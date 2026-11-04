import Podc.Foundations.GameTheory.NetworkCostSharing

/-!
# Bayesian ignorance in NCS games: universal upper bounds

Alon, Emek, Feldman, Tennenholtz, *Bayesian Ignorance* (PODC 2010), Section 3:

* `exists_isBayesEq`: every Bayesian NCS game has a pure Bayesian equilibrium (the paper derives it
  from Observation 2.1 and Rosenthal's potential; with infinite costs for agents that do not
  connect their terminals the potential has to be minimised over *feasible* strategy profiles,
  see `differencies.md`).
* `RosenthalCounterexample.no_finite_bayesPotential`, `RosenthalCounterexample.empty_minimises_not_isBayesEq`:
  with the paper's `∞` costs, Rosenthal's `Q` is not a Bayesian potential, and its global minimiser
  (the empty profile) is not an equilibrium.
* `lemma_3_1`: `worst-eq^P(G) ≤ k · opt^C(G)`.
* `lemma_3_8`: `best-eq^P(G) ≤ H(k) · opt^P(G)`.

* Table 1 corollaries: `table_upper_k`, `bestEqC_le_hnum_mul_bestEqP`, `worstEqC_le_card_mul_worstEqP`,
  with the complete-information price of stability / anarchy (`bestNash_le_hnum_mul_opt`,
  `worstNash_le_card_mul_opt`) as point-mass cases of Lemmas 3.8 and 3.1.

Both lemmas hold for directed and undirected (multi)graphs alike (`Network` is an arbitrary step
relation).
-/

open Finset Cslib.GameTheory Cslib.GameTheory.BayesianGame
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false

namespace Podc.BayesianIgnorance

variable {V E ι : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
  [Fintype ι] [DecidableEq ι] (N : Network V E) (p : PMF (ι → V × V))

/-! ### Lemma 3.1 -/

/-- Every agent can secure at most her distance: deviating to a cheapest connecting edge set. -/
lemma exCost_le_of_isBayesEq {s : ι → V × V → Finset E} (hs : (N.bayesGame p).IsBayesEq s)
    (i : ι) : (N.bayesGame p).exCost s i ≤ ∑ t, p t * N.dist (t i).1 (t i).2 := by
  classical
  let σ : V × V → Finset E := fun τ =>
    if h : N.Reachable τ.1 τ.2 then (N.exists_connects_eq_dist h).choose else ∅
  refine (hs i σ).trans ?_
  unfold exCost
  refine Finset.sum_le_sum fun t _ => mul_le_mul_right ?_ _
  rw [Network.bayesGame_cost, play_update]
  by_cases h : N.Reachable (t i).1 (t i).2
  · have hσ : σ (t i) = (N.exists_connects_eq_dist h).choose := by simp [σ, h]
    obtain ⟨hc, heq⟩ := (N.exists_connects_eq_dist h).choose_spec
    rw [N.agentCost_of_connects (by simpa [hσ] using hc), ← heq]
    simp only [hσ]
    exact_mod_cast N.payment_le _ i |>.trans (by simp)
  · rw [N.dist_eq_top h]; exact le_top

/-- Every agent's distance is at most the social cost of any action profile. -/
lemma dist_le_stateCost (t : ι → V × V) (a : ι → Finset E) (i : ι) :
    N.dist (t i).1 (t i).2 ≤ (N.bayesGame p).stateCost t a := by
  classical
  by_cases h : ∀ j, N.Connects (a j) (t j).1 (t j).2
  · rw [N.stateCost_bayesGame_of_forall p h]
    exact N.dist_le ((h i).mono (Finset.subset_biUnion_of_mem a (Finset.mem_univ i)))
  · push Not at h
    obtain ⟨j, hj⟩ := h
    rw [N.stateCost_bayesGame_of_not p hj]; exact le_top

/-- Lemma 3.1 of [Alon–Emek–Feldman–Tennenholtz 2010]: every `k`-agent Bayesian NCS game satisfies
`worst-eq^P(G) / opt^C(G) ≤ k`, i.e. `worst-eq^P(G) ≤ k · opt^C(G)`. -/
theorem lemma_3_1 :
    (N.bayesGame p).worstEqP ≤ (Fintype.card ι : ℝ≥0∞) * (N.bayesGame p).optC := by
  refine worstEqP_le _ fun s hs => ?_
  calc (N.bayesGame p).socialCost s
      ≤ ∑ i, ∑ t, p t * N.dist (t i).1 (t i).2 :=
        Finset.sum_le_sum fun i _ => exCost_le_of_isBayesEq N p hs i
    _ = ∑ t, p t * ∑ i, N.dist (t i).1 (t i).2 := by
        rw [Finset.sum_comm]; simp [Finset.mul_sum]
    _ ≤ ∑ t, p t * ((Fintype.card ι : ℝ≥0∞) * ⨅ a, (N.bayesGame p).stateCost t a) := by
        refine Finset.sum_le_sum fun t _ => mul_le_mul_right ?_ _
        calc ∑ i, N.dist (t i).1 (t i).2
            ≤ ∑ _i : ι, ⨅ a, (N.bayesGame p).stateCost t a :=
              Finset.sum_le_sum fun i _ => le_iInf fun a => dist_le_stateCost N p t a i
          _ = _ := by simp [Finset.sum_const, nsmul_eq_mul]
    _ = (Fintype.card ι : ℝ≥0∞) * (N.bayesGame p).optC := by
        simp only [optC, Network.bayesGame_prior, Finset.mul_sum]
        refine Finset.sum_congr rfl fun t _ => ?_
        ring

/-! ### Existence of Bayesian equilibria and Lemma 3.8 -/

/-- A strategy profile is *feasible* if every agent connects her terminals whenever possible. -/
def Feasible (s : ι → V × V → Finset E) : Prop :=
  ∀ i (τ : V × V), N.Reachable τ.1 τ.2 → N.Connects (s i τ) τ.1 τ.2

/-- The Bayesian potential `Q(s) = ∑_t p(t) ∑_e c(e) H(|{i : e ∈ s_i(t_i)}|)`. -/
noncomputable def bayesPotential (s : ι → V × V → Finset E) : ℝ≥0∞ :=
  ∑ t, p t * (N.potential (play s t) : ℝ≥0∞)

lemma bayesPotential_ne_top (s : ι → V × V → Finset E) : bayesPotential N p s ≠ ⊤ :=
  ENNReal.sum_ne_top.2 fun t _ => ENNReal.mul_ne_top (PMF.apply_ne_top p t) ENNReal.coe_ne_top

lemma feasible_update {s : ι → V × V → Finset E} (hs : Feasible N s) (i : ι) {σ : V × V → Finset E}
    (hσ : ∀ τ : V × V, N.Reachable τ.1 τ.2 → N.Connects (σ τ) τ.1 τ.2) :
    Feasible N (Function.update s i σ) := by
  intro j τ hτ
  by_cases h : j = i
  · subst h; simpa using hσ τ hτ
  · simpa [h] using hs j τ hτ

/-- The per-state potential identity for two feasible profiles differing in agent `i`. -/
lemma agentCost_add_potential {s : ι → V × V → Finset E} (hs : Feasible N s) (i : ι)
    {σ : V × V → Finset E} (hσ : ∀ τ : V × V, N.Reachable τ.1 τ.2 → N.Connects (σ τ) τ.1 τ.2)
    (t : ι → V × V) :
    N.agentCost t (play s t) i + (N.potential (play (Function.update s i σ) t) : ℝ≥0∞) =
      N.agentCost t (play (Function.update s i σ) t) i + (N.potential (play s t) : ℝ≥0∞) := by
  rw [play_update]
  by_cases h : N.Reachable (t i).1 (t i).2
  · rw [N.agentCost_of_connects (hs i _ h), N.agentCost_of_connects (by simpa using hσ _ h)]
    exact_mod_cast N.payment_add_potential_update (play s t) i (σ (t i))
  · have h1 : ¬ N.Connects (play s t i) (t i).1 (t i).2 := fun hc => h hc.reachable
    have h2 : ¬ N.Connects (Function.update (play s t) i (σ (t i)) i) (t i).1 (t i).2 :=
      fun hc => h hc.reachable
    rw [N.agentCost_of_not_connects h1, N.agentCost_of_not_connects h2]
    simp

/-- A minimiser of the Bayesian potential over the feasible strategy profiles is a Bayesian
equilibrium. -/
theorem isBayesEq_of_isMin {s : ι → V × V → Finset E} (hs : Feasible N s)
    (hmin : ∀ s', Feasible N s' → bayesPotential N p s ≤ bayesPotential N p s') :
    (N.bayesGame p).IsBayesEq s := by
  classical
  intro i σ
  set s' := Function.update s i σ
  by_cases htop : (N.bayesGame p).exCost s' i = ⊤
  · rw [htop]; exact le_top
  let σ' : V × V → Finset E := fun τ => if N.Connects (σ τ) τ.1 τ.2 then σ τ else s i τ
  have hσ' : ∀ τ : V × V, N.Reachable τ.1 τ.2 → N.Connects (σ' τ) τ.1 τ.2 := by
    intro τ hτ
    by_cases h : N.Connects (σ τ) τ.1 τ.2
    · simp [σ', h]
    · simpa [σ', h] using hs i τ hτ
  set s'' := Function.update s i σ'
  have hfeas : Feasible N s'' := feasible_update N hs i hσ'
  -- the deviation `s''` costs agent `i` the same as `s'`
  have heq : (N.bayesGame p).exCost s'' i = (N.bayesGame p).exCost s' i := by
    unfold exCost
    refine Finset.sum_congr rfl fun t _ => ?_
    by_cases hp : p t = 0
    · simp [hp]
    have hfin : N.agentCost t (play s' t) i ≠ ⊤ := by
      intro h
      apply htop
      exact ENNReal.sum_eq_top.2 ⟨t, Finset.mem_univ _, by simp [hp, h]⟩
    have hc : N.Connects (σ (t i)) (t i).1 (t i).2 := by
      by_contra hc
      apply hfin
      exact N.agentCost_of_not_connects (by simpa [s'] using hc)
    simp only [Network.bayesGame_cost, Network.bayesGame_prior, s'', s', play_update]
    congr 3
    simp [σ', hc]
  have hid : (N.bayesGame p).exCost s i + bayesPotential N p s'' =
      (N.bayesGame p).exCost s'' i + bayesPotential N p s := by
    simp only [exCost, bayesPotential, Network.bayesGame_cost, Network.bayesGame_prior, ← Finset.sum_add_distrib,
      ← mul_add]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [agentCost_add_potential N hs i hσ' t]
  rw [← heq]
  have : (N.bayesGame p).exCost s i + bayesPotential N p s'' ≤
      (N.bayesGame p).exCost s'' i + bayesPotential N p s'' := by
    rw [hid]; gcongr; exact hmin s'' hfeas
  exact (ENNReal.add_le_add_iff_right (bayesPotential_ne_top N p s'')).1 this

lemma feasible_univ : Feasible N (fun (_ : ι) (_ : V × V) => (Finset.univ : Finset E)) :=
  fun _ _ h => h

/-- Every Bayesian NCS game has a pure Bayesian equilibrium (Section 2 of the paper, via
Observation 2.1 and Rosenthal's potential): a minimiser of the Bayesian potential over the feasible
strategy profiles. -/
theorem exists_isBayesEq : ∃ s, Feasible N s ∧ (N.bayesGame p).IsBayesEq s ∧
    ∀ s', Feasible N s' → bayesPotential N p s ≤ bayesPotential N p s' := by
  classical
  obtain ⟨s, hs, hmin⟩ := Finset.exists_min_image
    (Finset.univ.filter fun s : ι → V × V → Finset E => Feasible N s) (bayesPotential N p)
    ⟨_, Finset.mem_filter.2 ⟨Finset.mem_univ _, feasible_univ N⟩⟩
  have hs' := (Finset.mem_filter.1 hs).2
  have hmin' : ∀ s', Feasible N s' → bayesPotential N p s ≤ bayesPotential N p s' :=
    fun s' h => hmin s' (Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩)
  exact ⟨s, hs', isBayesEq_of_isMin N p hs' hmin', hmin'⟩

/-- Lemma 3.8 of [Alon–Emek–Feldman–Tennenholtz 2010]: every `k`-agent Bayesian NCS game satisfies
`best-eq^P(G) ≤ H(k) · opt^P(G)`. -/
theorem lemma_3_8 :
    (N.bayesGame p).bestEqP ≤ (hnum (Fintype.card ι) : ℝ≥0∞) * (N.bayesGame p).optP := by
  classical
  obtain ⟨s, hfs, heq, hmin⟩ := exists_isBayesEq N p
  refine (bestEqP_le _ heq).trans ?_
  by_cases hk : Fintype.card ι = 0
  · have : IsEmpty ι := Fintype.card_eq_zero_iff.1 hk
    simp [socialCost]
  have hH : (hnum (Fintype.card ι) : ℝ≥0∞) ≠ 0 := by
    simpa using (zero_lt_one.trans_le (one_le_hnum (Nat.one_le_iff_ne_zero.2 hk))).ne'
  -- Case A: some type profile of positive probability has an unreachable destination.
  by_cases hA : ∃ t, p t ≠ 0 ∧ ∃ i, ¬ N.Reachable (t i).1 (t i).2
  · obtain ⟨t, hp, i, hi⟩ := hA
    have : (N.bayesGame p).optP = ⊤ := by
      refine iInf_eq_top.2 fun s' => ?_
      rw [socialCost_eq]
      refine ENNReal.sum_eq_top.2 ⟨t, Finset.mem_univ _, ?_⟩
      rw [N.stateCost_bayesGame_of_not p (i := i) (fun hc => hi hc.reachable)]
      simp [hp]
    rw [this, ENNReal.mul_top hH]; exact le_top
  push Not at hA
  -- `K(s) ≤ Q(s)`
  have hKQ : (N.bayesGame p).socialCost s ≤ bayesPotential N p s := by
    rw [socialCost_eq, bayesPotential]
    refine Finset.sum_le_sum fun t _ => ?_
    by_cases hp : p t = 0
    · simp [hp]
    rw [Network.bayesGame_prior, N.stateCost_bayesGame_of_forall p (a := play s t)
      (fun i => hfs i _ (hA t hp i))]
    gcongr
    exact N.totalCost_le_potential _
  refine hKQ.trans ?_
  rw [optP, ENNReal.mul_iInf_of_ne hH ENNReal.coe_ne_top]
  refine le_iInf fun s' => ?_
  -- make `s'` feasible without changing it on the support of the prior
  let s'' : ι → V × V → Finset E := fun i τ =>
    if N.Connects (s' i τ) τ.1 τ.2 then s' i τ else Finset.univ
  have hf'' : Feasible N s'' := by
    intro i τ hτ
    by_cases h : N.Connects (s' i τ) τ.1 τ.2
    · simp [s'', h]
    · simp only [s'', h, ite_false]; exact hτ
  refine (hmin s'' hf'').trans ?_
  rw [bayesPotential, socialCost_eq, Finset.mul_sum]
  refine Finset.sum_le_sum fun t _ => ?_
  by_cases hp : p t = 0
  · simp [hp]
  by_cases hc : ∀ i, N.Connects (s' i (t i)) (t i).1 (t i).2
  · have hplay : play s'' t = play s' t := by
      funext i; simp [s'', hc i]
    rw [hplay, Network.bayesGame_prior, N.stateCost_bayesGame_of_forall p (fun i => by simpa using hc i),
      mul_left_comm]
    gcongr
    exact_mod_cast N.potential_le_hnum_mul_totalCost _
  · push Not at hc
    obtain ⟨i, hi⟩ := hc
    rw [N.stateCost_bayesGame_of_not p (i := i) (by simpa using hi), Network.bayesGame_prior,
      ENNReal.mul_top hp, ENNReal.mul_top hH]
    exact le_top

/-! ### Complete-information games as point-mass priors; Table 1 corollaries -/

lemma exCost_pure (t : ι → V × V) (s : ι → V × V → Finset E) (i : ι) :
    (N.bayesGame (PMF.pure t)).exCost s i = N.agentCost t (play s t) i := by
  rw [exCost, Finset.sum_eq_single t]
  · simp
  · intro t' _ h; simp [PMF.pure_apply, h]
  · simp

lemma socialCost_pure (t : ι → V × V) (s : ι → V × V → Finset E) :
    (N.bayesGame (PMF.pure t)).socialCost s = (N.bayesGame p).stateCost t (play s t) := by
  simp [socialCost, stateCost, exCost_pure]

/-- A Bayesian equilibrium for the point-mass prior at `t` plays a Nash equilibrium of `G_t`. -/
lemma isNashEq_of_isBayesEq_pure {t : ι → V × V} {s : ι → V × V → Finset E}
    (hs : (N.bayesGame (PMF.pure t)).IsBayesEq s) : (N.bayesGame p).IsNashEq t (play s t) := by
  intro i b
  have h := hs i fun _ => b
  rw [exCost_pure, exCost_pure, play_update] at h
  exact h

/-- A Nash equilibrium of `G_t`, played as constant strategies, is a Bayesian equilibrium for the
point-mass prior at `t`. -/
lemma isBayesEq_pure_of_isNashEq {t : ι → V × V} {a : ι → Finset E}
    (ha : (N.bayesGame p).IsNashEq t a) :
    (N.bayesGame (PMF.pure t)).IsBayesEq (fun i _ => a i) := by
  intro i σ
  rw [exCost_pure, exCost_pure, play_update]
  exact ha i (σ (t i))

/-- Price of stability `H(k)` of complete-information NCS games (Anshelevich et al.), as the
point-mass case of Lemma 3.8. -/
theorem bestNash_le_hnum_mul_opt (t : ι → V × V) :
    ⨅ (a : ι → Finset E) (_ : (N.bayesGame p).IsNashEq t a), (N.bayesGame p).stateCost t a ≤
      (hnum (Fintype.card ι) : ℝ≥0∞) * ⨅ a, (N.bayesGame p).stateCost t a := by
  have h := lemma_3_8 N (PMF.pure t)
  refine le_trans ?_ (h.trans ?_)
  · refine le_iInf₂ fun s hs => ?_
    rw [socialCost_pure N p]
    exact iInf₂_le (f := fun a (_ : (N.bayesGame p).IsNashEq t a) => (N.bayesGame p).stateCost t a)
      _ (isNashEq_of_isBayesEq_pure N p hs)
  · gcongr
    refine le_iInf fun a => (iInf_le _ (fun i _ => a i)).trans ?_
    rw [socialCost_pure N p]
    exact le_rfl

/-- Price of anarchy `k` of complete-information NCS games, as the point-mass case of
Lemma 3.1. -/
theorem worstNash_le_card_mul_opt (t : ι → V × V) :
    ⨆ (a : ι → Finset E) (_ : (N.bayesGame p).IsNashEq t a), (N.bayesGame p).stateCost t a ≤
      (Fintype.card ι : ℝ≥0∞) * ⨅ a, (N.bayesGame p).stateCost t a := by
  have h := lemma_3_1 N (PMF.pure t)
  have hC : (N.bayesGame (PMF.pure t)).optC = ⨅ a, (N.bayesGame p).stateCost t a := by
    rw [optC, Finset.sum_eq_single t]
    · simp [stateCost]
    · intro t' _ h; simp [PMF.pure_apply, h]
    · simp
  rw [← hC]
  refine iSup₂_le fun a ha => le_trans ?_ h
  have := le_worstEqP _ (isBayesEq_pure_of_isNashEq N p ha)
  rwa [socialCost_pure N p] at this

/-- Table 1, universal lower bound on `best-eq^P / best-eq^C`: `best-eq^C(G) ≤ H(k) · best-eq^P(G)`,
i.e. the ratio is `Ω(1/log k)` (Anshelevich et al. combined with Observation 2.2). -/
theorem bestEqC_le_hnum_mul_bestEqP :
    (N.bayesGame p).bestEqC ≤ (hnum (Fintype.card ι) : ℝ≥0∞) * (N.bayesGame p).bestEqP := by
  calc (N.bayesGame p).bestEqC ≤ (hnum (Fintype.card ι) : ℝ≥0∞) * (N.bayesGame p).optC := by
        rw [bestEqC, optC, Finset.mul_sum]
        refine Finset.sum_le_sum fun t _ => ?_
        rw [mul_left_comm]
        gcongr
        exact bestNash_le_hnum_mul_opt N p t
    _ ≤ _ := by
        gcongr
        exact (N.bayesGame p).optC_le_optP.trans (N.bayesGame p).optP_le_bestEqP

/-- Table 1, universal lower bound on `worst-eq^P / worst-eq^C`: `worst-eq^C(G) ≤ k · worst-eq^P(G)`,
i.e. the ratio is `Ω(1/k)` (Lemma 3.1 for complete-information games and Observation 2.2). -/
theorem worstEqC_le_card_mul_worstEqP :
    (N.bayesGame p).worstEqC ≤ (Fintype.card ι : ℝ≥0∞) * (N.bayesGame p).worstEqP := by
  obtain ⟨s, -, hs, -⟩ := exists_isBayesEq N p
  calc (N.bayesGame p).worstEqC ≤ (Fintype.card ι : ℝ≥0∞) * (N.bayesGame p).optC := by
        rw [worstEqC, optC, Finset.mul_sum]
        refine Finset.sum_le_sum fun t _ => ?_
        rw [mul_left_comm]
        gcongr
        exact worstNash_le_card_mul_opt N p t
    _ ≤ _ := by
        gcongr
        exact ((N.bayesGame p).observation_2_2 ⟨s, hs⟩).1.trans
          (((N.bayesGame p).observation_2_2 ⟨s, hs⟩).2.1.trans
            ((N.bayesGame p).observation_2_2 ⟨s, hs⟩).2.2)

/-- Table 1, universal upper bounds in directed (and undirected) graphs: `opt^P`, `best-eq^P` and
`worst-eq^P` are at most `k` times `opt^C`, `best-eq^C` and `worst-eq^C` respectively (Lemma 3.1 with
Observation 2.2). -/
theorem table_upper_k :
    (N.bayesGame p).optP ≤ (Fintype.card ι : ℝ≥0∞) * (N.bayesGame p).optC ∧
    (N.bayesGame p).bestEqP ≤ (Fintype.card ι : ℝ≥0∞) * (N.bayesGame p).bestEqC ∧
    (N.bayesGame p).worstEqP ≤ (Fintype.card ι : ℝ≥0∞) * (N.bayesGame p).worstEqC := by
  obtain ⟨s, -, hs, -⟩ := exists_isBayesEq N p
  have h1 := lemma_3_1 N p
  have h2 := (N.bayesGame p).observation_2_2 ⟨s, hs⟩
  have hb : (N.bayesGame p).optC ≤ (N.bayesGame p).bestEqC := (N.bayesGame p).optC_le_bestEqC
  have hw : (N.bayesGame p).bestEqC ≤ (N.bayesGame p).worstEqC := by
    refine (N.bayesGame p).bestEqC_le_worstEqC fun t _ => ?_
    obtain ⟨s', -, hs', -⟩ := exists_isBayesEq N (PMF.pure t)
    exact ⟨_, isNashEq_of_isBayesEq_pure N p hs'⟩
  refine ⟨(h2.2.1.trans h2.2.2).trans h1, (h2.2.2.trans h1).trans ?_, h1.trans ?_⟩
  · gcongr
  · gcongr; exact hb.trans hw

end Podc.BayesianIgnorance

/-! ### Rosenthal's potential is not a Bayesian potential under `∞` costs (end of Section 2)

The paper defines `A_i = 2^E` and the cost of an agent whose edge set misses her path as `∞`, and
claims that `Q(s) = ∑_t p(t) ∑_e c(e) H(|{i : e ∈ s_i(t_i)}|)` is a Bayesian potential. On the
one-agent, one-edge network `0 → 1` no finite-valued function is a Bayesian potential (dropping the
edge changes the agent's cost by `∞`), and the global minimiser of `Q` (the empty profile, `Q = 0`)
is not a Bayesian equilibrium. -/

namespace Podc.BayesianIgnorance.RosenthalCounterexample

open Finset Cslib.GameTheory Cslib.GameTheory.BayesianGame
open scoped ENNReal NNReal

/-- The one-edge directed network `0 → 1` with edge cost `1`. -/
noncomputable def oneEdge : Network (Fin 2) Unit := Network.directed (fun _ => (0, 1)) (fun _ => 1)

/-- The type profile in which the single agent has to connect `0` to `1`. -/
def t₀ : Fin 1 → Fin 2 × Fin 2 := fun _ => (0, 1)

lemma not_connects_empty : ¬ oneEdge.Connects (∅ : Finset Unit) 0 1 := by
  intro h
  rcases Relation.ReflTransGen.cases_head h with h | ⟨_, ⟨e, he, _⟩, _⟩
  · exact absurd h (by decide)
  · simp at he

lemma exCost_pure (s : Fin 1 → Fin 2 × Fin 2 → Finset Unit) :
    (oneEdge.bayesGame (PMF.pure t₀)).exCost s 0 = oneEdge.agentCost t₀ (play s t₀) 0 := by
  classical
  unfold exCost
  rw [Finset.sum_eq_single t₀]
  · simp
  · intro t _ ht; simp [PMF.pure_apply, ht]
  · simp

lemma exCost_empty (s : Fin 1 → Fin 2 × Fin 2 → Finset Unit) (h : s 0 (0, 1) = ∅) :
    (oneEdge.bayesGame (PMF.pure t₀)).exCost s 0 = ⊤ := by
  rw [exCost_pure, oneEdge.agentCost_of_not_connects]
  simpa [t₀, h] using not_connects_empty

lemma exCost_univ_ne_top (s : Fin 1 → Fin 2 × Fin 2 → Finset Unit)
    (h : s 0 (0, 1) = Finset.univ) : (oneEdge.bayesGame (PMF.pure t₀)).exCost s 0 ≠ ⊤ := by
  rw [exCost_pure, oneEdge.agentCost_of_connects]
  · exact ENNReal.coe_ne_top
  · simpa [t₀, h] using oneEdge.connects_single (e := ()) (u := 0) (v := 1) rfl

/-- End of Section 2 (counterexample): the Bayesian NCS game on `oneEdge` with the point prior `t₀`
has no finite-valued Bayesian potential; in particular Rosenthal's `Q` (`bayesPotential`) is not one. -/
theorem no_finite_bayesPotential (Q : (Fin 1 → Fin 2 × Fin 2 → Finset Unit) → ℝ≥0∞)
    (hQ : ∀ s, Q s ≠ ⊤) : ¬ (oneEdge.bayesGame (PMF.pure t₀)).IsBayesPotential Q := by
  intro h
  have := h (fun _ _ => Finset.univ) 0 (fun _ => ∅)
  rw [exCost_empty (Function.update (fun _ _ => Finset.univ) 0 fun _ => ∅) (by simp),
    top_add] at this
  exact ENNReal.add_ne_top.2 ⟨exCost_univ_ne_top (fun _ _ => Finset.univ) rfl, hQ _⟩ this

/-- End of Section 2 (counterexample): the global minimiser of Rosenthal's `Q`, the empty profile,
is not a Bayesian equilibrium (so the paper's "a minimiser of `Q` is an equilibrium", used in the
proof of Lemma 3.8, needs the restriction to feasible profiles of `isBayesEq_of_isMin`). -/
theorem empty_minimises_not_isBayesEq :
    (∀ s, bayesPotential oneEdge (PMF.pure t₀) (fun _ _ => ∅) ≤
      bayesPotential oneEdge (PMF.pure t₀) s) ∧
    ¬ (oneEdge.bayesGame (PMF.pure t₀)).IsBayesEq (fun _ _ => ∅) := by
  constructor
  · intro s
    refine le_of_eq_of_le ?_ zero_le
    simp [bayesPotential, Network.potential, Network.load]
  · intro h
    have := h 0 (fun _ => Finset.univ)
    rw [exCost_empty (fun _ _ => ∅) rfl, top_le_iff] at this
    exact exCost_univ_ne_top _ (by simp) this

end Podc.BayesianIgnorance.RosenthalCounterexample
