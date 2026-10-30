import Mathlib

/-!
# Collaborative search on the plane: the model (§2 of Feinerman–Korman–Lotker–Sereni)

`k` identical probabilistic agents start at the source `s = (0,0)` of the grid `ℤ²` and search, without
communication, for a treasure placed by an adversary at a node `τ`. The search is over once some agent
visits `τ`.

* An agent's behaviour is a probability law on *trajectories* `ℕ → ℤ × ℤ` (position at each time
  step). Agents do not communicate, so the `k` trajectories are independent: the joint law is the
  product measure `Measure.pi ν` (`ν a` is the law of agent `a`). Since the agents know nothing about
  `τ`, the trajectory up to the moment the treasure is found does not depend on `τ`; what an agent does
  afterwards is irrelevant, so a law independent of `τ` is no loss of generality.
* A *uniform* algorithm is a single law `μ` used by all agents whatever `k` is (`ν = fun _ ↦ μ`); an
  algorithm with *advice* is a family `A : ℕ → Measure Traj`, an agent with estimate `k̃` using `A k̃`.
* `findTime ω τ` is the first time some agent is at `τ` (`⊤` if never), and `expectedTime ν τ` its
  expectation — the paper's `T_A(D, k)` for `d(s, τ) = D`.

We do *not* require the trajectories to be nearest-neighbour walks starting at `s`: the lower bounds
only use that an agent occupies one node per time unit, so they hold for this larger class of
"teleporting" agents, in particular for grid walks.

The two probabilistic facts behind all lower bounds of §4 are proved here:

* `sum_visit_le` — in `N` steps one agent visits at most `N + 1` nodes, hence the visit probabilities
  of any finite set of nodes sum to at most `N + 1`;
* `half_le_sum_visit` — Markov's inequality plus a union bound: if the expected time to find `u`
  with agent laws `ν` is at most `T` and `2T ≤ N + 1`, then `∑ₐ Pr[agent a visits u by time N] ≥ 1/2`.
-/

namespace Podc.CollaborativeSearchPlane

open MeasureTheory Finset
open scoped ENNReal

/-- Nodes of the grid `ℤ²`; the source is `0 = (0, 0)`. -/
abbrev Node := ℤ × ℤ

/-- Hop distance `d(s, u)` from the source `(0,0)` to `u` in the grid `ℤ²` (the `ℓ₁` norm). -/
def dist (u : Node) : ℕ := u.1.natAbs + u.2.natAbs

/-- A trajectory of one agent: its position at every time step. -/
abbrev Traj := ℕ → Node

/-- The first time at which one of the agents (trajectories `ω`) is at `τ`; `⊤` if this never
happens. -/
noncomputable def findTime {k : ℕ} (ω : Fin k → Traj) (τ : Node) : ℝ≥0∞ :=
  ⨅ (a : Fin k) (t : ℕ) (_ : ω a t = τ), (t : ℝ≥0∞)

/-- Expected running time when agent `a` moves according to the law `ν a`, independently of the
others, and the treasure is at `τ`. -/
noncomputable def expectedTime {k : ℕ} (ν : Fin k → Measure Traj) (τ : Node) : ℝ≥0∞ :=
  ∫⁻ ω, findTime ω τ ∂(Measure.pi ν)

/-- The optimal order of the running time, `D + D²/k` for `D = d(s, τ)`. -/
noncomputable def optBound (k : ℕ) (τ : Node) : ℝ := dist τ + (dist τ : ℝ) ^ 2 / k

/-- §2: a uniform algorithm (every agent's trajectory has law `μ`, whatever the number `k` of
agents) is `φ(k)`-competitive if `T(D, k) ≤ φ(k) · (D + D²/k)` for all `k ≥ 1` and all treasure
positions `τ ≠ s` (`D ≥ 1`; for `D = 0` the paper's bound says that the agents start at `s`, which
the lower bounds do not need). -/
def IsCompetitive (μ : Measure Traj) (φ : ℕ → ℝ) : Prop :=
  ∀ k : ℕ, 1 ≤ k → ∀ τ : Node, 1 ≤ dist τ →
    expectedTime (fun _ : Fin k => μ) τ ≤ ENNReal.ofReal (φ k * optBound k τ)

/-- The trajectories that visit `u` at some time `t ≤ N`. -/
def visitedBy (N : ℕ) (u : Node) : Set Traj := {ω | ∃ t ≤ N, ω t = u}

theorem measurableSet_visitedBy (N : ℕ) (u : Node) : MeasurableSet (visitedBy N u) := by
  have : visitedBy N u = ⋃ t ∈ Finset.range (N + 1), (fun ω : Traj => ω t) ⁻¹' {u} := by
    ext ω; simp [visitedBy]
  rw [this]
  exact Finset.measurableSet_biUnion _ fun t _ =>
    (measurable_pi_apply t) (measurableSet_singleton u)

-- CSLib candidate
/-- One agent visits at most `N + 1` nodes up to time `N`: the probabilities of visiting the nodes
of any finite set by time `N` sum to at most `N + 1`. -/
theorem sum_visit_le (μ : Measure Traj) [IsProbabilityMeasure μ] (S : Finset Node) (N : ℕ) :
    ∑ u ∈ S, μ (visitedBy N u) ≤ N + 1 := by
  classical
  have hpt : ∀ ω : Traj, ∑ u ∈ S, (visitedBy N u).indicator (fun _ => (1 : ℝ≥0∞)) ω ≤ N + 1 := by
    intro ω
    have h1 : ∑ u ∈ S, (visitedBy N u).indicator (fun _ => (1 : ℝ≥0∞)) ω
        = ((S.filter fun u => ω ∈ visitedBy N u).card : ℝ≥0∞) := by
      simp [Set.indicator_apply, Finset.sum_boole]
    rw [h1]
    have h2 : (S.filter fun u => ω ∈ visitedBy N u) ⊆ (Finset.range (N + 1)).image ω := by
      intro u hu
      rw [Finset.mem_filter] at hu
      obtain ⟨t, ht, rfl⟩ := hu.2
      exact Finset.mem_image.2 ⟨t, Finset.mem_range.2 (Nat.lt_succ_of_le ht), rfl⟩
    have h3 := (Finset.card_le_card h2).trans Finset.card_image_le
    rw [Finset.card_range] at h3
    exact_mod_cast h3
  calc ∑ u ∈ S, μ (visitedBy N u)
      = ∑ u ∈ S, ∫⁻ ω, (visitedBy N u).indicator (fun _ => (1 : ℝ≥0∞)) ω ∂μ := by
        refine Finset.sum_congr rfl fun u _ => ?_
        rw [lintegral_indicator_const (measurableSet_visitedBy N u), one_mul]
    _ = ∫⁻ ω, ∑ u ∈ S, (visitedBy N u).indicator (fun _ => (1 : ℝ≥0∞)) ω ∂μ := by
        rw [lintegral_finsetSum]
        intro u _
        exact (measurable_const.indicator (measurableSet_visitedBy N u))
    _ ≤ ∫⁻ _, ((N : ℝ≥0∞) + 1) ∂μ := lintegral_mono hpt
    _ = N + 1 := by simp

-- CSLib candidate
/-- Markov's inequality and a union bound: if the expected time to find `u` is at most `T` and
`2T ≤ N + 1`, then the probabilities that the individual agents visit `u` by time `N` sum to at
least `1/2`. -/
theorem half_le_sum_visit {k : ℕ} (ν : Fin k → Measure Traj) [∀ a, IsProbabilityMeasure (ν a)]
    (u : Node) (T : ℝ≥0∞) (N : ℕ) (hE : expectedTime ν u ≤ T) (hN : 2 * T ≤ N + 1) :
    1 / 2 ≤ ∑ a, ν a (visitedBy N u) := by
  set P := Measure.pi ν
  set bad : Set (Fin k → Traj) := Set.univ.pi fun _ => (visitedBy N u)ᶜ with hbad
  have hbadm : MeasurableSet bad :=
    MeasurableSet.univ_pi fun _ => (measurableSet_visitedBy N u).compl
  -- on `bad`, the treasure is not found by time `N`
  have hge : ∀ ω ∈ bad, ((N : ℝ≥0∞) + 1) ≤ findTime ω u := by
    intro ω hω
    simp only [hbad, Set.mem_pi, Set.mem_univ, Set.mem_compl_iff, visitedBy, Set.mem_ofPred_eq,
      not_exists, not_and, forall_const] at hω
    simp only [findTime, le_iInf_iff]
    intro a t ht
    have : N < t := by
      by_contra h
      exact hω a t (not_lt.1 h) ht
    exact_mod_cast Nat.succ_le_of_lt this
  have hmark : ((N : ℝ≥0∞) + 1) * P bad ≤ T := by
    calc ((N : ℝ≥0∞) + 1) * P bad = ∫⁻ ω, bad.indicator (fun _ => (N : ℝ≥0∞) + 1) ω ∂P := by
          rw [lintegral_indicator_const hbadm]
      _ ≤ ∫⁻ ω, findTime ω u ∂P := by
          refine lintegral_mono fun ω => ?_
          by_cases h : ω ∈ bad
          · simpa [Set.indicator_of_mem h] using hge ω h
          · simp [Set.indicator_of_notMem h]
      _ ≤ T := hE
  have hbad_le : P bad ≤ 1 / 2 := by
    have h2 : 2 * (((N : ℝ≥0∞) + 1) * P bad) ≤ (N : ℝ≥0∞) + 1 :=
      (by gcongr : 2 * (((N : ℝ≥0∞) + 1) * P bad) ≤ 2 * T).trans hN
    have hne : ((N : ℝ≥0∞) + 1) ≠ 0 := by positivity
    have hnt : ((N : ℝ≥0∞) + 1) ≠ ⊤ := by simp
    rw [← mul_assoc, mul_comm 2, mul_assoc] at h2
    have h3 : 2 * P bad ≤ 1 := by
      exact (ENNReal.mul_le_mul_iff_right hne hnt).1 (by simpa using h2)
    rw [ENNReal.le_div_iff_mul_le (by simp) (by simp), mul_comm]
    exact h3
  have hgood : 1 / 2 ≤ P badᶜ := by
    rw [prob_compl_eq_one_sub hbadm]
    refine ENNReal.le_sub_of_add_le_left (by simp) ?_
    calc P bad + 1 / 2 ≤ 1 / 2 + 1 / 2 := by gcongr
      _ = 1 := ENNReal.add_halves 1
  have hsub : badᶜ ⊆ ⋃ a ∈ (Finset.univ : Finset (Fin k)),
      (Function.eval a) ⁻¹' visitedBy N u := by
    intro ω hω
    simp only [hbad, Set.mem_compl_iff, Set.mem_pi, Set.mem_univ, forall_const, not_forall,
      not_not] at hω
    obtain ⟨a, ha⟩ := hω
    simp only [Set.mem_iUnion, Set.mem_preimage, Function.eval]
    exact ⟨a, Finset.mem_univ a, ha⟩
  calc 1 / 2 ≤ P badᶜ := hgood
    _ ≤ P (⋃ a ∈ (Finset.univ : Finset (Fin k)), (Function.eval a) ⁻¹' visitedBy N u) :=
        measure_mono hsub
    _ ≤ ∑ a, P ((Function.eval a) ⁻¹' visitedBy N u) := measure_biUnion_finset_le _ _
    _ = ∑ a, ν a (visitedBy N u) := by
        refine Finset.sum_congr rfl fun a _ => ?_
        exact (measurePreserving_eval ν a).measure_preimage
          (measurableSet_visitedBy N u).nullMeasurableSet

/-! ### Visits of the anti-diagonals of the first quadrant -/

/-- The first quadrant `ℕ × ℕ` inside the grid. -/
def quad (q : ℕ × ℕ) : Node := ((q.1 : ℤ), (q.2 : ℤ))

theorem quad_injective : Function.Injective quad := by
  intro q q' h
  simp only [quad, Prod.mk.injEq, Nat.cast_inj] at h
  exact Prod.ext h.1 h.2

theorem dist_quad (q : ℕ × ℕ) : dist (quad q) = q.1 + q.2 := by
  simp [dist, quad]

/-- The expected number of nodes `(x, y)` with `x, y ≥ 0` and `x + y = n` that one agent with law
`μ` visits by time `N`. -/
noncomputable def diagMass (μ : Measure Traj) (N n : ℕ) : ℝ :=
  ∑ q ∈ antidiagonal n, (μ (visitedBy N (quad q))).toReal

theorem diagMass_nonneg (μ : Measure Traj) (N n : ℕ) : 0 ≤ diagMass μ N n :=
  Finset.sum_nonneg fun _ _ => ENNReal.toReal_nonneg

/-- The anti-diagonal masses of any set of distances sum to at most `N + 1`. -/
theorem sum_diagMass_le (μ : Measure Traj) [IsProbabilityMeasure μ] (s : Finset ℕ) (N : ℕ) :
    ∑ n ∈ s, diagMass μ N n ≤ N + 1 := by
  classical
  have hdisj : (s : Set ℕ).PairwiseDisjoint fun n => antidiagonal n := by
    intro n _ m _ hnm
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro q hq hq'
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hq hq'
    exact hnm (hq.symm.trans hq')
  have h1 : ∑ n ∈ s, diagMass μ N n
      = ∑ u ∈ (s.biUnion fun n => antidiagonal n).image quad, (μ (visitedBy N u)).toReal := by
    rw [Finset.sum_image (fun x _ y _ h => quad_injective h), Finset.sum_biUnion hdisj]
    rfl
  rw [h1, ← ENNReal.toReal_sum (fun u _ => measure_ne_top μ _)]
  have h2 := sum_visit_le μ ((s.biUnion fun n => antidiagonal n).image quad) N
  have h3 : (∑ u ∈ (s.biUnion fun n => antidiagonal n).image quad, μ (visitedBy N u)).toReal
      ≤ ((N : ℝ≥0∞) + 1).toReal := ENNReal.toReal_mono (by simp) h2
  refine h3.trans (le_of_eq ?_)
  rw [ENNReal.toReal_add (by simp) (by simp)]
  simp

/-- If, with `k` independent agents of law `μ`, the expected time to find every node at distance `n`
is at most `T`, and `2T ≤ N + 1`, then `diagMass μ N n ≥ (n + 1) / (2k)`. -/
theorem diagMass_ge (μ : Measure Traj) [IsProbabilityMeasure μ] {k : ℕ} (hk : 0 < k) (N n : ℕ)
    (T : ℝ) (hT : 2 * T ≤ N + 1)
    (hE : ∀ u : Node, dist u = n → expectedTime (fun _ : Fin k => μ) u ≤ ENNReal.ofReal T) :
    ((n : ℝ) + 1) / (2 * k) ≤ diagMass μ N n := by
  have hq : ∀ q ∈ antidiagonal n, 1 / (2 * (k : ℝ)) ≤ (μ (visitedBy N (quad q))).toReal := by
    intro q hq
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hq
    have hT' : 2 * ENNReal.ofReal T ≤ (N : ℝ≥0∞) + 1 := by
      rcases le_or_gt T 0 with h0 | h0
      · simp [ENNReal.ofReal_of_nonpos h0]
      · have : ENNReal.ofReal (2 * T) ≤ ENNReal.ofReal ((N : ℝ) + 1) := ENNReal.ofReal_le_ofReal hT
        rw [ENNReal.ofReal_mul (by norm_num)] at this
        simpa [ENNReal.ofReal_add, ENNReal.ofReal_natCast] using this
    have h := half_le_sum_visit (fun _ : Fin k => μ) (quad q) _ N
      (hE _ (by rw [dist_quad, hq])) hT'
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h
    have h' := ENNReal.toReal_mono (ENNReal.mul_ne_top (by simp) (measure_ne_top μ _)) h
    rw [ENNReal.toReal_mul] at h'
    simp only [one_div, ENNReal.toReal_inv, ENNReal.toReal_ofNat, ENNReal.toReal_natCast] at h'
    have hk' : (0 : ℝ) < k := by exact_mod_cast hk
    rw [one_div, mul_inv, ← div_eq_mul_inv, div_le_iff₀ hk']
    linarith
  calc ((n : ℝ) + 1) / (2 * k) = ∑ _q ∈ antidiagonal n, 1 / (2 * (k : ℝ)) := by
        rw [Finset.sum_const, Finset.Nat.card_antidiagonal, nsmul_eq_mul]; push_cast; ring
    _ ≤ diagMass μ N n := Finset.sum_le_sum hq

end Podc.CollaborativeSearchPlane
