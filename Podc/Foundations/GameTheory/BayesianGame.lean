/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

-- CSLib candidate: Cslib/Foundations/GameTheory/BayesianGame.lean

/-!
# Finite Bayesian cost games

A *Bayesian game* (Harsanyi) with finitely many agents `i : ι`, finite action spaces `A i` and finite
type spaces `T i`: a type profile `t : ∀ i, T i` is drawn from a common prior `p`, every agent `i`
learns only her own type `t i` and chooses an action by a (pure) strategy `s i : T i → A i`.
Costs are `ℝ≥0∞`-valued, so that infinite costs (e.g. "the agent does not reach her destination"
in network cost sharing games) are allowed; expectations are finite sums `∑ t, p t * X t` (with
`0 * ⊤ = 0`, i.e. type profiles of prior probability `0` are irrelevant).

## Main definitions

* `BayesianGame ι A T`: cost functions `cost i t a` and the common prior `prior : PMF (∀ i, T i)`.
* `exCost s i` (ex-ante cost `C_i(s)`), `socialCost s` (`K(s)`), `stateCost t a` (`K_t(a)`).
* `IsBayesEq s` (pure Bayesian equilibrium), `IsNashEq t a` (pure Nash equilibrium of the
  underlying complete-information game `G_t`).
* The six quantities of Alon–Emek–Feldman–Tennenholtz (*Bayesian ignorance*, PODC 2010):
  `optP`, `bestEqP`, `worstEqP` (partial information) and `optC`, `bestEqC`, `worstEqC`
  (complete information, expectation over the prior).
* `IsBayesPotential Q`, `IsPotentialAt t q`: exact potentials, written additively
  (`C_i(s) + Q(s') = C_i(s') + Q(s)` for unilateral deviations `s'`), which is the usual
  `C_i(s) - C_i(s') = Q(s) - Q(s')` for finite values and avoids `⊤ - ⊤`.

## Main statements

* `observation_2_1`: potentials of all underlying games average to a Bayesian potential.
* `isBayesEq_of_isMin`, `exists_isBayesEq_of_potential`: a finite potential has a minimiser, which
  is a Bayesian equilibrium.
* `optC_le_optP`, `optP_le_bestEqP`, `bestEqP_le_worstEqP` (Observation 2.2).
-/

open Finset
open scoped ENNReal

namespace Cslib.GameTheory

/-- A finite Bayesian cost game: agents `ι`, actions `A i`, types `T i`, ℝ≥0∞-valued costs
`cost i t a` of agent `i` under type profile `t` and action profile `a`, and the common prior. -/
structure BayesianGame (ι : Type*) (A T : ι → Type*) where
  /-- `cost i t a`: the cost of agent `i` from the action profile `a` under the type profile `t`
  (the cost function `C_{i,t}` of the underlying game `G_t`). -/
  cost : ι → (∀ i, T i) → (∀ i, A i) → ℝ≥0∞
  /-- The common prior over type profiles. -/
  prior : PMF (∀ i, T i)

namespace BayesianGame

variable {ι : Type*} {A T : ι → Type*}

/-- The action profile played under the strategy profile `s` when the type profile is `t`. -/
def play (s : ∀ i, T i → A i) (t : ∀ i, T i) : ∀ i, A i := fun i => s i (t i)

@[simp] lemma play_apply (s : ∀ i, T i → A i) (t : ∀ i, T i) (i : ι) : play s t i = s i (t i) :=
  rfl

lemma play_update [DecidableEq ι] (s : ∀ i, T i → A i) (i : ι) (σ : T i → A i)
    (t : ∀ i, T i) : play (Function.update s i σ) t = Function.update (play s t) i (σ (t i)) := by
  funext j
  by_cases h : j = i
  · subst h; simp [play]
  · simp [play, h]

variable [Fintype ι] [DecidableEq ι] [∀ i, Fintype (T i)]
variable (G : BayesianGame ι A T)

/-- The social cost `K_t(a) = ∑_i C_{i,t}(a)` of the action profile `a` in the underlying game
`G_t`. -/
noncomputable def stateCost (t : ∀ i, T i) (a : ∀ i, A i) : ℝ≥0∞ := ∑ i, G.cost i t a

/-- The ex-ante (expected) cost `C_i(s) = ∑_t p(t) · C_{i,t}(s(t))` of agent `i`. -/
noncomputable def exCost (s : ∀ i, T i → A i) (i : ι) : ℝ≥0∞ :=
  ∑ t, G.prior t * G.cost i t (play s t)

/-- The social cost `K(s) = ∑_i C_i(s)` of a strategy profile. -/
noncomputable def socialCost (s : ∀ i, T i → A i) : ℝ≥0∞ := ∑ i, G.exCost s i

lemma socialCost_eq (s : ∀ i, T i → A i) :
    G.socialCost s = ∑ t, G.prior t * G.stateCost t (play s t) := by
  simp only [socialCost, exCost, stateCost, Finset.mul_sum]
  exact Finset.sum_comm

/-- A (pure) Bayesian equilibrium: no agent lowers her ex-ante cost by a unilateral deviation. -/
def IsBayesEq (s : ∀ i, T i → A i) : Prop :=
  ∀ i (σ : T i → A i), G.exCost s i ≤ G.exCost (Function.update s i σ) i

/-- A (pure) Nash equilibrium of the underlying complete-information game `G_t`. -/
def IsNashEq (t : ∀ i, T i) (a : ∀ i, A i) : Prop :=
  ∀ i (b : A i), G.cost i t a ≤ G.cost i t (Function.update a i b)

/-- `opt^P(G) = min_s K(s)`. -/
noncomputable def optP : ℝ≥0∞ := ⨅ s : (∀ i, T i → A i), G.socialCost s

/-- `best-eq^P(G)`: the least social cost of a Bayesian equilibrium (`⊤` if there is none). -/
noncomputable def bestEqP : ℝ≥0∞ := ⨅ (s : ∀ i, T i → A i) (_ : G.IsBayesEq s), G.socialCost s

/-- `worst-eq^P(G)`: the largest social cost of a Bayesian equilibrium (`0` if there is none). -/
noncomputable def worstEqP : ℝ≥0∞ := ⨆ (s : ∀ i, T i → A i) (_ : G.IsBayesEq s), G.socialCost s

/-- `opt^C(G) = ∑_t p(t) · min_a K_t(a)`. -/
noncomputable def optC : ℝ≥0∞ := ∑ t, G.prior t * ⨅ a, G.stateCost t a

/-- `best-eq^C(G) = ∑_t p(t) · min_{a Nash eq. of G_t} K_t(a)`. -/
noncomputable def bestEqC : ℝ≥0∞ :=
  ∑ t, G.prior t * ⨅ (a : ∀ i, A i) (_ : G.IsNashEq t a), G.stateCost t a

/-- `worst-eq^C(G) = ∑_t p(t) · max_{a Nash eq. of G_t} K_t(a)`. -/
noncomputable def worstEqC : ℝ≥0∞ :=
  ∑ t, G.prior t * ⨆ (a : ∀ i, A i) (_ : G.IsNashEq t a), G.stateCost t a

/-! ### Observation 2.2 -/

theorem optC_le_socialCost (s : ∀ i, T i → A i) : G.optC ≤ G.socialCost s := by
  rw [socialCost_eq, optC]
  gcongr with t
  exact iInf_le _ _

/-- Observation 2.2, first inequality: `opt^C(G) ≤ opt^P(G)`. -/
theorem optC_le_optP : G.optC ≤ G.optP := le_iInf G.optC_le_socialCost

/-- Observation 2.2, second inequality: `opt^P(G) ≤ best-eq^P(G)`. -/
theorem optP_le_bestEqP : G.optP ≤ G.bestEqP :=
  le_iInf₂ fun s _ => iInf_le _ s

/-- Observation 2.2, third inequality: `best-eq^P(G) ≤ worst-eq^P(G)` if a pure Bayesian
equilibrium exists. -/
theorem bestEqP_le_worstEqP {s : ∀ i, T i → A i} (hs : G.IsBayesEq s) :
    G.bestEqP ≤ G.worstEqP :=
  (iInf₂_le s hs).trans (le_iSup₂ (f := fun s (_ : G.IsBayesEq s) => G.socialCost s) s hs)

/-- Observation 2.2: `opt^C(G) ≤ opt^P(G) ≤ best-eq^P(G) ≤ worst-eq^P(G)` for every Bayesian game
admitting a pure Bayesian equilibrium. -/
theorem observation_2_2 (h : ∃ s, G.IsBayesEq s) :
    G.optC ≤ G.optP ∧ G.optP ≤ G.bestEqP ∧ G.bestEqP ≤ G.worstEqP :=
  ⟨G.optC_le_optP, G.optP_le_bestEqP, h.elim fun _ hs => G.bestEqP_le_worstEqP hs⟩

lemma le_worstEqP {s : ∀ i, T i → A i} (hs : G.IsBayesEq s) : G.socialCost s ≤ G.worstEqP :=
  le_iSup₂ (f := fun s (_ : G.IsBayesEq s) => G.socialCost s) s hs

lemma bestEqP_le {s : ∀ i, T i → A i} (hs : G.IsBayesEq s) : G.bestEqP ≤ G.socialCost s :=
  iInf₂_le s hs

lemma worstEqP_le {c : ℝ≥0∞} (h : ∀ s, G.IsBayesEq s → G.socialCost s ≤ c) : G.worstEqP ≤ c :=
  iSup₂_le h

/-- The complete-information analogue: `opt^C(G) ≤ best-eq^C(G)`. -/
theorem optC_le_bestEqC : G.optC ≤ G.bestEqC := by
  unfold optC bestEqC
  refine Finset.sum_le_sum fun t _ => mul_le_mul_right ?_ _
  exact le_iInf₂ fun a _ => iInf_le (fun a => G.stateCost t a) a

/-- `best-eq^C(G) ≤ worst-eq^C(G)` if every underlying game of positive prior probability has a
pure Nash equilibrium. -/
theorem bestEqC_le_worstEqC (h : ∀ t, G.prior t ≠ 0 → ∃ a, G.IsNashEq t a) :
    G.bestEqC ≤ G.worstEqC := by
  unfold bestEqC worstEqC
  refine Finset.sum_le_sum fun t _ => ?_
  by_cases ht : G.prior t = 0
  · simp [ht]
  obtain ⟨a, ha⟩ := h t ht
  gcongr
  exact (iInf₂_le (f := fun a (_ : G.IsNashEq t a) => G.stateCost t a) a ha).trans
    (le_iSup₂ (f := fun a (_ : G.IsNashEq t a) => G.stateCost t a) a ha)

/-! ### Deviations at a single type -/

/-- In a Bayesian equilibrium no agent with finite ex-ante cost gains by deviating at a single type
`τ` (the paper's "conditional" characterisation, written without dividing by `Pr[t_i = τ]`).
The finiteness hypothesis is needed: with infinite costs at another type the ex-ante comparison
`⊤ ≤ ⊤` carries no information about `τ`. -/
theorem IsBayesEq.cond_le [∀ i, DecidableEq (T i)] {s : ∀ i, T i → A i} (hs : G.IsBayesEq s)
    (i : ι) (hfin : G.exCost s i ≠ ⊤) (τ : T i) (b : A i) :
    ∑ t with t i = τ, G.prior t * G.cost i t (play s t) ≤
      ∑ t with t i = τ, G.prior t * G.cost i t (Function.update (play s t) i b) := by
  have h := hs i (Function.update (s i) τ b)
  unfold exCost at h
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun t => t i = τ),
    ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun t => t i = τ)
      (f := fun t => G.prior t * G.cost i t (play (Function.update s i _) t))] at h
  have h1 : ∑ t with t i = τ, G.prior t * G.cost i t (play (Function.update s i
      (Function.update (s i) τ b)) t) =
      ∑ t with t i = τ, G.prior t * G.cost i t (Function.update (play s t) i b) := by
    refine Finset.sum_congr rfl fun t ht => ?_
    rw [(Finset.mem_filter.1 ht).2.symm, play_update]
    simp
  have h2 : ∑ t with ¬ t i = τ, G.prior t * G.cost i t (play (Function.update s i
      (Function.update (s i) τ b)) t) = ∑ t with ¬ t i = τ, G.prior t * G.cost i t (play s t) := by
    refine Finset.sum_congr rfl fun t ht => ?_
    rw [play_update, Function.update_of_ne (Finset.mem_filter.1 ht).2]
    congr 2
    funext j
    by_cases hj : j = i
    · subst hj; simp
    · simp [hj]
  rw [h1, h2] at h
  refine (ENNReal.add_le_add_iff_right (ne_top_of_le_ne_top hfin ?_)).1 h
  exact Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)

/-- Sums against a pushed-forward prior. -/
lemma sum_map_mul {Ω X : Type*} [Fintype Ω] [Fintype X] (f : Ω → X) (q : PMF Ω)
    (g : X → ℝ≥0∞) : ∑ x, (q.map f) x * g x = ∑ ω, q ω * g (f ω) := by
  classical
  simp only [PMF.map_apply, tsum_fintype]
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ω _ => ?_
  rw [Finset.sum_eq_single (f ω)]
  · simp
  · intro x _ hx; simp only [mul_eq_zero, ite_eq_right_iff]; exact Or.inl fun h => absurd h hx
  · simp

/-! ### Potentials (Observation 2.1) -/

/-- `Q` is an exact Bayesian potential (additive form of `C_i(s) - C_i(s') = Q(s) - Q(s')` for every
unilateral deviation `s' = (s_{-i}, σ)`). -/
def IsBayesPotential (Q : (∀ i, T i → A i) → ℝ≥0∞) : Prop :=
  ∀ (s : ∀ i, T i → A i) (i : ι) (σ : T i → A i),
    G.exCost s i + Q (Function.update s i σ) = G.exCost (Function.update s i σ) i + Q s

/-- `q` is an exact potential of the underlying game `G_t` (additive form). -/
def IsPotentialAt (t : ∀ i, T i) (q : (∀ i, A i) → ℝ≥0∞) : Prop :=
  ∀ (a : ∀ i, A i) (i : ι) (b : A i),
    G.cost i t a + q (Function.update a i b) = G.cost i t (Function.update a i b) + q a

/-- Observation 2.1: if every underlying game `G_t` has a potential `q_t`, then
`Q(s) = ∑_t p(t) · q_t(s(t))` is a Bayesian potential. -/
theorem observation_2_1 (q : (∀ i, T i) → (∀ i, A i) → ℝ≥0∞) (hq : ∀ t, G.IsPotentialAt t (q t)) :
    G.IsBayesPotential fun s => ∑ t, G.prior t * q t (play s t) := by
  intro s i σ
  simp only [exCost, ← Finset.sum_add_distrib, ← mul_add, play_update]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [hq t (play s t) i (σ (t i))]

/-- A minimiser of a finite Bayesian potential is a Bayesian equilibrium. -/
theorem isBayesEq_of_isMin {Q : (∀ i, T i → A i) → ℝ≥0∞} (hQ : G.IsBayesPotential Q)
    {s : ∀ i, T i → A i} (hmin : ∀ s', Q s ≤ Q s') (hfin : ∀ s', Q s' ≠ ⊤) : G.IsBayesEq s := by
  intro i σ
  have h := hQ s i σ
  have : G.exCost s i + Q (Function.update s i σ) ≤
      G.exCost (Function.update s i σ) i + Q (Function.update s i σ) := by
    rw [h]; gcongr; exact hmin _
  exact (ENNReal.add_le_add_iff_right (hfin _)).1 this

/-- A Bayesian game with a finite Bayesian potential has a pure Bayesian equilibrium. -/
theorem exists_isBayesEq_of_potential [∀ i, Fintype (A i)] [∀ i, DecidableEq (T i)]
    [∀ i, Nonempty (A i)] {Q : (∀ i, T i → A i) → ℝ≥0∞} (hQ : G.IsBayesPotential Q)
    (hfin : ∀ s', Q s' ≠ ⊤) : ∃ s, G.IsBayesEq s := by
  obtain ⟨s, -, hs⟩ := Finset.exists_min_image (Finset.univ : Finset (∀ i, T i → A i)) Q
    Finset.univ_nonempty
  exact ⟨s, G.isBayesEq_of_isMin hQ (fun s' => hs s' (Finset.mem_univ _)) hfin⟩

end BayesianGame

end Cslib.GameTheory
