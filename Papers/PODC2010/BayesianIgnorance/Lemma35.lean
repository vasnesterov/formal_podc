import Papers.PODC2010.BayesianIgnorance.UpperBounds

/-!
# Lemma 3.5: the reduction from online Steiner tree

Alon, Emek, Feldman, Tennenholtz, *Bayesian Ignorance* (PODC 2010), Lemma 3.5: there are `Θ(n)`-agent
Bayesian NCS games on undirected `n`-vertex graphs with `opt^P(G) / opt^C(G) = Ω(log n)`.

The paper reduces from (a distributional version of) the online Steiner tree problem: for every
distribution `q` over request sequences `σ = ⟨v_1, …, v_{|σ|}⟩` (to be connected to a root `v₀`) it
builds an `n`-agent Bayesian NCS game `G^q` (agent `i` has type `(v_i, v₀)`, or `(v₀, v₀)` if
`i > |σ|`) and turns every strategy profile `s` into a deterministic online algorithm `ALG_q`
(at step `i` buy the edges of `s_i(v_i, v₀)` not bought before) with `E_q[ALG_q] ≤ K(s)`, while
`opt^C(G^q) = E_q[OPT]`. Hence `opt^P(G^q)/opt^C(G^q) ≥ E_q[ALG]/E_q[OPT]` for some deterministic
online algorithm, and a distribution `q` on which every deterministic online algorithm pays
`Ω(log n) · E_q[OPT]` (the Imase–Waxman lower bound on the diamond graph, made distributional
via Yao's principle) gives the lemma.

We formalize the reduction (`exists_onlineAlg`, `optC_le_expected_opt`, `lemma_3_5`) for an
arbitrary network; the online lower bound of Imase–Waxman is **not** formalized and enters
`lemma_3_5` as the hypothesis `hLB`.

Request sequences of length `≤ n` are represented as `σ : Fin n → Option V` (`σ i = some v`: the
`i`-th request is `v`; `none`: no request at step `i`), a harmless generalization of `V^{≤ n}`.
-/

open Finset Cslib.GameTheory Cslib.GameTheory.BayesianGame
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false

namespace Podc.BayesianIgnorance.Lemma35

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
  (N : Network V E) (v₀ : V) {n : ℕ}

/-- Request sequences of length `≤ n`, padded with `none`. -/
abbrev Req (V : Type*) (n : ℕ) := Fin n → Option V

/-- The type profile `t^σ`: agent `i` must connect `v_i` to the root, or nothing. -/
def typeOf (σ : Req V n) : Fin n → V × V := fun i => ((σ i).getD v₀, v₀)

/-- A deterministic online Steiner tree algorithm: at step `i` it buys `buy i σ`, which may only
depend on the requests `σ j`, `j ≤ i`, seen so far. -/
structure OnlineAlg (V E : Type*) (n : ℕ) where
  /-- The edges bought at step `i`. -/
  buy : Fin n → Req V n → Finset E
  /-- Online: the decision at step `i` depends only on the first `i` requests. -/
  causal : ∀ i σ σ', (∀ j ≤ i, σ j = σ' j) → buy i σ = buy i σ'

namespace OnlineAlg

/-- The algorithm serves the request sequence `σ`: after step `i` the edges bought so far
connect the `i`-th request to the root. -/
def Valid (A : OnlineAlg V E n) (σ : Req V n) : Prop :=
  ∀ i v, σ i = some v → N.Connects ((Finset.univ.filter (· ≤ i)).biUnion (A.buy · σ)) v v₀

/-- `ALG(σ) = ∑_i ∑_{e ∈ F_i} c(e)`. -/
noncomputable def cost (A : OnlineAlg V E n) (σ : Req V n) : ℝ≥0 :=
  ∑ i, ∑ e ∈ A.buy i σ, N.cost e

end OnlineAlg

/-- `OPT(σ)`: the cost of a cheapest edge set connecting all requests to the root (a minimum
Steiner tree). -/
noncomputable def steinerOpt (σ : Req V n) : ℝ≥0∞ :=
  ⨅ (F : Finset E) (_ : ∀ i v, σ i = some v → N.Connects F v v₀), ((∑ e ∈ F, N.cost e : ℝ≥0) : ℝ≥0∞)

/-- The Bayesian NCS game `G^q` with `p(t^σ) = q(σ)`. -/
noncomputable def game (q : PMF (Req V n)) := N.bayesGame (q.map (typeOf v₀))

/-- `opt^C(G^q) ≤ E_q[OPT]`. -/
theorem optC_le_expected_opt (q : PMF (Req V n)) :
    (game N v₀ q).optC ≤ ∑ σ, q σ * steinerOpt N v₀ σ := by
  rw [BayesianGame.optC, game, Network.bayesGame_prior, sum_map_mul]
  refine Finset.sum_le_sum fun σ _ => mul_le_mul_right ?_ _
  refine le_iInf₂ fun F hF => ?_
  refine (iInf_le _ (fun _ => F)).trans ?_
  have hc : ∀ i, N.Connects ((fun _ : Fin n => F) i) (typeOf v₀ σ i).1 (typeOf v₀ σ i).2 := by
    intro i
    simp only [typeOf]
    cases h : σ i with
    | none => exact N.connects_refl _ _
    | some v => exact hF i v h
  rw [N.stateCost_bayesGame_of_forall _ hc, Network.totalCost]
  gcongr
  intro e he
  obtain ⟨_, -, h⟩ := Finset.mem_biUnion.1 he
  exact h

/-- The online algorithm `ALG_q` built from a strategy profile `s`: at step `i` buy the edges of
`s_i(t^σ_i)` not bought before. -/
def algOf (s : Fin n → V × V → Finset E) : OnlineAlg V E n where
  buy i σ := s i (typeOf v₀ σ i) \
    (Finset.univ.filter (· < i)).biUnion fun j => s j (typeOf v₀ σ j)
  causal i σ σ' h := by
    have hi : typeOf v₀ σ i = typeOf v₀ σ' i := by simp [typeOf, h i le_rfl]
    have hj : ∀ j ∈ Finset.univ.filter (· < i), s j (typeOf v₀ σ j) = s j (typeOf v₀ σ' j) := by
      intro j hj
      simp [typeOf, h j (Finset.mem_filter.1 hj).2.le]
    simp only [hi, Finset.biUnion_congr rfl hj]

lemma subset_biUnion_algOf (s : Fin n → V × V → Finset E) (σ : Req V n) (i : Fin n) :
    s i (typeOf v₀ σ i) ⊆ (Finset.univ.filter (· ≤ i)).biUnion ((algOf v₀ s).buy · σ) := by
  intro e he
  set J := Finset.univ.filter fun j => e ∈ s j (typeOf v₀ σ j)
  have hJ : J.Nonempty := ⟨i, by simp [J, he]⟩
  set j₀ := J.min' hJ
  have hj₀ : e ∈ s j₀ (typeOf v₀ σ j₀) := by simpa [J] using J.min'_mem hJ
  refine Finset.mem_biUnion.2 ⟨j₀, by simpa using J.min'_le i (by simp [J, he]), ?_⟩
  simp only [algOf, Finset.mem_sdiff, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ,
    true_and, not_exists, not_and]
  refine ⟨hj₀, fun j hj hej => ?_⟩
  exact absurd (J.min'_le j (by simp [J, hej])) (not_le.2 hj)

lemma algOf_cost_le (s : Fin n → V × V → Finset E) (σ : Req V n) :
    (algOf v₀ s).cost N σ ≤ N.totalCost (BayesianGame.play s (typeOf v₀ σ)) := by
  classical
  rw [OnlineAlg.cost, ← Finset.sum_biUnion]
  · refine Finset.sum_le_sum_of_subset fun e he => ?_
    obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.1 he
    exact Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, (Finset.mem_sdiff.1 hi).1⟩
  · intro i _ j _ hij
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro e hei hej
    simp only [algOf, Finset.mem_sdiff, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ,
      true_and, not_exists, not_and] at hei hej
    rcases lt_or_gt_of_ne hij with h | h
    · exact hej.2 i h hei.1
    · exact hei.2 j h hej.1

/-- The reduction of Lemma 3.5: every strategy profile `s` of `G^q` with finite social cost yields a
deterministic online algorithm, valid on every request sequence of positive probability, with
`E_q[ALG] ≤ K(s)`. -/
theorem exists_onlineAlg (q : PMF (Req V n)) (s : Fin n → V × V → Finset E)
    (hs : (game N v₀ q).socialCost s ≠ ⊤) :
    ∃ A : OnlineAlg V E n, (∀ σ, q σ ≠ 0 → A.Valid N v₀ σ) ∧
      ∑ σ, q σ * (A.cost N σ : ℝ≥0∞) ≤ (game N v₀ q).socialCost s := by
  have hK : ∀ σ, q σ ≠ 0 →
      (game N v₀ q).stateCost (typeOf v₀ σ) (BayesianGame.play s (typeOf v₀ σ)) ≠ ⊤ := by
    intro σ hq htop
    apply hs
    rw [socialCost_eq, game, Network.bayesGame_prior, sum_map_mul]
    exact ENNReal.sum_eq_top.2 ⟨σ, Finset.mem_univ _, by rw [game] at htop; simp [hq, htop]⟩
  have hconn : ∀ σ, q σ ≠ 0 → ∀ i,
      N.Connects (s i (typeOf v₀ σ i)) (typeOf v₀ σ i).1 (typeOf v₀ σ i).2 := by
    intro σ hq i
    by_contra h
    exact hK σ hq (N.stateCost_bayesGame_of_not _ (a := BayesianGame.play s (typeOf v₀ σ)) h)
  refine ⟨algOf v₀ s, ?_, ?_⟩
  · intro σ hq i v hv
    have e : typeOf v₀ σ i = (v, v₀) := by simp [typeOf, hv]
    have h1 := hconn σ hq i
    have h2 := subset_biUnion_algOf v₀ s σ i
    rw [e] at h1 h2
    exact h1.mono h2
  · rw [socialCost_eq, game, Network.bayesGame_prior, sum_map_mul]
    refine Finset.sum_le_sum fun σ _ => ?_
    by_cases hq : q σ = 0
    · simp [hq]
    gcongr
    rw [N.stateCost_bayesGame_of_forall _ (a := BayesianGame.play s (typeOf v₀ σ)) (hconn σ hq)]
    exact_mod_cast algOf_cost_le N v₀ s σ

/-- Lemma 3.5 of [Alon–Emek–Feldman–Tennenholtz 2010], the reduction: if every deterministic
online Steiner tree algorithm (valid on the support of `q`) pays in expectation at least `α` times
the expected optimum, then `opt^P(G^q) ≥ α · opt^C(G^q)`. With the distributional Imase–Waxman
lower bound `α = Ω(log n)` on the `n`-vertex diamond graph (not formalized here) this is
Lemma 3.5. -/
theorem lemma_3_5 (q : PMF (Req V n)) (α : ℝ≥0∞)
    (hLB : ∀ A : OnlineAlg V E n, (∀ σ, q σ ≠ 0 → A.Valid N v₀ σ) →
      α * ∑ σ, q σ * steinerOpt N v₀ σ ≤ ∑ σ, q σ * (A.cost N σ : ℝ≥0∞)) :
    α * (game N v₀ q).optC ≤ (game N v₀ q).optP := by
  refine le_iInf fun s => ?_
  by_cases hs : (game N v₀ q).socialCost s = ⊤
  · rw [hs]; exact le_top
  obtain ⟨A, hA, hcost⟩ := exists_onlineAlg N v₀ q s hs
  calc α * (game N v₀ q).optC ≤ α * ∑ σ, q σ * steinerOpt N v₀ σ := by
        gcongr; exact optC_le_expected_opt N v₀ q
    _ ≤ _ := hLB A hA
    _ ≤ _ := hcost

end Podc.BayesianIgnorance.Lemma35
