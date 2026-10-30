import Mathlib

/-!
# Basic definitions: the Caro–Wei and Turán bounds

Boppana, Halldórsson, Rawitz, *Simple and local independent set approximation*, PODC 2018 (BA);
arXiv 1803.00786.

* `caroWei G = ∑ᵥ 1/(d(v)+1)` (eq. (1)), `turan G = n²/(2|E|+n)` (`= n/(d̄+1)`),
  `avgDegree G = 2|E|/n`.
* `sum_degree_indep_eq`: for an independent set `I`, `∑_{v∈I} d(v) = ∑_{u∉I} |N(u) ∩ I|`
  (every edge at `I` has its other endpoint outside `I`); consequences `sum_degree_indep_le`
  (eq. (4): `∑_{v∈I} d(v) ≤ Δ |V∖I|`) and `card_edgeFinset_le_sum_compl`
  (`|E| ≤ ∑_{u∉I} d(u)`).
* `exists_indep_card_eq_indepNum`, `indepNum_le_card`: the API for `α(G)`.
-/

open Finset SimpleGraph

namespace Podc.LocalISApproximation

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The Caro–Wei bound `CaroWei(G) = ∑_{v ∈ V} 1/(d(v)+1)` (eq. (1) of the paper). -/
noncomputable def caroWei : ℝ := ∑ v, 1 / ((G.degree v : ℝ) + 1)

/-- The Turán bound `Turán(G) = n/(d̄+1) = n²/(2|E|+n)` (§2.3 of the paper). -/
noncomputable def turan : ℝ :=
  (Fintype.card V : ℝ) ^ 2 / (2 * (#G.edgeFinset : ℝ) + Fintype.card V)

/-- The average degree `d̄ = 2|E|/n`. -/
noncomputable def avgDegree : ℝ := 2 * (#G.edgeFinset : ℝ) / Fintype.card V

variable {G}

/-- Double counting the edges at an independent set `I`: `∑_{v∈I} d(v) = ∑_{u∉I} |N(u) ∩ I|`. -/
theorem sum_degree_indep_eq {I : Finset V} (hI : G.IsIndepSet (I : Set V)) :
    ∑ v ∈ I, G.degree v = ∑ u ∈ Iᶜ, #(G.neighborFinset u ∩ I) := by
  have h1 : ∀ v, G.degree v = ∑ u, if G.Adj v u then 1 else 0 := by
    intro v
    rw [← card_neighborFinset_eq_degree, Finset.sum_boole, Nat.cast_id]
    congr 1; ext u; simp
  have h2 : ∀ u, #(G.neighborFinset u ∩ I) = ∑ v ∈ I, if G.Adj v u then 1 else 0 := by
    intro u
    rw [Finset.sum_boole, Nat.cast_id]
    congr 1; ext v; simp [G.adj_comm, and_comm]
  calc ∑ v ∈ I, G.degree v = ∑ v ∈ I, ∑ u, (if G.Adj v u then 1 else 0) := by simp_rw [← h1]
    _ = ∑ u, ∑ v ∈ I, (if G.Adj v u then 1 else 0) := Finset.sum_comm
    _ = ∑ u ∈ Iᶜ, ∑ v ∈ I, (if G.Adj v u then 1 else 0) := by
      rw [← Finset.sum_add_sum_compl I, Finset.sum_eq_zero, zero_add]
      intro u hu
      refine Finset.sum_eq_zero fun v hv => ?_
      simp only [ite_eq_right_iff, one_ne_zero, imp_false]
      intro hadj
      exact hI (Finset.mem_coe.2 hv) (Finset.mem_coe.2 hu) hadj.ne hadj
    _ = _ := by simp_rw [h2]

/-- `∑_{v∈I} d(v) ≤ ∑_{u∉I} d(u)` for an independent set `I`. -/
theorem sum_degree_indep_le_compl {I : Finset V} (hI : G.IsIndepSet (I : Set V)) :
    ∑ v ∈ I, G.degree v ≤ ∑ u ∈ Iᶜ, G.degree u := by
  rw [sum_degree_indep_eq hI]
  refine Finset.sum_le_sum fun u _ => ?_
  rw [← card_neighborFinset_eq_degree]
  exact Finset.card_le_card Finset.inter_subset_left

/-- Eq. (4) of the paper: if `I` is independent and all degrees are `≤ Δ`, then
`∑_{v∈I} d(v) ≤ Δ · |V ∖ I|`. -/
theorem sum_degree_indep_le {I : Finset V} (hI : G.IsIndepSet (I : Set V)) {Δ : ℕ}
    (hΔ : ∀ v, G.degree v ≤ Δ) : ∑ v ∈ I, G.degree v ≤ Δ * #Iᶜ := by
  refine (sum_degree_indep_le_compl hI).trans ?_
  calc ∑ u ∈ Iᶜ, G.degree u ≤ ∑ _u ∈ Iᶜ, Δ := Finset.sum_le_sum fun u _ => hΔ u
    _ = Δ * #Iᶜ := by rw [Finset.sum_const, smul_eq_mul, mul_comm]

/-- Every edge has an endpoint outside an independent set: `|E| ≤ ∑_{u∉I} d(u)`. -/
theorem card_edgeFinset_le_sum_compl {I : Finset V} (hI : G.IsIndepSet (I : Set V)) :
    #G.edgeFinset ≤ ∑ u ∈ Iᶜ, G.degree u := by
  have h := G.sum_degrees_eq_twice_card_edges
  rw [← Finset.sum_add_sum_compl I] at h
  have := sum_degree_indep_le_compl hI
  omega

/-- `|E| ≤ Δ |V ∖ I|` for an independent set `I` when all degrees are `≤ Δ`. -/
theorem card_edgeFinset_le {I : Finset V} (hI : G.IsIndepSet (I : Set V)) {Δ : ℕ}
    (hΔ : ∀ v, G.degree v ≤ Δ) : #G.edgeFinset ≤ Δ * #Iᶜ := by
  refine (card_edgeFinset_le_sum_compl hI).trans ?_
  calc ∑ u ∈ Iᶜ, G.degree u ≤ ∑ _u ∈ Iᶜ, Δ := Finset.sum_le_sum fun u _ => hΔ u
    _ = Δ * #Iᶜ := by rw [Finset.sum_const, smul_eq_mul, mul_comm]

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- A maximum independent set: a finset `I` with `|I| = α(G)`. -/
theorem exists_indep_card_eq_indepNum :
    ∃ I : Finset V, G.IsIndepSet (I : Set V) ∧ #I = G.indepNum := by
  obtain ⟨s, hs⟩ := G.exists_isNIndepSet_indepNum
  exact ⟨s, hs.isIndepSet, hs.card_eq⟩

omit [DecidableEq V] [DecidableRel G.Adj] in
/-- The independence number is at most `n`. -/
theorem indepNum_le_card : G.indepNum ≤ Fintype.card V := by
  obtain ⟨I, -, hI⟩ := exists_indep_card_eq_indepNum (G := G)
  rw [← hI]; exact Finset.card_le_univ I

/-- A *bound* `B` on the independence number: a real number for every finite graph. -/
abbrev GraphBound := ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
  [DecidableRel G.Adj], ℝ

/-- The Caro–Wei bound as a `GraphBound`. -/
noncomputable def caroWeiBound : GraphBound := @fun _ _ _ G _ => caroWei G

/-- The Turán bound as a `GraphBound`. -/
noncomputable def turanBound : GraphBound := @fun _ _ _ G _ => turan G

/-- §2 of the paper: the bound `B` has performance ratio `ρ` on graphs of maximum degree `Δ` if
`α(G) ≥ B(G) ≥ α(G)/ρ` for all graphs `G` with `Δ(G) = Δ`. (Written `α ≤ ρ · B` to avoid
dividing by `ρ`.) -/
def HasPerformanceRatio (B : GraphBound) (Δ : ℕ) (ρ : ℝ) : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    G.maxDegree = Δ → B G ≤ G.indepNum ∧ (G.indepNum : ℝ) ≤ ρ * B G

/-- The performance ratio `ρ` of `B` on graphs of maximum degree `Δ` is *tight*: it holds, and no
smaller ratio holds. -/
def HasTightPerformanceRatio (B : GraphBound) (Δ : ℕ) (ρ : ℝ) : Prop :=
  HasPerformanceRatio B Δ ρ ∧ ∀ ρ' < ρ, ¬ HasPerformanceRatio B Δ ρ'

end Podc.LocalISApproximation
