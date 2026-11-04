/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Podc.Foundations.GameTheory.BayesianGame

-- CSLib candidate: Cslib/Foundations/GameTheory/NetworkCostSharing.lean

/-!
# Network cost sharing games (fair cost allocation)

A network cost sharing (NCS) game (Anshelevich, Dasgupta, Kleinberg, Tardos, Wexler,
Roughgarden): a (directed or undirected) graph with non-negative edge costs `c(e)`; every agent `i`
has a source `x_i` and a destination `y_i`, her action is a set `a_i ⊆ E` of edges she buys, the
cost of each edge is shared equally by the agents buying it, and the cost of agent `i` is her total
payment if `a_i` contains an `(x_i, y_i)`-path and `∞` otherwise.

The graph is given abstractly by a relation `step e u v` ("edge `e` can be traversed from `u` to
`v`"), which covers directed (`Network.directed`) and undirected (`Network.undirected`) graphs and
multigraphs. "`F` contains an `(x, y)`-path" is `Connects F x y`, the reflexive-transitive closure
of the steps along edges of `F` (so `F` always connects `x` to itself).

## Main definitions

* `Network V E`, `Network.Connects`, `Network.Reachable`.
* `load a e`: the number of agents buying `e`; `payment a i = ∑_{e ∈ a_i} c(e) / load a e`;
  `totalCost a`: the cost of all bought edges; `potential a = ∑_e c(e) H(load a e)` (Rosenthal).
* `agentCost t a i` (`ℝ≥0∞`-valued, `⊤` when `a_i` does not connect `t_i`), and `bayesGame p`: the
  Bayesian NCS game with type spaces `T_i = V × V` and common prior `p`.
* `hnum n = 1 + 1/2 + ⋯ + 1/n` (harmonic numbers in `ℝ≥0`).

## Main statements

* `sum_payment`: the payments add up to the total cost of the bought edges.
* `payment_add_potential_update`: Rosenthal's exact potential, in additive form.
* `totalCost_le_potential`, `potential_le_hnum_mul_totalCost`: `K ≤ Φ ≤ H(k) K`.
* `stateCost_bayesGame`: the social cost of an action profile is the total cost of the bought
  edges if every agent connects her terminals, and `⊤` otherwise.
-/

open Finset
open scoped ENNReal NNReal

namespace Cslib.GameTheory

/-! ### Harmonic numbers in `ℝ≥0` -/

/-- The harmonic number `H(n) = 1 + 1/2 + ⋯ + 1/n` in `ℝ≥0`. -/
noncomputable def hnum (n : ℕ) : ℝ≥0 := ∑ j ∈ range n, ((j : ℝ≥0) + 1)⁻¹

@[simp] lemma hnum_zero : hnum 0 = 0 := by simp [hnum]

lemma hnum_succ (n : ℕ) : hnum (n + 1) = hnum n + ((n : ℝ≥0) + 1)⁻¹ := by
  simp [hnum, sum_range_succ]

@[simp] lemma hnum_one : hnum 1 = 1 := by simp [hnum]

lemma hnum_mono : Monotone hnum := by
  intro m n h
  exact Finset.sum_le_sum_of_subset (Finset.range_mono h)

lemma one_le_hnum {n : ℕ} (hn : 1 ≤ n) : 1 ≤ hnum n := hnum_one ▸ hnum_mono hn

lemma coe_hnum (n : ℕ) : ((hnum n : ℝ≥0) : ℝ) = (harmonic n : ℝ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [hnum_succ, harmonic_succ]
    push_cast [ih]
    ring

/-! ### Networks -/

/-- A network: `step e u v` means that edge `e` can be traversed from `u` to `v`; `cost e ≥ 0`. -/
structure Network (V E : Type*) where
  /-- Edge `e` leads from `u` to `v`. -/
  step : E → V → V → Prop
  /-- The (non-negative) cost of an edge. -/
  cost : E → ℝ≥0

namespace Network

variable {V E ι : Type*}

/-- A directed network: edge `e` goes from `(ends e).1` to `(ends e).2`. -/
def directed (ends : E → V × V) (c : E → ℝ≥0) : Network V E :=
  ⟨fun e u v => ends e = (u, v), c⟩

/-- An undirected network: edge `e` joins the two vertices of `ends e`. -/
def undirected (ends : E → Sym2 V) (c : E → ℝ≥0) : Network V E :=
  ⟨fun e u v => ends e = s(u, v), c⟩

variable (N : Network V E)

/-- The edge set `F` contains an `(x, y)`-path. -/
def Connects (F : Finset E) (x y : V) : Prop :=
  Relation.ReflTransGen (fun u v => ∃ e ∈ F, N.step e u v) x y

lemma Connects.mono {N : Network V E} {F F' : Finset E} {x y : V} (h : F ⊆ F')
    (hc : N.Connects F x y) : N.Connects F' x y :=
  Relation.ReflTransGen.mono (fun _ _ ⟨e, he, hs⟩ => ⟨e, h he, hs⟩) _ _ hc

lemma connects_refl (F : Finset E) (x : V) : N.Connects F x x := Relation.ReflTransGen.refl

lemma connects_single {e : E} {u v : V} (h : N.step e u v) : N.Connects {e} u v :=
  Relation.ReflTransGen.single ⟨e, Finset.mem_singleton_self e, h⟩

/-- `y` is reachable from `x` in the network. -/
def Reachable [Fintype E] (x y : V) : Prop := N.Connects Finset.univ x y

lemma Connects.reachable [Fintype E] {N : Network V E} {F : Finset E} {x y : V}
    (h : N.Connects F x y) : N.Reachable x y := h.mono (Finset.subset_univ F)

/-- The distance from `x` to `y`: the least cost of an edge set containing an `(x, y)`-path
(`⊤` if `y` is not reachable from `x`). -/
noncomputable def dist [Fintype E] (x y : V) : ℝ≥0∞ :=
  ⨅ (F : Finset E) (_ : N.Connects F x y), ((∑ e ∈ F, N.cost e : ℝ≥0) : ℝ≥0∞)

lemma dist_le [Fintype E] {F : Finset E} {x y : V} (h : N.Connects F x y) :
    N.dist x y ≤ ((∑ e ∈ F, N.cost e : ℝ≥0) : ℝ≥0∞) :=
  iInf₂_le (f := fun F (_ : N.Connects F x y) => ((∑ e ∈ F, N.cost e : ℝ≥0) : ℝ≥0∞)) F h

lemma dist_eq_top [Fintype E] {x y : V} (h : ¬ N.Reachable x y) : N.dist x y = ⊤ :=
  iInf₂_eq_top.2 fun _ hF => absurd hF.reachable h

/-- A cheapest connecting edge set (a shortest path) exists for reachable pairs. -/
lemma exists_connects_eq_dist [Fintype E] {x y : V} (h : N.Reachable x y) :
    ∃ F, N.Connects F x y ∧ ((∑ e ∈ F, N.cost e : ℝ≥0) : ℝ≥0∞) = N.dist x y := by
  classical
  obtain ⟨F, hF, hmin⟩ := Finset.exists_min_image
    (Finset.univ.filter fun F : Finset E => N.Connects F x y)
    (fun F => ∑ e ∈ F, N.cost e) ⟨Finset.univ, Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩⟩
  refine ⟨F, (Finset.mem_filter.1 hF).2, le_antisymm ?_ (N.dist_le (Finset.mem_filter.1 hF).2)⟩
  refine le_iInf₂ fun F' hF' => ?_
  exact_mod_cast hmin F' (by simpa using hF')

variable [Fintype ι] [DecidableEq E]

/-- The number of agents buying edge `e` in the action profile `a`. -/
def load (a : ι → Finset E) (e : E) : ℕ := #{j | e ∈ a j}

/-- The payment of agent `i`: her equal shares of the edges she buys. -/
noncomputable def payment (a : ι → Finset E) (i : ι) : ℝ≥0 :=
  ∑ e ∈ a i, N.cost e / (load a e : ℝ≥0)

/-- The total cost of all edges bought by somebody. -/
noncomputable def totalCost (a : ι → Finset E) : ℝ≥0 :=
  ∑ e ∈ Finset.univ.biUnion a, N.cost e

/-- Rosenthal's potential `Φ(a) = ∑_e c(e) · H(load a e)`. -/
noncomputable def potential [Fintype E] (a : ι → Finset E) : ℝ≥0 :=
  ∑ e, N.cost e * hnum (load a e)

/-- The cost of agent `i`: her payment if her edges connect her terminals `t i`, and `⊤`
otherwise. -/
noncomputable def agentCost (t : ι → V × V) (a : ι → Finset E) (i : ι) : ℝ≥0∞ := by
  classical
  exact if N.Connects (a i) (t i).1 (t i).2 then (N.payment a i : ℝ≥0∞) else ⊤

lemma agentCost_of_connects {t : ι → V × V} {a : ι → Finset E} {i : ι}
    (h : N.Connects (a i) (t i).1 (t i).2) : N.agentCost t a i = N.payment a i := by
  simp [agentCost, h]

lemma agentCost_of_not_connects {t : ι → V × V} {a : ι → Finset E} {i : ι}
    (h : ¬ N.Connects (a i) (t i).1 (t i).2) : N.agentCost t a i = ⊤ := by
  simp [agentCost, h]

lemma load_pos {a : ι → Finset E} {e : E} {i : ι} (h : e ∈ a i) : 0 < load a e :=
  Finset.card_pos.2 ⟨i, by simp [h]⟩

lemma load_le_card (a : ι → Finset E) (e : E) : load a e ≤ Fintype.card ι :=
  Finset.card_filter_le _ _

lemma payment_le (a : ι → Finset E) (i : ι) : N.payment a i ≤ ∑ e ∈ a i, N.cost e := by
  refine Finset.sum_le_sum fun e he => ?_
  have : (1 : ℝ≥0) ≤ load a e := by exact_mod_cast load_pos he
  exact div_le_self (N.cost e).2 this

/-- The payments add up to the total cost of the bought edges. -/
theorem sum_payment (a : ι → Finset E) : ∑ i, N.payment a i = N.totalCost a := by
  classical
  have hsub : ∀ i, a i ⊆ Finset.univ.biUnion a := fun i => Finset.subset_biUnion_of_mem a
    (Finset.mem_univ i)
  calc ∑ i, N.payment a i
      = ∑ i, ∑ e ∈ Finset.univ.biUnion a, if e ∈ a i then N.cost e / (load a e : ℝ≥0) else 0 := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [payment, ← Finset.sum_filter]
        congr 1
        ext e; simpa using fun h => hsub i h
    _ = ∑ e ∈ Finset.univ.biUnion a, (load a e : ℝ≥0) * (N.cost e / (load a e : ℝ≥0)) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun e _ => ?_
        rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
        rfl
    _ = N.totalCost a := by
        refine Finset.sum_congr rfl fun e he => ?_
        obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.1 he
        have : (load a e : ℝ≥0) ≠ 0 := by exact_mod_cast (load_pos hi).ne'
        field_simp

/-- The number of agents other than `i` buying `e`. -/
def loadOthers [DecidableEq ι] (a : ι → Finset E) (i : ι) (e : E) : ℕ :=
  #{j | j ≠ i ∧ e ∈ a j}

lemma load_eq [DecidableEq ι] (a : ι → Finset E) (i : ι) (e : E) :
    load a e = loadOthers a i e + if e ∈ a i then 1 else 0 := by
  unfold load loadOthers
  rw [← Finset.card_filter_add_card_filter_not (fun j => j ≠ i), Finset.filter_filter]
  congr 1
  · congr 1; ext j; simp [and_comm]
  · split_ifs with h
    · rw [Finset.card_eq_one]; exact ⟨i, by ext j; constructor <;> intro hj <;> simp_all⟩
    · rw [Finset.card_eq_zero]; ext j; simp only [Finset.mem_filter]; constructor
      · rintro ⟨⟨-, hj⟩, hji⟩; simp at hji; subst hji; exact absurd hj h
      · simp

lemma loadOthers_update [DecidableEq ι] (a : ι → Finset E) (i : ι) (b : Finset E) (e : E) :
    loadOthers (Function.update a i b) i e = loadOthers a i e := by
  unfold loadOthers
  congr 1
  ext j
  by_cases h : j = i <;> simp [h]

lemma load_update [DecidableEq ι] (a : ι → Finset E) (i : ι) (b : Finset E) (e : E) :
    load (Function.update a i b) e = loadOthers a i e + if e ∈ b then 1 else 0 := by
  rw [load_eq _ i, loadOthers_update]; simp

lemma payment_eq [DecidableEq ι] (a : ι → Finset E) (i : ι) :
    N.payment a i = ∑ e ∈ a i, N.cost e / ((loadOthers a i e : ℝ≥0) + 1) := by
  refine Finset.sum_congr rfl fun e he => ?_
  simp only [load_eq a i e, he, ite_true]; push_cast; rfl

/-- The payment of agent `i` after a unilateral deviation to `b`: every edge of `b` is shared
with the other agents buying it. -/
lemma payment_update [DecidableEq ι] (a : ι → Finset E) (i : ι) (b : Finset E) :
    N.payment (Function.update a i b) i =
      ∑ e ∈ b, N.cost e / ((loadOthers a i e : ℝ≥0) + 1) := by
  rw [payment_eq]
  simp only [Function.update_self, loadOthers_update]

/-- Dropping an edge `e` from agent `i`'s action saves her exactly her share of `e`. -/
lemma payment_erase_add [DecidableEq ι] (a : ι → Finset E) (i : ι) {e : E} (he : e ∈ a i) :
    N.payment (Function.update a i ((a i).erase e)) i +
      N.cost e / ((loadOthers a i e : ℝ≥0) + 1) = N.payment a i := by
  rw [payment_update, payment_eq, Finset.sum_erase_add _ _ he]

/-- Rosenthal's potential is an exact potential (additive form): for a unilateral deviation of
agent `i` from `a_i` to `b`, `pay_i(a) + Φ(a') = pay_i(a') + Φ(a)` where `a' = (a_{-i}, b)`. -/
theorem payment_add_potential_update [Fintype E] [DecidableEq ι] (a : ι → Finset E) (i : ι)
    (b : Finset E) :
    N.payment a i + N.potential (Function.update a i b) =
      N.payment (Function.update a i b) i + N.potential a := by
  rw [payment_eq, payment_eq, Function.update_self, potential, potential]
  simp only [loadOthers_update]
  have hmem : ∀ (F : Finset E) (f : E → ℝ≥0), ∑ e ∈ F, f e = ∑ e, if e ∈ F then f e else 0 :=
    fun F f => by rw [Finset.sum_ite_mem, Finset.univ_inter]
  rw [hmem (a i), hmem b, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [load_update, load_eq a i e]
  set m := loadOthers a i e
  by_cases ha : e ∈ a i <;> by_cases hb : e ∈ b <;> simp [ha, hb, hnum_succ] <;> ring

lemma load_eq_zero_iff {a : ι → Finset E} {e : E} :
    load a e = 0 ↔ e ∉ Finset.univ.biUnion a := by
  simp [load, Finset.card_eq_zero, Finset.filter_eq_empty_iff]

lemma potential_eq_sum_biUnion [Fintype E] (a : ι → Finset E) :
    N.potential a = ∑ e ∈ Finset.univ.biUnion a, N.cost e * hnum (load a e) := by
  rw [potential, ← Finset.sum_subset (Finset.subset_univ _)]
  intro e _ he
  rw [load_eq_zero_iff.2 he, hnum_zero, mul_zero]

/-- The social cost is at most Rosenthal's potential: `K(a) ≤ Φ(a)`. -/
theorem totalCost_le_potential [Fintype E] (a : ι → Finset E) :
    N.totalCost a ≤ N.potential a := by
  rw [potential_eq_sum_biUnion, totalCost]
  refine Finset.sum_le_sum fun e he => ?_
  obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.1 he
  exact le_mul_of_one_le_right zero_le (one_le_hnum (load_pos hi))

/-- Rosenthal's potential is at most `H(k)` times the social cost, `k` the number of agents. -/
theorem potential_le_hnum_mul_totalCost [Fintype E] (a : ι → Finset E) :
    N.potential a ≤ hnum (Fintype.card ι) * N.totalCost a := by
  rw [potential_eq_sum_biUnion, totalCost, Finset.mul_sum]
  refine Finset.sum_le_sum fun e _ => ?_
  rw [mul_comm]
  exact mul_le_mul_of_nonneg_right (hnum_mono (load_le_card a e)) zero_le

/-- The Bayesian NCS game on the network `N` with common prior `p`: type spaces `T_i = V × V`
(source, destination), action spaces `A_i = 2^E`. -/
noncomputable def bayesGame (p : PMF (ι → V × V)) :
    BayesianGame ι (fun _ => Finset E) (fun _ => V × V) where
  cost i t a := N.agentCost t a i
  prior := p

@[simp] lemma bayesGame_cost (p : PMF (ι → V × V)) (i : ι) (t : ι → V × V) (a : ι → Finset E) :
    (N.bayesGame p).cost i t a = N.agentCost t a i := rfl

@[simp] lemma bayesGame_prior (p : PMF (ι → V × V)) : (N.bayesGame p).prior = p := rfl

/-- The social cost `K_t(a)` of an NCS game: the total cost of the bought edges if every agent
connects her terminals, and `⊤` otherwise. -/
theorem stateCost_bayesGame [DecidableEq ι] (p : PMF (ι → V × V)) (t : ι → V × V)
    (a : ι → Finset E) [Decidable (∀ i, N.Connects (a i) (t i).1 (t i).2)] :
    (N.bayesGame p).stateCost t a =
      if ∀ i, N.Connects (a i) (t i).1 (t i).2 then (N.totalCost a : ℝ≥0∞) else ⊤ := by
  unfold BayesianGame.stateCost
  split_ifs with h
  · simp only [bayesGame_cost, N.agentCost_of_connects (h _)]
    rw [← ENNReal.ofNNReal_finsetSum, sum_payment]
  · push Not at h
    obtain ⟨i, hi⟩ := h
    exact ENNReal.sum_eq_top.2 ⟨i, Finset.mem_univ _, N.agentCost_of_not_connects hi⟩

lemma stateCost_bayesGame_of_forall [DecidableEq ι] (p : PMF (ι → V × V)) {t : ι → V × V}
    {a : ι → Finset E} (h : ∀ i, N.Connects (a i) (t i).1 (t i).2) :
    (N.bayesGame p).stateCost t a = N.totalCost a := by
  classical
  simp [stateCost_bayesGame, h]

lemma stateCost_bayesGame_of_not [DecidableEq ι] (p : PMF (ι → V × V)) {t : ι → V × V}
    {a : ι → Finset E} {i : ι} (h : ¬ N.Connects (a i) (t i).1 (t i).2) :
    (N.bayesGame p).stateCost t a = ⊤ := by
  classical
  simp only [stateCost_bayesGame]
  exact ite_eq_right_iff.2 fun h' => absurd (h' i) h

/-- An agent whose destinations (of positive prior probability) are reachable has a finite
ex-ante cost in every Bayesian equilibrium. -/
lemma exCost_ne_top_of_isBayesEq [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq ι]
    (p : PMF (ι → V × V)) {s : ι → V × V → Finset E} (hs : (N.bayesGame p).IsBayesEq s) (i : ι)
    (hr : ∀ t, p t ≠ 0 → N.Reachable (t i).1 (t i).2) : (N.bayesGame p).exCost s i ≠ ⊤ := by
  refine ne_top_of_le_ne_top ?_ (hs i fun _ => Finset.univ)
  refine ENNReal.sum_ne_top.2 fun t _ => ?_
  by_cases hp : p t = 0
  · simp [hp]
  rw [bayesGame_cost, BayesianGame.play_update, N.agentCost_of_connects (by rw [Function.update_self]; exact hr t hp)]
  exact ENNReal.mul_ne_top (PMF.apply_ne_top p t) ENNReal.coe_ne_top

/-- Dropping a positive-cost edge `e` that agent `i` does not need strictly lowers her payment. -/
lemma payment_erase_lt [DecidableEq ι] {a : ι → Finset E} {i : ι} {e : E} (he : e ∈ a i)
    (hc : 0 < N.cost e) : N.payment (Function.update a i ((a i).erase e)) i < N.payment a i := by
  rw [← N.payment_erase_add a i he]
  exact lt_add_of_pos_right _ (div_pos hc (by positivity))

/-- In a Nash equilibrium of an underlying NCS game no agent buys a positive-cost edge she does not
need. -/
theorem not_isNashEq_of_removable [DecidableEq ι] {p : PMF (ι → V × V)} {t : ι → V × V}
    {a : ι → Finset E} (h : (N.bayesGame p).IsNashEq t a) {i : ι} {e : E} (he : e ∈ a i)
    (hc : 0 < N.cost e) (hconn : N.Connects ((a i).erase e) (t i).1 (t i).2) : False := by
  have h1 := h i ((a i).erase e)
  simp only [bayesGame_cost] at h1
  rw [N.agentCost_of_connects (hconn.mono (Finset.erase_subset e _)),
    N.agentCost_of_connects (by simpa using hconn)] at h1
  exact absurd (ENNReal.coe_le_coe.1 h1) (not_le.2 (N.payment_erase_lt he hc))

/-- In a Bayesian equilibrium no agent (with finite ex-ante cost) buys, at a type of positive
probability, a positive-cost edge she does not need. -/
theorem not_isBayesEq_of_removable [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq ι]
    {p : PMF (ι → V × V)} {s : ι → V × V → Finset E} (hs : (N.bayesGame p).IsBayesEq s) {i : ι}
    (hfin : (N.bayesGame p).exCost s i ≠ ⊤) {τ : V × V} {e : E} (he : e ∈ s i τ)
    (hc : 0 < N.cost e) (hconn : N.Connects ((s i τ).erase e) τ.1 τ.2) {t₀ : ι → V × V}
    (ht₀ : t₀ i = τ) (hp : p t₀ ≠ 0) : False := by
  classical
  set σ := Function.update (s i) τ ((s i τ).erase e)
  have hdev : ∀ t, t i = τ → BayesianGame.play (Function.update s i σ) t =
      Function.update (BayesianGame.play s t) i ((BayesianGame.play s t i).erase e) := by
    intro t ht
    rw [BayesianGame.play_update]
    simp [σ, ht]
  have hle : ∀ t, p t * N.agentCost t (BayesianGame.play (Function.update s i σ) t) i ≤
      p t * N.agentCost t (BayesianGame.play s t) i := by
    intro t
    by_cases ht : t i = τ
    · rw [hdev t ht]
      have hc' : N.Connects ((BayesianGame.play s t i).erase e) (t i).1 (t i).2 := by
        simpa [ht] using hconn
      rw [N.agentCost_of_connects (hc'.mono (Finset.erase_subset e _)),
        N.agentCost_of_connects (by simpa using hc')]
      gcongr
      exact (N.payment_erase_lt (by simpa [ht] using he) hc).le
    · rw [BayesianGame.play_update]
      simp only [σ, Function.update_of_ne ht]
      rw [show s i (t i) = BayesianGame.play s t i from rfl, Function.update_eq_self]
  have hlt : p t₀ * N.agentCost t₀ (BayesianGame.play (Function.update s i σ) t₀) i <
      p t₀ * N.agentCost t₀ (BayesianGame.play s t₀) i := by
    rw [hdev t₀ ht₀]
    have hc' : N.Connects ((BayesianGame.play s t₀ i).erase e) (t₀ i).1 (t₀ i).2 := by
      simpa [ht₀] using hconn
    rw [N.agentCost_of_connects (hc'.mono (Finset.erase_subset e _)),
      N.agentCost_of_connects (by simpa using hc'), mul_comm, mul_comm (p t₀)]
    exact ENNReal.mul_lt_mul_left hp (PMF.apply_ne_top p t₀)
      (ENNReal.coe_lt_coe.2 (N.payment_erase_lt (by simpa [ht₀] using he) hc))
  have key : (N.bayesGame p).exCost (Function.update s i σ) i < (N.bayesGame p).exCost s i := by
    unfold BayesianGame.exCost
    simp only [bayesGame_cost, bayesGame_prior]
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ t₀),
      ← Finset.add_sum_erase _ _ (Finset.mem_univ t₀)]
    refine ENNReal.add_lt_add_of_lt_of_le ?_ hlt (Finset.sum_le_sum fun t _ => hle t)
    refine ne_top_of_le_ne_top hfin ?_
    refine (Finset.sum_le_sum fun t _ => hle t).trans ?_
    unfold BayesianGame.exCost
    exact Finset.sum_le_sum_of_subset (Finset.erase_subset _ _)
  exact absurd (hs i σ) (not_le.2 key)

end Network

end Cslib.GameTheory
