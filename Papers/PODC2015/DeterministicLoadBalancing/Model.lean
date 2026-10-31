import Mathlib

/-!
# Discrete diffusive load balancing on graphs: the model

Berenbrink, Klasing, Kosowski, Mallmann-Trenn, Uznański, *Improved Analysis of Deterministic
Load-Balancing Schemes*, PODC 2015 (arXiv:1404.4344v4), Section 1.3.

* The network is a finite simple graph `G` (the paper's "original graph"); every node additionally
  has `dl` self-loops (the paper's `d◦`). A node `v` has `D v = deg v + dl` edges in the balancing
  graph `G⁺` (the paper's `d⁺`).
* Time is synchronous. In every step every node `v` with load `x` (number of indivisible tokens)
  sends `out v s x w` tokens to each neighbour `w` and keeps `keep v s x` tokens (the tokens sent over
  its self-loops; the self-loops of a node only matter through their total, the distribution over
  individual self-loops is expressed by an explicit split `g : Fin dl → ℕ` in the fairness
  predicates below). `s` is the node's local state (e.g. a rotor), updated by `next`.
* A `Balancer` is deterministic and local: node `v` decides from its own identity, state and load
  only. Stateless algorithms are those with `σ = Unit`.

The discrepancy of a load vector is `max − min` (`disc`).
-/

open Finset

namespace Podc.DeterministicLoadBalancing

variable {V : Type*} [Fintype V] [DecidableEq V]

set_option linter.unusedSectionVars false

section General

variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- A deterministic, local, synchronous discrete load-balancing algorithm on `G`
(paper, Section 1.3). Node `v` in local state `s` holding `x` tokens sends `out v s x w` tokens
to its neighbour `w`, keeps `keep v s x` tokens (on its self-loops / in its remainder) and moves to
state `next v s x`. No tokens are created or destroyed. -/
structure Balancer where
  /-- Local state of a node. -/
  σ : Type
  /-- Initial local states (e.g. initial rotor positions). -/
  init : V → σ
  /-- Tokens sent from `v` to its neighbour `w`. -/
  out : V → σ → ℕ → V → ℕ
  /-- Tokens kept by `v` (sent over its self-loops). -/
  keep : V → σ → ℕ → ℕ
  /-- Next local state. -/
  next : V → σ → ℕ → σ
  /-- Conservation: a node distributes exactly its load. -/
  conserve : ∀ v s x, keep v s x + ∑ w ∈ G.neighborFinset v, out v s x w = x

/-- `∑_v ∑_{w ∼ v} f w v = ∑_w ∑_{v ∼ w} f w v` (double counting of darts). -/
lemma sum_sum_neighbor_swap {M : Type*} [AddCommMonoid M] (f : V → V → M) :
    ∑ v, ∑ w ∈ G.neighborFinset v, f w v = ∑ w, ∑ v ∈ G.neighborFinset w, f w v := by
  simp_rw [G.neighborFinset_eq_filter, Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun v _ => ?_
  simp [G.adj_comm]

namespace Balancer

variable {G} (A : Balancer G)

/-- One synchronous step: every node distributes its load; node `v` receives what it keeps plus
what its neighbours send to it. -/
def step (c : (V → ℕ) × (V → A.σ)) : (V → ℕ) × (V → A.σ) :=
  (fun v => A.keep v (c.2 v) (c.1 v) + ∑ w ∈ G.neighborFinset v, A.out w (c.2 w) (c.1 w) v,
   fun v => A.next v (c.2 v) (c.1 v))

/-- The configuration (loads, states) at time `t`, from initial loads `x₀`
(the paper's `x₁` is our time `0`). -/
def config (x₀ : V → ℕ) : ℕ → (V → ℕ) × (V → A.σ)
  | 0 => (x₀, A.init)
  | t + 1 => A.step (config x₀ t)

/-- Load vector at time `t`. -/
def load (x₀ : V → ℕ) (t : ℕ) : V → ℕ := (A.config x₀ t).1

/-- Local states at time `t`. -/
def state (x₀ : V → ℕ) (t : ℕ) : V → A.σ := (A.config x₀ t).2

/-- `f_t(v, w)`: tokens sent from `v` to its neighbour `w` in step `t`. -/
def flow (x₀ : V → ℕ) (t : ℕ) (v w : V) : ℕ := A.out v (A.state x₀ t v) (A.load x₀ t v) w

/-- Tokens kept by `v` (sent over its self-loops) in step `t`. -/
def kept (x₀ : V → ℕ) (t : ℕ) (v : V) : ℕ := A.keep v (A.state x₀ t v) (A.load x₀ t v)

/-- `F_t(v, w)`: cumulative number of tokens sent from `v` to `w` in steps `0, …, t`. -/
def cumFlow (x₀ : V → ℕ) (t : ℕ) (v w : V) : ℕ := ∑ τ ∈ range (t + 1), A.flow x₀ τ v w

@[simp] lemma load_zero (x₀ : V → ℕ) : A.load x₀ 0 = x₀ := rfl

lemma load_succ (x₀ : V → ℕ) (t : ℕ) (v : V) :
    A.load x₀ (t + 1) v = A.kept x₀ t v + ∑ w ∈ G.neighborFinset v, A.flow x₀ t w v := by
  simp only [load, kept, flow, state, config, step]

lemma state_succ (x₀ : V → ℕ) (t : ℕ) (v : V) :
    A.state x₀ (t + 1) v = A.next v (A.state x₀ t v) (A.load x₀ t v) := by
  simp only [load, state, config, step]

lemma kept_add_sum_flow (x₀ : V → ℕ) (t : ℕ) (v : V) :
    A.kept x₀ t v + ∑ w ∈ G.neighborFinset v, A.flow x₀ t v w = A.load x₀ t v :=
  A.conserve _ _ _

/-- The total load is invariant. -/
lemma sum_load_succ (x₀ : V → ℕ) (t : ℕ) : ∑ v, A.load x₀ (t + 1) v = ∑ v, A.load x₀ t v := by
  simp_rw [load_succ, Finset.sum_add_distrib]
  rw [sum_sum_neighbor_swap G (fun w v => A.flow x₀ t w v), ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun v _ => A.kept_add_sum_flow x₀ t v

lemma sum_load (x₀ : V → ℕ) (t : ℕ) : ∑ v, A.load x₀ t v = ∑ v, x₀ v := by
  induction t with
  | zero => rfl
  | succ t ih => rw [sum_load_succ, ih]

end Balancer

/-- A stateless balancer: node `v` with load `x` sends `out v x w` to `w` and keeps `keep v x`. -/
def Balancer.stateless (out : V → ℕ → V → ℕ) (keep : V → ℕ → ℕ)
    (h : ∀ v x, keep v x + ∑ w ∈ G.neighborFinset v, out v x w = x) : Balancer G where
  σ := Unit
  init _ := ()
  out v _ x := out v x
  keep v _ x := keep v x
  next _ _ _ := ()
  conserve v _ x := h v x

end General

/-! ### Discrepancy -/

/-- Discrepancy of a load vector: `max_v x v − min_v x v`. -/
def disc (x : V → ℕ) : ℕ := univ.sup fun p : V × V => x p.1 - x p.2

lemma sub_le_disc (x : V → ℕ) (u w : V) : x u - x w ≤ disc x :=
  Finset.le_sup (f := fun p : V × V => x p.1 - x p.2) (mem_univ (u, w))

lemma disc_eq_zero_iff (x : V → ℕ) : disc x = 0 ↔ ∀ u w, x u = x w := by
  constructor
  · intro h u w
    have h1 := sub_le_disc x u w
    have h2 := sub_le_disc x w u
    omega
  · intro h
    refine Nat.eq_zero_of_le_zero (Finset.sup_le fun p _ => ?_)
    simp [h p.1 p.2]

/-- If the total load is not divisible by the number of nodes, the discrepancy is at least `1`. -/
lemma one_le_disc_of_not_dvd (x : V → ℕ) (h : ¬ Fintype.card V ∣ ∑ v, x v) : 1 ≤ disc x := by
  by_contra h0
  have hc := (disc_eq_zero_iff x).1 (by omega)
  apply h
  rcases isEmpty_or_nonempty V with hV | ⟨⟨v₀⟩⟩
  · simp
  · refine ⟨x v₀, ?_⟩
    rw [Finset.sum_congr rfl fun v _ => hc v v₀]
    simp [mul_comm]

/-! ### Fairness notions -/

/-- `y` is a fair share of `x` tokens over `k` edges: `y = ⌊x/k⌋`, or `y = ⌊x/k⌋ + 1` when `k ∤ x`;
equivalently `⌊x/k⌋ ≤ y ≤ ⌈x/k⌉` (`fairShare_iff`). -/
def FairShare (k x y : ℕ) : Prop := y = x / k ∨ (x % k ≠ 0 ∧ y = x / k + 1)

lemma fairShare_iff {k x y : ℕ} (hk : 0 < k) : FairShare k x y ↔ x / k ≤ y ∧ y ≤ x ⌈/⌉ k := by
  rw [Nat.ceilDiv_eq_add_pred_div]
  have h1 := Nat.div_add_mod x k
  have h2 := Nat.mod_lt x hk
  have h3 : (x + k - 1) / k = x / k + if x % k = 0 then 0 else 1 := by
    have he : x + k - 1 = (x % k + k - 1) + k * (x / k) := by omega
    rw [he, Nat.add_mul_div_left _ _ hk]
    split_ifs with h
    · rw [h, Nat.div_eq_of_lt (by omega)]; simp
    · have : (x % k + k - 1) / k = 1 := Nat.div_eq_of_lt_le (by omega) (by omega)
      rw [this]; omega
  rw [h3]
  unfold FairShare
  split_ifs with h <;> omega

section Fairness

variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Round fairness with `dl` self-loops per node (the class of Rabani–Sinclair–Wanka [17]): a node
with load `x` sends a fair share `⌊x/d⁺⌋` or `⌈x/d⁺⌉` over each of its `d⁺ = deg + dl` edges,
including each self-loop (`g` is the split of the kept tokens over the self-loops). -/
def Balancer.RoundFair (dl : ℕ) (A : Balancer G) : Prop :=
  ∀ v s x, (∀ w ∈ G.neighborFinset v, FairShare (G.degree v + dl) x (A.out v s x w)) ∧
    ∃ g : Fin dl → ℕ, ∑ i, g i = A.keep v s x ∧ ∀ i, FairShare (G.degree v + dl) x (g i)

/-- Definition 2.1: cumulative `δ`-fairness. In every execution and every step, every edge of `v`
(including self-loops) receives at least `⌊x/d⁺⌋` tokens, and the cumulative flows `F_t` over any
two original edges of a node differ by at most `δ`. -/
def Balancer.CumulativelyFair (dl δ : ℕ) (A : Balancer G) : Prop :=
  ∀ x₀ t v,
    (∀ w ∈ G.neighborFinset v, A.load x₀ t v / (G.degree v + dl) ≤ A.flow x₀ t v w) ∧
    (∃ g : Fin dl → ℕ, ∑ i, g i = A.kept x₀ t v ∧
      ∀ i, A.load x₀ t v / (G.degree v + dl) ≤ g i) ∧
    ∀ w₁ ∈ G.neighborFinset v, ∀ w₂ ∈ G.neighborFinset v,
      A.cumFlow x₀ t v w₁ ≤ A.cumFlow x₀ t v w₂ + δ

/-- The one-step part of Definition 3.1: node `v` with load `x` sends a fair share over every edge
(round fairness, conditions "receive `⌊x/d⁺⌋`" and 3.) and at least `min{s, e}` self-loops receive
`⌈x/d⁺⌉ = ⌊x/d⁺⌋ + 1` tokens, where `e = x mod d⁺` (condition 2., `s`-self-preference). -/
def GoodStep (dl s : ℕ) (k : ℕ) (x : ℕ) (out : V → ℕ) (nbrs : Finset V) (keep : ℕ) : Prop :=
  (∀ w ∈ nbrs, FairShare k x (out w)) ∧
    ∃ g : Fin dl → ℕ, ∑ i, g i = keep ∧ (∀ i, FairShare k x (g i)) ∧
      min s (x % k) ≤ #{i | g i = x / k + 1}

/-- Definition 3.1: a good `s`-balancer (`1 ≤ s ≤ d◦`): cumulatively `1`-fair, round-fair and
`s`-self-preferring. -/
def Balancer.IsGood (dl s : ℕ) (A : Balancer G) : Prop :=
  1 ≤ s ∧ s ≤ dl ∧ A.CumulativelyFair dl 1 ∧
    ∀ v σ x, GoodStep dl s (G.degree v + dl) x (A.out v σ x) (G.neighborFinset v) (A.keep v σ x)

end Fairness

end Podc.DeterministicLoadBalancing
