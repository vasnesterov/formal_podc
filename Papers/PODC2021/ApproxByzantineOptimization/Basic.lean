/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# Approximate Byzantine fault-tolerance in distributed optimization: the one-shot model

Formalization of the model of Section 3 of

* S. Liu, N. Gupta, N. H. Vaidya, *Approximate Byzantine Fault-Tolerance in Distributed
  Optimization*, PODC 2021, DOI 10.1145/3465084.3467902 (full version arXiv:2101.09337v5).

There are `n` agents `Fin n`; agent `i` has a cost function `Q i : E → ℝ` (in the paper
`E = ℝ^d`). A *profile* is the vector of the agents' true cost functions. In an execution a set
`B` of at most `f` agents is Byzantine; the server receives a vector `R` of cost functions with
`R i = Q i` for `i ∉ B` and arbitrary `R j` for `j ∈ B`. A deterministic algorithm is a map from
received vectors to points of `E` (the paper's "server has full knowledge of all the agents' cost
functions", the best case for the server; Theorem 2's algorithm works in this model).

* `argminSet Q T` — `arg min_x ∑_{i ∈ T} Q i x` (`argminSet Q ∅ = univ`);
* `IsResilient f ε alg Q` — Definition 2, `(f, ε)`-resilience of `alg` when the true costs are `Q`
  (for every faulty set `|B| ≤ f`, every behaviour of `B`, every `S` of `n - f` non-faulty agents);
* `IsRedundant f ε Q` — Definition 3, `(2f, ε)`-redundancy;
* `Assumption1 Q` — Assumption 1 (all non-empty aggregates have a non-empty closed `arg min`).

Distances are extended (`Metric.infEDist`, `Metric.hausdorffEDist`, values in `ℝ≥0∞`); on
non-empty sets they are the paper's `dist (x, X)` and Hausdorff distance (4); the distance to the
empty set is `⊤`.

The main fact of this file is the *per-profile characterization* `exists_isResilient_iff`: for a
fixed profile, an `(f, ε)`-resilient algorithm exists iff some point is within `ε` of every
`arg min` of `n - f` agents.
-/

open Finset Metric
open scoped ENNReal NNReal

namespace Podc.ApproxByzantineOptimization

variable {E : Type*} {n : ℕ}

/-- A cost-function profile: the cost function of each of the `n` agents. -/
abbrev Profile (n : ℕ) (E : Type*) := Fin n → E → ℝ

/-- A deterministic server algorithm: it maps the `n` received cost functions to an output point. -/
abbrev Algorithm (n : ℕ) (E : Type*) := Profile n E → E

/-- `arg min_{x} ∑_{i ∈ T} Q i x`, the set of minimum points of the aggregate cost of `T`. -/
def argminSet (Q : Profile n E) (T : Finset (Fin n)) : Set E :=
  {x | ∀ y, ∑ i ∈ T, Q i x ≤ ∑ i ∈ T, Q i y}

lemma mem_argminSet {Q : Profile n E} {T : Finset (Fin n)} {x : E} :
    x ∈ argminSet Q T ↔ ∀ y, ∑ i ∈ T, Q i x ≤ ∑ i ∈ T, Q i y := Iff.rfl

@[simp] lemma argminSet_empty (Q : Profile n E) : argminSet Q ∅ = Set.univ := by
  ext x; simp [argminSet]

/-- The `arg min` of `T` only depends on the cost functions of the agents in `T`. -/
lemma argminSet_congr {Q Q' : Profile n E} {T : Finset (Fin n)} (h : ∀ i ∈ T, Q i = Q' i) :
    argminSet Q T = argminSet Q' T := by
  ext x
  simp only [argminSet, Set.mem_ofPred_eq]
  have : ∀ z, ∑ i ∈ T, Q i z = ∑ i ∈ T, Q' i z := fun z =>
    Finset.sum_congr rfl fun i hi => by rw [h i hi]
  simp only [this]

/-- `x` is the unique minimum point of the aggregate cost of `T`. -/
lemma argminSet_eq_singleton {Q : Profile n E} {T : Finset (Fin n)} {x : E}
    (h : ∀ y, y ≠ x → ∑ i ∈ T, Q i x < ∑ i ∈ T, Q i y) : argminSet Q T = {x} := by
  ext y
  simp only [argminSet, Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · intro hy
    by_contra hne
    exact absurd (hy x) (not_le.2 (h y hne))
  · rintro rfl z
    rcases eq_or_ne z y with rfl | hz
    · exact le_rfl
    · exact (h z hz).le

section EMetric

variable [PseudoEMetricSpace E]

/-- **Definition 2** (`(f, ε)`-resilience) of the paper, for the profile `Q` of true costs:
for every set `B` of at most `f` Byzantine agents, every vector `R` of received functions in which
the non-faulty agents report their true cost (`R i = Q i` for `i ∉ B`), and every set `S` of
`n - f` non-faulty agents, the output is within `ε` of `arg min ∑_{i ∈ S} Q i`. -/
def IsResilient (f : ℕ) (ε : ℝ≥0) (alg : Algorithm n E) (Q : Profile n E) : Prop :=
  ∀ B : Finset (Fin n), B.card ≤ f → ∀ R : Profile n E, (∀ i, i ∉ B → R i = Q i) →
    ∀ S : Finset (Fin n), Disjoint S B → S.card + f = n →
      infEDist (alg R) (argminSet Q S) ≤ ε

/-- **Definition 3** (`(2f, ε)`-redundancy) of the paper: for all `Ŝ ⊆ S` with `|S| = n - f` and
`|Ŝ| = n - 2f` the Hausdorff distance between the two `arg min` sets is at most `ε`.
(Cardinalities are stated additively, so for `2f > n` there is no such `Ŝ`, as in the paper.) -/
def IsRedundant (f : ℕ) (ε : ℝ≥0) (Q : Profile n E) : Prop :=
  ∀ S Ŝ : Finset (Fin n), Ŝ ⊆ S → S.card + f = n → Ŝ.card + 2 * f = n →
    hausdorffEDist (argminSet Q S) (argminSet Q Ŝ) ≤ ε

/-- **Assumption 1** of the paper, for all agents: every non-empty set of agents has a non-empty
closed set of aggregate minimum points. -/
def Assumption1 (Q : Profile n E) : Prop :=
  ∀ T : Finset (Fin n), T.Nonempty → (argminSet Q T).Nonempty ∧ IsClosed (argminSet Q T)

/-- **Per-profile characterization.** For a fixed profile `Q`, a deterministic `(f, ε)`-resilient
algorithm exists iff some point is within `ε` of the `arg min` of every set of `n - f` agents
(the constant algorithm then works). In particular `(2f, ε)`-redundancy plays no role for a fixed
profile; see `theorem_1_false_per_profile`. -/
theorem exists_isResilient_iff (f : ℕ) (ε : ℝ≥0) (Q : Profile n E) :
    (∃ alg : Algorithm n E, IsResilient f ε alg Q) ↔
      ∃ x : E, ∀ S : Finset (Fin n), S.card + f = n → infEDist x (argminSet Q S) ≤ ε := by
  constructor
  · rintro ⟨alg, h⟩
    exact ⟨alg Q, fun S hS => h ∅ (by simp) Q (fun _ _ => rfl) S (disjoint_empty_right S) hS⟩
  · rintro ⟨x, hx⟩
    exact ⟨fun _ => x, fun B _ R _ S _ hS => hx S hS⟩

/-- If two sets of `n - f` agents have singleton `arg min`s more than `2ε` apart, no deterministic
algorithm is `(f, ε)`-resilient for `Q`: when the faulty agents behave honestly, the server cannot
tell which of the two sets is non-faulty (the indistinguishability argument of Lemma 1 and
Theorem 1). -/
theorem not_isResilient_of_far {f : ℕ} {ε : ℝ≥0} {Q : Profile n E} {S T : Finset (Fin n)}
    (hS : S.card + f = n) (hT : T.card + f = n) {a b : E} (ha : argminSet Q S = {a})
    (hb : argminSet Q T = {b}) (hab : 2 * (ε : ℝ≥0∞) < edist a b) (alg : Algorithm n E) :
    ¬ IsResilient f ε alg Q := by
  intro h
  obtain ⟨x, hx⟩ := (exists_isResilient_iff f ε Q).1 ⟨alg, h⟩
  have h1 := hx S hS
  have h2 := hx T hT
  rw [ha, infEDist_singleton] at h1
  rw [hb, infEDist_singleton] at h2
  have : edist a b ≤ 2 * (ε : ℝ≥0∞) := by
    calc edist a b ≤ edist x a + edist x b := edist_triangle_left a b x
      _ ≤ ε + ε := add_le_add h1 h2
      _ = 2 * (ε : ℝ≥0∞) := (two_mul _).symm
  exact absurd hab (not_lt.2 this)

/-- Degenerate case `f ≥ n`: then the only "set of `n - f` agents" is `∅` (for `f = n`) or there is
none (`f > n`), and every algorithm is `(f, 0)`-resilient. -/
theorem isResilient_of_le {f : ℕ} (hf : n ≤ f) (ε : ℝ≥0) (alg : Algorithm n E) (Q : Profile n E) :
    IsResilient f ε alg Q := by
  intro B _ R _ S _ hS
  have : S = ∅ := Finset.card_eq_zero.1 (by omega)
  subst this
  rw [argminSet_empty, infEDist_zero_of_mem (Set.mem_univ _)]
  exact zero_le

end EMetric

end Podc.ApproxByzantineOptimization
