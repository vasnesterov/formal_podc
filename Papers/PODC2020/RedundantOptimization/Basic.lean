/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Cslib.Foundations.Data.Finset.Quorum

/-!
# Fault-tolerance in distributed optimization: the abstract one-shot model

Formalization of the model behind Section 3 of

* N. Gupta, N. H. Vaidya, *Fault-Tolerance in Distributed Optimization: The Case of Redundancy*,
  PODC 2020, DOI 10.1145/3382734.3405748.

There are `n` agents `Fin n`. In an execution, a set `H` of agents is honest (non-faulty) and
`|H| ≥ n - f`; honest agent `i` has the cost function `Q i : X → ℝ`. The server receives one cost
function `C j` from every agent: `C i = Q i` for `i ∈ H`, and an arbitrary *admissible* function for
`j ∉ H` (in the paper: an arbitrary differentiable convex function; a non-admissible function would
expose its sender). A deterministic algorithm is a map `Π` from received vectors to points; this is
the "best case for the server" of Section 3.1 (Theorem 1 is proved in this model).

Everything in this file works for an arbitrary type `X` and arbitrary real cost functions:

* `argmin`, `agg` — the set of minimum points and the aggregate `∑_{i∈S} Q i`;
* `lemma1` — Lemma 1 of the paper (no convexity or differentiability needed, `S` may be empty);
* `TwoFRedundant` — Definition 1 (2f-redundancy);
* `Resilient` — Definition 2 (f-resilience), relative to an explicit class of executions;
* `exists_resilient_redundant` — a deterministic algorithm that is f-resilient on *every*
  2f-redundant execution (existence half of the paper's characterization, for all `n`, `f`);
* `exists_resilient_redundant_insert` — such an algorithm can additionally be made f-resilient on any
  execution whose honest functions have a common minimum point, redundant or not.
-/

open Finset

namespace RedundantOptimization

variable {X : Type*} {ι : Type*}

/-- The set `arg min_w g(w)` of (global) minimum points of `g`. -/
def argmin (g : X → ℝ) : Set X := {w | ∀ v, g w ≤ g v}

/-- The aggregate cost `∑_{i ∈ S} Q_i` of a set `S` of agents. -/
def agg (S : Finset ι) (Q : ι → X → ℝ) : X → ℝ := fun w => ∑ i ∈ S, Q i w

@[simp] lemma agg_apply (S : Finset ι) (Q : ι → X → ℝ) (w : X) :
    agg S Q w = ∑ i ∈ S, Q i w := rfl

lemma agg_congr {S : Finset ι} {Q Q' : ι → X → ℝ} (h : ∀ i ∈ S, Q i = Q' i) :
    agg S Q = agg S Q' := by
  funext w; simp only [agg_apply]; exact Finset.sum_congr rfl fun i hi => by rw [h i hi]

@[simp] lemma argmin_agg_empty (Q : ι → X → ℝ) : argmin (agg ∅ Q) = Set.univ := by
  ext w; simp [argmin]

/-- **Lemma 1** of the paper. If the cost functions of the agents in `S` have a common minimum
point, then the minimum points of their aggregate are exactly the common minimum points.
(The paper assumes `S` non-empty; this is not needed.) -/
theorem lemma1 (S : Finset ι) (Q : ι → X → ℝ) (h : (⋂ i ∈ S, argmin (Q i)).Nonempty) :
    argmin (agg S Q) = ⋂ i ∈ S, argmin (Q i) := by
  obtain ⟨w', hw'⟩ := h
  simp only [Set.mem_iInter] at hw'
  ext w
  simp only [Set.mem_iInter]
  constructor
  · intro hw i hi v
    -- all terms are `≥` their values at `w'`, and the sums are `≤`, so they are equal
    have hle : ∀ j ∈ S, Q j w' ≤ Q j w := fun j hj => hw' j hj w
    have hsum : ∑ j ∈ S, Q j w' = ∑ j ∈ S, Q j w :=
      le_antisymm (Finset.sum_le_sum hle) (hw w')
    have := (Finset.sum_eq_sum_iff_of_le hle).1 hsum i hi
    rw [← this]; exact hw' i hi v
  · intro hw v
    exact Finset.sum_le_sum fun i hi => hw i hi v

/-- If `w` minimizes every `Q i`, `i ∈ S`, it minimizes the aggregate (easy half of Lemma 1). -/
lemma mem_argmin_agg_of_forall {S : Finset ι} {Q : ι → X → ℝ} {w : X}
    (h : ∀ i ∈ S, w ∈ argmin (Q i)) : w ∈ argmin (agg S Q) :=
  fun v => Finset.sum_le_sum fun i hi => h i hi v

/-- **Definition 1 (2f-redundancy).** The honest cost functions of `H` satisfy 2f-redundancy if
every subset `S ⊆ H` with `|S| ≥ n - 2f` has the same set of aggregate minimum points as `H`.
(`n - 2 * f` is truncated subtraction, which agrees with the paper's `|S| ≥ n - 2f` for `|S| ≥ 0`.) -/
def TwoFRedundant (n f : ℕ) (H : Finset ι) (Q : ι → X → ℝ) : Prop :=
  ∀ S ⊆ H, n - 2 * f ≤ S.card → argmin (agg S Q) = argmin (agg H Q)

lemma TwoFRedundant.congr {n f : ℕ} {H : Finset ι} {Q Q' : ι → X → ℝ}
    (h : TwoFRedundant n f H Q) (hQ : ∀ i ∈ H, Q i = Q' i) : TwoFRedundant n f H Q' := by
  intro S hS hcard
  rw [agg_congr (fun i hi => (hQ i (hS hi)).symm), agg_congr (fun i hi => (hQ i hi).symm)]
  exact h S hS hcard

/-! ### Executions, algorithms, resilience -/

variable {n : ℕ}

/-- An execution (more precisely, its honest part): the honest set `H` and the honest cost
functions (only `Q i` for `i ∈ H` matter). -/
abbrev Exec (n : ℕ) (X : Type*) := Finset (Fin n) × (Fin n → X → ℝ)

/-- The received vector `C` is *consistent* with the honest part `(H, Q)`: honest agents send their
own cost functions, the others send arbitrary admissible functions. -/
def Consistent (Adm : (X → ℝ) → Prop) (e : Exec n X) (C : Fin n → X → ℝ) : Prop :=
  (∀ i ∈ e.1, C i = e.2 i) ∧ ∀ j, Adm (C j)

/-- Executions of the model: at most `f` faulty agents and admissible honest cost functions. -/
def Valid (Adm : (X → ℝ) → Prop) (n f : ℕ) : Set (Exec n X) :=
  {e | n - f ≤ e.1.card ∧ ∀ i ∈ e.1, Adm (e.2 i)}

/-- All executions in which the honest aggregate has a minimum point (Definition 2 is
unsatisfiable on executions whose honest aggregate has none). -/
def AllExecs (Adm : (X → ℝ) → Prop) (n f : ℕ) : Set (Exec n X) :=
  {e | e ∈ Valid Adm n f ∧ (argmin (agg e.1 e.2)).Nonempty}

/-- Executions whose honest cost functions satisfy 2f-redundancy (and have a minimum point). -/
def RedExecs (Adm : (X → ℝ) → Prop) (n f : ℕ) : Set (Exec n X) :=
  {e | e ∈ AllExecs Adm n f ∧ TwoFRedundant n f e.1 e.2}

/-- **Definition 2 (f-resilience)**, relative to a class `K` of executions: on every execution of
`K` and for every behaviour of the faulty agents, the deterministic algorithm `alg` outputs a
minimum point of the aggregate cost of the honest agents. -/
def Resilient (Adm : (X → ℝ) → Prop) (K : Set (Exec n X))
    (alg : (Fin n → X → ℝ) → X) : Prop :=
  ∀ e ∈ K, ∀ C, Consistent Adm e C → alg C ∈ argmin (agg e.1 e.2)

lemma Resilient.mono {Adm : (X → ℝ) → Prop} {K K' : Set (Exec n X)}
    {alg : (Fin n → X → ℝ) → X} (h : Resilient Adm K alg) (hK : K' ⊆ K) :
    Resilient Adm K' alg := fun e he => h e (hK he)

/-- Two honest sets of size `≥ n - f` meet in at least `n - 2f` agents. -/
lemma card_inter_ge {f : ℕ} {T H : Finset (Fin n)} (hT : n - f ≤ T.card) (hH : n - f ≤ H.card) :
    n - 2 * f ≤ (T ∩ H).card := by
  simpa using Cslib.Quorum.card_sub_two_mul_le_card_inter (α := Fin n) (f := f)
    (by rwa [Fintype.card_fin]) (by rwa [Fintype.card_fin])

/-- Key fact behind sufficiency: two 2f-redundant executions that are consistent with the same
received vector have the same aggregate minimum points. -/
lemma argmin_eq_of_redundant {f : ℕ} {T H : Finset (Fin n)}
    {C : Fin n → X → ℝ} (hT : n - f ≤ T.card) (hH : n - f ≤ H.card)
    (hTr : TwoFRedundant n f T C) (hHr : TwoFRedundant n f H C) :
    argmin (agg T C) = argmin (agg H C) := by
  have hc := card_inter_ge hT hH
  rw [← hTr (T ∩ H) Finset.inter_subset_left hc, hHr (T ∩ H) Finset.inter_subset_right hc]

/-- **Sufficiency (existence form).** For all `n`, `f` and every admissibility predicate there is a
deterministic algorithm that is f-resilient on every 2f-redundant execution: output a minimum point
of the aggregate of *some* set of `≥ n - f` received functions that is 2f-redundant. -/
theorem exists_resilient_redundant [Nonempty X] (Adm : (X → ℝ) → Prop) (f : ℕ) :
    ∃ alg : (Fin n → X → ℝ) → X, Resilient Adm (RedExecs Adm n f) alg := by
  classical
  refine ⟨fun C => Classical.epsilon fun w => ∀ T : Finset (Fin n), n - f ≤ T.card →
      TwoFRedundant n f T C → (argmin (agg T C)).Nonempty → w ∈ argmin (agg T C), ?_⟩
  rintro ⟨H, Q⟩ ⟨⟨⟨hH, -⟩, hne⟩, hred⟩ C ⟨hC, -⟩
  simp only at hH hne hred hC
  have hagg : agg H C = agg H Q := agg_congr hC
  have hredC : TwoFRedundant n f H C := hred.congr fun i hi => (hC i hi).symm
  obtain ⟨w, hw⟩ := hne
  rw [← hagg] at hw ⊢
  have key : ∀ T : Finset (Fin n), n - f ≤ T.card → TwoFRedundant n f T C →
      (argmin (agg T C)).Nonempty → w ∈ argmin (agg T C) := by
    intro T hT hTr _
    rw [argmin_eq_of_redundant hT hH hTr hredC]; exact hw
  exact Classical.epsilon_spec (p := fun w => ∀ T : Finset (Fin n), n - f ≤ T.card →
      TwoFRedundant n f T C → (argmin (agg T C)).Nonempty → w ∈ argmin (agg T C)) ⟨w, key⟩
    H hH hredC ⟨w, hw⟩

/-- An execution `e₀` whose honest functions have a common minimum point `w₀` can be added to the
2f-redundant class: every 2f-redundant execution consistent with a received vector that is also
consistent with `e₀` has `w₀` among its aggregate minimum points. -/
lemma mem_argmin_of_redundant_of_common {Adm : (X → ℝ) → Prop} {f : ℕ} {e₀ : Exec n X}
    (he₀ : n - f ≤ e₀.1.card) {w₀ : X} (hw₀ : ∀ i ∈ e₀.1, w₀ ∈ argmin (e₀.2 i))
    {C : Fin n → X → ℝ} (hC : ∀ i ∈ e₀.1, C i = e₀.2 i) {e : Exec n X} (he : e ∈ RedExecs Adm n f)
    (heC : ∀ i ∈ e.1, C i = e.2 i) : w₀ ∈ argmin (agg e.1 e.2) := by
  obtain ⟨⟨⟨hT, -⟩, -⟩, hred⟩ := he
  have hc := card_inter_ge hT he₀
  rw [← hred (e.1 ∩ e₀.1) Finset.inter_subset_left hc]
  apply mem_argmin_agg_of_forall
  intro i hi
  rw [Finset.mem_inter] at hi
  rw [← heC i hi.1, hC i hi.2]
  exact hw₀ i hi.2

/-- **2f-redundancy is not a maximal solvable class.** For every execution `e₀` (redundant or not)
whose honest cost functions have a common minimum point, there is a deterministic algorithm that is
f-resilient on all 2f-redundant executions *and* on `e₀`. -/
theorem exists_resilient_redundant_insert [Nonempty X] (Adm : (X → ℝ) → Prop) (f : ℕ)
    (e₀ : Exec n X) (he₀ : n - f ≤ e₀.1.card)
    (hcommon : (⋂ i ∈ e₀.1, argmin (e₀.2 i)).Nonempty) :
    ∃ alg : (Fin n → X → ℝ) → X, Resilient Adm (insert e₀ (RedExecs Adm n f)) alg := by
  classical
  obtain ⟨alg, halg⟩ := exists_resilient_redundant (n := n) Adm f
  obtain ⟨w₀, hw₀⟩ := hcommon
  simp only [Set.mem_iInter] at hw₀
  refine ⟨fun C => if ∀ i ∈ e₀.1, C i = e₀.2 i then w₀ else alg C, ?_⟩
  rintro e he C hC
  dsimp only
  rcases he with rfl | he
  · split_ifs with h
    · exact mem_argmin_agg_of_forall hw₀
    · exact absurd hC.1 h
  · split_ifs with h
    · exact mem_argmin_of_redundant_of_common he₀ hw₀ h he hC.1
    · exact halg e he C hC

end RedundantOptimization
