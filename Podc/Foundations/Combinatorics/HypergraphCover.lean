import Mathlib

-- CSLib candidate: Cslib/Foundations/Combinatorics/HypergraphCover.lean

/-!
# Vertex covers, fractional covers and edge packings of hypergraphs

A (multi-)hypergraph is given by a vertex type `V`, an edge type `E` (both finite) and an incidence
map `inc : E → Finset V` (parallel edges are allowed, which is the natural set-cover reading: one
edge per element). We define

* `IsCover inc C` — `C` meets every edge (minimum-weight hypergraph vertex cover = weighted set cover);
* `IsFracCover inc x` — a feasible solution of the covering LP `∑_{v ∈ e} x(v) ≥ 1`, `x ≥ 0`;
* `IsPacking inc w δ` — a feasible solution of the dual edge-packing LP
  `∑_{e ∋ v} δ(e) ≤ w(v)`, `δ ≥ 0`;

and prove weak duality and the standard primal–dual bound for "tight" vertices: if every edge has
at most `f` vertices and every vertex of `T` is `β`-tight (`∑_{e ∋ v} δ(e) ≥ (1-β) w(v)`), then
`(1-β)·w(T) ≤ f·∑_e δ(e)`.

## Main statements

* `Cslib.Hypergraph.sum_le_of_isPacking`: weak duality `∑_e δ(e) ≤ ∑_v w(v) x(v)`.
* `Cslib.Hypergraph.mul_sum_tight_le`: `(1-β)·w(T) ≤ f·∑_e δ(e)` for `β`-tight `T`.
* `Cslib.Hypergraph.sum_tight_le_of_isPacking`: `w(T) ≤ (f + ε)·∑_v w(v) x(v)` for `β = ε/(f+ε)`
  (the primal–dual approximation bound, e.g. Claim A.1 of Ben-Basat et al., PODC 2019).
-/

namespace Cslib.Hypergraph

open Finset

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]

/-- The edges containing the vertex `v`. -/
def edgesAt (inc : E → Finset V) (v : V) : Finset E := univ.filter fun e => v ∈ inc e

/-- The load `∑_{e ∋ v} δ(e)` of an edge function `δ` at the vertex `v`. -/
def load (inc : E → Finset V) (δ : E → ℝ) (v : V) : ℝ := ∑ e ∈ edgesAt inc v, δ e

/-- `C` is a vertex cover of the hypergraph: it meets every edge. -/
def IsCover (inc : E → Finset V) (C : Finset V) : Prop := ∀ e, ∃ v ∈ inc e, v ∈ C

/-- `x` is a fractional vertex cover: a feasible solution of the covering LP. -/
def IsFracCover (inc : E → Finset V) (x : V → ℝ) : Prop :=
  (∀ v, 0 ≤ x v) ∧ ∀ e, 1 ≤ ∑ v ∈ inc e, x v

/-- `δ` is an edge packing: a feasible solution of the dual LP `∑_{e ∋ v} δ(e) ≤ w(v)`, `δ ≥ 0`. -/
def IsPacking (inc : E → Finset V) (w : V → ℝ) (δ : E → ℝ) : Prop :=
  (∀ e, 0 ≤ δ e) ∧ ∀ v, load inc δ v ≤ w v

omit [Fintype V] in
@[simp] theorem mem_edgesAt {inc : E → Finset V} {v : V} {e : E} :
    e ∈ edgesAt inc v ↔ v ∈ inc e := by simp [edgesAt]

/-- Double counting of incidences: `∑_v ∑_{e ∋ v} g v e = ∑_e ∑_{v ∈ e} g v e`. -/
theorem sum_edgesAt_comm (inc : E → Finset V) (g : V → E → ℝ) :
    ∑ v, ∑ e ∈ edgesAt inc v, g v e = ∑ e, ∑ v ∈ inc e, g v e := by
  simp only [edgesAt, sum_filter]
  rw [sum_comm]
  refine sum_congr rfl fun e _ => ?_
  rw [← sum_filter]
  congr 1
  ext v; simp

omit [Fintype V] [Fintype E] in
/-- The characteristic function of a vertex cover is a fractional vertex cover. -/
theorem IsCover.isFracCover {inc : E → Finset V} {C : Finset V} (hC : IsCover inc C) :
    IsFracCover inc fun v => if v ∈ C then 1 else 0 := by
  refine ⟨fun v => by dsimp only; split_ifs <;> norm_num, fun e => ?_⟩
  obtain ⟨v, hv, hvC⟩ := hC e
  calc (1 : ℝ) = if v ∈ C then 1 else 0 := by simp [hvC]
    _ ≤ ∑ u ∈ inc e, if u ∈ C then (1 : ℝ) else 0 :=
      single_le_sum (f := fun u => if u ∈ C then (1 : ℝ) else 0)
        (fun u _ => by split_ifs <;> norm_num) hv

/-- The weight of a vertex cover is the objective value of its characteristic function. -/
theorem sum_mul_indicator (w : V → ℝ) (C : Finset V) :
    ∑ v, w v * (if v ∈ C then 1 else 0) = ∑ v ∈ C, w v := by
  simp [mul_ite, sum_ite_mem]

/-- Weak duality: the value of an edge packing is at most the cost of any fractional cover. -/
theorem sum_le_of_isPacking {inc : E → Finset V} {w : V → ℝ} {δ : E → ℝ} {x : V → ℝ}
    (hδ : IsPacking inc w δ) (hx : IsFracCover inc x) : ∑ e, δ e ≤ ∑ v, w v * x v := by
  calc ∑ e, δ e ≤ ∑ e, ∑ v ∈ inc e, x v * δ e := by
        refine sum_le_sum fun e _ => ?_
        rw [← sum_mul]
        exact le_mul_of_one_le_left (hδ.1 e) (hx.2 e)
    _ = ∑ v, x v * load inc δ v := by
        rw [← sum_edgesAt_comm inc (fun v e => x v * δ e)]
        simp [load, mul_sum]
    _ ≤ ∑ v, w v * x v := by
        refine sum_le_sum fun v _ => ?_
        rw [mul_comm (w v)]
        exact mul_le_mul_of_nonneg_left (hδ.2 v) (hx.1 v)

/-- If every edge has at most `f` vertices, `δ ≥ 0`, and every vertex of `T` is `β`-tight, i.e.
`(1-β) w(v) ≤ ∑_{e ∋ v} δ(e)`, then `(1-β)·w(T) ≤ f·∑_e δ(e)`. -/
theorem mul_sum_tight_le {inc : E → Finset V} {w : V → ℝ} {δ : E → ℝ} {f : ℕ} {β : ℝ}
    (hf : ∀ e, (inc e).card ≤ f) (hδ : ∀ e, 0 ≤ δ e) {T : Finset V}
    (hT : ∀ v ∈ T, (1 - β) * w v ≤ load inc δ v) :
    (1 - β) * ∑ v ∈ T, w v ≤ f * ∑ e, δ e := by
  calc (1 - β) * ∑ v ∈ T, w v ≤ ∑ v ∈ T, load inc δ v := by
        rw [mul_sum]; exact sum_le_sum hT
    _ ≤ ∑ v, load inc δ v :=
        sum_le_sum_of_subset_of_nonneg (subset_univ _) fun v _ _ =>
          sum_nonneg fun e _ => hδ e
    _ = ∑ e, (inc e).card * δ e := by
        rw [show (∑ v, load inc δ v) = ∑ v, ∑ e ∈ edgesAt inc v, (fun _ e => δ e) v e from rfl,
          sum_edgesAt_comm]
        simp
    _ ≤ ∑ e, (f : ℝ) * δ e :=
        sum_le_sum fun e _ => mul_le_mul_of_nonneg_right (by exact_mod_cast hf e) (hδ e)
    _ = f * ∑ e, δ e := by rw [mul_sum]

/-- The primal–dual approximation bound: with `β = ε/(f+ε)`, the `β`-tight vertices of an edge
packing weigh at most `(f+ε)` times the cost of any fractional vertex cover (hence at most `f+ε`
times the optimum of the covering LP). -/
theorem sum_tight_le_of_isPacking {inc : E → Finset V} {w : V → ℝ} {δ : E → ℝ} {f : ℕ} {ε : ℝ}
    (hε : 0 < ε) (hf0 : 0 < f) (hf : ∀ e, (inc e).card ≤ f) (hδ : IsPacking inc w δ)
    {T : Finset V} (hT : ∀ v ∈ T, (1 - ε / (f + ε)) * w v ≤ load inc δ v) {x : V → ℝ}
    (hx : IsFracCover inc x) :
    ∑ v ∈ T, w v ≤ (f + ε) * ∑ v, w v * x v := by
  have hfp : (0 : ℝ) < f := by exact_mod_cast hf0
  have hfε : (0 : ℝ) < f + ε := by positivity
  have h1 : 1 - ε / (f + ε) = f / (f + ε) := by field_simp; ring
  have key := mul_sum_tight_le hf hδ.1 hT
  have hd := sum_le_of_isPacking hδ hx
  rw [h1, div_mul_eq_mul_div, div_le_iff₀ hfε] at key
  have : ∑ v ∈ T, w v ≤ (f + ε) * ∑ e, δ e := by nlinarith
  exact this.trans (mul_le_mul_of_nonneg_left hd hfε.le)

end Cslib.Hypergraph
