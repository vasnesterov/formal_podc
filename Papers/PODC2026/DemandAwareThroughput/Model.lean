import Mathlib.Analysis.Convex.DoublyStochasticMatrix
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Demand-aware throughput: the model

Bentert, Avin, Schmid, *A Separation Between Optimal Demand-Oblivious and Demand-Aware Network
Throughput*, PODC 2026 (arXiv:2605.04699v1), §1.1.

* A network on the node set `Fin n` is a directed multigraph (self-loops and parallel arcs
  allowed), given by its adjacency matrix `A : Matrix (Fin n) (Fin n) ℕ`; it is *directed
  `r`-regular* if every row and column of `A` sums to `r`.
* Every arc of an `r`-regular graph has capacity `1/r`. As in the paper we equivalently give every
  arc capacity `1` and scale the demand by `r`: `G` can host `M` iff it can route the
  multicommodity flow `r • M` (`CanHost`).
* A flow is a finite collection of pairs `(P_k, d_k)` of non-empty paths and non-negative amounts.
  It must serve exactly the demand of every ordered pair `(u, v)` (including `u = v`; a path has at
  least one arc, so demand from a node to itself uses a self-loop or a closed walk), and the total
  amount crossing the arcs from `u` to `v` must not exceed the number `A u v` of such arcs. A path
  that traverses the pair `(u, v)` several times is charged several times (see `differencies.md`:
  this is the most restrictive reading, used for constructions; the upper bounds in this
  development only use that a path through `(u,v)` is charged at least once).
* `CanDirectlyHost`: the same with single-arc paths only.
* The four decision problems of the paper (`DAThroughput`, `DAWeakThroughput`,
  `DADirectThroughput`, `DAWeakDirectThroughput`), with `N = 2n - 1` arcs per node. "The
  throughput of `G` w.r.t. `M` is at least `κ`" is rendered as "`G` can host `θ • M` for some
  `θ ≥ κ`" (the paper's throughput is the largest such `θ`).
-/

namespace Podc.DemandAwareThroughput

open Finset

variable {n : ℕ}

/-- A directed `r`-regular multigraph on `Fin n`: all row and column sums of the adjacency
matrix are `r`. -/
def IsRegular (r : ℕ) (A : Matrix (Fin n) (Fin n) ℕ) : Prop :=
  (∀ i, ∑ j, A i j = r) ∧ (∀ j, ∑ i, A i j = r)

/-- A non-empty path (a walk with at least one arc) in the complete directed graph on `Fin n`,
given by its start vertex `src` and the list `rest` of the following vertices. -/
structure Path (n : ℕ) where
  /-- First vertex. -/
  src : Fin n
  /-- The remaining vertices `v₁, …, v_ℓ` (`ℓ ≥ 1`). -/
  rest : List (Fin n)
  rest_ne : rest ≠ []

/-- The last vertex of a path. -/
def Path.tgt (p : Path n) : Fin n := p.rest.getLast p.rest_ne

/-- The arcs (ordered pairs of consecutive vertices) of a path, with repetitions. -/
def Path.arcs (p : Path n) : List (Fin n × Fin n) := (p.src :: p.rest).zip p.rest

/-- The single-arc path `u → v`. -/
def Path.arc (u v : Fin n) : Path n := ⟨u, [v], by simp⟩

/-- The two-arc path `u → h → v`. -/
def Path.two (u h v : Fin n) : Path n := ⟨u, [h, v], by simp⟩

@[simp] lemma Path.arc_src (u v : Fin n) : (Path.arc u v).src = u := rfl
@[simp] lemma Path.arc_tgt (u v : Fin n) : (Path.arc u v).tgt = v := rfl
@[simp] lemma Path.arc_arcs (u v : Fin n) : (Path.arc u v).arcs = [(u, v)] := rfl
@[simp] lemma Path.two_src (u h v : Fin n) : (Path.two u h v).src = u := rfl
@[simp] lemma Path.two_tgt (u h v : Fin n) : (Path.two u h v).tgt = v := rfl
@[simp] lemma Path.two_arcs (u h v : Fin n) : (Path.two u h v).arcs = [(u, h), (h, v)] := rfl

lemma Path.arcs_of_length_one {p : Path n} (h : p.rest.length = 1) :
    p.arcs = [(p.src, p.tgt)] := by
  obtain ⟨s, r, hr⟩ := p
  match r, hr, h with
  | [w], _, _ => rfl

/-- Demand served from `u` to `v` by the flow `(P, d)`. -/
noncomputable def served {ι : Type} [Fintype ι] (P : ι → Path n) (d : ι → ℝ) (u v : Fin n) : ℝ :=
  ∑ k, if (P k).src = u ∧ (P k).tgt = v then d k else 0

/-- Total amount the flow `(P, d)` sends over the arcs from `u` to `v` (a path traversing
`(u, v)` several times is counted several times). -/
noncomputable def load {ι : Type} [Fintype ι] (P : ι → Path n) (d : ι → ℝ) (u v : Fin n) : ℝ :=
  ∑ k, d k * ((P k).arcs.count (u, v) : ℝ)

/-- A feasible multicommodity flow for the (already scaled) demand `D` in the multigraph `A` with
unit arc capacities. -/
def IsFlow {ι : Type} [Fintype ι] (A : Matrix (Fin n) (Fin n) ℕ) (D : Matrix (Fin n) (Fin n) ℝ)
    (P : ι → Path n) (d : ι → ℝ) : Prop :=
  (∀ k, 0 ≤ d k) ∧ (∀ u v, served P d u v = D u v) ∧ (∀ u v, load P d u v ≤ A u v)

/-- The multigraph `A` with unit arc capacities can route the demand `D`. -/
def CanRoute (A : Matrix (Fin n) (Fin n) ℕ) (D : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (P : ι → Path n) (d : ι → ℝ), IsFlow A D P d

/-- The multigraph `A` can route the demand `D` along single arcs only. -/
def CanRouteDirectly (A : Matrix (Fin n) (Fin n) ℕ) (D : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (P : ι → Path n) (d : ι → ℝ),
    IsFlow A D P d ∧ ∀ k, (P k).rest.length = 1

/-- An `r`-regular graph `A` (arc capacities `1/r`) can host the demand matrix `M`
(§1.1: equivalently, with unit capacities it can route `r • M`). -/
def CanHost (r : ℕ) (A : Matrix (Fin n) (Fin n) ℕ) (M : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  CanRoute A ((r : ℝ) • M)

/-- `A` can directly host `M`. -/
def CanDirectlyHost (r : ℕ) (A : Matrix (Fin n) (Fin n) ℕ) (M : Matrix (Fin n) (Fin n) ℝ) :
    Prop :=
  CanRouteDirectly A ((r : ℝ) • M)

/-- The number of arcs per node, `N = 2n - 1`. -/
abbrev deg (n : ℕ) : ℕ := 2 * n - 1

/-- **Demand-Aware Throughput**: there is a directed `(2n-1)`-regular graph whose throughput
with respect to `M` is at least `κ`. -/
def DAThroughput (M : Matrix (Fin n) (Fin n) ℝ) (κ : ℝ) : Prop :=
  ∃ A, IsRegular (deg n) A ∧ ∃ θ, κ ≤ θ ∧ CanHost (deg n) A (θ • M)

/-- **Demand-Aware Direct Throughput**. -/
def DADirectThroughput (M : Matrix (Fin n) (Fin n) ℝ) (κ : ℝ) : Prop :=
  ∃ A, IsRegular (deg n) A ∧ ∃ θ, κ ≤ θ ∧ CanDirectlyHost (deg n) A (θ • M)

/-- **Demand-Aware Weak Throughput**: some `(2n-1)`-regular graph can host a sub-demand `M' ≤ M`
carrying at least a `κ`-fraction of the total demand `∑ M = n`. -/
def DAWeakThroughput (M : Matrix (Fin n) (Fin n) ℝ) (κ : ℝ) : Prop :=
  ∃ A, IsRegular (deg n) A ∧ ∃ M' : Matrix (Fin n) (Fin n) ℝ, (∀ i j, M' i j ≤ M i j) ∧
    κ ≤ (∑ i, ∑ j, M' i j) / n ∧ CanHost (deg n) A M'

/-- **Demand-Aware Weak Direct Throughput**. -/
def DAWeakDirectThroughput (M : Matrix (Fin n) (Fin n) ℝ) (κ : ℝ) : Prop :=
  ∃ A, IsRegular (deg n) A ∧ ∃ M' : Matrix (Fin n) (Fin n) ℝ, (∀ i j, M' i j ≤ M i j) ∧
    κ ≤ (∑ i, ∑ j, M' i j) / n ∧ CanDirectlyHost (deg n) A M'

/-! ### Basic facts -/

lemma CanRouteDirectly.canRoute {A : Matrix (Fin n) (Fin n) ℕ} {D : Matrix (Fin n) (Fin n) ℝ}
    (h : CanRouteDirectly A D) : CanRoute A D := by
  obtain ⟨ι, _, P, d, hf, -⟩ := h
  exact ⟨ι, inferInstance, P, d, hf⟩

/-- Routing can be scaled down. -/
lemma CanRoute.smul {A : Matrix (Fin n) (Fin n) ℕ} {D : Matrix (Fin n) (Fin n) ℝ}
    (h : CanRoute A D) {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) : CanRoute A (c • D) := by
  obtain ⟨ι, _, P, d, hd, hs, hl⟩ := h
  refine ⟨ι, inferInstance, P, fun k => c * d k, fun k => mul_nonneg hc0 (hd k), fun u v => ?_, fun u v => ?_⟩
  · have := hs u v
    simp only [served] at this ⊢
    simp only [Matrix.smul_apply, smul_eq_mul, ← this, mul_sum]
    refine sum_congr rfl fun k _ => ?_
    split_ifs <;> simp
  · have h1 := hl u v
    simp only [load] at h1 ⊢
    calc ∑ k, c * d k * ((P k).arcs.count (u, v) : ℝ)
        = c * ∑ k, d k * ((P k).arcs.count (u, v) : ℝ) := by
          rw [mul_sum]; exact sum_congr rfl fun k _ => by ring
      _ ≤ 1 * ∑ k, d k * ((P k).arcs.count (u, v) : ℝ) := by
          apply mul_le_mul_of_nonneg_right hc1
          exact sum_nonneg fun k _ => mul_nonneg (hd k) (Nat.cast_nonneg _)
      _ ≤ A u v := by rw [one_mul]; exact h1

/-- Direct routing can be scaled down. -/
lemma CanRouteDirectly.smul {A : Matrix (Fin n) (Fin n) ℕ} {D : Matrix (Fin n) (Fin n) ℝ}
    (h : CanRouteDirectly A D) {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    CanRouteDirectly A (c • D) := by
  obtain ⟨ι, _, P, d, hf, hlen⟩ := h
  obtain ⟨hd, hs, hl⟩ := hf
  refine ⟨ι, inferInstance, P, fun k => c * d k, ⟨fun k => mul_nonneg hc0 (hd k), fun u v => ?_, fun u v => ?_⟩,
    hlen⟩
  · have := hs u v
    simp only [served] at this ⊢
    simp only [Matrix.smul_apply, smul_eq_mul, ← this, mul_sum]
    refine sum_congr rfl fun k _ => ?_
    split_ifs <;> simp
  · have h1 := hl u v
    simp only [load] at h1 ⊢
    calc ∑ k, c * d k * ((P k).arcs.count (u, v) : ℝ)
        = c * ∑ k, d k * ((P k).arcs.count (u, v) : ℝ) := by
          rw [mul_sum]; exact sum_congr rfl fun k _ => by ring
      _ ≤ 1 * ∑ k, d k * ((P k).arcs.count (u, v) : ℝ) := by
          apply mul_le_mul_of_nonneg_right hc1
          exact sum_nonneg fun k _ => mul_nonneg (hd k) (Nat.cast_nonneg _)
      _ ≤ A u v := by rw [one_mul]; exact h1

/-- Direct routing is exactly entrywise domination: `D` can be routed along single arcs of `A`
iff `0 ≤ D ≤ A` entrywise. -/
theorem canRouteDirectly_iff {A : Matrix (Fin n) (Fin n) ℕ} {D : Matrix (Fin n) (Fin n) ℝ} :
    CanRouteDirectly A D ↔ ∀ u v, 0 ≤ D u v ∧ D u v ≤ A u v := by
  constructor
  · rintro ⟨ι, _, P, d, ⟨hd, hs, hl⟩, hlen⟩ u v
    have key : ∀ k, ((P k).arcs.count (u, v) : ℝ) =
        if (P k).src = u ∧ (P k).tgt = v then 1 else 0 := by
      intro k
      rw [Path.arcs_of_length_one (hlen k), List.count_singleton]
      by_cases h : (P k).src = u ∧ (P k).tgt = v
      · obtain ⟨h1, h2⟩ := h; simp [h1, h2]
      · rw [ite_eq_right h]
        have : ¬ ((P k).src, (P k).tgt) = (u, v) := by
          intro h'; simp only [Prod.mk.injEq] at h'; exact h h'
        simp [this]
    refine ⟨?_, ?_⟩
    · rw [← hs u v]; exact sum_nonneg fun k _ => by split_ifs <;> simp [hd k]
    · rw [← hs u v]
      refine le_of_eq_of_le ?_ (hl u v)
      simp only [served, load, key]
      exact sum_congr rfl fun k _ => by split_ifs <;> simp
  · intro h
    refine ⟨Fin n × Fin n, inferInstance, fun p => Path.arc p.1 p.2, fun p => D p.1 p.2,
      ⟨fun p => (h p.1 p.2).1, fun u v => ?_, fun u v => ?_⟩, fun p => rfl⟩
    · simp only [served, Path.arc_src, Path.arc_tgt]
      rw [Fintype.sum_eq_single (u, v)]
      · simp
      · rintro ⟨a, b⟩ hab
        have : ¬ (a = u ∧ b = v) := by rintro ⟨rfl, rfl⟩; exact hab rfl
        simp [this]
    · simp only [load, Path.arc_arcs]
      rw [Fintype.sum_eq_single (u, v)]
      · simpa using (h u v).2
      · rintro ⟨a, b⟩ hab
        rw [List.count_singleton]
        simp only [beq_iff_eq, Nat.cast_ite, Nat.cast_one, Nat.cast_zero, mul_ite, mul_one,
          mul_zero]
        rw [ite_eq_right]
        intro h'; exact hab (by rw [h'])

/-- Hosting `θ • M` for some `θ ≥ κ ≥ 0` gives hosting `κ • M`. -/
lemma CanHost.of_le {r : ℕ} {A : Matrix (Fin n) (Fin n) ℕ} {M : Matrix (Fin n) (Fin n) ℝ}
    {κ θ : ℝ} (h : CanHost r A (θ • M)) (hκ : 0 ≤ κ) (hκθ : κ ≤ θ) : CanHost r A (κ • M) := by
  rcases eq_or_lt_of_le (hκ.trans hκθ) with h0 | hθ
  · subst h0
    have : κ = 0 := le_antisymm hκθ hκ
    subst this; exact h
  · have := CanRoute.smul h (c := κ / θ) (div_nonneg hκ hθ.le) ((div_le_one hθ).2 hκθ)
    unfold CanHost
    convert this using 1
    ext i j
    simp only [Matrix.smul_apply, smul_eq_mul]
    field_simp

lemma CanDirectlyHost.of_le {r : ℕ} {A : Matrix (Fin n) (Fin n) ℕ}
    {M : Matrix (Fin n) (Fin n) ℝ}
    {κ θ : ℝ} (h : CanDirectlyHost r A (θ • M)) (hκ : 0 ≤ κ) (hκθ : κ ≤ θ) :
    CanDirectlyHost r A (κ • M) := by
  rcases eq_or_lt_of_le (hκ.trans hκθ) with h0 | hθ
  · subst h0
    have : κ = 0 := le_antisymm hκθ hκ
    subst this; exact h
  · have := CanRouteDirectly.smul h (c := κ / θ) (div_nonneg hκ hθ.le) ((div_le_one hθ).2 hκθ)
    unfold CanDirectlyHost
    convert this using 1
    ext i j
    simp only [Matrix.smul_apply, smul_eq_mul]
    field_simp

/-- **Observation 1** (first part): a yes-instance of Demand-Aware Direct Throughput is a
yes-instance of Demand-Aware Throughput. -/
theorem observation_1_direct {M : Matrix (Fin n) (Fin n) ℝ} {κ : ℝ}
    (h : DADirectThroughput M κ) : DAThroughput M κ := by
  obtain ⟨A, hA, θ, hθ, h⟩ := h
  exact ⟨A, hA, θ, hθ, CanRouteDirectly.canRoute h⟩

/-- **Observation 1** (second part): weak direct ⇒ weak. -/
theorem observation_1_weak {M : Matrix (Fin n) (Fin n) ℝ} {κ : ℝ}
    (h : DAWeakDirectThroughput M κ) : DAWeakThroughput M κ := by
  obtain ⟨A, hA, M', h1, h2, h⟩ := h
  exact ⟨A, hA, M', h1, h2, CanRouteDirectly.canRoute h⟩

lemma sum_smul_doublyStochastic {M : Matrix (Fin n) (Fin n) ℝ}
    (hM : M ∈ doublyStochastic ℝ (Fin n)) (hn : 0 < n) (κ : ℝ) :
    (∑ i, ∑ j, (κ • M) i j) / n = κ := by
  simp only [Matrix.smul_apply, smul_eq_mul, ← mul_sum, sum_row_of_mem_doublyStochastic hM,
    mul_one, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  have : (n : ℝ) ≠ 0 := by positivity
  field_simp

/-- **Observation 2** (first part): for `κ ∈ [0, 1]`, a yes-instance of Demand-Aware Throughput
is a yes-instance of Demand-Aware Weak Throughput (host `κ • M ≤ M`). -/
theorem observation_2 {M : Matrix (Fin n) (Fin n) ℝ} (hM : M ∈ doublyStochastic ℝ (Fin n))
    (hn : 0 < n) {κ : ℝ} (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1) (h : DAThroughput M κ) :
    DAWeakThroughput M κ := by
  obtain ⟨A, hA, θ, hθ, h⟩ := h
  refine ⟨A, hA, κ • M, fun i j => ?_, (sum_smul_doublyStochastic hM hn κ).ge,
    h.of_le hκ0 hθ⟩
  simp only [Matrix.smul_apply, smul_eq_mul]
  exact mul_le_of_le_one_left (nonneg_of_mem_doublyStochastic hM) hκ1

/-- **Observation 2** (second part): direct ⇒ weak direct, for `κ ∈ [0, 1]`. -/
theorem observation_2_direct {M : Matrix (Fin n) (Fin n) ℝ}
    (hM : M ∈ doublyStochastic ℝ (Fin n))
    (hn : 0 < n) {κ : ℝ} (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1) (h : DADirectThroughput M κ) :
    DAWeakDirectThroughput M κ := by
  obtain ⟨A, hA, θ, hθ, h⟩ := h
  refine ⟨A, hA, κ • M, fun i j => ?_, (sum_smul_doublyStochastic hM hn κ).ge,
    h.of_le hκ0 hθ⟩
  simp only [Matrix.smul_apply, smul_eq_mul]
  exact mul_le_of_le_one_left (nonneg_of_mem_doublyStochastic hM) hκ1

/-! ### Relabelling the nodes -/

/-- The image of a path under a relabelling of the nodes. -/
def Path.map (e : Fin n ≃ Fin n) (p : Path n) : Path n :=
  ⟨e p.src, p.rest.map e, by simpa using p.rest_ne⟩

@[simp] lemma Path.map_src (e : Fin n ≃ Fin n) (p : Path n) : (p.map e).src = e p.src := rfl

@[simp] lemma Path.map_tgt (e : Fin n ≃ Fin n) (p : Path n) : (p.map e).tgt = e p.tgt := by
  simp [Path.map, Path.tgt, List.getLast_map]

lemma Path.map_arcs (e : Fin n ≃ Fin n) (p : Path n) :
    (p.map e).arcs = p.arcs.map (Prod.map e e) := by
  simp only [Path.map, Path.arcs]
  rw [← List.map_cons, List.zip_map]

lemma Path.count_map (e : Fin n ≃ Fin n) (p : Path n) (u v : Fin n) :
    (p.map e).arcs.count (u, v) = p.arcs.count (e.symm u, e.symm v) := by
  rw [Path.map_arcs]
  have hinj : Function.Injective (Prod.map e e) :=
    Function.Injective.prodMap e.injective e.injective
  have : (u, v) = Prod.map e e (e.symm u, e.symm v) := by simp
  rw [this, List.count_map_of_injective _ _ hinj]

/-- Routing is invariant under relabelling the nodes. -/
lemma CanRoute.perm {A : Matrix (Fin n) (Fin n) ℕ} {D : Matrix (Fin n) (Fin n) ℝ}
    (h : CanRoute A D) (e : Fin n ≃ Fin n) :
    CanRoute (fun u v => A (e.symm u) (e.symm v)) (fun u v => D (e.symm u) (e.symm v)) := by
  obtain ⟨ι, _, P, d, hd, hs, hl⟩ := h
  refine ⟨ι, inferInstance, fun k => (P k).map e, d, hd, fun u v => ?_, fun u v => ?_⟩
  · change _ = D (e.symm u) (e.symm v)
    rw [← hs]
    unfold served
    refine sum_congr rfl fun k _ => ?_
    simp only [Path.map_src, Path.map_tgt]
    apply if_congr _ rfl rfl
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨by rw [← h1]; simp, by rw [← h2]; simp⟩
    · rintro ⟨h1, h2⟩; exact ⟨by rw [h1]; simp, by rw [h2]; simp⟩
  · refine le_of_eq_of_le ?_ (hl (e.symm u) (e.symm v))
    unfold load
    exact sum_congr rfl fun k _ => by rw [Path.count_map]

/-! ### The relaxed (indicator) capacity semantics

The paper charges a path `P_i` once to every arc `e ∈ P_i` of the multigraph
(`∑ᵢ 1_{e ∈ Pᵢ} dᵢ ≤ 1` per arc). Summed over the `A u v` parallel arcs from `u` to `v`, a path
through the pair `(u, v)` is charged at least once. `CanRouteRel` only asks for this aggregated
bound, so it is implied both by `CanRoute` and by the paper's per-arc condition; upper bounds
(no-instances) are proved for it. -/

/-- Total amount of the paths of `(P, d)` that traverse the pair `(u, v)` at least once. -/
noncomputable def loadInd {ι : Type} [Fintype ι] (P : ι → Path n) (d : ι → ℝ) (u v : Fin n) :
    ℝ :=
  ∑ k, d k * (if (u, v) ∈ (P k).arcs then 1 else 0)

/-- Relaxed routing: every path through the pair `(u, v)` is charged once to it. -/
def CanRouteRel (A : Matrix (Fin n) (Fin n) ℕ) (D : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (P : ι → Path n) (d : ι → ℝ),
    (∀ k, 0 ≤ d k) ∧ (∀ u v, served P d u v = D u v) ∧ (∀ u v, loadInd P d u v ≤ A u v)

lemma CanRoute.rel {A : Matrix (Fin n) (Fin n) ℕ} {D : Matrix (Fin n) (Fin n) ℝ}
    (h : CanRoute A D) : CanRouteRel A D := by
  obtain ⟨ι, _, P, d, hd, hs, hl⟩ := h
  refine ⟨ι, inferInstance, P, d, hd, hs, fun u v => le_trans ?_ (hl u v)⟩
  unfold loadInd load
  refine sum_le_sum fun k _ => mul_le_mul_of_nonneg_left ?_ (hd k)
  split_ifs with h
  · exact_mod_cast List.count_pos_iff.2 h
  · exact Nat.cast_nonneg _

/-- Demand-Aware Throughput in the relaxed semantics (`DAThroughput.rel`: implied by the
original). -/
def DAThroughputRel (M : Matrix (Fin n) (Fin n) ℝ) (κ : ℝ) : Prop :=
  ∃ A, IsRegular (deg n) A ∧ ∃ θ, κ ≤ θ ∧ CanRouteRel A ((deg n : ℝ) • (θ • M))

/-- Demand-Aware Weak Throughput in the relaxed semantics. -/
def DAWeakThroughputRel (M : Matrix (Fin n) (Fin n) ℝ) (κ : ℝ) : Prop :=
  ∃ A, IsRegular (deg n) A ∧ ∃ M' : Matrix (Fin n) (Fin n) ℝ, (∀ i j, M' i j ≤ M i j) ∧
    κ ≤ (∑ i, ∑ j, M' i j) / n ∧ CanRouteRel A ((deg n : ℝ) • M')

lemma DAThroughput.rel {M : Matrix (Fin n) (Fin n) ℝ} {κ : ℝ} (h : DAThroughput M κ) :
    DAThroughputRel M κ := by
  obtain ⟨A, hA, θ, hθ, h⟩ := h
  exact ⟨A, hA, θ, hθ, CanRoute.rel h⟩

lemma DAWeakThroughput.rel {M : Matrix (Fin n) (Fin n) ℝ} {κ : ℝ} (h : DAWeakThroughput M κ) :
    DAWeakThroughputRel M κ := by
  obtain ⟨A, hA, M', h1, h2, h⟩ := h
  exact ⟨A, hA, M', h1, h2, CanRoute.rel h⟩

/-- Relaxed routing is invariant under relabelling the nodes. -/
lemma CanRouteRel.perm {A : Matrix (Fin n) (Fin n) ℕ} {D : Matrix (Fin n) (Fin n) ℝ}
    (h : CanRouteRel A D) (e : Fin n ≃ Fin n) :
    CanRouteRel (fun u v => A (e.symm u) (e.symm v)) (fun u v => D (e.symm u) (e.symm v)) := by
  obtain ⟨ι, _, P, d, hd, hs, hl⟩ := h
  refine ⟨ι, inferInstance, fun k => (P k).map e, d, hd, fun u v => ?_, fun u v => ?_⟩
  · change _ = D (e.symm u) (e.symm v)
    rw [← hs]
    unfold served
    refine sum_congr rfl fun k _ => ?_
    simp only [Path.map_src, Path.map_tgt]
    apply if_congr _ rfl rfl
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨by rw [← h1]; simp, by rw [← h2]; simp⟩
    · rintro ⟨h1, h2⟩; exact ⟨by rw [h1]; simp, by rw [h2]; simp⟩
  · refine le_of_eq_of_le ?_ (hl (e.symm u) (e.symm v))
    unfold loadInd
    refine sum_congr rfl fun k _ => ?_
    have : (u, v) ∈ ((P k).map e).arcs ↔ (e.symm u, e.symm v) ∈ (P k).arcs := by
      rw [← List.count_pos_iff, ← List.count_pos_iff, Path.count_map]
    simp only [this]

end Podc.DemandAwareThroughput
