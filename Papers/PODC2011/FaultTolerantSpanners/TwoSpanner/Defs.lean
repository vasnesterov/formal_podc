import Mathlib

/-!
# Directed fault-tolerant spanners and LP (4) (Section 3 of Dinitz–Krauthgamer, PODC'11)

Section 3 works with a **directed** graph `G = (V, E)` with **unit edge lengths** and arbitrary
nonnegative arc costs `c`. We represent `E` as a finite set of arcs `E : Finset (V × V)` (loopless
where needed, `Loopless E`), and a candidate spanner as a sub-arc-set `H ⊆ E`.

* `DWalk E F u v n` — a directed walk with exactly `n` arcs of `E` from `u` to `v` all of whose
  vertices avoid `F` (except possibly the start vertex of an empty walk; the spanner definition
  only asks about `u, v ∉ F`).
* `IsFTSpanner E H r k` — `H` is an `r`-fault-tolerant `k`-spanner of `(V, E)`: `H ⊆ E` and for
  every `F ⊆ V` with `|F| ≤ r` and all `u, v ∉ F`, `d_{H \ F}(u, v) ≤ k · d_{G \ F}(u, v)` (unit
  lengths; stated with walks: every walk of length `n` in `G \ F` is matched by a walk of length
  `≤ k n` in `H \ F`; if there is no walk in `G \ F` the condition is vacuous, as `∞ ≤ k · ∞`).
* `mids E u v` — the midpoints `z` of the length-2 paths `u → z → v` in `E` (the set `P_{u,v}` of
  the paper: a length-2 path is determined by its midpoint).
* `IsLP4Feasible E r x f` — feasibility for LP (4): capacity, knapsack-cover and multiplicity
  constraints; `f uv z` is the flow `f_P` on the path `P = (u, z, v) ∈ P_{u,v}`.
* `roundE E x α T` — the output of Algorithm 1 (rounding) for thresholds `T : V → ℝ`.
-/

open Finset

namespace DinitzKrauthgamer

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- No arc is a self-loop. -/
def Loopless (E : Finset (V × V)) : Prop := ∀ e ∈ E, e.1 ≠ e.2

/-- `DWalk E F u v n`: a directed walk `u = x₀ → x₁ → ⋯ → xₙ = v` with arcs in `E`, all of whose
arcs have both endpoints outside `F`. -/
inductive DWalk (E : Finset (V × V)) (F : Finset V) : V → V → ℕ → Prop
  | nil (u : V) : DWalk E F u u 0
  | cons {u w v : V} {n : ℕ} : (u, w) ∈ E → u ∉ F → w ∉ F → DWalk E F w v n →
      DWalk E F u v (n + 1)

/-- `H` is an `r`-fault-tolerant `k`-spanner of the unit-length digraph `(V, E)`:
`H ⊆ E`, and for every fault set `F` with `|F| ≤ r` and all `u, v ∉ F`,
`d_{H \ F}(u, v) ≤ k · d_{G \ F}(u, v)`. -/
def IsFTSpanner (E H : Finset (V × V)) (r k : ℕ) : Prop :=
  H ⊆ E ∧ ∀ F : Finset V, #F ≤ r → ∀ u v, u ∉ F → v ∉ F →
    ∀ n, DWalk E F u v n → ∃ m ≤ k * n, DWalk H F u v m

/-- Midpoints of the length-2 paths from `u` to `v` (the paper's `P_{u,v}`). -/
def mids (E : Finset (V × V)) (u v : V) : Finset V :=
  univ.filter fun z => (u, z) ∈ E ∧ (z, v) ∈ E

@[simp] lemma mem_mids {E : Finset (V × V)} {u v z : V} :
    z ∈ mids E u v ↔ (u, z) ∈ E ∧ (z, v) ∈ E := by
  simp [mids]

/-- Total cost of an arc set. -/
def cost (c : V × V → ℝ) (H : Finset (V × V)) : ℝ := ∑ e ∈ H, c e

/-- Objective value `∑_e c_e x_e` of LP (4). -/
def lpValue (c : V × V → ℝ) (E : Finset (V × V)) (x : V × V → ℝ) : ℝ := ∑ e ∈ E, c e * x e

/-- Feasibility for **LP (4)**. The variables are `x e` (capacity of arc `e`) and `f uv z` (flow on
the length-2 path `u → z → v`, for `uv = (u, v) ∈ E`, `z ∈ mids E u v`). The capacity constraint is
written literally as in the paper: for every `(u, v) ∈ E` and every arc `e`, the flow on the paths
in `P_{u,v}` that use `e` is at most `x e`. -/
structure IsLP4Feasible (E : Finset (V × V)) (r : ℕ) (x : V × V → ℝ) (f : V × V → V → ℝ) :
    Prop where
  /-- Capacity constraints `∑_{P ∈ P_{u,v} : e ∈ P} f_P ≤ x_e`. -/
  capacity : ∀ uv ∈ E, ∀ e ∈ E,
    ∑ z ∈ (mids E uv.1 uv.2).filter (fun z => (uv.1, z) = e ∨ (z, uv.2) = e), f uv z ≤ x e
  /-- Knapsack-cover constraints
  `(r + 1 - |W|) x_{(u,v)} + ∑_{P ∈ P_{u,v} \ W} f_P ≥ r + 1 - |W|` for `W ⊆ P_{u,v}`, `|W| ≤ r`. -/
  knapsack : ∀ uv ∈ E, ∀ W ⊆ mids E uv.1 uv.2, #W ≤ r →
    ((r : ℝ) + 1 - #W) * x uv + ∑ z ∈ mids E uv.1 uv.2 \ W, f uv z ≥ (r : ℝ) + 1 - #W
  /-- Multiplicity constraints `0 ≤ x_e ≤ 1`. -/
  x_nonneg : ∀ e ∈ E, 0 ≤ x e
  x_le_one : ∀ e ∈ E, x e ≤ 1
  /-- `f_P ≥ 0`. -/
  f_nonneg : ∀ uv ∈ E, ∀ z ∈ mids E uv.1 uv.2, 0 ≤ f uv z

namespace IsLP4Feasible

variable {E : Finset (V × V)} {r : ℕ} {x : V × V → ℝ} {f : V × V → V → ℝ}

/-- Capacity, per path: `f_{(u,z,v)} ≤ x_{(u,z)}`. -/
lemma flow_le_left (h : IsLP4Feasible E r x f) {uv : V × V} (huv : uv ∈ E) {z : V}
    (hz : z ∈ mids E uv.1 uv.2) : f uv z ≤ x (uv.1, z) := by
  refine le_trans ?_ (h.capacity uv huv _ (mem_mids.mp hz).1)
  refine Finset.single_le_sum (f := fun z => f uv z) (fun z hz' => h.f_nonneg uv huv z ?_) ?_
  · exact (Finset.mem_filter.mp hz').1
  · exact Finset.mem_filter.mpr ⟨hz, Or.inl rfl⟩

/-- Capacity, per path: `f_{(u,z,v)} ≤ x_{(z,v)}`. -/
lemma flow_le_right (h : IsLP4Feasible E r x f) {uv : V × V} (huv : uv ∈ E) {z : V}
    (hz : z ∈ mids E uv.1 uv.2) : f uv z ≤ x (z, uv.2) := by
  refine le_trans ?_ (h.capacity uv huv _ (mem_mids.mp hz).2)
  refine Finset.single_le_sum (f := fun z => f uv z) (fun z hz' => h.f_nonneg uv huv z ?_) ?_
  · exact (Finset.mem_filter.mp hz').1
  · exact Finset.mem_filter.mpr ⟨hz, Or.inr rfl⟩

end IsLP4Feasible

/-- `H` *satisfies* the arc `(u, v)` (proof of Theorem 3.3): `(u, v) ∈ H` or `H` contains at least
`r + 1` length-2 paths from `u` to `v`. By Lemma 3.1, `H ⊆ E` is an `r`-fault-tolerant 2-spanner iff
it satisfies every arc of `E`. -/
def Satisfies (H : Finset (V × V)) (r : ℕ) (uv : V × V) : Prop :=
  uv ∈ H ∨ r + 1 ≤ #(mids H uv.1 uv.2)

/-- **Algorithm 1** (rounding): with thresholds `T v`, keep the arc `(u, v)` iff
`min {T_u, T_v} ≤ α · x_{(u,v)}`. -/
noncomputable def roundE (E : Finset (V × V)) (x : V × V → ℝ) (α : ℝ) (T : V → ℝ) : Finset (V × V) :=
  E.filter fun e => min (T e.1) (T e.2) ≤ α * x e

end DinitzKrauthgamer
