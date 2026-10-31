import Cslib.Foundations.Combinatorics.SimpleGraph.Ball
import Mathlib

-- CSLib candidate: Cslib/Foundations/Combinatorics/SimpleGraph/BallCard.lean

/-!
# Size of balls in graphs of bounded degree

In a graph of maximum degree `≤ Δ`, the closed ball of radius `ρ` has at most
`1 + Δ + Δ (Δ - 1) + ⋯ + Δ (Δ - 1) ^ (ρ - 1) = 1 + Δ * ∑_{i < ρ} (Δ - 1) ^ i` vertices
(the number of vertices of the radius-`ρ` ball of the infinite `Δ`-regular tree). The sharp factor
`Δ - 1` (rather than `Δ`) comes from non-backtracking: a vertex at distance `i ≥ 1` from the center
has a neighbour at distance `i - 1`, which is not at distance `i + 1`.

## Main definitions

* `SimpleGraph.sphereFinset G c i`: the vertices at extended distance exactly `i` from `c`, as a
  `Finset` (for a locally finite graph).

## Main results

* `mem_sphereFinset`, `coe_sphereFinset`: `sphereFinset G c i = {v | G.edist c v = i}`.
* `card_sphereFinset_succ_le`: `|S(i + 1)| ≤ Δ (Δ - 1) ^ i`.
* `finite_closedBall`: closed balls of finite radius in locally finite graphs are finite.
* `ncard_closedBall_le`: `|B(c, ρ)| ≤ 1 + Δ * ∑_{i < ρ} (Δ - 1) ^ i` for locally finite graphs of
  maximum degree `≤ Δ`; `card_filter_edist_le_le` is the `Finset` version for finite graphs.
* `one_add_mul_geom_sum_lt`: for `Δ ≥ 3`, `1 + Δ * ∑_{i < ρ} (Δ - 1) ^ i < 3 * (Δ - 1) ^ ρ`, the
  bound `1 + Δ/(Δ-2)·((Δ-1)^ρ - 1) < 3(Δ-1)^ρ` used in Floréen, Kaski, Polishchuk, Suomela,
  *Almost stable matchings in constant time* (PODC 2010), §6.3.
-/

namespace SimpleGraph

open Finset

variable {V : Type*} (G : SimpleGraph V) [G.LocallyFinite] [DecidableEq V]

/-- The sphere of radius `i` around `c`: the vertices at extended distance exactly `i` from `c`,
as a `Finset`. It is built recursively (a vertex at distance `i + 1` is a neighbour of a vertex at
distance `i`), so only local finiteness of `G` is needed. -/
noncomputable def sphereFinset (c : V) : ℕ → Finset V
  | 0 => {c}
  | i + 1 => by
    classical
    exact (sphereFinset c i).biUnion fun u =>
      (G.neighborFinset u).filter fun v => G.edist c v = (i + 1 : ℕ)

variable {G}

/-- Membership in `sphereFinset`: being at distance exactly `i` from the center. -/
@[simp] theorem mem_sphereFinset {c v : V} {i : ℕ} :
    v ∈ G.sphereFinset c i ↔ G.edist c v = i := by
  induction i generalizing v with
  | zero => rw [sphereFinset, mem_singleton, Nat.cast_zero, edist_eq_zero_iff, eq_comm]
  | succ i ih =>
    classical
    simp only [sphereFinset, mem_biUnion, mem_filter, mem_neighborFinset, ih]
    constructor
    · rintro ⟨_, _, _, h⟩; convert h
    · intro h
      obtain ⟨u, hu, hadj⟩ := exists_adj_of_edist_eq_succ h
      exact ⟨u, hu, hadj, by convert h⟩

/-- `sphereFinset G c i` as a set. -/
theorem coe_sphereFinset (c : V) (i : ℕ) :
    (G.sphereFinset c i : Set V) = {v | G.edist c v = i} := by
  ext v; simp

/-- The sphere of radius `0` is the center. -/
@[simp] theorem sphereFinset_zero (c : V) : G.sphereFinset c 0 = {c} := rfl

/-- The sphere of radius `1` has at most `deg c` vertices. -/
theorem card_sphereFinset_one_le (c : V) : (G.sphereFinset c 1).card ≤ G.degree c := by
  rw [← card_neighborFinset_eq_degree]
  refine card_le_card fun v hv => ?_
  rw [mem_sphereFinset] at hv
  exact (mem_neighborFinset _ _ _).2 (edist_eq_one_iff_adj.1 (by exact_mod_cast hv))

/-- Non-backtracking growth: if all degrees are `≤ Δ`, then for `i ≥ 1` the sphere of radius
`i + 1` has at most `(Δ - 1)` times as many vertices as the sphere of radius `i`. -/
theorem card_sphereFinset_succ_succ_le {Δ : ℕ} (hdeg : ∀ v, G.degree v ≤ Δ) (c : V) (i : ℕ) :
    (G.sphereFinset c (i + 2)).card ≤ (Δ - 1) * (G.sphereFinset c (i + 1)).card := by
  classical
  have hsub : G.sphereFinset c (i + 2) ⊆ (G.sphereFinset c (i + 1)).biUnion fun u =>
      (G.neighborFinset u).filter fun v => G.edist c v = (i + 2 : ℕ) := by
    intro v hv
    rw [mem_sphereFinset] at hv
    obtain ⟨u, hu, hadj⟩ := exists_adj_of_edist_eq_succ hv
    simp only [mem_biUnion, mem_filter, mem_neighborFinset, mem_sphereFinset]
    exact ⟨u, hu, hadj, hv⟩
  refine (card_le_card hsub).trans (card_biUnion_le.trans ?_)
  rw [mul_comm, ← smul_eq_mul]
  refine sum_le_card_nsmul _ _ _ fun u hu => ?_
  rw [mem_sphereFinset] at hu
  obtain ⟨w, hw, hadj⟩ := exists_adj_of_edist_eq_succ hu
  have hlt : ((G.neighborFinset u).filter fun v => G.edist c v = (i + 2 : ℕ)).card <
      (G.neighborFinset u).card := by
    refine card_lt_card (filter_ssubset.2 ⟨w, (mem_neighborFinset _ _ _).2 hadj.symm, ?_⟩)
    rw [hw]; exact_mod_cast (by omega : i ≠ i + 2)
  have := hdeg u
  rw [← card_neighborFinset_eq_degree] at this
  omega

/-- If all degrees are `≤ Δ`, the sphere of radius `i + 1` has at most `Δ (Δ - 1) ^ i`
vertices. -/
theorem card_sphereFinset_succ_le {Δ : ℕ} (hdeg : ∀ v, G.degree v ≤ Δ) (c : V) (i : ℕ) :
    (G.sphereFinset c (i + 1)).card ≤ Δ * (Δ - 1) ^ i := by
  induction i with
  | zero => simpa using (card_sphereFinset_one_le c).trans (hdeg c)
  | succ i ih =>
    calc (G.sphereFinset c (i + 2)).card ≤ (Δ - 1) * (G.sphereFinset c (i + 1)).card :=
          card_sphereFinset_succ_succ_le hdeg c i
      _ ≤ (Δ - 1) * (Δ * (Δ - 1) ^ i) := Nat.mul_le_mul_left _ ih
      _ = Δ * (Δ - 1) ^ (i + 1) := by ring

/-- The closed ball of radius `ρ` is the union of the spheres of radii `0, …, ρ`. -/
theorem closedBall_eq_coe_biUnion_sphereFinset (c : V) (ρ : ℕ) :
    G.closedBall c ρ = ↑((range (ρ + 1)).biUnion (G.sphereFinset c)) := by
  ext v
  simp only [mem_closedBall', coe_biUnion, coe_range, Set.mem_Iio, Finset.mem_coe,
    mem_sphereFinset, Set.mem_iUnion, exists_prop]
  constructor
  · intro h
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 (edist_ne_top_of_le_natCast h)
    rw [← hn] at h
    have hn' : n ≤ ρ := by exact_mod_cast h
    exact ⟨n, by omega, hn.symm⟩
  · rintro ⟨n, hn, h⟩
    rw [h]; exact_mod_cast Nat.le_of_lt_succ hn

/-- In a locally finite graph, closed balls of finite radius are finite. -/
theorem finite_closedBall (c : V) (ρ : ℕ) : (G.closedBall c ρ).Finite := by
  rw [closedBall_eq_coe_biUnion_sphereFinset]; exact Finset.finite_toSet _

/-- **Ball size in bounded-degree graphs.** In a locally finite graph with all degrees `≤ Δ`, the
closed ball of radius `ρ` has at most `1 + Δ * ∑_{i < ρ} (Δ - 1) ^ i` vertices. -/
theorem ncard_closedBall_le {Δ : ℕ} (hdeg : ∀ v, G.degree v ≤ Δ) (c : V) (ρ : ℕ) :
    (G.closedBall c ρ).ncard ≤ 1 + Δ * ∑ i ∈ range ρ, (Δ - 1) ^ i := by
  rw [closedBall_eq_coe_biUnion_sphereFinset, Set.ncard_coe_finset]
  refine card_biUnion_le.trans ?_
  rw [sum_range_succ', mul_sum, add_comm]
  simp only [sphereFinset_zero, card_singleton]
  exact Nat.add_le_add_left (sum_le_sum fun i _ => card_sphereFinset_succ_le hdeg c i) 1

/-- `Finset` version of `ncard_closedBall_le` for finite graphs: at most
`1 + Δ * ∑_{i < ρ} (Δ - 1) ^ i` vertices lie within distance `ρ` of `c`. -/
theorem card_filter_edist_le_le {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    [DecidableRel G.Adj] {Δ : ℕ} (hdeg : ∀ v, G.degree v ≤ Δ) (c : V) (ρ : ℕ)
    [DecidablePred fun v => G.edist c v ≤ ρ] :
    (univ.filter fun v => G.edist c v ≤ ρ).card ≤ 1 + Δ * ∑ i ∈ range ρ, (Δ - 1) ^ i := by
  have h : ((univ.filter fun v => G.edist c v ≤ ρ : Finset V) : Set V) = G.closedBall c ρ := by
    ext v; simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq, mem_closedBall']
  rw [← Set.ncard_coe_finset, h]
  exact ncard_closedBall_le hdeg c ρ

/-- For `Δ ≥ 3`, `1 + Δ * ∑_{i < ρ} (Δ - 1) ^ i < 3 * (Δ - 1) ^ ρ` (for every `ρ`, including
`ρ = 0`). This is the estimate `1 + Δ/(Δ-2) · ((Δ-1)^ρ - 1) < 3 (Δ-1)^ρ` of Floréen et al.
(PODC 2010), §6.3, written without division. -/
theorem one_add_mul_geom_sum_lt {Δ : ℕ} (hΔ : 3 ≤ Δ) (ρ : ℕ) :
    1 + Δ * ∑ i ∈ range ρ, (Δ - 1) ^ i < 3 * (Δ - 1) ^ ρ := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hΔ
  have hg := geom_sum_mul_add (k + 1) ρ
  have h1 : 3 + k - 1 = k + 1 + 1 := by omega
  rw [h1, ← hg]
  set S := ∑ i ∈ range ρ, (k + 1 + 1) ^ i
  nlinarith

/-- Combined bound: for `Δ ≥ 3`, a closed ball of radius `ρ` in a locally finite graph of maximum
degree `≤ Δ` has fewer than `3 (Δ - 1) ^ ρ` vertices. -/
theorem ncard_closedBall_lt {Δ : ℕ} (hΔ : 3 ≤ Δ) (hdeg : ∀ v, G.degree v ≤ Δ) (c : V) (ρ : ℕ) :
    (G.closedBall c ρ).ncard < 3 * (Δ - 1) ^ ρ :=
  (ncard_closedBall_le hdeg c ρ).trans_lt (one_add_mul_geom_sum_lt hΔ ρ)

end SimpleGraph
