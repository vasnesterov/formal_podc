-- CSLib candidate: Cslib/Foundations/Combinatorics/SimpleGraph/WeightedSpanner.lean
import Cslib.Foundations.Combinatorics.SimpleGraph.WeightedSpanner
import Mathlib.Basic.Real.ENatENNReal
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Combinatorics.SimpleGraph.Walk.Counting
import Mathlib.Data.Set.Finite.Lemmas

/-!
# Weighted distances and spanners with a real stretch

Complements to CSLib's `WeightedSpanner.lean` (`Walk.wlength`, `wdist`, `IsWeightedVFTSpanner`,
`IsWeightedEFTSpanner`, all with a natural stretch `t : ℕ`).

## Weighted distances

* `wdist_one`: with unit weights the weighted distance is the unweighted one,
  `G.wdist (fun _ => 1) u v = G.edist u v` (via the coercion `ℕ∞ → ℝ≥0∞`).
* `wdist_lt_top_iff`: `wdist` is finite exactly between connected vertices; `wdist_self`.
* `exists_isPath_wlength_eq`: on a finite graph, `wdist` is attained by a path.
* `wdist_smul`: scaling the weights by `t ≠ 0` scales distances by `t`.
* `wdist_le_wdist_of_forall_adj`: comparison of two weighted graphs edge by edge; this is the
  local criterion for spanners in its most general form.
* `wdistS`: `wdist` as a function of an unordered pair.

## Spanners with a real stretch

* `IsWSpanner G H w t`: `H ≤ G` and `d_H(u, v) ≤ t · d_G(u, v)` for a real stretch `t : ℝ≥0`;
  `isWSpanner_of_adj` (local criterion).
* Bridges: natural stretches are the casts `(t : ℝ≥0)` (`isWSpanner_natCast_iff`); unit weights
  give CSLib's unweighted notions (`isWeightedVFTSpanner_one_iff`, `isWeightedEFTSpanner_one_iff`).
-/

open Finset
open scoped ENNReal NNReal

namespace SimpleGraph

variable {V : Type*} {G H : SimpleGraph V} {w : Sym2 V → ℝ≥0} {u v : V}

/-! ### Walk weights -/

namespace Walk

/-- The weight of a walk is finite. -/
theorem wlength_lt_top (p : G.Walk u v) : p.wlength w < ⊤ := by
  induction p with
  | nil => simp
  | cons h q ih => rw [wlength_cons]; exact ENNReal.add_lt_top.mpr ⟨ENNReal.coe_lt_top, ih⟩

/-- Every edge of a walk weighs at most the walk. -/
theorem le_wlength_of_mem_edges (p : G.Walk u v) {e : Sym2 V} (he : e ∈ p.edges) :
    (w e : ℝ≥0∞) ≤ p.wlength w :=
  List.single_le_sum (fun _ _ => zero_le) _ (List.mem_map_of_mem he)

/-- With unit weights, the weight of a walk is its length. -/
@[simp] theorem wlength_one (p : G.Walk u v) : p.wlength (fun _ => 1) = p.length := by
  induction p with
  | nil => simp
  | cons h q ih => rw [wlength_cons, ih, length_cons]; push_cast; ring

/-- Scaling the weights scales the weight of a walk. -/
theorem wlength_smul (t : ℝ≥0) (p : G.Walk u v) : p.wlength (t • w) = t * p.wlength w := by
  simp only [wlength, Pi.smul_apply, smul_eq_mul, ENNReal.coe_mul, List.sum_map_mul_left]

/-- Bypassing a walk does not increase its weight (weights are nonnegative). -/
theorem wlength_bypass_le [DecidableEq V] (p : G.Walk u v) : p.bypass.wlength w ≤ p.wlength w := by
  obtain ⟨l, hl, hsub⟩ := List.subperm_of_subset p.bypass_isPath.isTrail.edges_nodup
    p.edges_bypass_subset_edges
  rw [wlength, wlength, ← (hl.map _).sum_eq]
  exact (hsub.map _).sum_le_sum fun _ _ => zero_le

end Walk

/-! ### Weighted distances -/

/-- The weighted distance from a vertex to itself is `0`. -/
@[simp] theorem wdist_self : G.wdist w u u = 0 :=
  le_antisymm ((wdist_le (Walk.nil : G.Walk u u)).trans (by simp)) zero_le

/-- Disconnected vertices are at weighted distance `⊤`. -/
theorem wdist_eq_top_of_not_reachable (h : ¬ G.Reachable u v) : G.wdist w u v = ⊤ := by
  have : IsEmpty (G.Walk u v) := ⟨fun p => h ⟨p⟩⟩
  simp [wdist]

/-- Connected vertices are at finite weighted distance. -/
theorem wdist_lt_top_of_reachable (h : G.Reachable u v) : G.wdist w u v < ⊤ :=
  (wdist_le h.some).trans_lt h.some.wlength_lt_top

/-- The weighted distance is finite exactly between connected vertices. -/
theorem wdist_lt_top_iff : G.wdist w u v < ⊤ ↔ G.Reachable u v :=
  ⟨fun h => by_contra fun hr => (wdist_eq_top_of_not_reachable hr ▸ h).ne rfl,
    wdist_lt_top_of_reachable⟩

/-- Vertices at finite weighted distance are connected. -/
theorem reachable_of_wdist_lt_top (h : G.wdist w u v < ⊤) : G.Reachable u v :=
  wdist_lt_top_iff.mp h

/-- **Unit weights.** With all weights `1`, the weighted distance is the unweighted distance. -/
theorem wdist_one : G.wdist (fun _ => 1) u v = G.edist u v := by
  by_cases hr : G.Reachable u v
  · obtain ⟨p, hp⟩ := hr.exists_walk_length_eq_edist
    refine le_antisymm ((wdist_le p).trans (by simp [← hp, ENat.toENNReal_coe])) ?_
    refine le_iInf fun q => ?_
    rw [Walk.wlength_one, ← ENat.toENNReal_coe, ENat.toENNReal_le]
    exact edist_le q
  · rw [wdist_eq_top_of_not_reachable hr, edist_eq_top_of_not_reachable hr, ENat.toENNReal_top]

/-- On a finite graph, the weighted distance between connected vertices is the weight of a path. -/
theorem exists_isPath_wlength_eq [Finite V] (h : G.Reachable u v) :
    ∃ p : G.Walk u v, p.IsPath ∧ p.wlength w = G.wdist w u v := by
  classical
  have := Fintype.ofFinite V
  set S : Set (G.Walk u v) := {p | p.IsPath ∧ p.length < Fintype.card V}
  have hne : S.Nonempty := ⟨h.some.bypass, h.some.bypass_isPath, h.some.bypass_isPath.length_lt⟩
  obtain ⟨p, hpS, hpmin⟩ := Set.exists_min_image S (fun p => p.wlength w) (Set.toFinite S) hne
  refine ⟨p, hpS.1, le_antisymm (le_iInf fun q => ?_) (wdist_le p)⟩
  exact (hpmin q.bypass ⟨q.bypass_isPath, q.bypass_isPath.length_lt⟩).trans q.wlength_bypass_le

/-- **Scaling.** Multiplying all weights by `t ≠ 0` multiplies all distances by `t`. -/
theorem wdist_smul {t : ℝ≥0} (ht : t ≠ 0) : G.wdist (t • w) u v = t * G.wdist w u v := by
  simp only [wdist, Walk.wlength_smul]
  rw [ENNReal.mul_iInf_of_ne (by exact_mod_cast ht) ENNReal.coe_ne_top]

/-- **Comparison along a walk.** If every edge `ab` of a walk `p` (of any graph) satisfies
`d_H^{w₁}(a, b) ≤ w₂(ab)`, then `d_H^{w₁}(u, v) ≤ w₂(p)`. -/
theorem wdist_le_wlength_of_forall_adj {K : SimpleGraph V} {w₁ w₂ : Sym2 V → ℝ≥0}
    (p : K.Walk u v) (h : ∀ a b, s(a, b) ∈ p.edges → H.wdist w₁ a b ≤ w₂ s(a, b)) :
    H.wdist w₁ u v ≤ p.wlength w₂ := by
  induction p with
  | nil => simp
  | @cons a b c hab q ih =>
    rw [Walk.wlength_cons]
    calc H.wdist w₁ a c ≤ H.wdist w₁ a b + H.wdist w₁ b c := wdist_triangle
      _ ≤ w₂ s(a, b) + q.wlength w₂ :=
        add_le_add (h a b (by simp)) (ih fun x y hxy => h x y (by simp [hxy]))

/-- **Local comparison of weighted graphs.** If every edge `ab` of `(K, w₂)` satisfies
`d_H^{w₁}(a, b) ≤ w₂(ab)`, then `d_H^{w₁} ≤ d_K^{w₂}` everywhere. -/
theorem wdist_le_wdist_of_forall_adj {K : SimpleGraph V} {w₁ w₂ : Sym2 V → ℝ≥0}
    (h : ∀ a b, K.Adj a b → H.wdist w₁ a b ≤ w₂ s(a, b)) : H.wdist w₁ u v ≤ K.wdist w₂ u v :=
  le_iInf fun p => wdist_le_wlength_of_forall_adj p fun a b hab => h a b (p.adj_of_mem_edges hab)

/-- The weighted distance as a function of an unordered pair. -/
noncomputable def wdistS (G : SimpleGraph V) (w : Sym2 V → ℝ≥0) (e : Sym2 V) : ℝ≥0∞ :=
  Sym2.lift ⟨fun u v => G.wdist w u v, fun _ _ => wdist_comm⟩ e

/-- `wdistS` on `s(u, v)` is `wdist` between `u` and `v`. -/
@[simp] theorem wdistS_mk (u v : V) : G.wdistS w s(u, v) = G.wdist w u v := rfl

/-! ### Spanners with a real stretch -/

/-- `H` is a `t`-spanner of the weighted graph `(G, w)`, for a real stretch `t`:
`H ≤ G` and `d_H(u, v) ≤ t · d_G(u, v)` for all `u, v`. -/
def IsWSpanner (G H : SimpleGraph V) (w : Sym2 V → ℝ≥0) (t : ℝ≥0) : Prop :=
  H ≤ G ∧ ∀ u v, H.wdist w u v ≤ t * G.wdist w u v

/-- A `t`-spanner stretches every edge of `G` by at most `t`. -/
theorem IsWSpanner.wdist_le_of_adj {t : ℝ≥0} (h : IsWSpanner G H w t) {x y : V}
    (hxy : G.Adj x y) : H.wdist w x y ≤ t * w s(x, y) :=
  (h.2 x y).trans (mul_le_mul_right (SimpleGraph.wdist_le_of_adj hxy) _)

/-- **Local criterion**: it suffices to check the stretch on the edges of `G`. -/
theorem isWSpanner_of_adj {t : ℝ≥0} (ht : 1 ≤ t) (hHG : H ≤ G)
    (h : ∀ x y, G.Adj x y → H.wdist w x y ≤ t * w s(x, y)) : IsWSpanner G H w t := by
  have ht0 : t ≠ 0 := (lt_of_lt_of_le one_pos ht).ne'
  refine ⟨hHG, fun u v => ?_⟩
  rw [← wdist_smul ht0]
  exact wdist_le_wdist_of_forall_adj fun a b hab => by simpa using h a b hab

/-- Every graph is a `t`-spanner of itself, for `t ≥ 1`. -/
theorem isWSpanner_refl {t : ℝ≥0} (ht : 1 ≤ t) : IsWSpanner G G w t :=
  ⟨le_rfl, fun _ _ => le_mul_of_one_le_left zero_le (by exact_mod_cast ht)⟩

/-- A spanner preserves connectivity. -/
theorem IsWSpanner.reachable {t : ℝ≥0} (hH : IsWSpanner G H w t) (h : G.Reachable u v) :
    H.Reachable u v :=
  reachable_of_wdist_lt_top ((hH.2 u v).trans_lt
    (ENNReal.mul_lt_top ENNReal.coe_lt_top (wdist_lt_top_of_reachable h)))

/-! ### Bridges: natural stretches and unit weights -/

/-- A natural stretch `t` is the real stretch `(t : ℝ≥0)`: a `t`-spanner is a `0`-fault-tolerant
`t`-spanner. -/
theorem isWSpanner_natCast_iff {t : ℕ} :
    IsWSpanner G H w t ↔ IsWeightedVFTSpanner G H w 0 t := by
  simp only [IsWSpanner, IsWeightedVFTSpanner, ENNReal.coe_natCast, Nat.le_zero, card_eq_zero]
  refine and_congr_right fun _ => ⟨fun h F hF u v _ _ => by simpa [hF] using h u v,
    fun h u v => by simpa using h ∅ rfl u v (by simp) (by simp)⟩

private theorem toENNReal_le_natCast_mul_iff {a b : ℕ∞} {t : ℕ} :
    (a : ℝ≥0∞) ≤ t * b ↔ a ≤ t * b := by
  rw [← ENat.toENNReal_coe t, ← ENat.toENNReal_mul, ENat.toENNReal_le]

/-- With unit weights, CSLib's weighted VFT spanners are its unweighted VFT spanners. -/
theorem isWeightedVFTSpanner_one_iff {f t : ℕ} :
    IsWeightedVFTSpanner G H (fun _ => 1) f t ↔ IsVFTSpanner G H f t := by
  simp only [IsWeightedVFTSpanner, IsVFTSpanner, wdist_one, toENNReal_le_natCast_mul_iff]

/-- With unit weights, CSLib's weighted EFT spanners are its unweighted EFT spanners. -/
theorem isWeightedEFTSpanner_one_iff {f t : ℕ} :
    IsWeightedEFTSpanner G H (fun _ => 1) f t ↔ IsEFTSpanner G H f t := by
  simp only [IsWeightedEFTSpanner, IsEFTSpanner, wdist_one, toENNReal_le_natCast_mul_iff]

end SimpleGraph
