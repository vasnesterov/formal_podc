import Papers.PODC2017.MaxISLocalRatio.Basic

/-!
# Parallel weight reductions on an independent set (Section 2.1, Lemma 2.2)

Let `U` be an independent set. Every `u ∈ U` reduces its weight `w(u)` from every vertex of its
**closed** neighbourhood `N[u]` (including `u` itself, whose weight becomes `0`):

* residual weights `w₂(v) = ∑_{u ∈ U ∩ N[v]} w(u)` (`red G U w`),
* reduced weights `w₁ = w - w₂`.

From a solution `x` for the reduced graph we get `x' = x ∪ {u ∈ U | N(u) ∩ x = ∅}` (`extend G U x`,
equation (1) of the paper). Lemma 2.2: if `x` is `r`-approximate for `w₁` then `x'` is
`r`-approximate for `w₁` and for `w₂`, hence (Theorem 2.1) for `w`.

The approximation factor comes from a *local independence bound* (`LocalBound G U r`): every
independent set meets every `N[u]`, `u ∈ U`, in at most `r` vertices. The paper uses
`r = Δ` (`localBound_of_degree_le`, needs `Δ ≥ 1`) and, for matchings in Section 2.4, `r = 2`
on the line graph (see `Matching.lean`).

The paper writes `N(v)` for the closed neighbourhood here (`w₂[u] = w[u]` for `u ∈ U` and
"at most `|N(u)| - 1`" only make sense for `N[u]`); see `differencies.md`.
-/

set_option linter.unusedSectionVars false

namespace Podc.MaxISLocalRatio

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The closed neighbourhood `N[u] = {u} ∪ N(u)`. -/
def cl (u : V) : Finset V := insert u (G.neighborFinset u)

/-- Residual weights of a parallel reduction step on `U`: `w₂(v) = ∑_{u ∈ U ∩ N[v]} w(u)`. -/
def red (U : Finset V) (w : V → ℝ) (v : V) : ℝ := ∑ u ∈ U with v ∈ cl G u, w u

/-- Equation (1): `x' = x ∪ {u ∈ U | no neighbour of u is in x}`. -/
def extend (U x : Finset V) : Finset V := x ∪ U.filter fun u => ∀ v ∈ x, ¬ G.Adj u v

/-- Every independent set meets the closed neighbourhood of every `u ∈ U` in at most `r` vertices. -/
def LocalBound (U : Finset V) (r : ℝ) : Prop :=
  ∀ u ∈ U, ∀ T : Finset V, G.IsIndepSet (T : Set V) → (#(T ∩ cl G u) : ℝ) ≤ r

variable {G}

theorem mem_cl {u v : V} : v ∈ cl G u ↔ v = u ∨ G.Adj u v := by
  simp [cl]

theorem self_mem_cl (u : V) : u ∈ cl G u := by simp [cl]

theorem mem_cl_comm {u v : V} : v ∈ cl G u ↔ u ∈ cl G v := by
  simp only [mem_cl]
  constructor <;> rintro (h | h) <;> first | exact Or.inl h.symm | exact Or.inr h.symm

/-- For `u` in the independent set `U`, `w₂(u) = w(u)` (so `w₁(u) = 0`). -/
theorem red_of_mem {U : Finset V} (hU : G.IsIndepSet (U : Set V)) (w : V → ℝ) {u : V}
    (hu : u ∈ U) : red G U w u = w u := by
  unfold red
  rw [show U.filter (fun u' => u ∈ cl G u') = {u} from ?_, sum_singleton]
  ext u'
  simp only [mem_filter, mem_singleton, mem_cl]
  constructor
  · rintro ⟨hu', h | h⟩
    · exact h.symm
    · by_contra hne
      exact hU (mem_coe.2 hu') (mem_coe.2 hu) hne h
  · rintro rfl; exact ⟨hu, Or.inl rfl⟩

theorem red_nonneg {U : Finset V} {w : V → ℝ} (hw : ∀ u ∈ U, 0 ≤ w u) (v : V) :
    0 ≤ red G U w v :=
  sum_nonneg fun u hu => hw u (mem_filter.1 hu).1

theorem red_of_notMem {U : Finset V} {w : V → ℝ} {v : V} (hv : ∀ u ∈ U, v ∉ cl G u) :
    red G U w v = 0 := by
  unfold red
  rw [filter_false_of_mem hv, sum_empty]

/-- Double counting: `w₂(T) = ∑_{u ∈ U} |T ∩ N[u]| · w(u)`. -/
theorem wt_red (U : Finset V) (w : V → ℝ) (T : Finset V) :
    wt (red G U w) T = ∑ u ∈ U, (#(T ∩ cl G u) : ℝ) * w u := by
  unfold wt red
  rw [sum_comm' (t' := U) (s' := fun u => T ∩ cl G u)]
  · refine sum_congr rfl fun u _ => ?_
    rw [sum_const, nsmul_eq_mul]
  · intro v u
    simp only [mem_filter, mem_inter]
    tauto

theorem wt_union_of_zero {f : V → ℝ} {x A : Finset V} (hA : ∀ v ∈ A, f v = 0) :
    wt f (x ∪ A) = wt f x := by
  rw [← union_sdiff_self_eq_union, wt, sum_union disjoint_sdiff,
    sum_eq_zero fun v hv => hA v (mem_sdiff.1 hv).1, add_zero, wt]

/-- `x'` is independent. -/
theorem extend_indep {U x : Finset V} (hU : G.IsIndepSet (U : Set V))
    (hx : G.IsIndepSet (x : Set V)) : G.IsIndepSet (extend G U x : Set V) := by
  intro a ha b hb hab hadj
  simp only [extend, coe_union, coe_filter, Set.mem_union, mem_coe, Set.mem_ofPred_eq] at ha hb
  rcases ha with ha | ⟨haU, ha⟩ <;> rcases hb with hb | ⟨hbU, hb⟩
  · exact hx ha hb hab hadj
  · exact hb a ha hadj.symm
  · exact ha b hb hadj
  · exact hU haU hbU hab hadj

theorem subset_extend (U x : Finset V) : x ⊆ extend G U x := subset_union_left

theorem extend_subset {U x : Finset V} : extend G U x ⊆ x ∪ U :=
  union_subset_union_right (filter_subset _ _)

/-- `x'` meets the closed neighbourhood of every `u ∈ U`. -/
theorem extend_meets {U x : Finset V} {u : V} (hu : u ∈ U) : (extend G U x ∩ cl G u).Nonempty := by
  by_cases h : ∀ v ∈ x, ¬ G.Adj u v
  · exact ⟨u, mem_inter.2 ⟨mem_union_right _ (mem_filter.2 ⟨hu, h⟩), self_mem_cl u⟩⟩
  · push Not at h
    obtain ⟨v, hv, huv⟩ := h
    exact ⟨v, mem_inter.2 ⟨mem_union_left _ hv, mem_cl.2 (Or.inr huv)⟩⟩

-- CSLib candidate
/-- **Lemma 2.2.** Let `U` be an independent set with nonnegative weights, and assume every
independent set meets each `N[u]`, `u ∈ U`, in at most `r` vertices. If `x` is an `r`-approximate
solution for the reduced weights `w₁ = w - w₂`, then `x'` is `r`-approximate both for the reduced
weights `w₁` and for the residual weights `w₂`. -/
theorem lemma_2_2 {U x : Finset V} {w : V → ℝ} {r : ℝ} (hU : G.IsIndepSet (U : Set V))
    (hw : ∀ u ∈ U, 0 ≤ w u) (hr : 0 ≤ r) (hloc : LocalBound G U r)
    (hx : IsApprox G r (w - red G U w) x) :
    IsApprox G r (w - red G U w) (extend G U x) ∧ IsApprox G r (red G U w) (extend G U x) := by
  have hind := extend_indep hU hx.1
  refine ⟨⟨hind, fun T hT => ?_⟩, ⟨hind, fun T hT => ?_⟩⟩
  · -- reduced graph: the added vertices have reduced weight `0`
    have : wt (w - red G U w) (extend G U x) = wt (w - red G U w) x :=
      wt_union_of_zero fun v hv => by
        simp [red_of_mem hU w (mem_filter.1 hv).1]
    rw [this]
    exact hx.2 T hT
  · -- residual graph: `w₂(T) ≤ r ∑_{u ∈ U} w(u) ≤ r w₂(x')`
    rw [wt_red, wt_red, mul_sum]
    refine sum_le_sum fun u hu => ?_
    have h1 : (#(T ∩ cl G u) : ℝ) ≤ r := hloc u hu T hT
    have h2 : (1 : ℝ) ≤ #(extend G U x ∩ cl G u) := by
      exact_mod_cast (extend_meets hu).card_pos
    have hwu := hw u hu
    calc (#(T ∩ cl G u) : ℝ) * w u ≤ r * w u := mul_le_mul_of_nonneg_right h1 hwu
      _ = r * (1 * w u) := by ring
      _ ≤ r * (#(extend G U x ∩ cl G u) * w u) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h2 hwu) hr

/-- Lemma 2.2 combined with Theorem 2.1: `x'` is `r`-approximate for the original weights `w`. -/
theorem lemma_2_2_total {U x : Finset V} {w : V → ℝ} {r : ℝ} (hU : G.IsIndepSet (U : Set V))
    (hw : ∀ u ∈ U, 0 ≤ w u) (hr : 0 ≤ r) (hloc : LocalBound G U r)
    (hx : IsApprox G r (w - red G U w) x) : IsApprox G r w (extend G U x) := by
  have h := lemma_2_2 hU hw hr hloc hx
  simpa using isApprox_add h.1 h.2

/-- An independent set meets `N[u]` in at most `max 1 (deg u)` vertices: in `{u}` if it contains
`u`, and in a subset of `N(u)` otherwise. -/
theorem card_inter_cl_le {T : Finset V} (hT : G.IsIndepSet (T : Set V)) (u : V) :
    #(T ∩ cl G u) ≤ max 1 (G.degree u) := by
  by_cases hu : u ∈ T
  · refine le_max_of_le_left (card_le_one.2 fun a ha b hb => ?_)
    have key : ∀ a ∈ T ∩ cl G u, a = u := by
      intro a ha
      obtain ⟨haT, hacl⟩ := mem_inter.1 ha
      rcases mem_cl.1 hacl with h | h
      · exact h
      · by_contra hne
        exact hT (mem_coe.2 hu) (mem_coe.2 haT) (Ne.symm hne) h
    rw [key a ha, key b hb]
  · refine le_max_of_le_right ?_
    rw [← G.card_neighborFinset_eq_degree]
    refine card_le_card fun a ha => ?_
    obtain ⟨haT, hacl⟩ := mem_inter.1 ha
    rcases mem_cl.1 hacl with h | h
    · exact absurd (h ▸ haT) hu
    · exact (G.mem_neighborFinset u a).2 h

/-- The bound used for Lemma 2.2 with `r = Δ`: if all degrees are at most `Δ` and `Δ ≥ 1`, every
independent set meets every closed neighbourhood in at most `Δ` vertices. (For `Δ = 0` the
bound is `1`, not `0`; see `differencies.md`.) -/
theorem localBound_of_degree_le {Δ : ℕ} (hΔ : ∀ v, G.degree v ≤ Δ) (h1 : 1 ≤ Δ) (U : Finset V) :
    LocalBound G U Δ := fun u _ T hT => by
  exact_mod_cast (card_inter_cl_le hT u).trans (max_le h1 (hΔ u))

end Podc.MaxISLocalRatio
