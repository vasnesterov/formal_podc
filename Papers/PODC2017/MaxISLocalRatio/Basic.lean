import Mathlib

/-!
# Weighted independent sets and the local-ratio theorem (Section 2.1, Theorem 2.1)

Bar-Yehuda, Censor-Hillel, Ghaffari, Schwartzman, *Distributed Approximation of Maximum Independent
Set and Maximum Matching*, PODC 2017 (arXiv 1708.00276).

* `wt w S` — the weight `∑_{v ∈ S} w(v)` of a finite set of vertices.
* `IsApprox G r w S` — `S` is an independent set of `G` and `w(T) ≤ r · w(S)` for every independent
  set `T`, i.e. `S` is an `r`-approximate maximum-weight independent set. Weights may be negative
  (the paper stresses that Theorem 2.1 is used with negative weights in the reduced graph).
* `theorem_2_1` — the local-ratio theorem for maximization ([BYBFR04, Theorem 9]) for an arbitrary
  set of feasible vectors in `ℝⁿ`, and `isApprox_add` — its instance for independent sets.
-/

set_option linter.unusedSectionVars false

namespace Podc.MaxISLocalRatio

open Finset

section Vectors

variable {ι : Type*} [Fintype ι]

/-- `x` is an `r`-approximate solution of `max w·x` over the feasible set `C`:
`x ∈ C` and `w·y ≤ r (w·x)` for every `y ∈ C`. For `r > 0` this is the usual
"`w·x ≥ OPT / r`". -/
def IsApproxVec (C : Set (ι → ℝ)) (r : ℝ) (w x : ι → ℝ) : Prop :=
  x ∈ C ∧ ∀ y ∈ C, w ⬝ᵥ y ≤ r * (w ⬝ᵥ x)

-- CSLib candidate
/-- **Theorem 2.1** (local-ratio theorem for maximization problems, [BYBFR04, Thm. 9]).
If `w = w₁ + w₂` and a feasible `x` is `r`-approximate with respect to `w₁` and to `w₂`, then it is
`r`-approximate with respect to `w`. No sign condition on the weights is needed. -/
theorem theorem_2_1 {C : Set (ι → ℝ)} {r : ℝ} {w w₁ w₂ x : ι → ℝ} (hw : w = w₁ + w₂)
    (h₁ : IsApproxVec C r w₁ x) (h₂ : IsApproxVec C r w₂ x) : IsApproxVec C r w x := by
  refine ⟨h₁.1, fun y hy => ?_⟩
  subst hw
  simp only [add_dotProduct]
  have := h₁.2 y hy
  have := h₂.2 y hy
  linarith

end Vectors

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The weight `w(S) = ∑_{v ∈ S} w(v)` of a set of vertices. -/
def wt (w : V → ℝ) (S : Finset V) : ℝ := ∑ v ∈ S, w v

/-- The vertices of positive weight (the vertex set `V` of the current recursive call of
Algorithm 1, after lines 3–6 removed the nonpositive ones). -/
noncomputable def pos (w : V → ℝ) : Finset V := univ.filter fun v => 0 < w v

@[simp] theorem mem_pos {w : V → ℝ} {v : V} : v ∈ pos w ↔ 0 < w v := by simp [pos]

theorem wt_add (w₁ w₂ : V → ℝ) (S : Finset V) : wt (w₁ + w₂) S = wt w₁ S + wt w₂ S := by
  simp [wt, sum_add_distrib]

theorem wt_sub (w₁ w₂ : V → ℝ) (S : Finset V) : wt (w₁ - w₂) S = wt w₁ S - wt w₂ S := by
  simp [wt, sum_sub_distrib]

/-- `S` is an `r`-approximate maximum-weight independent set of `G` for the weights `w`: it is
independent and `w(T) ≤ r · w(S)` for every independent set `T`. -/
def IsApprox (G : SimpleGraph V) (r : ℝ) (w : V → ℝ) (S : Finset V) : Prop :=
  G.IsIndepSet (S : Set V) ∧ ∀ T : Finset V, G.IsIndepSet (T : Set V) → wt w T ≤ r * wt w S

/-- Theorem 2.1 for independent sets (the form used in the paper). -/
theorem isApprox_add {G : SimpleGraph V} {r : ℝ} {w₁ w₂ : V → ℝ} {S : Finset V}
    (h₁ : IsApprox G r w₁ S) (h₂ : IsApprox G r w₂ S) : IsApprox G r (w₁ + w₂) S := by
  refine ⟨h₁.1, fun T hT => ?_⟩
  rw [wt_add, wt_add]
  have := h₁.2 T hT
  have := h₂.2 T hT
  linarith

/-- The set form is the vector form for indicator vectors (bridge between `IsApprox` and
`IsApproxVec` with `C` = indicator vectors of independent sets). -/
theorem wt_eq_dotProduct (w : V → ℝ) (S : Finset V) :
    wt w S = w ⬝ᵥ (fun v => if v ∈ S then (1 : ℝ) else 0) := by
  simp [wt, dotProduct, Finset.sum_ite_mem, Finset.univ_inter]

end Podc.MaxISLocalRatio
