import Cslib.Foundations.Combinatorics.SimpleGraph.Ball
import Mathlib.Combinatorics.SimpleGraph.Prod

-- CSLib candidate: Cslib/Foundations/Combinatorics/SimpleGraph/Ball.lean (append to the existing file)

/-!
# Distance bounds from potentials; closed balls in box products

A potential `f : V → ℕ` that grows by at most one along every edge ("1-Lipschitz") is a certificate
for lower bounds on distances: `f b ≤ f a + d(a, b)`. A function that is constant along edges is
constant on connected pairs (the `0`-Lipschitz case). Closed balls in a box product `G₁ □ G₂`
are controlled by Mathlib's `SimpleGraph.edist_boxProd`.

## Main statements

* `SimpleGraph.Walk.le_add_length_of_lipschitz`, `SimpleGraph.le_add_edist_of_lipschitz`,
  `SimpleGraph.Reachable.le_add_dist_of_lipschitz`, `SimpleGraph.le_add_of_edist_le_of_lipschitz`:
  `f b ≤ f a + d(a, b)` for a potential growing by at most one along each edge.
* `SimpleGraph.Walk.apply_eq_of_forall_adj`, `SimpleGraph.Reachable.apply_eq_of_forall_adj`:
  a function constant along edges is constant along walks.
* `SimpleGraph.closedBall_prod_subset_closedBall_boxProd`,
  `SimpleGraph.fst_mem_closedBall_of_mem_boxProd`, `SimpleGraph.snd_mem_closedBall_of_mem_boxProd`:
  closed balls of `G₁ □ G₂` versus products of closed balls of the factors.
* `SimpleGraph.closedBall_eq_univ_of_preconnected`: in a preconnected graph on `n` vertices the
  closed ball of radius `n - 1` is everything; `SimpleGraph.closedBall_boxProd_eq_univ`.
-/

namespace SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-! ### Lipschitz potentials -/

section Lipschitz

variable {f : V → ℕ} {a b : V}

/-- A potential growing by at most one along each edge grows by at most the length of a walk. -/
theorem Walk.le_add_length_of_lipschitz (hf : ∀ x y, G.Adj x y → f y ≤ f x + 1)
    (w : G.Walk a b) : f b ≤ f a + w.length := by
  induction w with
  | nil => simp
  | cons h _ ih =>
    have := hf _ _ h
    simp only [Walk.length_cons]
    omega

/-- A potential growing by at most one along each edge gives lower bounds on distances:
`f b ≤ f a + d(a, b)` (extended-distance version). -/
theorem le_add_edist_of_lipschitz (hf : ∀ x y, G.Adj x y → f y ≤ f x + 1) (a b : V) :
    (f b : ℕ∞) ≤ f a + G.edist a b := by
  by_cases h : G.Reachable a b
  · obtain ⟨w, hw⟩ := h.exists_walk_length_eq_edist
    rw [← hw]
    exact_mod_cast w.le_add_length_of_lipschitz hf
  · simp [edist_eq_top_of_not_reachable h]

/-- A potential growing by at most one along each edge gives lower bounds on distances:
`f b ≤ f a + d(a, b)` for connected `a`, `b`. -/
theorem Reachable.le_add_dist_of_lipschitz (hf : ∀ x y, G.Adj x y → f y ≤ f x + 1)
    (h : G.Reachable a b) : f b ≤ f a + G.dist a b := by
  obtain ⟨w, hw⟩ := h.exists_walk_length_eq_dist
  rw [← hw]
  exact w.le_add_length_of_lipschitz hf

/-- A potential growing by at most one along each edge changes by at most `r` within distance
`r`. -/
theorem le_add_of_edist_le_of_lipschitz (hf : ∀ x y, G.Adj x y → f y ≤ f x + 1) {r : ℕ}
    (h : G.edist a b ≤ r) : f b ≤ f a + r := by
  have : (f b : ℕ∞) ≤ f a + r := (le_add_edist_of_lipschitz hf a b).trans (by gcongr)
  exact_mod_cast this

/-- A function constant along edges is constant along walks. -/
theorem Walk.apply_eq_of_forall_adj {β : Sort*} {g : V → β} (hg : ∀ x y, G.Adj x y → g x = g y)
    (w : G.Walk a b) : g a = g b := by
  induction w with
  | nil => rfl
  | cons h _ ih => exact (hg _ _ h).trans ih

/-- A function constant along edges is constant on connected pairs. -/
theorem Reachable.apply_eq_of_forall_adj {β : Sort*} {g : V → β}
    (hg : ∀ x y, G.Adj x y → g x = g y) (h : G.Reachable a b) : g a = g b :=
  h.elim (·.apply_eq_of_forall_adj hg)

end Lipschitz

/-! ### Closed balls in box products and in finite connected graphs -/

section BoxProd

variable {α β : Type*} {G₁ : SimpleGraph α} {G₂ : SimpleGraph β}

/-- A product of closed balls lies in the closed ball of the box product (radii add up). -/
theorem closedBall_prod_subset_closedBall_boxProd (x₁ : α) (x₂ : β) (r₁ r₂ : ℕ∞) :
    G₁.closedBall x₁ r₁ ×ˢ G₂.closedBall x₂ r₂ ⊆ (G₁ □ G₂).closedBall (x₁, x₂) (r₁ + r₂) := by
  rintro ⟨y₁, y₂⟩ ⟨h₁, h₂⟩
  rw [mem_closedBall, edist_boxProd]
  exact add_le_add h₁ h₂

/-- The first coordinate of a point of a closed ball of `G₁ □ G₂` lies in the closed ball of `G₁`
of the same radius. -/
theorem fst_mem_closedBall_of_mem_boxProd {x y : α × β} {r : ℕ∞}
    (h : y ∈ (G₁ □ G₂).closedBall x r) : y.1 ∈ G₁.closedBall x.1 r := by
  rw [mem_closedBall, edist_boxProd] at h
  exact le_self_add.trans h

/-- The second coordinate of a point of a closed ball of `G₁ □ G₂` lies in the closed ball of `G₂`
of the same radius. -/
theorem snd_mem_closedBall_of_mem_boxProd {x y : α × β} {r : ℕ∞}
    (h : y ∈ (G₁ □ G₂).closedBall x r) : y.2 ∈ G₂.closedBall x.2 r := by
  rw [mem_closedBall, edist_boxProd] at h
  exact le_add_self.trans h

/-- If all closed balls of radius `r₁` of `G₁` and of radius `r₂` of `G₂` are everything, then so
are the closed balls of radius `r₁ + r₂` of `G₁ □ G₂`. -/
theorem closedBall_boxProd_eq_univ {r₁ r₂ : ℕ∞} (h₁ : ∀ x, G₁.closedBall x r₁ = Set.univ)
    (h₂ : ∀ x, G₂.closedBall x r₂ = Set.univ) (x : α × β) :
    (G₁ □ G₂).closedBall x (r₁ + r₂) = Set.univ := by
  refine Set.eq_univ_of_univ_subset ?_
  rw [← Set.univ_prod_univ, ← h₁ x.1, ← h₂ x.2]
  exact closedBall_prod_subset_closedBall_boxProd _ _ _ _

end BoxProd

/-- In a preconnected graph on `n` vertices, every closed ball of radius `≥ n - 1` is the whole
vertex set. -/
theorem closedBall_eq_univ_of_preconnected [Fintype V] (hG : G.Preconnected) (x : V) {r : ℕ}
    (hr : Fintype.card V ≤ r + 1) : G.closedBall x r = Set.univ := by
  classical
  refine Set.eq_univ_of_forall fun y => ?_
  obtain ⟨p⟩ := hG y x
  have := p.bypass_isPath.length_lt
  exact (edist_le p.bypass).trans (by exact_mod_cast (by omega : p.bypass.length ≤ r))

end SimpleGraph
