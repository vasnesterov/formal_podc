import Papers.PODC2019.MinimalSymmetryBreaking.Tree

/-!
# Anonymous randomized algorithms on the oriented tree; the speedup lemmas

Section 5 (`Δ = 4`) and Section 7 (`Δ = 2k`) of the paper. Nodes have no identifiers; every node
`v` has an independent random value `x v` from a finite probability space `(Ω, μ)`.

* A `t`-round (node) algorithm with palette `α` is a function `out` of the field around the origin
  that only depends on the ball of radius `t`; node `v` outputs `out (shift v x)`. It *fails
  locally* at `v` if all `2k` neighbours of `v` output the same colour as `v` (no weak colouring).
* A `t`-round edge algorithm assigns to the edge `{v, v gᵈ}` of dimension `d` the value
  `out d (shift v x)`, a function of the balls of radius `t` around both endpoints. It fails
  locally at `v` if, in every dimension, the two edges of `v` get the same value.

Since all nodes of the tree look the same, the local failure probability does not depend on the
node; we compute it at the origin (`failProb`).
-/

namespace Podc.MinimalSymmetryBreaking

open Finset Function
open scoped Classical

noncomputable section

variable {k : ℕ} {Ω : Type} [Fintype Ω] [Inhabited Ω]

/-- A `t`-round anonymous randomized algorithm on the oriented `2k`-regular tree with output
palette `α`: node `v` outputs `out (shift v x)`. -/
structure NodeAlg (k : ℕ) (Ω : Type) (t : ℕ) (α : Type) where
  /-- The output of the origin, as a function of the random field. -/
  out : (Tree k → Ω) → α
  /-- The output only depends on the random values within distance `t`. -/
  dep : DependsOn out (ball 1 t)

/-- A `t`-round anonymous randomized *edge* algorithm: the edge `{v, v * gᵈ}` outputs
`out d (shift v x)`, a function of the radius-`t` balls around both endpoints. -/
structure EdgeAlg (k : ℕ) (Ω : Type) (t : ℕ) (β : Type) where
  /-- The output of the edge `{1, gᵈ}`. -/
  out : Fin k → (Tree k → Ω) → β
  /-- The output only depends on the random values within distance `t` of an endpoint. -/
  dep : ∀ d, DependsOn (out d) (ball 1 t ∪ ball (dir (d, true)) t)

variable {t : ℕ} {α β : Type}

/-- Local failure of a node algorithm at the origin: all neighbours have the colour of the
origin. -/
def NodeAlg.Fail (A : NodeAlg k Ω t α) (x : Tree k → Ω) : Prop :=
  ∀ p : Fin k × Bool, A.out (shift (dir p) x) = A.out x

/-- Local failure of an edge algorithm at the origin: in every dimension `d` the two edges of
dimension `d` at the origin, `{1, gᵈ}` and `{gᵈ⁻¹, 1}`, have the same value. -/
def EdgeAlg.Fail (B : EdgeAlg k Ω t β) (x : Tree k → Ω) : Prop :=
  ∀ d : Fin k, B.out d x = B.out d (shift (dir (d, false)) x)

variable (μ : FinDist Ω)

/-- The local failure probability of a node algorithm. -/
def NodeAlg.failProb (A : NodeAlg k Ω t α) : ℝ := prob μ (Ball (t + 1)) A.Fail

/-- The local failure probability of an edge algorithm. -/
def EdgeAlg.failProb (B : EdgeAlg k Ω t β) : ℝ := prob μ (Ball (t + 1)) B.Fail

variable {μ}

lemma dir_mem_ball_one (p : Fin k × Bool) {r : ℕ} (hr : 1 ≤ r) : dir p ∈ ball (1 : Tree k) r := by
  simp [mem_ball, hr]

lemma NodeAlg.dep_shift (A : NodeAlg k Ω t α) (v : Tree k) :
    DependsOn (fun x => A.out (shift v x)) (ball v t) := by
  have := dependsOn_shift_ball A.dep v; rwa [mul_one] at this

lemma ball_dir_subset_one (p : Fin k × Bool) (r : ℕ) : ball (dir p) r ⊆ ball (1 : Tree k) (r + 1) := by
  have := ball_dir_subset (1 : Tree k) p r; rwa [one_mul] at this

lemma NodeAlg.fail_dependsOn (A : NodeAlg k Ω t α) : DependsOn A.Fail (ball 1 (t + 1)) := by
  intro x x' h
  unfold NodeAlg.Fail
  apply propext
  apply forall_congr'
  intro p
  have e1 : A.out (shift (dir p) x) = A.out (shift (dir p) x') :=
    A.dep_shift (dir p) (fun w hw => h w (ball_dir_subset_one p t hw))
  have e2 : A.out x = A.out x' := A.dep (fun w hw => h w (ball_mono (Nat.le_succ t) hw))
  rw [e1, e2]

lemma EdgeAlg.dep_shift (B : EdgeAlg k Ω t β) (d : Fin k) (v : Tree k) :
    DependsOn (fun x => B.out d (shift v x)) (ball v t ∪ ball (v * dir (d, true)) t) := by
  have := dependsOn_shift (B.dep d) v
  rwa [Set.preimage_union, preimage_inv_mul_ball, preimage_inv_mul_ball, mul_one] at this

lemma EdgeAlg.fail_dependsOn (B : EdgeAlg k Ω t β) : DependsOn B.Fail (ball 1 (t + 1)) := by
  intro x x' h
  unfold EdgeAlg.Fail
  apply propext
  apply forall_congr'
  intro d
  have h1 : ball 1 t ∪ ball (dir (d, true)) t ⊆ ball (1 : Tree k) (t + 1) :=
    Set.union_subset (ball_mono (Nat.le_succ t)) (ball_dir_subset_one _ t)
  have h2 : ball (dir (d, false)) t ∪ ball (dir (d, false) * dir (d, true)) t ⊆
      ball (1 : Tree k) (t + 1) := by
    have : dir (d, false) * dir (d, true) = (1 : Tree k) := by
      rw [show dir (d, false) = (dir (d, true))⁻¹ by rw [dir_inv]; rfl]; group
    rw [this]
    exact Set.union_subset (ball_dir_subset_one _ t) (ball_mono (Nat.le_succ t))
  have e1 : B.out d x = B.out d x' := B.dep d (fun w hw => h w (h1 hw))
  have e2 : B.out d (shift (dir (d, false)) x) = B.out d (shift (dir (d, false)) x') :=
    B.dep_shift d (dir (d, false)) (fun w hw => h w (h2 hw))
  rw [e1, e2]

/-! ### Products of indicators -/

lemma ind_forall {κ : Type*} [Fintype κ] (E : κ → (Tree k → Ω) → Prop) (x : Tree k → Ω) :
    ind (fun x => ∀ j, E j x) x = ∏ j, ind (E j) x := by
  by_cases h : ∀ j, E j x
  · simp [ind, h]
  · push_neg at h
    obtain ⟨j, hj⟩ := h
    rw [Finset.prod_eq_zero (Finset.mem_univ j) (by simp [ind, hj])]
    simp only [ind]
    rw [if_neg]; push_neg; exact ⟨j, hj⟩

lemma prod_ind_nonneg {κ : Type*} [Fintype κ] (E : κ → (Tree k → Ω) → Prop)
    (x : Tree k → Ω) : 0 ≤ ∏ j, ind (E j) x :=
  Finset.prod_nonneg fun j _ => ind_nonneg _ _

end

end Podc.MinimalSymmetryBreaking
