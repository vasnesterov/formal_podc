import Papers.PODC2010.TruncatedGaleShapley.Basic

/-!
# The examples of §2.4 and §2.5

* §2.4 (`triangle_not_epsStable`): the triangle with "rotational-symmetric" preferences (node `v`
  prefers `v+1` over `v+2`) has no `ε`-stable matching for `ε < 1`: every matching has at least
  as many unstable edges as matching edges, and at least one.
* §2.5 (`no_order_based_two_sub_eps`): on the path `0 - 1 - 2 - 3` with weights `1, α, 1`
  (`α > 1`), the order of the weights does not depend on `α`, and no fixed matching is a
  `(2 - ε)`-approximation of the maximum-weight matching for all `α > 1`.
-/

namespace Podc.TruncatedGaleShapley

open Finset

/-! ### §2.4: the triangle -/

/-- The triangle on `Fin 3`; node `v` prefers `v + 1` (rank `0`) over `v + 2` (rank `1`). -/
def triangle : PrefGraph (Fin 3) where
  N v := univ.erase v
  symm := by decide
  rank v u := ((u - v - 1 : Fin 3) : ℕ)
  rank_inj := by decide

/-- Every matching of the rotational triangle has at least one unstable edge and at least as many
unstable edges as matching edges ("one unstable edge to every matching edge"). -/
theorem triangle_unstable (p : Fin 3 → Option (Fin 3)) (hp : triangle.IsMatching p) :
    (matchingEdges p).card ≤ (triangle.unstableEdges p).card ∧
      0 < (triangle.unstableEdges p).card := by
  have key : ∀ p : Fin 3 → Option (Fin 3),
      (∀ u v, p u = some v → v ∈ triangle.N u ∧ p v = some u) →
      (matchingEdges p).card ≤ (triangle.unstableEdges p).card ∧
        0 < (triangle.unstableEdges p).card := by decide
  exact key p fun u v h => ⟨hp.mem_N u v h, hp.symm u v h⟩

/-- **§2.4.** The rotational triangle (a non-bipartite instance) has no `ε`-stable matching for
`ε < 1`. -/
theorem triangle_not_epsStable {ε : ℝ} (hε : ε < 1) (p : Fin 3 → Option (Fin 3))
    (hp : triangle.IsMatching p) : ¬ triangle.IsEpsStable ε p := by
  obtain ⟨h1, h2⟩ := triangle_unstable p hp
  rw [PrefGraph.isEpsStable_iff]
  intro h
  have h1' : ((matchingEdges p).card : ℝ) ≤ (triangle.unstableEdges p).card := by exact_mod_cast h1
  have h2' : (0 : ℝ) < (triangle.unstableEdges p).card := by exact_mod_cast h2
  have hM : (0 : ℝ) ≤ (matchingEdges p).card := Nat.cast_nonneg _
  have hM0 : ((matchingEdges p).card : ℝ) ≤ 0 := by
    by_contra hpos
    have := mul_lt_mul_of_pos_right hε (lt_of_not_ge hpos)
    linarith
  nlinarith

/-! ### §2.5: approximation `2 - ε` is impossible for order-based algorithms -/

/-- The edges of the path `0 - 1 - 2 - 3`. -/
def e₀ : Sym2 (Fin 4) := s(0, 1)
/-- The middle edge. -/
def e₁ : Sym2 (Fin 4) := s(1, 2)
/-- The last edge. -/
def e₂ : Sym2 (Fin 4) := s(2, 3)

/-- The edge set of the path. -/
def pathEdges : Finset (Sym2 (Fin 4)) := {e₀, e₁, e₂}

/-- A matching of the path: a set of path edges, every node in at most one of them. -/
def IsPathMatching (M : Finset (Sym2 (Fin 4))) : Prop :=
  M ⊆ pathEdges ∧ ∀ v : Fin 4, (M.filter (v ∈ ·)).card ≤ 1

instance (M : Finset (Sym2 (Fin 4))) : Decidable (IsPathMatching M) := by
  unfold IsPathMatching; infer_instance

/-- The weights `1, α, 1`. -/
def wα (α : ℝ) (e : Sym2 (Fin 4)) : ℝ := if e = e₁ then α else 1

set_option maxRecDepth 20000 in
lemma pathMatching_cases :
    ∀ M ∈ pathEdges.powerset, IsPathMatching M → (e₁ ∈ M → M = {e₁}) ∧ (e₁ ∉ M → M ⊆ {e₀, e₂}) := by
  decide

/-- **§2.5.** For every `ε > 0` and every matching `M` of the path `0 - 1 - 2 - 3` (the output of an
algorithm that sees only the order of the weights `1, α, 1`, which is the same for all `α > 1`),
there is `α > 1` and a matching `M*` with `(2 - ε) w_α(M) < w_α(M*)`: no such algorithm is a
`(2 - ε)`-approximation. -/
theorem no_order_based_two_sub_eps {ε : ℝ} (hε : 0 < ε) (M : Finset (Sym2 (Fin 4)))
    (hM : IsPathMatching M) :
    ∃ α : ℝ, 1 < α ∧ ∃ M' : Finset (Sym2 (Fin 4)), IsPathMatching M' ∧
      (2 - ε) * ∑ e ∈ M, wα α e < ∑ e ∈ M', wα α e := by
  obtain ⟨h1, h2⟩ := pathMatching_cases M (mem_powerset.2 hM.1) hM
  by_cases he : e₁ ∈ M
  · refine ⟨1 + ε / 4, by linarith, {e₀, e₂}, by decide, ?_⟩
    rw [h1 he]
    rw [sum_singleton, sum_pair (by decide)]
    simp only [wα, show e₀ ≠ e₁ by decide, show e₂ ≠ e₁ by decide, ite_true, ite_false]
    nlinarith
  · refine ⟨4, by norm_num, {e₁}, by decide, ?_⟩
    have hle : ∑ e ∈ M, wα 4 e ≤ 2 := by
      calc ∑ e ∈ M, wα 4 e ≤ ∑ e ∈ ({e₀, e₂} : Finset _), wα 4 e :=
            sum_le_sum_of_subset_of_nonneg (h2 he) fun _ _ _ => by unfold wα; split_ifs <;> norm_num
        _ = 2 := by
          rw [sum_pair (by decide)]
          simp [wα, show e₀ ≠ e₁ by decide, show e₂ ≠ e₁ by decide]; norm_num
    have h0 : 0 ≤ ∑ e ∈ M, wα 4 e := sum_nonneg fun _ _ => by unfold wα; split_ifs <;> norm_num
    rw [sum_singleton, show wα 4 e₁ = 4 by simp [wα]]
    rcases le_or_gt ε 2 with h | h <;> nlinarith

end Podc.TruncatedGaleShapley
