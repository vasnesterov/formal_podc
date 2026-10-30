import Papers.PODC2026.OverwriteLeastFixedPoints.Basic

/-!
# Section 6: the hypotheses of the theorems in some applications

* `alg5_not_monotone`: Algorithm 5 (lock-free Gale–Shapley) is **not** monotone on the paper's
  lattice `{0,…,n+1}ⁿ`, contrary to "Notice that Algorithm 5 is inflationary and monotone", so
  Theorems 3 and 4 do not apply to it.
* `alg7_no_common_fixed_point`, `alg7_not_monotone`: Algorithm 7 (Bellman–Ford with levels) has no
  common fixed point at all (for every relaxation rule), and it is not monotone, so Corollary 4.2
  does not apply to it.
* `alg10_out_of_range`: Algorithm 10 (envy-eliminating subsidies) does not map the paper's lattice
  `{0,…,mΔ}ⁿ` into itself (needs a cap).
-/

namespace Podc.OverwriteLeastFixedPoints.Apps

open Podc.OverwriteLeastFixedPoints

/-! ## Algorithm 5 -/

/-- The woman man `j` currently proposes to: his `G j`-th choice if `1 ≤ G j ≤ n` (positions are
1-based; `mpref j k` is his `(k+1)`-th choice), and nobody otherwise. -/
def cur {n : ℕ} (mpref : Fin n → Fin n → Fin n) (G : Fin n → Fin (n + 2)) (j : Fin n) :
    Option (Fin n) :=
  if h : 1 ≤ (G j).val ∧ (G j).val ≤ n then some (mpref j ⟨(G j).val - 1, by omega⟩) else none

/-- Algorithm 5 of the paper (function `f(i)`), on states `G : Fin n → {0,…,n+1}`:
`G[i] = 0 ⇒ G[i] := 1`; `G[i] > n ⇒` no change; otherwise, with `w` the woman `i` proposes to, if
some man `j ≠ i` currently proposes to `w` and `w` ranks `j` better (`rank w j < rank w i`), then
`G[i] := G[i] + 1`. -/
def alg5 {n : ℕ} (mpref : Fin n → Fin n → Fin n) (rank : Fin n → Fin n → ℕ) (i : Fin n)
    (G : Fin n → Fin (n + 2)) : Fin n → Fin (n + 2) :=
  if G i = 0 then Function.update G i 1
  else match cur mpref G i with
    | none => G
    | some w =>
      if ∃ j, j ≠ i ∧ cur mpref G j = some w ∧ rank w j < rank w i then
        Function.update G i (G i + 1)
      else G

/-- **Algorithm 5 is not monotone.** Two men who both rank `w₀` first and `w₁` second; `w₀`
prefers `m₁`. For `G = (1, 1)` (both propose to `w₀`) and `H = (1, 2)` (`m₁` has moved on to `w₁`)
we have `G ≤ H`, but `f₀ G = (2, 1)` (`m₀` is rejected because `m₁` is at `w₀`) and `f₀ H = (1, 2)`
(nobody better is at `w₀`), and `(2, 1) ≰ (1, 2)`. All values are proposal positions in `1..n`, so
the reading of out-of-range positions does not matter. -/
theorem alg5_not_monotone :
    let mpref : Fin 2 → Fin 2 → Fin 2 := fun _ k => k
    let rank : Fin 2 → Fin 2 → ℕ := fun w j => if w = 0 then (if j = 1 then 0 else 1) else j
    let G : Fin 2 → Fin 4 := ![1, 1]
    let H : Fin 2 → Fin 4 := ![1, 2]
    G ≤ H ∧ alg5 mpref rank 0 G = ![2, 1] ∧ alg5 mpref rank 0 H = ![1, 2] ∧
      ¬ alg5 mpref rank 0 G ≤ alg5 mpref rank 0 H ∧ ¬ Monotone (alg5 mpref rank 0) := by
  intro mpref rank G H
  have hG : alg5 mpref rank 0 G = ![2, 1] := by decide
  have hH : alg5 mpref rank 0 H = ![1, 2] := by decide
  have hGH : G ≤ H := by decide
  have hn : ¬ alg5 mpref rank 0 G ≤ alg5 mpref rank 0 H := by rw [hG, hH]; decide
  exact ⟨hGH, hG, hH, hn, fun hm => hn (hm hGH)⟩

/-! ## Algorithm 7 -/

/-- Algorithm 7 (Bellman–Ford with levels), for an arbitrary relaxation rule `relax` computing the
new distance of `i` from the state: a state is a vector of pairs `(dist, level)`; if some vertex
lags behind `i` (smaller level) nothing changes, otherwise `i` relaxes its distance and increments
its level. -/
def alg7 {n : ℕ} (relax : (Fin n → ℕ × ℕ) → Fin n → ℕ) (i : Fin n) (G : Fin n → ℕ × ℕ) :
    Fin n → ℕ × ℕ :=
  if ∃ k, (G k).2 < (G i).2 then G else Function.update G i (relax G i, (G i).2 + 1)

/-- **Algorithm 7 has no common fixed point** (for any relaxation rule and any `n ≥ 1`): the vertex
of minimal level always increments its level. Hence Corollary 4.2 (which needs a finite lattice and
yields a common fixed point) cannot apply to it. -/
theorem alg7_no_common_fixed_point {n : ℕ} [NeZero n] (relax : (Fin n → ℕ × ℕ) → Fin n → ℕ)
    (G : Fin n → ℕ × ℕ) : ¬ IsCommonFixed (alg7 relax) G := by
  intro h
  obtain ⟨i, -, hi⟩ := Finset.exists_min_image Finset.univ (fun k => (G k).2) ⟨0, Finset.mem_univ _⟩
  have hfix := congrFun (h i) i
  have hno : ¬ ∃ k, (G k).2 < (G i).2 := fun ⟨k, hk⟩ => absurd (hi k (Finset.mem_univ _)) (by omega)
  simp only [alg7, hno, ite_false, Function.update_self] at hfix
  have := congrArg Prod.snd hfix
  simp at this

/-- The relaxation of Algorithm 7 for a weighted digraph `w k i = some c` (edge `k → i` of weight
`c`): `dist i := min (dist i) (min over predecessors k of dist k + w k i)`. -/
def bfRelax {n : ℕ} (w : Fin n → Fin n → Option ℕ) (G : Fin n → ℕ × ℕ) (i : Fin n) : ℕ :=
  Finset.univ.fold min (G i).1 fun k => match w k i with
    | some c => (G k).1 + c
    | none => (G i).1

/-- The paper's order on Algorithm 7's states: componentwise, distances ordered by `≥` and levels by
`≤`. -/
def bfLe {n : ℕ} (G H : Fin n → ℕ × ℕ) : Prop := ∀ i, (H i).1 ≤ (G i).1 ∧ (G i).2 ≤ (H i).2

/-- **Algorithm 7 is not monotone** (in the paper's order): one edge `0 → 1` of weight `1`;
`G = ((0,1), (5,1))` and `H = ((0,1), (5,2))` satisfy `G ⊑ H`; vertex `1` relaxes in `G`
(giving `(1,2)`), but in `H` vertex `0` lags behind, so nothing changes and distance `5` stays. -/
theorem alg7_not_monotone :
    let w : Fin 2 → Fin 2 → Option ℕ := fun k i => if k = 0 ∧ i = 1 then some 1 else none
    let G : Fin 2 → ℕ × ℕ := ![(0, 1), (5, 1)]
    let H : Fin 2 → ℕ × ℕ := ![(0, 1), (5, 2)]
    bfLe G H ∧ alg7 (bfRelax w) 1 G = ![(0, 1), (1, 2)] ∧ alg7 (bfRelax w) 1 H = H ∧
      ¬ bfLe (alg7 (bfRelax w) 1 G) (alg7 (bfRelax w) 1 H) := by
  intro w G H
  have h1 : alg7 (bfRelax w) 1 G = ![(0, 1), (1, 2)] := by decide
  have h2 : alg7 (bfRelax w) 1 H = H := by decide
  refine ⟨by unfold bfLe; decide, h1, h2, ?_⟩
  rw [h1, h2]; unfold bfLe; decide

/-! ## Algorithm 10 -/

/-- Algorithm 10: `G[i] := G[i] + max(0, max_{j ≠ i} (v_i(X_j) + G[j] − v_i(X_i) − G[i]))`, where
`val i j = v_i(X_j)`. -/
def alg10 {n : ℕ} (val : Fin n → Fin n → ℤ) (i : Fin n) (G : Fin n → ℤ) : Fin n → ℤ :=
  Function.update G i
    (G i + (Finset.univ.filter (· ≠ i)).fold max 0 fun j => val i j + G j - (val i i + G i))

/-- **Algorithm 10 leaves the lattice `{0,…,mΔ}ⁿ`.** Two agents, one item (`m = 1`) given to agent
`0` and valued `1` by both, so `Δ = max v_i(X_j) = 1` and `L = {0,1}²` (the allocation is
envy-freeable). From `G = (1,1) ∈ L`, `f₁` produces `G[1] = 2 ∉ {0,1}`. (Capping the update at
`mΔ` repairs this.) -/
theorem alg10_out_of_range :
    let val : Fin 2 → Fin 2 → ℤ := ![![1, 0], ![1, 0]]
    alg10 val 1 ![1, 1] 1 = 2 := by
  decide

end Podc.OverwriteLeastFixedPoints.Apps
