import Papers.PODC2018.SparseColoringLB.Model

/-!
# A toroidal triangulation that is not 4-colourable (Fisk)

The graph `torus w` (Figure 3 of the paper, up to drawing) has `n = 3w + 1` vertices: three rows
`a_0 … a_{w-1}`, `b_0 … b_{w-1}`, `c_0 … c_{w-1}` (vertex `some (i, j)` is row `i`, column `j`) and
one extra vertex `a_w` of the first row (`none`). It is the triangulation of the torus made of three
triangulated bands between the cyclic rows `a` (length `w + 1`), `b`, `c` (length `w`):
* column triangles `a_j b_j c_j`;
* between columns `j` and `j + 1`: `a_j a_{j+1}`, `b_j b_{j+1}`, `c_j c_{j+1}`, `b_j a_{j+1}`,
  `c_j b_{j+1}`, `c_j a_{j+1}`;
* around the torus: `b_{w-1} b_0`, `c_{w-1} c_0`, `c_{w-1} b_0`, and `a_w` is adjacent to
  `a_{w-1}, a_0, b_{w-1}, b_0, c_{w-1}, c_0`.
All degrees are `6`, except `deg a_0 = 4` and `deg b_0 = deg c_0 = 7`: exactly two vertices of odd
degree, and they are adjacent, so Fisk's theorem (cited by the paper) says that `torus w` is not
4-colourable.

We prove this directly (`torus_not_colorable`) by Fisk's parity argument specialised to this
"3-row" family, phrased as a transfer argument: the colours `(a_j, b_j, c_j)` of a column form one
of 24 *states*; consecutive columns are related by a relation `R` that never leaves one of 6 classes
(`stateClass`), while the passage through `a_w` from column `w - 1` to column `0` always changes the
class. Both facts are finite checks (`decide`).
-/

namespace Podc.SparseColoringLB

open SimpleGraph

/-- Vertices of `torus w`: `some (i, j)` is row `i ∈ {a, b, c}`, column `j`; `none` is `a_w`. -/
abbrev TV (w : ℕ) := Option (Fin 3 × Fin w)

/-- The edges of `torus w`, each listed once (in one direction). -/
def torusRel (w : ℕ) : TV w → TV w → Prop
  | some (i, j), some (i', j') =>
    (j = j' ∧ i ≠ i') ∨
    ((j : ℕ) + 1 = j' ∧ (i' = i ∨ (i = 1 ∧ i' = 0) ∨ (i = 2 ∧ i' = 1) ∨ (i = 2 ∧ i' = 0))) ∨
    ((j : ℕ) + 1 = w ∧ (j' : ℕ) = 0 ∧ ((i = 1 ∧ i' = 1) ∨ (i = 2 ∧ i' = 2) ∨ (i = 2 ∧ i' = 1)))
  | none, some (_, j) => (j : ℕ) + 1 = w ∨ (j : ℕ) = 0
  | _, _ => False

/-- The toroidal triangulation of Figure 3 with `3w + 1` vertices (two adjacent vertices `b_0`,
`c_0` of odd degree `7`, all others of even degree). -/
def torus (w : ℕ) : SimpleGraph (TV w) := SimpleGraph.fromRel (torusRel w)

/-- Class of a column state `(a, b, c)` (colours of `a_j, b_j, c_j`); the 6 classes are the
connected components of the transfer relation on the 24 proper states. -/
def stateClass (a b c : Fin 4) : Fin 6 :=
  (![0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 3, 0, 4, 5, 0, 0, 0, 3, 5, 0, 0, 0, 0, 4, 0, 0, 0, 2, 0, 1,
    0, 0, 1, 0, 4, 5, 0, 0, 2, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 2, 0, 3, 0, 4, 0, 1, 5, 0, 0, 0, 0, 0,
    0] : Fin 64 → Fin 6) ⟨a * 16 + b * 4 + c, by omega⟩

set_option synthInstance.maxSize 4000 in
/-- The transfer relation between consecutive columns preserves the class. -/
lemma stateClass_step : ∀ a b c a' b' c' : Fin 4, a ≠ b → b ≠ c → c ≠ a →
    a' ≠ b' → b' ≠ c' → c' ≠ a' → a ≠ a' → b ≠ b' → c ≠ c' → b ≠ a' → c ≠ b' → c ≠ a' →
    stateClass a b c = stateClass a' b' c' := by decide

set_option synthInstance.maxSize 4000 in
/-- The passage from column `w - 1` to column `0` through `a_w` (colour `x`) changes the class. -/
lemma stateClass_wrap : ∀ a b c x a' b' c' : Fin 4, a ≠ b → b ≠ c → c ≠ a →
    a' ≠ b' → b' ≠ c' → c' ≠ a' → b ≠ b' → c ≠ c' → c ≠ b' →
    x ≠ a → x ≠ b → x ≠ c → x ≠ a' → x ≠ b' → x ≠ c' →
    stateClass a b c ≠ stateClass a' b' c' := by decide

section Adj

variable {w : ℕ}

lemma torus_adj_col (i i' : Fin 3) (j : Fin w) (h : i ≠ i') :
    (torus w).Adj (some (i, j)) (some (i', j)) := by
  rw [torus, fromRel_adj]
  exact ⟨by simpa using h, Or.inl (Or.inl ⟨rfl, h⟩)⟩

lemma torus_adj_next (i i' : Fin 3) (j j' : Fin w) (hj : (j : ℕ) + 1 = j')
    (h : i' = i ∨ (i = 1 ∧ i' = 0) ∨ (i = 2 ∧ i' = 1) ∨ (i = 2 ∧ i' = 0)) :
    (torus w).Adj (some (i, j)) (some (i', j')) := by
  rw [torus, fromRel_adj]
  refine ⟨?_, Or.inl (Or.inr (Or.inl ⟨hj, h⟩))⟩
  intro h'
  simp only [Option.some.injEq, Prod.mk.injEq] at h'
  rw [h'.2] at hj; omega

lemma torus_adj_wrap (hw : 2 ≤ w) (i i' : Fin 3) (j j' : Fin w) (hj : (j : ℕ) + 1 = w)
    (hj' : (j' : ℕ) = 0) (h : (i = 1 ∧ i' = 1) ∨ (i = 2 ∧ i' = 2) ∨ (i = 2 ∧ i' = 1)) :
    (torus w).Adj (some (i, j)) (some (i', j')) := by
  rw [torus, fromRel_adj]
  refine ⟨?_, Or.inl (Or.inr (Or.inr ⟨hj, hj', h⟩))⟩
  intro h'
  simp only [Option.some.injEq, Prod.mk.injEq] at h'
  rw [h'.2] at hj; omega

lemma torus_adj_extra (i : Fin 3) (j : Fin w) (hj : (j : ℕ) + 1 = w ∨ (j : ℕ) = 0) :
    (torus w).Adj none (some (i, j)) := by
  rw [torus, fromRel_adj]
  exact ⟨by simp, Or.inl hj⟩

end Adj

/-- **Fisk's theorem for the triangulations of Figure 3.** For `w ≥ 2`, `torus w` (with `3w + 1`
vertices) is not 4-colourable. -/
theorem torus_not_colorable {w : ℕ} (hw : 2 ≤ w) : IsEmpty ((torus w).Coloring (Fin 4)) := by
  refine ⟨fun C => ?_⟩
  have hc : ∀ {p q}, (torus w).Adj p q → C p ≠ C q := fun h => C.valid h
  let col : Fin w → Fin 6 := fun j =>
    stateClass (C (some (0, j))) (C (some (1, j))) (C (some (2, j)))
  have hcol := fun (j : Fin w) (i i' : Fin 3) (h : i ≠ i') => hc (torus_adj_col i i' j h)
  -- consecutive columns have the same class
  have step : ∀ (j j' : Fin w), (j : ℕ) + 1 = j' → col j = col j' := by
    intro j j' hj
    have hn := fun (i i' : Fin 3) h => hc (torus_adj_next i i' j j' hj h)
    exact stateClass_step _ _ _ _ _ _ (hcol j 0 1 (by decide)) (hcol j 1 2 (by decide))
      (hcol j 2 0 (by decide)) (hcol j' 0 1 (by decide)) (hcol j' 1 2 (by decide))
      (hcol j' 2 0 (by decide)) (hn 0 0 (by decide)) (hn 1 1 (by decide)) (hn 2 2 (by decide))
      (hn 1 0 (by decide)) (hn 2 1 (by decide)) (hn 2 0 (by decide))
  have hall : ∀ (k : ℕ) (hk : k < w), col ⟨k, hk⟩ = col ⟨0, by omega⟩ := by
    intro k
    induction k with
    | zero => intro _; rfl
    | succ k ih =>
      intro hk
      rw [← ih (by omega)]
      exact (step ⟨k, by omega⟩ ⟨k + 1, hk⟩ rfl).symm
  -- the passage through `a_w` changes the class
  set l : Fin w := ⟨w - 1, by omega⟩
  set z : Fin w := ⟨0, by omega⟩
  have hl : (l : ℕ) + 1 = w := by simp [l]; omega
  have hz : (z : ℕ) = 0 := rfl
  have hwr := fun (i i' : Fin 3) h => hc (torus_adj_wrap hw i i' l z hl hz h)
  have hx := fun (i : Fin 3) (j : Fin w) h => hc (torus_adj_extra i j h)
  have := stateClass_wrap _ _ _ (C none) _ _ _ (hcol l 0 1 (by decide)) (hcol l 1 2 (by decide))
    (hcol l 2 0 (by decide)) (hcol z 0 1 (by decide)) (hcol z 1 2 (by decide))
    (hcol z 2 0 (by decide)) (hwr 1 1 (by decide)) (hwr 2 2 (by decide)) (hwr 2 1 (by decide))
    (hx 0 l (Or.inl hl)) (hx 1 l (Or.inl hl)) (hx 2 l (Or.inl hl))
    (hx 0 z (Or.inr hz)) (hx 1 z (Or.inr hz)) (hx 2 z (Or.inr hz))
  exact this (hall (w - 1) (by omega))

end Podc.SparseColoringLB
