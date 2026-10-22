import Papers.PODC2018.SparseColoringLB.Model

-- CSLib candidate: Cslib/Foundations/Combinatorics/SimpleGraph/KleinGrid.lean (klein, klein_not_colorable,
-- kshift automorphism).

/-!
# Grids on the Klein bottle are not 3-colourable

`klein m n` is the `m × n` rectangular grid on the Klein bottle (`G_{m,n}` in the paper,
Figure 2, left): the vertices are `(i, j) ∈ Fin m × Fin n`, the columns `{(i, j) | i}` are cycles of
length `m` (`cycleGraph m`), consecutive columns are joined by horizontal edges `(i, j) ~ (i, j + 1)`,
and the last column is glued to the first one with a reflection: `(i, n - 1) ~ (-i, 0)`.
Equivalently, `klein m n = C_m □ P_n` plus the twisted wrap-around edges.

The paper cites Gallai: `G_{2k+1, 2ℓ+1}` is 4-chromatic. We prove the part that is used, in a more
general form: for every odd `m ≥ 3` and every `n ≥ 2`, `klein m n` is not 3-colourable
(`klein_not_colorable`). The proof is the classical winding-number argument: in a 3-colouring with
colours in `ℤ/3`, every edge has a "slope" `±1`; around each 4-face the slopes sum to `0`; hence the
total slope `W j` of the column cycle `j` does not depend on `j`, while the twisted gluing reverses
the orientation of the column cycle, so `W 0 = -W 0`. But `W 0` is a sum of `m` odd numbers.

The file also provides the tools for the locality arguments of Theorems 2.5 and 2.6:
* `kshift`: the column shift, an automorphism of `klein m n` of order `2n` (`kshift_adj_iff`);
* `cyl m k = C_m □ P_k` (the Klein bottle grid without its twisted edges), `ballAgree_klein_cyl`
  (seen from far from the twisted edges, the two graphs agree), and `cyl_view` (every edge of the
  Klein bottle grid is seen, within radius `r`, as an edge in the middle of the cylinder, provided
  `2r + 2 ≤ k`).
-/

namespace Podc.SparseColoringLB

open SimpleGraph

/-- The twisted wrap-around edges of the Klein bottle grid: `(i, n - 1) ~ (-i, 0)`. -/
def kleinWrap (m n : ℕ) : SimpleGraph (Fin m × Fin n) :=
  SimpleGraph.fromRel fun p q => (p.2 : ℕ) + 1 = n ∧ (q.2 : ℕ) = 0 ∧ q.1 = -p.1

/-- The `m × n` grid on the Klein bottle (`G_{m,n}` in the paper): `C_m □ P_n` plus the twisted
wrap-around edges `(i, n - 1) ~ (-i, 0)`. -/
def klein (m n : ℕ) : SimpleGraph (Fin m × Fin n) :=
  (cycleGraph m □ pathGraph n) ⊔ kleinWrap m n

/-- The slope of an edge coloured `a → b` with colours in `ℤ/3`: `+1` if `b = a + 1`, else `-1`. -/
def slope (a b : Fin 3) : ℤ := if b = a + 1 then 1 else -1

lemma slope_face : ∀ a b c d : Fin 3, a ≠ b → b ≠ c → c ≠ d → d ≠ a →
    slope a b + slope b c + slope c d + slope d a = 0 := by decide

lemma slope_swap : ∀ a b : Fin 3, a ≠ b → slope b a = - slope a b := by decide

lemma slope_eq (a b : Fin 3) : slope a b = 2 * (if b = a + 1 then 1 else 0) - 1 := by
  unfold slope; split_ifs <;> norm_num

section Adj

variable {m n : ℕ}

lemma klein_adj_vert (hm : 3 ≤ m) (i : Fin m) (j : Fin n) [NeZero m] :
    (klein m n).Adj (i, j) (i + 1, j) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
  left
  rw [boxProd_adj]
  left
  refine ⟨?_, rfl⟩
  rw [cycleGraph_adj]
  right; simp

lemma klein_adj_horiz (i : Fin m) (j j' : Fin n) (h : (j' : ℕ) = j + 1) :
    (klein m n).Adj (i, j) (i, j') := by
  left
  rw [boxProd_adj]
  right
  refine ⟨?_, rfl⟩
  show (pathGraph n).Adj j j'
  rw [pathGraph_adj]; omega

lemma klein_adj_wrap (hn : 2 ≤ n) (i : Fin m) (j j' : Fin n) (hj : (j : ℕ) + 1 = n)
    (hj' : (j' : ℕ) = 0) : (klein m n).Adj (i, j) (-i, j') := by
  right
  rw [kleinWrap, fromRel_adj]
  refine ⟨?_, Or.inl ⟨hj, hj', rfl⟩⟩
  intro h
  have h2 : j = j' := (Prod.ext_iff.1 h).2
  have := congrArg Fin.val h2
  omega

end Adj

/-- **Gallai.** For odd `m ≥ 3` and `n ≥ 2`, the Klein bottle grid `klein m n` has no proper
3-colouring. (The paper cites [Gallai] that `G_{2k+1,2ℓ+1}` is 4-chromatic; we only need, and prove,
`χ > 3`, for every `n ≥ 2`.) -/
theorem klein_not_colorable {m n : ℕ} (hm : Odd m) (hm3 : 3 ≤ m) (hn : 2 ≤ n) :
    IsEmpty ((klein m n).Coloring (Fin 3)) := by
  have : NeZero m := ⟨by omega⟩
  refine ⟨fun C => ?_⟩
  let c : Fin m × Fin n → Fin 3 := C
  have hc : ∀ {p q}, (klein m n).Adj p q → c p ≠ c q := fun h => C.valid h
  -- total slope of column `j`
  let W : Fin n → ℤ := fun j => ∑ i : Fin m, slope (c (i, j)) (c (i + 1, j))
  -- consecutive columns have the same total slope
  have step : ∀ j j' : Fin n, (j' : ℕ) = j + 1 → W j = W j' := by
    intro j j' hjj
    let h : Fin m → ℤ := fun i => slope (c (i, j)) (c (i, j'))
    have key : ∀ i : Fin m, slope (c (i, j)) (c (i + 1, j)) - slope (c (i, j')) (c (i + 1, j')) =
        h i - h (i + 1) := by
      intro i
      have hf := slope_face (c (i, j)) (c (i + 1, j)) (c (i + 1, j')) (c (i, j'))
        (hc (klein_adj_vert hm3 i j)) (hc (klein_adj_horiz _ _ _ hjj))
        (hc (klein_adj_vert hm3 i j').symm) (hc (klein_adj_horiz _ _ _ hjj).symm)
      have s1 := slope_swap _ _ (hc (klein_adj_vert hm3 i j'))
      have s2 := slope_swap _ _ (hc (klein_adj_horiz i j j' hjj))
      simp only [h]
      linarith
    have hsum : ∑ i : Fin m, (h i - h (i + 1)) = 0 := by
      rw [Finset.sum_sub_distrib, sub_eq_zero]
      exact (Fintype.sum_equiv (Equiv.addRight 1) _ _ (fun _ => rfl)).symm
    have : W j - W j' = 0 := by
      simp only [W, ← Finset.sum_sub_distrib, key, hsum]
    linarith
  -- all columns have the same total slope
  have hall : ∀ (k : ℕ) (hk : k < n), W ⟨k, hk⟩ = W ⟨0, by omega⟩ := by
    intro k
    induction k with
    | zero => intro _; rfl
    | succ k ih =>
      intro hk
      rw [← ih (by omega)]
      exact (step ⟨k, by omega⟩ ⟨k + 1, hk⟩ rfl).symm
  -- the twisted gluing reverses the orientation
  have hwrap : W ⟨n - 1, by omega⟩ + W ⟨0, by omega⟩ = 0 := by
    set l : Fin n := ⟨n - 1, by omega⟩
    set z : Fin n := ⟨0, by omega⟩
    have hl : (l : ℕ) + 1 = n := by simp [l]; omega
    have hz : (z : ℕ) = 0 := rfl
    let g : Fin m → ℤ := fun i => slope (c (i, l)) (c (-i, z))
    have key : ∀ i : Fin m, slope (c (i, l)) (c (i + 1, l)) +
        slope (c (-(i + 1), z)) (c (-(i + 1) + 1, z)) = g i - g (i + 1) := by
      intro i
      have e1 : -(i + 1) + 1 = -i := by abel
      have a1 := klein_adj_vert hm3 i l
      have a2 := klein_adj_wrap hn (i + 1) l z hl hz
      have a3 := klein_adj_vert hm3 (-(i + 1)) z
      rw [e1] at a3
      have a4 := klein_adj_wrap hn i l z hl hz
      have hf := slope_face (c (i, l)) (c (i + 1, l)) (c (-(i + 1), z)) (c (-i, z))
        (hc a1) (hc a2) (hc a3) (hc a4.symm)
      have s1 := slope_swap _ _ (hc a4)
      simp only [g, e1]
      linarith
    have hsum : ∑ i : Fin m, (g i - g (i + 1)) = 0 := by
      rw [Finset.sum_sub_distrib, sub_eq_zero]
      exact (Fintype.sum_equiv (Equiv.addRight 1) _ _ (fun _ => rfl)).symm
    have hW0 : ∑ i : Fin m, slope (c (-(i + 1), z)) (c (-(i + 1) + 1, z)) = W z := by
      exact Fintype.sum_equiv ((Equiv.addRight 1).trans (Equiv.neg _)) _ _ (fun i => rfl)
    rw [← hW0, ← hsum]
    simp only [W, l, z, ← Finset.sum_add_distrib, key]
  have h0 : W ⟨0, by omega⟩ = 0 := by
    have := hall (n - 1) (by omega)
    linarith
  -- but the total slope of a column is odd
  have hodd : Odd (W ⟨0, by omega⟩) := by
    simp only [W, slope_eq, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    obtain ⟨t, ht⟩ := hm
    refine ⟨∑ i : Fin m, (if c (i + 1, ⟨0, by omega⟩) = c (i, ⟨0, by omega⟩) + 1 then 1 else 0)
      - t - 1, ?_⟩
    have hm' : (m : ℤ) = 2 * t + 1 := by exact_mod_cast ht
    linear_combination -hm'
  rw [h0] at hodd
  exact absurd hodd (by decide)

/-! ### The column shift: an automorphism of the Klein bottle grid -/

section Shift

variable {m n : ℕ}

/-- Shift one column to the right; the last column goes to the first one with the reflection
`i ↦ -i`. This is an automorphism of `klein m n` (`kshift_adj_iff`) of order `2n`. -/
def kshift (p : Fin m × Fin n) : Fin m × Fin n :=
  if h : (p.2 : ℕ) + 1 < n then (p.1, ⟨p.2 + 1, h⟩)
  else (-p.1, ⟨0, Nat.zero_lt_of_lt p.2.isLt⟩)

lemma kshift_of_lt {i : Fin m} {j : Fin n} (h : (j : ℕ) + 1 < n) :
    kshift (i, j) = (i, ⟨j + 1, h⟩) := dite_eq_left h

lemma kshift_of_eq {i : Fin m} {j : Fin n} (h : (j : ℕ) + 1 = n) :
    kshift (i, j) = (-i, ⟨0, by omega⟩) := dite_eq_right (by show ¬ ((j : ℕ) + 1 < n); omega)

lemma kshift_iterate_of_lt (i : Fin m) (j : Fin n) (t : ℕ) (h : (j : ℕ) + t < n) :
    kshift^[t] (i, j) = (i, ⟨j + t, h⟩) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [Function.iterate_succ_apply', ih (by omega), kshift_of_lt (by simp; omega)]
    rfl

lemma kshift_iterate_wrap (i : Fin m) (j : Fin n) :
    kshift^[n - j] (i, j) = (-i, ⟨0, Nat.zero_lt_of_lt j.isLt⟩) := by
  obtain ⟨t, ht⟩ : ∃ t, n - j = t + 1 := ⟨n - j - 1, by omega⟩
  rw [ht, Function.iterate_succ_apply', kshift_iterate_of_lt _ _ _ (by omega),
    kshift_of_eq (by simp; omega)]

lemma kshift_iterate_two_mul (p : Fin m × Fin n) : kshift^[2 * n] p = p := by
  obtain ⟨i, j⟩ := p
  have h1 : 2 * n = j + (n + (n - j)) := by omega
  have h2 := kshift_iterate_wrap (-i) (⟨0, Nat.zero_lt_of_lt j.isLt⟩ : Fin n)
  simp only [Nat.sub_zero, neg_neg] at h2
  rw [h1, Function.iterate_add_apply, Function.iterate_add_apply, kshift_iterate_wrap, h2,
    kshift_iterate_of_lt _ _ _ (by simp)]
  simp

/-- Adjacency in the Klein bottle grid, by cases. -/
lemma klein_adj_iff {i i' : Fin (m + 2)} {j j' : Fin n} :
    (klein (m + 2) n).Adj (i, j) (i', j') ↔
      (j = j' ∧ (i - i' = 1 ∨ i' - i = 1)) ∨
      (i = i' ∧ ((j : ℕ) + 1 = j' ∨ (j' : ℕ) + 1 = j)) ∨
      ((i, j) ≠ (i', j') ∧ (((j : ℕ) + 1 = n ∧ (j' : ℕ) = 0 ∧ i' = -i) ∨
        ((j' : ℕ) + 1 = n ∧ (j : ℕ) = 0 ∧ i = -i'))) := by
  simp only [klein, kleinWrap, sup_adj, boxProd_adj, cycleGraph_adj, pathGraph_adj, fromRel_adj]
  constructor
  · rintro ((⟨h1, h2⟩ | ⟨h1, h2⟩) | h)
    · exact Or.inl ⟨h2, h1⟩
    · exact Or.inr (Or.inl ⟨h2, h1⟩)
    · exact Or.inr (Or.inr h)
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩ | h)
    · exact Or.inl (Or.inl ⟨h2, h1⟩)
    · exact Or.inl (Or.inr ⟨h2, h1⟩)
    · exact Or.inr h

/-- The column shift preserves adjacency. -/
lemma kshift_adj (hn : 2 ≤ n) {p q : Fin (m + 2) × Fin n} (h : (klein (m + 2) n).Adj p q) :
    (klein (m + 2) n).Adj (kshift p) (kshift q) := by
  -- one-directional cases; the reverse ones follow by symmetry
  have hor : ∀ (a : Fin (m + 2)) (j j' : Fin n), (j : ℕ) + 1 = j' →
      (klein (m + 2) n).Adj (kshift (a, j)) (kshift (a, j')) := by
    intro a j j' hj
    rw [kshift_of_lt (by omega)]
    by_cases h2 : (j' : ℕ) + 1 < n
    · rw [kshift_of_lt h2]
      exact klein_adj_horiz _ _ _ (by simp; omega)
    · rw [kshift_of_eq (by omega)]
      exact klein_adj_wrap hn _ _ _ (by simp; omega) rfl
  have wr : ∀ (a : Fin (m + 2)) (j j' : Fin n), (j : ℕ) + 1 = n → (j' : ℕ) = 0 →
      (klein (m + 2) n).Adj (kshift (a, j)) (kshift (-a, j')) := by
    intro a j j' hj hj'
    rw [kshift_of_eq hj, kshift_of_lt (by omega)]
    exact klein_adj_horiz _ _ _ (by simp; omega)
  have ver : ∀ (a b : Fin (m + 2)) (j : Fin n), a - b = 1 →
      (klein (m + 2) n).Adj (kshift (a, j)) (kshift (b, j)) := by
    intro a b j hab
    by_cases h2 : (j : ℕ) + 1 < n
    · rw [kshift_of_lt h2, kshift_of_lt h2, klein_adj_iff]
      exact Or.inl ⟨rfl, Or.inl hab⟩
    · rw [kshift_of_eq (by omega), kshift_of_eq (by omega), klein_adj_iff]
      exact Or.inl ⟨rfl, Or.inr (by rw [← hab]; abel)⟩
  obtain ⟨i, j⟩ := p
  obtain ⟨i', j'⟩ := q
  rw [klein_adj_iff] at h
  rcases h with ⟨rfl, h | h⟩ | ⟨rfl, h | h⟩ | ⟨-, ⟨h1, h2, rfl⟩ | ⟨h1, h2, rfl⟩⟩
  · exact ver _ _ _ h
  · exact (ver _ _ _ h).symm
  · exact hor _ _ _ h
  · exact (hor _ _ _ h).symm
  · exact wr _ _ _ h1 h2
  · exact (wr _ _ _ h1 h2).symm

lemma kshift_iterate_adj (hn : 2 ≤ n) (t : ℕ) {p q : Fin (m + 2) × Fin n}
    (h : (klein (m + 2) n).Adj p q) : (klein (m + 2) n).Adj (kshift^[t] p) (kshift^[t] q) := by
  induction t with
  | zero => exact h
  | succ t ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    exact kshift_adj hn ih

/-- The column shift is an automorphism. -/
lemma kshift_adj_iff (hn : 2 ≤ n) {p q : Fin (m + 2) × Fin n} :
    (klein (m + 2) n).Adj (kshift p) (kshift q) ↔ (klein (m + 2) n).Adj p q := by
  refine ⟨fun h => ?_, kshift_adj hn⟩
  have := kshift_iterate_adj hn (2 * n - 1) h
  rwa [← Function.iterate_succ_apply, ← Function.iterate_succ_apply,
    show (2 * n - 1).succ = 2 * n by omega, kshift_iterate_two_mul,
    kshift_iterate_two_mul] at this

lemma kshift_iterate_adj_iff (hn : 2 ≤ n) (t : ℕ) {p q : Fin (m + 2) × Fin n} :
    (klein (m + 2) n).Adj (kshift^[t] p) (kshift^[t] q) ↔ (klein (m + 2) n).Adj p q := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', kshift_adj_iff hn, ih]

/-- The column shift as a permutation. -/
def kshiftEquiv (n : ℕ) (hn : 0 < n) : Equiv.Perm (Fin m × Fin n) where
  toFun := kshift
  invFun := kshift^[2 * n - 1]
  left_inv p := by
    rw [← Function.iterate_succ_apply, show (2 * n - 1).succ = 2 * n by omega,
      kshift_iterate_two_mul]
  right_inv p := by
    show kshift (kshift^[2 * n - 1] p) = p
    rw [← Function.iterate_succ_apply' kshift, show (2 * n - 1).succ = 2 * n by omega,
      kshift_iterate_two_mul]

@[simp] lemma coe_kshiftEquiv_pow (hn : 0 < n) (t : ℕ) :
    ⇑((kshiftEquiv (m := m) n hn) ^ t) = kshift^[t] := by
  rw [← Equiv.Perm.iterate_eq_pow]
  rfl

/-- Every vertex can be shifted to any prescribed column. -/
lemma exists_kshift_iterate_col (i : Fin m) (j c : Fin n) :
    ∃ t, ∃ i', kshift^[t] (i, j) = (i', c) := by
  by_cases h : (j : ℕ) ≤ c
  · refine ⟨c - j, i, ?_⟩
    rw [kshift_iterate_of_lt _ _ _ (by omega)]
    exact Prod.ext rfl (Fin.ext (by simp; omega))
  · refine ⟨c + (n - j), -i, ?_⟩
    rw [Function.iterate_add_apply, kshift_iterate_wrap, kshift_iterate_of_lt _ _ _ (by simp)]
    exact Prod.ext rfl (Fin.ext (by simp))
  
end Shift

/-! ### The cylinder `C_m □ P_k` inside the Klein bottle grid -/

/-- The cylinder `C_m □ P_k`: the Klein bottle grid without its twisted wrap-around edges. -/
def cyl (m k : ℕ) : SimpleGraph (Fin m × Fin k) := cycleGraph m □ pathGraph k

lemma cyl_le_klein (m k : ℕ) : cyl m k ≤ klein m k := le_sup_left

section Distances

variable {m k : ℕ}

lemma cyl_col_lipschitz : ∀ x y : Fin (m + 2) × Fin k, (cyl (m + 2) k).Adj x y →
    (y.2 : ℕ) ≤ x.2 + 1 := by
  intro x y h
  rcases h with ⟨_, h⟩ | ⟨h, _⟩
  · rw [h]; omega
  · rw [pathGraph_adj] at h; omega

lemma cyl_col'_lipschitz : ∀ x y : Fin (m + 2) × Fin k, (cyl (m + 2) k).Adj x y →
    k - 1 - (y.2 : ℕ) ≤ k - 1 - x.2 + 1 := by
  intro x y h
  rcases h with ⟨_, h⟩ | ⟨h, _⟩
  · rw [h]; omega
  · rw [pathGraph_adj] at h; omega

/-- A node in column `0` is at distance at least `col u` from `u`. -/
lemma cyl_edist_col_zero (u a : Fin (m + 2) × Fin k) (ha : (a.2 : ℕ) = 0) :
    ((u.2 : ℕ) : ℕ∞) ≤ (cyl (m + 2) k).edist u a := by
  have := le_add_edist_of_lipschitz cyl_col_lipschitz a u
  rw [ha, edist_comm] at this
  simpa using this

/-- A node in column `k - 1` is at distance at least `k - 1 - col u` from `u`. -/
lemma cyl_edist_col_last (u a : Fin (m + 2) × Fin k) (ha : (a.2 : ℕ) + 1 = k) :
    ((k - 1 - u.2 : ℕ) : ℕ∞) ≤ (cyl (m + 2) k).edist u a := by
  have := le_add_edist_of_lipschitz cyl_col'_lipschitz a u
  rw [show k - 1 - (a.2 : ℕ) = 0 by omega, edist_comm] at this
  simpa using this

end Distances

/-- Seen from a node `u` with `r ≤ col u ≤ k - 1 - r` (and one inequality strict), `H_k` and the
Klein bottle grid `klein (m + 2) k` have the same labelled ball of radius `r`. -/
lemma ballAgree_klein_cyl {m k r : ℕ} (u : Fin (m + 2) × Fin k) (h₁ : r ≤ (u.2 : ℕ))
    (h₂ : r ≤ k - 1 - (u.2 : ℕ)) (h₃ : r < (u.2 : ℕ) ∨ r < k - 1 - (u.2 : ℕ)) :
    BallAgree (klein (m + 2) k) (cyl (m + 2) k) u r := by
  -- a deleted edge is a twisted wrap-around edge
  have wrap : ∀ a b, (klein (m + 2) k).Adj a b → ¬ (cyl (m + 2) k).Adj a b →
      ((a.2 : ℕ) + 1 = k ∧ (b.2 : ℕ) = 0) ∨ ((b.2 : ℕ) + 1 = k ∧ (a.2 : ℕ) = 0) := by
    intro a b hab hn
    rcases hab with h | h
    · exact absurd h hn
    · rw [kleinWrap, fromRel_adj] at h
      rcases h.2 with ⟨h1, h2, _⟩ | ⟨h1, h2, _⟩
      · exact Or.inl ⟨h1, h2⟩
      · exact Or.inr ⟨h1, h2⟩
  have end0 := cyl_edist_col_zero (k := k) u
  have endl := cyl_edist_col_last (k := k) u
  apply ballAgree_of_le (cyl_le_klein (m + 2) k)
  · intro a b hab hn
    rcases wrap a b hab hn with ⟨h1, _⟩ | ⟨_, h2⟩
    · exact le_trans (by exact_mod_cast h₂) (endl a h1)
    · exact le_trans (by exact_mod_cast h₁) (end0 a h2)
  · intro a b hab hn
    rcases wrap a b hab hn with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rcases h₃ with h | h
      · exact Or.inr (lt_of_lt_of_le (by exact_mod_cast h) (end0 b h2))
      · exact Or.inl (lt_of_lt_of_le (by exact_mod_cast h) (endl a h1))
    · rcases h₃ with h | h
      · exact Or.inl (lt_of_lt_of_le (by exact_mod_cast h) (end0 a h2))
      · exact Or.inr (lt_of_lt_of_le (by exact_mod_cast h) (endl b h1))

/-- The column of `kshift p` only depends on the column of `p`. -/
lemma kshift_iterate_snd {m n : ℕ} (t : ℕ) (i i' : Fin m) (j : Fin n) :
    (kshift^[t] (i, j)).2 = (kshift^[t] (i', j)).2 := by
  induction t generalizing i i' j with
  | zero => rfl
  | succ t ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
    by_cases h : (j : ℕ) + 1 < n
    · rw [kshift_of_lt h, kshift_of_lt h]; exact ih _ _ _
    · rw [kshift_of_eq (by omega), kshift_of_eq (by omega)]; exact ih _ _ _

/-- In `klein (m + 2) k`, every edge is vertical or of the form `{p, kshift p}`. -/
lemma klein_adj_cases {m k : ℕ} {p q : Fin (m + 2) × Fin k} (h : (klein (m + 2) k).Adj p q) :
    p.2 = q.2 ∨ q = kshift p ∨ p = kshift q := by
  obtain ⟨i, j⟩ := p
  obtain ⟨i', j'⟩ := q
  rw [klein_adj_iff] at h
  rcases h with ⟨h, _⟩ | ⟨rfl, h | h⟩ | ⟨-, ⟨h1, h2, rfl⟩ | ⟨h1, h2, rfl⟩⟩
  · exact Or.inl h
  · right; left
    rw [kshift_of_lt (by omega)]
    exact Prod.ext rfl (Fin.ext (by simp; omega))
  · right; right
    rw [kshift_of_lt (by omega)]
    exact Prod.ext rfl (Fin.ext (by simp; omega))
  · right; left
    rw [kshift_of_eq h1]
    exact Prod.ext rfl (Fin.ext (by simp; omega))
  · right; right
    rw [kshift_of_eq h1]
    exact Prod.ext rfl (Fin.ext (by simp; omega))

/-- The views needed by `not_colours_of_views`, for an edge `{p, q}` with `q` vertical from `p` or
`q = kshift p`: shift `p` to column `r`. -/
lemma cyl_view {m k r : ℕ} (hk : 2 * r + 2 ≤ k) {V : Type*} (e₂ : (Fin (m + 2) × Fin k) ↪ V)
    {p q : Fin (m + 2) × Fin k} (hpq : (klein (m + 2) k).Adj p q) (hcase : p.2 = q.2 ∨ q = kshift p) :
    ∃ σ : Equiv.Perm (Fin (m + 2) × Fin k), (cyl (m + 2) k).Adj (σ p) (σ q) ∧
      ((σ p).2 : ℕ) = r ∧ (((σ q).2 : ℕ) = r ∨ ((σ q).2 : ℕ) = r + 1) ∧
      BallAgree ((cyl (m + 2) k).map (σ.symm.toEmbedding.trans e₂)) ((klein (m + 2) k).map e₂) (e₂ p) r ∧
      BallAgree ((cyl (m + 2) k).map (σ.symm.toEmbedding.trans e₂)) ((klein (m + 2) k).map e₂) (e₂ q) r := by
  have hk0 : 0 < k := by omega
  have hk2 : 2 ≤ k := by omega
  obtain ⟨t, i', ht⟩ := exists_kshift_iterate_col p.1 p.2 (⟨r, by omega⟩ : Fin k)
  let σ : Equiv.Perm (Fin (m + 2) × Fin k) := kshiftEquiv k hk0 ^ t
  have hσ : ∀ a, σ a = kshift^[t] a := fun a => by simp [σ]
  have hσadj : ∀ a b, (klein (m + 2) k).Adj (σ a) (σ b) ↔ (klein (m + 2) k).Adj a b := fun a b => by
    rw [hσ, hσ]; exact kshift_iterate_adj_iff hk2 t
  have hx : σ p = (i', ⟨r, by omega⟩) := by rw [hσ]; exact ht
  have hadj : (klein (m + 2) k).Adj (σ p) (σ q) := (hσadj p q).2 hpq
  -- position of the image of `q`, and the image edge is an edge of `H_k`
  have hy : ((σ q).2 = ⟨r, by omega⟩ ∨ (σ q).2 = ⟨r + 1, by omega⟩) ∧
      (cyl (m + 2) k).Adj (σ p) (σ q) := by
    rcases hcase with h | rfl
    · have hq : q = (q.1, p.2) := Prod.ext rfl h.symm
      have h2 : (σ q).2 = ⟨r, by omega⟩ := by
        rw [hσ, hq, kshift_iterate_snd t q.1 p.1 p.2, ht]
      refine ⟨Or.inl h2, ?_⟩
      rcases hadj with h' | h'
      · exact h'
      · exfalso
        rw [kleinWrap, fromRel_adj, hx, h2] at h'
        rcases h'.2 with ⟨h1, h3⟩ | ⟨h1, h3⟩ <;> simp at h1 h3 <;> omega
    · have h2 : σ (kshift p) = kshift (i', ⟨r, by omega⟩) := by
        rw [hσ, ← Function.iterate_succ_apply, Function.iterate_succ_apply', ← hσ, hx]
      rw [kshift_of_lt (i := i') (j := ⟨r, by omega⟩) (by show r + 1 < k; omega)] at h2
      rw [h2, hx]
      refine ⟨Or.inr rfl, ?_⟩
      show (cycleGraph (m + 2) □ pathGraph k).Adj _ _
      rw [boxProd_adj, pathGraph_adj]
      exact Or.inr ⟨Or.inl rfl, rfl⟩
  have hH := hy.2
  replace hy := hy.1
  let e : (Fin (m + 2) × Fin k) ↪ V := σ.symm.toEmbedding.trans e₂
  have he : ∀ a, e (σ a) = e₂ a := fun a => by simp [e]
  have hmap := map_trans_eq_of_aut σ hσadj e₂
  refine ⟨σ, hH, by rw [hx], by rcases hy with h | h <;> rw [h] <;> simp, ?_, ?_⟩
  · rw [← he p, ← hmap]
    refine (BallAgree.map e ?_)
    refine (ballAgree_klein_cyl _ ?_ ?_ ?_).symm <;> rw [hx] <;> simp <;> omega
  · rw [← he q, ← hmap]
    refine (BallAgree.map e ?_)
    refine (ballAgree_klein_cyl _ ?_ ?_ ?_).symm <;> rcases hy with h | h <;> rw [h] <;>
      simp <;> omega


end Podc.SparseColoringLB
