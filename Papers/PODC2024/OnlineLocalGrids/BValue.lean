import Papers.PODC2024.OnlineLocalGrids.Defs

/-!
# `a`-values and `b`-values of 3-colourings (§3.1 of Chang–Mishra–Nguyen–Yang–Yeh, PODC 2024)

Colours are `Fin 3 = {0, 1, 2}`; our colour `2` plays the role of the paper's colour `3`, and our
colours `0, 1` play the roles of the paper's `1, 2` (so `aval` below is the paper's `a`, see
`differencies.md`).

* `aval x y` (Definition 3.1), `ind x` (the indicator `i(u)` of colour 3),
* `bval c p` for a walk `p` (Definition 3.2): the sum of `a(c u, c v)` over its darts,
* Lemma 3.3 (`aval_cell`, `bval_four_cycle`), Lemma 3.5 (`bval_parity`, `bval_closed_parity`),
* Lemma 3.4 for (simple) grids, in the stronger form "every closed walk has `b = 0`"
  (`grid_bval_closed`), proved without any Jordan-curve argument via a potential
  (`grid_exists_potential`: `a(c p, c q) = φ q - φ p` on every edge);
* row sums on graphs `G₁ □ C_b` (cylinders and tori): equal on adjacent rows (`rowSum_eq_of_adj`),
  odd for odd `b` (`rowSum_odd`), negated by reflecting the columns (`rowSum_reflect`).
-/

namespace Papers.PODC2024.OnlineLocalGrids

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-- **Definition 3.2** (`b`-value of a directed walk). -/
def bval (c : V → Fin 3) {u v : V} (p : G.Walk u v) : ℤ :=
  (p.darts.map fun d => aval (c d.fst) (c d.snd)).sum

@[simp] lemma bval_nil (c : V → Fin 3) (u : V) : bval c (Walk.nil : G.Walk u u) = 0 := rfl

lemma bval_cons (c : V → Fin 3) {u v w : V} (h : G.Adj u v) (p : G.Walk v w) :
    bval c (Walk.cons h p) = aval (c u) (c v) + bval c p := by
  simp [bval]

lemma bval_append (c : V → Fin 3) {u v w : V} (p : G.Walk u v) (q : G.Walk v w) :
    bval c (p.append q) = bval c p + bval c q := by
  simp [bval, Walk.darts_append]

lemma bval_reverse (c : V → Fin 3) {u v : V} (p : G.Walk u v) :
    bval c p.reverse = - bval c p := by
  induction p with
  | nil => simp
  | cons h p ih =>
    rw [Walk.reverse_cons, bval_append, ih, bval_cons, bval_cons, bval_nil, aval_antisymm]
    ring

lemma abs_bval_le (c : V → Fin 3) {u v : V} (p : G.Walk u v) : |bval c p| ≤ p.length := by
  induction p with
  | nil => simp
  | @cons x y _ h p ih =>
    rw [bval_cons, Walk.length_cons, Nat.cast_add, Nat.cast_one]
    have := abs_aval_le (c x) (c y)
    have := abs_add_le (aval (c x) (c y)) (bval c p)
    linarith

/-- **Lemma 3.3**: a properly coloured closed walk of length 4 has `b`-value `0`. -/
theorem bval_four_cycle {c : V → Fin 3} (hc : IsProper G c) {u : V} (p : G.Walk u u)
    (hp : p.length = 4) : bval c p = 0 := by
  rcases p with _ | ⟨h1, _ | ⟨h2, _ | ⟨h3, _ | ⟨h4, _ | ⟨h5, p⟩⟩⟩⟩⟩ <;> simp at hp
  simp only [bval_cons, bval_nil, add_zero, ← add_assoc]
  exact aval_cell _ _ _ _ (hc _ _ h1) (hc _ _ h2) (hc _ _ h3) (hc _ _ h4)

/-- **Lemma 3.5** (parity of `b`-values of paths): for a proper colouring,
`b(P) ≡ i(u) + i(v) + ℓ (mod 2)`. Holds for all walks. -/
theorem bval_parity {c : V → Fin 3} (hc : IsProper G c) {u v : V} (p : G.Walk u v) :
    bval c p ≡ ind (c u) + ind (c v) + p.length [ZMOD 2] := by
  induction p with
  | nil => simp [Int.ModEq]; omega
  | cons h p ih =>
    have h1 := aval_parity _ _ (hc _ _ h)
    rw [bval_cons, Walk.length_cons, Nat.cast_add, Nat.cast_one]
    rw [Int.modEq_iff_dvd] at *
    omega

/-- **Lemma 3.5** (cycles): a properly coloured closed walk of length `ℓ` has `b ≡ ℓ (mod 2)`. -/
theorem bval_closed_parity {c : V → Fin 3} (hc : IsProper G c) {u : V} (p : G.Walk u u) :
    bval c p ≡ p.length [ZMOD 2] := by
  have := bval_parity hc p
  rw [Int.modEq_iff_dvd] at *
  omega

/-! ### Simple grids: Lemma 3.4 via a potential -/

/-- A colouring of the grid extended by `0` to all of `ℕ × ℕ`. -/
private def extC {a b : ℕ} (c : Fin a × Fin b → Fin 3) (i j : ℕ) : Fin 3 :=
  if h : i < a ∧ j < b then c (⟨i, h.1⟩, ⟨j, h.2⟩) else 0

private lemma extC_eq {a b : ℕ} (c : Fin a × Fin b → Fin 3) {i j : ℕ} (hi : i < a) (hj : j < b) :
    extC c i j = c (⟨i, hi⟩, ⟨j, hj⟩) := by
  simp [extC, hi, hj]

/-- The potential: walk along row `0` to column `j`, then down column `j` to row `i`. -/
private def gridPot {a b : ℕ} (c : Fin a × Fin b → Fin 3) (i j : ℕ) : ℤ :=
  (∑ k ∈ Finset.range j, aval (extC c 0 k) (extC c 0 (k + 1))) +
    ∑ k ∈ Finset.range i, aval (extC c k j) (extC c (k + 1) j)

private lemma gridPot_vert {a b : ℕ} (c : Fin a × Fin b → Fin 3) (i j : ℕ) :
    gridPot c (i + 1) j - gridPot c i j = aval (extC c i j) (extC c (i + 1) j) := by
  simp only [gridPot, Finset.sum_range_succ]; ring

private lemma gridPot_horiz {a b : ℕ} {c : Fin a × Fin b → Fin 3} (hc : IsProper (grid a b) c)
    {j : ℕ} (hj : j + 1 < b) : ∀ i, i < a →
    gridPot c i (j + 1) - gridPot c i j = aval (extC c i j) (extC c i (j + 1)) := by
  intro i
  induction i with
  | zero => intro _; simp only [gridPot, Finset.sum_range_succ, Finset.range_zero,
      Finset.sum_empty]; ring
  | succ i ih =>
    intro hi
    have ih := ih (by omega)
    have hv1 := gridPot_vert c i j
    have hv2 := gridPot_vert c i (j + 1)
    rw [extC_eq c (i := i) (by omega) (by omega), extC_eq c (i := i + 1) hi (by omega),
      extC_eq c (i := i) (j := j + 1) (by omega) hj,
      extC_eq c (i := i + 1) (j := j + 1) hi hj] at *
    have cell := aval_cell (c (⟨i, by omega⟩, ⟨j, by omega⟩)) (c (⟨i, by omega⟩, ⟨j + 1, hj⟩))
      (c (⟨i + 1, hi⟩, ⟨j + 1, hj⟩)) (c (⟨i + 1, hi⟩, ⟨j, by omega⟩))
      (hc _ _ (by simp [boxProd_adj, pathGraph_adj]))
      (hc _ _ (by simp [boxProd_adj, pathGraph_adj]))
      (hc _ _ (by simp [boxProd_adj, pathGraph_adj]))
      (hc _ _ (by simp [boxProd_adj, pathGraph_adj]))
    have e1 := aval_antisymm (c (⟨i + 1, hi⟩, ⟨j + 1, hj⟩)) (c (⟨i + 1, hi⟩, ⟨j, by omega⟩))
    have e2 := aval_antisymm (c (⟨i, by omega⟩, ⟨j, by omega⟩)) (c (⟨i + 1, hi⟩, ⟨j, by omega⟩))
    linarith

/-- In a properly 3-coloured grid the `a`-values are a gradient. -/
theorem grid_exists_potential {a b : ℕ} {c : Fin a × Fin b → Fin 3} (hc : IsProper (grid a b) c) :
    ∃ φ : Fin a × Fin b → ℤ, ∀ p q, (grid a b).Adj p q → aval (c p) (c q) = φ q - φ p := by
  refine ⟨fun p => gridPot c p.1 p.2, ?_⟩
  rintro ⟨⟨i, hi⟩, ⟨j, hj⟩⟩ ⟨⟨i', hi'⟩, ⟨j', hj'⟩⟩ h
  simp only [boxProd_adj, pathGraph_adj, Fin.mk.injEq] at h
  rcases h with ⟨h | h, rfl⟩ | ⟨h | h, rfl⟩
  · subst h
    rw [gridPot_vert, extC_eq c hi hj, extC_eq c hi' hj]
  · subst h
    rw [← neg_sub, gridPot_vert, extC_eq c hi hj, extC_eq c hi' hj, aval_antisymm]
  · subst h
    rw [gridPot_horiz hc hj' i hi, extC_eq c hi hj, extC_eq c hi hj']
  · subst h
    rw [← neg_sub, gridPot_horiz hc hj i hi, extC_eq c hi hj, extC_eq c hi hj', aval_antisymm]

/-- **Lemma 3.4** (strengthened): in a properly 3-coloured grid, every closed walk (in particular
every simple directed cycle) has `b`-value `0`. -/
theorem grid_bval_closed {a b : ℕ} {c : Fin a × Fin b → Fin 3} (hc : IsProper (grid a b) c)
    {u : Fin a × Fin b} (p : (grid a b).Walk u u) : bval c p = 0 := by
  obtain ⟨φ, hφ⟩ := grid_exists_potential hc
  suffices ∀ {v w} (q : (grid a b).Walk v w), bval c q = φ w - φ v by simpa using this p
  intro v w q
  induction q with
  | nil => simp
  | cons h q ih => rw [bval_cons, ih, hφ _ _ h]; ring

/-! ### Cylinders and tori: row sums -/

section Rows

variable {α : Type*} {G₁ : SimpleGraph α} {b : ℕ} [NeZero b]

/-- The `b`-value of row `i` of `G₁ □ C_b`, traversed in increasing column order. -/
def rowSum (c : α × Fin b → Fin 3) (i : α) : ℤ :=
  ∑ j : Fin b, aval (c (i, j)) (c (i, j + 1))

lemma cycleGraph_adj_add_one (hb : 2 ≤ b) (j : Fin b) : (cycleGraph b).Adj j (j + 1) := by
  obtain ⟨n, rfl⟩ : ∃ n, b = n + 2 := ⟨b - 2, by omega⟩
  rw [cycleGraph_adj]
  right
  simp

/-- Rows connected by an edge have the same row sum (sum of Lemma 3.3 over the cells between
them). Needs `b ≥ 2` so that `j ~ j + 1` in `C_b`. -/
theorem rowSum_eq_of_adj (hb : 2 ≤ b) {c : α × Fin b → Fin 3} (hc : IsProper (G₁ □ cycleGraph b) c)
    {i i' : α} (h : G₁.Adj i i') : rowSum c i = rowSum c i' := by
  have cell : ∀ j : Fin b, aval (c (i, j)) (c (i, j + 1)) + aval (c (i, j + 1)) (c (i', j + 1)) +
      aval (c (i', j + 1)) (c (i', j)) + aval (c (i', j)) (c (i, j)) = 0 := fun j =>
    aval_cell _ _ _ _ (hc _ _ (by simp [boxProd_adj, cycleGraph_adj_add_one hb]))
      (hc _ _ (by simp [boxProd_adj, h])) (hc _ _ (by simp [boxProd_adj, (cycleGraph_adj_add_one hb j).symm]))
      (hc _ _ (by simp [boxProd_adj, h.symm]))
  have hsum := Finset.sum_eq_zero (s := Finset.univ) fun j _ => cell j
  simp only [Finset.sum_add_distrib] at hsum
  have hre : ∑ j : Fin b, aval (c (i, j + 1)) (c (i', j + 1)) = ∑ j : Fin b, aval (c (i, j)) (c (i', j)) :=
    Equiv.sum_comp (Equiv.addRight (1 : Fin b)) (fun j => aval (c (i, j)) (c (i', j)))
  have h2 : ∑ j : Fin b, aval (c (i', j + 1)) (c (i', j)) = - rowSum c i' := by
    simp only [rowSum, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun j _ => aval_antisymm _ _
  have h3 : ∑ j : Fin b, aval (c (i', j)) (c (i, j)) = - ∑ j : Fin b, aval (c (i, j)) (c (i', j)) := by
    simp only [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun j _ => aval_antisymm _ _
  unfold rowSum
  unfold rowSum at h2
  linarith

/-- Rows in the same connected component of `G₁` have the same row sum. -/
theorem rowSum_eq_of_reachable (hb : 2 ≤ b) {c : α × Fin b → Fin 3}
    (hc : IsProper (G₁ □ cycleGraph b) c) {i i' : α} (h : G₁.Reachable i i') :
    rowSum c i = rowSum c i' := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => rfl
  | cons h _ ih => exact (rowSum_eq_of_adj hb hc h).trans ih

/-- **Lemma 3.5** for a row cycle: an odd row has an odd row sum. -/
theorem rowSum_odd (hb : 3 ≤ b) (hodd : Odd b) {c : α × Fin b → Fin 3}
    (hc : IsProper (G₁ □ cycleGraph b) c) (i : α) : Odd (rowSum c i) := by
  have hb2 : 2 ≤ b := by omega
  have hdvd : ∀ j : Fin b,
      (2 : ℤ) ∣ aval (c (i, j)) (c (i, j + 1)) - ind (c (i, j)) - ind (c (i, j + 1)) - 1 := by
    intro j
    have := (aval_parity _ _ (hc (i, j) (i, j + 1)
      (by simp [boxProd_adj, cycleGraph_adj_add_one hb2]))).symm
    rw [Int.modEq_iff_dvd] at this
    have e : aval (c (i, j)) (c (i, j + 1)) - ind (c (i, j)) - ind (c (i, j + 1)) - 1 =
      aval (c (i, j)) (c (i, j + 1)) - (ind (c (i, j)) + ind (c (i, j + 1)) + 1) := by ring
    rw [e]; exact this
  have hs := Finset.dvd_sum (s := Finset.univ) fun j _ => hdvd j
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one] at hs
  have hre : ∑ j : Fin b, ind (c (i, j + 1)) = ∑ j : Fin b, ind (c (i, j)) :=
    Equiv.sum_comp (Equiv.addRight (1 : Fin b)) (fun j => ind (c (i, j)))
  rw [hre] at hs
  obtain ⟨k, hk⟩ := hodd
  unfold rowSum
  generalize ∑ j : Fin b, aval (c (i, j)) (c (i, j + 1)) = R at hs ⊢
  generalize ∑ j : Fin b, ind (c (i, j)) = S at hs
  subst hk
  push_cast at hs
  rw [Int.odd_iff]
  omega

/-- Reflecting the columns (`j ↦ -j`) of a row negates its row sum. -/
theorem rowSum_reflect (c : α × Fin b → Fin 3) (i : α) :
    rowSum (fun p => c (p.1, -p.2)) i = - rowSum c i := by
  unfold rowSum
  rw [← Finset.sum_neg_distrib]
  refine (Fintype.sum_equiv ((Equiv.addRight (1 : Fin b)).trans (Equiv.neg _)) _ _ ?_).symm
  intro j
  have e : -1 + (j + 1) = j := by abel
  simp only [Equiv.trans_apply, Equiv.coe_addRight, Equiv.neg_apply, neg_neg, neg_add_rev, e]
  rw [aval_antisymm, neg_neg]

end Rows

end Papers.PODC2024.OnlineLocalGrids
