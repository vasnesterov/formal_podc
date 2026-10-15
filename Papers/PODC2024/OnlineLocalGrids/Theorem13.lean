import Papers.PODC2024.OnlineLocalGrids.BValue

/-!
# Theorem 1.3: `Ω(√n)` for 3-colouring cylindrical and toroidal grids (§3.3)

Chang–Mishra–Nguyen–Yang–Yeh, PODC 2024. Host graphs: `cylinder a b = P_a □ C_b` (rows `Fin a`
form a path, every row is a cycle of length `b`) and `torus a b = C_a □ C_b`.

The adversary reveals two whole rows `r₁ = T` and `r₂ = 3T + 2` first. Their radius-`T`
neighbourhoods (rows `[0, 2T]` and `[2T+2, 4T+2]`) are disjoint and non-adjacent, so reflecting the
columns (`j ↦ -j`) of all rows `≥ 2T + 2` is invisible to the algorithm. In both runs the row sums
(`b`-values of the row cycles) of `r₁` and `r₂` are equal (`rowSum_eq_of_reachable`); the reflection
fixes row `r₁` and negates the row sum of `r₂` (`rowSum_reflect`), so the row sum is `0`,
contradicting its oddness (`rowSum_odd`, `b` odd).

For the torus the two bands must also be separated across the wrap-around, which needs one more
row: `4T + 4 ≤ a` (instead of `4T + 3 ≤ a` for the cylinder).
-/

namespace Papers.PODC2024.OnlineLocalGrids

open SimpleGraph Cslib.OnlineLocal

/-- The cylindrical grid: rows `Fin a` (a path), columns `Fin b` (a cycle). -/
abbrev cylinder (a b : ℕ) : SimpleGraph (Fin a × Fin b) := pathGraph a □ cycleGraph b

/-- The toroidal grid: rows `Fin a` (a cycle), columns `Fin b` (a cycle). -/
abbrev torus (a b : ℕ) : SimpleGraph (Fin a × Fin b) := cycleGraph a □ cycleGraph b

/-! ### Auxiliary lemmas -/

-- CSLib candidate
/-- The first coordinate of a point of a ball in a box product lies in the ball of the projection. -/
lemma fst_mem_ball_boxProd {α β : Type*} {R : SimpleGraph α} {H : SimpleGraph β}
    {U : Set (α × β)} {k : ℕ} {x : α × β} (hx : x ∈ ball (R □ H) U k) :
    x.1 ∈ ball R (Prod.fst '' U) k := by
  induction k generalizing x with
  | zero => exact ⟨x, hx, rfl⟩
  | succ k ih =>
    rcases hx with hx | ⟨z, hz, hzx⟩
    · exact ball_subset_succ (ih hx)
    · rcases boxProd_adj.1 hzx with ⟨h, _⟩ | ⟨_, h⟩
      · exact mem_ball_succ_of_adj (ih hz) h
      · rw [← h]; exact ball_subset_succ (ih hz)

-- CSLib candidate
/-- Adjacency in a cycle graph, in terms of values. -/
lemma cycleGraph_adj_val {n : ℕ} {x y : Fin n} (h : (cycleGraph n).Adj x y) :
    y.val = x.val + 1 ∨ x.val = y.val + 1 ∨ (x.val = 0 ∧ y.val + 1 = n) ∨
      (y.val = 0 ∧ x.val + 1 = n) := by
  rw [cycleGraph_adj'] at h
  have hx := x.isLt
  have hy := y.isLt
  rcases le_or_gt y x with hxy | hxy <;> rcases le_or_gt x y with hyx | hyx
  · rcases h with h | h
    · rw [Fin.coe_sub_iff_le.2 hxy] at h; omega
    · rw [Fin.coe_sub_iff_le.2 hyx] at h; omega
  · rcases h with h | h
    · rw [Fin.coe_sub_iff_le.2 hxy] at h; omega
    · rw [Fin.coe_sub_iff_lt.2 hyx] at h; omega
  · rcases h with h | h
    · rw [Fin.coe_sub_iff_lt.2 hxy] at h; omega
    · rw [Fin.coe_sub_iff_le.2 hyx] at h; omega
  · exact absurd (hxy.trans hyx) (lt_irrefl _)

/-- Description of a row graph `R` on `Fin a` that is either a path or a cycle. -/
def RowLike {a : ℕ} (R : SimpleGraph (Fin a)) : Prop :=
  ∀ x y : Fin a, R.Adj x y → y.val = x.val + 1 ∨ x.val = y.val + 1 ∨
    (x.val = 0 ∧ y.val + 1 = a) ∨ (y.val = 0 ∧ x.val + 1 = a)

lemma rowLike_pathGraph (a : ℕ) : RowLike (pathGraph a) := fun x y h => by
  rw [pathGraph_adj] at h; omega

lemma rowLike_cycleGraph (a : ℕ) : RowLike (cycleGraph a) := fun _ _ h => cycleGraph_adj_val h

/-- In a path/cycle, a ball of radius `k` around `r` (not reaching the ends) is `[r - k, r + k]`. -/
lemma RowLike.ball_bound {a : ℕ} {R : SimpleGraph (Fin a)} (hR : RowLike R) (r : Fin a) :
    ∀ k, k ≤ r.val → r.val + k < a → ∀ x ∈ ball R {r} k, r.val ≤ x.val + k ∧ x.val ≤ r.val + k := by
  intro k
  induction k with
  | zero => rintro - - x rfl; omega
  | succ k ih =>
    rintro hk1 hk2 x (hx | ⟨z, hz, hzx⟩)
    · have := ih (by omega) (by omega) x hx; omega
    · have := ih (by omega) (by omega) z hz
      have := hR z x hzx
      omega

lemma rowSum_congr {α : Type*} {b : ℕ} [NeZero b] {c c' : α × Fin b → Fin 3} {i i' : α}
    (h : ∀ j, c (i, j) = c' (i', j)) : rowSum c i = rowSum c' i' := by
  unfold rowSum; simp only [h]

/-! ### The reflection -/

section Reflection

variable {a b T : ℕ}

/-- Reflect the columns (`j ↦ -j`) of all rows `≥ 2T + 2`. -/
def reflectFun (T : ℕ) (p : Fin a × Fin b) : Fin a × Fin b :=
  if 2 * T + 2 ≤ p.1.val then (p.1, -p.2) else p

lemma reflectFun_involutive : Function.Involutive (reflectFun (a := a) (b := b) T) := by
  intro p
  unfold reflectFun
  split_ifs with h1 <;> simp_all

/-- The reflection as a permutation of positions. -/
def reflect (T : ℕ) : Equiv.Perm (Fin a × Fin b) :=
  Function.Involutive.toPerm _ (reflectFun_involutive (T := T))

lemma reflect_apply (p : Fin a × Fin b) : reflect T p = reflectFun T p := rfl

lemma reflect_symm_apply (p : Fin a × Fin b) : (reflect T).symm p = reflect T p := by
  rw [Equiv.symm_apply_eq, reflect_apply, reflect_apply, reflectFun_involutive]

lemma cycleGraph_adj_neg [NeZero b] {u v : Fin b} : (cycleGraph b).Adj (-u) (-v) ↔ (cycleGraph b).Adj u v := by
  rw [cycleGraph_adj', cycleGraph_adj', neg_sub_neg, neg_sub_neg, or_comm]

/-- The reflection preserves the edges between rows on the same side, and between rows that are
neither equal nor adjacent. -/
lemma adj_reflect_iff [NeZero b] {R : SimpleGraph (Fin a)} {x y : Fin a × Fin b}
    (h : (2 * T + 2 ≤ x.1.val ↔ 2 * T + 2 ≤ y.1.val) ∨ (x.1 ≠ y.1 ∧ ¬ R.Adj x.1 y.1)) :
    (R □ cycleGraph b).Adj x y ↔ (R □ cycleGraph b).Adj (reflect T x) (reflect T y) := by
  obtain ⟨x1, x2⟩ := x
  obtain ⟨y1, y2⟩ := y
  simp only [reflect_apply, reflectFun] at h ⊢
  rcases h with h | ⟨h1, h2⟩
  · by_cases hx : 2 * T + 2 ≤ x1.val
    · have hy := h.1 hx
      simp only [hx, hy, ite_true, boxProd_adj, neg_inj, cycleGraph_adj_neg]
    · have hy : ¬ 2 * T + 2 ≤ y1.val := fun hy => hx (h.2 hy)
      simp only [hx, hy, ite_false]
  · have : ∀ z w : Fin a × Fin b, z.1 = x1 → w.1 = y1 → ¬ (R □ cycleGraph b).Adj z w := by
      rintro z w rfl rfl hzw
      rcases boxProd_adj.1 hzw with ⟨h, _⟩ | ⟨_, h⟩
      · exact h2 h
      · exact h1 h
    exact iff_of_false (this _ _ rfl rfl) (this _ _ (by split_ifs <;> rfl) (by split_ifs <;> rfl))

end Reflection

/-! ### The main argument -/

/-- **Theorem 1.3**, generic form: for host graphs `R □ C_b` whose row graph `R` is a connected
path-or-cycle in which the bands `[0, 2T]` and `[2T+2, 4T+2]` are non-adjacent, no
deterministic Online-LOCAL algorithm with locality `T` 3-colours the graph when `b` is odd. -/
theorem not_colors_of_rowLike {ι : Type*} [DecidableEq ι] {a b T : ℕ} (R : SimpleGraph (Fin a))
    (hR : RowLike R) (hconn : R.Preconnected)
    (hsep : ∀ x y : Fin a, R.Adj x y → x.val ≤ 2 * T → 2 * T + 2 ≤ y.val → y.val ≤ 4 * T + 2 → False)
    (e : ι ≃ Fin a × Fin b) (ha : 4 * T + 3 ≤ a) (hb : 3 ≤ b) (hodd : Odd b)
    (A : Algorithm ι (Fin 3)) : ¬ A.Colors (R □ cycleGraph b) T := by
  classical
  have : NeZero b := ⟨by omega⟩
  let : Fintype ι := Fintype.ofEquiv _ e.symm
  intro hA
  set G := R □ cycleGraph b with hG
  let r₁ : Fin a := ⟨T, by omega⟩
  let r₂ : Fin a := ⟨3 * T + 2, by omega⟩
  -- the reveal order: rows `r₁` and `r₂` first
  let L : List ι := (Finset.univ : Finset ι).toList
  let row : ι → Prop := fun x => (e x).1 = r₁ ∨ (e x).1 = r₂
  let P : List ι := L.filter fun x => decide (row x)
  let Q : List ι := L.filter fun x => !decide (row x)
  have hP : ∀ x, x ∈ P ↔ row x := by intro x; simp [P, L]
  have hσ : IsOrder (P ++ Q) := by
    refine ⟨List.nodup_append.2 ⟨(Finset.nodup_toList _).filter _, (Finset.nodup_toList _).filter _,
      ?_⟩, fun x => ?_⟩
    · intro x hx y hy hxy
      subst hxy
      simp [P, Q] at hx hy
      exact hy.2 hx.2
    · by_cases h : row x <;> simp [P, Q, L, h]
  -- the positions of the revealed prefix lie in the rows `r₁`, `r₂`
  set U : Set (Fin a × Fin b) := e '' {x | x ∈ P}
  have hU : ∀ u ∈ U, u.1 = r₁ ∨ u.1 = r₂ := by
    rintro _ ⟨x, hx, rfl⟩
    exact (hP x).1 hx
  have hball : ∀ k ≤ T, ∀ x ∈ ball G U k,
      (T ≤ x.1.val + k ∧ x.1.val ≤ T + k) ∨ (3 * T + 2 ≤ x.1.val + k ∧ x.1.val ≤ 3 * T + 2 + k) := by
    intro k hk x hx
    have h1 := fst_mem_ball_boxProd hx
    have hsub : Prod.fst '' U ⊆ {r₁} ∪ {r₂} := by
      rintro _ ⟨u, hu, rfl⟩
      rcases hU u hu with h | h
      · exact Or.inl h
      · exact Or.inr h
    have h2 := ball_mono_set hsub h1
    rw [ball_union] at h2
    rcases h2 with h2 | h2
    · have := hR.ball_bound r₁ k (by simp [r₁]; omega) (by simp [r₁]; omega) _ h2
      left; simp only [r₁] at this; omega
    · have := hR.ball_bound r₂ k (by simp [r₂]; omega) (by simp [r₂]; omega) _ h2
      right; simp only [r₂] at this; omega
  -- sides are preserved along the visible edges
  have hside : ∀ k ≤ T, ∀ x ∈ ball G U k, ∀ y : Fin a × Fin b,
      (k < T ∨ y ∈ ball G U T) →
      (2 * T + 2 ≤ x.1.val ↔ 2 * T + 2 ≤ y.1.val) ∨ (x.1 ≠ y.1 ∧ ¬ R.Adj x.1 y.1) := by
    intro k hk x hx y hy
    by_cases h1 : x.1 = y.1
    · left; rw [h1]
    by_cases h2 : R.Adj x.1 y.1
    · left
      have hxb := hball k hk x hx
      have hxy := hR _ _ h2
      rcases hy with hy | hy
      · omega
      · have hyb := hball T le_rfl y hy
        rcases hxb with hxb | hxb <;> rcases hyb with hyb | hyb
        · omega
        · exact absurd (hsep _ _ h2 (by omega) (by omega) (by omega)) id
        · exact absurd (hsep _ _ h2.symm (by omega) (by omega) (by omega)) id
        · omega
    · exact Or.inr ⟨h1, h2⟩
  have hagree : AgreeOn G (G.comap (reflect T)) U T := by
    refine ⟨fun k hk x hx y => ?_, fun x hx y hy => ?_⟩
    · exact adj_reflect_iff (hside k hk.le x hx y (Or.inl hk))
    · exact adj_reflect_iff (hside T le_rfl x hx y (Or.inr hy))
  have hagree' := agreeOn_comap (G := G) e (reflect T) hagree
  -- the two runs
  set e₂ : ι ≃ Fin a × Fin b := e.trans (reflect T)
  let c₁ : Fin a × Fin b → Fin 3 := fun p => A.label (G.comap e) T (P ++ Q) (e.symm p)
  let c₂ : Fin a × Fin b → Fin 3 := fun p => A.label (G.comap e₂) T (P ++ Q) (e₂.symm p)
  have hc₁ : IsProper G c₁ := fun p q hpq => hA e _ hσ _ _ (by simpa using hpq)
  have hc₂ : IsProper G c₂ := fun p q hpq => hA e₂ _ hσ _ _ (by simpa using hpq)
  -- labels of revealed nodes agree
  have hlab : ∀ x ∈ P, A.label (G.comap e₂) T (P ++ Q) x = A.label (G.comap e) T (P ++ Q) x := by
    intro x hx
    rw [label_append _ _ _ _ hx, label_append _ _ _ _ hx]
    exact (label_eq_of_agreeOn A hagree' x).symm
  have hrow1 : rowSum c₂ r₁ = rowSum c₁ r₁ := by
    refine rowSum_congr fun j => ?_
    have hfix : (reflect T).symm (r₁, j) = (r₁, j) := by
      rw [reflect_symm_apply, reflect_apply, reflectFun]
      split_ifs with h
      · simp only [r₁] at h; omega
      · rfl
    simp only [c₁, c₂, e₂, Equiv.symm_trans_apply, hfix]
    exact hlab _ ((hP _).2 (by simp [row]))
  have hrow2 : rowSum c₂ r₂ = rowSum (fun p => c₁ (p.1, -p.2)) r₂ := by
    refine rowSum_congr fun j => ?_
    have hfix : (reflect T).symm (r₂, j) = (r₂, -j) := by
      rw [reflect_symm_apply, reflect_apply, reflectFun]
      split_ifs with h
      · rfl
      · simp only [r₂] at h; omega
    simp only [c₁, c₂, e₂, Equiv.symm_trans_apply, hfix]
    exact hlab _ ((hP _).2 (by simp [row]))
  have hb2 : 2 ≤ b := by omega
  have e1 := rowSum_eq_of_reachable hb2 hc₁ (hconn r₁ r₂)
  have e2 := rowSum_eq_of_reachable hb2 hc₂ (hconn r₁ r₂)
  rw [rowSum_reflect] at hrow2
  have hzero : rowSum c₁ r₂ = 0 := by linarith
  have hodd' := rowSum_odd hb hodd hc₁ r₂
  rw [hzero] at hodd'
  exact absurd hodd' (by decide)

/-- **Theorem 1.3** (cylindrical grids). On the `a × b` cylinder (rows form a path of length `a`,
each row is a cycle of odd length `b ≥ 3`), no deterministic Online-LOCAL algorithm with locality
`T` finds a proper 3-colouring if `a ≥ 4T + 3`. -/
theorem theorem_1_3_cylinder {ι : Type*} [DecidableEq ι] {a b T : ℕ} (e : ι ≃ Fin a × Fin b)
    (ha : 4 * T + 3 ≤ a) (hb : 3 ≤ b) (hodd : Odd b) (A : Algorithm ι (Fin 3)) :
    ¬ A.Colors (cylinder a b) T :=
  not_colors_of_rowLike _ (rowLike_pathGraph a) (pathGraph_preconnected a)
    (fun x y h hx hy _ => by rw [pathGraph_adj] at h; omega) e ha hb hodd A

/-- **Theorem 1.3** (toroidal grids). On the `a × b` torus with `b ≥ 3` odd, no deterministic
Online-LOCAL algorithm with locality `T` finds a proper 3-colouring if `a ≥ 4T + 4`. -/
theorem theorem_1_3_torus {ι : Type*} [DecidableEq ι] {a b T : ℕ} (e : ι ≃ Fin a × Fin b)
    (ha : 4 * T + 4 ≤ a) (hb : 3 ≤ b) (hodd : Odd b) (A : Algorithm ι (Fin 3)) :
    ¬ A.Colors (torus a b) T :=
  not_colors_of_rowLike _ (rowLike_cycleGraph a) cycleGraph_preconnected
    (fun x y h hx hy hy' => by have := cycleGraph_adj_val h; omega) e (by omega) hb hodd A

/-- **Theorem 1.3**, `√n` form (cylinder): on the `m × m` cylinder (`n = m²`, `m ≥ 3` odd), every
correct Online-LOCAL 3-colouring algorithm has locality `T > (√n - 3) / 4`. -/
theorem theorem_1_3_cylinder_square {ι : Type*} [DecidableEq ι] {m T : ℕ} (hm : 3 ≤ m)
    (hodd : Odd m) (e : ι ≃ Fin m × Fin m) {A : Algorithm ι (Fin 3)}
    (hA : A.Colors (cylinder m m) T) : m < 4 * T + 3 := by
  by_contra h
  exact theorem_1_3_cylinder e (by omega) hm hodd A hA

/-- **Theorem 1.3**, `√n` form (torus): on the `m × m` torus (`n = m²`, `m ≥ 3` odd), every
correct Online-LOCAL 3-colouring algorithm has locality `T > (√n - 4) / 4`. -/
theorem theorem_1_3_torus_square {ι : Type*} [DecidableEq ι] {m T : ℕ} (hm : 3 ≤ m)
    (hodd : Odd m) (e : ι ≃ Fin m × Fin m) {A : Algorithm ι (Fin 3)}
    (hA : A.Colors (torus m m) T) : m < 4 * T + 4 := by
  by_contra h
  exact theorem_1_3_torus e (by omega) hm hodd A hA

end Papers.PODC2024.OnlineLocalGrids
