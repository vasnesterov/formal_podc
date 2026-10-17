import Papers.PODC2024.OnlineLocalGrids.Theorem13
import Papers.PODC2024.OnlineLocalGrids.Theorem11

/-!
# Non-vacuity: locality `O(√n)` suffices

Chang–Mishra–Nguyen–Yang–Yeh, PODC 2024. The lower bounds of Theorem 1.3 are not vacuous: the
generic "see everything" algorithm `seeAll` (from `Cslib.OnlineLocal`) properly 3-colours the grid,
the cylinder and the torus of dimensions `a × b` as soon as the locality is `T ≥ a + b`
(for `√n × √n` grids: `T = 2√n`). Hence the `Ω(√n)` bound of Theorem 1.3 is tight up to constants.
-/

namespace Papers.PODC2024.OnlineLocalGrids

open SimpleGraph Cslib.OnlineLocal

/-! ### Balls in products, paths and cycles -/

lemma closedBall_pathGraph (a : ℕ) (i : Fin a) : (pathGraph a).closedBall i a = Set.univ :=
  closedBall_eq_univ_of_preconnected (pathGraph_preconnected a) i (by simp)

lemma closedBall_cycleGraph (b : ℕ) (j : Fin b) : (cycleGraph b).closedBall j b = Set.univ :=
  closedBall_eq_univ_of_preconnected cycleGraph_preconnected j (by simp)

/-- Balls of radius `a + b` cover `R □ C` when `R`-balls of radius `a` and `C`-balls of radius
`b` do. -/
lemma ball_boxProd_eq_univ {α β : Type*} {G₁ : SimpleGraph α} {G₂ : SimpleGraph β} {a b T : ℕ}
    (h₁ : ∀ x, G₁.closedBall x a = Set.univ) (h₂ : ∀ y, G₂.closedBall y b = Set.univ)
    (hT : a + b ≤ T) (x : α × β) : ball (G₁ □ G₂) {x} T = Set.univ := by
  rw [ball_eq_biUnion_closedBall, Set.biUnion_singleton]
  refine Set.eq_univ_of_univ_subset ?_
  rw [← closedBall_boxProd_eq_univ h₁ h₂ x]
  exact closedBall_mono (by exact_mod_cast hT)

/-! ### Proper 3-colourings -/

/-- Sum of proper colourings of the factors is a proper colouring of the box product. -/
lemma isProper_boxProd {α β : Type*} {G₁ : SimpleGraph α} {G₂ : SimpleGraph β}
    {κ₁ : α → Fin 3} {κ₂ : β → Fin 3} (h₁ : IsProper G₁ κ₁) (h₂ : IsProper G₂ κ₂) :
    IsProper (G₁ □ G₂) fun p => κ₁ p.1 + κ₂ p.2 := by
  rintro ⟨x₁, x₂⟩ ⟨y₁, y₂⟩ h
  rcases boxProd_adj.1 h with ⟨h, rfl⟩ | ⟨h, rfl⟩
  · exact fun e => h₁ h (add_right_cancel e)
  · exact fun e => h₂ h (add_left_cancel e)

lemma isProper_pathGraph (a : ℕ) :
    IsProper (pathGraph a) fun i => (⟨i.val % 2, by omega⟩ : Fin 3) := by
  intro x y h e
  rw [pathGraph_adj] at h
  simp only [Fin.mk.injEq] at e
  omega

lemma exists_isProper_cycleGraph (b : ℕ) : ∃ κ : Fin b → Fin 3, IsProper (cycleGraph b) κ := by
  by_cases hb : 2 ≤ b
  · exact ⟨cycleGraph.tricoloring b hb, fun x y h => (cycleGraph.tricoloring b hb).valid h⟩
  · refine ⟨fun _ => 0, fun x y h => ?_⟩
    interval_cases b
    · exact x.elim0
    · exact absurd h cycleGraph_one_adj

/-! ### Non-vacuity -/

/-- The simple `m × m` grid is 3-coloured by `seeAll` with locality `2m` (= `2√n`). -/
theorem grid_colors_of_le {ι : Type*} [DecidableEq ι] {m T : ℕ} (hT : 2 * m ≤ T) :
    (seeAll (ι := ι) (Fin 3)).Colors (grid m m) T :=
  seeAll_colors
    (ball_boxProd_eq_univ (closedBall_pathGraph m) (closedBall_pathGraph m) (by omega))
    ⟨_, isProper_boxProd (isProper_pathGraph m) (isProper_pathGraph m)⟩

/-- The `a × b` cylinder is 3-coloured by `seeAll` with locality `a + b`. -/
theorem cylinder_colors_of_le {ι : Type*} [DecidableEq ι] {a b T : ℕ} (hT : a + b ≤ T) :
    (seeAll (ι := ι) (Fin 3)).Colors (cylinder a b) T := by
  obtain ⟨κ, hκ⟩ := exists_isProper_cycleGraph b
  exact seeAll_colors
    (ball_boxProd_eq_univ (closedBall_pathGraph a) (closedBall_cycleGraph b) hT)
    ⟨_, isProper_boxProd (isProper_pathGraph a) hκ⟩

/-- The `a × b` torus is 3-coloured by `seeAll` with locality `a + b`. -/
theorem torus_colors_of_le {ι : Type*} [DecidableEq ι] {a b T : ℕ} (hT : a + b ≤ T) :
    (seeAll (ι := ι) (Fin 3)).Colors (torus a b) T := by
  obtain ⟨κ₁, hκ₁⟩ := exists_isProper_cycleGraph a
  obtain ⟨κ₂, hκ₂⟩ := exists_isProper_cycleGraph b
  exact seeAll_colors
    (ball_boxProd_eq_univ (closedBall_cycleGraph a) (closedBall_cycleGraph b) hT)
    ⟨_, isProper_boxProd hκ₁ hκ₂⟩

/-- Tightness of Theorem 1.3 up to constants: on the `m × m` torus (`n = m²`, `m ≥ 3` odd) the
optimal locality `T*` of 3-colouring satisfies `m - 3 ≤ 4 T*` (Theorem 1.3) and `T* ≤ 2m`. -/
theorem torus_square_tight {ι : Type*} [DecidableEq ι] {m : ℕ} (hm : 3 ≤ m) (hodd : Odd m)
    (e : ι ≃ Fin m × Fin m) :
    (seeAll (ι := ι) (Fin 3)).Colors (torus m m) (2 * m) ∧
      ∀ (A : Algorithm ι (Fin 3)) (T : ℕ), A.Colors (torus m m) T → m < 4 * T + 4 :=
  ⟨torus_colors_of_le (by omega), fun _ _ hA => theorem_1_3_torus_square hm hodd e hA⟩

/-- Tightness of Theorem 1.3 up to constants for the `m × m` cylinder. -/
theorem cylinder_square_tight {ι : Type*} [DecidableEq ι] {m : ℕ} (hm : 3 ≤ m) (hodd : Odd m)
    (e : ι ≃ Fin m × Fin m) :
    (seeAll (ι := ι) (Fin 3)).Colors (cylinder m m) (2 * m) ∧
      ∀ (A : Algorithm ι (Fin 3)) (T : ℕ), A.Colors (cylinder m m) T → m < 4 * T + 3 :=
  ⟨cylinder_colors_of_le (by omega), fun _ _ hA => theorem_1_3_cylinder_square hm hodd e hA⟩

/-- Theorem 1.1 together with non-vacuity: on the `m × m` grid (`n = m²`) a correct algorithm
exists with locality `2m`, and every correct algorithm has locality `T` with
`log₂ n < 12 T + 14`. (The matching `O(log n)` upper bound of Akbari et al. is not formalized.) -/
theorem grid_bounds {ι : Type*} [DecidableEq ι] {m : ℕ} (e : ι ≃ Fin m × Fin m) :
    (seeAll (ι := ι) (Fin 3)).Colors (grid m m) (2 * m) ∧
      ∀ (A : Algorithm ι (Fin 3)) (T : ℕ), A.Colors (grid m m) T →
        Nat.log 2 (m * m) < 12 * T + 14 :=
  ⟨grid_colors_of_le le_rfl, fun A _ hA => theorem_1_1_log e A hA⟩

end Papers.PODC2024.OnlineLocalGrids
