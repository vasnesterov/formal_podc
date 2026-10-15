import Papers.PODC2024.OnlineLocalGrids.Defs

/-!
# `b`-values of row paths

A row of the grid is coloured by `g : ℤ → Fin 3` (column ↦ colour). The directed row path from
column `x` to column `x + n` has `b`-value `S g x n` (Definition 3.2 specialised to row paths;
the leftward path has `b`-value `- S g x n`).

* `S_add`, `S_parity` (Lemma 3.5 for row paths), transport along column translations and
  reflections (`S_shift`, `S_flip`);
* `HasFactor g L R k`: some row path inside columns `[L, R]` has `|b| ≥ k`;
* `combine`: the arithmetic core of the inductive step of Lemma 3.6.
-/

namespace Papers.PODC2024.OnlineLocalGrids

/-- `b`-value of the rightward row path from column `x` to column `x + n`. -/
def S (g : ℤ → Fin 3) (x : ℤ) (n : ℕ) : ℤ :=
  ∑ i ∈ Finset.range n, aval (g (x + i)) (g (x + i + 1))

/-- The row colouring is proper between columns `L` and `R`. -/
def RowProper (g : ℤ → Fin 3) (L R : ℤ) : Prop := ∀ j, L ≤ j → j < R → g j ≠ g (j + 1)

/-- Some directed row path inside the columns `[L, R]` has `|b| ≥ k`. -/
def HasFactor (g : ℤ → Fin 3) (L R : ℤ) (k : ℕ) : Prop :=
  ∃ x : ℤ, ∃ n : ℕ, L ≤ x ∧ x + n ≤ R ∧ k ≤ (S g x n).natAbs

@[simp] lemma S_zero (g : ℤ → Fin 3) (x : ℤ) : S g x 0 = 0 := by simp [S]

lemma S_succ (g : ℤ → Fin 3) (x : ℤ) (n : ℕ) :
    S g x (n + 1) = S g x n + aval (g (x + n)) (g (x + n + 1)) := by
  simp [S, Finset.sum_range_succ]

lemma S_add (g : ℤ → Fin 3) (x : ℤ) (n n' : ℕ) : S g x (n + n') = S g x n + S g (x + n) n' := by
  induction n' with
  | zero => simp
  | succ n' ih =>
    rw [← Nat.add_assoc, S_succ, ih, S_succ]
    push_cast
    rw [add_assoc x]
    simp only [add_assoc]

lemma natAbs_S_le (g : ℤ → Fin 3) (x : ℤ) (n : ℕ) : (S g x n).natAbs ≤ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [S_succ]
    have := abs_le.mp (abs_aval_le (g (x + n)) (g (x + n + 1)))
    omega

/-- **Lemma 3.5** for row paths. -/
lemma S_parity {g : ℤ → Fin 3} {x : ℤ} {n : ℕ} (h : RowProper g x (x + n)) :
    S g x n ≡ ind (g x) + ind (g (x + n)) + n [ZMOD 2] := by
  induction n with
  | zero => simp only [S_zero, Nat.cast_zero, add_zero]; rw [Int.modEq_iff_dvd]; omega
  | succ n ih =>
    have ih := ih (fun j h1 h2 => h j h1 (by push_cast; omega))
    have hp := aval_parity (g (x + n)) (g (x + n + 1)) (h (x + n) (by omega) (by push_cast; omega))
    rw [S_succ]
    rw [Int.modEq_iff_dvd] at ih hp ⊢
    push_cast
    rw [← add_assoc x]
    omega

lemma S_congr {g g' : ℤ → Fin 3} {x : ℤ} {n : ℕ} (h : ∀ j, x ≤ j → j ≤ x + n → g' j = g j) :
    S g' x n = S g x n := by
  unfold S
  refine Finset.sum_congr rfl fun i hi => ?_
  simp only [Finset.mem_range] at hi
  rw [h _ (by omega) (by omega), h _ (by omega) (by omega)]

/-- Transport along a translation of columns. -/
lemma S_shift {g g' : ℤ → Fin 3} {d x : ℤ} {n : ℕ}
    (h : ∀ j, x ≤ j → j ≤ x + n → g' (d + j) = g j) : S g' (d + x) n = S g x n := by
  unfold S
  refine Finset.sum_congr rfl fun i hi => ?_
  simp only [Finset.mem_range] at hi
  rw [show d + x + i = d + (x + i) by ring, show d + (x + i) + 1 = d + (x + i + 1) by ring,
    h _ (by omega) (by omega), h _ (by omega) (by omega)]

/-- Transport along a reflection of columns. -/
lemma S_flip {g g' : ℤ → Fin 3} {d x : ℤ} {n : ℕ}
    (h : ∀ j, x ≤ j → j ≤ x + n → g' (d - j) = g j) : S g' (d - (x + n)) n = - S g x n := by
  unfold S
  rw [← Finset.sum_range_reflect, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i hi => ?_
  simp only [Finset.mem_range] at hi
  rw [aval_antisymm]
  congr 2
  · rw [show d - (x + n) + ((n - 1 - i : ℕ) : ℤ) + 1 = d - (x + i) by omega, h _ (by omega) (by omega)]
  · rw [show d - (x + n) + ((n - 1 - i : ℕ) : ℤ) = d - (x + i + 1) by omega,
      h _ (by omega) (by omega)]

lemma rowProper_mono {g : ℤ → Fin 3} {L R L' R' : ℤ} (h : RowProper g L R) (h1 : L ≤ L')
    (h2 : R' ≤ R) : RowProper g L' R' := fun j hj1 hj2 => h j (by omega) (by omega)

lemma rowProper_shift {g g' : ℤ → Fin 3} {d L R : ℤ}
    (h : ∀ j, L ≤ j → j ≤ R → g' (d + j) = g j) (hp : RowProper g' (d + L) (d + R)) :
    RowProper g L R := by
  intro j h1 h2
  have := hp (d + j) (by omega) (by omega)
  rwa [h j h1 h2.le, show d + j + 1 = d + (j + 1) by ring, h (j + 1) (by omega) (by omega)] at this

lemma rowProper_flip {g g' : ℤ → Fin 3} {d L R : ℤ}
    (h : ∀ j, L ≤ j → j ≤ R → g' (d - j) = g j) (hp : RowProper g' (d - R) (d - L)) :
    RowProper g L R := by
  intro j h1 h2
  have := hp (d - (j + 1)) (by omega) (by omega)
  rw [show d - (j + 1) + 1 = d - j by ring, h j h1 h2.le, h (j + 1) (by omega) (by omega)] at this
  exact fun e => this e.symm

/-- The arithmetic core of the inductive step of Lemma 3.6: if two paths have `b`-values at least
`k - 1` in the same direction and the connecting path has `b`-value of parity different from
`k - 1`, then one of the connecting path and the concatenation has `|b| ≥ k`. -/
lemma combine {k : ℕ} {s₁ h s₂ : ℤ} (ε : ℤ) (hε : ε = 1 ∨ ε = -1) (h₁ : (k : ℤ) ≤ ε * s₁ + 1)
    (h₂ : (k : ℤ) ≤ ε * s₂ + 1) (hpar : ¬ (h ≡ (k : ℤ) + 1 [ZMOD 2])) :
    k ≤ s₁.natAbs ∨ k ≤ s₂.natAbs ∨ k ≤ h.natAbs ∨ k ≤ (s₁ + h + s₂).natAbs := by
  rw [Int.modEq_iff_dvd] at hpar
  rcases hε with rfl | rfl <;> omega

end Papers.PODC2024.OnlineLocalGrids
