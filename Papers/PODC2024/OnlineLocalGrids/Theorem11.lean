import Papers.PODC2024.OnlineLocalGrids.Lemma36
import Papers.PODC2024.OnlineLocalGrids.BValue

/-!
# Theorem 1.1: `Ω(log n)` locality for 3-colouring the `√n × √n` grid in Online-LOCAL

Chang–Mishra–Nguyen–Yang–Yeh, PODC 2024, §3.2.

With `k = 4T + 5`, Lemma 3.6 forces (in row `r₁ = T`) a row path `P_{u,v}` with `|b| ≥ k`. The
adversary then reveals the path `P_{s,t}` right above it in row `r₂ = r₁ + 2T + 2`, and reflects it
(invisibly) if necessary so that `b(P_{s,t})` has the opposite sign. The rectangle `u → v → s → t → u`
has `b`-value `0` in any proper colouring (Lemma 3.4, via the potential `grid_exists_potential`),
but its two vertical sides contribute at most `2(2T + 2) < k`.

Explicit constants: if `2^(4T+5) · (2T+3) ≤ m` then no algorithm of locality `T` 3-colours the
`m × m` grid (`theorem_1_1`); equivalently every correct algorithm has
`log₂ n < 12 T + 14` where `n = m²` (`theorem_1_1_log`).
-/

namespace Papers.PODC2024.OnlineLocalGrids

open SimpleGraph Cslib.OnlineLocal

/-- Telescoping a sum of `a`-values along a line against a potential. -/
lemma S_eq_of_potential {f : ℤ → Fin 3} {ψ : ℤ → ℤ} {x : ℤ} {n : ℕ}
    (h : ∀ i : ℕ, i < n → aval (f (x + i)) (f (x + i + 1)) = ψ (x + i + 1) - ψ (x + i)) :
    S f x n = ψ (x + n) - ψ x := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [S_succ, ih (fun i hi => h i (by omega)), h n (by omega)]
    push_cast; ring_nf

variable {ι : Type*} [DecidableEq ι]

/-- **Theorem 1.1** (explicit form). If `2^(4T+5) · (2T+3) ≤ m`, then no deterministic
Online-LOCAL algorithm with locality `T` properly 3-colours the `m × m` grid: for some assignment
of the identifiers to the grid nodes and some reveal order the produced colouring is improper. -/
theorem theorem_1_1 {m T : ℕ} (e : ι ≃ Fin m × Fin m) (hm : 2 ^ (4 * T + 5) * (2 * T + 3) ≤ m)
    (A : Algorithm ι (Fin 3)) : ¬ A.Colors (grid m m) T := by
  intro hA
  have hk : 4 * T + 5 < 2 ^ (4 * T + 5) := Nat.lt_two_pow_self
  have hm1 : 4 * T + 5 < m := by nlinarith
  have : NeZero m := ⟨by omega⟩
  let : Fintype ι := Fintype.ofEquiv _ e.symm
  set k := 4 * T + 5
  have hseg := segLen_add T k
  -- Step 1: Lemma 3.6 in row `r₁ = T`, stretch starting at column `T`
  obtain ⟨δ, μ, L, R, -, hnd, hL, hLR, hR, hmem, hfac⟩ :=
    lemma36 A T k [] e (T : ℤ) (T : ℤ) List.nodup_nil le_rfl (by omega) le_rfl
      (by nlinarith) (by simp)
  simp only [List.nil_append] at hnd hfac
  set pos₁ := e.trans μ with hpos₁
  have hmem' : ∀ x, x ∈ δ ↔ ∃ j, L ≤ j ∧ j ≤ R ∧ pos₁ x = pt T j := hmem
  set g := rowCol A T pos₁ δ T with hg
  have hRm : R + T < m := by nlinarith
  -- positions of the first segment
  have hcol : ∀ j : ℤ, L ≤ j → j ≤ R → pos₁.symm (pt T j) ∈ δ := fun j h1 h2 =>
    (hmem' _).2 ⟨j, h1, h2, by simp⟩
  have rzpt : ∀ r j : ℤ, 0 ≤ r → r < m → rz (pt (m := m) r j) = r := fun r j h0 h1 => rz_pt h0 h1
  have czpt : ∀ r j : ℤ, 0 ≤ j → j < m → cz (pt (m := m) r j) = j := fun r j h0 h1 => cz_pt h0 h1
  have adj_row : ∀ r j : ℤ, 0 ≤ r → r < m → 0 ≤ j → j + 1 < m →
      (grid m m).Adj (pt r j) (pt r (j + 1)) := fun r j h0 h1 h2 h3 => by
    rw [grid_adj_iff]; unfold md
    rw [rzpt r j h0 h1, rzpt r (j + 1) h0 h1, czpt r j h2 (by omega), czpt r (j + 1) (by omega) h3]
    omega
  have adj_col : ∀ i j : ℤ, 0 ≤ i → i + 1 < m → 0 ≤ j → j < m →
      (grid m m).Adj (pt i j) (pt (i + 1) j) := fun i j h0 h1 h2 h3 => by
    rw [grid_adj_iff]; unfold md
    rw [rzpt i j h0 (by omega), rzpt (i + 1) j (by omega) h1, czpt i j h2 h3, czpt (i + 1) j h2 h3]
    omega
  by_cases hP : RowProper g L R
  swap
  · -- the algorithm already coloured two adjacent nodes of the segment alike
    simp only [RowProper, not_forall, not_not] at hP
    obtain ⟨j, h1, h2, hj⟩ := hP
    have hσ := isOrder_completeOrder hnd
    have := hA pos₁ (completeOrder δ) hσ (pos₁.symm (pt T j)) (pos₁.symm (pt T (j + 1)))
      (by simpa using adj_row T j (by omega) (by omega) (by omega) (by omega))
    apply this
    simp only [completeOrder]
    rw [label_append A _ T _ (hcol j h1 h2.le), label_append A _ T _ (hcol (j + 1) (by omega) h2)]
    exact hj
  obtain ⟨x0, n, hx0, hxn, hS⟩ := hfac hP
  -- Step 2: reveal the path right above, in row `r₂ = 3T + 2`
  set r₂ : ℤ := 3 * T + 2 with hr₂
  set δ' : List ι := (List.range (n + 1)).map (fun i : ℕ => pos₁.symm (pt r₂ (x0 + (i : ℤ))))
    with hδ'
  have hmem2 : ∀ x, x ∈ δ' ↔ ∃ j, x0 ≤ j ∧ j ≤ x0 + n ∧ pos₁ x = pt r₂ j := by
    intro x
    simp only [hδ', List.mem_map, List.mem_range]
    constructor
    · rintro ⟨i, hi, rfl⟩; exact ⟨x0 + i, by omega, by omega, by simp⟩
    · rintro ⟨j, h1, h2, h3⟩
      refine ⟨(j - x0).toNat, by omega, ?_⟩
      rw [show x0 + (((j - x0).toNat : ℕ) : ℤ) = j by omega, ← h3, Equiv.symm_apply_apply]
  have hnd2 : (δ ++ δ').Nodup := by
    rw [List.nodup_append]
    refine ⟨hnd, ?_, ?_⟩
    · refine List.Nodup.map_on (fun i hi i' hi' h => ?_) List.nodup_range
      simp only [List.mem_range] at hi hi'
      have := congrArg cz (pos₁.symm.injective h)
      rw [czpt _ _ (by omega) (by omega), czpt _ _ (by omega) (by omega)] at this
      omega
    · intro x hx y hy hxy
      subst hxy
      obtain ⟨j, -, -, h1⟩ := (hmem' x).1 hx
      obtain ⟨j', -, -, h2⟩ := (hmem2 x).1 hy
      have := congrArg rz (h1.symm.trans h2)
      rw [rzpt _ _ (by omega) (by omega), rzpt _ _ (by omega) (by omega)] at this
      omega
  set h₀ := rowCol A T pos₁ (δ ++ δ') r₂ with hh₀
  set s := S g x0 n
  set t := S h₀ x0 n
  obtain ⟨fl, hfl⟩ : ∃ fl : Bool, fl = decide ((0 < s ∧ 0 < t) ∨ (s < 0 ∧ t < 0)) := ⟨_, rfl⟩
  obtain ⟨d, hd⟩ : ∃ d : ℤ, d = if fl then 2 * x0 + n else 0 := ⟨_, rfl⟩
  have hcm : ∀ j, x0 ≤ j → j ≤ x0 + n → x0 ≤ cm fl d j ∧ cm fl d j ≤ x0 + n := by
    intro j h1 h2; cases fl <;> simp only [cm, Bool.false_eq_true, ↓reduceIte] at hd ⊢ <;> omega
  -- Step 3: reflect the upper path if needed
  obtain ⟨μ2, hfix2, hmove2, hag2⟩ := grid_exists_move (U₁ := pos₁ '' {x | x ∈ δ})
    (U₂ := pos₁ '' {x | x ∈ δ'}) (T := T) fl d
    (by
      rintro u ⟨x, hx, rfl⟩
      obtain ⟨j, h1, h2, h3⟩ := (hmem2 x).1 hx
      obtain ⟨h4, h5⟩ := hcm j h1 h2
      rw [h3, rzpt _ _ (by omega) (by omega), czpt _ _ (by omega) (by omega)]
      omega)
    (by
      rintro u ⟨y, hy, rfl⟩ v ⟨x, hx, rfl⟩
      obtain ⟨j, h1, h2, h3⟩ := (hmem2 x).1 hx
      obtain ⟨j', h1', h2', h3'⟩ := (hmem' y).1 hy
      rw [h3, h3']
      simp only [md, rzpt _ _ (by omega : (0 : ℤ) ≤ T) (by omega),
        rzpt _ _ (by omega : (0 : ℤ) ≤ r₂) (by omega)]
      omega)
  have hU : pos₁ '' {x | x ∈ δ} ∪ pos₁ '' {x | x ∈ δ'} = pos₁ '' {x | x ∈ δ ++ δ'} := by
    rw [← Set.image_union]; congr 1; ext x; simp
  rw [hU] at hag2
  set pos₂ := pos₁.trans μ2 with hpos₂
  set σ := completeOrder (δ ++ δ')
  -- Step 4: the final colouring
  have hσ := isOrder_completeOrder hnd2
  set c : Fin m × Fin m → Fin 3 := fun p => A.label ((grid m m).comap pos₂) T σ (pos₂.symm p) with hc
  have hprop : IsProper (grid m m) c := by
    intro p q hpq hcpq
    exact hA pos₂ σ hσ (pos₂.symm p) (pos₂.symm q) (by simpa using hpq) hcpq
  obtain ⟨φ, hφ⟩ := grid_exists_potential hprop
  -- the final colours on the two rows
  have hrow1 : ∀ j, x0 ≤ j → j ≤ x0 + n → c (pt T j) = g j := by
    intro j h1 h2
    have hx := hcol j (by omega) (by omega)
    have hpx : pos₂ (pos₁.symm (pt T j)) = pt T j := by
      rw [hpos₂, Equiv.trans_apply, Equiv.apply_symm_apply]
      exact hfix2 _ (subset_ball ⟨_, hx, by simp⟩)
    have : pos₂.symm (pt T j) = pos₁.symm (pt T j) := by rw [Equiv.symm_apply_eq, hpx]
    simp only [hc, this, σ, completeOrder]
    rw [label_append A _ T _ (List.mem_append_left _ hx), hpos₂,
      ← label_eq_of_agreeOn A (agreeOn_comap pos₁ μ2 hag2), label_append A _ T _ hx]
    rfl
  have hrow2 : ∀ j, x0 ≤ j → j ≤ x0 + n → c (pt r₂ (cm fl d j)) = h₀ j := by
    intro j h1 h2
    have hx : pos₁.symm (pt r₂ j) ∈ δ' := (hmem2 _).2 ⟨j, h1, h2, by simp⟩
    obtain ⟨h4, h5⟩ := hmove2 _ ⟨_, hx, rfl⟩
    obtain ⟨h6, h7⟩ := hcm j h1 h2
    have hpx : pos₂ (pos₁.symm (pt r₂ j)) = pt r₂ (cm fl d j) := by
      rw [eq_pt_iff (by omega) (by omega) (by omega) (by omega), hpos₂, Equiv.trans_apply, h4, h5]
      simp only [Equiv.apply_symm_apply]
      rw [rzpt _ _ (by omega) (by omega), czpt _ _ (by omega) (by omega)]
      exact ⟨rfl, rfl⟩
    have : pos₂.symm (pt r₂ (cm fl d j)) = pos₁.symm (pt r₂ j) := by
      rw [Equiv.symm_apply_eq, hpx]
    simp only [hc, this, σ, completeOrder]
    rw [label_append A _ T _ (List.mem_append_right _ hx), hpos₂,
      ← label_eq_of_agreeOn A (agreeOn_comap pos₁ μ2 hag2)]
    rfl
  -- `b`-values of the four sides
  have hS1 : S (fun j => c (pt T j)) x0 n = s := S_congr (fun j h1 h2 => hrow1 j h1 h2)
  have hS2 : S (fun j => c (pt r₂ j)) x0 n = if fl then -t else t := by
    by_cases hfl' : fl = true
    · simp only [hfl', ↓reduceIte]
      have := S_flip (g := h₀) (g' := fun j => c (pt r₂ j)) (d := d) (x := x0) (n := n)
        (fun j h1 h2 => by simpa [cm, hfl'] using hrow2 j h1 h2)
      rwa [show d - (x0 + n) = x0 by simp [hd, hfl']; ring] at this
    · simp only [Bool.not_eq_true] at hfl'
      simp only [hfl', Bool.false_eq_true, ↓reduceIte]
      exact S_congr (fun j h1 h2 => by simpa [cm, hd, hfl'] using hrow2 j h1 h2)
  have hpotRow : ∀ r : ℤ, 0 ≤ r → r < m →
      S (fun j => c (pt r j)) x0 n = φ (pt r (x0 + n)) - φ (pt r x0) := by
    intro r h0 h1
    exact S_eq_of_potential (ψ := fun j => φ (pt r j))
      (fun i hi => hφ _ _ (adj_row r _ h0 h1 (by omega) (by omega)))
  have hpotCol : ∀ j : ℤ, 0 ≤ j → j < m →
      S (fun i => c (pt i j)) T (2 * T + 2) = φ (pt r₂ j) - φ (pt T j) := by
    intro j h0 h1
    rw [S_eq_of_potential (ψ := fun i => φ (pt i j))
      (fun i hi => hφ _ _ (adj_col _ j (by omega) (by omega) h0 h1))]
    rw [show (T : ℤ) + ((2 * T + 2 : ℕ) : ℤ) = r₂ by push_cast; omega]
  have hV1 := natAbs_S_le (fun i => c (pt i x0)) T (2 * T + 2)
  have hV2 := natAbs_S_le (fun i => c (pt i (x0 + n))) T (2 * T + 2)
  rw [hpotCol x0 (by omega) (by omega)] at hV1
  rw [hpotCol (x0 + n) (by omega) (by omega)] at hV2
  have e1 := hpotRow T (by omega) (by omega)
  have e2 := hpotRow r₂ (by omega) (by omega)
  rw [hS1] at e1
  rw [hS2] at e2
  -- sign bookkeeping
  have hsk : k ≤ s.natAbs := hS
  by_cases hfl' : fl = true
  · simp only [hfl', ↓reduceIte] at e2
    have : (0 < s ∧ 0 < t) ∨ (s < 0 ∧ t < 0) := by simpa [hfl] using hfl'
    omega
  · simp only [Bool.not_eq_true] at hfl'
    simp only [hfl', Bool.false_eq_true, ↓reduceIte] at e2
    have : ¬ ((0 < s ∧ 0 < t) ∨ (s < 0 ∧ t < 0)) := by simpa [hfl] using hfl'
    omega

/-- **Theorem 1.1** (`Ω(log n)` form): any deterministic Online-LOCAL algorithm with locality `T`
that properly 3-colours the `m × m` grid (`n = m²` nodes) satisfies `log₂ n < 12 T + 14`. -/
theorem theorem_1_1_log {m T : ℕ} (e : ι ≃ Fin m × Fin m) (A : Algorithm ι (Fin 3))
    (hA : A.Colors (grid m m) T) : Nat.log 2 (m * m) < 12 * T + 14 := by
  have h1 : m < 2 ^ (4 * T + 5) * (2 * T + 3) := by
    by_contra h; exact theorem_1_1 e (by omega) A hA
  have h2 : 2 * T + 3 ≤ 2 ^ (2 * T + 2) := by
    have := Nat.lt_two_pow_self (n := 2 * T + 2)
    have : 2 * T + 2 + 1 ≤ 2 ^ (2 * T + 2) := this
    omega
  have h3 : m < 2 ^ (6 * T + 7) := by
    calc m < 2 ^ (4 * T + 5) * (2 * T + 3) := h1
      _ ≤ 2 ^ (4 * T + 5) * 2 ^ (2 * T + 2) := Nat.mul_le_mul_left _ h2
      _ = 2 ^ (6 * T + 7) := by rw [← pow_add]; ring_nf
  have h4 : m * m < 2 ^ (12 * T + 14) := by
    calc m * m < 2 ^ (6 * T + 7) * 2 ^ (6 * T + 7) := Nat.mul_lt_mul'' h3 h3
      _ = 2 ^ (12 * T + 14) := by rw [← pow_add]; ring_nf
  rcases Nat.eq_zero_or_pos m with h0 | h0
  · subst h0; simp
  · exact Nat.log_lt_of_lt_pow (by positivity) h4

end Papers.PODC2024.OnlineLocalGrids
