import Papers.PODC2020.TightBipartiteMatching.Relaxations

/-!
# Lemma 4.4 and Theorem 4.5: the lower bound

* `lemma_4_4`: `Ψ^W_Δ(a, b, c)` (and, dually, `Ψ^B_Δ(a, b, c)`) is not 0-round solvable for
  `1 ≤ a ≤ Δ - 1` and `b, c ≤ Δ - a - 1`.
* `phi_not_zero`, `phi'_not_zero`: the same for `Φ^W(x, y)` and `Φ'(x, y)` when `x, y < Δ`
  (claimed without proof in the proof of Theorem 4.5).
* `theorem_4_5`: the white round complexity of `Φ^W_Δ(x, y)` is at least `T_Δ(x, y)`.
-/

namespace TightBipartiteMatching

open Lab Finset

variable {d : ℕ}

theorem exists_eq_of_count_pos {n : ℕ} {g : Fin n → Lab} {ℓ : Lab} (h : 1 ≤ (mset g).count ℓ) :
    ∃ k, g k = ℓ := by
  rw [count_mset] at h
  obtain ⟨k, hk⟩ := Finset.card_pos.1 h
  exact ⟨k, by simpa using hk⟩

/-- **Lemma 4.4.** For `Δ ≥ 2`, `1 ≤ a ≤ Δ - 1` and `0 ≤ b, c ≤ Δ - a - 1`, there is no
deterministic 0-round algorithm for `Ψ_Δ(a, b, c)` (with either colour active: `Ψ^B` is the same
statement for the black side). -/
theorem lemma_4_4 {a b c : ℕ} (ha : 1 ≤ a) (ha' : a ≤ d) (hb : b ≤ d - a) (hc : c ≤ d - a)
    (A : View d 0 → Fin (d + 1) → Lab) : ¬ Solves A (Psi d a b c).W (Psi d a b c).B := by
  refine not_solves_zero (fun g hg => ?_) A
  have hconst : ∀ k ℓ, g k = ℓ → (ℓ = M ∨ ℓ = Z ∨ ℓ = P) →
      mset (fun _ : Fin (d + 1) => g k) ∉ (Psi d a b c).B := by
    intro k ℓ hk hℓ hB
    have := psi_B_counts ha hB
    simp only [count_mset_const, hk] at this
    rcases hℓ with rfl | rfl | rfl <;> simp at this <;> omega
  rcases psi_W_counts hg with h | h | h
  · obtain ⟨k, hk⟩ := exists_eq_of_count_pos h; exact ⟨k, hconst k _ hk (by simp)⟩
  · obtain ⟨k, hk⟩ := exists_eq_of_count_pos h; exact ⟨k, hconst k _ hk (by simp)⟩
  · obtain ⟨k, hk⟩ := exists_eq_of_count_pos (show 1 ≤ (mset g).count P by omega)
    exact ⟨k, hconst k _ hk (by simp)⟩

/-- `Φ^W(x, y)` has no white 0-round algorithm when `x, y < Δ`. -/
theorem phi_not_zero {x y : ℕ} (hy : 1 ≤ y) (hy' : y ≤ d) (hx : x ≤ d)
    (A : View d 0 → Fin (d + 1) → Lab) : ¬ Solves A (Phi d x y).W (Phi d x y).B := by
  refine not_solves_zero (fun g hg => ?_) A
  have hconst : ∀ k ℓ, g k = ℓ → (ℓ = M ∨ ℓ = P) →
      mset (fun _ : Fin (d + 1) => g k) ∉ (Phi d x y).B := by
    intro k ℓ hk hℓ hB
    have := phi_B_counts hy hB
    simp only [count_mset_const, hk] at this
    rcases hℓ with rfl | rfl <;> simp at this <;> omega
  rcases phi_W_counts hg with h | h
  · obtain ⟨k, hk⟩ := exists_eq_of_count_pos h; exact ⟨k, hconst k _ hk (Or.inl rfl)⟩
  · obtain ⟨k, hk⟩ := exists_eq_of_count_pos (show 1 ≤ (mset g).count P by omega)
    exact ⟨k, hconst k _ hk (Or.inr rfl)⟩

/-- `Φ'(x, y)` has no black 0-round algorithm when `x, y < Δ`. -/
theorem phi'_not_zero {x y : ℕ} (hy : 1 ≤ y) (hy' : y ≤ d) (hx : x ≤ d)
    (A : View d 0 → Fin (d + 1) → Lab) : ¬ Solves A (Phi' d x y).B (Phi' d x y).W := by
  refine not_solves_zero (fun g hg => ?_) A
  have hconst : ∀ k ℓ, g k = ℓ → (ℓ = M ∨ ℓ = P) →
      mset (fun _ : Fin (d + 1) => g k) ∉ (Phi' d x y).W := by
    intro k ℓ hk hℓ hW
    have := phi'_W_counts hy hW
    simp only [count_mset_const, hk] at this
    rcases hℓ with rfl | rfl <;> simp at this <;> omega
  rcases phi'_B_counts hg with h | h
  · obtain ⟨k, hk⟩ := exists_eq_of_count_pos h; exact ⟨k, hconst k _ hk (Or.inl rfl)⟩
  · obtain ⟨k, hk⟩ := exists_eq_of_count_pos (show 1 ≤ (mset g).count P by omega)
    exact ⟨k, hconst k _ hk (Or.inr rfl)⟩

/-! ### The sequence of problems -/

/-- Solvability of `Ψ_Δ(a, b, c)` by the active side in `t` rounds (white for `Ψ^W`, black for
`Ψ^B`; both are the same predicate). -/
def PsiIn (d a b c t : ℕ) : Prop := (Psi d a b c).WhiteIn d t

/-- One step of the sequence (Lemma 4.1 with Theorem 2.1). -/
theorem psiIn_step {a b c t : ℕ} (ha : 1 ≤ a) (ha' : a ≤ d) (h : PsiIn d a b c (t + 1)) :
    PsiIn d a (min (c + a) (d + 1 - a)) b t :=
  (theorem_2_1 h).relax (lemma_4_1 ha ha')

/-- The parameters `(b_i, c_i)` of the `i`-th problem `Ψ(y, b_i, c_i)` of the sequence. -/
def seqBC (d x y : ℕ) : ℕ → ℕ × ℕ
  | 0 => (min x (d + 1 - y), 0)
  | i + 1 => (min ((seqBC d x y i).2 + y) (d + 1 - y), (seqBC d x y i).1)

/-- The uncapped parameters. -/
def seqU (x y : ℕ) : ℕ → ℕ × ℕ
  | 0 => (x, 0)
  | i + 1 => ((seqU x y i).2 + y, (seqU x y i).1)

theorem seqBC_le (x y : ℕ) : ∀ i, (seqBC d x y i).1 ≤ (seqU x y i).1 ∧ (seqBC d x y i).2 ≤ (seqU x y i).2
  | 0 => by simp [seqBC, seqU]
  | i + 1 => by
    have := seqBC_le x y i
    simp only [seqBC, seqU]; omega

theorem seqU_even (x y j : ℕ) : seqU x y (2 * j) = (x + j * y, j * y) := by
  induction j with
  | zero => simp [seqU]
  | succ j ih =>
    rw [show 2 * (j + 1) = 2 * j + 1 + 1 by ring]
    simp only [seqU, ih, Prod.mk.injEq]; constructor <;> ring

theorem seqU_odd (x y j : ℕ) : seqU x y (2 * j + 1) = ((j + 1) * y, x + j * y) := by
  rw [seqU, seqU_even]; simp only [Prod.mk.injEq]; exact ⟨by ring, trivial⟩

theorem psiIn_seq {x y : ℕ} (hy : 1 ≤ y) (hy' : y ≤ d) (i : ℕ) : ∀ t : ℕ,
    PsiIn d y (seqBC d x y 0).1 0 (t + i) → PsiIn d y (seqBC d x y i).1 (seqBC d x y i).2 t := by
  induction i with
  | zero => intro t h; exact h
  | succ i ih =>
    intro t h
    have := ih (t + 1) (by rw [show t + 1 + i = t + (i + 1) by omega]; exact h)
    exact psiIn_step hy hy' this

/-- From `Φ^W(x, y)` in `i + 2` rounds to the `i`-th problem of the sequence in 0 rounds; this is
impossible as soon as its parameters are at most `Δ - y - 1` (Lemma 4.4). -/
theorem phi_not_whiteIn_of_seq {x y : ℕ} (hy : 1 ≤ y) (hy' : y ≤ d) (i : ℕ)
    (hb : (seqBC d x y i).1 ≤ d - y) (hc : (seqBC d x y i).2 ≤ d - y) :
    ¬ (Phi d x y).WhiteIn d (i + 2) := by
  intro hW
  have hPhi' : (Phi' d x y).BlackIn d (i + 1) := (theorem_2_1 hW).relax (lemma_4_2 hy hy')
  have hPsi : PsiIn d y (seqBC d x y 0).1 0 (0 + i) := by
    rw [Nat.zero_add]; exact (theorem_2_1_dual hPhi').relax (lemma_4_3 hy hy')
  obtain ⟨A, hA⟩ := psiIn_seq hy hy' i 0 hPsi
  exact lemma_4_4 hy hy' hb hc A hA

/-- **Theorem 4.5.** In the port-numbering model (on 2-coloured `Δ`-regular trees), for
`0 ≤ x ≤ Δ` and `1 ≤ y ≤ Δ - 1`, the white round complexity of bipartite `x`-maximal `y`-matching
`Φ^W_Δ(x, y)` is at least `T_Δ(x, y)`: no white algorithm with fewer rounds exists. -/
theorem theorem_4_5 {x y : ℕ} (hy : 1 ≤ y) (hy' : y ≤ d) (hx : x ≤ d + 1) {t : ℕ}
    (ht : t < Tval (d + 1) x y) : ¬ (Phi d x y).WhiteIn d t := by
  intro h
  set q := (d + 1 - x) ⌈/⌉ y with hq
  set Q := (d + 1) ⌈/⌉ y with hQ
  have h1 := Nat.le_ceilDiv_mul (a := d + 1 - x) hy
  have h2 := Nat.ceilDiv_mul_le (d + 1 - x) y
  have h3 := Nat.ceilDiv_mul_le (d + 1) y
  have h4 := Nat.le_ceilDiv_mul (a := d + 1) hy
  rw [← hq] at h1 h2; rw [← hQ] at h3 h4
  have hqQ : q ≤ Q := Nat.ceilDiv_mono y (by omega)
  unfold Tval at ht
  rw [← hq, ← hQ] at ht
  split_ifs at ht with hlt
  · -- `T = 2q`
    obtain ⟨j, hj⟩ | hq1 : (∃ j, q = j + 2) ∨ q ≤ 1 := by
      rcases Nat.lt_or_ge q 2 with h' | h'
      · exact Or.inr (by omega)
      · exact Or.inl ⟨q - 2, by omega⟩
    · -- index `2q - 1 = (2j + 1) + 2`
      rw [hj] at h1 h2 ht hlt
      have hW := h.mono (show t ≤ 2 * j + 1 + 2 by omega)
      refine phi_not_whiteIn_of_seq hy hy' (2 * j + 1) ?_ ?_ hW
      · have := (seqBC_le (d := d) x y (2 * j + 1)).1
        rw [seqU_odd] at this
        have hm : (j + 3) * y ≤ Q * y := Nat.mul_le_mul_right _ (by omega)
        have e1 : (j + 3) * y = j * y + 3 * y := by ring
        have e2 : (j + 1) * y = j * y + y := by ring
        omega
      · have := (seqBC_le (d := d) x y (2 * j + 1)).2
        rw [seqU_odd] at this
        have e1 : (j + 2) * y = j * y + 2 * y := by ring
        omega
    · -- `q = 1`, `T = 2`: the index-1 problem `Φ'` would be 0-round solvable
      have hq1' : q = 1 := by omega
      rw [hq1'] at h1 h2
      have hW := h.mono (show t ≤ 1 by omega)
      obtain ⟨A, hA⟩ := (theorem_2_1 hW).relax (lemma_4_2 hy hy')
      exact phi'_not_zero hy hy' (by omega) A hA
  · -- `T = 2q - 1` and `q = Q`
    have hqQ' : q = Q := by omega
    obtain ⟨j, hj⟩ | hq1 : (∃ j, q = j + 2) ∨ q ≤ 1 := by
      rcases Nat.lt_or_ge q 2 with h' | h'
      · exact Or.inr (by omega)
      · exact Or.inl ⟨q - 2, by omega⟩
    · rw [hj] at h1 h2 ht hqQ'
      rw [← hqQ'] at h3
      have hW := h.mono (show t ≤ 2 * j + 2 by omega)
      refine phi_not_whiteIn_of_seq hy hy' (2 * j) ?_ ?_ hW
      · have := (seqBC_le (d := d) x y (2 * j)).1
        rw [seqU_even] at this
        have e1 : (j + 2) * y = j * y + 2 * y := by ring
        omega
      · have := (seqBC_le (d := d) x y (2 * j)).2
        rw [seqU_even] at this
        have e1 : (j + 2) * y = j * y + 2 * y := by ring
        omega
    · -- `q = 1`, `T = 1`: `Φ^W` itself would be 0-round solvable
      have hQ1 : 1 ≤ Q := by
        rcases Nat.eq_zero_or_pos Q with h0 | h0
        · rw [h0] at h4; omega
        · exact h0
      have hq1' : q = 1 := by omega
      rw [hq1'] at h1 h2
      have ht0 : t = 0 := by omega
      subst ht0
      obtain ⟨A, hA⟩ := h
      exact phi_not_zero hy hy' (by omega) A hA

end TightBipartiteMatching
