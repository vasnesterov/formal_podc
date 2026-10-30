import Papers.PODC2023.PPDoubleExpThresholds.Lemma4Main
import Mathlib.Algebra.BigOperators.Fin

/-!
# Register totals and the threshold `k = 2 ∑ᵢ Nᵢ`

Good configurations of every size (the counting argument of the proof of Theorem 3).
-/

namespace Podc.PPDoubleExpThresholds

open Program Finset

variable {n : ℕ}

/-- `Reg n ≃ (Fin n × Fin 4) ⊕ Unit`. -/
def regEquiv (n : ℕ) : Reg n ≃ (Fin n × Fin 4) ⊕ Unit where
  toFun
    | .r i k => .inl (i, k)
    | .R => .inr ()
  invFun
    | .inl (i, k) => .r i k
    | .inr _ => .R
  left_inv := by intro r; cases r <;> rfl
  right_inv := by intro x; rcases x with ⟨i, k⟩ | ⟨⟩ <;> rfl

/-- The program has `4n + 1` registers. -/
theorem card_reg (n : ℕ) : Fintype.card (Reg n) = 4 * n + 1 := by
  rw [Fintype.card_congr (regEquiv n)]; simp; ring

theorem reg_succ {i : ℕ} (hi : i < n) (k : Fin 4) : reg n (i + 1) k = .r ⟨i, hi⟩ k := by
  simp [reg, hi]

/-- The total of a configuration, level by level. -/
theorem total_eq (C : Reg n → ℕ) :
    total C = C .R + ∑ i ∈ range n, ∑ k, C (reg n (i + 1) k) := by
  rw [total, ← (regEquiv n).symm.sum_comp, Fintype.sum_sum_type, Fintype.sum_prod_type, add_comm]
  congr 1
  rw [← Fin.sum_univ_eq_sum_range (fun i => ∑ k, C (reg n (i + 1) k))]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
  rw [reg_succ i.2]; rfl

/-- The partial thresholds `S j = 2 (N₁ + ⋯ + Nⱼ)`; the threshold is `k = S n`. -/
def S (j : ℕ) : ℕ := ∑ i ∈ range j, 2 * N (i + 1)

theorem S_succ (j : ℕ) : S (j + 1) = S j + 2 * N (j + 1) := by simp [S, sum_range_succ]

theorem lsum_proper {C : Reg n → ℕ} {i : ℕ} (h : Proper C i) {l : ℕ} (hl : 1 ≤ l) (hli : l ≤ i) :
    ∑ k, C (reg n l k) = 2 * N l := by
  obtain ⟨h0, h1, h2, h3⟩ := h l hl hli
  simp [Fin.sum_univ_four, h0, h1, h2, h3]; ring

/-- An `n`-proper configuration has at least `k` units. -/
theorem S_le_total {C : Reg n → ℕ} (h : Proper C n) : S n ≤ total C := by
  rw [total_eq, S]
  have : ∑ i ∈ range n, ∑ k, C (reg n (i + 1) k) = ∑ i ∈ range n, 2 * N (i + 1) :=
    Finset.sum_congr rfl fun i hi => lsum_proper h (by omega) (by simp at hi; omega)
  omega

/-- A `J`-low and `(J+1)`-empty configuration has fewer than `k` units. -/
theorem total_lt_S {C : Reg n → ℕ} {J : ℕ} (hJ : 1 ≤ J) (hJn : J ≤ n) (hL : Low C J)
    (hE : Empty C (J + 1)) : total C < S n := by
  rw [total_eq, S, hE.2, zero_add]
  obtain ⟨hP, hnP, hx, hy, hxb, hyb⟩ := hL
  have hlow : ∑ k, C (reg n J k) < 2 * N J := by
    simp only [Fin.sum_univ_four, hx, hy]
    by_contra h
    exact hnP ((proper_succ_iff hJ).2 ⟨hP, hx, by omega, hy, by omega⟩)
  apply Finset.sum_lt_sum
  · intro i hi
    simp only [mem_range] at hi
    rcases Nat.lt_trichotomy (i + 1) J with h | h | h
    · exact (lsum_proper hP (by omega) (by omega)).le
    · rw [h]; exact hlow.le
    · simp [hE.1 (i + 1) (by omega) (by omega)]
  · exact ⟨J - 1, by simp; omega, by rw [show J - 1 + 1 = J by omega]; exact hlow⟩

/-- A configuration given level by level. -/
def mk (a : ℕ → Fin 4 → ℕ) (r₀ : ℕ) : Reg n → ℕ
  | .r i k => a (i.1 + 1) k
  | .R => r₀

theorem mk_reg (a : ℕ → Fin 4 → ℕ) (r₀ : ℕ) {i : ℕ} (hi : 1 ≤ i) (hin : i ≤ n) (k : Fin 4) :
    mk a r₀ (reg n i k) = a i k := by
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  rw [reg_succ (by omega)]; rfl

theorem total_mk (a : ℕ → Fin 4 → ℕ) (r₀ : ℕ) :
    total (mk (n := n) a r₀) = r₀ + ∑ i ∈ range n, ∑ k, a (i + 1) k := by
  rw [total_eq]
  congr 1
  refine Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun k _ => ?_
  exact mk_reg a r₀ (by omega) (by simp at hi; omega) k

/-- The proper values of a level. -/
def pa (i : ℕ) (k : Fin 4) : ℕ := if k = 1 ∨ k = 3 then N i else 0

theorem sum_pa (i : ℕ) : ∑ k, pa i k = 2 * N i := by
  simp [Fin.sum_univ_four, pa]; ring

/-- `J`-low and `(J+1)`-empty with `rem` units on level `J`. -/
def la (J rem : ℕ) (i : ℕ) (k : Fin 4) : ℕ :=
  if i < J then pa i k
  else if i = J then (if k = 1 then min rem (N J) else if k = 3 then rem - min rem (N J) else 0)
  else 0

theorem sum_la {J : ℕ} (hJ : 1 ≤ J) (hJn : J ≤ n) (rem : ℕ) :
    ∑ i ∈ range n, ∑ k, la J rem (i + 1) k = S (J - 1) + rem := by
  obtain ⟨m, hm⟩ : ∃ m, n = J - 1 + (m + 1) := ⟨n - J, by omega⟩
  rw [hm, sum_range_add, sum_range_succ']
  have h1 : ∑ i ∈ range (J - 1), ∑ k, la J rem (i + 1) k = S (J - 1) :=
    Finset.sum_congr rfl fun i hi => by
      simp at hi; simp only [la, if_pos (by omega : i + 1 < J)]; exact sum_pa _
  have h2 : ∀ i, ∑ k, la J rem (J - 1 + (i + 1) + 1) k = 0 := fun i => by
    simp [la, show ¬ J - 1 + (i + 1) + 1 < J by omega, show J - 1 + (i + 1) + 1 ≠ J by omega]
  have h3 : ∑ k, la J rem (J - 1 + 0 + 1) k = rem := by
    rw [show J - 1 + 0 + 1 = J by omega]
    simp [la, Fin.sum_univ_four]
  rw [h1, h3]; simp [h2]

/-- **Good configurations of every size** (proof of Theorem 3). -/
theorem exists_good (m : ℕ) : ∃ C : Reg n → ℕ, total C = m ∧
    ((S n ≤ m ∧ Proper C n) ∨ (m < S n ∧ ∃ J, 1 ≤ J ∧ J ≤ n ∧ Low C J ∧ Empty C (J + 1))) := by
  classical
  rcases le_or_gt (S n) m with h | h
  · refine ⟨mk pa (m - S n), ?_, .inl ⟨h, ?_⟩⟩
    · rw [total_mk]; simp only [sum_pa]; rw [← S]; omega
    · intro l hl hln
      simp [mk_reg _ _ hl hln, pa]
  · have hn : 1 ≤ n := by
      rcases n with _ | n
      · simp [S] at h
      · omega
    have hex : ∃ j, m < S (j + 1) := ⟨n - 1, by rw [Nat.sub_add_cancel hn]; exact h⟩
    obtain ⟨j, hj, hjmin⟩ : ∃ j, m < S (j + 1) ∧ ∀ k < j, ¬ m < S (k + 1) :=
      ⟨Nat.find hex, Nat.find_spec hex, fun k hk => Nat.find_min hex hk⟩
    have hjn : j + 1 ≤ n := by
      by_contra hc
      exact hjmin (n - 1) (by omega) (by rw [Nat.sub_add_cancel hn]; exact h)
    have hSj : S j ≤ m := by
      rcases Nat.eq_zero_or_pos j with h0 | h0
      · rw [h0]; simp [S]
      · have := hjmin (j - 1) (by omega)
        rw [show j - 1 + 1 = j by omega] at this; omega
    have hrem : m - S j < 2 * N (j + 1) := by rw [S_succ] at hj; omega
    generalize hJ : j + 1 = J at hjn hrem
    generalize hr : m - S j = rem at hrem
    refine ⟨mk (la J rem) 0, ?_, .inr ⟨h, J, by omega, hjn, ?_, ?_⟩⟩
    · rw [total_mk, sum_la (by omega) hjn, ← hJ, Nat.add_sub_cancel]; omega
    · have hP : Proper (mk (n := n) (la J rem) 0) (J - 1) := by
        intro l hl hlJ
        simp [mk_reg (n := n) _ _ hl (by omega), la, pa, show l < J by omega]
      refine ⟨hP, fun hJ => ?_, ?_, ?_, ?_, ?_⟩
      · have := (hJ J (by omega) le_rfl).2.2.2
        rw [mk_reg _ _ (by omega) hjn] at this
        simp [la] at this
        omega
      all_goals rw [mk_reg _ _ (by omega) hjn]; simp [la] <;> omega
    · refine ⟨fun l hl hln k => ?_, rfl⟩
      rw [mk_reg _ _ (by omega) hln]
      simp [la, show ¬ l < J by omega, show l ≠ J by omega]

end Podc.PPDoubleExpThresholds
