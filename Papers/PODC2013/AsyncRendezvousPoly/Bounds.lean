import Papers.PODC2013.AsyncRendezvousPoly.Algorithm
import Papers.PODC2013.AsyncRendezvousPoly.Poly

/-!
# Index arithmetic for the route of Algorithm RV-asynch-poly

Positions of pieces, segments, borders and fences in the route, and the length estimates used in
the proofs of Lemmas 3.2–3.6 (e.g. `|T(k)| ≤ (2k-1)|K(k)|`).
-/

namespace Podc.AsyncRendezvousPoly

open Finset

variable (P : ℕ → ℕ) (bs : List Bool)

theorem nSeg_pos (hbs : bs ≠ []) {k : ℕ} (hk : 1 ≤ k) : 0 < nSeg bs k := by
  unfold nSeg; have := List.length_pos_of_ne_nil hbs; omega

theorem nSeg_le (k : ℕ) : nSeg bs k ≤ k := min_le_left _ _

@[simp] theorem segS_zero (k : ℕ) : segS P bs k 0 = iS P bs k := by simp [segS]

theorem segS_succ (k i : ℕ) : segS P bs k (i + 1) = segS P bs k i + lenUnit P bs k i := by
  simp [segS, sum_range_succ]; ring

theorem segS_mono (k : ℕ) {i i' : ℕ} (h : i ≤ i') : segS P bs k i ≤ segS P bs k i' := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => rw [segS_succ]; omega

/-- The border after segment `i` ends where segment `i + 1` starts. -/
theorem segS_succ_border (k i : ℕ) (hi : i + 1 < nSeg bs k) :
    segS P bs k (i + 1) = segS P bs k i + 2 * lenAtom P (bit bs i) k + lenK P k := by
  rw [segS_succ]; simp [lenUnit, lenSep, hi]; ring

theorem segE_le_fS (k i : ℕ) (hi : i < nSeg bs k) :
    segS P bs k i + 2 * lenAtom P (bit bs i) k ≤ fS P bs k := by
  unfold fS
  rcases (show i = nSeg bs k - 1 ∨ i + 1 ≤ nSeg bs k - 1 by omega) with rfl | h
  · exact le_rfl
  · have h1 := segS_mono P bs k h
    rw [segS_succ_border P bs k i (by omega)] at h1
    omega

theorem lenIt_eq (hbs : bs ≠ []) {k : ℕ} (hk : 1 ≤ k) :
    iS P bs k + lenIt P bs k = fS P bs k + lenOm P k := by
  have hm := nSeg_pos bs hbs hk
  unfold fS lenIt
  obtain ⟨m, hm'⟩ : ∃ m, nSeg bs k = m + 1 := ⟨nSeg bs k - 1, by omega⟩
  rw [hm', sum_range_succ, Nat.add_sub_cancel]
  simp only [segS, lenUnit, lenSep, hm', lt_irrefl, ↓reduceIte]; ring

theorem iS_succ (hbs : bs ≠ []) {k : ℕ} (hk : 1 ≤ k) :
    iS P bs (k + 1) = fS P bs k + lenOm P k := by
  rw [← lenIt_eq P bs hbs hk]
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  simp [iS, sum_range_succ]

theorem iS_mono {k k' : ℕ} (h : k ≤ k') : iS P bs k ≤ iS P bs k' := by
  unfold iS
  exact sum_le_sum_of_subset (range_subset_range.2 (by omega))

variable {P}

theorem iS_lt_fS (hP1 : ∀ k, 1 ≤ P k) (hbs : bs ≠ []) {k : ℕ} (hk : 1 ≤ k) :
    iS P bs k + lenAtom P (bit bs 0) k < fS P bs k := by
  have := segE_le_fS P bs k 0 (nSeg_pos bs hbs hk)
  have := lenAtom_pos P hP1 (bit bs 0) k
  simp at *; omega

theorem iS_le_fS (hP1 : ∀ k, 1 ≤ P k) (hbs : bs ≠ []) {k : ℕ} (hk : 1 ≤ k) :
    iS P bs k ≤ fS P bs k := (Nat.le_add_right _ _).trans (iS_lt_fS bs hP1 hbs hk).le

theorem fS_lt_iS_succ (hP1 : ∀ k, 1 ≤ P k) (hbs : bs ≠ []) {k : ℕ} (hk : 1 ≤ k) :
    fS P bs k < iS P bs (k + 1) := by
  rw [iS_succ P bs hbs hk]
  have : 1 ≤ lenOm P k := by
    unfold lenOm
    have h1 : 1 ≤ 2 * k - 1 := by omega
    have h2 : 1 ≤ lenK P k := by
      unfold lenK; have hx := lenX_pos P hP1 k; have := lenA_pos P hP1 (8 * k)
      exact one_le_mul (by omega) hx
    have h3 := lenX_pos P hP1 k
    exact one_le_mul (one_le_mul h1 h2) h3
  omega

theorem fS_mono (hP1 : ∀ k, 1 ≤ P k) (hbs : bs ≠ []) {k k' : ℕ} (hk : 1 ≤ k) (h : k ≤ k') :
    fS P bs k ≤ fS P bs k' := by
  rcases h.lt_or_eq with h | rfl
  · have h1 := fS_lt_iS_succ bs hP1 hbs hk
    have h2 := iS_mono P bs (show k + 1 ≤ k' by omega)
    have h3 := iS_lt_fS bs hP1 hbs (show 1 ≤ k' by omega)
    omega
  · exact le_rfl

theorem two_lenAtom_le_lenK (hP : Monotone P) (b : Bool) (k : ℕ) :
    2 * lenAtom P b k ≤ 2 * (lenB P (4 * k) + lenA P (8 * k)) := by
  have h1 := lenB_mono hP (show 2 * k ≤ 4 * k by omega)
  have h2 := lenA_mono hP (show 4 * k ≤ 8 * k by omega)
  unfold lenAtom; split_ifs <;> omega

/-- An atom of iteration `k` is short compared to a border of iteration `k'` if `k ≤ 2k'`. -/
theorem two_lenAtom_le_of_le (hP : Monotone P) (b : Bool) {k k' : ℕ} (h : k ≤ 2 * k') :
    2 * lenAtom P b k ≤ 2 * (lenB P (4 * k') + lenA P (8 * k')) := by
  have h1 := lenB_mono hP (show 2 * k ≤ 4 * k' by omega)
  have h2 := lenA_mono hP (show 4 * k ≤ 8 * k' by omega)
  unfold lenAtom; split_ifs <;> omega

theorem le_lenK (hP1 : ∀ k, 1 ≤ P k) (k : ℕ) :
    2 * (lenB P (4 * k) + lenA P (8 * k)) ≤ lenK P k := by
  unfold lenK; have := lenX_pos P hP1 k; exact Nat.le_mul_of_pos_right _ this

/-- The length of a piece: `|T(k)| ≤ (2k-1)|K(k)|`. -/
theorem fS_le_piece (hP : Monotone P) (hP1 : ∀ k, 1 ≤ P k) (hbs : bs ≠ []) {k : ℕ} (hk : 1 ≤ k) :
    fS P bs k ≤ iS P bs k + (2 * k - 1) * lenK P k := by
  have hm := nSeg_pos bs hbs hk
  have hmk := nSeg_le bs k
  have hA : ∀ i, 2 * lenAtom P (bit bs i) k ≤ lenK P k := fun i =>
    (two_lenAtom_le_lenK hP _ k).trans (le_lenK hP1 k)
  -- segment starts grow by at most `2|K(k)|` per segment
  have hseg : ∀ i, i < nSeg bs k → segS P bs k i ≤ iS P bs k + i * (2 * lenK P k) := by
    intro i hi
    induction i with
    | zero => simp
    | succ i ih =>
      rw [segS_succ_border P bs k i hi]
      have := ih (by omega); have := hA i; nlinarith
  unfold fS
  have h1 := hseg (nSeg bs k - 1) (by omega)
  have h2 := hA (nSeg bs k - 1)
  have h3 : (nSeg bs k - 1) * (2 * lenK P k) + lenK P k ≤ (2 * k - 1) * lenK P k := by
    have : (nSeg bs k - 1) * 2 + 1 ≤ 2 * k - 1 := by omega
    nlinarith
  omega

/-- The route of the first `N` iterations is covered by `piBound P N`. -/
theorem fS_le_piBound (hP : Monotone P) (hP1 : ∀ k, 1 ≤ P k) (hbs : bs ≠ []) {N : ℕ}
    (hN : 1 ≤ N) : fS P bs N ≤ piBound P N := by
  have h1 := fS_lt_iS_succ bs hP1 hbs hN
  have : iS P bs (N + 1) ≤ piBound P N := by
    unfold iS piBound
    simp only [Nat.add_sub_cancel]
    apply sum_le_sum
    intro t _
    have := lenIt_eq P bs hbs (show 1 ≤ t + 1 by omega)
    have := fS_le_piece bs hP hP1 hbs (show 1 ≤ t + 1 by omega)
    omega
  omega

end Podc.AsyncRendezvousPoly
