import Papers.PODC2023.PPDoubleExpThresholds.Regs

/-!
# Basic facts about the configuration types

How `Proper`, `High`, `Geq`, … behave under changes confined to one level (`Off`), and under the
transformation `lg` of `Large`.
-/

namespace Podc.PPDoubleExpThresholds

variable {n : ℕ}

theorem N_pos {i : ℕ} (hi : 1 ≤ i) : 0 < N i := by
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  simp [N]

theorem N_succ (i : ℕ) : N (i + 1) = (N i + 1) ^ 2 := rfl

/-! ### `Off` -/

theorem Off.refl (C : Reg n → ℕ) (i : ℕ) : Off C C i := fun _ _ => rfl

theorem Off.trans {C C' C'' : Reg n → ℕ} {i : ℕ} (h : Off C C' i) (h' : Off C' C'' i) :
    Off C C'' i := fun z hz => (h' z hz).trans (h z hz)

theorem Off.symm {C C' : Reg n → ℕ} {i : ℕ} (h : Off C C' i) : Off C' C i :=
  fun z hz => (h z hz).symm

theorem off_mv (C : Reg n → ℕ) {x y : Reg n} {i : ℕ} (hx : x.lvl = i) (hy : y.lvl = i) :
    Off C (mv C x y) i := by
  intro z hz
  have h1 : z ≠ x := fun h => hz (by rw [h]; exact hx)
  have h2 : z ≠ y := fun h => hz (by rw [h]; exact hy)
  simp [mv, h1, h2]

theorem off_swp (C : Reg n → ℕ) {x y : Reg n} {i : ℕ} (hx : x.lvl = i) (hy : y.lvl = i) :
    Off C (swp C x y) i := by
  intro z hz
  have h1 : z ≠ x := fun h => hz (by rw [h]; exact hx)
  have h2 : z ≠ y := fun h => hz (by rw [h]; exact hy)
  simp [swp, Equiv.swap_apply_of_ne_of_ne h1 h2]

theorem off_lg (C : Reg n → ℕ) {x y : Reg n} {i : ℕ} (hx : x.lvl = i) (hy : y.lvl = i) (m : ℕ) :
    Off C (lg C x y m) i := by
  intro z hz
  exact lg_apply_other C (fun h => hz (by rw [h]; exact hx)) (fun h => hz (by rw [h]; exact hy)) m

theorem off_shift (C : Reg n → ℕ) {x y : Reg n} {i : ℕ} (hx : x.lvl = i) (hy : y.lvl = i)
    (m : ℕ) : Off C (shift C x y m) i := by
  intro z hz
  exact shift_apply_other C (fun h => hz (by rw [h]; exact hx)) (fun h => hz (by rw [h]; exact hy))
    m

theorem Off.apply_reg {C C' : Reg n → ℕ} {i l : ℕ} (h : Off C C' i) (hl : 1 ≤ l) (hln : l ≤ n)
    (hli : l ≠ i) (k : Fin 4) : C' (reg n l k) = C (reg n l k) :=
  h _ (by rw [lvl_reg hl hln]; exact hli)

/-! ### Invariance of the types -/

theorem Proper.mono {C : Reg n → ℕ} {i j : ℕ} (h : Proper C i) (hj : j ≤ i) : Proper C j :=
  fun l hl hlj => h l hl (hlj.trans hj)

theorem proper_iff_of_agree {C C' : Reg n → ℕ} {j : ℕ} (hj : j ≤ n)
    (h : ∀ l, 1 ≤ l → l ≤ j → ∀ k, C' (reg n l k) = C (reg n l k)) :
    Proper C' j ↔ Proper C j := by
  unfold Proper
  refine forall_congr' fun l => forall_congr' fun hl => forall_congr' fun hlj => ?_
  simp only [h l hl hlj]

theorem Off.proper_iff {C C' : Reg n → ℕ} {i j : ℕ} (h : Off C C' i) (hji : j < i)
    (hin : i ≤ n) : Proper C' j ↔ Proper C j :=
  proper_iff_of_agree (by omega) fun l hl hlj k => h.apply_reg hl (by omega) (by omega) k

theorem Off.psum_eq {C C' : Reg n → ℕ} {i l : ℕ} (h : Off C C' i) (hl : 1 ≤ l) (hln : l ≤ n)
    (hli : l ≠ i) (k : Fin 4) : psum C' l k = psum C l k := by
  simp [psum, h.apply_reg hl hln hli]

theorem Off.high_iff {C C' : Reg n → ℕ} {i j : ℕ} (h : Off C C' i) (hj : 1 ≤ j) (hji : j < i)
    (hin : i ≤ n) : High C' j ↔ High C j := by
  unfold High
  rw [h.proper_iff (by omega : j - 1 < i) hin, h.proper_iff hji hin,
    h.psum_eq hj (by omega) (by omega), h.psum_eq hj (by omega) (by omega)]

theorem Off.geq_iff {C C' : Reg n → ℕ} {i j : ℕ} (h : Off C C' i) (hj : 1 ≤ j) (hji : j < i)
    (hin : i ≤ n) : Geq C' j ↔ Geq C j := by
  unfold Geq
  rw [h.proper_iff (by omega : j - 1 < i) hin, h.psum_eq hj (by omega) (by omega),
    h.psum_eq hj (by omega) (by omega)]

/-- Proper at level `i` in terms of the four registers. -/
theorem proper_succ_iff {C : Reg n → ℕ} {i : ℕ} (hi : 1 ≤ i) :
    Proper C i ↔ Proper C (i - 1) ∧ C (reg n i 0) = 0 ∧ C (reg n i 1) = N i ∧
      C (reg n i 2) = 0 ∧ C (reg n i 3) = N i := by
  constructor
  · intro h
    exact ⟨h.mono (by omega), h i hi le_rfl⟩
  · rintro ⟨h, h'⟩ l hl hli
    rcases Nat.lt_or_ge l i with hlt | hge
    · exact h l hl (by omega)
    · obtain rfl : l = i := by omega
      exact h'

theorem Proper.wproper {C : Reg n → ℕ} {i : ℕ} (hi : 1 ≤ i) (h : Proper C i) : WProper C i := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := (proper_succ_iff hi).1 h
  exact ⟨h1, by simp [psum, bar, h2, h3], by simp [psum, bar, h4, h5]⟩

theorem Proper.geq {C : Reg n → ℕ} {i : ℕ} (hi : 1 ≤ i) (h : Proper C i) : Geq C i := by
  obtain ⟨h1, h2, h3⟩ := h.wproper hi
  exact ⟨h1, h2.ge, h3.ge⟩

theorem High.geq {C : Reg n → ℕ} {i : ℕ} (h : High C i) : Geq C i := ⟨h.1, h.2.2⟩

theorem WProper.geq {C : Reg n → ℕ} {i : ℕ} (h : WProper C i) : Geq C i :=
  ⟨h.1, h.2.1.ge, h.2.2.ge⟩

/-- `psum` of the pair of `k` is the `x`- or `y`-sum. -/
theorem psum_pair (C : Reg n → ℕ) (i : ℕ) (k : Fin 4) :
    psum C i k = psum C i 0 ∨ psum C i k = psum C i 2 := by
  fin_cases k <;> simp [psum, bar] <;> omega

theorem Geq.psum {C : Reg n → ℕ} {i : ℕ} (h : Geq C i) (k : Fin 4) : N i ≤ psum C i k := by
  rcases psum_pair C i k with h' | h' <;> rw [h']
  exacts [h.2.1, h.2.2]

theorem WProper.psum {C : Reg n → ℕ} {i : ℕ} (h : WProper C i) (k : Fin 4) : psum C i k = N i := by
  rcases psum_pair C i k with h' | h' <;> rw [h']
  exacts [h.2.1, h.2.2]

/-! ### The transformation of `Large` -/

section lg

variable {C : Reg n → ℕ} {i : ℕ} (hi : 1 ≤ i) (hin : i ≤ n) (k : Fin 4)
include hi hin

theorem lg_off (m : ℕ) : Off C (lg C (reg n i k) (reg n i (bar k)) m) i :=
  off_lg C (lvl_reg hi hin k) (lvl_reg hi hin _) m

theorem psum_lg {m : ℕ} (hm : m ≤ C (reg n i k)) (k' : Fin 4) :
    psum (lg C (reg n i k) (reg n i (bar k)) m) i k' = psum C i k' := by
  have hne := reg_ne_bar hi hin k
  have key : psum (lg C (reg n i k) (reg n i (bar k)) m) i k = psum C i k := by
    simp only [psum, lg_apply_x _ hne, lg_apply_y]; omega
  by_cases h1 : k' = k
  · subst h1; exact key
  by_cases h2 : k' = bar k
  · subst h2; rw [psum_bar, psum_bar, key]
  have h3 : bar k' ≠ k := fun h => h2 (by rw [← h, bar_bar])
  have h4 : bar k' ≠ bar k := fun h => h1 (by rw [← bar_bar k', h, bar_bar])
  have r1 : reg n i k' ≠ reg n i k := by rw [Ne, reg_inj hi hin hi hin]; simp [h1]
  have r2 : reg n i k' ≠ reg n i (bar k) := by rw [Ne, reg_inj hi hin hi hin]; simp [h2]
  have r3 : reg n i (bar k') ≠ reg n i k := by rw [Ne, reg_inj hi hin hi hin]; simp [h3]
  have r4 : reg n i (bar k') ≠ reg n i (bar k) := by rw [Ne, reg_inj hi hin hi hin]; simp [h4]
  simp only [psum, lg_apply_other _ r1 r2, lg_apply_other _ r3 r4]

theorem proper_lg_iff (hm : N i ≤ C (reg n i k)) :
    Proper (lg C (reg n i k) (reg n i (bar k)) (N i)) i ↔ Proper C i := by
  have hN := N_pos hi
  rw [proper_succ_iff hi, proper_succ_iff hi, (lg_off hi hin k _).proper_iff (by omega) hin]
  fin_cases k <;> simp [lg, Function.update_apply, reg_inj hi hin hi hin, bar] at hm ⊢ <;> omega

theorem High.lg (h : High C i) (hm : N i ≤ C (reg n i k)) :
    High (lg C (reg n i k) (reg n i (bar k)) (N i)) i := by
  refine ⟨((lg_off hi hin k _).proper_iff (by omega) hin).2 h.1,
    fun h' => h.2.1 ((proper_lg_iff hi hin k hm).1 h'), ?_, ?_⟩ <;>
    rw [psum_lg hi hin k hm]
  exacts [h.2.2.1, h.2.2.2]

theorem Geq.lg (h : Geq C i) (hm : N i ≤ C (reg n i k)) :
    Geq (lg C (reg n i k) (reg n i (bar k)) (N i)) i := by
  refine ⟨((lg_off hi hin k _).proper_iff (by omega) hin).2 h.1, ?_, ?_⟩ <;>
    rw [psum_lg hi hin k hm]
  exacts [h.2.1, h.2.2]

theorem lg_eq_self (h : WProper C i) (hm : N i ≤ C (reg n i k)) :
    lg C (reg n i k) (reg n i (bar k)) (N i) = C := by
  have hs := h.psum k
  simp only [psum] at hs
  have hne := reg_ne_bar hi hin k
  funext z
  by_cases h1 : z = reg n i k
  · subst h1; rw [lg_apply_x _ hne]; omega
  by_cases h2 : z = reg n i (bar k)
  · subst h2; rw [lg_apply_y]; omega
  rw [lg_apply_other _ h1 h2]

end lg

end Podc.PPDoubleExpThresholds
