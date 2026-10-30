import Papers.PODC2023.PPDoubleExpThresholds.Base
import Mathlib.Tactic.Ring

/-!
# The random walk of `Large` on proper configurations

For `Large(x)` at level `i ≥ 2` started on an `(i−1)`-proper configuration `C`, every configuration
reached in the loop is described by `WalkSt C i k c e D`: `c` units have been moved from `x` to `x̄`, and
the level-`(i−1)` registers form a weakly proper two-digit counter with value `e`.
-/

namespace Podc.PPDoubleExpThresholds

variable {n : ℕ}

theorem Off.wproper_iff {C C' : Reg n → ℕ} {i j : ℕ} (h : Off C C' i) (hj : 1 ≤ j) (hji : j < i)
    (hin : i ≤ n) : WProper C' j ↔ WProper C j := by
  unfold WProper
  rw [h.proper_iff (by omega : j - 1 < i) hin, h.psum_eq hj (by omega) (by omega),
    h.psum_eq hj (by omega) (by omega)]

theorem WProper.le {C : Reg n → ℕ} {i : ℕ} (h : WProper C i) (k : Fin 4) : C (reg n i k) ≤ N i := by
  have := h.psum k; unfold Podc.PPDoubleExpThresholds.psum at this; omega

theorem WProper.bar_eq {C : Reg n → ℕ} {i : ℕ} (h : WProper C i) (k : Fin 4) :
    C (reg n i (bar k)) = N i - C (reg n i k) := by
  have := h.psum k; unfold Podc.PPDoubleExpThresholds.psum at this; omega

/-- The counter of a weakly proper configuration is below `N_{i+1}`. -/
theorem WProper.ctr_lt {C : Reg n → ℕ} {i : ℕ} (h : WProper C i) : ctr C i 0 2 < N (i + 1) := by
  have h0 := h.le 0; have h2 := h.le 2
  simp only [ctr, N_succ]
  nlinarith

/-- The counter `(x̄, ȳ)` is the complement of the counter `(x, y)`. -/
theorem WProper.ctr_bar {C : Reg n → ℕ} {i : ℕ} (h : WProper C i) :
    ctr C i 1 3 + ctr C i 0 2 + 1 = N (i + 1) := by
  have h1 : C (reg n i 1) = N i - C (reg n i 0) := h.bar_eq 0
  have h3 : C (reg n i 3) = N i - C (reg n i 2) := h.bar_eq 2
  have h0 := h.le 0; have h2 := h.le 2
  simp only [ctr, N_succ, h1, h3]
  zify [h0, h2]
  ring

theorem WProper.ctr_eq_zero {C : Reg n → ℕ} {i : ℕ} :
    ctr C i 0 2 = 0 ↔ C (reg n i 0) = 0 ∧ C (reg n i 2) = 0 := by
  simp only [ctr]
  constructor
  · intro h
    have : C (reg n i 0) * (N i + 1) = 0 := by omega
    simp at this; omega
  · rintro ⟨h0, h2⟩; simp [h0, h2]

section walk

variable (C : Reg n → ℕ) (i : ℕ) (k : Fin 4)

/-- The state of the random walk of `Large(x)`: `c` units moved from `x = reg n i k` to `x̄`, the
counter on level `i − 1` has value `e`. -/
def WalkSt (c e : ℕ) (D : Reg n → ℕ) : Prop :=
  WProper D (i - 1) ∧ ctr D (i - 1) 0 2 = e ∧
    Off (shift C (reg n i k) (reg n i (bar k)) c) D (i - 1) ∧ c ≤ C (reg n i k)

variable {C i k} (hi : 2 ≤ i) (hin : i ≤ n)
include hi hin

theorem WalkSt.start (hC : Proper C (i - 1)) : WalkSt C i k 0 0 C := by
  refine ⟨hC.wproper (by omega), ?_, ?_, Nat.zero_le _⟩
  · obtain ⟨-, h0, -, h2, -⟩ := (proper_succ_iff (by omega)).1 hC
    simp [ctr, h0, h2]
  · rw [shift_zero]; exact Off.refl _ _

theorem WalkSt.x {c e : ℕ} {D : Reg n → ℕ} (h : WalkSt C i k c e D) : D (reg n i k) = C (reg n i k) - c := by
  rw [h.2.2.1 _ (by rw [lvl_reg (by omega) hin]; omega), shift_apply_x]

theorem WalkSt.xb {c e : ℕ} {D : Reg n → ℕ} (h : WalkSt C i k c e D) :
    D (reg n i (bar k)) = C (reg n i (bar k)) + c := by
  rw [h.2.2.1 _ (by rw [lvl_reg (by omega) hin]; omega),
    shift_apply_y _ (reg_ne_bar (by omega) hin k)]

theorem WalkSt.move {c e : ℕ} {D : Reg n → ℕ} (h : WalkSt C i k c e D) (hc : c < C (reg n i k)) :
    WalkSt C i k (c + 1) e (mv D (reg n i k) (reg n i (bar k))) := by
  have hne := reg_ne_bar (by omega) hin k
  have hoff := off_mv D (lvl_reg (by omega) hin k) (lvl_reg (by omega) hin (bar k))
  refine ⟨(hoff.wproper_iff (by omega) (by omega) hin).2 h.1, ?_, ?_, hc⟩
  · rw [← h.2.1]; simp only [ctr]
    rw [hoff.apply_reg (by omega) (by omega) (by omega), hoff.apply_reg (by omega) (by omega) (by omega)]
  · intro z hz
    by_cases hzi : z.lvl = i
    · have hx := h.x hi hin; have hxb := h.xb hi hin
      by_cases h1 : z = reg n i k
      · subst h1; simp only [mv, shift, hne, if_true, if_false]; omega
      by_cases h2 : z = reg n i (bar k)
      · subst h2; simp only [mv, shift, Ne.symm hne, if_true, if_false]; omega
      · simp only [mv, shift, h1, h2, if_false, Nat.sub_zero, Nat.add_zero]
        rw [h.2.2.1 z hz, shift_apply_other _ h1 h2]
    · rw [hoff z (by omega), h.2.2.1 z hz, shift_apply_other, shift_apply_other] <;>
        (intro h'; apply hzi; rw [h', lvl_reg (by omega) hin])

theorem WalkSt.move_back {c e : ℕ} {D : Reg n → ℕ} (h : WalkSt C i k (c + 1) e D) :
    WalkSt C i k c e (mv D (reg n i (bar k)) (reg n i k)) := by
  have hne := reg_ne_bar (by omega) hin k
  have hoff := off_mv D (lvl_reg (by omega) hin (bar k)) (lvl_reg (by omega) hin k)
  refine ⟨(hoff.wproper_iff (by omega) (by omega) hin).2 h.1, ?_, ?_, by have := h.2.2.2; omega⟩
  · rw [← h.2.1]; simp only [ctr]
    rw [hoff.apply_reg (by omega) (by omega) (by omega), hoff.apply_reg (by omega) (by omega) (by omega)]
  · intro z hz
    by_cases hzi : z.lvl = i
    · have hx := h.x hi hin; have hxb := h.xb hi hin
      have hc := h.2.2.2
      by_cases h1 : z = reg n i k
      · subst h1; simp only [mv, shift, hne, if_true, if_false]; omega
      by_cases h2 : z = reg n i (bar k)
      · subst h2; simp only [mv, shift, Ne.symm hne, if_true, if_false]; omega
      · simp only [mv, shift, h1, h2, if_false, Nat.sub_zero, Nat.add_zero]
        rw [h.2.2.1 z hz, shift_apply_other _ h1 h2]
    · rw [hoff z (by omega), h.2.2.1 z hz, shift_apply_other, shift_apply_other] <;>
        (intro h'; apply hzi; rw [h', lvl_reg (by omega) hin])

/-- A change of the level-`(i−1)` registers keeping them weakly proper. -/
theorem WalkSt.change {c e e' : ℕ} {D D' : Reg n → ℕ} (h : WalkSt C i k c e D) (hw : WProper D' (i - 1))
    (hoff : Off D D' (i - 1)) (he : ctr D' (i - 1) 0 2 = e') : WalkSt C i k c e' D' :=
  ⟨hw, he, h.2.2.1.trans hoff, h.2.2.2⟩

theorem WalkSt.e_lt {c e : ℕ} {D : Reg n → ℕ} (h : WalkSt C i k c e D) : e < N i := by
  have := h.1.ctr_lt
  rw [show i - 1 + 1 = i by omega] at this
  rw [← h.2.1]; exact this

/-- At the end of the walk upwards: swapping gives the result of `Large`. -/
theorem WalkSt.final {D : Reg n → ℕ} (h : WalkSt C i k (N i) 0 D) (hC : Proper C (i - 1)) :
    swp D (reg n i k) (reg n i (bar k)) = lg C (reg n i k) (reg n i (bar k)) (N i) := by
  have hne := reg_ne_bar (by omega) hin k
  rw [← swp_shift_eq_lg C hne]
  congr 1
  funext z
  by_cases hz : z.lvl = i - 1
  · obtain rfl | ⟨l, k', hl, hln, rfl⟩ := z.eq_reg
    · simp [Reg.lvl] at hz; omega
    rw [lvl_reg hl hln] at hz
    subst hz
    have hz0 : (shift C (reg n i k) (reg n i (bar k)) (N i)) (reg n (i - 1) k') = C (reg n (i - 1) k') := by
      apply shift_apply_other <;> rw [Ne, reg_inj hl hln (by omega) hin] <;> omega
    rw [hz0]
    obtain ⟨h0, h2⟩ := WProper.ctr_eq_zero.1 h.2.1
    obtain ⟨-, c0, c1, c2, c3⟩ := (proper_succ_iff hl).1 hC
    have w1 := h.1.bar_eq 0; have w3 := h.1.bar_eq 2
    simp only [bar] at w1 w3
    fin_cases k' <;> simp_all
  · exact h.2.2.1 z hz

/-- At the end of the walk downwards: back at `C`. -/
theorem WalkSt.eq_start {D : Reg n → ℕ} (h : WalkSt C i k 0 0 D) (hC : Proper C (i - 1)) : D = C := by
  funext z
  by_cases hz : z.lvl = i - 1
  · obtain rfl | ⟨l, k', hl, hln, rfl⟩ := z.eq_reg
    · simp [Reg.lvl] at hz; omega
    rw [lvl_reg hl hln] at hz
    subst hz
    obtain ⟨h0, h2⟩ := WProper.ctr_eq_zero.1 h.2.1
    obtain ⟨-, c0, c1, c2, c3⟩ := (proper_succ_iff hl).1 hC
    have w1 := h.1.bar_eq 0; have w3 := h.1.bar_eq 2
    simp only [bar] at w1 w3
    fin_cases k' <;> simp_all
  · rw [h.2.2.1 z hz, shift_zero]

end walk

end Podc.PPDoubleExpThresholds

namespace Podc.PPDoubleExpThresholds

variable {n : ℕ}

/-- **Lemma 10(a)** from 10(b): on weakly `i`-proper configurations `Zero(x)` is a deterministic
zero test. -/
theorem zeroA_of_B {i : ℕ} (hi : 1 ≤ i) (hin : i ≤ n) (hB : ZeroB n i) (k : Fin 4)
    {C : Reg n → ℕ} (OF : Bool) (hC : WProper C i) :
    Spec n (.zero i k) C OF fun C' b => C' = C ∧ b = decide (C (reg n i k) = 0) := by
  obtain ⟨hR, h2, h3⟩ := hB k C OF hC.1 (hC.psum k).ge
  refine ⟨fun C' OF' b => ?_, h2, h3⟩
  rw [hR]
  have hs := hC.psum k
  unfold psum at hs
  constructor
  · rintro ⟨rfl, ⟨rfl, rfl, hx⟩ | ⟨rfl, hx, rfl⟩⟩
    · exact ⟨rfl, rfl, by simp; omega⟩
    · refine ⟨rfl, ?_, by simp; omega⟩
      have := lg_eq_self hi hin (bar k) (C := C) hC (by simpa using hx)
      simpa using this
  · rintro ⟨rfl, h1, rfl⟩
    rw [h1]
    refine ⟨rfl, ?_⟩
    by_cases h0 : C (reg n i k) = 0
    · refine .inr ⟨by simp [h0], by omega, ?_⟩
      have := lg_eq_self hi hin (bar k) (C := C) hC (by omega)
      simpa using this.symm
    · exact .inl ⟨by simp [h0], rfl, by omega⟩

/-- `AssertProper(0)` satisfies Lemma 9(a). -/
theorem apa_zero : APA n 0 := fun C OF _ => ap_zero C OF

end Podc.PPDoubleExpThresholds
