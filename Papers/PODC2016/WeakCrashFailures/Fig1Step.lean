import Papers.PODC2016.WeakCrashFailures.Fig1Inv

/-!
# Fig. 1: basic step lemmas, preservation of doom and of tags
-/

namespace Podc.WeakCrashFailures.Fig1

open Finset

variable {n : ℕ} {x : Fin n → ℕ}

/-! ### Frame lemmas (no invariant needed) -/

lemma stAt_of_lt {C : Cfg n} {j : ℕ} (h : j < n) : stAt C j = C.st ⟨j, h⟩ := by
  simp [stAt, h]

lemma inAt_of_lt {C : Cfg n} {j : ℕ} (h : j < n) : inAt C j = C.inr ⟨j, h⟩ := by
  simp [inAt, h]

@[simp] lemma setPc_st (i : Fin n) (c : PC) (C : Cfg n) : (setPc i c C).st = C.st := rfl
@[simp] lemma setPc_inr (i : Fin n) (c : PC) (C : Cfg n) : (setPc i c C).inr = C.inr := rfl
@[simp] lemma setPc_dec (i : Fin n) (c : PC) (C : Cfg n) : (setPc i c C).dec = C.dec := rfl
@[simp] lemma setPc_pc_self (i : Fin n) (c : PC) (C : Cfg n) : (setPc i c C).pc i = c := by
  simp [setPc]
lemma setPc_pc_ne {i k : Fin n} (h : k ≠ i) (c : PC) (C : Cfg n) : (setPc i c C).pc k = C.pc k := by
  simp [setPc, Function.update_of_ne h]

lemma step_pc_ne {i k : Fin n} (h : k ≠ i) (C : Cfg n) : (step x i C).pc k = C.pc k := by
  unfold step
  split <;> (try split) <;> (try split_ifs) <;> (try split) <;>
    simp [setPc, Function.update_of_ne h]

lemma step_st_ne {i k : Fin n} (h : k ≠ i) (C : Cfg n) : (step x i C).st k = C.st k := by
  unfold step
  split <;> (try split) <;> (try split_ifs) <;> (try split) <;>
    simp [setPc, Function.update_of_ne h]

lemma step_inr_ne {i k : Fin n} (h : k ≠ i) (C : Cfg n) : (step x i C).inr k = C.inr k := by
  unfold step
  split <;> (try split) <;> (try split_ifs) <;> (try split) <;>
    simp [setPc, Function.update_of_ne h]

lemma step_dec_isSome {i : Fin n} {C : Cfg n} (h : C.dec.isSome) : (step x i C).dec.isSome := by
  unfold step
  split <;> (try split) <;> (try split_ifs) <;> (try split) <;>
    simp_all [setPc]

lemma step_done {i : Fin n} {C : Cfg n} {v : ℕ} (h : C.pc i = .done v) : step x i C = C := by
  simp [step, h]

/-- The only write to `state[i]` (line 8). -/
lemma step_st_self (i : Fin n) (C : Cfg n) :
    (step x i C).st i = C.st i ∨ ∃ r j cnt mx, C.pc i = .scan r j cnt mx ∧ ¬ j < n ∧
      cnt ≠ n - 1 ∧ (step x i C).st i = r := by
  unfold step
  split <;> (try split) <;> (try split_ifs) <;> (try split) <;>
    simp_all [setPc]

/-! ### Monotonicity of the state registers -/

lemma st_step_mono {C : Cfg n} (hI : Inv x C) (i k : Fin n) : C.st k ≤ (step x i C).st k := by
  by_cases hk : k = i
  · subst hk
    rcases step_st_self (x := x) k C with h | ⟨r, j, cnt, mx, hpc, -, -, h⟩
    · rw [h]
    · have := hI.li k
      rw [hpc] at this
      obtain ⟨-, -, -, h1, -⟩ := this
      omega
  · rw [step_st_ne hk]

lemma st_step_le3 {C : Cfg n} (hI : Inv x C) (i k : Fin n) : (step x i C).st k ≤ 3 := by
  by_cases hk : k = i
  · subst hk
    rcases step_st_self (x := x) k C with h | ⟨r, j, cnt, mx, hpc, -, -, h⟩
    · rw [h]; exact hI.le3 k
    · have := hI.li k
      rw [hpc] at this
      obtain ⟨-, h3, -⟩ := this
      omega
  · rw [step_st_ne hk]; exact hI.le3 k

/-! ### Doom is preserved -/

lemma doomed_frame {C C' : Cfg n} {r : ℕ} {y : Fin n} (h : DoomedR C r y)
    (hpc : C'.pc y = C.pc y) (hst : C'.st y = C.st y) (hmono : ∀ k, C.st k ≤ C'.st k) :
    DoomedR C' r y :=
  ⟨fun k hk => le_trans (h.1 k hk) (hmono k), hst ▸ h.2.1, hpc ▸ h.2.2⟩

/-- A doomed process stays doomed (it never writes `r` into its state). -/
lemma doomed_step {C : Cfg n} (hI : Inv x C) {r : ℕ} (hr1 : 1 ≤ r) (hr3 : r ≤ 3) {y : Fin n}
    (h : DoomedR C r y) (i : Fin n) : DoomedR (step x i C) r y := by
  by_cases hyi : y = i
  · subst hyi
    obtain ⟨hoth, hlt, hpre⟩ := h
    have hli := hI.li y
    refine ⟨fun k hk => by rw [step_st_ne hk]; exact hoth k hk, ?_, ?_⟩
    · rcases step_st_self (x := x) y C with h' | ⟨r', j, cnt, mx, hpc, hj, hcnt, h'⟩
      · rw [h']; exact hlt
      · rw [h']
        rw [hpc] at hpre
        rcases hpre with hpre | ⟨rfl, hpre⟩
        · exact hpre
        · exact absurd (hpre.trans (cntLt_of_le (Nat.le_of_not_lt hj) y)) hcnt
    · unfold step
      generalize hc : C.pc y = c at hpre hli
      cases c with
      | start => simp only [Function.update_self]; simp [PreRpc]; omega
      | scan r' j cnt mx =>
        simp only [PreRpc] at hpre
        obtain ⟨h1, h2, h3, h4, -⟩ := hli
        dsimp only
        split_ifs with hj hle hcn
        · simp only [setPc_pc_self, PreRpc]
          rcases hpre with hpre | ⟨rfl, hpre⟩
          · exact Or.inl hpre
          · right; refine ⟨rfl, ?_⟩
            rw [cntLt_succ, dite_eq_left_of_eq_true (eq_true hj), hpre]
            have : (⟨j, hj⟩ : Fin n) ≠ y := by
              rintro he
              rw [stAt_of_lt hj, he] at hle
              omega
            simp [this]
        · simp only [setPc_pc_self, PreRpc]
          rcases hpre with hpre | ⟨rfl, hpre⟩
          · exact Or.inl hpre
          · right; refine ⟨rfl, ?_⟩
            rw [cntLt_succ, dite_eq_left_of_eq_true (eq_true hj), hpre]
            have : (⟨j, hj⟩ : Fin n) = y := by
              by_contra he
              exact hle (by rw [stAt_of_lt hj]; exact hoth _ he)
            simp [this]
        · simp [PreRpc]
        · simp only [Function.update_self, PreRpc]
          rcases hpre with hpre | ⟨rfl, hpre⟩
          · exact hpre
          · exact absurd (hpre.trans (cntLt_of_le (Nat.le_of_not_lt hj) y)) hcn
      | scanIn r' j cnt mx =>
        simp only [setPc_pc_self, PreRpc] at hpre ⊢
        rcases hpre with hpre | ⟨rfl, hpre⟩
        · exact Or.inl hpre
        · exact Or.inr ⟨rfl, hpre⟩
      | wait r' j cnt mx =>
        simp only [PreRpc] at hpre
        dsimp only
        by_cases hj : j < n
        · simp only [hj, ite_true, setPc_pc_self, PreRpc]; exact hpre
        · simp only [hj, ite_false]
          cases hd : C.dec with
          | some d => simp [PreRpc]
          | none =>
            dsimp only
            split_ifs with h1 h2 h3
            · simp only [setPc_pc_self, PreRpc]
              rcases Nat.lt_or_ge (r' + 1) r with h | h
              · exact Or.inl h
              · exact Or.inr ⟨by omega, by simp⟩
            · omega
            · omega
            · simpa [PreRpc] using hpre
      | chk => simp [PreRpc] at hpre
      | chkIn => simp [PreRpc] at hpre
      | fin => simp [PreRpc] at hpre
      | finDec => simp [PreRpc] at hpre
      | finIn => simp [PreRpc] at hpre
      | done v => simp [hc, PreRpc]
  · exact doomed_frame h (step_pc_ne hyi C) (step_st_ne hyi C) (st_step_mono hI i)

/-! ### Tags are preserved -/

lemma tagFact_step {C : Cfg n} (hI : Inv x C) {t : Tag n} (h : TagFact C t) (i : Fin n) :
    TagFact (step x i C) t := by
  cases t with
  | all =>
    intro k
    have := h k
    have h1 := st_step_mono hI i k
    have h2 := st_step_le3 hI i k
    omega
  | ex y =>
    obtain ⟨hlt, hfr⟩ := h
    by_cases hyi : y = i
    · subst hyi
      rcases hfr with ⟨v, hv⟩ | hd
      · rw [step_done hv]; exact ⟨hlt, Or.inl ⟨v, hv⟩⟩
      · have hd' := doomed_step hI (by omega) le_rfl hd y
        refine ⟨fun k hk => ?_, Or.inr hd'⟩
        have := hd'.1 k hk
        have := hd'.2.1
        omega
    · refine ⟨fun k hk => ?_, ?_⟩
      · rw [step_st_ne hyi]
        exact lt_of_lt_of_le (hlt k hk) (st_step_mono hI i k)
      · rcases hfr with ⟨v, hv⟩ | hd
        · exact Or.inl ⟨v, by rw [step_pc_ne hyi]; exact hv⟩
        · exact Or.inr (doomed_frame hd (step_pc_ne hyi C) (step_st_ne hyi C) (st_step_mono hI i))

end Podc.WeakCrashFailures.Fig1
