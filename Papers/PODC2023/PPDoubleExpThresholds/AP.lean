import Papers.PODC2023.PPDoubleExpThresholds.LargeB

/-!
# Lemma 9: `AssertProper(i)`
-/

namespace Podc.PPDoubleExpThresholds

open Program

variable {n : ℕ}

set_option hygiene false in
local macro "ins" : tactic => `(tactic| (rw [Program.instr, hcode]; try rfl))

/-- `Large(x̄)` on configurations with `x = 0` and `x̄ ≤ N` has no effect. -/
theorem large_bar_noeffect {i : ℕ} (hi : 1 ≤ i) (hin : i ≤ n) (hLB : LargeB n i) (k : Fin 4)
    {C : Reg n → ℕ} (OF : Bool) (hC : Proper C (i - 1)) (h0 : C (reg n i k) = 0)
    (hle : C (reg n i (bar k)) ≤ N i) :
    (∀ C' OF' b, (prog n).Returns (.large i (bar k)) C OF C' OF' b → OF' = OF ∧ C' = C) ∧
      ¬ (prog n).Restarts (.large i (bar k)) C OF ∧ (prog n).Terminates (.large i (bar k)) C OF := by
  obtain ⟨hR, h2, h3⟩ := hLB (bar k) C OF hC
  refine ⟨fun C' OF' b h => ?_, h2, h3⟩
  obtain ⟨rfl, ⟨-, rfl⟩ | ⟨-, hx, rfl⟩⟩ := (hR C' OF' b).1 h
  · exact ⟨rfl, rfl⟩
  · refine ⟨rfl, ?_⟩
    have hne := reg_ne_bar hi hin (bar k)
    simp only [bar_bar] at hne ⊢
    funext z
    by_cases h1 : z = reg n i (bar k)
    · subst h1; rw [lg_apply_x _ hne]; omega
    by_cases h2 : z = reg n i k
    · subst h2; rw [lg_apply_y]; omega
    rw [lg_apply_other _ h1 h2]

section

variable {i : ℕ} (hi : 1 ≤ i) (hin : i ≤ n)
include hi hin

theorem ap_fwd : ∀ pc ins, (prog n).instr (.assertProper i) pc = some ins →
    FwdOK ((prog n).code (.assertProper i)).length pc ins := by
  intro pc ins h
  have hcode := code_assertProper n hi
  have hlt := instr_lt h
  rw [hcode] at hlt ⊢
  rw [Program.instr, hcode] at h
  simp only [List.length_cons, List.length_nil] at hlt ⊢
  interval_cases pc <;> simp at h <;> subst h <;> simp [FwdOK]

/-- **Lemma 9(d)**: `AssertProper(i)` is robust (given robustness of its callees). -/
theorem ap_robust (hAPR : Robust n (.assertProper (i - 1))) (hLR : ∀ k, Robust n (.large i k)) :
    Robust n (.assertProper i) := by
  intro j hj hjn _ C OF hC
  refine forward_preserve (fun D => High D j) (by rw [code_assertProper n hi]; simp)
    (ap_fwd hi hin) (fun pc q tT tF hq D OF₁ hD => ?_) hC
  have hcode := code_assertProper n hi
  have hlt := instr_lt hq
  rw [hcode] at hlt
  rw [Program.instr, hcode] at hq
  simp only [List.length_cons, List.length_nil] at hlt
  interval_cases pc <;> simp at hq <;> obtain ⟨rfl, -, -⟩ := hq
  · exact hAPR j hj hjn trivial D OF₁ hD
  · exact hLR 1 j hj hjn trivial D OF₁ hD
  · exact hLR 3 j hj hjn trivial D OF₁ hD

/-- **Lemma 9(a)**: `post(C, AssertProper(i)) = {C}` for `i`-proper or `i`-low `C`. -/
theorem ap_A (hAPA : APA n (i - 1)) (hLB : LargeB n i) : APA n i := by
  intro C OF hC
  have hcode := code_assertProper n hi
  have hP : Proper C (i - 1) := by
    rcases hC with h | h
    · exact h.mono (by omega)
    · exact h.1
  have hx0 : C (reg n i 0) = 0 ∧ C (reg n i 2) = 0 ∧ C (reg n i 1) ≤ N i ∧ C (reg n i 3) ≤ N i := by
    rcases hC with h | h
    · obtain ⟨-, h0, h1, h2, h3⟩ := (proper_succ_iff hi).1 h; omega
    · exact ⟨h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩
  have L1 := large_bar_noeffect hi hin hLB 0 OF hP hx0.1 hx0.2.2.1
  have L3 := large_bar_noeffect hi hin hLB 2 OF hP hx0.2.1 hx0.2.2.2
  simp only [show bar 0 = 1 from rfl, show bar 2 = 3 from rfl] at L1 L3
  have A0 := hAPA C OF (.inl hP)
  -- invariant: registers `C`, no restart instruction reached
  let I : Loc (Reg n) → Prop := fun a => a.C = C ∧ a.OF = OF ∧ a.pc < 16 ∧
    a.pc ∉ ({2, 6, 9, 13} : Finset ℕ)
  have hI : ∀ a a', I a → (prog n).AStep (.assertProper i) a a' → I a' := by
    rintro ⟨pc, D, OF₁⟩ a' ⟨hD, hO, hlt, hpc⟩ hs
    simp only at hD hO hlt hpc
    subst hD hO
    rw [astep_iff] at hs
    interval_cases pc <;> simp at hpc <;>
      simp only [Program.instr, hcode, List.getElem?_cons_succ, List.getElem?_cons_zero] at hs
    · obtain ⟨C', OF', b, hr, rfl⟩ := hs
      obtain ⟨rfl, rfl, -⟩ := (A0.1 _ _ _).1 hr
      exact ⟨rfl, rfl, by simp⟩
    · rcases hs with ⟨h, rfl⟩ | rfl
      · omega
      · exact ⟨rfl, rfl, by simp⟩
    · subst hs; exact ⟨rfl, rfl, by simp⟩
    · obtain ⟨C', OF', b, hr, rfl⟩ := hs
      obtain ⟨rfl, rfl⟩ := L1.1 _ _ _ hr
      exact ⟨rfl, rfl, by simp⟩
    · rcases hs with ⟨h, rfl⟩ | rfl
      · omega
      · exact ⟨rfl, rfl, by simp⟩
    · subst hs; exact ⟨rfl, rfl, by simp⟩
    · rcases hs with ⟨h, rfl⟩ | rfl
      · omega
      · exact ⟨rfl, rfl, by simp⟩
    · subst hs; exact ⟨rfl, rfl, by simp⟩
    · obtain ⟨C', OF', b, hr, rfl⟩ := hs
      obtain ⟨rfl, rfl⟩ := L3.1 _ _ _ hr
      exact ⟨rfl, rfl, by simp⟩
    · rcases hs with ⟨h, rfl⟩ | rfl
      · omega
      · exact ⟨rfl, rfl, by simp⟩
    · subst hs; exact ⟨rfl, rfl, by simp⟩
  have hreach : ∀ a, (prog n).AReach (.assertProper i) ⟨0, C, OF⟩ a → I a :=
    fun a ha => AReach.inv hI ha ⟨rfl, rfl, by simp, by simp⟩
  have hnr : ¬ (prog n).Restarts (.assertProper i) C OF := by
    intro h
    obtain ⟨a, ha, hr⟩ := restarts_iff.1 h
    obtain ⟨hC', hOF, -, hpc⟩ := hreach a ha
    obtain ⟨pc, D, OF₁⟩ := a
    simp only at hC' hOF hpc; subst hC' hOF
    rcases hr with hr | ⟨q, tT, tF, hq, hr⟩
    · have hlt := instr_lt hr
      rw [hcode] at hlt
      rw [Program.instr, hcode] at hr
      simp only [List.length_cons, List.length_nil] at hlt
      interval_cases pc <;> simp at hr hpc
    · have hlt := instr_lt hq
      rw [hcode] at hlt
      rw [Program.instr, hcode] at hq
      simp only [List.length_cons, List.length_nil] at hlt
      interval_cases pc <;> simp at hq <;> obtain ⟨rfl, -, -⟩ := hq
      · exact A0.2.1 hr
      · exact L1.2.1 hr
      · exact L3.2.1 hr
  have hfp := forward_preserve (prog := prog n) (p := .assertProper i) (fun D => D = C)
    (by rw [hcode]; simp) (ap_fwd hi hin) (fun pc q tT tF hq D OF₁ hD => by
      subst hD
      have hlt := instr_lt hq
      rw [hcode] at hlt
      rw [Program.instr, hcode] at hq
      simp only [List.length_cons, List.length_nil] at hlt
      interval_cases pc <;> simp at hq <;> obtain ⟨rfl, -, -⟩ := hq
      · exact ⟨(hAPA D OF₁ (.inl hP)).2.2, fun C' OF' b h => by
          obtain ⟨h1, h2, -⟩ := ((hAPA D OF₁ (.inl hP)).1 _ _ _).1 h; exact ⟨h1, h2⟩⟩
      · have := large_bar_noeffect hi hin hLB 0 OF₁ hP hx0.1 hx0.2.2.1
        exact ⟨this.2.2, fun C' OF' b h => this.1 _ _ _ h⟩
      · have := large_bar_noeffect hi hin hLB 2 OF₁ hP hx0.2.1 hx0.2.2.2
        exact ⟨this.2.2, fun C' OF' b h => this.1 _ _ _ h⟩) (C := C) (OF := OF) rfl
  refine ⟨fun C' OF' b => ⟨fun h => ?_, ?_⟩, hnr, hfp.1⟩
  · obtain ⟨h1, h2⟩ := hfp.2 _ _ _ h
    have hb := h.mem_code
    rw [hcode] at hb
    simp at hb
    exact ⟨h1, h2, hb⟩
  · rintro ⟨rfl, rfl, rfl⟩
    rcases hfp.1.returns_or_restarts with ⟨C', OF', b, hr⟩ | hr
    · obtain ⟨h1, h2⟩ := hfp.2 _ _ _ hr
      have hb := hr.mem_code
      rw [hcode] at hb
      simp at hb
      subst h1 h2 hb
      exact hr
    · exact absurd hr hnr


/-- **Lemma 9(c)**. -/
theorem ap_C (hAPA : APA n (i - 1)) (hLB : LargeB n i) : APC n i := by
  intro C OF hP k hk hcond
  have hcode := code_assertProper n hi
  have r0 : (prog n).Returns (.assertProper (i - 1)) C OF C OF false :=
    ((hAPA C OF (.inl hP)).1 _ _ _).2 ⟨rfl, rfl, rfl⟩
  have lF : ∀ k', (prog n).Returns (.large i k') C OF C OF false := fun k' =>
    ((hLB k' C OF hP).1 _ _ _).2 ⟨rfl, .inl ⟨rfl, rfl⟩⟩
  have lT : ∀ k', N i ≤ C (reg n i k') → (prog n).Returns (.large i k') C OF
      (lg C (reg n i k') (reg n i (bar k')) (N i)) OF true := fun k' h =>
    ((hLB k' C OF hP).1 _ _ _).2 ⟨rfl, .inr ⟨rfl, h, rfl⟩⟩
  have p1 : (prog n).AReach (.assertProper i) ⟨0, C, OF⟩ ⟨1, C, OF⟩ := .single (.call (by ins) r0)
  have hNpos := N_pos hi
  simp only [Finset.mem_insert, Finset.mem_singleton] at hk
  rcases hk with rfl | rfl
  · rcases hcond with h | h
    · exact restarts_iff.2 ⟨_, p1.tail (.detectT (by ins) h), .inl (by ins)⟩
    · change N i < C (reg n i 1) at h
      have hD : 0 < lg C (reg n i 1) (reg n i (bar 1)) (N i) (reg n i 0) := by
        rw [show bar 1 = 0 from rfl, lg_apply_y]; omega
      exact restarts_iff.2 ⟨_, (p1.tail (.detectF (by ins))).tail (.call (by ins) (lT 1 h.le))
        |>.tail (.detectT (by ins) hD), .inl (by ins)⟩
  · have p8 : (prog n).AReach (.assertProper i) ⟨0, C, OF⟩ ⟨8, C, OF⟩ :=
      (((p1.tail (.detectF (by ins))).tail (.call (by ins) (lF 1))).tail (.detectF (by ins)))
    rcases hcond with h | h
    · exact restarts_iff.2 ⟨_, p8.tail (.detectT (by ins) h), .inl (by ins)⟩
    · change N i < C (reg n i 3) at h
      have hD : 0 < lg C (reg n i 3) (reg n i (bar 3)) (N i) (reg n i 2) := by
        rw [show bar 3 = 2 from rfl, lg_apply_y]; omega
      exact restarts_iff.2 ⟨_, (p8.tail (.detectF (by ins))).tail (.call (by ins) (lT 3 h.le))
        |>.tail (.detectT (by ins) hD), .inl (by ins)⟩

/-- **Lemma 9(b)**. -/
theorem ap_B (hAPA : APA n (i - 1)) (hAPB : APB n (i - 1)) (hLB : LargeB n i) : APB n i := by
  intro j hj hji C OF hC
  have hcode := code_assertProper n hi
  rcases Nat.lt_or_ge j i with hlt | hge
  · exact restarts_iff.2 ⟨_, .refl, .inr ⟨_, 1, 1, by ins, hAPB j hj (by omega) C OF hC⟩⟩
  · obtain rfl : j = i := by omega
    obtain ⟨hP, hnP, hs0, hs2⟩ := hC
    have hnP' := hnP
    rw [proper_succ_iff hi] at hnP'
    simp only [psum, show bar 0 = 1 from rfl, show bar 2 = 3 from rfl] at hs0 hs2
    by_cases h0 : 0 < C (reg n j 0) ∨ N j < C (reg n j 1)
    · exact ap_C hi hin hAPA hLB C OF hP 0 (by simp) h0
    · refine ap_C hi hin hAPA hLB C OF hP 2 (by simp) ?_
      simp only [show bar 2 = 3 from rfl]
      by_contra h2
      apply hnP'
      exact ⟨hP, by omega, by omega, by omega, by omega⟩

end

end Podc.PPDoubleExpThresholds
