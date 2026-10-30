import Papers.PODC2023.PPDoubleExpThresholds.AP

/-!
# Lemma 10: `Zero(x)`
-/

namespace Podc.PPDoubleExpThresholds

open Program

variable {n : ℕ}

set_option hygiene false in
local macro "ins" : tactic => `(tactic| (rw [Program.instr, hcode]; try rfl))

/-- The invariant of `Zero(x)` on configurations satisfying Lemma 10(b)'s hypothesis. -/
def ZInv (C : Reg n → ℕ) (i : ℕ) (k : Fin 4) (pc : ℕ) (D : Reg n → ℕ) : Prop :=
  match pc with
  | 0 => D = C
  | 1 => D = C
  | 2 => D = C
  | 3 => D = C ∧ 0 < C (reg n i k)
  | 5 => D = C
  | 6 => N i ≤ C (reg n i (bar k)) ∧ D = lg C (reg n i (bar k)) (reg n i k) (N i)
  | 8 => D = C
  | _ => False

theorem ZInv.lt {C : Reg n → ℕ} {i : ℕ} {k : Fin 4} {pc : ℕ} {D : Reg n → ℕ}
    (h : ZInv C i k pc D) : pc < 9 := by
  unfold ZInv at h; split at h <;> first | omega | exact h.elim

/-- **Lemma 10(c)**: `Zero(x)` returns `false` only if `x > 0`. -/
theorem zero_C (i : ℕ) : ZeroC n i := by
  intro k C OF C' OF' h
  have hcode := code_zero n i k
  let I : Loc (Reg n) → Prop := fun a => a.pc < 9 ∧ (a.pc = 3 → 0 < a.C (reg n i k))
  have hI : ∀ a a', I a → (prog n).AStep (.zero i k) a a' → I a' := by
    rintro ⟨pc, D, OF₁⟩ a' ⟨hlt, h3⟩ hs
    simp only at hlt h3
    rw [astep_iff] at hs
    interval_cases pc <;>
      simp only [Program.instr, hcode, List.getElem?_cons_succ, List.getElem?_cons_zero] at hs
    · subst hs; exact ⟨by simp, by simp⟩
    · obtain ⟨C', OF', b, -, rfl⟩ := hs; exact ⟨by simp, by simp⟩
    · rcases hs with ⟨hx, rfl⟩ | rfl
      · exact ⟨by simp, fun _ => hx⟩
      · exact ⟨by simp, by simp⟩
    · subst hs; exact ⟨by simp, by simp⟩
    · obtain ⟨C', OF', b, -, rfl⟩ := hs; exact ⟨by cases b <;> simp, by cases b <;> simp⟩
    · subst hs; exact ⟨by simp, by simp⟩
    · subst hs; exact ⟨by simp, by simp⟩
  obtain ⟨a, ha, rfl, rfl, hb⟩ := returns_iff.1 h
  obtain ⟨hlt, h3⟩ := AReach.inv hI ha ⟨by simp, by simp⟩
  obtain ⟨pc, D, OF₁⟩ := a
  simp only at hlt h3 hb ⊢
  interval_cases pc <;> simp [Program.instr, hcode] at hb
  exact h3 rfl

section

variable {i : ℕ} (hi : 1 ≤ i) (hin : i ≤ n)
include hi hin

/-- **Lemma 10(b)**. -/
theorem zero_B (hAPA : APA n (i - 1)) (hLB : LargeB n i) : ZeroB n i := by
  intro k C OF hP hsum
  have hcode := code_zero n i k
  have A0 := hAPA C OF (.inl hP)
  have LB := hLB (bar k) C OF hP
  simp only [bar_bar] at LB
  let I : Loc (Reg n) → Prop := fun a => a.OF = OF ∧ ZInv C i k a.pc a.C
  have hI : ∀ a a', I a → (prog n).AStep (.zero i k) a a' → I a' := by
    rintro ⟨pc, D, OF₁⟩ a' ⟨rfl, hI⟩ hs
    rw [astep_iff] at hs
    have hlt := hI.lt
    simp only at hlt hI ⊢
    interval_cases pc <;> simp only [ZInv] at hI <;>
      simp only [Program.instr, hcode, List.getElem?_cons_succ, List.getElem?_cons_zero] at hs
    · subst hs; exact ⟨rfl, hI⟩
    · subst hI
      obtain ⟨C', OF', b, hr, rfl⟩ := hs
      obtain ⟨rfl, hC', -⟩ := (A0.1 _ _ _).1 hr
      simp only [Bool.cond_self]
      exact ⟨rfl, hC'⟩
    · subst hI
      rcases hs with ⟨hx, rfl⟩ | rfl
      · exact ⟨rfl, rfl, hx⟩
      · exact ⟨rfl, rfl⟩
    · subst hI
      obtain ⟨C', OF', b, hr, rfl⟩ := hs
      obtain ⟨rfl, ⟨rfl, hC'⟩ | ⟨rfl, hx, hC'⟩⟩ := (LB.1 _ _ _).1 hr
      · exact ⟨rfl, hC'⟩
      · exact ⟨rfl, hx, hC'⟩
    · subst hs; exact ⟨rfl, hI⟩
  have hreach : ∀ a, (prog n).AReach (.zero i k) ⟨0, C, OF⟩ a → I a :=
    fun a ha => AReach.inv hI ha ⟨rfl, rfl⟩
  have rA : (prog n).Returns (.assertProper (i - 1)) C OF C OF false := (A0.1 _ _ _).2 ⟨rfl, rfl, rfl⟩
  have rF : (prog n).Returns (.large i (bar k)) C OF C OF false := (LB.1 _ _ _).2 ⟨rfl, .inl ⟨rfl, rfl⟩⟩
  have p2 : ∀ pc, pc ∈ ({0, 1, 2, 5, 8} : Finset ℕ) →
      (prog n).AReach (.zero i k) ⟨pc, C, OF⟩ ⟨2, C, OF⟩ := by
    have q1 : (prog n).AReach (.zero i k) ⟨1, C, OF⟩ ⟨2, C, OF⟩ := .single (.call (by ins) rA)
    have q0 : (prog n).AReach (.zero i k) ⟨0, C, OF⟩ ⟨2, C, OF⟩ := .head (.goto (by ins)) q1
    have q8 : (prog n).AReach (.zero i k) ⟨8, C, OF⟩ ⟨2, C, OF⟩ := .head (.goto (by ins)) q0
    intro pc hpc
    simp only [Finset.mem_insert, Finset.mem_singleton] at hpc
    rcases hpc with rfl | rfl | rfl | rfl | rfl
    · exact q0
    · exact q1
    · exact .refl
    · exact .head (.call (by ins) rF) q8
    · exact q8
  have pT : N i ≤ C (reg n i (bar k)) → (prog n).AReach (.zero i k) ⟨2, C, OF⟩
      ⟨6, lg C (reg n i (bar k)) (reg n i k) (N i), OF⟩ := fun hx =>
    .head (.detectF (by ins)) (.single (.call (by ins) ((LB.1 _ _ _).2 ⟨rfl, .inr ⟨rfl, hx, rfl⟩⟩)))
  have hdone : ∀ pc, pc ∈ ({0, 1, 2, 5, 8} : Finset ℕ) → ∃ a', (prog n).AReach (.zero i k)
      ⟨pc, C, OF⟩ a' ∧ (prog n).ADone (.zero i k) a' := by
    intro pc hpc
    by_cases hx : 0 < C (reg n i k)
    · exact ⟨_, (p2 pc hpc).tail (.detectT (by ins) hx), .inl ⟨false, by ins⟩⟩
    · have : N i ≤ C (reg n i (bar k)) := by unfold psum at hsum; omega
      exact ⟨_, (p2 pc hpc).trans (pT this), .inl ⟨true, by ins⟩⟩
  have callSpec : ∀ a, (prog n).AReach (.zero i k) ⟨0, C, OF⟩ a → ∀ q tT tF,
      (prog n).instr (.zero i k) a.pc = some (.call q tT tF) →
      ¬ (prog n).Restarts q a.C a.OF ∧ (prog n).Terminates q a.C a.OF := by
    intro a ha q tT tF hq
    obtain ⟨hOF, hI⟩ := hreach a ha
    obtain ⟨pc, D, OF₁⟩ := a
    have hlt := hI.lt
    simp only at hlt hI hq hOF ⊢
    subst hOF
    interval_cases pc <;> simp only [ZInv] at hI <;>
      simp only [Program.instr, hcode, List.getElem?_cons_succ, List.getElem?_cons_zero,
        Option.some.injEq, Instr.call.injEq, reduceCtorEq] at hq <;> obtain ⟨rfl, -, -⟩ := hq <;>
      subst hI
    · exact ⟨A0.2.1, A0.2.2⟩
    · exact ⟨LB.2.1, LB.2.2⟩
  refine ⟨fun C' OF' b => ⟨fun h => ?_, ?_⟩, fun h => ?_, ?_⟩
  · obtain ⟨a, ha, rfl, rfl, hb⟩ := returns_iff.1 h
    obtain ⟨hOF, hI⟩ := hreach a ha
    refine ⟨hOF, ?_⟩
    obtain ⟨pc, D, OF₁⟩ := a
    have hlt := hI.lt
    simp only at hlt hI hb ⊢
    interval_cases pc <;> simp only [ZInv] at hI <;>
      simp only [Program.instr, hcode, List.getElem?_cons_succ, List.getElem?_cons_zero,
        Option.some.injEq, Instr.ret.injEq, reduceCtorEq] at hb
    · exact .inl ⟨hb.symm, hI.1, hI.2⟩
    · exact .inr ⟨hb.symm, hI.1, hI.2⟩
  · rintro ⟨hOF', ⟨hb, hC', hx⟩ | ⟨hb, hx, hC'⟩⟩ <;> rw [hOF', hb, hC']
    · exact returns_iff.2 ⟨_, (p2 0 (by simp)).tail (.detectT (by ins) hx), rfl, rfl, by ins⟩
    · exact returns_iff.2 ⟨_, (p2 0 (by simp)).trans (pT hx), rfl, rfl, by ins⟩
  · obtain ⟨a, ha, hr⟩ := restarts_iff.1 h
    rcases hr with hr | ⟨q, tT, tF, hq, hr⟩
    · obtain ⟨-, hI⟩ := hreach a ha
      obtain ⟨pc, D, OF₁⟩ := a
      have hlt := hI.lt
      simp only at hlt hI hr
      interval_cases pc <;> simp [Program.instr, hcode] at hr
    · exact (callSpec a ha q tT tF hq).1 hr
  · refine terminates_of (fun a ha q tT tF hq => (callSpec a ha q tT tF hq).2) (fun a ha => ?_)
    obtain ⟨hOF, hI⟩ := hreach a ha
    obtain ⟨pc, D, OF₁⟩ := a
    have hlt := hI.lt
    simp only at hlt hI hOF ⊢
    subst hOF
    interval_cases pc <;> simp only [ZInv] at hI
    · subst hI; exact hdone _ (by simp)
    · subst hI; exact hdone _ (by simp)
    · subst hI; exact hdone _ (by simp)
    · exact ⟨_, .refl, .inl ⟨false, by ins⟩⟩
    · subst hI; exact hdone _ (by simp)
    · exact ⟨_, .refl, .inl ⟨true, by ins⟩⟩
    · subst hI; exact hdone _ (by simp)

/-- **Lemma 10(d)**: `Zero(x)` is robust. -/
theorem zero_robust (hAPA : APA n (i - 1)) (hAPB : APB n (i - 1))
    (hAPR : Robust n (.assertProper (i - 1))) (hLB : LargeB n i) (hLR : ∀ k, Robust n (.large i k))
    (k : Fin 4) : Robust n (.zero i k) := by
  intro j hj hjn _ C OF hC
  have hcode := code_zero n i k
  rcases Nat.lt_or_ge j i with hlt | hge
  · -- `j < i`: robust callees, and `AssertProper(i − 1)` may restart
    let I : Loc (Reg n) → Prop := fun a => High a.C j ∧ a.OF = OF ∧ a.pc < 10
    have hI : ∀ a a', I a → (prog n).AStep (.zero i k) a a' → I a' := by
      rintro ⟨pc, D, OF₁⟩ a' ⟨hD, rfl, hpc⟩ hs
      simp only at hD hpc
      rw [astep_iff] at hs
      interval_cases pc <;>
        simp only [Program.instr, hcode, List.getElem?_cons_succ, List.getElem?_cons_zero] at hs
      · subst hs; exact ⟨hD, rfl, by simp⟩
      · obtain ⟨C', OF', b, hr, rfl⟩ := hs
        obtain ⟨rfl, h'⟩ := (hAPR j hj hjn trivial D OF₁ hD).2 _ _ _ hr
        exact ⟨h', rfl, by cases b <;> simp⟩
      · rcases hs with ⟨-, rfl⟩ | rfl
        · exact ⟨hD, rfl, by simp⟩
        · exact ⟨hD, rfl, by simp⟩
      · subst hs; exact ⟨hD, rfl, by simp⟩
      · obtain ⟨C', OF', b, hr, rfl⟩ := hs
        obtain ⟨rfl, h'⟩ := (hLR (bar k) j hj hjn trivial D OF₁ hD).2 _ _ _ hr
        exact ⟨h', rfl, by cases b <;> simp⟩
      · subst hs; exact ⟨hD, rfl, by simp⟩
      · subst hs; exact ⟨hD, rfl, by simp⟩
    have hreach : ∀ a, (prog n).AReach (.zero i k) ⟨0, C, OF⟩ a → I a :=
      fun a ha => AReach.inv hI ha ⟨hC, rfl, by simp⟩
    have hcallT : ∀ a, (prog n).AReach (.zero i k) ⟨0, C, OF⟩ a → ∀ q tT tF,
        (prog n).instr (.zero i k) a.pc = some (.call q tT tF) → (prog n).Terminates q a.C a.OF := by
      intro a ha q tT tF hq
      obtain ⟨hD, -, hpc⟩ := hreach a ha
      obtain ⟨pc, D, OF₁⟩ := a
      simp only at hD hpc hq ⊢
      interval_cases pc <;>
        simp only [Program.instr, hcode, List.getElem?_cons_succ, List.getElem?_cons_zero,
          Option.some.injEq, Instr.call.injEq, reduceCtorEq] at hq <;> obtain ⟨rfl, -, -⟩ := hq
      · exact (hAPR j hj hjn trivial D OF₁ hD).1
      · exact (hLR (bar k) j hj hjn trivial D OF₁ hD).1
    refine ⟨terminates_of hcallT (fun a ha => exists_target_of_rank (T := (prog n).ADone (.zero i k))
      (fun a => if a.pc ≤ 1 then 1 - a.pc else 10 - a.pc) (fun a ha => ?_) a ha),
      fun C' OF' b h => ?_⟩
    · obtain ⟨hD, hOF, hpc⟩ := hreach a ha
      obtain ⟨pc, D, OF₁⟩ := a
      simp only at hD hpc hOF ⊢
      interval_cases pc
      · exact .inr ⟨_, .goto (by ins), by simp⟩
      · exact .inl (.inr (.inr ⟨_, 2, 2, by ins, hAPB j hj (by omega) D OF₁ hD⟩))
      · exact .inr ⟨_, .detectF (by ins), by simp⟩
      · exact .inl (.inl ⟨false, by ins⟩)
      · exact .inr ⟨_, .goto (by ins), by simp⟩
      · rcases (hLR (bar k) j hj hjn trivial D OF₁ hD).1.returns_or_restarts with
          ⟨C', OF', b, hr⟩ | hr
        · exact .inr ⟨_, .call (by ins) hr, by cases b <;> simp⟩
        · exact .inl (.inr (.inr ⟨_, 6, 8, by ins, hr⟩))
      · exact .inl (.inl ⟨true, by ins⟩)
      · exact .inr ⟨_, .goto (by ins), by simp⟩
      · exact .inr ⟨_, .goto (by ins), by simp⟩
      · exact .inl (.inl ⟨false, by ins⟩)
    · obtain ⟨a, ha, rfl, rfl, -⟩ := returns_iff.1 h
      obtain ⟨hD, hOF, -⟩ := hreach a ha
      exact ⟨hOF, hD⟩
  · -- `j ≥ i`: Lemma 10(b) applies
    have hP : Proper C (i - 1) := hC.1.mono (by omega)
    have hs : N i ≤ psum C i k := by
      rcases Nat.eq_or_lt_of_le hge with rfl | hgt
      · exact hC.geq.psum k
      · exact ((hC.proper_of_lt hgt).wproper hi).geq.psum k
    obtain ⟨hR, -, hT⟩ := zero_B hi hin hAPA hLB k C OF hP hs
    refine ⟨hT, fun C' OF' b h => ?_⟩
    obtain ⟨rfl, ⟨-, rfl, -⟩ | ⟨-, hx, rfl⟩⟩ := (hR C' OF' b).1 h
    · exact ⟨rfl, hC⟩
    · refine ⟨rfl, ?_⟩
      have := hC.lg (C := C)
      rcases Nat.eq_or_lt_of_le hge with rfl | hgt
      · have h' := High.lg hi hin (bar k) hC hx
        simpa using h'
      · have h' := lg_eq_self hi hin (bar k) ((hC.proper_of_lt hgt).wproper hi) hx
        simp only [bar_bar] at h'
        rw [h']; exact hC

end

end Podc.PPDoubleExpThresholds
