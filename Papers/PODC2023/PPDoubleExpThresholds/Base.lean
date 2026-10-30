import Papers.PODC2023.PPDoubleExpThresholds.Types

/-!
# `Large` at level 1, `AssertProper(0)`, and robustness of `Large` for `j ≥ i`
-/

namespace Podc.PPDoubleExpThresholds

open Program

variable {n : ℕ}

set_option hygiene false in
/-- Discharge `(prog n).instr p pc = some ins` using the local code listing `hcode`. -/
local macro "ins" : tactic => `(tactic| (rw [Program.instr, hcode]; try rfl))

/-- **Lemma 12(b)** at level `1`. -/
theorem large_one_B (hn : 1 ≤ n) : LargeB n 1 := by
  intro k C OF _
  have hcode := code_large_one n (le_refl 1) k
  set x := reg n 1 k
  set xb := reg n 1 (bar k)
  have hne : x ≠ xb := reg_ne_bar le_rfl hn k
  have hN : N 1 = 1 := rfl
  let I : Loc (Reg n) → Prop := fun a => a.OF = OF ∧
    ((a.pc = 0 ∧ a.C = C) ∨ (a.pc = 1 ∧ a.C = C ∧ 0 < C x) ∨
     (a.pc = 2 ∧ a.C = mv C x xb ∧ 0 < C x) ∨ (a.pc = 3 ∧ a.C = lg C x xb 1 ∧ 0 < C x) ∨
     (a.pc = 5 ∧ a.C = C))
  have hI : ∀ a a', I a → (prog n).AStep (.large 1 k) a a' → I a' := by
    rintro ⟨pc, C₁, OF₁⟩ a' ⟨rfl, hpc⟩ hs
    rw [astep_iff] at hs
    rcases hpc with ⟨rfl, rfl⟩ | ⟨rfl, rfl, h⟩ | ⟨rfl, rfl, h⟩ | ⟨rfl, rfl, h⟩ | ⟨rfl, rfl⟩ <;>
      simp [Program.instr, hcode] at hs
    · rcases hs with ⟨h, rfl⟩ | rfl
      · exact ⟨rfl, .inr (.inl ⟨rfl, rfl, h⟩)⟩
      · exact ⟨rfl, .inr (.inr (.inr (.inr ⟨rfl, rfl⟩)))⟩
    · obtain ⟨-, rfl⟩ := hs; exact ⟨rfl, .inr (.inr (.inl ⟨rfl, rfl, h⟩))⟩
    · subst hs; exact ⟨rfl, .inr (.inr (.inr (.inl ⟨rfl, swp_mv_eq_lg C hne, h⟩)))⟩
  have hreach : ∀ a, (prog n).AReach (.large 1 k) ⟨0, C, OF⟩ a → I a :=
    fun a ha => AReach.inv hI ha ⟨rfl, .inl ⟨rfl, rfl⟩⟩
  have p5 : (prog n).AReach (.large 1 k) ⟨0, C, OF⟩ ⟨5, C, OF⟩ :=
    .single (.detectF (x := x) (tT := 1) (tF := 5) (by ins))
  have p3 : 0 < C x → (prog n).AReach (.large 1 k) ⟨0, C, OF⟩ ⟨3, lg C x xb 1, OF⟩ := fun h =>
    ((Relation.ReflTransGen.single (.detectT (x := x) (tF := 5) (by ins) h)).tail
      (.move (by ins) h)).tail
      (by rw [← swp_mv_eq_lg C hne]; exact .swap (by ins))
  refine ⟨fun C' OF' b => ⟨fun h => ?_, ?_⟩, fun h => ?_, ?_⟩
  · obtain ⟨a, ha, rfl, rfl, hb⟩ := returns_iff.1 h
    obtain ⟨h1, hpc⟩ := hreach a ha
    refine ⟨h1, ?_⟩
    rcases hpc with ⟨h, h'⟩ | ⟨h, h', -⟩ | ⟨h, h', -⟩ | ⟨h, h', hx⟩ | ⟨h, h'⟩ <;>
      simp [Program.instr, hcode, h] at hb
    · exact .inr ⟨hb, hx, h'⟩
    · exact .inl ⟨hb, h'⟩
  · rintro ⟨rfl, ⟨rfl, rfl⟩ | ⟨rfl, hx, rfl⟩⟩
    · exact returns_iff.2 ⟨_, p5, rfl, rfl, by ins⟩
    · exact returns_iff.2 ⟨_, p3 hx, rfl, rfl, by ins⟩
  · obtain ⟨a, ha, hr⟩ := restarts_iff.1 h
    obtain ⟨-, hpc⟩ := hreach a ha
    rcases hpc with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;>
      rcases hr with hr | ⟨q, tT, tF, hr, -⟩ <;> simp [Program.instr, hcode, h] at hr
  · refine terminates_of (fun a ha q tT tF hq => ?_) (fun a ha => ?_)
    · obtain ⟨-, hpc⟩ := hreach a ha
      rcases hpc with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;>
        simp [Program.instr, hcode, h] at hq
    · obtain ⟨h1, hpc⟩ := hreach a ha
      obtain ⟨pc, C₁, OF₁⟩ := a
      simp only at h1 hpc; subst h1
      rcases hpc with ⟨rfl, rfl⟩ | ⟨rfl, rfl, h⟩ | ⟨rfl, rfl, h⟩ | ⟨rfl, rfl, h⟩ | ⟨rfl, rfl⟩
      · exact ⟨_, .single (.detectF (x := x) (tT := 1) (tF := 5) (by ins)),
          .inl ⟨false, by ins⟩⟩
      · refine ⟨_, (Relation.ReflTransGen.single (.move (by ins) h)).tail
          (.swap (by ins)), .inl ⟨true, by ins⟩⟩
      · exact ⟨_, .single (.swap (by ins)),
          .inl ⟨true, by ins⟩⟩
      · exact ⟨_, .refl, .inl ⟨true, by ins⟩⟩
      · exact ⟨_, .refl, .inl ⟨false, by ins⟩⟩

/-- High configurations of a level `j > i` are `i`-proper. -/
theorem High.proper_of_lt {C : Reg n → ℕ} {i j : ℕ} (h : High C j) (hij : i < j) : Proper C i :=
  h.1.mono (by omega)

/-- **Robustness of `Large(x)` for `j ≥ i`** (from Lemma 12(b), as in the proof of 12(c)). -/
theorem large_robust_ge {i : ℕ} (hi : 1 ≤ i) (hin : i ≤ n) (hB : LargeB n i) (k : Fin 4) :
    RobustOn n (fun j => i ≤ j) (.large i k) := by
  intro j hj hjn hij C OF hC
  obtain ⟨hR, -, hT⟩ := hB k C OF (hC.1.mono (by omega))
  refine ⟨hT, fun C' OF' b h => ?_⟩
  obtain ⟨rfl, ⟨-, rfl⟩ | ⟨-, hx, rfl⟩⟩ := (hR C' OF' b).1 h
  · exact ⟨rfl, hC⟩
  · refine ⟨rfl, ?_⟩
    rcases Nat.eq_or_lt_of_le hij with rfl | hlt
    · exact hC.lg hi hin k hx
    · rw [lg_eq_self hi hin k ((hC.proper_of_lt hlt).wproper hi) hx]; exact hC

/-- `AssertProper(0)` has no effect. -/
theorem ap_zero (C : Reg n → ℕ) (OF : Bool) :
    Spec n (.assertProper 0) C OF fun C' b => C' = C ∧ b = false := by
  have hcode := code_assertProper_zero n
  have hreach : ∀ a, (prog n).AReach (.assertProper 0) ⟨0, C, OF⟩ a → a = ⟨0, C, OF⟩ := by
    intro a ha
    induction ha with
    | refl => rfl
    | tail _ hs ih => subst ih; rw [astep_iff] at hs; simp [Program.instr, hcode] at hs
  refine ⟨fun C' OF' b => ⟨fun h => ?_, ?_⟩, fun h => ?_, ?_⟩
  · obtain ⟨a, ha, rfl, rfl, hb⟩ := returns_iff.1 h
    obtain rfl := hreach a ha
    simp [Program.instr, hcode] at hb
    exact ⟨rfl, rfl, hb⟩
  · rintro ⟨rfl, rfl, rfl⟩
    exact returns_iff.2 ⟨_, .refl, rfl, rfl, by ins⟩
  · obtain ⟨a, ha, hr⟩ := restarts_iff.1 h
    obtain rfl := hreach a ha
    rcases hr with hr | ⟨q, tT, tF, hr, -⟩ <;> simp [Program.instr, hcode] at hr
  · refine terminates_of (fun a ha q tT tF hq => ?_) (fun a ha => ?_)
    · obtain rfl := hreach a ha; simp [Program.instr, hcode] at hq
    · obtain rfl := hreach a ha
      exact ⟨_, .refl, .inl ⟨false, by ins⟩⟩

theorem Spec.terminates {p : Proc} {C : Reg n → ℕ} {OF : Bool} {Q : (Reg n → ℕ) → Bool → Prop}
    (h : Spec n p C OF Q) : (prog n).Terminates p C OF := h.2.2

theorem Spec.not_restarts {p : Proc} {C : Reg n → ℕ} {OF : Bool} {Q : (Reg n → ℕ) → Bool → Prop}
    (h : Spec n p C OF Q) : ¬ (prog n).Restarts p C OF := h.2.1

end Podc.PPDoubleExpThresholds
