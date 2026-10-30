import Papers.PODC2023.PPDoubleExpThresholds.Code

namespace Podc.PPDoubleExpThresholds

open Program

variable {n : ℕ}

theorem ae_last (C : Reg n → ℕ) (OF : Bool) :
    (∀ C' OF' b, (prog n).Returns (.assertEmpty (n + 1)) C OF C' OF' b ↔
      C' = C ∧ OF' = OF ∧ b = false) ∧
    ((prog n).Restarts (.assertEmpty (n + 1)) C OF ↔ 0 < C .R) ∧
    (prog n).Terminates (.assertEmpty (n + 1)) C OF := by
  have hcode := code_assertEmpty_last n
  let I : Loc (Reg n) → Prop := fun a => a.C = C ∧ a.OF = OF ∧
    (a.pc = 0 ∨ (a.pc = 1 ∧ 0 < C .R) ∨ a.pc = 3)
  have hI : ∀ a a', I a → (prog n).AStep (.assertEmpty (n + 1)) a a' → I a' := by
    rintro ⟨pc, C₁, OF₁⟩ a' ⟨rfl, rfl, hpc⟩ hs
    rw [astep_iff] at hs
    rcases hpc with rfl | ⟨rfl, -⟩ | rfl <;> simp [Program.instr, hcode] at hs
    rcases hs with ⟨h, rfl⟩ | rfl
    · exact ⟨rfl, rfl, .inr (.inl ⟨rfl, h⟩)⟩
    · exact ⟨rfl, rfl, .inr (.inr rfl)⟩
  have hreach : ∀ a, (prog n).AReach (.assertEmpty (n + 1)) ⟨0, C, OF⟩ a → I a :=
    fun a ha => AReach.inv hI ha ⟨rfl, rfl, .inl rfl⟩
  have h3 : (prog n).AReach (.assertEmpty (n + 1)) ⟨0, C, OF⟩ ⟨3, C, OF⟩ :=
    .single (.detectF (x := .R) (tT := 1) (by simp [Program.instr, hcode]))
  refine ⟨fun C' OF' b => ⟨fun h => ?_, ?_⟩, ⟨fun h => ?_, fun h => ?_⟩, ?_⟩
  · obtain ⟨a, ha, rfl, rfl, hb⟩ := returns_iff.1 h
    obtain ⟨h1, h2, hpc⟩ := hreach a ha
    rcases hpc with h | ⟨h, -⟩ | h <;> simp [Program.instr, hcode, h] at hb
    exact ⟨h1, h2, hb⟩
  · rintro ⟨rfl, rfl, rfl⟩
    exact returns_iff.2 ⟨_, h3, rfl, rfl, by simp [Program.instr, hcode]⟩
  · obtain ⟨a, ha, hr⟩ := restarts_iff.1 h
    obtain ⟨h1, h2, hpc⟩ := hreach a ha
    rcases hpc with h | ⟨h, hR⟩ | h
    · rcases hr with hr | ⟨q, tT, tF, hr, -⟩ <;> simp [Program.instr, hcode, h] at hr
    · exact hR
    · rcases hr with hr | ⟨q, tT, tF, hr, -⟩ <;> simp [Program.instr, hcode, h] at hr
  · exact restarts_iff.2 ⟨⟨1, C, OF⟩, .single (.detectT (x := .R) (tF := 3) (by simp [Program.instr, hcode]) h),
      .inl (by simp [Program.instr, hcode])⟩
  · refine terminates_of (fun a ha q tT tF hq => ?_) (fun a ha => ?_)
    · obtain ⟨-, -, hpc⟩ := hreach a ha
      rcases hpc with h | ⟨h, -⟩ | h <;> simp [Program.instr, hcode, h] at hq
    · obtain ⟨h1, h2, hpc⟩ := hreach a ha
      obtain ⟨pc, C₁, OF₁⟩ := a
      simp only at h1 h2; subst h1 h2
      rcases hpc with h | ⟨h, -⟩ | h <;> simp only at h <;> subst h
      · exact ⟨_, h3, .inl ⟨false, by simp [Program.instr, hcode]⟩⟩
      · exact ⟨_, .refl, .inr (.inl (by simp [Program.instr, hcode]))⟩
      · exact ⟨_, .refl, .inl ⟨false, by simp [Program.instr, hcode]⟩⟩

end Podc.PPDoubleExpThresholds

namespace Podc.PPDoubleExpThresholds

open Program

variable {n : ℕ}

theorem empty_succ {C : Reg n → ℕ} {i : ℕ} (hi : 1 ≤ i) (hin : i ≤ n) :
    Empty C i ↔ Empty C (i + 1) ∧ ∀ k, C (reg n i k) = 0 := by
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨⟨fun j hj hjn k => h1 j (by omega) hjn k, h2⟩, fun k => h1 i le_rfl hin k⟩
  · rintro ⟨⟨h1, h2⟩, h3⟩
    refine ⟨fun j hj hjn k => ?_, h2⟩
    rcases Nat.eq_or_lt_of_le hj with rfl | hj
    · exact h3 k
    · exact h1 j hj hjn k

theorem empty_last {C : Reg n → ℕ} : Empty C (n + 1) ↔ C .R = 0 :=
  ⟨fun h => h.2, fun h => ⟨fun j hj hjn => by omega, h⟩⟩

/-- **Lemma 8** (`AssertEmpty`): `post(C, AssertEmpty(i)) = {C} ∪ S` with `S = ∅` if `C` is
`i`-empty and `S = {restart}` otherwise; the call always terminates. -/
theorem lemma_8 : ∀ i, 1 ≤ i → i ≤ n + 1 → ∀ (C : Reg n → ℕ) (OF : Bool),
    (∀ C' OF' b, (prog n).Returns (.assertEmpty i) C OF C' OF' b ↔
      C' = C ∧ OF' = OF ∧ b = false) ∧
    ((prog n).Restarts (.assertEmpty i) C OF ↔ ¬ Empty C i) ∧
    (prog n).Terminates (.assertEmpty i) C OF := by
  intro i hi hin
  induction h : n + 1 - i generalizing i with
  | zero =>
    obtain rfl : i = n + 1 := by omega
    intro C OF
    obtain ⟨h1, h2, h3⟩ := ae_last C OF
    refine ⟨h1, ?_, h3⟩
    rw [h2, empty_last]; omega
  | succ d ih =>
    have hin' : i ≤ n := by omega
    have IH := ih (i + 1) (by omega) (by omega) (by omega)
    intro C OF
    obtain ⟨IH1, IH2, IH3⟩ := IH C OF
    have hcode := code_assertEmpty n hin'
    let S : List ℕ := [0, 1, 4, 7, 10, 13]
    let I : Loc (Reg n) → Prop := fun a => a.C = C ∧ a.OF = OF ∧
      (a.pc ∈ S ∨ ∃ k : Fin 4, a.pc = 3 * k.1 + 2 ∧ 0 < C (reg n i k))
    have hI : ∀ a a', I a → (prog n).AStep (.assertEmpty i) a a' → I a' := by
      rintro ⟨pc, C₁, OF₁⟩ a' ⟨rfl, rfl, hpc⟩ hs
      rw [astep_iff] at hs
      simp only [S, List.mem_cons, List.not_mem_nil, or_false] at hpc
      rcases hpc with (rfl | rfl | rfl | rfl | rfl | rfl) | ⟨k, rfl, -⟩
      · simp only [Program.instr, hcode] at hs
        obtain ⟨C', OF', b, hr, rfl⟩ := hs
        obtain ⟨rfl, rfl, rfl⟩ := (IH1 _ _ _).1 hr
        exact ⟨rfl, rfl, .inl (by simp [S])⟩
      all_goals first
        | (fin_cases k <;> simp [Program.instr, hcode] at hs)
        | (simp [Program.instr, hcode] at hs; done)
        | (simp [Program.instr, hcode] at hs
           rcases hs with ⟨h, rfl⟩ | rfl
           · first
             | exact ⟨rfl, rfl, .inr ⟨0, rfl, h⟩⟩
             | exact ⟨rfl, rfl, .inr ⟨1, rfl, h⟩⟩
             | exact ⟨rfl, rfl, .inr ⟨2, rfl, h⟩⟩
             | exact ⟨rfl, rfl, .inr ⟨3, rfl, h⟩⟩
           · exact ⟨rfl, rfl, .inl (by simp [S])⟩)
    have hreach : ∀ a, (prog n).AReach (.assertEmpty i) ⟨0, C, OF⟩ a → I a :=
      fun a ha => AReach.inv hI ha ⟨rfl, rfl, .inl (by simp [S])⟩
    -- the straight path through all the checks
    have hret : (prog n).Returns (.assertEmpty (i + 1)) C OF C OF false := (IH1 _ _ _).2 ⟨rfl, rfl, rfl⟩
    have hp : ∀ pc ∈ S, (prog n).AReach (.assertEmpty i) ⟨pc, C, OF⟩ ⟨13, C, OF⟩ := by
      intro pc hpc
      have s10 : (prog n).AReach (.assertEmpty i) ⟨10, C, OF⟩ ⟨13, C, OF⟩ :=
        .single (.detectF (x := reg n i 3) (tT := 11) (by rw [Program.instr, hcode]; rfl))
      have s7 : (prog n).AReach (.assertEmpty i) ⟨7, C, OF⟩ ⟨13, C, OF⟩ :=
        .head (.detectF (x := reg n i 2) (tT := 8) (by rw [Program.instr, hcode]; rfl)) s10
      have s4 : (prog n).AReach (.assertEmpty i) ⟨4, C, OF⟩ ⟨13, C, OF⟩ :=
        .head (.detectF (x := reg n i 1) (tT := 5) (by rw [Program.instr, hcode]; rfl)) s7
      have s1 : (prog n).AReach (.assertEmpty i) ⟨1, C, OF⟩ ⟨13, C, OF⟩ :=
        .head (.detectF (x := reg n i 0) (tT := 2) (by rw [Program.instr, hcode]; rfl)) s4
      have s0 : (prog n).AReach (.assertEmpty i) ⟨0, C, OF⟩ ⟨13, C, OF⟩ :=
        .head (.call (by rw [Program.instr, hcode]; rfl) hret) s1
      simp only [S, List.mem_cons, List.not_mem_nil, or_false] at hpc
      rcases hpc with rfl | rfl | rfl | rfl | rfl | rfl
      exacts [s0, s1, s4, s7, s10, .refl]
    refine ⟨fun C' OF' b => ⟨fun h => ?_, ?_⟩, ⟨fun h => ?_, fun h => ?_⟩, ?_⟩
    · obtain ⟨a, ha, rfl, rfl, hb⟩ := returns_iff.1 h
      obtain ⟨h1, h2, hpc⟩ := hreach a ha
      refine ⟨h1, h2, ?_⟩
      simp only [S, List.mem_cons, List.not_mem_nil, or_false] at hpc
      rcases hpc with (h | h | h | h | h | h) | ⟨k, h, -⟩ <;>
        [skip; skip; skip; skip; skip; skip; fin_cases k] <;>
        simp_all [Program.instr, hcode]
    · rintro ⟨rfl, rfl, rfl⟩
      exact returns_iff.2 ⟨_, hp 0 (by simp [S]), rfl, rfl, by rw [Program.instr, hcode]; rfl⟩
    · obtain ⟨a, ha, hr⟩ := restarts_iff.1 h
      obtain ⟨h1, h2, hpc⟩ := hreach a ha
      obtain ⟨pc, C₁, OF₁⟩ := a
      simp only at h1 h2 hpc; subst h1 h2
      rw [empty_succ hi hin', not_and_or, ← IH2]
      simp only [S, List.mem_cons, List.not_mem_nil, or_false] at hpc
      rcases hpc with (rfl | rfl | rfl | rfl | rfl | rfl) | ⟨k, rfl, hk⟩
      · rcases hr with hr | ⟨q, tT, tF, hq, hr⟩
        · simp [Program.instr, hcode] at hr
        · simp only [Program.instr, hcode] at hq
          cases hq; exact .inl hr
      all_goals first
        | exact .inr fun h => (Nat.pos_iff_ne_zero.1 hk) (h k)
        | (rcases hr with hr | ⟨q, tT, tF, hr, -⟩ <;> simp [Program.instr, hcode] at hr)
    · rw [empty_succ hi hin', not_and_or, ← IH2] at h
      rcases h with h | h
      · exact restarts_iff.2 ⟨_, .refl, .inr ⟨_, 1, 1, by rw [Program.instr, hcode]; rfl, h⟩⟩
      · push Not at h
        obtain ⟨k, hk⟩ := h
        have hk' : 0 < C (reg n i k) := Nat.pos_of_ne_zero hk
        -- reach the check of register `k`
        have hpath : ∃ pc ∈ S, (prog n).AReach (.assertEmpty i) ⟨0, C, OF⟩ ⟨pc, C, OF⟩ ∧
            (prog n).instr (.assertEmpty i) pc = some (.detect (reg n i k) (3 * k.1 + 2) (3 * k.1 + 4)) := by
          have s0 : (prog n).AReach (.assertEmpty i) ⟨0, C, OF⟩ ⟨1, C, OF⟩ :=
            .single (.call (by rw [Program.instr, hcode]; rfl) hret)
          have s1 : (prog n).AReach (.assertEmpty i) ⟨0, C, OF⟩ ⟨4, C, OF⟩ :=
            s0.tail (.detectF (x := reg n i 0) (tT := 2) (by rw [Program.instr, hcode]; rfl))
          have s2 : (prog n).AReach (.assertEmpty i) ⟨0, C, OF⟩ ⟨7, C, OF⟩ :=
            s1.tail (.detectF (x := reg n i 1) (tT := 5) (by rw [Program.instr, hcode]; rfl))
          have s3 : (prog n).AReach (.assertEmpty i) ⟨0, C, OF⟩ ⟨10, C, OF⟩ :=
            s2.tail (.detectF (x := reg n i 2) (tT := 8) (by rw [Program.instr, hcode]; rfl))
          fin_cases k
          · exact ⟨1, by simp [S], s0, by rw [Program.instr, hcode]; rfl⟩
          · exact ⟨4, by simp [S], s1, by rw [Program.instr, hcode]; rfl⟩
          · exact ⟨7, by simp [S], s2, by rw [Program.instr, hcode]; rfl⟩
          · exact ⟨10, by simp [S], s3, by rw [Program.instr, hcode]; rfl⟩
        obtain ⟨pc, -, hpc, hins⟩ := hpath
        refine restarts_iff.2 ⟨_, hpc.tail (.detectT hins hk'), .inl ?_⟩
        fin_cases k <;> rw [Program.instr, hcode] <;> rfl
    · refine terminates_of (fun a ha q tT tF hq => ?_) (fun a ha => ?_)
      · obtain ⟨h1, h2, hpc⟩ := hreach a ha
        simp only [S, List.mem_cons, List.not_mem_nil, or_false] at hpc
        rcases hpc with (h | h | h | h | h | h) | ⟨k, h, -⟩ <;>
          [skip; skip; skip; skip; skip; skip; fin_cases k] <;>
          simp [Program.instr, hcode, h] at hq
        obtain ⟨rfl, -, -⟩ := hq
        rw [h1, h2]; exact IH3
      · obtain ⟨h1, h2, hpc⟩ := hreach a ha
        obtain ⟨pc, C₁, OF₁⟩ := a
        simp only at h1 h2 hpc; subst h1 h2
        rcases hpc with hpc | ⟨k, rfl, -⟩
        · exact ⟨_, hp pc hpc, .inl ⟨false, by rw [Program.instr, hcode]; rfl⟩⟩
        · refine ⟨_, .refl, .inr (.inl ?_)⟩
          fin_cases k <;> rw [Program.instr, hcode] <;> rfl

end Podc.PPDoubleExpThresholds
