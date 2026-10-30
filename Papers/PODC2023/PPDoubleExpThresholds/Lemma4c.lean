import Papers.PODC2023.PPDoubleExpThresholds.Lemma4

/-!
# Lemma 4(a) and 4(c)
-/

namespace Podc.PPDoubleExpThresholds

open Program

variable {n : ℕ}

local macro "om" : tactic => `(tactic| ((try dsimp only at *) <;> omega))
local macro "som" : tactic => `(tactic| ((try simp) <;> om))

/-- Restarts everywhere in `Main`, from an invariant and a ranking. -/
theorem main_restarts {C : Reg n → ℕ} {OF₀ : Bool} (I : Loc (Reg n) → Prop)
    (hI0 : I ⟨0, C, OF₀⟩) (hIc : ∀ a a', I a → (prog n).AStep .main a a' → I a')
    (hterm : ∀ a, I a → ∀ q tT tF, (prog n).instr .main a.pc = some (.call q tT tF) →
      (prog n).Terminates q a.C a.OF)
    (rk : Loc (Reg n) → ℕ)
    (hrk : ∀ a, I a → (prog n).ARst .main a ∨ ∃ a', (prog n).AStep .main a a' ∧ rk a' < rk a) :
    ∀ s, (prog n).Reach₀ ((prog n).init C OF₀) s → (prog n).CanRestart s := by
  have hreach : ∀ a, (prog n).AReach .main ⟨0, C, OF₀⟩ a → I a := fun a ha => AReach.inv hIc ha hI0
  exact canRestart_of (a₀ := ⟨0, C, OF₀⟩) (fun a ha => hterm a (hreach a ha))
    (fun a ha => exists_target_of_rank rk (fun a ha => hrk a (hreach a ha)) a ha)

/-- The order of the positions inside a loop that is passed through (`r = 1` leaves the loop). -/
def ordPass (r : ℕ) : ℕ := if r ≤ 1 then 1 - r else 6 - r

/-- The ranking of `Main`: loops of levels `< J` are passed through, inside the other loops the
positions are ordered by `ord`. -/
def rkMain (n J : ℕ) (ord : ℕ → ℕ) (a : Loc (Reg n)) : ℕ :=
  if a.pc = 0 then 10 * n + 100
  else if a.pc ≤ 5 * n then
    10 * (n + 1 - (a.pc + 4) / 5) + (if (a.pc + 4) / 5 < J then ordPass ((a.pc + 4) % 5)
      else ord ((a.pc + 4) % 5))
  else if a.pc = 5 * n + 1 then 4 else if a.pc = 5 * n + 2 then 2
  else if a.pc = 5 * n + 4 then 3 else 0

theorem rkMain_it (J : ℕ) (ord : ℕ → ℕ) {j r : ℕ} (hj : 1 ≤ j) (hjn : j ≤ n) (hr : r < 5)
    (D : Reg n → ℕ) (OF : Bool) :
    rkMain n J ord ⟨5 * j - 4 + r, D, OF⟩ =
      10 * (n + 1 - j) + (if j < J then ordPass r else ord r) := by
  simp only [rkMain]
  rw [if_neg (by omega), if_pos (by omega), show (5 * j - 4 + r + 4) / 5 = j by omega,
    show (5 * j - 4 + r + 4) % 5 = r by omega]

theorem rkMain_next (J : ℕ) (ord : ℕ → ℕ) (hord : ord 0 ≤ 9) {j : ℕ} (hj : 1 ≤ j) (hjn : j ≤ n)
    (D : Reg n → ℕ) (OF : Bool) :
    rkMain n J ord ⟨5 * j + 1, D, OF⟩ < 10 * (n + 1 - j) := by
  rcases Nat.lt_or_ge j n with h | h
  · have := rkMain_it J ord (j := j + 1) (r := 0) (by omega) h (by omega) D OF
    rw [show 5 * (j + 1) - 4 + 0 = 5 * j + 1 by omega] at this
    rw [this]; simp only [ordPass]; split_ifs <;> omega
  · obtain rfl : j = n := by omega
    simp only [rkMain]; rw [if_neg (by omega), if_neg (by omega)]; simp

theorem rkMain_le (J : ℕ) (ord : ℕ → ℕ) (hord : ∀ r, ord r ≤ 9) {j r : ℕ} (hj : 1 ≤ j) (hjn : j ≤ n)
    (hr : r < 5) (D : Reg n → ℕ) (OF : Bool) :
    10 * (n + 1 - j) ≤ rkMain n J ord ⟨5 * j - 4 + r, D, OF⟩ ∧
      rkMain n J ord ⟨5 * j - 4 + r, D, OF⟩ < 10 * (n + 1 - j) + 10 := by
  rw [rkMain_it J ord hj hjn hr]
  have := hord r
  simp only [ordPass]; split_ifs <;> omega

/-- Passing through a proper loop decreases the rank. -/
theorem pass_step (J : ℕ) (ord : ℕ → ℕ) (hord : ∀ r, ord r ≤ 9) {j r : ℕ} (hj : 1 ≤ j)
    (hjn : j ≤ n) (hjJ : j < J) (hr : r < 5) {D : Reg n → ℕ} (OF : Bool) (hD : Proper D j) :
    ∃ a', (prog n).AStep .main ⟨5 * j - 4 + r, D, OF⟩ a' ∧
      rkMain n J ord a' < rkMain n J ord ⟨5 * j - 4 + r, D, OF⟩ := by
  obtain ⟨s0, s1, s2, s3, s4⟩ := steps_proper hj hjn OF hD
  have rk := fun r (hr : r < 5) => rkMain_it (n := n) J ord hj hjn hr D OF
  interval_cases r
  · refine ⟨_, by simpa using s0, ?_⟩
    have := rk 1 (by omega); rw [show 5 * j - 4 + 1 = 5 * j - 3 by omega] at this
    rw [this, rk 0 (by omega)]; simp [ordPass, hjJ]
  · refine ⟨_, by rw [show 5 * j - 4 + 1 = 5 * j - 3 by omega]; exact s1, ?_⟩
    have := rkMain_next (n := n) J ord (hord 0) hj hjn D OF
    rw [rk 1 (by omega)]; omega
  · refine ⟨_, by rw [show 5 * j - 4 + 2 = 5 * j - 2 by omega]; exact s2, ?_⟩
    have := rk 3 (by omega); rw [show 5 * j - 4 + 3 = 5 * j - 1 by omega] at this
    rw [this, rk 2 (by omega)]; simp [ordPass, hjJ]
  · refine ⟨_, by rw [show 5 * j - 4 + 3 = 5 * j - 1 by omega]; exact s3, ?_⟩
    have := rk 4 (by omega); rw [show 5 * j - 4 + 4 = 5 * j by omega] at this
    rw [this, rk 3 (by omega)]; simp [ordPass, hjJ]
  · refine ⟨_, by rw [show 5 * j - 4 + 4 = 5 * j by omega]; exact s4, ?_⟩
    have := rk 0 (by omega); rw [show 5 * j - 4 + 0 = 5 * j - 4 by omega] at this
    rw [this, rk 4 (by omega)]; simp [ordPass, hjJ]

theorem rk_start (J : ℕ) (ord : ℕ → ℕ) (hord : ∀ r, ord r ≤ 9) (D D' : Reg n → ℕ) (OF OF' : Bool) :
    rkMain n J ord ⟨1, D', OF'⟩ < rkMain n J ord ⟨0, D, OF⟩ := by
  have h0 : rkMain n J ord ⟨0, D, OF⟩ = 10 * n + 100 := by simp [rkMain]
  rw [h0]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [rkMain]
  · have := (rkMain_le (n := n) J ord hord (j := 1) (r := 0) le_rfl hn (by omega) D' OF').2
    simp only [show 5 * 1 - 4 + 0 = 1 by omega] at this; omega

theorem rk_fin (J : ℕ) (ord : ℕ → ℕ) (D D' : Reg n → ℕ) (OF OF' : Bool) :
    rkMain n J ord ⟨5 * n + 2, D', OF'⟩ < rkMain n J ord ⟨5 * n + 1, D, OF⟩ ∧
    rkMain n J ord ⟨5 * n + 3, D', OF'⟩ < rkMain n J ord ⟨5 * n + 2, D, OF⟩ ∧
    rkMain n J ord ⟨5 * n + 2, D', OF'⟩ < rkMain n J ord ⟨5 * n + 4, D, OF⟩ := by
  have e1 : rkMain n J ord ⟨5 * n + 1, D, OF⟩ = 4 := by simp [rkMain]
  have e2 : ∀ D OF, rkMain n J ord ⟨5 * n + 2, D, OF⟩ = 2 := fun D OF => by simp [rkMain]
  have e3 : rkMain n J ord ⟨5 * n + 3, D', OF'⟩ = 0 := by simp [rkMain]
  have e4 : rkMain n J ord ⟨5 * n + 4, D, OF⟩ = 3 := by simp [rkMain]
  rw [e1, e2, e2, e3, e4]; omega

/-- The calls made by `Main`. -/
theorem main_call_cases {pc : ℕ} {q : Proc} {tT tF : ℕ}
    (hq : (prog n).instr .main pc = some (.call q tT tF)) :
    (∃ j, 1 ≤ j ∧ j ≤ n ∧ ((pc = 5 * j - 4 ∧ q = .large j 1) ∨ (pc = 5 * j - 3 ∧ q = .large j 3) ∨
      (pc = 5 * j - 2 ∧ q = .assertProper j) ∨ (pc = 5 * j - 1 ∧ q = .assertEmpty (j + 1)))) ∨
    (pc = 5 * n + 3 ∧ q = .assertProper n) := by
  rcases main_pc_cases (n := n) pc with rfl | ⟨j, r, hj, hjn, hr, rfl⟩ | h
  · rw [instr_main_zero n] at hq; simp at hq
  · refine .inl ⟨j, hj, hjn, ?_⟩
    interval_cases r
    · rw [Nat.add_zero, instr_it0 hj hjn] at hq; simp at hq; exact .inl ⟨by omega, hq.1.symm⟩
    · rw [show 5 * j - 4 + 1 = 5 * j - 3 by omega, instr_it1 hj hjn] at hq; simp at hq
      exact .inr (.inl ⟨by omega, hq.1.symm⟩)
    · rw [show 5 * j - 4 + 2 = 5 * j - 2 by omega, instr_it2 hj hjn] at hq; simp at hq
      exact .inr (.inr (.inl ⟨by omega, hq.1.symm⟩))
    · rw [show 5 * j - 4 + 3 = 5 * j - 1 by omega, instr_it3 hj hjn] at hq; simp at hq
      exact .inr (.inr (.inr ⟨by omega, hq.1.symm⟩))
    · rw [show 5 * j - 4 + 4 = 5 * j by omega, instr_it4 hj hjn] at hq; simp at hq
  · obtain ⟨r, rfl⟩ : ∃ r, pc = 5 * n + 1 + r := ⟨pc - (5 * n + 1), by omega⟩
    rcases Nat.lt_or_ge r 5 with hr | hr
    · interval_cases r
      · rw [Nat.add_zero, instr_fin0] at hq; simp at hq
      · rw [show 5 * n + 1 + 1 = 5 * n + 2 by omega, instr_fin1] at hq; simp at hq
      · rw [show 5 * n + 1 + 2 = 5 * n + 3 by omega, instr_fin2] at hq; simp at hq
        exact .inr ⟨rfl, hq.1.symm⟩
      · rw [show 5 * n + 1 + 3 = 5 * n + 4 by omega, instr_fin3] at hq; simp at hq
      · rw [show 5 * n + 1 + 4 = 5 * n + 5 by omega, instr_fin4] at hq; simp at hq
    · rw [instr_main_none n (by omega)] at hq; simp at hq

/-! ### Case 3 of Lemma 4(c): a high level -/

theorem lemma_4c_high {C : Reg n → ℕ} {J : ℕ} (hJ : 1 ≤ J) (hJn : J ≤ n) (hC : High C J)
    (OF₀ : Bool) : ∀ s, (prog n).Reach₀ ((prog n).init C OF₀) s → (prog n).CanRestart s := by
  let ord : ℕ → ℕ := fun r => if r ≤ 2 then 2 - r else 7 - r
  have hord : ∀ r, ord r ≤ 9 := fun r => by simp only [ord]; split_ifs <;> omega
  let I : Loc (Reg n) → Prop := fun a => High a.C J ∧ a.pc ≤ 5 * n + 4
  -- robust callees
  have rob : ∀ j, 1 ≤ j → j ≤ n → ∀ D OF, High D J →
      (∀ k, (prog n).Terminates (.large j k) D OF ∧ ∀ D' OF' b, (prog n).Returns (.large j k) D OF D' OF' b →
        OF' = OF ∧ High D' J) ∧
      ((prog n).Terminates (.assertProper j) D OF ∧ ∀ D' OF' b,
        (prog n).Returns (.assertProper j) D OF D' OF' b → OF' = OF ∧ High D' J) := fun j hj hjn D OF hD =>
    ⟨fun k => (levels j hj hjn).largeR k J hJ hJn trivial D OF hD,
     (levels j hj hjn).apR J hJ hJn trivial D OF hD⟩
  have hIc : ∀ a a', I a → (prog n).AStep .main a a' → I a' := by
    rintro ⟨pc, D, OF⟩ a' ⟨hD, hpc⟩ hs
    simp only at hD hpc
    rcases main_astep hs with ⟨rfl, rfl⟩ | ⟨j, hj, hjn, h⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
        ⟨rfl, D', OF', b, hr, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨hD, by om⟩
    · rcases h with ⟨rfl, D', OF', b, hr, rfl⟩ | ⟨rfl, D', OF', b, hr, rfl⟩ |
          ⟨rfl, D', OF', b, hr, rfl⟩ | ⟨rfl, D', OF', b, hr, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨((rob j hj hjn D OF hD).1 1).2 _ _ _ hr |>.2, by cases b <;> simp <;> om⟩
      · exact ⟨((rob j hj hjn D OF hD).1 3).2 _ _ _ hr |>.2, by cases b <;> simp <;> om⟩
      · exact ⟨((rob j hj hjn D OF hD).2.2 _ _ _ hr).2, by om⟩
      · obtain ⟨rfl, -⟩ := (ae_facts hj hjn OF).2.1 _ _ _ hr; exact ⟨hD, by om⟩
      · exact ⟨hD, by om⟩
    · exact ⟨hD, by om⟩
    · exact ⟨hD, by om⟩
    · exact ⟨((rob n (by omega) le_rfl D OF hD).2.2 _ _ _ hr).2, by om⟩
    · exact ⟨hD, by om⟩
  refine main_restarts I ⟨hC, by simp⟩ hIc ?_ (rkMain n J ord) ?_
  · rintro ⟨pc, D, OF⟩ ⟨hD, hpc⟩ q tT tF hq
    simp only at hD hq ⊢
    rcases main_call_cases hq with ⟨j, hj, hjn, ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩⟩ | ⟨-, rfl⟩
    · exact ((rob j hj hjn D OF hD).1 1).1
    · exact ((rob j hj hjn D OF hD).1 3).1
    · exact (rob j hj hjn D OF hD).2.1
    · exact (ae_facts hj hjn OF).2.2.2
    · exact (rob n (by omega) le_rfl D OF hD).2.1
  · rintro ⟨pc, D, OF⟩ ⟨hD, hpc⟩
    simp only at hD hpc
    rcases main_pc_cases (n := n) pc with rfl | ⟨j, r, hj, hjn, hr, rfl⟩ | h
    · exact .inr ⟨_, .setOF (instr_main_zero n), rk_start J ord hord D D OF false⟩
    · rcases Nat.lt_or_ge j J with hjJ | hjJ
      · exact .inr (pass_step J ord hord hj hjn hjJ hr OF (hD.1.mono (by omega)))
      · have hjJ' : ¬ j < J := by omega
        have rk := fun r (hr : r < 5) (D : Reg n → ℕ) (OF : Bool) =>
          rkMain_it (n := n) J ord hj hjn hr D OF
        have e : ∀ r (hr : r < 5) D OF, rkMain n J ord ⟨5 * j - 4 + r, D, OF⟩ =
            10 * (n + 1 - j) + ord r := fun r hr D OF => by rw [rk r hr D OF, if_neg hjJ']
        have i0 := instr_it0 hj hjn; have i1 := instr_it1 hj hjn; have i2 := instr_it2 hj hjn
        have i3 := instr_it3 hj hjn; have i4 := instr_it4 hj hjn
        have e1 := e 1 (by omega); have e2 := e 2 (by omega); have e3 := e 3 (by omega)
        have e4 := e 4 (by omega); have e0 := e 0 (by omega)
        simp only [show 5 * j - 4 + 1 = 5 * j - 3 by omega, show 5 * j - 4 + 2 = 5 * j - 2 by omega,
          show 5 * j - 4 + 3 = 5 * j - 1 by omega, show 5 * j - 4 + 4 = 5 * j by omega,
          Nat.add_zero] at e1 e2 e3 e4 e0
        interval_cases r
        · rcases ((rob j hj hjn D OF hD).1 1).1.returns_or_restarts with ⟨D', OF', b, hr'⟩ | hr'
          · refine .inr ⟨_, .call (by simpa using i0) hr', ?_⟩
            cases b
            · simp only [Bool.cond_false, Nat.add_zero, e2, e0]; simp [ord]
            · simp only [Bool.cond_true, Nat.add_zero, e1, e0]; simp [ord]
          · exact .inl (.inr ⟨_, _, _, by simpa using i0, hr'⟩)
        · rw [show 5 * j - 4 + 1 = 5 * j - 3 by omega]
          rcases ((rob j hj hjn D OF hD).1 3).1.returns_or_restarts with ⟨D', OF', b, hr'⟩ | hr'
          · refine .inr ⟨_, .call i1 hr', ?_⟩
            cases b
            · simp only [Bool.cond_false, e2, e1]; simp [ord]
            · simp only [Bool.cond_true, e1]
              have := rkMain_next (n := n) J ord (hord 0) hj hjn D' OF'
              simp [ord] at this ⊢; omega
          · exact .inl (.inr ⟨_, _, _, i1, hr'⟩)
        · rw [show 5 * j - 4 + 2 = 5 * j - 2 by omega]
          exact .inl (.inr ⟨_, _, _, i2, (levels j hj hjn).apB J hJ hjJ D OF hD⟩)
        · rw [show 5 * j - 4 + 3 = 5 * j - 1 by omega]
          rcases (ae_facts hj hjn (D := D) OF).2.2.2.returns_or_restarts with ⟨D', OF', b, hr'⟩ | hr'
          · refine .inr ⟨_, .call i3 hr', ?_⟩
            simp only [Bool.cond_self, e4, e3]; simp [ord]
          · exact .inl (.inr ⟨_, _, _, i3, hr'⟩)
        · rw [show 5 * j - 4 + 4 = 5 * j by omega]
          refine .inr ⟨_, .goto i4, ?_⟩
          simp only [e0, e4]; simp [ord]
    · obtain ⟨hf0, hf1, hf2⟩ := rk_fin (n := n) J ord D D OF OF
      rcases (show pc = 5 * n + 1 ∨ pc = 5 * n + 2 ∨ pc = 5 * n + 3 ∨ pc = 5 * n + 4 by omega) with
        rfl | rfl | rfl | rfl
      · exact .inr ⟨_, .setOF instr_fin0, (rk_fin (n := n) J ord D D OF true).1⟩
      · exact .inr ⟨_, .goto instr_fin1, hf1⟩
      · exact .inl (.inr ⟨_, _, _, instr_fin2, (levels n (by omega) le_rfl).apB J hJ hJn D OF hD⟩)
      · exact .inr ⟨_, .goto instr_fin3, hf2⟩

/-! ### Case 2 of Lemma 4(c): `x̄ < N` for some `x`, not low -/

/-- Some pair of level `J` violates the invariant from above or `x > 0`. -/
def Bad (D : Reg n → ℕ) (J : ℕ) : Prop :=
  (0 < D (reg n J 0) ∨ N J < D (reg n J 1)) ∨ (0 < D (reg n J 2) ∨ N J < D (reg n J 3))

/-- The registers in case 2: `(J−1)`-proper, the small pair `k₀` stays small, `Bad`. -/
def Q2 (J : ℕ) (k₀ : Fin 4) (D : Reg n → ℕ) : Prop :=
  Proper D (J - 1) ∧ D (reg n J (bar k₀)) < N J ∧ Bad D J

theorem q2_large {J : ℕ} (hJ : 1 ≤ J) (hJn : J ≤ n) {k₀ : Fin 4} (hk₀ : k₀ = 0 ∨ k₀ = 2)
    {D : Reg n → ℕ} (hD : Q2 J k₀ D) (k : Fin 4) (hk : k = 1 ∨ k = 3) (OF : Bool) :
    (prog n).Terminates (.large J k) D OF ∧ ¬ (prog n).Restarts (.large J k) D OF ∧
    ∀ D' OF' b, (prog n).Returns (.large J k) D OF D' OF' b → OF' = OF ∧ Q2 J k₀ D' ∧
      (b = true → N J ≤ D (reg n J k)) := by
  obtain ⟨hR, h2, h3⟩ := (levels J hJ hJn).largeB k D OF hD.1
  refine ⟨h3, h2, fun D' OF' b h => ?_⟩
  obtain ⟨rfl, ⟨rfl, rfl⟩ | ⟨rfl, hm, rfl⟩⟩ := (hR _ _ _).1 h
  · exact ⟨rfl, hD, by simp⟩
  · refine ⟨rfl, ⟨((lg_off hJ hJn k _).proper_iff (by omega) hJn).2 hD.1, ?_, ?_⟩, fun _ => hm⟩
    · have hk' : bar k₀ ≠ k := by
        rintro rfl; have := hD.2.1; omega
      have hk'' : bar k₀ ≠ bar k := by
        rcases hk₀ with rfl | rfl <;> rcases hk with rfl | rfl <;> simp [bar] at hk' ⊢
      rw [lg_apply_other _ (by rw [Ne, reg_inj hJ hJn hJ hJn]; simp [hk'])
        (by rw [Ne, reg_inj hJ hJn hJ hJn]; simp [hk''])]
      exact hD.2.1
    · have hne := reg_ne_bar hJ hJn k
      have hB := hD.2.2
      unfold Bad at hB ⊢
      rcases hk with rfl | rfl
      · have e1 : lg D (reg n J 1) (reg n J (bar 1)) (N J) (reg n J 1) = D (reg n J 0) + N J := by
          rw [lg_apply_x _ hne]; rfl
        have e0 : lg D (reg n J 1) (reg n J (bar 1)) (N J) (reg n J 0) = D (reg n J 1) - N J := by
          rw [show (reg n J 0 : Reg n) = reg n J (bar 1) from rfl, lg_apply_y]
        have e2 : lg D (reg n J 1) (reg n J (bar 1)) (N J) (reg n J 2) = D (reg n J 2) :=
          lg_apply_other _ (by rw [Ne, reg_inj hJ hJn hJ hJn]; simp [bar])
            (by rw [Ne, reg_inj hJ hJn hJ hJn]; simp [bar]) _
        have e3 : lg D (reg n J 1) (reg n J (bar 1)) (N J) (reg n J 3) = D (reg n J 3) :=
          lg_apply_other _ (by rw [Ne, reg_inj hJ hJn hJ hJn]; simp [bar])
            (by rw [Ne, reg_inj hJ hJn hJ hJn]; simp [bar]) _
        rw [e0, e1, e2, e3]; omega
      · have e3 : lg D (reg n J 3) (reg n J (bar 3)) (N J) (reg n J 3) = D (reg n J 2) + N J := by
          rw [lg_apply_x _ hne]; rfl
        have e2 : lg D (reg n J 3) (reg n J (bar 3)) (N J) (reg n J 2) = D (reg n J 3) - N J := by
          rw [show (reg n J 2 : Reg n) = reg n J (bar 3) from rfl, lg_apply_y]
        have e0 : lg D (reg n J 3) (reg n J (bar 3)) (N J) (reg n J 0) = D (reg n J 0) :=
          lg_apply_other _ (by rw [Ne, reg_inj hJ hJn hJ hJn]; simp [bar])
            (by rw [Ne, reg_inj hJ hJn hJ hJn]; simp [bar]) _
        have e1 : lg D (reg n J 3) (reg n J (bar 3)) (N J) (reg n J 1) = D (reg n J 1) :=
          lg_apply_other _ (by rw [Ne, reg_inj hJ hJn hJ hJn]; simp [bar])
            (by rw [Ne, reg_inj hJ hJn hJ hJn]; simp [bar]) _
        rw [e0, e1, e2, e3]; omega

theorem apa_prev {J : ℕ} (hJ : 1 ≤ J) (hJn : J ≤ n) : APA n (J - 1) := by
  rcases Nat.eq_or_lt_of_le hJ with h | h
  · rw [← h]; exact apOK_zero.apA
  · exact (levels (J - 1) (by omega) (by omega)).apA

theorem q2_ap {J : ℕ} (hJ : 1 ≤ J) (hJn : J ≤ n) {k₀ : Fin 4} (hk₀ : k₀ = 0 ∨ k₀ = 2)
    {D : Reg n → ℕ} (hD : Q2 J k₀ D) (OF : Bool) :
    (prog n).Terminates (.assertProper J) D OF ∧
    ∀ D' OF' b, (prog n).Returns (.assertProper J) D OF D' OF' b → OF' = OF ∧ Q2 J k₀ D' := by
  refine forward_preserve (prog := prog n) (fun E => Q2 J k₀ E) (by rw [code_assertProper n hJ]; simp)
    (ap_fwd hJ hJn) (fun pc q tT tF hq E OF₁ hE => ?_) hD
  have hcode := code_assertProper n hJ
  have hlt := instr_lt hq
  rw [hcode] at hlt
  rw [Program.instr, hcode] at hq
  simp only [List.length_cons, List.length_nil] at hlt
  interval_cases pc <;> simp at hq <;> obtain ⟨rfl, -, -⟩ := hq
  · obtain ⟨hR, -, hT⟩ := apa_prev hJ hJn E OF₁ (.inl hE.1)
    exact ⟨hT, fun E' OF' b h => by obtain ⟨h1, h2, -⟩ := (hR _ _ _).1 h; subst h2; exact ⟨h1, hE⟩⟩
  · obtain ⟨hT, -, hR⟩ := q2_large hJ hJn hk₀ hE 1 (.inl rfl) OF₁
    exact ⟨hT, fun E' OF' b h => by obtain ⟨h1, h2, -⟩ := hR _ _ _ h; exact ⟨h1, h2⟩⟩
  · obtain ⟨hT, -, hR⟩ := q2_large hJ hJn hk₀ hE 3 (.inr rfl) OF₁
    exact ⟨hT, fun E' OF' b h => by obtain ⟨h1, h2, -⟩ := hR _ _ _ h; exact ⟨h1, h2⟩⟩

theorem lemma_4c_case2 {C : Reg n → ℕ} {J : ℕ} (hJ : 1 ≤ J) (hJn : J ≤ n) {k₀ : Fin 4}
    (hk₀ : k₀ = 0 ∨ k₀ = 2) (hC : Q2 J k₀ C) (OF₀ : Bool) :
    ∀ s, (prog n).Reach₀ ((prog n).init C OF₀) s → (prog n).CanRestart s := by
  let ord : ℕ → ℕ := fun r => if r ≤ 2 then 2 - r else 7 - r
  have hord : ∀ r, ord r ≤ 9 := fun r => by simp only [ord]; split_ifs <;> omega
  let I : Loc (Reg n) → Prop := fun a => Q2 J k₀ a.C ∧ a.pc ≤ 5 * J ∧ (a.pc = 5 * J - 3 → k₀ = 2)
  have hsmall : ∀ D, Q2 J k₀ D → ∀ k, k = bar k₀ → ¬ N J ≤ D (reg n J k) := by
    rintro D hD k rfl h; have := hD.2.1; omega
  have hIc : ∀ a a', I a → (prog n).AStep .main a a' → I a' := by
    rintro ⟨pc, D, OF⟩ a' ⟨hD, hpc, h3⟩ hs
    simp only at hD hpc h3
    have hPj : ∀ j, j < J → Proper D j := fun j hj => hD.1.mono (by omega)
    rcases main_astep hs with ⟨rfl, rfl⟩ | ⟨j, hj, hjn, h⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
        ⟨rfl, D', OF', b, hr, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨hD, by om, by om⟩
    · rcases Nat.lt_or_ge j J with hjJ | hjJ
      · have hP := hPj j hjJ
        rcases h with ⟨rfl, D', OF', b, hr, rfl⟩ | ⟨rfl, D', OF', b, hr, rfl⟩ |
            ⟨rfl, D', OF', b, hr, rfl⟩ | ⟨rfl, D', OF', b, hr, rfl⟩ | ⟨rfl, rfl⟩
        · obtain ⟨rfl, rfl⟩ := (large_proper hj hjn OF hP 1 (.inl rfl) true).2 _ _ _ hr
          exact ⟨hD, by cases b <;> simp <;> om, by cases b <;> simp <;> om⟩
        · obtain ⟨rfl, rfl⟩ := (large_proper hj hjn OF hP 3 (.inr rfl) true).2 _ _ _ hr
          exact ⟨hD, by cases b <;> simp <;> om, by cases b <;> simp <;> om⟩
        · obtain ⟨rfl, rfl⟩ := (ap_proper hj hjn OF (.inl hP)).2.1 _ _ _ hr
          exact ⟨hD, by om, by om⟩
        · obtain ⟨rfl, rfl⟩ := (ae_facts hj hjn OF).2.1 _ _ _ hr
          exact ⟨hD, by om, by om⟩
        · exact ⟨hD, by om, by om⟩
      · obtain rfl : j = J := by
          rcases h with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> om
        rcases h with ⟨rfl, D', OF', b, hr, rfl⟩ | ⟨rfl, D', OF', b, hr, rfl⟩ |
            ⟨rfl, D', OF', b, hr, rfl⟩ | ⟨rfl, D', OF', b, hr, rfl⟩ | ⟨rfl, rfl⟩
        · obtain ⟨-, hQ, hb⟩ := (q2_large hJ hJn hk₀ hD 1 (.inl rfl) OF).2.2 _ _ _ hr
          cases b
          · exact ⟨hQ, by som, by som⟩
          · refine ⟨hQ, by som, fun _ => ?_⟩
            rcases hk₀ with rfl | rfl
            · exact absurd (hb rfl) (hsmall D hD 1 rfl)
            · rfl
        · obtain ⟨-, hQ, hb⟩ := (q2_large hJ hJn hk₀ hD 3 (.inr rfl) OF).2.2 _ _ _ hr
          cases b
          · exact ⟨hQ, by som, by som⟩
          · exact absurd (hb rfl) (hsmall D hD 3 (by rw [h3 rfl]; rfl))
        · obtain ⟨-, hQ⟩ := (q2_ap hJ hJn hk₀ hD OF).2 _ _ _ hr
          exact ⟨hQ, by om, by om⟩
        · obtain ⟨rfl, rfl⟩ := (ae_facts hj hjn OF).2.1 _ _ _ hr
          exact ⟨hD, by om, by om⟩
        · exact ⟨hD, by om, by om⟩
    · exfalso; om
    · exfalso; om
    · exfalso; om
    · exfalso; om
  refine main_restarts I ⟨hC, by simp, by simp; omega⟩ hIc ?_ (rkMain n J ord) ?_
  · rintro ⟨pc, D, OF⟩ ⟨hD, hpc, -⟩ q tT tF hq
    simp only at hD hq hpc ⊢
    rcases main_call_cases hq with ⟨j, hj, hjn, ⟨h1, rfl⟩ | ⟨h1, rfl⟩ | ⟨h1, rfl⟩ | ⟨-, rfl⟩⟩ | ⟨h1, rfl⟩
    · exact ((levels j hj hjn).largeB 1 D OF (hD.1.mono (by omega))).2.2
    · exact ((levels j hj hjn).largeB 3 D OF (hD.1.mono (by omega))).2.2
    · rcases Nat.lt_or_ge j J with hjJ | hjJ
      · exact (ap_proper hj hjn OF (.inl (hD.1.mono (by omega)))).2.2.2
      · obtain rfl : j = J := by omega
        exact (q2_ap hJ hJn hk₀ hD OF).1
    · exact (ae_facts hj hjn OF).2.2.2
    · exfalso; omega
  · rintro ⟨pc, D, OF⟩ ⟨hD, hpc, h3⟩
    simp only at hD hpc h3
    rcases main_pc_cases (n := n) pc with rfl | ⟨j, r, hj, hjn, hr, rfl⟩ | h
    · exact .inr ⟨_, .setOF (instr_main_zero n), rk_start J ord hord D D OF false⟩
    · rcases Nat.lt_or_ge j J with hjJ | hjJ
      · exact .inr (pass_step J ord hord hj hjn hjJ hr OF (hD.1.mono (by omega)))
      · obtain rfl : j = J := by omega
        have hjJ' : ¬ j < j := by omega
        have e : ∀ r (hr : r < 5) D OF, rkMain n j ord ⟨5 * j - 4 + r, D, OF⟩ =
            10 * (n + 1 - j) + ord r := fun r hr D OF => by
          rw [rkMain_it (n := n) j ord hj hjn hr, if_neg hjJ']
        have e2 := e 2 (by omega); have e3 := e 3 (by omega)
        have e4 := e 4 (by omega); have e0 := e 0 (by omega); have e1 := e 1 (by omega)
        simp only [show 5 * j - 4 + 1 = 5 * j - 3 by omega, show 5 * j - 4 + 2 = 5 * j - 2 by omega,
          show 5 * j - 4 + 3 = 5 * j - 1 by omega, show 5 * j - 4 + 4 = 5 * j by omega,
          Nat.add_zero] at e1 e2 e3 e4 e0
        have hF : ∀ k, (prog n).Returns (.large j k) D OF D OF false := fun k =>
          (((levels j hj hjn).largeB k D OF hD.1).1 _ _ _).2 ⟨rfl, .inl ⟨rfl, rfl⟩⟩
        interval_cases r
        · refine .inr ⟨_, .call (by simpa using instr_it0 hj hjn) (hF 1), ?_⟩
          simp only [Bool.cond_false, Nat.add_zero, e2, e0]; simp [ord]
        · rw [show 5 * j - 4 + 1 = 5 * j - 3 by omega]
          refine .inr ⟨_, .call (instr_it1 hj hjn) (hF 3), ?_⟩
          simp only [Bool.cond_false, e2, e1]; simp [ord]
        · rw [show 5 * j - 4 + 2 = 5 * j - 2 by omega]
          refine .inl (.inr ⟨_, _, _, instr_it2 hj hjn, ?_⟩)
          have hB := hD.2.2
          unfold Bad at hB
          rcases hB with hB | hB
          · exact (levels j hj hjn).apC D OF hD.1 0 (by simp) hB
          · exact (levels j hj hjn).apC D OF hD.1 2 (by simp) hB
        · rw [show 5 * j - 4 + 3 = 5 * j - 1 by omega]
          rcases (ae_facts hj hjn (D := D) OF).2.2.2.returns_or_restarts with ⟨D', OF', b, hr'⟩ | hr'
          · refine .inr ⟨_, .call (instr_it3 hj hjn) hr', ?_⟩
            simp only [Bool.cond_self, e4, e3]; simp [ord]
          · exact .inl (.inr ⟨_, _, _, instr_it3 hj hjn, hr'⟩)
        · rw [show 5 * j - 4 + 4 = 5 * j by omega]
          refine .inr ⟨_, .goto (instr_it4 hj hjn), ?_⟩
          simp only [e0, e4]; simp [ord]
    · exfalso; omega

/-! ### `Main` on low configurations: case 1 of Lemma 4(c), and Lemma 4(a) -/

theorem low_closure {C : Reg n → ℕ} {J : ℕ} (hJ : 1 ≤ J) (hJn : J ≤ n) (hL : Low C J) {pc : ℕ}
    {OF : Bool} {a' : Loc (Reg n)} (hpc : pc ≤ 5 * J) (h3 : pc = 5 * J - 3 → N J ≤ C (reg n J 1))
    (hs : (prog n).AStep .main ⟨pc, C, OF⟩ a') :
    a'.C = C ∧ 1 ≤ a'.pc ∧ a'.pc ≤ 5 * J ∧ (a'.pc = 5 * J - 3 → N J ≤ C (reg n J 1)) ∧
      (pc ≠ 0 → a'.OF = OF) ∧ (pc = 0 → a'.OF = false) ∧ (5 * J - 4 ≤ pc → 5 * J - 4 ≤ a'.pc) := by
  obtain ⟨hP, hnP, hx0, hy0, hx1, hy1⟩ := hL
  rcases main_astep hs with ⟨rfl, rfl⟩ | ⟨j, hj, hjn, h⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, D', OF', b, hr, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨rfl, le_rfl, by som, by som, by simp, fun _ => rfl, by som⟩
  · rcases Nat.lt_or_ge j J with hjJ | hjJ
    · have hPj : Proper C j := hP.mono (by omega)
      rcases h with ⟨rfl, D', OF', b, hr, rfl⟩ | ⟨rfl, D', OF', b, hr, rfl⟩ |
          ⟨rfl, D', OF', b, hr, rfl⟩ | ⟨rfl, D', OF', b, hr, rfl⟩ | ⟨rfl, rfl⟩
      · obtain ⟨rfl, rfl⟩ := (large_proper hj hjn OF hPj 1 (.inl rfl) true).2 _ _ _ hr
        refine ⟨rfl, ?_, ?_, ?_, fun _ => rfl, by omega, ?_⟩ <;> cases b <;> simp <;> omega
      · obtain ⟨rfl, rfl⟩ := (large_proper hj hjn OF hPj 3 (.inr rfl) true).2 _ _ _ hr
        refine ⟨rfl, ?_, ?_, ?_, fun _ => rfl, by omega, ?_⟩ <;> cases b <;> simp <;> omega
      · obtain ⟨rfl, rfl⟩ := (ap_proper hj hjn OF (.inl hPj)).2.1 _ _ _ hr
        exact ⟨rfl, by som, by som, by som, fun _ => rfl, by omega, by som⟩
      · obtain ⟨rfl, rfl⟩ := (ae_facts hj hjn OF).2.1 _ _ _ hr
        exact ⟨rfl, by som, by som, by som, fun _ => rfl, by omega, by som⟩
      · exact ⟨rfl, by som, by som, by som, fun _ => rfl, by omega, by som⟩
    · obtain rfl : j = J := by
        rcases h with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> omega
      have hLow : Low C j := ⟨hP, hnP, hx0, hy0, hx1, hy1⟩
      rcases h with ⟨rfl, D', OF', b, hr, rfl⟩ | ⟨rfl, D', OF', b, hr, rfl⟩ |
          ⟨rfl, D', OF', b, hr, rfl⟩ | ⟨rfl, D', OF', b, hr, rfl⟩ | ⟨rfl, rfl⟩
      · have hne := large_bar_noeffect hj hjn (levels j hj hjn).largeB 0 OF hP hx0 hx1
        have hb : b = true → N j ≤ C (reg n j 1) := by
          obtain ⟨h1, h2 | h2⟩ := (((levels j hj hjn).largeB 1 C OF hP).1 _ _ _).1 hr
          · exact fun hb => by simp [h2.1] at hb
          · exact fun _ => h2.2.1
        obtain ⟨hO, hCC⟩ := hne.1 _ _ _ hr
        subst OF' D'
        refine ⟨rfl, ?_, ?_, ?_, fun _ => rfl, by omega, ?_⟩ <;> cases b <;> simp <;> try omega
        exact hb rfl
      · have hne := large_bar_noeffect hj hjn (levels j hj hjn).largeB 2 OF hP hy0 hy1
        have hL3 := (((levels j hj hjn).largeB 3 C OF hP).1 _ _ _).1 hr
        obtain ⟨hO, hCC⟩ := hne.1 _ _ _ hr
        subst OF' D'
        cases b
        · exact ⟨rfl, by som, by som, by som, fun _ => rfl, by omega, by som⟩
        · exfalso
          obtain ⟨-, h2 | h2⟩ := hL3
          · simp at h2
          · have hx := h3 rfl
            apply hnP
            rw [proper_succ_iff hj]
            exact ⟨hP, hx0, by omega, hy0, by have := h2.2.1; omega⟩
      · obtain ⟨rfl, rfl⟩ := (ap_proper hj hjn OF (.inr hLow)).2.1 _ _ _ hr
        exact ⟨rfl, by som, by som, by som, fun _ => rfl, by omega, by som⟩
      · obtain ⟨rfl, rfl⟩ := (ae_facts hj hjn OF).2.1 _ _ _ hr
        exact ⟨rfl, by som, by som, by som, fun _ => rfl, by omega, by som⟩
      · exact ⟨rfl, by som, by som, by som, fun _ => rfl, by omega, by som⟩
  all_goals (exfalso; omega)

theorem low_terminates {C : Reg n → ℕ} {J : ℕ} (hJ : 1 ≤ J) (hJn : J ≤ n) (hL : Low C J) {pc : ℕ}
    (OF : Bool) (hpc : pc ≤ 5 * J) {q : Proc} {tT tF : ℕ}
    (hq : (prog n).instr .main pc = some (.call q tT tF)) : (prog n).Terminates q C OF := by
  rcases main_call_cases hq with ⟨j, hj, hjn, ⟨h1, rfl⟩ | ⟨h1, rfl⟩ | ⟨h1, rfl⟩ | ⟨-, rfl⟩⟩ | ⟨h1, rfl⟩
  · exact ((levels j hj hjn).largeB 1 C OF (hL.1.mono (by omega))).2.2
  · exact ((levels j hj hjn).largeB 3 C OF (hL.1.mono (by omega))).2.2
  · rcases Nat.lt_or_ge j J with hjJ | hjJ
    · exact (ap_proper hj hjn OF (.inl (hL.1.mono (by omega)))).2.2.2
    · obtain rfl : j = J := by omega
      exact (ap_proper hj hjn OF (.inr hL)).2.2.2
  · exact (ae_facts hj hjn OF).2.2.2
  · exfalso; omega

/-- Case 1 of Lemma 4(c): `j`-low but not `(j+1)`-empty. -/
theorem lemma_4c_case1 {C : Reg n → ℕ} {J : ℕ} (hJ : 1 ≤ J) (hJn : J ≤ n) (hL : Low C J)
    (hE : ¬ Empty C (J + 1)) (OF₀ : Bool) :
    ∀ s, (prog n).Reach₀ ((prog n).init C OF₀) s → (prog n).CanRestart s := by
  let ord : ℕ → ℕ := fun r => if r = 4 then 3 else if r ≤ 1 then 2 else 3 - r
  have hord : ∀ r, ord r ≤ 9 := fun r => by simp only [ord]; split_ifs <;> omega
  let I : Loc (Reg n) → Prop := fun a => a.C = C ∧ a.pc ≤ 5 * J ∧
    (a.pc = 5 * J - 3 → N J ≤ C (reg n J 1))
  have hIc : ∀ a a', I a → (prog n).AStep .main a a' → I a' := by
    rintro ⟨pc, D, OF⟩ a' ⟨hD, hpc, h3⟩ hs
    simp only at hD hpc h3; subst hD
    obtain ⟨h1, -, h2, h4, -⟩ := low_closure hJ hJn hL hpc h3 hs
    exact ⟨h1, h2, h4⟩
  refine main_restarts I ⟨rfl, by simp, by simp; omega⟩ hIc ?_ (rkMain n J ord) ?_
  · rintro ⟨pc, D, OF⟩ ⟨hD, hpc, -⟩ q tT tF hq
    simp only at hD hpc hq ⊢; subst hD
    exact low_terminates hJ hJn hL OF hpc hq
  · rintro ⟨pc, D, OF⟩ ⟨hD, hpc, h3⟩
    simp only at hD hpc h3; subst hD
    rcases main_pc_cases (n := n) pc with rfl | ⟨j, r, hj, hjn, hr, rfl⟩ | h
    · exact .inr ⟨_, .setOF (instr_main_zero n), rk_start J ord hord D D OF false⟩
    · rcases Nat.lt_or_ge j J with hjJ | hjJ
      · exact .inr (pass_step J ord hord hj hjn hjJ hr OF (hL.1.mono (by omega)))
      · obtain rfl : j = J := by omega
        have hjJ' : ¬ j < j := by omega
        have e : ∀ r (hr : r < 5) D OF, rkMain n j ord ⟨5 * j - 4 + r, D, OF⟩ =
            10 * (n + 1 - j) + ord r := fun r hr D OF => by
          rw [rkMain_it (n := n) j ord hj hjn hr, if_neg hjJ']
        have e2 := e 2 (by omega); have e3 := e 3 (by omega)
        have e4 := e 4 (by omega); have e0 := e 0 (by omega); have e1 := e 1 (by omega)
        simp only [show 5 * j - 4 + 1 = 5 * j - 3 by omega, show 5 * j - 4 + 2 = 5 * j - 2 by omega,
          show 5 * j - 4 + 3 = 5 * j - 1 by omega, show 5 * j - 4 + 4 = 5 * j by omega,
          Nat.add_zero] at e1 e2 e3 e4 e0
        have hF : ∀ k, (prog n).Returns (.large j k) D OF D OF false := fun k =>
          (((levels j hj hjn).largeB k D OF hL.1).1 _ _ _).2 ⟨rfl, .inl ⟨rfl, rfl⟩⟩
        interval_cases r
        · refine .inr ⟨_, .call (by simpa using instr_it0 hj hjn) (hF 1), ?_⟩
          simp only [Bool.cond_false, Nat.add_zero, e2, e0]; simp [ord]
        · rw [show 5 * j - 4 + 1 = 5 * j - 3 by omega]
          refine .inr ⟨_, .call (instr_it1 hj hjn) (hF 3), ?_⟩
          simp only [Bool.cond_false, e2, e1]; simp [ord]
        · rw [show 5 * j - 4 + 2 = 5 * j - 2 by omega]
          refine .inr ⟨_, .call (instr_it2 hj hjn) (ap_proper hj hjn OF (.inr hL)).1, ?_⟩
          simp only [Bool.cond_self, e3, e2]; simp [ord]
        · rw [show 5 * j - 4 + 3 = 5 * j - 1 by omega]
          exact .inl (.inr ⟨_, _, _, instr_it3 hj hjn, (ae_facts hj hjn OF).2.2.1.2 hE⟩)
        · rw [show 5 * j - 4 + 4 = 5 * j by omega]
          refine .inr ⟨_, .goto (instr_it4 hj hjn), ?_⟩
          simp only [e0, e4]; simp [ord]
    · exfalso; omega

/-- The first step of `Main` sets `OF := false`. -/
theorem reach_main_init {C : Reg n → ℕ} {OF₀ : Bool} {s : Cfg (Reg n) Proc}
    (h : (prog n).Reach₀ ((prog n).init C OF₀) s) :
    s = (prog n).init C OF₀ ∨ (prog n).Reach₀ (atLoc .main ⟨1, C, false⟩) s := by
  rcases Relation.ReflTransGen.cases_head h with rfl | ⟨c, hc, hcs⟩
  · exact .inl rfl
  · refine .inr ?_
    have h0 := instr_main_zero n
    have hm : (prog n).main = .main := rfl
    have : c = atLoc .main ⟨1, C, false⟩ := by
      cases hc with
      | setOF h => rw [hm, h0] at h; cases h; rfl
      | move h => rw [hm, h0] at h; cases h
      | swap h => rw [hm, h0] at h; cases h
      | detectT h => rw [hm, h0] at h; cases h
      | detectF h => rw [hm, h0] at h; cases h
      | goto h => rw [hm, h0] at h; cases h
      | call h => rw [hm, h0] at h; cases h
    rwa [← this]

/-- **Lemma 4(a)**: on a `j`-low and `(j+1)`-empty configuration, `Main` may stabilise to
`false`. -/
theorem lemma_4a {C : Reg n → ℕ} {J : ℕ} (hJ : 1 ≤ J) (hJn : J ≤ n) (hL : Low C J)
    (hE : Empty C (J + 1)) (OF₀ : Bool) :
    (∃ s, (prog n).Reach₀ ((prog n).init C OF₀) s ∧ ¬ (prog n).CanRestart s) ∧
    ∀ s, (prog n).Reach₀ ((prog n).init C OF₀) s →
      ∃ s', (prog n).Reach₀ s s' ∧ ∀ s'', (prog n).Reach₀ s' s'' → s''.OF = false := by
  -- all abstract configurations after the first step
  let I : Loc (Reg n) → Prop := fun a => a.C = C ∧ 1 ≤ a.pc ∧ a.pc ≤ 5 * J ∧ a.OF = false ∧
    (a.pc = 5 * J - 3 → N J ≤ C (reg n J 1))
  have hIc : ∀ a a', I a → (prog n).AStep .main a a' → I a' := by
    rintro ⟨pc, D, OF⟩ a' ⟨hD, h1, hpc, hOF, h3⟩ hs
    try dsimp only at hD h1 hpc hOF h3
    subst D OF
    obtain ⟨e1, e2, e3, e4, e5, -⟩ := low_closure hJ hJn hL hpc h3 hs
    exact ⟨e1, e2, e3, e5 (by omega), e4⟩
  have hI1 : I ⟨1, C, false⟩ := ⟨rfl, le_rfl, by som, rfl, by som⟩
  -- the loop of level `J` is a trap without restarts
  set T : Loc (Reg n) := ⟨5 * J - 4, C, false⟩ with hTdef
  have hTnr : ¬ (prog n).CanRestart (atLoc .main T) := by
    refine not_canRestart_of fun a ha => ?_
    have hT : I a ∧ 5 * J - 4 ≤ a.pc := by
      refine AReach.inv (I := fun a => I a ∧ 5 * J - 4 ≤ a.pc) ?_ ha
        ⟨⟨rfl, by rw [hTdef]; som, by rw [hTdef]; som, rfl, by rw [hTdef]; som⟩, le_rfl⟩
      rintro ⟨pc, D, OF⟩ a' ⟨⟨hD, h1, hpc, hOF, h3⟩, hlo⟩ hs
      try dsimp only at hD h1 hpc hOF h3 hlo
      subst D OF
      obtain ⟨e1, e2, e3, e4, e5, -, e6⟩ := low_closure hJ hJn hL hpc h3 hs
      exact ⟨⟨e1, e2, e3, e5 (by omega), e4⟩, e6 hlo⟩
    obtain ⟨⟨hD, -, hpc, hOF, -⟩, hlo⟩ := hT
    obtain ⟨pc, D, OF⟩ := a
    try dsimp only at hD hpc hOF hlo
    subst D OF
    rintro (h | ⟨q, tT, tF, hq, hr⟩)
    · rcases main_pc_cases (n := n) pc with rfl | ⟨j, r, hj, hjn, hr, rfl⟩ | h'
      · omega
      · obtain rfl : j = J := by omega
        interval_cases r
        · rw [Nat.add_zero, instr_it0 hj hjn] at h; simp at h
        · rw [show 5 * j - 4 + 1 = 5 * j - 3 by omega, instr_it1 hj hjn] at h; simp at h
        · rw [show 5 * j - 4 + 2 = 5 * j - 2 by omega, instr_it2 hj hjn] at h; simp at h
        · rw [show 5 * j - 4 + 3 = 5 * j - 1 by omega, instr_it3 hj hjn] at h; simp at h
        · rw [show 5 * j - 4 + 4 = 5 * j by omega, instr_it4 hj hjn] at h; simp at h
      · omega
    · rcases main_call_cases hq with ⟨j, hj, hjn, ⟨h1, rfl⟩ | ⟨h1, rfl⟩ | ⟨h1, rfl⟩ | ⟨h1, rfl⟩⟩ | ⟨h1, rfl⟩
      · obtain rfl : j = J := by dsimp only at h1; omega
        exact ((levels j hj hjn).largeB 1 C false hL.1).2.1 hr
      · obtain rfl : j = J := by dsimp only at h1; omega
        exact ((levels j hj hjn).largeB 3 C false hL.1).2.1 hr
      · obtain rfl : j = J := by dsimp only at h1; omega
        exact (ap_proper hj hjn false (.inr hL)).2.2.1 hr
      · obtain rfl : j = J := by dsimp only at h1; omega
        exact ((ae_facts hj hjn false).2.2.1.1 hr) hE
      · dsimp only at h1; omega
  have hTreach : (prog n).AReach .main ⟨1, C, false⟩ T := by
    rcases Nat.eq_or_lt_of_le hJ with rfl | hJ1
    · exact .refl
    · have := through_propers false (J := J) (by omega) hL.1 1 le_rfl hJ1 0 (by omega)
      simpa using this
  refine ⟨⟨atLoc .main T, ?_, hTnr⟩, fun s hs => ?_⟩
  · exact (Relation.ReflTransGen.single (.setOF (instr_main_zero n))).trans (hTreach.reach₀ [])
  · have hAG : ∀ s, (prog n).Reach₀ (atLoc .main ⟨1, C, false⟩) s →
        ∀ s'', (prog n).Reach₀ s s'' → s''.OF = false := fun s hs s'' hs'' =>
      main_of_eq (fun a ha => (AReach.inv hIc ha hI1).2.2.2.1) s'' (hs.trans hs'')
    rcases reach_main_init hs with rfl | hs1
    · exact ⟨_, .single (.setOF (instr_main_zero n)), hAG _ .refl⟩
    · exact ⟨s, .refl, hAG s hs1⟩

end Podc.PPDoubleExpThresholds
