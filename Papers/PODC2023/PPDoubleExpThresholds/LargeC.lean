import Papers.PODC2023.PPDoubleExpThresholds.Incr

/-!
# Lemma 12(c): robustness of `Large(x)` for `j < i`

* `large_robust_low`: `j ≤ i − 2`. All callees are `j`-robust and `AssertProper(i − 2)` may
  restart at every iteration.
* `large_robust_mid` (in `LargeSym.lean`): `j = i − 1`, the paper's symmetry argument.
-/

namespace Podc.PPDoubleExpThresholds

open Program

variable {n : ℕ}

set_option hygiene false in
local macro "ins" : tactic => `(tactic| (rw [Program.instr, hcode]; try rfl))

/-- **Lemma 12(c)** for `j ≤ i − 2`. -/
theorem large_robust_low {i : ℕ} (hi : 2 ≤ i) (hin : i ≤ n)
    (hAPR : Robust n (.assertProper (i - 2))) (hAPB : APB n (i - 2))
    (hZR : ∀ k, Robust n (.zero (i - 1) k))
    (hIR : ∀ bx by', RobustOn n (fun j => j < i - 1) (.incrPair (i - 1) bx by')) (k : Fin 4) :
    RobustOn n (fun j => j ≤ i - 2) (.large i k) := by
  intro j hj hjn hji C OF hC
  have hcode := code_large n hi k
  have hlv : ∀ k', (reg n i k').lvl = i := fun k' => lvl_reg (by omega) hin k'
  have hHmv : ∀ D (a b : Fin 4), High (mv D (reg n i a) (reg n i b)) j ↔ High D j := fun D a b =>
    (off_mv D (hlv a) (hlv b)).high_iff hj (by omega) hin
  have hHswp : ∀ D (a b : Fin 4), High (swp D (reg n i a) (reg n i b)) j ↔ High D j := fun D a b =>
    (off_swp D (hlv a) (hlv b)).high_iff hj (by omega) hin
  -- the callees: robust for `j`
  have hcall : ∀ q, (q = .assertProper (i - 2) ∨ (∃ k', q = .zero (i - 1) k') ∨
      ∃ bx by', q = .incrPair (i - 1) bx by') → ∀ D OF₁, High D j →
      (prog n).Terminates q D OF₁ ∧ ∀ D' OF' b, (prog n).Returns q D OF₁ D' OF' b →
        OF' = OF₁ ∧ High D' j := by
    rintro q (rfl | ⟨k', rfl⟩ | ⟨bx, by', rfl⟩) D OF₁ hD
    · exact hAPR j hj hjn trivial D OF₁ hD
    · exact hZR k' j hj hjn trivial D OF₁ hD
    · exact hIR bx by' j hj hjn (by omega) D OF₁ hD
  let I : Loc (Reg n) → Prop := fun a => High a.C j ∧ a.OF = OF ∧ a.pc < 25 ∧
    (a.pc = 7 → 0 < a.C (reg n i k)) ∧ (a.pc = 20 → 0 < a.C (reg n i (bar k)))
  have hI : ∀ a a', I a → (prog n).AStep (.large i k) a a' → I a' := by
    rintro ⟨pc, D, OF₁⟩ a' ⟨hD, rfl, hpc, h7, h20⟩ hs
    simp only at hD hpc h7 h20
    rw [astep_iff] at hs
    interval_cases pc <;>
      simp only [Program.instr, hcode, List.getElem?_cons_succ, List.getElem?_cons_zero] at hs
    all_goals first
      | (obtain ⟨C', OF', b, hr, rfl⟩ := hs
         obtain ⟨rfl, h'⟩ := (hcall _ (by simp) D OF₁ hD).2 _ _ _ hr
         exact ⟨h', rfl, by cases b <;> simp, by cases b <;> simp, by cases b <;> simp⟩)
      | (subst hs; exact ⟨hD, rfl, by simp, by simp, by simp⟩)
      | (subst hs; exact ⟨(hHswp _ _ _).2 hD, rfl, by simp, by simp, by simp⟩)
      | (rcases hs with ⟨hx, rfl⟩ | rfl
         · exact ⟨hD, rfl, by simp, fun _ => hx, by simp⟩
         · exact ⟨hD, rfl, by simp, by simp, by simp⟩)
      | (rcases hs with ⟨hx, rfl⟩ | rfl
         · exact ⟨hD, rfl, by simp, by simp, fun _ => hx⟩
         · exact ⟨hD, rfl, by simp, by simp, by simp⟩)
      | (obtain ⟨-, rfl⟩ := hs; exact ⟨(hHmv _ _ _).2 hD, rfl, by simp, by simp, by simp⟩)
  have hreach : ∀ a, (prog n).AReach (.large i k) ⟨0, C, OF⟩ a → I a :=
    fun a ha => AReach.inv hI ha ⟨hC, rfl, by simp, by simp, by simp⟩
  have hcallT : ∀ a, (prog n).AReach (.large i k) ⟨0, C, OF⟩ a → ∀ q tT tF,
      (prog n).instr (.large i k) a.pc = some (.call q tT tF) → (prog n).Terminates q a.C a.OF := by
    intro a ha q tT tF hq
    obtain ⟨hD, -, hpc, -, -⟩ := hreach a ha
    obtain ⟨pc, D, OF₁⟩ := a
    simp only at hD hpc hq ⊢
    interval_cases pc <;>
      simp only [Program.instr, hcode, List.getElem?_cons_succ, List.getElem?_cons_zero,
        Option.some.injEq, Instr.call.injEq, reduceCtorEq] at hq <;> obtain ⟨rfl, -, -⟩ := hq <;>
      exact (hcall _ (by simp) D OF₁ hD).1
  refine ⟨terminates_of hcallT (fun a ha => exists_target_of_rank
    (T := (prog n).ADone (.large i k))
    (fun a => if a.pc ≤ 5 then 5 - a.pc else 30 - a.pc) (fun a ha => ?_) a ha),
    fun C' OF' b h => ?_⟩
  · obtain ⟨hD, hOF, hpc, h7, h20⟩ := hreach a ha
    obtain ⟨pc, D, OF₁⟩ := a
    simp only at hD hpc hOF h7 h20 ⊢
    -- a call: step to its return, or it restarts
    have callStep : ∀ q tT tF, (prog n).instr (.large i k) pc = some (.call q tT tF) →
        (pc < tT ∧ pc < tF ∧ (5 < pc ∨ (tT ≤ 5 ∧ tF ≤ 5))) →
        (prog n).ADone (.large i k) ⟨pc, D, OF₁⟩ ∨ ∃ a', (prog n).AStep (.large i k) ⟨pc, D, OF₁⟩ a' ∧
          (if a'.pc ≤ 5 then 5 - a'.pc else 30 - a'.pc) <
            (if pc ≤ 5 then 5 - pc else 30 - pc) := by
      intro q tT tF hq hlt
      have hT := hcallT ⟨pc, D, OF₁⟩ ha q tT tF hq
      rcases hT.returns_or_restarts with ⟨C', OF', b, hr⟩ | hr
      · refine .inr ⟨_, .call hq hr, ?_⟩
        cases b <;> simp only [cond_true, cond_false] <;> split_ifs <;> omega
      · exact .inl (.inr (.inr ⟨q, tT, tF, hq, hr⟩))
    interval_cases pc
    · exact callStep _ _ _ (by ins) (by omega)
    · exact callStep _ _ _ (by ins) (by omega)
    · exact .inl (.inr (.inl (by ins)))
    · exact .inr ⟨_, .goto (by ins), by simp⟩
    · exact .inr ⟨_, .goto (by ins), by simp⟩
    · exact .inl (.inr (.inr ⟨_, 6, 6, by ins, hAPB j hj hji D OF₁ hD⟩))
    · exact .inr ⟨_, .detectF (by ins), by simp⟩
    · exact .inr ⟨_, .move (by ins) (h7 rfl), by simp⟩
    · exact callStep _ _ _ (by ins) (by omega)
    · exact callStep _ _ _ (by ins) (by omega)
    · exact callStep _ _ _ (by ins) (by omega)
    · exact .inr ⟨_, .swap (by ins), by simp⟩
    · exact .inl (.inl ⟨true, by ins⟩)
    · exact .inr ⟨_, .goto (by ins), by simp⟩
    · exact .inr ⟨_, .goto (by ins), by simp⟩
    · exact callStep _ _ _ (by ins) (by omega)
    · exact callStep _ _ _ (by ins) (by omega)
    · exact .inl (.inl ⟨false, by ins⟩)
    · exact .inr ⟨_, .goto (by ins), by simp⟩
    · exact .inr ⟨_, .detectF (by ins), by simp⟩
    · exact .inr ⟨_, .move (by ins) (h20 rfl), by simp⟩
    · exact callStep _ _ _ (by ins) (by omega)
    · exact .inr ⟨_, .goto (by ins), by simp⟩
    · exact .inr ⟨_, .goto (by ins), by simp⟩
    · exact .inl (.inl ⟨false, by ins⟩)
  · obtain ⟨a, ha, rfl, rfl, -⟩ := returns_iff.1 h
    obtain ⟨hD, hOF, -⟩ := hreach a ha
    exact ⟨hOF, hD⟩

end Podc.PPDoubleExpThresholds
