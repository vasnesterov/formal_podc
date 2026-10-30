import Papers.PODC2023.PPDoubleExpThresholds.MainCode

/-!
# Auxiliary facts for the analysis of `Main`

* `noOF`: only `Main` changes the output flag, and no procedure calls `Main`; hence `OF` is
  constant during every call (`Reach₀.of_eq`).
* `not_canRestart_of`: no `restart` is reachable if none is reachable at the abstract level.
-/

namespace Podc.PPDoubleExpThresholds

open Program

variable {n : ℕ}

/-- The procedures other than `Main` neither set `OF` nor call `Main`. -/
theorem noOF (p : Proc) (hp : p ≠ .main) : ∀ ins ∈ (prog n).code p,
    (∀ b, ins ≠ .setOF b) ∧ ∀ tT tF, ins ≠ .call .main tT tF := by
  cases p with
  | main => exact absurd rfl hp
  | assertEmpty i =>
    by_cases h1 : i ≤ n
    · rw [code_assertEmpty n h1]; simp
    · by_cases h2 : i = n + 1
      · subst h2; rw [code_assertEmpty_last]; simp
      · simp [prog, body, h1, h2, Stmt.body, Stmt.compile]
  | assertProper i =>
    by_cases h : i = 0
    · subst h; rw [code_assertProper_zero]; simp
    · rw [code_assertProper n (by omega)]; simp
  | zero i k => rw [code_zero]; simp
  | incrPair i bx by' => rw [code_incrPair]; simp
  | large i k =>
    by_cases h : i ≤ 1
    · rw [code_large_one n h]; simp
    · rw [code_large n (by omega)]; simp

/-- During a call of a procedure other than `Main`, `OF` does not change. -/
theorem Reach₀.of_eq {C : Reg n → ℕ} {OF : Bool} {σ : List (Proc × ℕ)} {s : Cfg (Reg n) Proc}
    (hσ : ∀ f ∈ σ, f.1 ≠ .main) (h : (prog n).Reach₀ ⟨C, OF, σ⟩ s) :
    s.OF = OF ∧ ∀ f ∈ s.stk, f.1 ≠ .main := by
  have keep : ∀ (p : Proc) (pc pc' : ℕ) (σ' : List (Proc × ℕ)),
      (∀ f ∈ (p, pc) :: σ', f.1 ≠ .main) → ∀ f ∈ (p, pc') :: σ', f.1 ≠ .main := by
    intro p pc pc' σ' h f hf
    simp only [List.mem_cons] at hf
    rcases hf with rfl | hf
    · exact h (p, pc) List.mem_cons_self
    · exact h f (List.mem_cons_of_mem _ hf)
  induction h with
  | refl => exact ⟨rfl, hσ⟩
  | tail _ hst ih =>
    obtain ⟨hOF, hfr⟩ := ih
    cases hst with
    | @setOF C₁ OF₁ p pc σ₁ b h =>
      exact absurd rfl ((noOF _ (hfr (p, pc) List.mem_cons_self) _ (instr_mem h)).1 b)
    | @call C₁ OF₁ p pc σ₁ q tT tF h =>
      refine ⟨hOF, fun f hf => ?_⟩
      simp only [List.mem_cons] at hf
      rcases hf with rfl | hf
      · intro hq; simp only at hq; subst hq
        exact (noOF _ (hfr (p, pc) List.mem_cons_self) _ (instr_mem h)).2 _ _ rfl
      · exact hfr f (by simpa using hf)
    | @ret C₁ OF₁ q pc p pc' σ₁ b q' tT tF h h' =>
      refine ⟨hOF, keep p pc' _ σ₁ (fun f hf => hfr f ?_)⟩
      exact List.mem_cons_of_mem _ hf
    | move => exact ⟨hOF, keep _ _ _ _ hfr⟩
    | swap => exact ⟨hOF, keep _ _ _ _ hfr⟩
    | detectT => exact ⟨hOF, keep _ _ _ _ hfr⟩
    | detectF => exact ⟨hOF, keep _ _ _ _ hfr⟩
    | goto => exact ⟨hOF, keep _ _ _ _ hfr⟩

/-- No procedure other than `Main` calls `Main`. -/
theorem call_ne_main {p q : Proc} {pc tT tF : ℕ} (hp : p ≠ .main)
    (h : (prog n).instr p pc = some (.call q tT tF)) : q ≠ .main := by
  rintro rfl
  exact (noOF _ hp _ (instr_mem h)).2 _ _ rfl

theorem itsCode_ne_main (m a : ℕ) : ∀ ins ∈ itsCode n m a, ∀ tT tF, ins ≠ .call .main tT tF := by
  induction m with
  | zero => simp [itsCode]
  | succ m ih =>
    intro ins hins tT tF
    simp only [itsCode, List.mem_append] at hins
    rcases hins with h | h
    · exact ih ins h tT tF
    · simp [itCode] at h; rcases h with rfl | rfl | rfl | rfl | rfl <;> simp

/-- If all abstract configurations of `Main` reachable from `a₀` have output flag `b`, so do all
configurations reachable from it. -/
theorem main_of_eq {a₀ : Loc (Reg n)} {b : Bool}
    (h : ∀ a, (prog n).AReach .main a₀ a → a.OF = b) :
    ∀ s, (prog n).Reach₀ (atLoc .main a₀) s → s.OF = b := by
  intro s hs
  rcases reach_cases hs with ⟨a, ha, rfl⟩ | ⟨a, q, tT, tF, σ, ha, hcall, -, hreach, -⟩
  · exact h a ha
  · have hq : q ≠ .main := by
      rintro rfl
      -- `Main` never calls itself
      have := instr_mem hcall
      rw [code_main] at this
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil] at this
      rcases this with (h | h) | h
      · simp at h
      · exact itsCode_ne_main n 1 _ h _ _ rfl
      · simp at h
    have := (Reach₀.of_eq (σ := [(q, 0)]) (by simpa using hq) hreach).1
    rw [this]; exact h a ha

/-- No restart is reachable if none is reachable at the abstract level. -/
theorem not_canRestart_of {p : Proc} {a₀ : Loc (Reg n)}
    (h : ∀ a, (prog n).AReach p a₀ a → ¬ (prog n).ARst p a) :
    ¬ (prog n).CanRestart (atLoc p a₀) := by
  rintro ⟨s, hs, p', pc', σ', h1, h2⟩
  rcases reach_cases hs with ⟨a, ha, rfl⟩ | ⟨a, q, tT, tF, σ, ha, hcall, hσ, hreach, hstk⟩
  · simp only [atLoc, List.cons.injEq, Prod.mk.injEq] at h1
    obtain ⟨⟨rfl, rfl⟩, -⟩ := h1
    exact h a ha (.inl h2)
  · refine h a ha (.inr ⟨q, tT, tF, hcall, ⟨_, hreach, p', pc', ?_⟩⟩)
    obtain _ | ⟨f, σ₁⟩ := σ
    · exact absurd rfl hσ
    · rw [hstk] at h1; simp only [List.cons_append, List.cons.injEq] at h1
      exact ⟨σ₁, by simp [h1.1], h2⟩

end Podc.PPDoubleExpThresholds
