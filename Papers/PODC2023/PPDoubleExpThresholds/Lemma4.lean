import Papers.PODC2023.PPDoubleExpThresholds.MainFacts

/-!
# Lemma 4: `Main`

For a register configuration `C`, `Main` started on `C`
* (a) may stabilise to `false` if `C` is `j`-low and `(j+1)`-empty;
* (b) may stabilise to `true` if `C` is `n`-proper;
* (c) always restarts otherwise.

"May stabilise to `b`": some configuration reachable without restarting cannot restart any more, and
from every configuration (reachable without restarting) that cannot restart one reaches a
configuration all of whose successors have `OF = b`. "Always restarts": a `restart` is reachable
from every configuration reachable without restarting.
-/

namespace Podc.PPDoubleExpThresholds

open Program

variable {n : ℕ}

/-- `omega` after reducing structure projections. -/
local macro "om" : tactic => `(tactic| ((try dsimp only at *) <;> omega))

/-- `AssertProper(n)` on `n`-proper configurations (also for `n = 0`). -/
theorem apn_facts {D : Reg n → ℕ} (OF : Bool) (hD : Proper D n) :
    (prog n).Returns (.assertProper n) D OF D OF false ∧
      (∀ D' OF' b', (prog n).Returns (.assertProper n) D OF D' OF' b' → D' = D ∧ OF' = OF) ∧
      ¬ (prog n).Restarts (.assertProper n) D OF ∧ (prog n).Terminates (.assertProper n) D OF := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · obtain ⟨hR, h2, h3⟩ := ap_zero D OF
    exact ⟨(hR _ _ _).2 ⟨rfl, rfl, rfl⟩, fun D' OF' b' h => by
      obtain ⟨h1, h2, -⟩ := (hR _ _ _).1 h; exact ⟨h2, h1⟩, h2, h3⟩
  · exact ap_proper hn le_rfl OF (.inl hD)

/-- A configuration of `Main` on `C` is `b`-stable if all its successors have `OF = b`. -/
theorem stable_of_trap {C : Reg n → ℕ} {b : Bool} {a₀ : Loc (Reg n)}
    (h : ∀ a, (prog n).AReach .main a₀ a → a.OF = b) :
    ∀ s, (prog n).Reach₀ (atLoc .main a₀) s → s.OF = b := main_of_eq h

/-- **Lemma 4(b)**: on an `n`-proper configuration, `Main` may stabilise to `true`. -/
theorem lemma_4b {C : Reg n → ℕ} (hC : Proper C n) (OF₀ : Bool) :
    (∃ s, (prog n).Reach₀ ((prog n).init C OF₀) s ∧ ¬ (prog n).CanRestart s) ∧
    ∀ s, (prog n).Reach₀ ((prog n).init C OF₀) s → ¬ (prog n).CanRestart s →
      ∃ s', (prog n).Reach₀ s s' ∧ ∀ s'', (prog n).Reach₀ s' s'' → s''.OF = true := by
  have hinit : (prog n).init C OF₀ = atLoc .main ⟨0, C, OF₀⟩ := rfl
  rw [hinit]
  set T : Loc (Reg n) := ⟨5 * n + 2, C, true⟩
  have hAP := apn_facts true hC
  -- the final loop is a trap
  have htrap : ∀ a, (prog n).AReach .main T a →
      a.C = C ∧ a.OF = true ∧ (a.pc = 5 * n + 2 ∨ a.pc = 5 * n + 3 ∨ a.pc = 5 * n + 4) := by
    intro a ha
    refine AReach.inv (I := fun a => a.C = C ∧ a.OF = true ∧
      (a.pc = 5 * n + 2 ∨ a.pc = 5 * n + 3 ∨ a.pc = 5 * n + 4)) ?_ ha ⟨rfl, rfl, .inl rfl⟩
    rintro ⟨pc, D, OF⟩ a' ⟨rfl, rfl, hpc⟩ hs
    rcases main_astep hs with ⟨rfl, -⟩ | ⟨j, -, hjn, h⟩ | ⟨rfl, -⟩ | ⟨rfl, rfl⟩ | ⟨rfl, D', OF', b, hr, rfl⟩ |
        ⟨rfl, rfl⟩
    · simp at hpc
    · exfalso; rcases h with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> simp at hpc <;> om
    · simp at hpc
    · exact ⟨rfl, rfl, .inr (.inl rfl)⟩
    · obtain ⟨rfl, rfl⟩ := hAP.2.1 _ _ _ hr
      exact ⟨rfl, rfl, .inr (.inr rfl)⟩
    · exact ⟨rfl, rfl, .inl rfl⟩
  have hTnr : ¬ (prog n).CanRestart (atLoc .main T) := by
    refine not_canRestart_of fun a ha => ?_
    obtain ⟨hC', hOF, hpc⟩ := htrap a ha
    rintro (h | ⟨q, tT, tF, hq, hr⟩)
    · rcases hpc with h' | h' | h' <;> rw [h'] at h
      · rw [instr_fin1] at h; simp at h
      · rw [instr_fin2] at h; simp at h
      · rw [instr_fin3] at h; simp at h
    · rcases hpc with h' | h' | h' <;> rw [h'] at hq
      · rw [instr_fin1] at hq; (try simp at hq)
      · rw [instr_fin2] at hq; simp at hq
        obtain ⟨rfl, -, -⟩ := hq
        rw [hC', hOF] at hr; exact hAP.2.2.1 hr
      · rw [instr_fin3] at hq; (try simp at hq)
  -- the invariant of `Main` on `C`
  let I : Loc (Reg n) → Prop := fun a => a.C = C ∧ (a.pc = 0 ∨ (1 ≤ a.pc ∧ a.pc ≤ 5 * n + 1 ∧
    a.OF = false) ∨ (5 * n + 2 ≤ a.pc ∧ a.pc ≤ 5 * n + 4 ∧ a.OF = true))
  have hI : ∀ a a', I a → (prog n).AStep .main a a' → I a' := by
    rintro ⟨pc, D, OF⟩ a' ⟨rfl, hpc⟩ hs
    rcases main_astep hs with ⟨rfl, rfl⟩ | ⟨j, hj, hjn, h⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
        ⟨rfl, D', OF', b, hr, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨rfl, .inr (.inl ⟨le_rfl, by om, rfl⟩)⟩
    · have hP : Proper D j := hC.mono hjn
      rcases h with ⟨rfl, D', OF', b, hr, rfl⟩ | ⟨rfl, D', OF', b, hr, rfl⟩ |
          ⟨rfl, D', OF', b, hr, rfl⟩ | ⟨rfl, D', OF', b, hr, rfl⟩ | ⟨rfl, rfl⟩
      · obtain ⟨rfl, rfl⟩ := (large_proper hj hjn OF hP 1 (.inl rfl) true).2 _ _ _ hr
        exact ⟨rfl, .inr (.inl ⟨by cases b <;> simp <;> om, by cases b <;> simp <;> om,
          by rcases hpc with h | ⟨h1, h2, h⟩ | ⟨h1, h2, h⟩ <;> first | exact h | om⟩)⟩
      · obtain ⟨rfl, rfl⟩ := (large_proper hj hjn OF hP 3 (.inr rfl) true).2 _ _ _ hr
        exact ⟨rfl, .inr (.inl ⟨by cases b <;> simp <;> om, by cases b <;> simp <;> om,
          by rcases hpc with h | ⟨h1, h2, h⟩ | ⟨h1, h2, h⟩ <;> first | exact h | om⟩)⟩
      · obtain ⟨rfl, rfl⟩ := (ap_proper hj hjn OF (.inl hP)).2.1 _ _ _ hr
        exact ⟨rfl, .inr (.inl ⟨by om, by om, by rcases hpc with h | ⟨h1, h2, h⟩ | ⟨h1, h2, h⟩ <;> first | exact h | om⟩)⟩
      · obtain ⟨rfl, rfl⟩ := (ae_facts hj hjn OF).2.1 _ _ _ hr
        exact ⟨rfl, .inr (.inl ⟨by om, by om, by rcases hpc with h | ⟨h1, h2, h⟩ | ⟨h1, h2, h⟩ <;> first | exact h | om⟩)⟩
      · exact ⟨rfl, .inr (.inl ⟨by om, by om, by rcases hpc with h | ⟨h1, h2, h⟩ | ⟨h1, h2, h⟩ <;> first | exact h | om⟩)⟩
    · exact ⟨rfl, .inr (.inr ⟨le_rfl, by om, rfl⟩)⟩
    · exact ⟨rfl, .inr (.inr ⟨by om, by om, by rcases hpc with h | ⟨h1, h2, h⟩ | ⟨h1, h2, h⟩ <;> first | exact h | om⟩)⟩
    · obtain ⟨rfl, rfl⟩ := (apn_facts OF hC).2.1 _ _ _ hr
      exact ⟨rfl, .inr (.inr ⟨by om, le_rfl, by rcases hpc with h | ⟨h1, h2, h⟩ | ⟨h1, h2, h⟩ <;> first | exact h | om⟩)⟩
    · exact ⟨rfl, .inr (.inr ⟨le_rfl, by om, by rcases hpc with h | ⟨h1, h2, h⟩ | ⟨h1, h2, h⟩ <;> first | exact h | om⟩)⟩
  have hreach : ∀ a, (prog n).AReach .main ⟨0, C, OF₀⟩ a → I a :=
    fun a ha => AReach.inv hI ha ⟨rfl, .inl rfl⟩
  -- from every abstract configuration, the final loop
  have toT : ∀ a, I a → (prog n).AReach .main a T := by
    rintro ⟨pc, D, OF⟩ ⟨rfl, hpc⟩
    have last : ∀ OF, (prog n).AReach .main ⟨5 * n + 1, D, OF⟩ T :=
      fun OF => .single (.setOF instr_fin0)
    have fromIt : ∀ OF, ∀ j r, 1 ≤ j → j ≤ n → r < 5 →
        (prog n).AReach .main ⟨5 * j - 4 + r, D, OF⟩ T := fun OF j r hj hjn hr => by
      have := through_propers OF (J := n + 1) le_rfl (by simpa using hC) j hj (by om) r hr
      rw [show 5 * (n + 1) - 4 = 5 * n + 1 by om] at this
      exact this.trans (last OF)
    rcases hpc with rfl | ⟨h1, h2, rfl⟩ | ⟨h1, h2, rfl⟩
    · refine .head (.setOF (instr_main_zero n)) ?_
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · exact last false
      · simpa using fromIt false 1 0 le_rfl hn (by om)
    · rcases Nat.lt_or_ge pc (5 * n + 1) with h | h
      · obtain ⟨j, r, hj, hjn, hr, rfl⟩ : ∃ j r, 1 ≤ j ∧ j ≤ n ∧ r < 5 ∧ pc = 5 * j - 4 + r :=
          ⟨(pc + 4) / 5, (pc + 4) % 5, by om, by om, by om, by om⟩
        exact fromIt false j r hj hjn hr
      · obtain rfl : pc = 5 * n + 1 := by om
        exact last false
    · rcases (show pc = 5 * n + 2 ∨ pc = 5 * n + 3 ∨ pc = 5 * n + 4 by om) with rfl | rfl | rfl
      · exact .refl
      · exact .head (.call instr_fin2 hAP.1) (.single (.goto instr_fin3))
      · exact .single (.goto instr_fin3)
  refine ⟨⟨atLoc .main T, (toT _ ⟨rfl, .inl rfl⟩).reach₀ [], hTnr⟩, fun s hs hns => ?_⟩
  -- every call made by `Main` on `C` terminates
  have hterm : ∀ a, (prog n).AReach .main ⟨0, C, OF₀⟩ a → ∀ q tT tF,
      (prog n).instr .main a.pc = some (.call q tT tF) → (prog n).Terminates q a.C a.OF := by
    intro a ha q tT tF hq
    obtain ⟨hC', -⟩ := hreach a ha
    obtain ⟨pc, D, OF⟩ := a
    simp only at hC' hq ⊢; subst hC'
    rcases main_pc_cases (n := n) pc with rfl | ⟨j, r, hj, hjn, hr, rfl⟩ | h
    · rw [instr_main_zero n] at hq; simp at hq
    · have hP : Proper D j := hC.mono hjn
      interval_cases r
      · rw [Nat.add_zero, instr_it0 hj hjn] at hq; simp at hq; obtain ⟨rfl, -⟩ := hq
        exact ((levels j hj hjn).largeB 1 D OF (hP.mono (by om))).2.2
      · rw [show 5 * j - 4 + 1 = 5 * j - 3 by om, instr_it1 hj hjn] at hq; simp at hq
        obtain ⟨rfl, -⟩ := hq
        exact ((levels j hj hjn).largeB 3 D OF (hP.mono (by om))).2.2
      · rw [show 5 * j - 4 + 2 = 5 * j - 2 by om, instr_it2 hj hjn] at hq; simp at hq
        obtain ⟨rfl, -⟩ := hq
        exact (ap_proper hj hjn OF (.inl hP)).2.2.2
      · rw [show 5 * j - 4 + 3 = 5 * j - 1 by om, instr_it3 hj hjn] at hq; simp at hq
        obtain ⟨rfl, -⟩ := hq
        exact (ae_facts hj hjn OF).2.2.2
      · rw [show 5 * j - 4 + 4 = 5 * j by om, instr_it4 hj hjn] at hq; simp at hq
    · obtain ⟨r, rfl⟩ : ∃ r, pc = 5 * n + 1 + r := ⟨pc - (5 * n + 1), by om⟩
      rcases Nat.lt_or_ge r 5 with hr | hr
      · interval_cases r
        · rw [Nat.add_zero, instr_fin0] at hq; (try simp at hq)
        · rw [show 5 * n + 1 + 1 = 5 * n + 2 by om, instr_fin1] at hq; (try simp at hq)
        · rw [show 5 * n + 1 + 2 = 5 * n + 3 by om, instr_fin2] at hq; simp at hq
          obtain ⟨rfl, -⟩ := hq
          exact (apn_facts OF hC).2.2.2
        · rw [show 5 * n + 1 + 3 = 5 * n + 4 by om, instr_fin3] at hq; (try simp at hq)
        · rw [show 5 * n + 1 + 4 = 5 * n + 5 by om, instr_fin4] at hq; (try simp at hq)
      · rw [instr_main_none n (by om)] at hq; simp at hq
  obtain ⟨s', hs', hG⟩ := agef (prog := prog n) (p := .main) (a₀ := ⟨0, C, OF₀⟩)
    (G := fun s => (prog n).AtRestart s ∨ s = atLoc .main T) (fun s h => .inl h) hterm
    (fun a ha => ⟨_, (toT a (hreach a ha)).reach₀ [], .inr rfl⟩) s hs
  rcases hG with h | rfl
  · exact absurd ⟨s', hs', h⟩ hns
  · refine ⟨_, hs', fun s'' h'' => main_of_eq (fun a ha => (htrap a ha).2.1) s'' h''⟩

end Podc.PPDoubleExpThresholds
