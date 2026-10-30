import Papers.PODC2023.PPDoubleExpThresholds.MainSteps

/-!
# Callees of `Main` on proper configurations, and the steps of `Main` they allow
-/

namespace Podc.PPDoubleExpThresholds

open Program

variable {n : ℕ}

section proper

variable {j : ℕ} (hj : 1 ≤ j) (hjn : j ≤ n) {D : Reg n → ℕ} (OF : Bool)
include hj hjn

/-- `Large(x̄ⱼ)`, `Large(ȳⱼ)` on `j`-proper configurations have no effect. -/
theorem large_proper (hD : Proper D j) (k : Fin 4) (hk : k = 1 ∨ k = 3) (b : Bool) :
    (prog n).Returns (.large j k) D OF D OF b ∧
      ∀ D' OF' b', (prog n).Returns (.large j k) D OF D' OF' b' → D' = D ∧ OF' = OF := by
  have hB := ((levels j hj hjn).largeB k D OF (hD.mono (by omega))).1
  have hw := hD.wproper hj
  obtain ⟨-, e0, e1, e2, e3⟩ := (proper_succ_iff hj).1 hD
  have hk' : N j ≤ D (reg n j k) := by rcases hk with rfl | rfl <;> omega
  have hlg := lg_eq_self hj hjn k hw hk'
  refine ⟨(hB _ _ _).2 ⟨rfl, ?_⟩, fun D' OF' b' h => ?_⟩
  · cases b
    · exact .inl ⟨rfl, rfl⟩
    · exact .inr ⟨rfl, hk', hlg.symm⟩
  · obtain ⟨rfl, ⟨-, rfl⟩ | ⟨-, -, rfl⟩⟩ := (hB _ _ _).1 h
    · exact ⟨rfl, rfl⟩
    · exact ⟨hlg, rfl⟩

/-- `AssertProper(j)` on `j`-proper configurations has no effect. -/
theorem ap_proper (hD : Proper D j ∨ Low D j) :
    (prog n).Returns (.assertProper j) D OF D OF false ∧
      (∀ D' OF' b', (prog n).Returns (.assertProper j) D OF D' OF' b' → D' = D ∧ OF' = OF) ∧
      ¬ (prog n).Restarts (.assertProper j) D OF ∧ (prog n).Terminates (.assertProper j) D OF := by
  obtain ⟨hR, h2, h3⟩ := (levels j hj hjn).apA D OF hD
  exact ⟨(hR _ _ _).2 ⟨rfl, rfl, rfl⟩, fun D' OF' b' h => by
    obtain ⟨h1, h2, -⟩ := (hR _ _ _).1 h; exact ⟨h2, h1⟩, h2, h3⟩

/-- `AssertEmpty(j + 1)` never changes the registers and may always return. -/
theorem ae_facts :
    (prog n).Returns (.assertEmpty (j + 1)) D OF D OF false ∧
      (∀ D' OF' b', (prog n).Returns (.assertEmpty (j + 1)) D OF D' OF' b' → D' = D ∧ OF' = OF) ∧
      ((prog n).Restarts (.assertEmpty (j + 1)) D OF ↔ ¬ Empty D (j + 1)) ∧
      (prog n).Terminates (.assertEmpty (j + 1)) D OF := by
  obtain ⟨hR, h2, h3⟩ := lemma_8 (j + 1) (by omega) (by omega) D OF
  exact ⟨(hR _ _ _).2 ⟨rfl, rfl, rfl⟩, fun D' OF' b' h => by
    obtain ⟨h1, h2, -⟩ := (hR _ _ _).1 h; exact ⟨h1, h2⟩, h2, h3⟩

/-- Steps of `Main` through a loop whose level is proper. -/
theorem steps_proper (hD : Proper D j) :
    (prog n).AStep .main ⟨5 * j - 4, D, OF⟩ ⟨5 * j - 3, D, OF⟩ ∧
    (prog n).AStep .main ⟨5 * j - 3, D, OF⟩ ⟨5 * j + 1, D, OF⟩ ∧
    (prog n).AStep .main ⟨5 * j - 2, D, OF⟩ ⟨5 * j - 1, D, OF⟩ ∧
    (prog n).AStep .main ⟨5 * j - 1, D, OF⟩ ⟨5 * j, D, OF⟩ ∧
    (prog n).AStep .main ⟨5 * j, D, OF⟩ ⟨5 * j - 4, D, OF⟩ :=
  ⟨.call (instr_it0 hj hjn) (large_proper hj hjn OF hD 1 (.inl rfl) true).1,
   .call (instr_it1 hj hjn) (large_proper hj hjn OF hD 3 (.inr rfl) true).1,
   .call (instr_it2 hj hjn) (ap_proper hj hjn OF (.inl hD)).1,
   .call (instr_it3 hj hjn) (ae_facts hj hjn OF).1,
   .goto (instr_it4 hj hjn)⟩

/-- Through a loop whose level is proper, from any of its positions to the next loop. -/
theorem through_proper (hD : Proper D j) {r : ℕ} (hr : r < 5) :
    (prog n).AReach .main ⟨5 * j - 4 + r, D, OF⟩ ⟨5 * j + 1, D, OF⟩ := by
  obtain ⟨s0, s1, s2, s3, s4⟩ := steps_proper hj hjn OF hD
  have p0 : (prog n).AReach .main ⟨5 * j - 4, D, OF⟩ ⟨5 * j + 1, D, OF⟩ := .head s0 (.single s1)
  interval_cases r
  · simpa using p0
  · rw [show 5 * j - 4 + 1 = 5 * j - 3 by omega]; exact .single s1
  · rw [show 5 * j - 4 + 2 = 5 * j - 2 by omega]; exact .head s2 (.head s3 (.head s4 p0))
  · rw [show 5 * j - 4 + 3 = 5 * j - 1 by omega]; exact .head s3 (.head s4 p0)
  · rw [show 5 * j - 4 + 4 = 5 * j by omega]; exact .head s4 p0

end proper

/-- From the loop of level `j` to the loop of level `J` (or to the end of the loops when
`J = n + 1`), through proper levels. -/
theorem through_propers {D : Reg n → ℕ} (OF : Bool) {J : ℕ} (hJ : J ≤ n + 1)
    (hD : Proper D (J - 1)) : ∀ j, 1 ≤ j → j < J → ∀ r, r < 5 →
      (prog n).AReach .main ⟨5 * j - 4 + r, D, OF⟩ ⟨5 * J - 4, D, OF⟩ := by
  intro j hj hjJ
  induction h : J - j generalizing j with
  | zero => omega
  | succ d ih =>
    intro r hr
    have p := through_proper hj (by omega) OF (hD.mono (by omega)) hr
    rcases Nat.eq_or_lt_of_le (show j + 1 ≤ J by omega) with h' | h'
    · rw [show 5 * J - 4 = 5 * j + 1 by omega]; exact p
    · have := ih (j + 1) (by omega) h' (by omega) 0 (by omega)
      rw [show 5 * (j + 1) - 4 + 0 = 5 * j + 1 by omega] at this
      exact p.trans this

end Podc.PPDoubleExpThresholds
