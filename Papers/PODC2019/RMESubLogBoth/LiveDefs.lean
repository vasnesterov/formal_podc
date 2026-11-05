import Papers.PODC2019.RMESubLogBoth.Frame

/-!
# Runs, fairness, and a ranking lemma for liveness
-/

namespace Podc.RMESubLogBoth

variable {k : ℕ}

/-- Fairness (conditions (i)–(ii) of Section 1.2): a process that is not idle in the remainder
section later takes a (normal or crash) step. -/
def Fair (r : Run k) : Prop :=
  ∀ p t, (r.cfg t).pc p ≠ .rem → ∃ t', t ≤ t' ∧ (r.ev t' = .step p ∨ r.ev t' = .crash p)

/-- No crash at or after time `T`. -/
def CrashFreeFrom (r : Run k) (T : ℕ) : Prop := ∀ t, T ≤ t → ∀ p, r.ev t ≠ .crash p

/-- Finitely many crashes. -/
def FinCrash (r : Run k) : Prop := ∃ T, CrashFreeFrom r T

/-- The Try section (including the recovery code, which the algorithm runs in Try). -/
def PC.InTry : PC k → Prop
  | .rem | .cs _ | .l28 _ | .l29 => False
  | _ => True

/-- A generic ranking argument: if from time `T` on, until `Goal` holds, the rank `μ` never
increases, and every event of the process `d` (which is not idle) strictly decreases it, then
`Goal` eventually holds. The process `d` may depend on the time but must stay the same while the
rank does not change. -/
lemma eventually_of_rank (r : Run k) (hF : Fair r) (μ : ℕ → ℕ) (Goal : ℕ → Prop)
    (d : ℕ → Fin k) (T : ℕ)
    (hmono : ∀ t, T ≤ t → ¬ Goal t → ¬ Goal (t + 1) → μ (t + 1) ≤ μ t)
    (hd : ∀ t, T ≤ t → ¬ Goal t → (r.cfg t).pc (d t) ≠ .rem)
    (hdstep : ∀ t, T ≤ t → ¬ Goal t → (r.ev t = .step (d t) ∨ r.ev t = .crash (d t)) →
      ¬ Goal (t + 1) → μ (t + 1) < μ t)
    (hdsame : ∀ t, T ≤ t → ¬ Goal t → ¬ Goal (t + 1) → μ (t + 1) = μ t → d (t + 1) = d t) :
    ∃ t, T ≤ t ∧ Goal t := by
  by_contra hno
  push_neg at hno
  -- strong induction on the rank
  have key : ∀ n, ∀ t, T ≤ t → μ t ≤ n → False := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro t ht hμ
      obtain ⟨t', htt', hev⟩ := hF (d t) t (hd t ht (hno t ht))
      -- either the rank drops before `t'`, or `d` stays the driver until `t'`
      have : ∀ s, t ≤ s → s ≤ t' → μ s < μ t ∨ (μ s = μ t ∧ d s = d t) := by
        intro s hs hs'
        induction s, hs using Nat.le_induction with
        | base => exact .inr ⟨rfl, rfl⟩
        | succ s hs ihs =>
          rcases ihs (by omega) with h | ⟨h1, h2⟩
          · exact .inl (lt_of_le_of_lt (hmono s (by omega) (hno s (by omega))
              (hno (s + 1) (by omega))) h)
          · have hle := hmono s (by omega) (hno s (by omega)) (hno (s + 1) (by omega))
            rcases lt_or_eq_of_le hle with h3 | h3
            · exact .inl (h3.trans_eq h1)
            · exact .inr ⟨h3.trans h1, (hdsame s (by omega) (hno s (by omega))
                (hno (s + 1) (by omega)) h3).trans h2⟩
      rcases this t' htt' le_rfl with h | ⟨h1, h2⟩
      · exact ih (μ t') (by omega) t' (by omega) le_rfl
      · have h3 := hdstep t' (by omega) (hno t' (by omega)) (h2 ▸ hev) (hno (t' + 1) (by omega))
        exact ih (μ (t' + 1)) (by omega) (t' + 1) (by omega) le_rfl
  exact key (μ T) T le_rfl le_rfl

end Podc.RMESubLogBoth
