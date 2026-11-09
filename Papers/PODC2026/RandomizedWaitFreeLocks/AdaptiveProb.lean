import Mathlib

/-!
# Finite-horizon probabilities against a full-information (weak adaptive) adversary

A system with states `S`, adversary actions `A` and a transition `step : S → A → Bool → S`
that also takes the outcome of one biased coin; `π s a` is the probability that this coin is
`true` when the adversary chooses `a` in state `s`.  The adversary `σ` chooses the next action
as a function of the whole history of states (it sees everything that happened so far, but not
the coin of the step it schedules: a *weak adaptive* adversary).

`prob step π σ E n h s` is the probability that after `n` further steps from `s` (history `h`)
the state satisfies `E`.  For a monotone event (once true, true forever) this is the
probability that `E` happens within `n` steps; a bound for every `n` is a bound for the
infinite execution.

`prob_le_of_super`: a bounded *supersolution* `V` (`V ≥ 1` on `E`, `V ≥ 0`, and every action
does not increase the expectation of `V`) bounds the probability, for every adversary and
every horizon.  This is the "potential function" form of an optional-stopping argument.
-/

namespace Podc.RandomizedWaitFreeLocks

variable {S A : Type*}

open Classical in
/-- Probability that `E` holds after `n` steps, adversary `σ`, history `h`, current state `s`. -/
noncomputable def prob (step : S → A → Bool → S) (π : S → A → ℝ) (σ : List S → A)
    (E : S → Prop) : ℕ → List S → S → ℝ
  | 0, _, s => if E s then 1 else 0
  | n + 1, h, s =>
    π s (σ (h ++ [s])) * prob step π σ E n (h ++ [s]) (step s (σ (h ++ [s])) true) +
      (1 - π s (σ (h ++ [s]))) * prob step π σ E n (h ++ [s]) (step s (σ (h ++ [s])) false)

/-- **Supersolution bound** (CSLib candidate). -/
theorem prob_le_of_super (step : S → A → Bool → S) (π : S → A → ℝ) (E : S → Prop)
    (I : S → Prop) (V : S → ℝ)
    (hI : ∀ s a b, I s → I (step s a b))
    (hπ : ∀ s a, I s → 0 ≤ π s a ∧ π s a ≤ 1)
    (hE : ∀ s, I s → E s → 1 ≤ V s) (hV : ∀ s, I s → 0 ≤ V s)
    (hsup : ∀ s a, I s → π s a * V (step s a true) + (1 - π s a) * V (step s a false) ≤ V s)
    (σ : List S → A) : ∀ n h s, I s → prob step π σ E n h s ≤ V s := by
  intro n
  induction n with
  | zero =>
    intro h s hs
    simp only [prob]
    split_ifs with he
    · exact hE s hs he
    · exact hV s hs
  | succ n ih =>
    intro h s hs
    simp only [prob]
    set a := σ (h ++ [s])
    obtain ⟨h0, h1⟩ := hπ s a hs
    have e1 := ih (h ++ [s]) _ (hI s a true hs)
    have e2 := ih (h ++ [s]) _ (hI s a false hs)
    calc π s a * prob step π σ E n (h ++ [s]) (step s a true) +
          (1 - π s a) * prob step π σ E n (h ++ [s]) (step s a false)
        ≤ π s a * V (step s a true) + (1 - π s a) * V (step s a false) := by
          gcongr
      _ ≤ V s := hsup s a hs

end Podc.RandomizedWaitFreeLocks
