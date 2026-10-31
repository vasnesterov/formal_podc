import Papers.PODC2021.WakeUpMatching.Radio
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Theorem 1.1 in the corner case `Δ = 1`

Dani, Gupta, Hayes, Pettie, PODC 2021 (arXiv:2104.09096v2), Theorem 1.1:
`P(M is a maximal matching and every node used energy ≤ 2C (log n)(log Δ)) ≥ 1 − 1/n²`.

Energy per round (Section 2.3: one unit per send or listen): a recruiter sends and listens
(`2`), plus one send if it matched; an acceptor listens (`1`), plus a send and a listen if it heard
a recruiter (`2`); sleeping and matched nodes spend nothing (`energyRound`).

For `Δ = 1` (a legal parameter: "any upper bound on the maximum degree") the energy bound is
`2C (log n)(log 1) = 0`, but a node can only get matched in a round in which it participates.
So on every graph with an edge, the event of Theorem 1.1 is *empty* for every execution
(`theorem_1_1_delta_one`): the literal statement fails for `Δ = 1`. With the usual convention
`log Δ := max(1, log Δ)` this corner disappears; it does not affect the asymptotic claim
`O((log n)(log Δ))` of the abstract.
-/

set_option linter.unusedSectionVars false

namespace Podc.WakeUpMatching

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Energy spent by `v` in one round (one unit per send or listen timestep). -/
noncomputable def energyRound (partner : V → Option V) (ρ : V → Role) (v : V) : ℕ :=
  if (partner v).isSome then 0
  else match ρ v with
    | .recruit => 2 + if (matchR G partner ρ v).isSome then 1 else 0
    | .accept => 1 + if (hear₁ G partner ρ v).isSome then 2 else 0
    | .sleep => 0

/-- Total energy spent by `v` during the first `t` rounds. -/
noncomputable def energyAfter (ρ : ℕ → V → Role) : ℕ → V → ℕ
  | 0 => fun _ => 0
  | t + 1 => fun v => energyAfter ρ t v + energyRound G (partnerAfter G ρ t) (ρ (t + 1)) v

/-- A node that is matched after `t` rounds has spent at least one unit of energy. -/
theorem one_le_energy_of_matched (ρ : ℕ → V → Role) :
    ∀ t v, (partnerAfter G ρ t v).isSome → 1 ≤ energyAfter G ρ t v := by
  intro t
  induction t with
  | zero => intro v h; simp [partnerAfter] at h
  | succ t ih =>
    intro v h
    simp only [energyAfter]
    by_cases hv : (partnerAfter G ρ t v).isSome
    · have := ih v hv; omega
    · have hround : (round G (partnerAfter G ρ t) (ρ (t + 1)) v).isSome := h
      unfold round at hround
      rw [ite_eq_right_of_eq_false _ _ (eq_false hv)] at hround
      have : 1 ≤ energyRound G (partnerAfter G ρ t) (ρ (t + 1)) v := by
        unfold energyRound
        rw [ite_eq_right_of_eq_false _ _ (eq_false hv)]
        split_ifs at hround with h1 h2 <;> simp_all
      omega

/-- **Theorem 1.1 fails literally for `Δ = 1`.** On any graph with an edge, for any constant
`C`, any `n` and any execution (role choices `ρ`) of `T` rounds, it is impossible that the final
matching is maximal and every node used energy `≤ 2C (log n)(log Δ)` with `Δ = 1`. So the
probability of the event of Theorem 1.1 is `0 < 1 − 1/n²`. -/
theorem theorem_1_1_delta_one {a b : V} (hab : G.Adj a b) (C : ℝ) (n T : ℕ)
    (ρ : ℕ → V → Role) :
    ¬ ((∀ x y, G.Adj x y →
          (partnerAfter G ρ T x).isSome ∨ (partnerAfter G ρ T y).isSome) ∧
        ∀ v, (energyAfter G ρ T v : ℝ) ≤ 2 * C * Real.log n * Real.log (1 : ℕ)) := by
  rintro ⟨hmax, hen⟩
  rcases hmax a b hab with h | h
  · have := one_le_energy_of_matched G ρ T a h
    have h2 := hen a
    simp only [Nat.cast_one, Real.log_one, mul_zero] at h2
    have : (1 : ℝ) ≤ energyAfter G ρ T a := by exact_mod_cast this
    linarith
  · have := one_le_energy_of_matched G ρ T b h
    have h2 := hen b
    simp only [Nat.cast_one, Real.log_one, mul_zero] at h2
    have : (1 : ℝ) ≤ energyAfter G ρ T b := by exact_mod_cast this
    linarith

end Podc.WakeUpMatching
