import Papers.PODC2026.EarlyStabilizingCounting.Algorithm

/-!
# Corollary 5.8: early-stabilizing counting in `O(f + 1 + log n)` rounds

Applying Algorithm 1 recursively with a balanced partition and the trivial single-node counter as
base case gives, for every `n ≥ 1` and `C ≥ 1`, a deterministic `C`-counter on `n` nodes in the
self-stabilising Byzantine model that, in every execution with `f` faulty nodes, `3 f < n`,
stabilizes within `120 f + 113 ⌈log₂ n⌉` rounds (`corollary_5_8`).

The bound depends on the actual number `f` of faults, not on the resilience `t` (early
stabilization). The recursion uses a part `b` with `3 f_b < |V_b|` and `2 f_b ≤ f`, which always
exists for the balanced partition (`exists_good_side`); the paper's proof only says "either `V₀`
or `V₁` contains at most half of the faulty nodes", which by itself does not give `3 f_b < |V_b|`.
-/

set_option linter.unusedSectionVars false

namespace EarlyStabilizingCounting

open Finset Cslib.Byzantine.SyncCounting

/-- The trivial single-node counter (base case). -/
def baseAlg (C : ℕ) [NeZero C] : Algorithm (Fin 1) ℕ C where
  g i m := m i + 1
  h _ s := ⟨s % C, Nat.mod_lt _ (NeZero.pos C)⟩

theorem baseAlg_isES (C : ℕ) [NeZero C] : IsESCounter (baseAlg C) (fun _ => 0) := by
  intro F hF x hx
  have hF0 : F = ∅ := by
    rw [← card_eq_zero]; omega
  subst hF0
  have hstep : ∀ t, x t 0 = x 0 0 + t := by
    intro t
    induction t with
    | zero => rfl
    | succ t ih =>
      obtain ⟨m, hm, h⟩ := hx t 0 (by simp)
      rw [h, show (baseAlg C).g 0 m = m 0 + 1 from rfl, hm 0 (by simp), ih]; ring
  refine ⟨x 0 0, fun r i _ => ?_⟩
  rw [Fin.fin_one_eq_zero i]
  show x (0 + r) 0 % C = _
  rw [Nat.zero_add, hstep]

/-- For the balanced partition one of the parts has fewer than a third faulty nodes and at most
half of all faulty nodes. -/
theorem exists_good_side {n f₀ f₁ : ℕ} (h : 3 * (f₀ + f₁) < n) :
    (3 * f₀ < n / 2 ∧ 2 * f₀ ≤ f₀ + f₁) ∨ (3 * f₁ < n - n / 2 ∧ 2 * f₁ ≤ f₀ + f₁) := by
  omega

/-- Corollary 5.8 (stabilization time): for all `n ≥ 1` and `C ≥ 1` there is a deterministic
`C`-counting algorithm on `n` nodes that, in every execution with `f` Byzantine nodes, `3f < n`,
and arbitrary initial states, stabilizes within `120 f + 113 ⌈log₂ n⌉` rounds. -/
theorem corollary_5_8 (n C : ℕ) (hn : 1 ≤ n) (hC : 1 ≤ C) :
    ∃ (X : Type) (_ : Nonempty X) (A : Algorithm (Fin n) X C),
      IsESCounter A (fun f => 120 * f + 113 * Nat.clog 2 n) := by
  induction n using Nat.strong_induction_on generalizing C with
  | _ n ih =>
    have : NeZero C := ⟨by omega⟩
    rcases Nat.lt_or_ge n 2 with h1 | h2
    · obtain rfl : n = 1 := by omega
      refine ⟨ℕ, inferInstance, baseAlg C, fun F hF x hx => ?_⟩
      exact (baseAlg_isES C F hF x hx).mono (Nat.zero_le _)
    · obtain ⟨X₀, hX₀, A₀, hA₀⟩ := ih (n / 2) (by omega) (kk Dk false * n) (by omega)
        (by simp [kk, Dk]; omega)
      obtain ⟨X₁, hX₁, A₁, hA₁⟩ := ih (n - n / 2) (by omega) (kk Dk true * n) (by omega)
        (by simp [kk, Dk]; omega)
      refine ⟨LS n × X₀ × X₁, inferInstance, tmpl 2 C A₀ A₁, fun F hF x hx => ?_⟩
      have hlog : Nat.clog 2 n = Nat.clog 2 (n - n / 2) + 1 := by
        rw [Nat.clog_of_two_le (by norm_num) h2]
        congr 2; omega
      have hlog₀ : Nat.clog 2 (n / 2) ≤ Nat.clog 2 (n - n / 2) :=
        Nat.clog_mono_right 2 (by omega)
      have hsum := card_F₀_add_F₁ F
      obtain ⟨h₀, h₁⟩ := theorem_5_7 hA₀ hA₁ F hF x hx
      rcases exists_good_side (n := n) (f₀ := (F₀ F).card) (f₁ := (F₁ F).card)
        (by rw [hsum]; exact hF) with ⟨g1, g2⟩ | ⟨g1, g2⟩
      · refine (h₀ g1).mono ?_
        rw [hsum] at g2
        nlinarith
      · refine (h₁ g1).mono ?_
        rw [hsum] at g2
        nlinarith

end EarlyStabilizingCounting
