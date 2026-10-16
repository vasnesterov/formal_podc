import Papers.PODC2021.GoodCaseLatencyBB.UnsyncRuns

/-!
# Claim 1 of the proof of Theorem 10

`g` cannot distinguish Execution 1 from Execution 2 before time `Δ + 1.5δ`: in the physical
execution `X` and in the world `W`, `g` has the same states up to time `Δ + 3e − 1` and `A` up to
time `Δ + e − 1` (and `C`, shifted by its late start, up to local time `2e − 1`; `h` is quiet up
to time `2e − 1` in both).
-/

set_option linter.unusedSectionVars false

namespace GoodCaseLatencyBB.Thm10

open Cslib.Byzantine.PartialSync Finset

variable {P M S V K : Type*} [DecidableEq P] [Fintype P]
variable {A : Algorithm P M S V V} {s : P} {v0 : V} {Δ e L : ℕ}

/-- Deadlines for the comparison in `claim1`. -/
private def claim1T (Δ e : ℕ) (lab : P → ℕ) (p : P) : ℕ :=
  if lab p = 0 then Δ + 3 * e - 1 else if lab p = 1 then Δ + e - 1
  else if lab p = 3 then 3 * e - 1 else 2 * e - 1

private theorem DX_pos (he : 1 ≤ e) (hΔ : 2 * e < Δ) (hL : L = Δ + 3 * e) (i j : ℕ) :
    1 ≤ DX Δ e L i j := by
  unfold DX; split_ifs <;> omega

private theorem DW_pos (he : 1 ≤ e) (hΔ : 2 * e < Δ) (hL : L = Δ + 3 * e) (i j : ℕ) :
    1 ≤ DW Δ e L i j := by
  unfold DW; split_ifs <;> omega

theorem claim1 {lab lab' : P → ℕ} (hl : Labels s lab lab') (he : 1 ≤ e) (hΔ : 2 * e < Δ)
    (hL : L = Δ + 3 * e) (va vb : V) :
    ∀ p τ, (lab p = 0 ∧ τ ≤ Δ + 3 * e - 1) ∨ (lab p = 1 ∧ τ ≤ Δ + e - 1) →
      (X A s v0 Δ e L lab lab' va vb).st (lateStart A) τ p =
        (W s v0 Δ e L va lab).st (lateStart A) τ p := by
  set R := X A s v0 Δ e L lab lab' va vb with hR
  set R' := W s v0 Δ e L va lab with hR'
  have hfX : ∀ q, q ∈ R.faulty ↔ lab q = 2 := fun q => by simp [hR, X]
  have hfW : ∀ q, q ∉ R'.faulty := fun q => by simp [hR', W]
  have key := Run.st_shift_eq (lateStart A) R R' (X := {p | lab p ≠ 2}) (off lab e)
    (fun _ => 0) (claim1T Δ e lab) ?h0 ?hin
  · intro p τ hp
    have h3 : lab p ≠ 3 := by omega
    have : off lab e p = 0 := by simp [off, h3]
    have h := key τ p (by change lab p ≠ 2; omega) (by omega)
      (by simp only [claim1T]; split_ifs <;> omega)
    simpa [this] using h
  case h0 =>
    intro p hp _
    have hp' : lab p ≠ 2 := hp
    have hps : p ≠ s := fun h => hp' (h ▸ hl.bc)
    by_cases h3 : lab p = 3
    · have hu : ustart R p = e := by simp [ustart, hR, X, h3]
      have := lateStart_st_start (A := A) (R := R) p
      rw [hu] at this
      simp only [off, h3, ite_true]
      rw [this]
      simp [hR, hR', X, W, lateStart, hps]
    · simp [off, h3, hR, hR', X, W, lateStart, hps]
  case hin =>
    intro τ ih p hp hop hpT
    have hp' : lab p ≠ 2 := hp
    -- correct senders
    have outEq : ∀ q t t', lab q ≠ 2 → off lab e q ≤ t → t ≤ claim1T Δ e lab q → t ≤ τ →
        t' = t - off lab e q → R.out (lateStart A) q t p = R'.out (lateStart A) q t' p := by
      intro q t t' hq h1 h2 h3 h4
      rw [Run.out_of_correct _ _ (by rw [hfX]; exact hq), Run.out_of_correct _ _ (hfW q),
        ih q hq t h3 h1 h2, h4, Nat.add_zero]
    have outPre : ∀ q t, lab q = 3 → t < e → R.out (lateStart A) q t p = [] := by
      intro q t hq ht
      exact lateStart_out_before (by rw [hfX]; omega) (by simp [ustart, hR, X, hq]; exact ht) p
    have outB : ∀ q t, lab q = 2 → lab p ≤ 1 → t < Δ + e →
        R.out (lateStart A) q t p = R'.out (lateStart A) q t p := by
      intro q t hq hp1 ht
      rw [Run.out_of_faulty _ _ (by rw [hfX]; exact hq)]
      simp [hR, hR', X, ht, hp1]
    funext q
    rw [Run.inbox_of_const _ R (c := DX Δ e L (lab q) (lab p)) (DX_pos he hΔ hL _ _)
        (fun t => rfl),
      Run.inbox_of_const _ R' (c := DW Δ e L (lab q) (lab p)) (DW_pos he hΔ hL _ _)
        (fun t => rfl)]
    have hq4 := hl.le4 q
    have hp4 := hl.le4 p
    simp only [Nat.add_zero]
    simp only [off, claim1T] at hop hpT ⊢
    have hq5 : lab q = 0 ∨ lab q = 1 ∨ lab q = 2 ∨ lab q = 3 ∨ lab q = 4 := by omega
    have hp5 : lab p = 0 ∨ lab p = 1 ∨ lab p = 3 ∨ lab p = 4 := by omega
    obtain hq | hq | hq | hq | hq := hq5 <;> obtain hpl | hpl | hpl | hpl := hp5
    all_goals simp only [hq, hpl, DX, DW, Nat.reduceEqDiff, and_true, and_false, or_false,
      or_true, ite_true, ite_false, Nat.sub_zero] at hop hpT ⊢
    all_goals
      split_ifs <;> first
        | rfl
        | (exfalso; omega)
        | exact outB q _ hq (by omega) (by omega)
        | exact outPre q _ hq (by omega)
        | exact outEq q _ _ (by omega)
            (by simp only [off, hq, Nat.reduceEqDiff, ite_true, ite_false]; omega)
            (by simp only [claim1T, hq, Nat.reduceEqDiff, ite_true, ite_false]; omega)
            (by omega)
            (by simp only [off, hq, Nat.reduceEqDiff, ite_true, ite_false]; omega)

end GoodCaseLatencyBB.Thm10
