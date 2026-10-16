import Papers.PODC2021.GoodCaseLatencyBB.UnsyncRuns

/-!
# Claim 2 of the proof of Theorem 10

`A` and `C` cannot distinguish Executions 2 and 3: the physical execution `X lab lab' a b`
(where `C` starts at time `e`) and its mirror `X lab' lab b a` (where `A` starts at time `e`) are
the same execution up to the start-time shifts: every non-`B` process has, at each local time, the
same state in both.
-/

set_option linter.unusedSectionVars false

namespace GoodCaseLatencyBB.Thm10

open Cslib.Byzantine.PartialSync Finset

variable {P M S V K : Type*} [DecidableEq P] [Fintype P]
variable {A : Algorithm P M S V V} {s : P} {v0 : V} {Δ e L : ℕ}


/-- Effective delays of `X` are positive. -/
theorem DX_pos (he : 1 ≤ e) (hΔ : 2 * e < Δ) (hL : L = Δ + 3 * e) (i j : ℕ) :
    1 ≤ DX Δ e L i j := by
  unfold DX; split_ifs <;> omega

/-- The delay table of `X` is invariant under mirroring, up to the start offsets. -/
theorem DX_mirror (_he : 1 ≤ e) (hΔ : 2 * e < Δ) (hL : L = Δ + 3 * e) {i j : ℕ} (hi : i ≤ 4)
    (hj : j ≤ 4) (hj2 : j ≠ 2) :
    DX Δ e L (4 - i) (4 - j) + (if j = 3 then e else 0) + (if 4 - i = 3 then e else 0) =
      DX Δ e L i j + (if 4 - j = 3 then e else 0) + (if i = 3 then e else 0) := by
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) with rfl | rfl | rfl | rfl | rfl <;>
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 3 ∨ j = 4) with rfl | rfl | rfl | rfl <;>
  simp [DX] <;> omega

/-- Inbox from a correct sender under `lateStart`, on a link with constant effective delay. -/
theorem inbox_lateStart (R : Run P M (V × ℕ)) {q p : P} (hq : q ∉ R.faulty) {c : ℕ} (hc : 1 ≤ c)
    (hdl : ∀ t, R.dl q t p = t + c - 1) (τ : ℕ) :
    R.inbox (lateStart A) p τ q =
      if c + ustart R q ≤ τ + 1 then R.out (lateStart A) q (τ + 1 - c) p else [] := by
  rw [Run.inbox_of_const _ R hc hdl]
  by_cases h1 : c ≤ τ + 1
  · by_cases h2 : c + ustart R q ≤ τ + 1
    · simp only [h1, h2, ↓reduceIte]
    · simp only [h1, h2, ↓reduceIte]; rw [lateStart_out_before hq (by omega)]
  · have h2 : ¬ c + ustart R q ≤ τ + 1 := by omega
    simp only [h1, h2, ↓reduceIte]

theorem X_byz_mirror {lab lab' : P → ℕ} (hl : Labels s lab lab') (va vb : V) :
    (X A s v0 Δ e L lab lab' va vb).byz = (X A s v0 Δ e L lab' lab vb va).byz := by
  funext q t p
  simp only [X]
  have h4 := hl.le4 p
  have hm := hl.mirror p
  split_ifs <;> first | rfl | omega

theorem claim2 {lab lab' : P → ℕ} (hl : Labels s lab lab') (he : 1 ≤ e) (hΔ : 2 * e < Δ)
    (hL : L = Δ + 3 * e) (va vb : V) :
    ∀ τ p, lab p ≠ 2 → off lab e p ≤ τ →
      (X A s v0 Δ e L lab lab' va vb).st (lateStart A) τ p =
        (X A s v0 Δ e L lab' lab vb va).st (lateStart A) (τ + off lab' e p - off lab e p) p := by
  intro τ0 p hp hop
  set R := X A s v0 Δ e L lab lab' va vb with hR
  set R' := X A s v0 Δ e L lab' lab vb va with hR'
  have hf : ∀ q, q ∈ R.faulty ↔ lab q = 2 := fun q => by simp [hR, X]
  have hf' : ∀ q, q ∈ R'.faulty ↔ lab q = 2 := fun q => by
    simp only [hR', X, mem_filter, mem_univ, true_and, hl.mirror q]; have := hl.le4 q; omega
  have hu : ∀ q, ustart R q = off lab e q := fun q => rfl
  have hu' : ∀ q, ustart R' q = off lab' e q := fun q => rfl
  have ho : ∀ q, off lab' e q = if 4 - lab q = 3 then e else 0 := fun q => by
    simp only [off, hl.mirror q]
  refine Run.st_shift_eq (lateStart A) R R' (X := {p | lab p ≠ 2}) (off lab e) (off lab' e)
    (fun _ => τ0) ?_ ?_ τ0 p hp hop le_rfl
  · intro p hp _
    have hps : p ≠ s := fun h => hp (h ▸ hl.bc)
    change R.st (lateStart A) (ustart R p) p = R'.st (lateStart A) (ustart R' p) p
    rw [lateStart_st_start, lateStart_st_start]
    simp [hR, hR', X, hps]
  · intro τ ih p hp hop _
    funext q
    have hp2 : lab p ≠ 2 := hp
    have hdl : ∀ t, R.dl q t p = t + DX Δ e L (lab q) (lab p) - 1 := fun t => rfl
    have hdl' : ∀ t, R'.dl q t p = t + DX Δ e L (4 - lab q) (4 - lab p) - 1 := fun t => by
      simp only [hR', X, hl.mirror]
    have key := DX_mirror he hΔ hL (hl.le4 q) (hl.le4 p) hp2
    have c1 := DX_pos he hΔ hL (lab q) (lab p)
    have c2 := DX_pos he hΔ hL (4 - lab q) (4 - lab p)
    have K : DX Δ e L (4 - lab q) (4 - lab p) + off lab e p + off lab' e q =
        DX Δ e L (lab q) (lab p) + off lab' e p + off lab e q := by
      rw [ho p, ho q]; exact key
    by_cases hq2 : lab q = 2
    · have hq : q ∈ R.faulty := (hf q).2 hq2
      have hq' : q ∈ R'.faulty := (hf' q).2 hq2
      have h1 : off lab e q = 0 := by simp [off, hq2]
      have h2 : off lab' e q = 0 := by rw [ho q, hq2]; rfl
      rw [Run.inbox_of_const _ R c1 hdl, Run.inbox_of_const _ R' c2 hdl',
        Run.out_of_faulty _ _ hq, Run.out_of_faulty _ _ hq', X_byz_mirror hl]
      split_ifs with i1 i2 i2
      · congr 1; omega
      · omega
      · omega
      · rfl
    · have hq : q ∉ R.faulty := fun h => hq2 ((hf q).1 h)
      have hq' : q ∉ R'.faulty := fun h => hq2 ((hf' q).1 h)
      rw [inbox_lateStart R hq c1 hdl, inbox_lateStart R' hq' c2 hdl', hu, hu']
      by_cases hc : DX Δ e L (lab q) (lab p) + off lab e q ≤ τ + 1
      · have hc' : DX Δ e L (4 - lab q) (4 - lab p) + off lab' e q ≤
            τ + off lab' e p - off lab e p + 1 := by omega
        simp only [hc, hc', ↓reduceIte]
        rw [Run.out_of_correct _ _ hq, Run.out_of_correct _ _ hq',
          ih q hq2 (τ + 1 - DX Δ e L (lab q) (lab p)) (by omega) (by omega) (by omega)]
        have ht : τ + 1 - DX Δ e L (lab q) (lab p) + off lab' e q - off lab e q =
            τ + off lab' e p - off lab e p + 1 - DX Δ e L (4 - lab q) (4 - lab p) := by omega
        rw [ht]
      · have hc' : ¬ DX Δ e L (4 - lab q) (4 - lab p) + off lab' e q ≤
            τ + off lab' e p - off lab e p + 1 := by omega
        simp only [hc, hc', ↓reduceIte]

end GoodCaseLatencyBB.Thm10
