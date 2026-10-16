import Papers.PODC2021.GoodCaseLatencyBB.Unsync

/-!
# The executions of Theorem 10 (`Δ + 1.5δ` lower bound with unsynchronized start)

Abraham–Nayak–Ren–Xiang, PODC 2021, Theorem 10, Appendix C.4, Figure 11.

Time is discrete, `δ = 2e` (so `0.5δ = e`), and all delays are *effective* delays (see
`Basic.lean`). Processes are labelled by `lab : P → ℕ`:
`0 = g`, `1 = A`, `2 = B` (contains the broadcaster `s`), `3 = C`, `4 = h`.
The mirror labelling is `lab' p = 4 - lab p` (swap `g ↔ h`, `A ↔ C`).

* `W va lab` — the *world* of Execution 1: everybody correct and starting at `0`, the broadcaster
  has input `va`; delays: `C → g` is `Δ + e`, `C → A`, `g → C`, `A → C`, `h → A` are `Δ − e`,
  `A → h` is `Δ + e`, `g ↔ h`, `C → B`, `h → B` are `L` (very late), everything else `δ`.
  Execution 1 is `W a lab` with `C ∪ {h}` Byzantine (`Run.enlarge`); Execution 4 is the mirror.
* `X lab lab' va vb` — the *physical execution* shared by Executions 2 and 3: `B` is Byzantine and
  replays, up to time `TB = Δ + e`, what it sends in `W va lab` towards `g, A` and what it sends in
  `W vb lab'` towards `C, h`; `C` starts at time `e`, everybody else at `0`; delays as in
  Execution 2 of the paper (`g ↔ A`: `δ`, `g ↔ C`: `Δ`, `C → A`: `Δ − δ`, `A → C`: `Δ`,
  `h → A`: `Δ − e`, `A → h`: `Δ + e`, `C → h`: `e`, `h → C`: `3e`, `B → C`: `3e`, `g ↔ h`: `L`,
  everything else `δ`). Execution 2 is `X lab lab' a b` with `B ∪ {h}` Byzantine; Execution 3
  is the mirror `X lab' lab b a` with `B ∪ {g}` Byzantine.

Unlike the paper, Byzantine processes behaving "honestly" are modelled as correct processes of an
auxiliary run, made Byzantine with `Run.enlarge`; this makes executions 2 and 3 literally the same
physical execution up to the start-time shift of `A` and `C` (`claim2`).
-/

set_option linter.unusedSectionVars false

namespace GoodCaseLatencyBB

open Cslib.Byzantine.PartialSync Finset

namespace Thm10

variable {P M S V K : Type*} [DecidableEq P]

/-- Effective delays of the world `W` (sender label `i`, receiver label `j`). -/
def DW (Δ e L i j : ℕ) : ℕ :=
  if i = 3 ∧ j = 0 then Δ + e
  else if i = 3 ∧ j = 1 then Δ - e
  else if i = 0 ∧ j = 3 then Δ - e
  else if i = 1 ∧ j = 3 then Δ - e
  else if i = 4 ∧ j = 1 then Δ - e
  else if i = 1 ∧ j = 4 then Δ + e
  else if (i = 0 ∧ j = 4) ∨ (i = 4 ∧ j = 0) ∨ (i = 3 ∧ j = 2) ∨ (i = 4 ∧ j = 2) then L
  else 2 * e

/-- Effective delays of the physical execution `X` (sender label `i`, receiver label `j`). -/
def DX (Δ e L i j : ℕ) : ℕ :=
  if (i = 0 ∧ j = 3) ∨ (i = 3 ∧ j = 0) ∨ (i = 1 ∧ j = 3) then Δ
  else if i = 3 ∧ j = 1 then Δ - 2 * e
  else if (i = 0 ∧ j = 4) ∨ (i = 4 ∧ j = 0) then L
  else if i = 4 ∧ j = 1 then Δ - e
  else if i = 1 ∧ j = 4 then Δ + e
  else if i = 3 ∧ j = 4 then e
  else if (i = 4 ∧ j = 3) ∨ (i = 2 ∧ j = 3) then 3 * e
  else 2 * e

variable (A : Algorithm P M S V V) (s : P) (v0 : V) (Δ e L : ℕ)

/-- The world of Execution 1 (all correct, all start at `0`). -/
def W (va : V) (lab : P → ℕ) : Run P M (V × ℕ) where
  faulty := ∅
  inp p := (if p = s then va else v0, 0)
  gst := 0
  byz _ _ _ := []
  dl q t p := t + DW Δ e L (lab q) (lab p) - 1

/-- The physical execution of Executions 2 and 3. -/
def X [Fintype P] (lab lab' : P → ℕ) (va vb : V) : Run P M (V × ℕ) where
  faulty := univ.filter fun p => lab p = 2
  inp p := (if p = s then va else v0, if lab p = 3 then e else 0)
  gst := 0
  byz q t p := if t < Δ + e then
      (if lab p ≤ 1 then (W s v0 Δ e L va lab).out (lateStart A) q t p
       else if 3 ≤ lab p then (W s v0 Δ e L vb lab').out (lateStart A) q t p else [])
    else []
  dl q t p := t + DX Δ e L (lab q) (lab p) - 1

/-- Hypotheses on the labelling. -/
structure Labels (s : P) (lab lab' : P → ℕ) : Prop where
  le4 : ∀ p, lab p ≤ 4
  mirror : ∀ p, lab' p = 4 - lab p
  bc : lab s = 2

theorem Labels.swap {lab lab' : P → ℕ} (h : Labels s lab lab') : Labels s lab' lab where
  le4 p := by rw [h.mirror]; omega
  mirror p := by rw [h.mirror]; have := h.le4 p; omega
  bc := by rw [h.mirror, h.bc]

/-! ### The claims (to be proved in `UnsyncClaims.lean`) -/

variable [Fintype P] {A s v0 Δ e L}

/-- Start offset of `p` in `X lab lab' _ _`. -/
def off (lab : P → ℕ) (e : ℕ) (p : P) : ℕ := if lab p = 3 then e else 0

end Thm10

end GoodCaseLatencyBB
