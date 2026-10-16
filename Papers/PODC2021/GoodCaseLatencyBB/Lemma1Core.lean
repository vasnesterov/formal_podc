import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith

/-!
# The timing core of Lemma 1 (the `(Δ + 1.5δ)`-BB protocol, Figure 9)

Abraham–Nayak–Ren–Xiang, PODC 2021, Lemma 1 parts (1) and (2). We do **not** formalize the protocol
of Figure 9; this file only checks the timing argument, abstracted as follows (all times are
global and real-valued; clocks have no drift, so a local waiting window of length `w` after a local
event is a global window of length `w` after the corresponding global event).

* `P h` is the time at which honest `h` receives its first valid proposal (for value `v h`) and
  forwards it to everybody; `det h` is the time at which `h` detects equivocation.
* **Forwarding + delay bound `Δ`:** if `v h ≠ v h'`, then `h` detects equivocation by the time it
  holds both values: `det h ≤ max (P h) (P h' + Δ)`.
* **Vote rule (Step 3):** `h` sends a vote with parameter `d` only if it has detected no
  equivocation until `P h + Δ − d/2`, i.e. `P h + Δ − d/2 < det h`.
* **Commit rule (Step 4a):** `h` commits with parameter `d` only if it has detected no equivocation
  until `P h + Δ + d/2`, i.e. `P h + Δ + d/2 < det h`.

Remark (proof imprecision, statement unaffected): the paper argues with the commit *time* `t` ("if
`h'` receives `v'` at `≤ t − Δ`, its forwarded proposal stops `h` from committing"). Step 4a only
requires no equivocation until `t_prop + Δ + 0.5d`, which may be earlier than `t` (when the votes
arrive late), so this sentence is not justified as written; the argument below compares with
`P h + 0.5d` instead and needs nothing else.
-/

namespace GoodCaseLatencyBB.Lemma1

variable {H V : Type*} (P det : H → ℝ) (v : H → V) (Δ : ℝ)

/-- Forwarding and the delay bound: holding two different values means detecting equivocation. -/
def Forwarding : Prop := ∀ h h', v h ≠ v h' → det h ≤ max (P h) (P h' + Δ)

/-- **Lemma 1 (1).** If `h` commits `v h` with parameter `d` and `h'` votes for `v h'` with parameter
`d' ≤ d`, then `v h' = v h`. -/
theorem part1 (hF : Forwarding P det v Δ) {h h' : H} {d d' : ℝ} (hd' : 0 ≤ d') (hdd : d' ≤ d)
    (hdΔ : d' < 2 * Δ) (hcommit : P h + Δ + d / 2 < det h) (hvote : P h' + Δ - d' / 2 < det h') :
    v h' = v h := by
  by_contra hne
  have h1 := hF h h' (Ne.symm hne)
  have h2 := hF h' h hne
  rcases le_total (P h) (P h' + Δ) with c1 | c1
  · rw [max_eq_right c1] at h1
    rcases le_total (P h') (P h + Δ) with c2 | c2
    · rw [max_eq_right c2] at h2; linarith
    · rw [max_eq_left c2] at h2; linarith
  · rw [max_eq_left c1] at h1; linarith

/-- **Lemma 1 (2).** Two honest parties that commit (with any parameters `d, d' ≥ 0`) commit the
same value. -/
theorem part2 (hF : Forwarding P det v Δ) {h h' : H} {d d' : ℝ} (hd : 0 ≤ d) (hd' : 0 ≤ d')
    (hΔ : 0 < Δ) (hc : P h + Δ + d / 2 < det h) (hc' : P h' + Δ + d' / 2 < det h') :
    v h = v h' := by
  by_contra hne
  have h1 := hF h h' hne
  have h2 := hF h' h (Ne.symm hne)
  rcases le_total (P h) (P h' + Δ) with c1 | c1
  · rw [max_eq_right c1] at h1
    rcases le_total (P h') (P h + Δ) with c2 | c2
    · rw [max_eq_right c2] at h2; linarith
    · rw [max_eq_left c2] at h2; linarith
  · rw [max_eq_left c1] at h1; linarith

end GoodCaseLatencyBB.Lemma1
