import Papers.PODC2010.GroupMutexLogRMR.StepDoor
import Papers.PODC2010.GroupMutexLogRMR.StepLocal
import Papers.PODC2010.GroupMutexLogRMR.StepWrite
import Papers.PODC2010.GroupMutexLogRMR.StepSwitch

/-!
# Mutual exclusion (P1) and the paper's invariants

`Inv` (`Inv.lean`) holds in every reachable configuration. Consequences: mutual exclusion (P1),
the paper's Invariant 5, Invariant 3, Invariant 4 and Lemma 1.
-/

namespace Podc.GroupMutexLogRMR

variable {n : ℕ} {J : Type} [DecidableEq J]

theorem Inv.init (s₀ : J) : Inv (Cfg.init n s₀) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro s d; simp [Cfg.init, Loc.cnt, PC.btw, PC.idx]
  · intro y; simp [Cfg.init, PC.btw, PC.idx]
  · intro s; left; simp [Cfg.init]
  · intro s _ h; simp [Cfg.init] at h
  · intro s y _ _ e he; simp [Cfg.init, Loc.pside, PC.btw, PC.idx] at he
  · intro y z _ h; simp [Cfg.init] at h
  · intro h; simp [Cfg.init] at h
  · intro y; constructor <;> simp [Cfg.init, PC.btw, PC.idx]

theorem Inv.step {c : Cfg n J} (hI : Inv c) (p : Fin n) (σ : J) : Inv (c.step p σ) := by
  cases hp : (c.loc p).pc with
  | rem => exact inv_step_rem hI p σ hp
  | l1_1 => exact inv_step_l1_1 hI p σ hp
  | l1_2 => exact inv_step_l1_2 hI p σ hp
  | l1_3 => exact inv_step_l1_3 hI p σ hp
  | l1_4 => exact inv_step_l1_4 hI p σ hp
  | l1_5 => exact inv_step_l1_5 hI p σ hp
  | l1_6 => exact inv_step_l1_6 hI p σ hp
  | l1_7 => exact inv_step_l1_7 hI p σ hp
  | l2 => exact inv_step_l2 hI p σ hp
  | l3 => exact inv_step_l3 hI p σ hp
  | l4 => exact inv_step_l4 hI p σ hp
  | l5_1 => exact inv_step_l5_1 hI p σ hp
  | l5_2 => exact inv_step_l5_2 hI p σ hp
  | l5_3 => exact inv_step_l5_3 hI p σ hp
  | l6 => exact inv_step_l6 hI p σ hp
  | l8 => exact inv_step_l8 hI p σ hp
  | l9 => exact inv_step_l9 hI p σ hp
  | l11 => exact inv_step_l11 hI p σ hp
  | l12 => exact inv_step_l12 hI p σ hp
  | cs => exact inv_step_cs hI p σ hp
  | l13 => exact inv_step_l13 hI p σ hp
  | l14 => exact inv_step_l14 hI p σ hp
  | l16_1 => exact inv_step_l16_1 hI p σ hp
  | l16_3 => exact inv_step_l16_3 hI p σ hp
  | l16_4 => exact inv_step_l16_4 hI p σ hp
  | l16_6 => exact inv_step_l16_6 hI p σ hp
  | l16_7 => exact inv_step_l16_7 hI p σ hp
  | l16_8 => exact inv_step_l16_8 hI p σ hp
  | l16_12 => exact inv_step_l16_12 hI p σ hp
  | l5_5 => exact inv_step_l5_5 hI p σ hp
  | l7 => exact inv_step_l7 hI p σ hp
  | l16_11 => exact inv_step_l16_11 hI p σ hp
  | l16_13 => exact inv_step_l16_13 hI p σ hp
  | l15 => exact inv_step_l15 hI p σ hp
  | l16_5 => exact inv_step_l16_5 hI p σ hp
  | l16_14 => exact inv_step_l16_14 hI p σ hp
  | l5_4 =>
    cases hl : c.linkS p
    · exact inv_step_l5_4_fail hI p σ hp hl
    · exact inv_step_l5_4_succ hI p σ hp hl
  | l10 =>
    cases hl : c.linkEx p
    · exact inv_step_l10_fail hI p σ hp hl
    · exact inv_step_l10_succ hI p σ hp hl
  | l16_2 =>
    cases hl : c.linkEx p
    · exact inv_step_l16_2_fail hI p σ hp hl
    · exact inv_step_l16_2_succ hI p σ hp hl
  | l16_9 =>
    cases hl : c.linkEx p
    · exact inv_step_l16_9_fail hI p σ hp hl
    · exact inv_step_l16_9_succ hI p σ hp hl
  | l16_10 =>
    cases hl : c.linkS p
    · exact inv_step_l16_10_fail hI p σ hp hl
    · exact inv_step_l16_10_succ hI p σ hp hl

theorem Inv.run {c : Cfg n J} (hI : Inv c) (es : List (Ev n J)) : Inv (run c es) := by
  induction es generalizing c with
  | nil => exact hI
  | cons e es ih => exact ih (hI.step e.1 e.2)

theorem Reachable.inv {s₀ : J} {c : Cfg n J} (h : Reachable s₀ c) : Inv c := by
  obtain ⟨es, rfl⟩ := h
  exact (Inv.init s₀).run es

/-- **(P1) Mutual exclusion** (Theorem 1 of the paper): two processes in the critical section
request the same session. -/
theorem mutual_exclusion {s₀ : J} {c : Cfg n J} (h : Reachable s₀ c) (y z : Fin n)
    (hy : (c.loc y).pc = .cs) (hz : (c.loc z).pc = .cs) : (c.loc y).s = (c.loc z).s :=
  h.inv.mutex y z hy hz

/-- **Invariant 5 of the paper**: a process at lines 9–16.6 of session `s` and side `d` has
`S = (s, d, −)` and `Out[s] = d`. -/
theorem invariant5 {s₀ : J} {c : Cfg n J} (h : Reachable s₀ c) (y : Fin n)
    (hy : PC.btw .l9 .l16_6 (c.loc y).pc) :
    c.S.1 = (c.loc y).s ∧ c.S.2.1 = (c.loc y).d ∧ c.Out (c.loc y).s = (c.loc y).d :=
  (h.inv.li y).i5 hy

/-- **Invariant 3 of the paper**: if `S = (s, d', w)` and `Out[s] ≠ d'`, a process of session `w`
is at line 5.5 or 16.11 (about to write `Out[s] ← d'`). -/
theorem invariant3 {s₀ : J} {c : Cfg n J} (h : Reachable s₀ c) (hout : c.Out c.S.1 ≠ c.S.2.1) :
    ∃ z, ((c.loc z).pc = .l5_5 ∨ (c.loc z).pc = .l16_11) ∧ (c.loc z).s = c.S.2.2 :=
  let ⟨z, h1, _, h3⟩ := h.inv.g8 hout
  ⟨z, h1, h3⟩

end Podc.GroupMutexLogRMR
