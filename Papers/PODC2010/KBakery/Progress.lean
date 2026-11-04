import Papers.PODC2010.KBakery.RunLemmas

/-!
# Progress toolkit for the liveness proof
-/

set_option linter.unusedSectionVars false

namespace Podc.KBakery

open Finset

variable {P : Type} [LinearOrder P] [Fintype P]
variable {fife : Bool} {k : ℕ}

-- CSLib candidate: `Cslib/Foundations/Data/Nat/Descent.lean` (progress by a measure for any schedule)
/-- Progress by a measure: if from time `T₀` on, as long as `Good` does not hold, the domain `Dom`
is preserved, `μ` never increases and strictly decreases at every step of `q`, and `q` takes
infinitely many steps, then `Good` eventually holds. -/
lemma exists_good_of_measure (sched : ℕ → P) (q : P) (hinf : ∀ T, ∃ t ≥ T, sched t = q)
    (Good Dom : ℕ → Prop) (μ : ℕ → ℕ) (T₀ : ℕ) (h₀ : Dom T₀)
    (hstep : ∀ t ≥ T₀, Dom t → ¬ Good (t + 1) →
      Dom (t + 1) ∧ μ (t + 1) ≤ μ t ∧ (sched t = q → μ (t + 1) < μ t)) :
    ∃ t ≥ T₀, Good t := by
  by_contra H
  push Not at H
  have hD : ∀ t ≥ T₀, Dom t := by
    intro t ht
    induction t, ht using Nat.le_induction with
    | base => exact h₀
    | succ t ht ih => exact (hstep t ht ih (H (t + 1) (by omega))).1
  have hmono : ∀ t ≥ T₀, ∀ t' ≥ t, μ t' ≤ μ t := by
    intro t ht t' ht'
    induction t', ht' using Nat.le_induction with
    | base => exact le_rfl
    | succ t' ht' ih =>
      exact (hstep t' (by omega) (hD t' (by omega)) (H (t' + 1) (by omega))).2.1.trans ih
  have hdec : ∀ n : ℕ, ∃ t ≥ T₀, μ t + n ≤ μ T₀ := by
    intro n
    induction n with
    | zero => exact ⟨T₀, le_rfl, by simp⟩
    | succ n ih =>
      obtain ⟨t, ht, hμ⟩ := ih
      obtain ⟨t', ht', hs⟩ := hinf t
      have h1 := (hstep t' (by omega) (hD t' (by omega)) (H (t' + 1) (by omega))).2.2 hs
      have h2 := hmono t ht t' ht'
      exact ⟨t' + 1, by omega, by omega⟩
  obtain ⟨t, -, ht⟩ := hdec (μ T₀ + 1)
  omega

namespace Run

variable (r : Run fife k P)

/-- A process that is not crashed and is eventually always outside the NCS takes infinitely
many steps. -/
lemma inf_sched_of_not_crashed {q : P} (hq : ¬ r.Crashed q) {T : ℕ}
    (hT : ∀ t ≥ T, (r.s t).pc q ≠ .ncs) : ∀ T', ∃ t ≥ T', r.sched t = q := by
  intro T'
  by_contra H
  push Not at H
  exact hq ⟨max T T', fun t ht => ⟨H t (by omega), hT t (by omega)⟩⟩

/-- A process that takes finitely many steps eventually keeps its program counter. -/
lemma pc_const_of_fin_sched {q : P} {T : ℕ} (hT : ∀ t ≥ T, r.sched t ≠ q) :
    ∀ t ≥ T, (r.s t).pc q = (r.s T).pc q ∧ (r.s t).want q = (r.s T).want q := by
  intro t ht
  induction t, ht using Nat.le_induction with
  | base => exact ⟨rfl, rfl⟩
  | succ t ht ih =>
    rw [r.pc_succ_of_ne (hT t ht), r.want_succ_of_ne (hT t ht)]; exact ih

/-- A process in the trying protocol stays there or enters the CS. -/
lemma trying_succ {t : ℕ} {q : P} (h : ((r.s t).pc q).InTrying) :
    ((r.s (t + 1)).pc q).InTrying ∨ (r.s (t + 1)).pc q = .cs := by
  by_cases hq : r.sched t = q
  · rw [r.step t, stepAt_pc, hq]
    rcases hpc : (r.s t).pc q with _ | rem' | ⟨acc', rem'⟩ | rem' | ⟨pred, cap⟩ | ⟨pred, rem'⟩ |
      ⟨pred, rem', cap⟩ | rem' | _ | rem' <;>
      simp only [hpc, PC.InTrying, PC.InDoorway, PC.InWaiting, or_self] at h <;>
      simp only [core, hpc] <;> (try split_ifs) <;> (try cases fife) <;>
      simp [PC.InTrying, PC.InDoorway, PC.InWaiting]
  · rw [r.pc_succ_of_ne hq]; exact Or.inl h

/-- If `q` is in the trying protocol at `t₀` and never in the CS afterwards, it stays in the
trying protocol forever. -/
lemma trying_forever {t₀ : ℕ} {q : P} (h : ((r.s t₀).pc q).InTrying)
    (hcs : ∀ t ≥ t₀, (r.s t).pc q ≠ .cs) : ∀ t ≥ t₀, ((r.s t).pc q).InTrying := by
  intro t ht
  induction t, ht using Nat.le_induction with
  | base => exact h
  | succ t ht ih =>
    rcases r.trying_succ ih with h' | h'
    · exact h'
    · exact absurd h' (hcs (t + 1) (by omega))

end Run

/-- Past line 16 and before the CS: lines 19–23. -/
def PC.Settled : PC P → Prop
  | .head _ _ | .scan _ _ | .chk _ _ _ | .cap23 _ => True
  | _ => False

/-- Distance (in own steps) from the trying protocol to line 19. -/
def doorMu (N : ℕ) : PC P → ℕ
  | .d14 rem => rem.card + 1 + (N + 1) + N
  | .d15 _ rem => rem.card + 1 + N
  | .d16 rem => rem.card + 1
  | _ => 0

lemma doorMu_step {s : Cfg P} {q i : P} (ha : Admissible s q i)
    (hpre : (s.pc q).InDoorway ∨ ∃ rem, s.pc q = .d16 rem) :
    ((stepAt fife k s q i).pc q).Settled ∨
      doorMu (Fintype.card P) ((stepAt fife k s q i).pc q) < doorMu (Fintype.card P) (s.pc q) := by
  have hc : ∀ s : Finset P, s.card ≤ Fintype.card P := fun s => card_le_univ s
  rw [stepAt_pc]
  rcases hpc : s.pc q with _ | rem' | ⟨acc', rem'⟩ | rem' | ⟨pred, cap⟩ | ⟨pred, rem'⟩ |
      ⟨pred, rem', cap⟩ | rem' | _ | rem' <;>
    simp [hpc, PC.InDoorway] at hpre <;>
    simp only [core, hpc] <;> (try split_ifs) <;> simp [PC.Settled, doorMu] <;>
    first
    | exact card_erase_lt_of_mem ‹_›
    | (have := hc (univ.erase q); have := card_erase_add_one (mem_univ q)
       simp only [card_univ] at this; omega)
    | omega

/-- From lines 19–23 a step stays there or enters the CS. -/
lemma settled_step {s : Cfg P} {q i : P} (h : (s.pc q).Settled) :
    ((stepAt fife k s q i).pc q).Settled ∨ (stepAt fife k s q i).pc q = .cs := by
  rw [stepAt_pc]
  rcases hpc : s.pc q with _ | rem' | ⟨acc', rem'⟩ | rem' | ⟨pred, cap⟩ | ⟨pred, rem'⟩ |
      ⟨pred, rem', cap⟩ | rem' | _ | rem' <;> simp [hpc, PC.Settled] at h <;>
    simp only [core, hpc] <;> (try split_ifs) <;> (try cases fife) <;> simp [PC.Settled]

namespace Run

variable (r : Run fife k P)

/-- A non-crashed process that stays in the trying protocol forever eventually stays at lines
19–23 forever, with a fixed ticket. -/
lemma settles {q : P} (hq : ¬ r.Crashed q) {T : ℕ} (hT : ∀ t ≥ T, ((r.s t).pc q).InTrying) :
    ∃ T' ≥ T, ∀ t ≥ T', ((r.s t).pc q).Settled ∧ (r.s t).ticket q = (r.s T').ticket q := by
  have hinf := r.inf_sched_of_not_crashed hq (T := T) (fun t ht h => by
    have := hT t ht; rw [h] at this; simp [PC.InTrying, PC.InDoorway, PC.InWaiting] at this)
  obtain ⟨T', hT', hS⟩ := exists_good_of_measure r.sched q hinf
    (fun t => ((r.s t).pc q).Settled) (fun t => ((r.s t).pc q).InTrying)
    (fun t => doorMu (Fintype.card P) ((r.s t).pc q)) T (hT T le_rfl) (by
      intro t ht hD hG
      have hdec : r.sched t = q → doorMu (Fintype.card P) ((r.s (t + 1)).pc q) <
          doorMu (Fintype.card P) ((r.s t).pc q) := by
        intro hs
        have hadm := r.adm t
        rw [hs] at hadm
        by_cases hpre : ((r.s t).pc q).InDoorway ∨ ∃ rem, (r.s t).pc q = .d16 rem
        · rcases doorMu_step (fife := fife) (k := k) hadm hpre with h | h
          · exact absurd (by rw [r.step t, hs]; exact h) hG
          · rw [r.step t, hs]; exact h
        · exfalso
          have hS : ((r.s t).pc q).Settled := by
            rcases hpc : (r.s t).pc q with _ | rem' | ⟨acc', rem'⟩ | rem' | ⟨pred, cap⟩ |
              ⟨pred, rem'⟩ | ⟨pred, rem', cap⟩ | rem' | _ | rem' <;>
              simp [hpc, PC.InTrying, PC.InDoorway, PC.InWaiting, PC.Settled] at hD hpre ⊢
          rcases settled_step (fife := fife) (k := k) (i := r.choice t) hS with h | h
          · exact hG (by rw [r.step t, hs]; exact h)
          · have := hT (t + 1) (by omega)
            rw [r.step t, hs, h] at this; simp [PC.InTrying, PC.InDoorway, PC.InWaiting] at this
      refine ⟨hT (t + 1) (by omega), ?_, hdec⟩
      by_cases hs : r.sched t = q
      · exact (hdec hs).le
      · rw [r.pc_succ_of_ne hs])
  refine ⟨T', hT', fun t ht => ?_⟩
  induction t, ht using Nat.le_induction with
  | base => exact ⟨hS, rfl⟩
  | succ t ht ih =>
    obtain ⟨hS', htk⟩ := ih
    have hn15 : ∀ acc rem, (r.s t).pc q ≠ .d15 acc rem := by
      intro acc rem h; rw [h] at hS'; simp [PC.Settled] at hS'
    refine ⟨?_, by rw [r.ticket_succ_of_not_d15 hn15, htk]⟩
    by_cases hs : r.sched t = q
    · rcases settled_step (fife := fife) (k := k) (i := r.choice t) hS' with h | h
      · rw [r.step t, hs]; exact h
      · have := hT (t + 1) (by omega)
        rw [r.step t, hs, h] at this; simp [PC.InTrying, PC.InDoorway, PC.InWaiting] at this
    · rw [r.pc_succ_of_ne hs]; exact hS'

end Run

end Podc.KBakery
