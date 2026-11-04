import Papers.PODC2010.KBakery.RunLemmas

/-!
# FIFE for the full algorithm (Lemma 5.16 of the thesis; part of Theorem 9 of the paper)

*If a process `p` finishes the doorway before a process `q` starts the doorway, and `q` enters
the CS before `p`, then `p` can enter the CS in a bounded number of its own steps.*

We prove it with the explicit bound `4N + 7` on the number of `p`'s own steps
(`N = |P|`), counted from the moment `q` is in the CS.
-/

set_option linter.unusedSectionVars false

namespace Podc.KBakery

open Finset

variable {P : Type} [LinearOrder P] [Fintype P]
variable {k : ℕ}

/-- Number of steps of `p` in the time interval `[t₁, t₂)`. -/
def Run.stepsOf {fife : Bool} (r : Run fife k P) (p : P) (t₁ t₂ : ℕ) : ℕ :=
  ((Finset.Ico t₁ t₂).filter fun u => r.sched u = p).card

lemma Run.stepsOf_succ {fife : Bool} (r : Run fife k P) (p : P) {t₁ t : ℕ} (h : t₁ ≤ t) :
    r.stepsOf p t₁ (t + 1) = r.stepsOf p t₁ t + if r.sched t = p then 1 else 0 := by
  unfold Run.stepsOf
  rw [Nat.Ico_succ_right_eq_insert_Ico h, filter_insert]
  split_ifs with hs
  · rw [card_insert_of_notMem (by simp)]
  · rfl

/-- The bound of FIFE. -/
def fifeBound (N : ℕ) : ℕ := 4 * N + 7

/-- State of `q` relative to the fixed ticket `tp` of `p`: either `q` already captured `p` with a
value `> tp`, or `q` is in a passage whose ticket will be `> tp` and has not yet written
`Capture[q][p]`. -/
def FifeQ (tp : ℕ) (p : P) (c : PC P) (tq : ℕ) : Prop :=
  match c with
  | .ncs | .d14 _ => True
  | .d15 acc rem => tp ≤ acc ∨ p ∈ rem
  | .d16 _ | .head _ _ | .scan _ _ | .chk _ _ _ => tp < tq
  | .cap23 rem => p ∈ rem ∧ tp < tq
  | .cs | .ex _ => False

/-- The measure of `p`'s remaining steps once `Capture[q][p] > Ticket[p]`. -/
def fifeMu (N : ℕ) (q : P) : PC P → ℕ
  | .d16 rem => rem.card + 1 + (3 * N + 6)
  | .head _ false => 3 * N + 6
  | .head _ true => N + 2
  | .scan _ rem => rem.card + 1 + (N + 1) + 1 + (N + 2)
  | .chk _ rem cap => rem.card + 1 + (if cap = true ∨ q ∈ rem then N + 2 else 3 * N + 6)
  | .cap23 rem => rem.card + 1
  | _ => 0

lemma fifeMu_le (q : P) (c : PC P) : fifeMu (Fintype.card P) q c ≤ fifeBound (Fintype.card P) := by
  have hc : ∀ s : Finset P, s.card ≤ Fintype.card P := fun s => card_le_univ s
  unfold fifeMu fifeBound
  split
  · have := hc ‹_›; omega
  · omega
  · omega
  · have := hc ‹_›; omega
  · have := hc ‹_›; split_ifs <;> omega
  · have := hc ‹_›; omega
  · omega

lemma fifeMu_pos {q : P} {c : PC P} (h : c.InWaiting) : 0 < fifeMu (Fintype.card P) q c := by
  unfold fifeMu
  split <;> simp_all [PC.InWaiting] <;> omega

lemma capture_le_succ {fife : Bool} (r : Run fife k P) (t : ℕ) (a b : P) :
    (r.s t).capture a b ≤ (r.s (t + 1)).capture a b := by
  by_cases hs : r.sched t = a
  · have hI := r.inv t
    rw [r.step t, stepAt_capture, hs]
    by_cases hc : ∃ rem, (r.s t).pc a = .cap23 rem
    · obtain ⟨rem, hpc⟩ := hc
      simp only [core, hpc]
      split_ifs
      · by_cases hb : b = r.choice t
        · subst hb; simp [hI.capLe]
        · simp [Function.update_of_ne hb]
      · rfl
    · push Not at hc
      rw [core_capture_self_of_ne_cap23 hc]
  · rw [r.capture_succ_of_ne hs]

/-- Every step of `p` decreases `fifeMu`, as long as `Capture[q][p] > Ticket[p]`. -/
lemma fifeMu_step {s : Cfg P} {p q i : P} (hqp : q ≠ p) (hw : (s.pc p).InWaiting)
    (hcap : s.ticket p < s.capture q p) (ha : Admissible s p i) :
    (stepAt true k s p i).pc p = .cs ∨
      fifeMu (Fintype.card P) q ((stepAt true k s p i).pc p) <
        fifeMu (Fintype.card P) q (s.pc p) := by
  have hc : ∀ s : Finset P, s.card ≤ Fintype.card P := fun s => card_le_univ s
  have hN : 0 < Fintype.card P := Fintype.card_pos_iff.2 ⟨p⟩
  rw [stepAt_pc]
  rcases hpc : s.pc p with _ | rem' | ⟨acc', rem'⟩ | rem' | ⟨pred, cap⟩ | ⟨pred, rem'⟩ |
      ⟨pred, rem', cap⟩ | rem' | _ | rem' <;> simp only [hpc, PC.InWaiting] at hw <;>
    (try cases cap) <;>
    simp only [core, hpc] <;> (try split_ifs) <;> (try (left; simp; done)) <;> right <;>
    simp [fifeMu] <;> first
    | exact card_erase_lt_of_mem ‹_›
    | (have := hc pred; omega)
    | omega
    | (simp_all; done)
    | (have h1 := card_erase_add_one ‹i ∈ rem'›
       split_ifs with hA hB hB
       · omega
       · omega
       · exfalso; apply hA
         by_cases hqi : q = i
         · left; rw [← hqi]; exact hcap
         · right; exact ⟨hqi, hB⟩
       · omega)
    | (have h0 := admissible_of_not_mem ha (by simpa [hpc, PC.rem] using ‹i ∉ rem'›)
       simp only [hpc, PC.rem] at h0
       subst h0
       simp)

/-- **FIFE** (Lemma 5.16 of the thesis, part of Theorem 9). In the full algorithm, suppose that at
time `t₀` the process `p` has finished its doorway (it is in the waiting room) and `q` is in the
NCS (it has not started its next doorway), and that `q` is in the CS at time `t₁ ≥ t₀` while `p`
has not been in the CS during `[t₀, t₁]`. Then from time `t₁` on, `p` is in the CS after at most
`4N + 7` of its own steps. -/
theorem fife (r : Run true k P) (p q : P) (t₀ t₁ : ℕ)
    (hp₀ : ((r.s t₀).pc p).InWaiting) (hq₀ : (r.s t₀).pc q = .ncs) (h₀₁ : t₀ ≤ t₁)
    (hq₁ : (r.s t₁).pc q = .cs) (hp : ∀ t, t₀ ≤ t → t ≤ t₁ → (r.s t).pc p ≠ .cs)
    (t₂ : ℕ) (h₁₂ : t₁ ≤ t₂) (hsteps : fifeBound (Fintype.card P) ≤ r.stepsOf p t₁ t₂) :
    ∃ t, t₁ ≤ t ∧ t ≤ t₂ ∧ (r.s t).pc p = .cs := by
  have hW := r.waiting_interval hp₀ hp
  set tp := (r.s t₀).ticket p
  have hqp : q ≠ p := by
    rintro rfl; rw [hq₀] at hp₀; simp [PC.InWaiting] at hp₀
  -- Phase 1: by time `t₁`, `q` has captured `p` with a value `> tp`.
  have hJ : ∀ t, t₀ ≤ t → t ≤ t₁ →
      tp < (r.s t).capture q p ∨ FifeQ tp p ((r.s t).pc q) ((r.s t).ticket q) := by
    intro t h0 h1
    induction t, h0 using Nat.le_induction with
    | base => right; simp [hq₀, FifeQ]
    | succ t ht ih =>
      have ih := ih (by omega)
      have hpt := (hW t ht (by omega)).2
      have hI := r.inv t
      by_cases hs : r.sched t = q
      · have hadm := r.adm t
        rw [hs] at hadm
        rw [r.step t, stepAt_capture, stepAt_pc, stepAt_ticket, hs]
        rcases ih with ih | ih
        · left
          by_cases hc : ∃ rem, (r.s t).pc q = .cap23 rem ∧ p ∈ rem ∧ r.choice t = p
          · obtain ⟨rem, hpc, hpr, hch⟩ := hc
            simp only [core, hpc, hch, hpr, if_true, Function.update_self]
            exact ih.trans_le (hI.capLe q p)
          · have : (core true k (r.s t) q (r.choice t)).capture q p = (r.s t).capture q p := by
              by_cases hc' : ∃ rem, (r.s t).pc q = .cap23 rem
              · obtain ⟨rem, hpc⟩ := hc'
                simp only [core, hpc]
                split_ifs with hi
                · have : p ≠ r.choice t := fun h => hc ⟨rem, hpc, h ▸ hi, h.symm⟩
                  simp [Function.update_of_ne this]
                · rfl
              · push Not at hc'
                exact congrFun (core_capture_self_of_ne_cap23 hc') p
            rw [this]; exact ih
        · rcases hpc : (r.s t).pc q with _ | rem' | ⟨acc', rem'⟩ | rem' | ⟨pred, cap⟩ |
            ⟨pred, rem'⟩ | ⟨pred, rem', cap⟩ | rem' | _ | rem' <;>
            simp only [hpc, FifeQ] at ih <;>
            simp only [core, hpc] <;> (try split_ifs) <;>
            simp [FifeQ] <;> rename_i hi <;> first
            | exact Or.inr ih
            | (rcases ih with ih | ih
               · exact Or.inr (Or.inl (Or.inl ih))
               · by_cases hpc' : p = r.choice t
                 · rw [← hpc', hpt]; exact Or.inr (Or.inl (Or.inr le_rfl))
                 · exact Or.inr (Or.inr ⟨hpc', ih⟩))
            | (by_cases hpc' : p = r.choice t
               · left; rw [hpc', Function.update_self]; exact ih.2
               · exact Or.inr ⟨⟨hpc', ih.1⟩, ih.2⟩)
            | (have h0 := admissible_of_not_mem hadm (by simpa [hpc, PC.rem] using hi)
               simp only [hpc, PC.rem] at h0
               subst h0
               simp at ih
               try exact Or.inr ih)
      · rw [r.capture_succ_of_ne hs, r.pc_succ_of_ne hs, r.ticket_succ_of_ne hs]; exact ih
  have hcap₁ : tp < (r.s t₁).capture q p := by
    rcases hJ t₁ h₀₁ le_rfl with h | h
    · exact h
    · rw [hq₁] at h; simp [FifeQ] at h
  -- Phase 2: from `t₁` on, every step of `p` decreases `fifeMu`.
  by_contra hcon
  push Not at hcon
  have hK : ∀ t, t₁ ≤ t → t ≤ t₂ →
      ((r.s t).pc p).InWaiting ∧ (r.s t).ticket p = tp ∧ tp < (r.s t).capture q p ∧
      r.stepsOf p t₁ t + fifeMu (Fintype.card P) q ((r.s t).pc p) ≤
        fifeMu (Fintype.card P) q ((r.s t₁).pc p) := by
    intro t h1 h2
    induction t, h1 using Nat.le_induction with
    | base =>
      refine ⟨(hW t₁ h₀₁ le_rfl).1, (hW t₁ h₀₁ le_rfl).2, hcap₁, ?_⟩
      simp [Run.stepsOf]
    | succ t ht ih =>
      obtain ⟨hw, htk, hc, hμ⟩ := ih (by omega)
      have hnot15 := Run.not_d15_of_waiting hw
      refine ⟨?_, ?_, hc.trans_le (capture_le_succ r t q p), ?_⟩
      · rcases r.waiting_succ hw with h | h
        · exact h
        · exact absurd h (hcon (t + 1) (by omega) h2)
      · rw [r.ticket_succ_of_not_d15 hnot15, htk]
      · rw [r.stepsOf_succ p ht]
        by_cases hs : r.sched t = p
        · have hadm := r.adm t
          rw [hs] at hadm
          rcases fifeMu_step (k := k) hqp hw (by rw [htk]; exact hc) hadm with h | h
          · exfalso; apply hcon (t + 1) (by omega) h2; rw [r.step t, hs]; exact h
          · rw [if_pos hs]
            rw [r.step t, hs]
            omega
        · rw [if_neg hs, r.pc_succ_of_ne hs]; omega
  obtain ⟨hw, -, -, hμ⟩ := hK t₂ h₁₂ le_rfl
  have h1 := fifeMu_pos (q := q) hw
  have h2 := fifeMu_le q ((r.s t₁).pc p)
  omega

end Podc.KBakery
