import Papers.PODC2010.KBakery.RunLemmas

/-!
# k-FCFS (Lemma 6 of the paper; Lemma 5.6 of the thesis)

*For any set `Y` of `k` processes, if all processes in `Y` finish the doorway before a process
`p` starts the doorway, then `p` does not enter the CS before at least one process in `Y` enters
the CS.*

We state it for both variants of the algorithm (the thesis' Theorem 5.20 also claims it for the
FIFE algorithm).
-/

set_option linter.unusedSectionVars false

namespace Podc.KBakery

open Finset

variable {P : Type} [LinearOrder P] [Fintype P]
variable {fife : Bool} {k : ℕ}

/-- Progress of `p` in its passage relative to the tickets `T q` of the processes `q ∈ Y`. -/
def FcfsQ (Y : Finset P) (T : P → ℕ) (c : PC P) (tk : ℕ) : Prop :=
  match c with
  | .ncs | .d14 _ => True
  | .d15 acc rem => ∀ q ∈ Y, q ∉ rem → T q ≤ acc
  | .ex _ => False
  | _ => ∀ q ∈ Y, T q < tk

/-- **k-FCFS** (Lemma 6 / Lemma 5.6). At time `t₀` the process `p` is in the NCS (it has not
started the doorway of its next passage) and every `q ∈ Y` has finished its doorway but not yet
entered the CS; `|Y| = k`. If `p` is in the CS at a time `t₁ ≥ t₀`, then some `q ∈ Y` is in the CS
at some time in `[t₀, t₁]`. -/
theorem k_fcfs (r : Run fife k P) (Y : Finset P) (hY : Y.card = k) (p : P) (t₀ : ℕ)
    (hp₀ : (r.s t₀).pc p = .ncs) (hY₀ : ∀ q ∈ Y, ((r.s t₀).pc q).InWaiting)
    (t₁ : ℕ) (h₀₁ : t₀ ≤ t₁) (hp₁ : (r.s t₁).pc p = .cs) :
    ∃ q ∈ Y, ∃ t, t₀ ≤ t ∧ t ≤ t₁ ∧ (r.s t).pc q = .cs := by
  classical
  by_contra hcon
  push Not at hcon
  -- the processes of `Y` stay in the waiting room with fixed tickets
  have hA : ∀ q ∈ Y, ∀ t, t₀ ≤ t → t ≤ t₁ →
      ((r.s t).pc q).InWaiting ∧ (r.s t).ticket q = (r.s t₀).ticket q := fun q hq =>
    r.waiting_interval (hY₀ q hq) (fun t h0 h1 => hcon q hq t h0 h1)
  set T : P → ℕ := fun q => (r.s t₀).ticket q
  -- first time at or after `t₀` at which `p` is in the CS
  have hex : ∃ n, (r.s (t₀ + n)).pc p = .cs := ⟨t₁ - t₀, by rw [Nat.add_sub_cancel' h₀₁]; exact hp₁⟩
  set n := Nat.find hex with hn
  have hn1 : (r.s (t₀ + n)).pc p = .cs := Nat.find_spec hex
  have hn2 : ∀ m < n, (r.s (t₀ + m)).pc p ≠ .cs := fun m hm => Nat.find_min hex hm
  have hnle : n ≤ t₁ - t₀ := Nat.find_min' hex (by rw [Nat.add_sub_cancel' h₀₁]; exact hp₁)
  -- `p`'s progress
  have hQ : ∀ m ≤ n, FcfsQ Y T ((r.s (t₀ + m)).pc p) ((r.s (t₀ + m)).ticket p) := by
    intro m hm
    induction m with
    | zero => simp [hp₀, FcfsQ]
    | succ m ih =>
      have ih := ih (by omega)
      have hncs := hn2 m (by omega)
      have hYm : ∀ q ∈ Y, (r.s (t₀ + m)).ticket q = T q := fun q hq =>
        (hA q hq (t₀ + m) (by omega) (by omega)).2
      have hpY : ∀ q ∈ Y, q ≠ p := by
        intro q hq hqp; subst hqp
        have := (hA q hq t₀ le_rfl h₀₁).1; rw [hp₀] at this; simp [PC.InWaiting] at this
      rw [show t₀ + (m + 1) = t₀ + m + 1 by omega]
      by_cases hs : r.sched (t₀ + m) = p
      · rw [r.step (t₀ + m), stepAt_pc, stepAt_ticket, hs]
        have hadm := r.adm (t₀ + m)
        rw [hs] at hadm
        rcases hpc : (r.s (t₀ + m)).pc p with _ | rem' | ⟨acc', rem'⟩ | rem' | ⟨pred, cap⟩ |
          ⟨pred, rem'⟩ | ⟨pred, rem', cap⟩ | rem' | _ | rem' <;>
          simp only [hpc, FcfsQ] at ih hncs <;>
          simp only [core, hpc] <;> (try split_ifs) <;> (try cases fife) <;>
          simp [FcfsQ] <;> (try exact ih) <;> (try simp at hncs) <;> rename_i hi <;>
          intro q hq
        · intro hqr
          by_cases hqi : q = r.choice (t₀ + m)
          · subst hqi; rw [← hYm _ hq]; exact Or.inr le_rfl
          · exact Or.inl (ih q hq (hqr hqi))
        · intro hqr
          by_cases hqi : q = r.choice (t₀ + m)
          · subst hqi; rw [← hYm _ hq]; exact Or.inr le_rfl
          · exact Or.inl (ih q hq (hqr hqi))
        all_goals
          have h0 := admissible_of_not_mem hadm (by simpa [hpc, PC.rem] using hi)
          simp only [hpc, PC.rem] at h0
          subst h0
          exact ih q hq (by simp)
      · rw [r.pc_succ_of_ne hs, r.ticket_succ_of_ne hs]; exact ih
  have hfin := hQ n le_rfl
  rw [hn1] at hfin
  simp only [FcfsQ] at hfin
  -- now `p` is past its loop, so fewer than `k` processes are unsafe for it
  have h4 := (r.inv (t₀ + n)).s4 p (by simp [hn1, PC.Qual])
  have hsub : Y ⊆ U (r.s (t₀ + n)) ((r.s (t₀ + n)).ticket p) p := by
    intro q hq
    obtain ⟨hw, htk⟩ := hA q hq (t₀ + n) (by omega) (by omega)
    rw [mem_U]
    refine ⟨?_, fun hsafe => ?_⟩
    · rintro rfl; rw [hn1] at hw; simp [PC.InWaiting] at hw
    · have hl : lexLt ((r.s (t₀ + n)).ticket p) p ((r.s (t₀ + n)).ticket q) q := by
        unfold Safe at hsafe
        rcases hpc : (r.s (t₀ + n)).pc q with _ | rem' | ⟨acc', rem'⟩ | rem' | ⟨pred, cap⟩ |
          ⟨pred, rem'⟩ | ⟨pred, rem', cap⟩ | rem' | _ | rem' <;>
          simp only [hpc, PC.InWaiting] at hw hsafe <;> exact hsafe
      have := hfin q hq
      rw [htk] at hl
      rcases hl with hl | ⟨hl, -⟩ <;> simp only [T] at this <;> omega
  have := card_le_card hsub
  omega

end Podc.KBakery
