import Papers.PODC2019.RMESubLogBoth.LiveToken5

/-!
# Liveness, part 4: a process outside the recovery code reaches the CS
-/

namespace Podc.RMESubLogBoth

variable {k : ℕ}

open Relation Classical

/-- Phase 2 is kept until the CS. -/
lemma ph2_next {c c' : Cfg k} (hc : Reach c) {e : Ev k} (h : Next c e c') {p : Fin k} {yp : ℕ}
    (hph : Ph2 c p yp) (hcr : e ≠ .crash p) : Ph2 c' p yp ∨ c'.pc p = .cs yp := by
  obtain ⟨hn, hpc⟩ := hph
  by_cases he : e = .step p
  · subst he
    have h' : Step c p c' := h
    obtain ⟨own, hG, hL⟩ := inv_reach hc
    have hnode : c'.node p = c.node p := by
      rcases hpc with ⟨m, h1⟩ | ⟨m, h1⟩ | ⟨v, h1⟩ | h1 <;> cases h' <;> simp_all [Cfg.setPc]
    rcases hpc with ⟨m, h1⟩ | ⟨m, h1⟩ | ⟨v, h1⟩ | h1
    · exact .inl ⟨hnode ▸ hn, .inr (.inl ⟨m, step_l14 h' h1⟩)⟩
    · exact .inl ⟨hnode ▸ hn, .inr (.inr (.inl ⟨_, step_l15 h' h1⟩))⟩
    · have hLp := hL p; unfold LI at hLp; rw [h1] at hLp
      obtain ⟨-, -, ⟨m, rfl⟩, -⟩ := hLp
      rcases step_l25 h' h1 with ⟨-, h2⟩ | ⟨-, rfl⟩
      · exact .inl ⟨hnode ▸ hn, .inr (.inr (.inr h2))⟩
      · exact .inl ⟨hn, .inr (.inr (.inl ⟨_, h1⟩))⟩
    · exact .inr (step_l26 h' h1)
  · have h1 := Next.pc_other h he hcr
    have h2 := Next.node_other h he
    exact .inl ⟨h2 ▸ hn, h1 ▸ hpc⟩

/-- **Phase 2.** After the last crash, once nobody runs the recovery code or `RLock`, a process
at lines 14–26 eventually enters the CS. -/
theorem phase2_cs (r : Run k) (hF : Fair r) {T : ℕ} (hT : CrashFreeFrom r T)
    (hNR : ∀ t, T ≤ t → NoRec (r.cfg t)) {p : Fin k} {yp : ℕ} {t0 : ℕ} (ht0 : T ≤ t0)
    (hph : Ph2 (r.cfg t0) p yp) : ∃ t, t0 ≤ t ∧ (r.cfg t).InCS p := by
  let Goal : ℕ → Prop := fun t => ∃ t', t0 ≤ t' ∧ t' ≤ t ∧ (r.cfg t').InCS p
  have hph' : ∀ t, t0 ≤ t → ¬ Goal t → Ph2 (r.cfg t) p yp := by
    intro t ht
    induction t, ht using Nat.le_induction with
    | base => intro _; exact hph
    | succ t ht ih =>
      intro hg
      have hg' : ¬ Goal t := fun ⟨t', h1, h2, h3⟩ => hg ⟨t', h1, by omega, h3⟩
      rcases ph2_next (r.reach t) (r.next t) (ih hg') (hT t (by omega) p) with h1 | h1
      · exact h1
      · exact absurd ⟨t + 1, by omega, le_rfl, ⟨yp, h1⟩⟩ hg
  have hHO : ∀ t, t0 ≤ t → ¬ Goal t → ∃ s, HO (r.cfg t) s := by
    intro t ht hg
    obtain ⟨own, hG, hL⟩ := inv_reach (r.reach t)
    obtain ⟨s, x, hs, hx, -⟩ := (hph' t ht hg).holder hG hL (hNR t (by omega))
    exact ⟨s, x, hs, hx⟩
  let d : ℕ → Fin k := fun t => if h : ∃ s, HO (r.cfg t) s then h.choose else p
  have hdHO : ∀ t, t0 ≤ t → ¬ Goal t → HO (r.cfg t) (d t) := by
    intro t ht hg
    have h := hHO t ht hg
    simp only [d, dif_pos h]; exact h.choose_spec
  have hstep := fun t (ht : t0 ≤ t) (hg : ¬ Goal t) =>
    token_step (inv_reach (r.reach t)) (inv_reach (r.reach (t + 1))) (hNR t (by omega))
      (s := match r.ev t with | .step s => s | .crash s => s)
      (by
        have := r.next t
        cases he : r.ev t with
        | step s => rw [he] at this; exact this
        | crash s => exact absurd he (hT t (by omega) s))
      (hph' t ht hg)
  have hgoal_cs : ∀ t, t0 ≤ t → (r.cfg (t + 1)).pc p = .cs yp → Goal (t + 1) :=
    fun t ht h => ⟨t + 1, by omega, le_rfl, ⟨yp, h⟩⟩
  obtain ⟨t, ht, hg⟩ := eventually_of_rank r hF (fun t => tokMu (r.cfg t) yp) Goal d t0
    (by
      intro t ht hg hg'
      by_cases hs : HO (r.cfg t) (match r.ev t with | .step s => s | .crash s => s)
      · rcases (hstep t ht hg).2 hs with h1 | h1
        · exact h1.le
        · exact absurd (hgoal_cs t ht h1) hg'
      · exact ((hstep t ht hg).1 hs).1.le)
    (by
      intro t ht hg hrem
      obtain ⟨own, hG, hL⟩ := inv_reach (r.reach t)
      have := HO.pc hG hL (hNR t (by omega)) (hdHO t ht hg)
      rw [hrem] at this; exact this rfl)
    (by
      intro t ht hg hev hg'
      rcases hev with hev | hev
      · have hs := hdHO t ht hg
        have hs' : HO (r.cfg t) (match r.ev t with | .step s => s | .crash s => s) := by
          rw [hev]; exact hs
        rcases (hstep t ht hg).2 hs' with h1 | h1
        · exact h1
        · exact absurd (hgoal_cs t ht h1) hg'
      · exact absurd hev (hT t (by omega) _))
    (by
      intro t ht hg hg' heq
      have hs : ¬ HO (r.cfg t) (match r.ev t with | .step s => s | .crash s => s) := by
        intro hs
        rcases (hstep t ht hg).2 hs with h1 | h1
        · omega
        · exact hg' (hgoal_cs t ht h1)
      have hiff := ((hstep t ht hg).1 hs).2
      obtain ⟨own, hG, -⟩ := inv_reach (r.reach t)
      exact HO.unique hG ((hiff _).mp (hdHO (t + 1) (by omega) hg')) (hdHO t ht hg))
  obtain ⟨t', h1, h2, h3⟩ := hg
  exact ⟨t', h1, h3⟩

end Podc.RMESubLogBoth
