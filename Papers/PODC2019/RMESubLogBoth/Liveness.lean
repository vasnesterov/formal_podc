import Papers.PODC2019.RMESubLogBoth.LivePhase
import Papers.PODC2019.RMESubLogBoth.LiveRepair4

/-!
# Starvation freedom (Lemma 5)
-/

namespace Podc.RMESubLogBoth

variable {k : ℕ}

lemma noRec_of {c : Cfg k} (h : ∀ q, ¬ (c.pc q).Rec) : NoRec c := by
  intro q
  have hq := h q
  cases hpc : c.pc q <;> rw [hpc] at hq <;> simp_all [PC.Rec, PC.isRec, preW, PC.InR]

/-- The Try section is left only into the CS. -/
lemma try_next {c c' : Cfg k} (hc : Reach c) {e : Ev k} (h : Next c e c') {p : Fin k}
    (hcr : e ≠ .crash p) (ht : (c.pc p).InTry) : (c'.pc p).InTry ∨ ∃ x, c'.pc p = .cs x := by
  by_cases he : e = .step p
  · subst he
    have h' : Step c p c' := h
    obtain ⟨own, hG, hL⟩ := inv_reach hc
    have hLp := hL p; unfold LI at hLp
    cases hpc : c.pc p with
    | rem => rw [hpc] at ht; simp [PC.InTry] at ht
    | cs x => rw [hpc] at ht; simp [PC.InTry] at ht
    | l28 x => rw [hpc] at ht; simp [PC.InTry] at ht
    | l29 => rw [hpc] at ht; simp [PC.InTry] at ht
    | l10 => rcases step_l10 h' (.inr hpc) with ⟨-, h2⟩ | ⟨x, -, h2⟩ <;> simp [h2, PC.InTry]
    | l11 => simp [step_l11 h' hpc, PC.InTry]
    | l13 x => simp [step_l13 h' hpc, PC.InTry]
    | l14 x m => simp [step_l14 h' hpc, PC.InTry]
    | l15 x m => simp [step_l15 h' hpc, PC.InTry]
    | l18 x => rcases step_l18 h' hpc with h2 | h2 <;> simp [h2, PC.InTry]
    | l18w x => simp [step_l18w h' hpc, PC.InTry]
    | l19 x => rcases step_l19 h' hpc with h2 | h2 | ⟨v, h2⟩ <;> simp [h2, PC.InTry]
    | l22a x => simp [step_l22a h' hpc, PC.InTry]
    | l22b => simp [(step_l22b h' hpc).1, PC.InTry]
    | l23 x v => simp [step_l23 h' hpc, PC.InTry]
    | l24 x v => rcases step_l24 h' hpc with ⟨h2, -⟩ | ⟨h2, -⟩ <;> simp [h2, PC.InTry]
    | l30 x v => rcases step_l30 h' hpc with h2 | h2 <;> simp [h2, PC.InTry]
    | l31 x => simp [step_l31 h' hpc, PC.InTry]
    | l33 x tl V E i =>
      rcases step_l33 h' hpc with ⟨-, h2⟩ | ⟨-, a, h2⟩ | ⟨-, h2⟩ <;> simp [h2, PC.InTry]
    | l35 x tl V E i a =>
      rcases step_l35 h' hpc with ⟨-, h2⟩ | ⟨-, rfl⟩
      · simp [h2, PC.InTry]
      · simp [hpc, PC.InTry]
    | l36 x tl V E i a => simp [step_l36 h' hpc, PC.InTry]
    | l39 x tl V E => obtain ⟨_, _, h2⟩ := step_l39 h' hpc; simp [h2, PC.InTry]
    | l42 x tl V E mp tp hp dn =>
      rcases step_l42 h' hpc with ⟨σ, -, -, h2⟩ | h2 <;> simp [h2, PC.InTry]
    | l43 x tl V E mp tp hp dn σ => rcases step_l43 h' hpc with h2 | h2 <;> simp [h2, PC.InTry]
    | l44 x tl V E mp tp hp dn σ => obtain ⟨_, h2⟩ := step_l44 h' hpc; simp [h2, PC.InTry]
    | l46 x tl V E mp tp hp =>
      rcases step_l46 h' hpc with ⟨_, h2⟩ | ⟨_, h2⟩ <;> simp [h2, PC.InTry]
    | l47 x s => simp [step_l47 h' hpc, PC.InTry]
    | l49 x m => simp [step_l49 h' hpc, PC.InTry]
    | rx x v => simp [(step_rx h' hpc).1, PC.InTry]
    | l25 x v =>
      rw [hpc] at hLp
      obtain ⟨-, -, ⟨m, rfl⟩, -⟩ := hLp
      rcases step_l25 h' hpc with ⟨-, h2⟩ | ⟨-, rfl⟩
      · simp [h2, PC.InTry]
      · simp [hpc, PC.InTry]
    | l26 x => simp [step_l26 h' hpc, PC.InTry]
  · left; rw [Next.pc_other h he hcr]; exact ht

/-- The next step of `p`. -/
lemma next_own_step (r : Run k) (hF : Fair r) {p : Fin k} {t0 : ℕ}
    (hnc : ∀ t, t0 ≤ t → r.ev t ≠ .crash p) (hrem : (r.cfg t0).pc p ≠ .rem) :
    ∃ t1, t0 ≤ t1 ∧ r.ev t1 = .step p ∧ (r.cfg t1).pc p = (r.cfg t0).pc p ∧
      (r.cfg t1).node p = (r.cfg t0).node p := by
  classical
  have hex : ∃ t', t0 ≤ t' ∧ r.ev t' = .step p := by
    obtain ⟨t', h1, h2⟩ := hF p t0 hrem
    rcases h2 with h2 | h2
    · exact ⟨t', h1, h2⟩
    · exact absurd h2 (hnc t' h1)
  let n := Nat.find hex
  have hn := Nat.find_spec hex
  have hmin : ∀ t, t0 ≤ t → t < n → r.ev t ≠ .step p := fun t h1 h2 h3 =>
    Nat.find_min hex h2 ⟨h1, h3⟩
  refine ⟨n, hn.1, hn.2, ?_⟩
  have key : ∀ t, t0 ≤ t → t ≤ n → (r.cfg t).pc p = (r.cfg t0).pc p ∧
      (r.cfg t).node p = (r.cfg t0).node p := by
    intro t ht htn
    induction t, ht using Nat.le_induction with
    | base => exact ⟨rfl, rfl⟩
    | succ t ht ih =>
      obtain ⟨h1, h2⟩ := ih (by omega)
      have hs := hmin t ht (by omega)
      exact ⟨by rw [Next.pc_other (r.next t) hs (hnc t ht), h1],
        by rw [Next.node_other (r.next t) hs, h2]⟩
  exact key n hn.1 le_rfl

/-- **Lemma 5 (Starvation Freedom).** If the total number of crashes is finite and a process is
in the Try section and does not crash any more, it later enters the CS. -/
theorem starvation_freedom (r : Run k) (hF : Fair r) (hC : FinCrash r) (p : Fin k) (t : ℕ)
    (htry : ((r.cfg t).pc p).InTry) (hnc : ∀ t', t ≤ t' → r.ev t' ≠ .crash p) :
    ∃ t', t ≤ t' ∧ (r.cfg t').InCS p := by
  obtain ⟨T, hT⟩ := hC
  have hT' : CrashFreeFrom r (max T t) := fun s hs q => hT s (by omega) q
  obtain ⟨T1, hT1, hNR⟩ := eventually_no_rec r hF hT' p
  have hNR' : ∀ s, T1 ≤ s → NoRec (r.cfg s) := fun s hs => noRec_of (hNR s hs).1
  have hT1' : CrashFreeFrom r T1 := fun s hs q => hT s (by omega) q
  -- `p` stays in Try until the CS
  have hstay : ∀ s, t ≤ s → (∃ t', t ≤ t' ∧ t' ≤ s ∧ (r.cfg t').InCS p) ∨
      ((r.cfg s).pc p).InTry := by
    intro s hs
    induction s, hs using Nat.le_induction with
    | base => exact .inr htry
    | succ s hs ih =>
      rcases ih with ⟨t', h1, h2, h3⟩ | ih
      · exact .inl ⟨t', h1, by omega, h3⟩
      · rcases try_next (r.reach s) (r.next s) (hnc s hs) ih with h1 | ⟨x, h1⟩
        · exact .inr h1
        · exact .inl ⟨s + 1, by omega, le_rfl, ⟨x, h1⟩⟩
  rcases hstay T1 (by omega) with ⟨t', h1, -, h3⟩ | htry1
  · exact ⟨t', h1, h3⟩
  -- at `T1`, `p` is at line 11, 13, 14, 15, 25 or 26
  have hcsd : ∀ s, T1 ≤ s → Ph2 (r.cfg s) p ((r.cfg s).node p |>.getD 0) →
      ∃ t', t ≤ t' ∧ (r.cfg t').InCS p := by
    intro s hs hph
    obtain ⟨t', h1, h2⟩ := phase2_cs r hF hT1' hNR' hs hph
    exact ⟨t', by omega, h2⟩
  have hph_of : ∀ s, T1 ≤ s → (∃ y m, (r.cfg s).pc p = .l14 y m) →
      ∃ t', t ≤ t' ∧ (r.cfg t').InCS p := by
    rintro s hs ⟨y, m, h1⟩
    obtain ⟨own, -, hL⟩ := inv_reach (r.reach s)
    have := (hL p).node_of_pc_l14 h1
    exact hcsd s hs ⟨by rw [this.1]; rfl, .inl ⟨m, by rw [this.1]; exact h1⟩⟩
  -- from line 13
  have from13 : ∀ s, T1 ≤ s → (∃ y, (r.cfg s).pc p = .l13 y) →
      ∃ t', t ≤ t' ∧ (r.cfg t').InCS p := by
    rintro s hs ⟨y, h1⟩
    obtain ⟨t1, h2, h3, h4, -⟩ := next_own_step r hF (t0 := s) (fun u hu => hnc u (by omega))
      (by rw [h1]; simp)
    have hn := r.next t1; rw [h3] at hn
    exact hph_of (t1 + 1) (by omega) ⟨_, _, step_l13 hn (h4.trans h1)⟩
  obtain ⟨own, -, hL⟩ := inv_reach (r.reach T1)
  have hLp := hL p; unfold LI at hLp
  have hpl := (hNR' T1 le_rfl).plain p
  cases hpc : (r.cfg T1).pc p with
  | l11 =>
    obtain ⟨t1, h2, h3, h4, -⟩ := next_own_step r hF (t0 := T1) (fun u hu => hnc u (by omega))
      (by rw [hpc]; simp)
    have hn := r.next t1; rw [h3] at hn
    exact from13 (t1 + 1) (by omega) ⟨_, step_l11 hn (h4.trans hpc)⟩
  | l13 y => exact from13 T1 le_rfl ⟨y, hpc⟩
  | l14 y m => exact hph_of T1 le_rfl ⟨y, m, hpc⟩
  | l15 y m =>
    rw [hpc] at hLp
    exact hcsd T1 le_rfl ⟨by rw [hLp.1]; rfl, .inr (.inl ⟨m, by rw [hLp.1, hpc]; rfl⟩)⟩
  | l25 y v =>
    rw [hpc] at hLp
    exact hcsd T1 le_rfl ⟨by rw [hLp.1]; rfl, .inr (.inr (.inl ⟨v, by rw [hLp.1, hpc]; rfl⟩))⟩
  | l26 y =>
    rw [hpc] at hLp
    exact hcsd T1 le_rfl ⟨by rw [hLp.1]; rfl, .inr (.inr (.inr (by rw [hLp.1, hpc]; rfl)))⟩
  | _ => rw [hpc] at hpl htry1; simp [PC.Plain, PC.InTry] at hpl htry1

end Podc.RMESubLogBoth
