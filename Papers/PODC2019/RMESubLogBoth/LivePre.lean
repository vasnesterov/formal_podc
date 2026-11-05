import Papers.PODC2019.RMESubLogBoth.LiveDefs
import Papers.PODC2019.RMESubLogBoth.StepPC
import Papers.PODC2019.RMESubLogBoth.InvBasic

/-!
# Liveness, part 1: the recovery code before `RLock` terminates

After the last crash, every process executing lines 10, 16–23 of a recovery reaches line 24, the
critical section, or a fresh passage, and no process enters this code again.
-/

namespace Podc.RMESubLogBoth

variable {k : ℕ}

/-- Remaining steps in the recovery code before `RLock` (`0` outside it). -/
def preW (c : Cfg k) (q : Fin k) : ℕ :=
  match c.pc q with
  | .l10 => if c.node q = none then 1 else 9
  | .l18 _ => 8
  | .l18w _ => 7
  | .l19 _ => 6
  | .l23 _ _ => 4
  | .l22a _ => 3
  | .l22b => 2
  | _ => 0

lemma preW_step {c c' : Cfg k} {own : ℕ → ℕ} (hL : ∀ q, LI c own q) {p : Fin k}
    (h : Step c p c') : (preW c p = 0 → preW c' p = 0) ∧ (preW c p ≠ 0 → preW c' p < preW c p) := by
  have hLp := hL p
  unfold LI at hLp
  cases hpc : c.pc p with
  | rem =>
    rw [hpc] at hLp
    rcases step_l10 h (.inl hpc) with ⟨-, h'⟩ | ⟨x, hn, -⟩
    · simp [preW, h', hpc]
    · rw [hLp] at hn; cases hn
  | l10 =>
    rcases step_l10 h (.inr hpc) with ⟨hn, h'⟩ | ⟨x, hn, h'⟩
    · simp [preW, h', hpc, hn]
    · simp [preW, h', hpc, hn]
  | l11 => simp [preW, step_l11 h hpc, hpc]
  | l13 x => simp [preW, step_l13 h hpc, hpc]
  | l14 x m => simp [preW, step_l14 h hpc, hpc]
  | l15 x m => simp [preW, step_l15 h hpc, hpc]
  | l18 x => rcases step_l18 h hpc with h' | h' <;> simp [preW, h', hpc]
  | l18w x => simp [preW, step_l18w h hpc, hpc]
  | l19 x =>
    rcases step_l19 h hpc with h' | h' | ⟨v, h'⟩ <;> simp [preW, h', hpc]
  | l22a x => simp [preW, step_l22a h hpc, hpc]
  | l22b => simp [preW, (step_l22b h hpc).1, (step_l22b h hpc).2, hpc]
  | l23 x v => simp [preW, step_l23 h hpc, hpc]
  | l24 x v =>
    rcases step_l24 h hpc with ⟨h', -⟩ | ⟨h', -⟩ <;> simp [preW, h', hpc]
  | l30 x v => rcases step_l30 h hpc with h' | h' <;> simp [preW, h', hpc]
  | l31 x => simp [preW, step_l31 h hpc, hpc]
  | l33 x tl V E i =>
    rcases step_l33 h hpc with ⟨-, h'⟩ | ⟨-, a, h'⟩ | ⟨-, h'⟩ <;> simp [preW, h', hpc]
  | l35 x tl V E i a =>
    rcases step_l35 h hpc with ⟨-, h'⟩ | ⟨-, rfl⟩
    · simp [preW, h', hpc]
    · simp [preW, hpc]
  | l36 x tl V E i a => simp [preW, step_l36 h hpc, hpc]
  | l39 x tl V E => obtain ⟨_, _, h'⟩ := step_l39 h hpc; simp [preW, h', hpc]
  | l42 x tl V E mp tp hp dn =>
    rcases step_l42 h hpc with ⟨σ, -, -, h'⟩ | h' <;> simp [preW, h', hpc]
  | l43 x tl V E mp tp hp dn σ => rcases step_l43 h hpc with h' | h' <;> simp [preW, h', hpc]
  | l44 x tl V E mp tp hp dn σ => obtain ⟨_, h'⟩ := step_l44 h hpc; simp [preW, h', hpc]
  | l46 x tl V E mp tp hp =>
    rcases step_l46 h hpc with ⟨_, h'⟩ | ⟨_, h'⟩ <;> simp [preW, h', hpc]
  | l47 x s => simp [preW, step_l47 h hpc, hpc]
  | l49 x m => simp [preW, step_l49 h hpc, hpc]
  | rx x v => simp [preW, (step_rx h hpc).1, hpc]
  | l25 x v =>
    rw [hpc] at hLp
    obtain ⟨-, -, ⟨m, rfl⟩, -⟩ := hLp
    rcases step_l25 h hpc with ⟨-, h'⟩ | ⟨-, rfl⟩
    · simp [preW, h', hpc]
    · simp [preW, hpc]
  | l26 x => simp [preW, step_l26 h hpc, hpc]
  | cs x => simp [preW, step_cs h hpc, hpc]
  | l28 x => simp [preW, step_l28 h hpc, hpc]
  | l29 => simp [preW, step_l29 h hpc, hpc]

lemma preW_next {c c' : Cfg k} {own : ℕ → ℕ} (hL : ∀ q, LI c own q) {e : Ev k}
    (h : Next c e c') (hc : ∀ p, e ≠ .crash p) (q : Fin k) :
    preW c' q ≤ preW c q ∧ (preW c q = 0 → preW c' q = 0) ∧
      (e = .step q → preW c q ≠ 0 → preW c' q < preW c q) := by
  cases e with
  | crash p => exact absurd rfl (hc p)
  | step p =>
    by_cases hqp : q = p
    · subst hqp
      have := preW_step hL h
      refine ⟨?_, this.1, fun _ => this.2⟩
      by_cases h0 : preW c q = 0
      · rw [this.1 h0, h0]
      · exact (this.2 h0).le
    · have h1 : c'.pc q = c.pc q := Step.pc_other h hqp
      have h2 : c'.node q = c.node q := Step.node_other h hqp
      have : preW c' q = preW c q := by simp only [preW, h1, h2]
      refine ⟨this.le, fun h0 => this.trans h0, fun he => ?_⟩
      cases he; exact absurd rfl hqp

/-- After the last crash, eventually no process runs the recovery code before `RLock`. -/
theorem eventually_no_pre (r : Run k) (hF : Fair r) (hinv : ∀ t, Inv (r.cfg t)) {T : ℕ}
    (hT : CrashFreeFrom r T) (p0 : Fin k) :
    ∃ T1, T ≤ T1 ∧ ∀ t, T1 ≤ t → ∀ q, preW (r.cfg t) q = 0 := by
  classical
  have hstep : ∀ t, T ≤ t → ∀ q, preW (r.cfg (t + 1)) q ≤ preW (r.cfg t) q ∧
      (preW (r.cfg t) q = 0 → preW (r.cfg (t + 1)) q = 0) ∧
      (r.ev t = .step q → preW (r.cfg t) q ≠ 0 → preW (r.cfg (t + 1)) q < preW (r.cfg t) q) := by
    intro t ht q
    obtain ⟨own, -, hL⟩ := hinv t
    exact preW_next hL (r.next t) (fun p => hT t ht p) q
  let μ : ℕ → ℕ := fun t => ∑ q, preW (r.cfg t) q
  let Goal : ℕ → Prop := fun t => ∀ q, preW (r.cfg t) q = 0
  let S : ℕ → Finset (Fin k) := fun t => Finset.univ.filter (fun q => preW (r.cfg t) q ≠ 0)
  let d : ℕ → Fin k := fun t => if h : (S t).Nonempty then (S t).min' h else p0
  have hdS : ∀ t, ¬ Goal t → d t ∈ S t := by
    intro t hg
    have hne : (S t).Nonempty := by
      simp only [Goal, not_forall] at hg; obtain ⟨q, hq⟩ := hg; exact ⟨q, by simp [S, hq]⟩
    simp only [d, dif_pos hne]; exact Finset.min'_mem _ _
  have hmonoμ : ∀ t, T ≤ t → μ (t + 1) ≤ μ t := fun t ht =>
    Finset.sum_le_sum (fun q _ => (hstep t ht q).1)
  obtain ⟨t1, ht1, hg⟩ := eventually_of_rank r hF μ Goal d T
    (fun t ht _ _ => hmonoμ t ht)
    (by
      intro t ht hg hrem
      have := hdS t hg
      simp only [S, Finset.mem_filter] at this
      apply this.2
      simp [preW, hrem])
    (by
      intro t ht hg hev _
      rcases hev with hev | hev
      · have hd := hdS t hg
        simp only [S, Finset.mem_filter] at hd
        apply Finset.sum_lt_sum (fun q _ => (hstep t ht q).1)
        exact ⟨d t, Finset.mem_univ _, (hstep t ht (d t)).2.2 hev hd.2⟩
      · exact absurd hev (hT t ht _))
    (by
      intro t ht _ _ heq
      have hall : ∀ q, preW (r.cfg (t + 1)) q = preW (r.cfg t) q := by
        intro q
        have := (Finset.sum_eq_sum_iff_of_le (fun q _ => (hstep t ht q).1)).mp heq
        exact this q (Finset.mem_univ _)
      have : S (t + 1) = S t := by
        ext q; simp [S, hall q]
      simp only [d, this])
  refine ⟨t1, ht1, fun t ht q => ?_⟩
  induction t, ht using Nat.le_induction with
  | base => exact hg q
  | succ t ht' ih => exact (hstep t (by omega) q).2.1 ih

end Podc.RMESubLogBoth
