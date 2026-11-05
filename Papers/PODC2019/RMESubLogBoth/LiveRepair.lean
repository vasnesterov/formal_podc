import Papers.PODC2019.RMESubLogBoth.LivePre
import Papers.PODC2019.RMESubLogBoth.Safety

/-!
# Liveness, part 2: the recovery code and `RLock` terminate (frame and holder lemmas)

After the last crash, eventually no process is in the recovery code (lines 10, 16–24) or in the
critical section of `RLock` (lines 30–49 and its exit), and `RLock` is free.

This file contains the preliminary lemmas: the region `PC.Rec`, the invariant on the holder of
`RLock` (`holderOK_reach`), and frame lemmas for single steps.
-/

namespace Podc.RMESubLogBoth

variable {k : ℕ}

/-- The recovery/`RLock` region (Boolean version). -/
def PC.isRec : PC k → Bool
  | .l10 | .l18 _ | .l18w _ | .l19 _ | .l22a _ | .l22b | .l23 _ _ | .l24 _ _ => true
  | .l30 _ _ | .l31 _ | .l33 _ _ _ _ _ | .l35 _ _ _ _ _ _ | .l36 _ _ _ _ _ _ | .l39 _ _ _ _
  | .l42 _ _ _ _ _ _ _ _ | .l43 _ _ _ _ _ _ _ _ _ | .l44 _ _ _ _ _ _ _ _ _
  | .l46 _ _ _ _ _ _ _ | .l47 _ _ | .l49 _ _ | .rx _ _ => true
  | _ => false

/-- The recovery/`RLock` region: lines 10 (after a crash), 18, 19, 22, 23, 24 of the recovery
code and every program counter in the critical section of `RLock` (`PC.InR`). -/
def PC.Rec (q : PC k) : Prop := q.isRec = true

instance (q : PC k) : Decidable q.Rec := inferInstanceAs (Decidable (_ = true))

lemma PC.rec_of_InR {q : PC k} (h : q.InR) : q.Rec := by
  cases q <;> simp_all [PC.InR, PC.Rec, PC.isRec]

/-- Outside the code before `RLock`, the region consists of line 24 and the CS of `RLock`. -/
lemma rec_cases {c : Cfg k} {q : Fin k} (h0 : preW c q = 0) (h : (c.pc q).Rec) :
    (c.pc q).InR ∨ ∃ y v, c.pc q = .l24 y v := by
  cases hq : c.pc q <;> simp_all [preW, PC.InR, PC.Rec, PC.isRec]
  split_ifs at h0

/-! ### The holder of `RLock` -/

/-- The holder of `RLock` crashed in its CS and runs the recovery code towards line 24 (its node
is marked `&Crash` or points to a node, so it gets back to line 24). -/
def HolderPre (c : Cfg k) (h : Fin k) : Prop :=
  ∃ y, c.node h = some y ∧ (c.pred y = .crash ∨ ∃ m, c.pred y = .node m) ∧
    (c.pc h = .l10 ∨ c.pc h = .l18 y ∨ c.pc h = .l19 y ∨
      ∃ v, c.pc h = .l23 y v ∨ c.pc h = .l24 y v)

/-- The holder of `RLock` is in its CS or on the way back to it after a crash. -/
def HolderOK (c : Cfg k) : Prop := ∀ h, c.holder = some h → (c.pc h).InR ∨ HolderPre c h

lemma li_InR {c : Cfg k} {own : ℕ → ℕ} {q : Fin k} (hL : LI c own q) (h : (c.pc q).InR) :
    ∃ y, c.node q = some y ∧ (c.pred y = .crash ∨ ∃ m, c.pred y = .node m) := by
  unfold LI at hL
  cases hq : c.pc q <;> simp only [hq, PC.InR] at h hL
  all_goals first
    | exact absurd h id
    | (obtain ⟨h1, h2, h3, -⟩ := hL; subst h2; exact ⟨_, h1, h3⟩)
    | (obtain ⟨h1, h2, -⟩ := hL; exact ⟨_, h1, .inl h2⟩)
    | (obtain ⟨h1, h2, ⟨m, rfl⟩, -⟩ := hL; exact ⟨_, h1, .inr ⟨m, h2⟩⟩)

/-- How the holder of `RLock` changes. -/
lemma step_holder {c c' : Cfg k} {p : Fin k} (h : Step c p c') (hne : c'.holder ≠ c.holder) :
    (∃ x v, c.pc p = .l24 x v ∧ (c.holder = none ∨ c.holder = some p) ∧ c'.holder = some p ∧
      c'.pc p = .l30 x v) ∨ ∃ x v, c.pc p = .rx x v ∧ c'.holder = none := by
  cases h <;> simp_all [Cfg.setPc]

lemma step_InR {c c' : Cfg k} {p : Fin k} (h : Step c p c') (hp : (c.pc p).InR) :
    ((c'.pc p).InR ∧ c'.holder = c.holder) ∨ ∃ x v, c.pc p = .rx x v ∧ c'.holder = none := by
  have hhold : (∀ x v, c.pc p ≠ .l24 x v) → (∀ x v, c.pc p ≠ .rx x v) →
      c'.holder = c.holder := by
    intro h1 h2
    by_contra hne
    rcases step_holder h hne with ⟨x, v, h3, -⟩ | ⟨x, v, h3, -⟩
    · exact h1 x v h3
    · exact h2 x v h3
  cases hpc : c.pc p with
  | rx x v => exact .inr ⟨x, v, rfl, (step_rx h hpc).2⟩
  | l30 x v =>
    refine .inl ⟨?_, hhold (by simp [hpc]) (by simp [hpc])⟩
    rcases step_l30 h hpc with h' | h' <;> simp [h', PC.InR]
  | l31 x => exact .inl ⟨by simp [step_l31 h hpc, PC.InR], hhold (by simp [hpc]) (by simp [hpc])⟩
  | l33 x tl V E i =>
    refine .inl ⟨?_, hhold (by simp [hpc]) (by simp [hpc])⟩
    rcases step_l33 h hpc with ⟨-, h'⟩ | ⟨-, a, h'⟩ | ⟨-, h'⟩ <;> simp [h', PC.InR]
  | l35 x tl V E i a =>
    refine .inl ⟨?_, hhold (by simp [hpc]) (by simp [hpc])⟩
    rcases step_l35 h hpc with ⟨-, h'⟩ | ⟨-, rfl⟩
    · simp [h', PC.InR]
    · simp [hpc, PC.InR]
  | l36 x tl V E i a => exact .inl ⟨by simp [step_l36 h hpc, PC.InR], hhold (by simp [hpc]) (by simp [hpc])⟩
  | l39 x tl V E =>
    refine .inl ⟨?_, hhold (by simp [hpc]) (by simp [hpc])⟩
    obtain ⟨_, _, h'⟩ := step_l39 h hpc; simp [h', PC.InR]
  | l42 x tl V E mp tp hp' dn =>
    refine .inl ⟨?_, hhold (by simp [hpc]) (by simp [hpc])⟩
    rcases step_l42 h hpc with ⟨σ, -, -, h'⟩ | h' <;> simp [h', PC.InR]
  | l43 x tl V E mp tp hp' dn σ =>
    refine .inl ⟨?_, hhold (by simp [hpc]) (by simp [hpc])⟩
    rcases step_l43 h hpc with h' | h' <;> simp [h', PC.InR]
  | l44 x tl V E mp tp hp' dn σ =>
    refine .inl ⟨?_, hhold (by simp [hpc]) (by simp [hpc])⟩
    obtain ⟨_, h'⟩ := step_l44 h hpc; simp [h', PC.InR]
  | l46 x tl V E mp tp hp' =>
    refine .inl ⟨?_, hhold (by simp [hpc]) (by simp [hpc])⟩
    rcases step_l46 h hpc with ⟨_, h'⟩ | ⟨_, h'⟩ <;> simp [h', PC.InR]
  | l47 x s => exact .inl ⟨by simp [step_l47 h hpc, PC.InR], hhold (by simp [hpc]) (by simp [hpc])⟩
  | l49 x m => exact .inl ⟨by simp [step_l49 h hpc, PC.InR], hhold (by simp [hpc]) (by simp [hpc])⟩
  | _ => simp [hpc, PC.InR] at hp

lemma holderPre_step {c c' : Cfg k} {h : Fin k} (hs : Step c h c') (hpre : HolderPre c h) :
    (c'.pc h).InR ∨ HolderPre c' h := by
  obtain ⟨y, hn, hpr, hpc⟩ := hpre
  rcases hpr with hpr | ⟨m, hpr⟩ <;>
  rcases hpc with hpc | hpc | hpc | ⟨v, hpc | hpc⟩ <;> cases hs <;>
    simp_all [Cfg.setPc, HolderPre, PC.InR]

lemma holderOK_next {c c' : Cfg k} (hI : Inv c) (hH : HolderOK c) {e : Ev k} (he : Next c e c') :
    HolderOK c' := by
  obtain ⟨own, hG, hL⟩ := hI
  intro h hh
  cases e with
  | crash p =>
    change c' = c.crash p at he; subst he
    simp only [Cfg.crash, Cfg.setPc_holder] at hh
    by_cases hp : h = p
    · subst hp
      right
      rcases hH h hh with hR | ⟨y, hn, hpr, -⟩
      · obtain ⟨y, hn, hpr⟩ := li_InR (hL h) hR
        exact ⟨y, by simpa [Cfg.crash] using hn, by simpa [Cfg.crash] using hpr,
          .inl (by simp [Cfg.crash])⟩
      · exact ⟨y, by simpa [Cfg.crash] using hn, by simpa [Cfg.crash] using hpr,
          .inl (by simp [Cfg.crash])⟩
    · simp only [HolderPre, Cfg.crash, Cfg.setPc_pc_ne _ _ hp, Cfg.setPc_node, Cfg.setPc_pred]
      rcases hH h hh with hR | ⟨y, hn, hpr, hpc⟩
      · exact .inl hR
      · exact .inr ⟨y, hn, hpr, hpc⟩
  | step p =>
    change Step c p c' at he
    by_cases hch : c'.holder = c.holder
    · have hh0 : c.holder = some h := hch ▸ hh
      by_cases hp : h = p
      · subst hp
        rcases hH h hh0 with hR | hpre
        · rcases step_InR he hR with ⟨h1, -⟩ | ⟨x, v, -, h2⟩
          · exact .inl h1
          · rw [h2] at hh; cases hh
        · exact holderPre_step he hpre
      · have hpc : c'.pc h = c.pc h := Step.pc_other he hp
        have hnd : c'.node h = c.node h := Step.node_other he hp
        rw [hpc]
        rcases hH h hh0 with hR | ⟨y, hn, hpr, hpc'⟩
        · exact .inl hR
        · have hpy : c'.pred y = c.pred y := Step.pred_other ⟨own, hG, hL⟩ he hp hn
          right
          refine ⟨y, hnd ▸ hn, hpy ▸ hpr, ?_⟩
          simpa [hpc] using hpc'
    · rcases step_holder he hch with ⟨x, v, -, -, h1, h2⟩ | ⟨x, v, -, h1⟩
      · rw [h1] at hh; cases hh; left; rw [h2]; trivial
      · rw [h1] at hh; cases hh

/-- **Holder invariant.** In every reachable configuration the holder of `RLock` is in the CS of
`RLock`, or it crashed there and is on its way back to line 24. -/
theorem holderOK_reach {c : Cfg k} (h : Reach c) : HolderOK c := by
  induction h with
  | init => intro h hh; simp [Cfg.init] at hh
  | next e hr hn ih => exact holderOK_next (inv_reach hr) ih hn

end Podc.RMESubLogBoth
