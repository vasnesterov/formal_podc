import Papers.PODC2010.GroupMutexLogRMR.InvLemmas

/-!
# Frame lemma for local steps

A *local* step of `p` changes only `p`'s local state and `p`'s links. `LI_frame_local` derives the
per-process clauses of every other process `y ≠ p` from a few obligations about `p`'s old and new
local state (`p` stays a valid witness of the existential clauses, or the context excludes it; `p`
does not violate the universal clauses).
-/

namespace Podc.GroupMutexLogRMR

variable {n : ℕ} {J : Type} [DecidableEq J]

/-- `p` keeps its session, side and time-stamp. -/
def SameSDT (l l' : Loc J) : Prop := l'.s = l.s ∧ l'.d = l.d ∧ l'.tm = l.tm

/-- The constraint of the clause `win` on another process `z`, for a winner of session `s`. -/
def WinOK (c : Cfg n J) (s : J) (z : Fin n) : Prop :=
  ¬ PC.btw .l16_10 .l16_14 (c.loc z).pc ∧
  (PC.btw .l11 .l16_3 (c.loc z).pc → (c.loc z).pc = .l11 ∨ ((c.loc z).pc = .l12 ∧ (c.loc z).a.1 = s)) ∧
  ((c.loc z).pc = .l10 → c.linkEx z = false) ∧
  (PC.btw .l16_4 .l16_9 (c.loc z).pc → c.linkEx z = false)

/-- Obligations of a local step of `p` from `c` to `c'`. -/
structure LocalOK (c c' : Cfg n J) (p : Fin n) : Prop where
  S : c'.S = c.S
  Ex : c'.Ex = c.Ex
  G : c.G ≤ c'.G
  In : c'.In = c.In
  Out : c'.Out = c.Out
  Exclear : c'.Exclear = c.Exclear
  loc : ∀ z, z ≠ p → c'.loc z = c.loc z
  linkS : ∀ z, z ≠ p → c'.linkS z = c.linkS z
  linkEx : ∀ z, z ≠ p → c'.linkEx z = c.linkEx z
  /-- witness at lines 5.1–8 -/
  r8 : PC.btw .l5_1 .l8 (c.loc p).pc →
    (PC.btw .l5_1 .l8 (c'.loc p).pc ∧ SameSDT (c.loc p) (c'.loc p)) ∨
    (c.S.1 = (c.loc p).s ∧ c.S.2.1 = (c.loc p).d ∧ c.Out (c.loc p).s = (c.loc p).d)
  /-- witness at lines 5.1–10 -/
  r10 : PC.btw .l5_1 .l10 (c.loc p).pc → ((c.loc p).pc = .l10 → c.linkEx p = true) →
    (PC.btw .l5_1 .l10 (c'.loc p).pc ∧ ((c'.loc p).pc = .l10 → c'.linkEx p = true) ∧
      SameSDT (c.loc p) (c'.loc p)) ∨ c.Ex ≠ none
  /-- witness at lines 5.1–12 -/
  r12 : PC.btw .l5_1 .l12 (c.loc p).pc →
    (PC.btw .l5_1 .l12 (c'.loc p).pc ∧ SameSDT (c.loc p) (c'.loc p)) ∨
    ((c.loc p).pc = .l11 ∧ c.Ex = none) ∨ ((c.loc p).pc = .l12 ∧ c.Exclear (c.loc p).a.1 = true)
  /-- witness at lines 5.1–16.2 -/
  r162 : PC.btw .l5_1 .l16_2 (c.loc p).pc → ((c.loc p).pc = .l16_2 → c.linkEx p = true) →
    PC.btw .l5_1 .l16_2 (c'.loc p).pc ∧ ((c'.loc p).pc = .l16_2 → c'.linkEx p = true) ∧
      SameSDT (c.loc p) (c'.loc p)
  /-- `p` does not break `NoSide` of the current side of `S` when `Min(Q)` is of another session -/
  ns : NoSide c c.S.1 c.S.2.1 → minQ c.Q ≠ none → (∀ sh dh, minQ c.Q = some (sh, dh) → sh ≠ c.S.1) →
    (c'.loc p).s = c.S.1 → (c'.loc p).pc ≠ .l1_5 ∧ (c'.loc p).pc ≠ .l1_6 ∧ (c'.loc p).pside ≠ some c.S.2.1
  /-- `p` does not enter the set constrained by `w2` (when `Ex = false`) unless it was in it -/
  w2 : c.Ex = none →
    (PC.btw .l11 .l16_3 (c'.loc p).pc ∨ ((c'.loc p).pc = .l10 ∧ c'.linkEx p = false)) →
    (PC.btw .l11 .l16_3 (c.loc p).pc ∨ ((c.loc p).pc = .l10 ∧ c.linkEx p = false)) ∧
      (c'.loc p).s = (c.loc p).s ∧ (c'.loc p).d = (c.loc p).d
  /-- `p` keeps the constraints of a winner of session `s` -/
  win : ∀ s, c.Ex = some s → c.Exclear s = false → WinOK c s p → WinOK c' s p

theorem ExW_of_local {c c' : Cfg n J} {p : Fin n} (h : LocalOK c c' p) {s : J} {d : Bool}
    (hw : ExW c s d .l5_1 .l8) (hctx : c.S.1 ≠ s ∨ c.Out s ≠ d) : ExW c' s d .l5_1 .l8 := by
  obtain ⟨m, h1, h2, h3⟩ := hw
  by_cases hm : m = p
  · subst hm
    rcases h.r8 h3 with ⟨h4, h5, h6, -⟩ | ⟨h4, -, h5⟩
    · exact ⟨m, by rw [h5, h1], by rw [h6, h2], h4⟩
    · rcases hctx with hc | hc
      · exact absurd (h4.trans h1) hc
      · exact absurd (by rw [← h1, ← h2]; exact h5) hc
  · exact ⟨m, by rw [h.loc m hm]; exact h1, by rw [h.loc m hm]; exact h2, by rw [h.loc m hm]; exact h3⟩

theorem NoSide_of_local {c c' : Cfg n J} {p : Fin n} (hI : Inv c) (h : LocalOK c c' p)
    (hns : NoSide c c.S.1 c.S.2.1) (hm : ∃ m sh dh, PC.btw .l5_1 .l13 (c.loc m).pc ∧
      (c.loc m).s = sh ∧ (c.loc m).d = dh ∧ sh ≠ c.S.1) :
    NoSide c' c'.S.1 c'.S.2.1 := by
  rw [h.S]
  intro z hz
  by_cases hzp : z = p
  · subst hzp
    obtain ⟨m, sh, dh, hm1, -, -, -⟩ := hm
    exact h.ns hns (hI.minQ_ne_none hm1) (fun sh dh hq => hI.minQ_ne_sess hns hq) hz
  · rw [h.loc z hzp] at hz ⊢
    exact hns z hz

/-- **Frame lemma**: the per-process clauses of `y ≠ p` survive a local step of `p`. -/
theorem LI_frame_local {c c' : Cfg n J} {p y : Fin n} (hI : Inv c) (h : LocalOK c c' p) (hy : y ≠ p) :
    LI c' y := by
  have hL := hI.li y
  have ly := h.loc y hy
  have lSy := h.linkS y hy
  have lEy := h.linkEx y hy
  -- rewrite all shared fields and `y`'s own data
  constructor
  · rw [ly]; exact fun h1 => le_trans (hL.tm h1) h.G
  · -- l1
    rw [ly, h.S]
    intro h1 h2 h3
    obtain ⟨q, q1, q2, q3, q4⟩ := hL.l1 h1 h2 h3
    by_cases hq : q = p
    · subst hq
      rcases h.r8 q2 with ⟨h4, h5, h6, h7⟩ | ⟨h4, -, -⟩
      · exact ⟨q, by rw [h5]; exact q1, h4, fun h8 => by rw [h7]; exact lt_of_lt_of_le (q3 h8) h.G,
          by rw [h7]; exact q4⟩
      · exact absurd (h4.symm.trans h2) q1
    · refine ⟨q, ?_, ?_, fun h8 => ?_, ?_⟩ <;> rw [h.loc q hq]
      · exact q1
      · exact q2
      · exact lt_of_lt_of_le (q3 h8) h.G
      · exact q4
  · rw [ly, h.S, h.In]; exact hL.l14
  · rw [ly, h.S]; exact hL.l16
  · rw [ly, h.S, h.Out]; exact hL.i5
  · rw [ly, h.S]; exact hL.i7
  · rw [ly, h.S, h.Out]; exact hL.i8
  · rw [ly, h.S, lSy]; exact hL.a1
  · -- a2
    rw [ly, h.S, lSy]
    intro h1 h2
    obtain ⟨sh, dh, hb, hw⟩ := hL.a2 h1 h2
    exact ⟨sh, dh, hb, fun hne => ExW_of_local h (hw hne) (Or.inl (Ne.symm hne))⟩
  · -- a3
    rw [ly, lSy]
    intro h1 h2
    obtain ⟨hns, hsh⟩ := hL.a3 h1 h2
    obtain ⟨sh, dh, hb, hw⟩ := hL.a2 (Or.inr h1) h2
    have hne : sh ≠ c.S.1 := hsh sh dh hb
    obtain ⟨m, m1, m2, m3⟩ := hw hne
    refine ⟨NoSide_of_local hI h hns ⟨m, sh, dh, ⟨m3.1, le_trans m3.2 (by decide)⟩, m1, m2, hne⟩, ?_⟩
    rw [h.S]; exact hsh
  · -- p5
    rw [ly, h.S, h.Out]
    intro h1
    obtain ⟨sh, dh, hb, hne, heq⟩ := hL.p5 h1
    refine ⟨sh, dh, hb, fun hs => ?_, heq⟩
    obtain ⟨e1, e2, e3⟩ := hne hs
    exact ⟨e1, e2, ExW_of_local h e3 (Or.inr e2)⟩
  · rw [ly, h.S, lSy]; exact hL.e1
  · rw [ly, lSy]; exact hL.x1
  · -- x2
    rw [ly, lSy]
    intro h1 h2 sh dh hb hne
    have he1 := hL.e1 ⟨le_trans (by decide) h1.1, le_trans h1.2 (by decide)⟩ h2
    exact ExW_of_local h (hL.x2 h1 h2 sh dh hb hne) (Or.inl (by rw [he1.1]; exact Ne.symm hne))
  · -- x3
    rw [ly, lEy]
    intro h1 h2 dh hb
    obtain ⟨m, m1, m2, m3, m4⟩ := hL.x3 h1 h2 dh hb
    by_cases hm : m = p
    · subst hm
      obtain ⟨k1, k2, k3, k4, -⟩ := h.r162 m3 m4
      exact ⟨m, by rw [k3]; exact m1, by rw [k4]; exact m2, k1, k2⟩
    · refine ⟨m, ?_, ?_, ?_, ?_⟩ <;> rw [h.loc m hm] <;> (try rw [h.linkEx m hm]) <;> assumption
  · -- e2
    rw [ly, lSy, lEy]
    intro h1 h2 h3
    obtain ⟨hns, sh, dh, hb, hne⟩ := hL.e2 h1 h2 h3
    have he1 := hL.e1 (by rw [h1]; decide) h2
    have hw := hL.x2 (by rw [h1]; decide) h2 sh dh hb hne
    obtain ⟨m, m1, m2, m3⟩ := hw
    have hns' : NoSide c c.S.1 c.S.2.1 := by rw [he1.1, he1.2]; exact hns
    have := NoSide_of_local hI h hns' ⟨m, sh, dh, ⟨m3.1, le_trans m3.2 (by decide)⟩, m1, m2,
      by rw [he1.1]; exact hne⟩
    rw [h.S, he1.1, he1.2] at this
    exact ⟨this, sh, dh, hb, hne⟩
  · -- e3
    rw [ly, lSy]
    intro h1 h2
    obtain ⟨hns, sh, dh, hb, hne, hw⟩ := hL.e3 h1 h2
    have he1 := hL.e1 (by rw [h1]; decide) h2
    obtain ⟨m, m1, m2, m3⟩ := hw
    have hns' : NoSide c c.S.1 c.S.2.1 := by rw [he1.1, he1.2]; exact hns
    have := NoSide_of_local hI h hns' ⟨m, sh, dh, ⟨m3.1, le_trans m3.2 (by decide)⟩, m1, m2,
      by rw [he1.1]; exact hne⟩
    rw [h.S, he1.1, he1.2] at this
    exact ⟨this, sh, dh, hb, hne, ExW_of_local h ⟨m, m1, m2, m3⟩ (Or.inl (by rw [he1.1]; exact Ne.symm hne))⟩
  · -- p11
    rw [ly, h.S, h.Out]
    intro h1
    obtain ⟨sh, dh, hb, e1, e2, e3, e4⟩ := hL.p11 h1
    exact ⟨sh, dh, hb, e1, e2, e3, ExW_of_local h e4 (Or.inr e3)⟩
  · rw [ly, lEy, h.Ex]; exact hL.w1
  · -- w2
    rw [ly, lEy]
    intro h1 h2 z hz
    by_cases hzp : z = p
    · subst hzp
      have hEx := hL.w1 h1 h2
      obtain ⟨k1, k2, k3⟩ := h.w2 hEx hz
      have := hL.w2 h1 h2 z k1
      exact ⟨by rw [k2]; exact this.1, by rw [k3]; exact this.2.1, this.2.2⟩
    · rw [h.loc z hzp, h.linkEx z hzp] at hz
      rw [h.loc z hzp]
      exact hL.w2 h1 h2 z hz
  · rw [ly, lEy, h.Ex]; exact hL.w3
  · -- w4
    rw [ly, lEy, h.S]
    intro h1 h2 h3
    obtain ⟨m, m1, m2, m3, m4⟩ := hL.w4 h1 h2 h3
    by_cases hm : m = p
    · subst hm
      rcases h.r10 m3 m4 with ⟨k1, k2, k3, k4, -⟩ | hEx
      · exact ⟨m, by rw [k3]; exact m1, by rw [k4]; exact m2, k1, k2⟩
      · exact absurd (hL.w1 h1 h2) hEx
    · refine ⟨m, ?_, ?_, ?_, ?_⟩ <;> rw [h.loc m hm] <;> (try rw [h.linkEx m hm]) <;> assumption
  · rw [ly, lEy, h.Exclear]; exact hL.w5
  · -- win
    rw [ly, h.Ex, h.Exclear]
    intro h1
    obtain ⟨e1, e2, e3⟩ := hL.win h1
    refine ⟨e1, e2, fun z hzy => ?_⟩
    by_cases hzp : z = p
    · subst hzp
      exact h.win _ e1 e2 (e3 z hzy)
    · rw [h.loc z hzp, h.linkEx z hzp]; exact e3 z hzy
  · -- winS
    rw [ly, h.S]
    intro h1 h2
    obtain ⟨m, m1, m2, m3⟩ := hL.winS h1 h2
    obtain ⟨e1, e2, e3⟩ := hL.win h1
    by_cases hm : m = p
    · subst hm
      have hmy : m ≠ y := fun h' => hy h'.symm
      rcases h.r12 m3 with ⟨k1, k2, k3, -⟩ | ⟨k1, k2⟩ | ⟨k1, k2⟩
      · exact ⟨m, by rw [k2]; exact m1, by rw [k3]; exact m2, k1⟩
      · rw [e1] at k2; cases k2
      · have := (e3 m hmy).2.1 (by rw [k1]; decide)
        rw [k1] at this
        rcases this with h' | ⟨-, h'⟩
        · cases h'
        · rw [h', e2] at k2; cases k2
    · exact ⟨m, by rw [h.loc m hm]; exact m1, by rw [h.loc m hm]; exact m2, by rw [h.loc m hm]; exact m3⟩
  · rw [ly, h.S, h.Out]; exact hL.p13

end Podc.GroupMutexLogRMR

namespace Podc.GroupMutexLogRMR

variable {n : ℕ} {J : Type} [DecidableEq J]

/-- **Global frame lemma** for a local step of `p`. -/
theorem Inv.of_local {c c' : Cfg n J} {p : Fin n} (hI : Inv c) (h : LocalOK c c' p)
    (hC : ∀ s d, c'.C s d + (c.loc p).cnt s d = c.C s d + (c'.loc p).cnt s d)
    (hQ : ∀ z, z ≠ p → c'.Q z = c.Q z) (hQp : c'.Q p = if PC.btw .l5_1 .l13 (c'.loc p).pc then
      some ((c'.loc p).s, (c'.loc p).d, (c'.loc p).tm) else none)
    (hg5 : ∀ s, c.S.1 = s → c.In s = c.S.2.1 → ∃ y, (c'.loc y).s = s ∧
      (c'.loc y).pside = some c.S.2.1 ∧ PC.btw .l1_4 .l15 (c'.loc y).pc)
    (hg7 : c.S.1 ≠ (c'.loc p).s → ∀ e, (c'.loc p).pside = some e → e = c.In (c'.loc p).s)
    (hU : (c'.loc p).pc ≠ .l5_5 ∧ (c'.loc p).pc ≠ .l16_11)
    (hU' : (c.loc p).pc ≠ .l5_5 ∧ (c.loc p).pc ≠ .l16_11)
    (hLp : LI c' p) : Inv c' := by
  have hloc : c'.loc = Function.update c.loc p (c'.loc p) := by
    funext z
    by_cases hz : z = p
    · subst hz; simp
    · rw [Function.update_of_ne hz, h.loc z hz]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro s d
    have := sum_cnt_update c.loc p (c'.loc p) s d
    rw [← hloc] at this
    have h2 := hC s d
    rw [hI.gC s d] at h2
    omega
  · intro z
    by_cases hz : z = p
    · subst hz; exact hQp
    · rw [hQ z hz, h.loc z hz]; exact hI.gQ z
  · rw [h.In, h.Out, h.S]; exact hI.g4
  · rw [h.S, h.In]; exact hg5
  · intro s z hs hz e he
    rw [h.S] at hs; rw [h.In]
    by_cases hzp : z = p
    · subst hzp; subst hz; exact hg7 hs e he
    · rw [h.loc z hzp] at hz he; exact hI.g7 s z hs hz e he
  · intro y z hyz hy
    by_cases hyp : y = p
    · subst hyp; exact absurd hy (by rcases hU with ⟨h1, h2⟩; tauto)
    · rw [h.loc y hyp] at hy
      by_cases hzp : z = p
      · subst hzp; exact hU
      · rw [h.loc z hzp]; exact hI.gU y z hyz hy
  · rw [h.Out, h.S]
    intro hout
    obtain ⟨z, z1, z2, z3⟩ := hI.g8 hout
    have hzp : z ≠ p := by rintro rfl; rcases z1 with h1 | h1; exacts [hU'.1 h1, hU'.2 h1]
    exact ⟨z, by rw [h.loc z hzp]; exact z1, by rw [h.loc z hzp]; exact z2, by rw [h.loc z hzp]; exact z3⟩
  · intro y
    by_cases hy : y = p
    · subst hy; exact hLp
    · exact LI_frame_local hI h hy

end Podc.GroupMutexLogRMR
