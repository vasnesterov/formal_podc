import Papers.PODC2013.ConstantBarriersMutex.InvLemmas

/-!
# Preservation of the invariant by flushes (performing a buffered write)
-/

namespace Podc.ConstantBarriersMutex

variable {h : ℕ}

section
variable {s : Cfg h} {g : Proc h} {w : W h} {b' : List (W h)}

lemma flush_eq (hb : s.buf g = w :: b') :
    s.flush g = { s with mem := s.mem.write w, buf := Function.update s.buf g b' } :=
  flush_of_cons s g hb

lemma flush_buf_self (hb : s.buf g = w :: b') : (s.flush g).buf g = b' := by
  rw [flush_eq hb]; simp

lemma flush_buf_ne (hb : s.buf g = w :: b') {q : Proc h} (hq : q ≠ g) :
    (s.flush g).buf q = s.buf q := by
  rw [flush_eq hb]; simp [Function.update_of_ne hq]

lemma flush_mem (hb : s.buf g = w :: b') : (s.flush g).mem = s.mem.write w := by
  rw [flush_eq hb]

/-- The write performed by a non-holder. -/
lemma Inv.flush_nonholder_kind (hI : Inv s) (hb : s.buf g = w :: b') (hg : ¬ Holds s g) :
    NHW g w := hI.nonholder_buf hg w (by simp [hb])

end

/-- A flush of `g` whose oldest buffered write `w` is neither a write to `lock` nor a write
`signal[r] ← true` preserves the invariant, provided the local invariant of `g` is
re-established. -/
lemma inv_flush_quiet {s : Cfg h} (hI : Inv s) {g : Proc h} {w : W h} {b' : List (W h)}
    (hb : s.buf g = w :: b') (hwl : w.isLock = false) (hws : ∀ r, w ≠ .signal r true)
    (hLI : LI (s.flush g) g) : Inv (s.flush g) := by
  have hm : (s.flush g).mem = s.mem.write w := flush_mem hb
  have hbg : (s.flush g).buf g = b' := flush_buf_self hb
  have hbq : ∀ q, q ≠ g → (s.flush g).buf q = s.buf q := fun q hq => flush_buf_ne hb hq
  have hpc : (s.flush g).pc = s.pc := flush_pc s g
  have hent : (s.flush g).ent = s.ent := flush_ent s g
  have hlock : (s.flush g).mem.lock = s.mem.lock := by
    rw [hm, write_lock]; cases w <;> simp_all [W.isLock]
  -- kinds of `w`
  have hkind : (Holds s g ∧ ExitType g w) ∨
      (¬ Holds s g ∧ (w = .signal g false ∨ w = .apply g true ∨ ∃ i, w = .node i g)) := by
    by_cases hg : Holds s g
    · left; refine ⟨hg, ?_⟩
      rcases hI.holder_buf hg w (by simp [hb]) with h1 | h1 | ⟨nx, h1⟩
      · exact h1
      · rw [hwl] at h1; exact absurd h1 (by simp)
      · exact absurd h1 (hws nx)
    · right; refine ⟨hg, ?_⟩
      rcases hI.flush_nonholder_kind hb hg with h1 | h1 | h1 | ⟨nx, h1⟩
      · exact Or.inl h1
      · exact Or.inr (Or.inl h1)
      · exact Or.inr (Or.inr h1)
      · exact absurd h1 (hws nx)
  -- effect on `signal` and `apply`
  have hsig : ∀ r, (s.flush g).mem.signal r = s.mem.signal r ∨
      (r = g ∧ w = .signal g false ∧ s.mem.apply g = false) := by
    intro r
    rw [hm]
    rcases hkind with ⟨-, hX⟩ | ⟨-, hw | hw | ⟨i, rfl⟩⟩
    · exact Or.inl (hX.signal _ r)
    · subst hw
      by_cases hr : r = g
      · subst hr; exact Or.inr ⟨rfl, rfl, hI.apply_false_of_head_sig hb⟩
      · left; simp [Mem.write, Function.update_of_ne hr]
    · subst hw; left; rfl
    · left; rfl
  have happ : ∀ r, (s.flush g).mem.apply r = s.mem.apply r ∨
      (r = g ∧ ((w = .apply g true ∧ s.mem.signal g = false) ∨ Holds s g)) := by
    intro r
    rw [hm]
    by_cases hr : r = g
    · subst hr
      rcases hkind with ⟨hg, -⟩ | ⟨-, hw | hw | ⟨i, rfl⟩⟩
      · exact Or.inr ⟨rfl, Or.inr hg⟩
      · subst hw; left; rfl
      · subst hw; exact Or.inr ⟨rfl, Or.inl ⟨rfl, hI.signal_false_of_head_apply hb⟩⟩
      · left; rfl
    · left
      rcases hkind with ⟨-, hX⟩ | ⟨-, hw | hw | ⟨i, rfl⟩⟩
      · exact hX.apply _ hr
      · subst hw; rfl
      · subst hw; simp [Mem.write, Function.update_of_ne hr]
      · rfl
  have hsigF : ∀ r, s.mem.signal r = false → (s.flush g).mem.signal r = false := by
    intro r hr
    rcases hsig r with h1 | ⟨rfl, rfl, -⟩
    · rw [h1, hr]
    · rw [hm]; simp [Mem.write]
  have hsigT : ∀ r, (s.flush g).mem.signal r = true → s.mem.signal r = true := by
    intro r hr
    rcases hsig r with h1 | ⟨rfl, rfl, -⟩
    · rw [← h1, hr]
    · rw [hm] at hr; simp [Mem.write] at hr
  have happT : ∀ r, s.mem.apply r = true → (s.flush g).mem.apply r = true ∨ Holds s r := by
    intro r hr
    rcases happ r with h1 | ⟨rfl, ⟨rfl, -⟩ | h1⟩
    · left; rw [h1, hr]
    · left; rw [hm]; simp [Mem.write]
    · exact Or.inr h1
  -- holders and handers
  have hholds : ∀ q, Holds (s.flush g) q ↔ Holds s q := by
    intro q
    unfold Holds; rw [hpc]
    by_cases hq : q = g
    · subst hq
      have hmem : ∀ o, W.lock o ∈ b' ↔ W.lock o ∈ s.buf q := by
        intro o; rw [hb]; simp only [List.mem_cons]
        constructor
        · exact Or.inr
        · rintro (h1 | h1)
          · subst h1; simp [W.isLock] at hwl
          · exact h1
      cases s.pc q <;> simp only [hbg, hmem]
    · rw [hbq q hq]
  have hng_hands : ∀ nx, ¬ Hands s g nx := by
    intro nx hh; rcases hh with ⟨-, h1⟩ | ⟨-, h1⟩
    · rw [hb] at h1; simp at h1
    · rw [hb] at h1; simp at h1; exact hws nx h1.1
  have hhands : ∀ q nx, Hands (s.flush g) q nx ↔ Hands s q nx := by
    intro q nx
    by_cases hq : q = g
    · subst hq
      refine ⟨fun hh => ?_, fun hh => absurd hh (hng_hands nx)⟩
      exfalso
      have hl := hI.loc q
      unfold LI at hl
      unfold Hands at hh; rw [hpc, hbg] at hh
      rcases hh with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h1] at hl; subst h2
        rcases hl.2 with ⟨B, hB, -⟩ | ⟨hB, -⟩
        · rw [hb] at hB
          rcases B with _ | ⟨x, B⟩
          · simp at hB; subst hB; simp [W.isLock] at hwl
          · simp at hB
        · rw [hb] at hB; simp at hB
      · rw [h1] at hl; subst h2
        rcases hl.2 with ⟨B, hB, -⟩ | ⟨hB, -⟩ | ⟨hB, -⟩
        · rw [hb] at hB
          rcases B with _ | ⟨x, B⟩
          · simp at hB; obtain ⟨rfl, -⟩ := hB; simp [W.isLock] at hwl
          · first | (simp at hB; done) | (simp at hB; have := congrArg List.length hB.2; simp at this)
        · rw [hb] at hB; simp at hB
        · rw [hb] at hB; simp at hB
    · unfold Hands; rw [hpc, hbq q hq]
  have hbufne : ∀ q, (s.flush g).buf q ≠ [] → s.buf q ≠ [] := by
    intro q hq
    by_cases hqg : q = g
    · subst hqg; rw [hb]; simp
    · rwa [hbq q hqg] at hq
  have hincsx : ∀ q, (s.flush g).InCSX q → s.InCSX q := by
    intro q hq
    unfold Cfg.InCSX at hq ⊢
    rw [hpc] at hq
    rcases hq with hq | hq | ⟨ho, hne⟩
    · exact Or.inl hq
    · exact Or.inr (Or.inl hq)
    · exact Or.inr (Or.inr ⟨ho, hbufne q hne⟩)
  -- the logical memory
  have hlv : (lv (s.flush g)).promQ = (lv s).promQ ∧
      ∀ r, (lv (s.flush g)).inPromQ r = (lv s).inPromQ r := by
    unfold lv
    rw [hlock]
    rcases hL : s.mem.lock with _ | g'
    · rcases hkind with ⟨hg, -⟩ | ⟨-, hw⟩
      · rw [hI.holds_lock hg] at hL; exact absurd hL (by simp)
      · rw [hm]
        rcases hw with rfl | rfl | ⟨i, rfl⟩ <;>
          exact ⟨rfl, fun r => by simp [write_inPromQ]⟩
    · simp only
      by_cases hgg : g' = g
      · subst hgg
        rw [hm, hbg, hb]; exact ⟨rfl, fun _ => rfl⟩
      · rw [hbq g' hgg, hm]
        rcases hkind with ⟨hg, -⟩ | ⟨-, hw⟩
        · rw [hI.holds_lock hg] at hL; exact absurd (Option.some_injective _ hL) (Ne.symm hgg)
        · refine ⟨view_promQ_congr _ ?_, fun r => view_inPromQ_congr _ ?_⟩ <;>
            rcases hw with rfl | rfl | ⟨i, rfl⟩ <;> simp [write_inPromQ]
  have hexits : (s.flush g).mem.exits = s.mem.exits ∨ (∃ v, w = .exits v) := by
    rw [hm, write_exits]; cases w <;> simp
  refine
    { loc := ?_, hc := HC_frame hI hpc hlv.1 hlv.2 happT hbufne, lockRole := ?_, uniq := ?_,
      sig := ?_, nodup := ?_, pq := ?_, inpq := ?_, q4 := ?_, ex1 := ?_, ex2 := ?_, ex3 := ?_,
      ex4 := ?_ }
  · intro q
    by_cases hq : q = g
    · subst hq; exact hLI
    · refine LI_mono (hbq q hq) (by rw [hpc]) ?_ hlock hsigF (hI.loc q)
      rcases happ q with h1 | ⟨rfl, -⟩
      · exact h1
      · exact absurd rfl hq
  · intro g' hg'
    rw [hlock] at hg'
    rcases hI.lockRole g' hg' with h1 | ⟨h1, h2, h3⟩
    · exact Or.inl ((hholds g').2 h1)
    · right
      refine ⟨by rw [hpc]; exact h1, ?_, ?_⟩
      · rcases happT g' h2 with h4 | h4
        · exact h4
        · exact absurd h4 (by
            intro hh; unfold Holds at hh; revert hh h1; cases s.pc g' <;> simp [PC.Entry])
      · rcases h3 with h3 | ⟨g'', h3⟩
        · left
          rcases hsig g' with h4 | ⟨rfl, -, h4⟩
          · rw [h4, h3]
          · rw [h2] at h4; exact absurd h4 (by simp)
        · exact Or.inr ⟨g'', (hhands g'' g').2 h3⟩
  · intro g₁ g₂ h₁ h₂; exact hI.uniq _ _ (hincsx _ h₁) (hincsx _ h₂)
  · intro q hs hE ha
    rw [hpc] at hE
    have hs' := hsigT q hs
    have ha' : s.mem.apply q = true := by
      rcases happ q with h1 | ⟨rfl, ⟨rfl, h2⟩ | h2⟩
      · rw [← h1, ha]
      · rw [h2] at hs'; exact absurd hs' (by simp)
      · exact absurd h2 (by intro hh; unfold Holds at hh; revert hh hE; cases s.pc q <;> simp [PC.Entry])
    obtain ⟨h1, h2⟩ := hI.sig q hs' hE ha'
    exact ⟨by rw [hlock]; exact h1, fun g' hh => h2 g' ((hhands g' q).1 hh)⟩
  · rw [hlv.1]; exact hI.nodup
  · intro q hq
    rw [hlv.1] at hq
    obtain ⟨h1, h2, h3⟩ := hI.pq q hq
    refine ⟨by rw [hpc]; exact h1, ?_, by rw [hlock]; exact h3⟩
    rcases happT q h2 with h4 | h4
    · exact h4
    · exact absurd (hI.holds_lock h4) h3
  · intro q
    rw [hlv.1, hlv.2, hpc]; exact hI.inpq q
  · intro hn
    rw [hlock] at hn
    rw [hm, write_promQ]
    rcases hkind with ⟨hg, -⟩ | ⟨-, hw⟩
    · rw [hI.holds_lock hg] at hn; exact absurd hn (by simp)
    · rcases hw with rfl | rfl | ⟨i, rfl⟩ <;> exact hI.q4 hn
  · intro g' hg'
    rw [hpc] at hg'
    rw [hent]
    rcases hexits with h1 | ⟨v, rfl⟩
    · rw [h1]; exact hI.ex1 g' hg'
    · exfalso
      have hgh := hI.holds_of_exits_mem (show W.exits v ∈ s.buf g by simp [hb])
      have := hI.uniq g g' (hI.incsx_of_holds hgh)
        (by unfold Cfg.InCSX; rcases hg' with h | h | h <;> simp [h, PC.Exit])
      subst this
      exact hI.no_exits_early hg' v (by simp [hb])
  · intro g' v hv
    rw [hent]
    have hv' : W.exits v ∈ s.buf g' := by
      by_cases hgg : g' = g
      · subst hgg; rw [hbg] at hv; simp [hb, hv]
      · rwa [hbq g' hgg] at hv
    rcases hexits with h1 | ⟨v0, rfl⟩
    · rw [h1]; exact hI.ex2 g' v hv'
    · exfalso
      have hgh := hI.holds_of_exits_mem (show W.exits v0 ∈ s.buf g by simp [hb])
      have hgh' := hI.holds_of_exits_mem hv'
      have := hI.holds_unique hgh hgh'; subst this
      rw [hbg] at hv
      have h4 := hI.ex4 g
      rw [hb] at h4
      have : 0 < b'.countP (fun w => w.isExits) := List.countP_pos_iff.2 ⟨_, hv, rfl⟩
      rw [List.countP_cons_of_pos (by rfl)] at h4; omega
  · intro hpre
    rw [hent]
    by_cases hwe : ∃ v, w = .exits v
    · obtain ⟨v, rfl⟩ := hwe
      obtain ⟨-, h2⟩ := hI.ex2 g v (by simp [hb])
      rw [hm]; simp; exact h2
    · have h1 : (s.flush g).mem.exits = s.mem.exits := by
        rcases hexits with h1 | h1
        · exact h1
        · exact absurd h1 hwe
      rw [h1]
      apply hI.ex3
      intro g'
      obtain ⟨h2, h3, h4, h5⟩ := hpre g'
      rw [hpc] at h2 h3 h4
      refine ⟨h2, h3, h4, fun v hv => ?_⟩
      by_cases hgg : g' = g
      · subst hgg
        rw [hb] at hv; simp only [List.mem_cons] at hv
        rcases hv with hv | hv
        · exact hwe ⟨v, hv.symm⟩
        · exact h5 v (by rw [hbg]; exact hv)
      · exact h5 v (by rw [hbq g' hgg]; exact hv)
  · intro g'
    by_cases hgg : g' = g
    · subst hgg
      rw [hbg]; have := hI.ex4 g'; rw [hb, List.countP_cons] at this; omega
    · rw [hbq g' hgg]; exact hI.ex4 g'

end Podc.ConstantBarriersMutex

namespace Podc.ConstantBarriersMutex

variable {h : ℕ}

/-- Local invariant after performing a doorway write. -/
lemma LI_flush_door {s : Cfg h} (hI : Inv s) {g : Proc h} {w : W h} {b' : List (W h)}
    (hb : s.buf g = w :: b') (hw : w = .signal g false ∨ w = .apply g true ∨ ∃ i, w = .node i g) :
    LI (s.flush g) g := by
  obtain ⟨i, hik, hget, hbk, hap, hsg, hd⟩ := hI.door_of_head hb hw
  have hb2 := hbk; rw [hb] at hb2
  obtain ⟨-, -, hb'⟩ := drop_take_cons hb2.symm
  have hm : (s.flush g).mem = s.mem.write w := flush_mem hb
  refine LI_of_door (hI.loc g) (by rw [flush_pc]) hd ⟨i + 1, by omega, ?_, ?_, ?_⟩
  · rw [flush_buf_self hb, hb']
  · rw [hm, write_apply]
    rcases i with _ | _ | i
    · rw [doorList_get0] at hget; cases hget; simp [hap]
    · rw [doorList_get1] at hget; cases hget; simp
    · have hnode : ∃ j, w = .node j g := by
        rcases hw with rfl | rfl | hw
        · have := doorList_get_signal hget; omega
        · have := doorList_get_apply hget; omega
        · exact hw
      obtain ⟨j, rfl⟩ := hnode
      simp only [hap]; omega
  · intro hi1
    have : i = 0 := by omega
    subst this
    rw [doorList_get0] at hget; cases hget
    rw [hm]; simp [Mem.write]

lemma XB_flush {s s' : Cfg h} {g : Proc h} {w : W h} {B : List (W h)} (hX : XB s g (w :: B))
    (hm : s'.mem = s.mem.write w) : XB s' g B := by
  obtain ⟨h1, h2, h3⟩ := hX
  simp only [List.tail_cons] at h3
  refine ⟨fun w' hw' => h1 w' (by simp [hw']), ?_, fun hm' => h3 (List.mem_of_mem_tail hm')⟩
  have hwX : ExitType g w := h1 w (by simp)
  rw [hm]
  by_cases hwa : w = .apply g false
  · subst hwa; simp [Mem.write, h3]
  · have : (s.mem.write w).apply g = s.mem.apply g := by
      rcases hwX with h | hX | hX | ⟨r', b, rfl⟩
      · exact absurd h hwa
      all_goals first | rfl | (cases w <;> simp_all [W.isExits, W.isPromQ, Mem.write])
    rw [this, h2]; simp [Ne.symm hwa]

/-- Local invariant after performing a write of the exit section. -/
lemma LI_flush_exit {s : Cfg h} (hI : Inv s) {g : Proc h} {w : W h} {b' : List (W h)}
    (hb : s.buf g = w :: b') (hg : Holds s g) (hX : ExitType g w) : LI (s.flush g) g := by
  have hm : (s.flush g).mem = s.mem.write w := flush_mem hb
  have hbg : (s.flush g).buf g = b' := flush_buf_self hb
  have hlock : (s.flush g).mem.lock = s.mem.lock := by rw [hm]; exact hX.lock _
  have hL := hI.loc g
  unfold LI at hL ⊢
  rw [flush_pc, hbg, hlock]
  unfold Holds at hg
  cases hp : s.pc g <;> simp only [hp] at hL hg ⊢ <;> try exact hg.elim
  all_goals first
    | (rw [hL.1] at hb; simp at hb)
    | (rw [hb] at hL; exact ⟨hL.1, XB_flush hL.2.1 hm, hL.2.2⟩)
    | (rw [hb] at hL; exact ⟨hL.1, XB_flush hL.2 hm⟩)
    | skip
  · rcases hL.2 with ⟨h1, -⟩ | ⟨h1, -⟩ <;> rw [h1] at hb <;> simp at hb
    obtain ⟨rfl, rfl⟩ := hb
    refine ⟨hL.1, Or.inr ⟨rfl, ?_⟩⟩
    rw [hm]; simp [Mem.write]
  · rename_i nx
    rcases hL.2 with ⟨B, hB, hXB, hlk⟩ | ⟨hB, -⟩
    · rcases B with _ | ⟨x, B⟩
      · rw [hb] at hB; simp at hB; obtain ⟨rfl, -⟩ := hB
        rcases hX with h | h | h | ⟨r, b, h⟩ <;> simp_all [W.isExits, W.isPromQ]
      · rw [hb] at hB; simp only [List.cons_append, List.cons.injEq] at hB
        obtain ⟨rfl, rfl⟩ := hB
        exact ⟨hL.1, Or.inl ⟨B, rfl, XB_flush hXB hm, hlk⟩⟩
    · rw [hB] at hb; simp at hb
  · rename_i o
    rcases o with _ | nx
    · rcases hL with ⟨B, hB, hXB, hlk⟩ | ⟨hB, -⟩
      · rcases B with _ | ⟨x, B⟩
        · rw [hb] at hB; simp at hB; obtain ⟨rfl, -⟩ := hB
          rcases hX with h | h | h | ⟨r, b, h⟩ <;> simp_all [W.isExits, W.isPromQ]
        · rw [hb] at hB; simp only [List.cons_append, List.cons.injEq] at hB
          obtain ⟨rfl, rfl⟩ := hB
          exact Or.inl ⟨B, rfl, XB_flush hXB hm, hlk⟩
      · rw [hB] at hb; simp at hb
    · rcases hL.2 with ⟨B, hB, hXB, hlk⟩ | ⟨hB, -⟩ | ⟨hB, -⟩
      · rcases B with _ | ⟨x, B⟩
        · rw [hb] at hB; simp at hB; obtain ⟨rfl, -⟩ := hB
          rcases hX with h | h | h | ⟨r, b, h⟩ <;> simp_all [W.isExits, W.isPromQ]
        · rw [hb] at hB; simp only [List.cons_append, List.cons.injEq] at hB
          obtain ⟨rfl, rfl⟩ := hB
          exact ⟨hL.1, Or.inl ⟨B, rfl, XB_flush hXB hm, hlk⟩⟩
      · rw [hB] at hg; simp at hg
      · rw [hB] at hb; simp at hb

/-- Common facts for flushes that leave all program counters unchanged. -/
lemma incsx_flush_imp {s : Cfg h} {g : Proc h} {q : Proc h} (hq : (s.flush g).InCSX q) :
    s.InCSX q := by
  unfold Cfg.InCSX at hq ⊢
  rw [flush_pc] at hq
  rcases hq with hq | hq | ⟨ho, hne⟩
  · exact Or.inl hq
  · exact Or.inr (Or.inl hq)
  · refine Or.inr (Or.inr ⟨ho, fun h0 => hne ?_⟩)
    unfold Cfg.flush; split
    · exact h0
    · rename_i w b hb
      by_cases hqg : q = g
      · subst hqg; rw [hb] at h0; simp at h0
      · simp [Function.update_of_ne hqg, h0]

lemma flush_buf_sub {s : Cfg h} {g q : Proc h} {w : W h} (hw : w ∈ (s.flush g).buf q) :
    w ∈ s.buf q := by
  unfold Cfg.flush at hw; split at hw
  · exact hw
  · rename_i w' b hb
    by_cases hqg : q = g
    · subst hqg; simp at hw; rw [hb]; exact List.mem_cons_of_mem _ hw
    · simpa [Function.update_of_ne hqg] using hw

lemma flush_countP_le {s : Cfg h} {g q : Proc h} (p : W h → Bool) :
    ((s.flush g).buf q).countP p ≤ (s.buf q).countP p := by
  unfold Cfg.flush; split
  · exact le_rfl
  · rename_i w' b hb
    by_cases hqg : q = g
    · subst hqg; simp only [Function.update_self]; rw [hb, List.countP_cons]; omega
    · simp [Function.update_of_ne hqg]

/-- Performing the holder's write to `lock` (statement 43 or 47). -/
lemma inv_flush_lock {s : Cfg h} (hI : Inv s) {g : Proc h} {o : Option (Proc h)}
    {b' : List (W h)} (hb : s.buf g = .lock o :: b')
    (hcase : (∃ nx, s.pc g = .x48 nx ∧ o = some nx ∧ b' = []) ∨
      (s.pc g = .x50 none ∧ o = none ∧ b' = []) ∨
      (∃ nx, s.pc g = .x50 (some nx) ∧ o = some nx ∧ b' = [.signal nx true])) :
    Inv (s.flush g) := by
  have hm : (s.flush g).mem = s.mem.write (.lock o) := flush_mem hb
  have hbg : (s.flush g).buf g = b' := flush_buf_self hb
  have hbq : ∀ q, q ≠ g → (s.flush g).buf q = s.buf q := fun q hq => flush_buf_ne hb hq
  have hpc : (s.flush g).pc = s.pc := flush_pc s g
  have hent : (s.flush g).ent = s.ent := flush_ent s g
  have hg : Holds s g := by
    unfold Holds
    rcases hcase with ⟨nx, hp, rfl, -⟩ | ⟨hp, rfl, -⟩ | ⟨nx, hp, rfl, -⟩ <;> rw [hp] <;> simp [hb]
  have hlkg := hI.holds_lock hg
  have hgX : s.InCSX g := hI.incsx_of_holds hg
  have hother : ∀ q, q ≠ g → ¬ s.InCSX q := fun q hq hc => hq (hI.uniq _ _ hc hgX)
  have hlock' : (s.flush g).mem.lock = o := by rw [hm]; rfl
  have hsig : ∀ r, (s.flush g).mem.signal r = s.mem.signal r := by intro r; rw [hm]; rfl
  have happ : ∀ r, (s.flush g).mem.apply r = s.mem.apply r := by intro r; rw [hm]; rfl
  have hHC := hI.hc g
  have hLg := hI.loc g
  -- `apply[g]` was reset (the exit-section writes before the lock write are performed)
  have hapg : s.mem.apply g = false := by
    unfold LI at hLg
    rcases hcase with ⟨nx, hp, rfl, rfl⟩ | ⟨hp, rfl, rfl⟩ | ⟨nx, hp, rfl, rfl⟩ <;>
      simp only [hp] at hLg
    · rcases hLg.2 with ⟨B, hB, hX, -⟩ | ⟨hB, -⟩
      · rw [hb] at hB; rcases B with _ | ⟨x, B⟩
        · cases ha : s.mem.apply g; · rfl
          · have := hX.2.1.1 ha; simp at this
        · first | (simp at hB; done) | (simp at hB; have := congrArg List.length hB.2; simp at this)
      · rw [hb] at hB; simp at hB
    · rcases hLg with ⟨B, hB, hX, -⟩ | ⟨hB, -⟩
      · rw [hb] at hB; rcases B with _ | ⟨x, B⟩
        · cases ha : s.mem.apply g; · rfl
          · have := hX.2.1.1 ha; simp at this
        · first | (simp at hB; done) | (simp at hB; have := congrArg List.length hB.2; simp at this)
      · rw [hb] at hB; simp at hB
    · rcases hLg.2 with ⟨B, hB, hX, -⟩ | ⟨hB, -⟩ | ⟨hB, -⟩
      · rw [hb] at hB; rcases B with _ | ⟨x, B⟩
        · cases ha : s.mem.apply g; · rfl
          · have := hX.2.1.1 ha; simp at this
        · first | (simp at hB; done) | (simp at hB; have := congrArg List.length hB.2; simp at this)
      · rw [hb] at hB; simp at hB
      · rw [hb] at hB; simp at hB
  -- the logical memory is unchanged
  have hlvs : lv s = (s.mem.write (.lock o)).view b' := by
    unfold lv; rw [hlkg]; simp [hb]
  have hb'q : ∀ w ∈ b', w.isPromQ = false ∧ ∀ r, w.isInPromQ r = false := by
    intro w hw
    rcases hcase with ⟨nx, -, -, rfl⟩ | ⟨-, -, rfl⟩ | ⟨nx, -, -, rfl⟩
    · simp at hw
    · simp at hw
    · simp at hw; subst hw; exact ⟨rfl, fun _ => rfl⟩
  have hlv : (lv (s.flush g)).promQ = (lv s).promQ ∧
      ∀ r, (lv (s.flush g)).inPromQ r = (lv s).inPromQ r := by
    rw [hlvs]
    rw [view_promQ_of (fun w hw => (hb'q w hw).1)]
    simp only [fun r => view_inPromQ_of (m := s.mem.write (.lock o)) (b := b') (q := r)
      (fun w hw => (hb'q w hw).2 r)]
    unfold lv; rw [hlock']
    rcases o with _ | nx
    · rw [hm]; exact ⟨rfl, fun _ => rfl⟩
    · simp only
      have hnx : nx ≠ g := by
        rcases hcase with ⟨nx', hp, hn, -⟩ | ⟨-, hn, -⟩ | ⟨nx', hp, hn, -⟩
        · cases hn; have := hLg; unfold LI at this; rw [hp] at this; exact this.1
        · cases hn
        · cases hn; have := hLg; unfold LI at this; rw [hp] at this; exact this.1
      rw [hbq nx hnx, hm]
      have hnb := hI.nonholder_buf (fun hh => hnx (hI.holds_unique hh hg))
      exact ⟨view_promQ_of (fun w hw => (hnb w hw).promQ),
        fun r => view_inPromQ_of (fun w hw => (hnb w hw).inPromQ)⟩
  have hbufne : ∀ q, (s.flush g).buf q ≠ [] → s.buf q ≠ [] := by
    intro q hq
    by_cases hqg : q = g
    · subst hqg; rw [hb]; simp
    · rwa [hbq q hqg] at hq
  -- the handed process
  have hNx : ∀ nx, o = some nx → NxOK s nx ∧ nx ≠ g := by
    intro nx hn
    unfold HC at hHC; unfold LI at hLg
    rcases hcase with ⟨nx', hp, hn', -⟩ | ⟨-, hn', -⟩ | ⟨nx', hp, hn', -⟩
    · rw [hn'] at hn; cases hn; rw [hp] at hHC hLg; exact ⟨hHC, hLg.1⟩
    · rw [hn'] at hn; cases hn
    · rw [hn'] at hn; cases hn; rw [hp] at hHC hLg; exact ⟨hHC (by rw [hb]; simp), hLg.1⟩
  refine
    { loc := ?_, hc := HC_frame hI hpc hlv.1 hlv.2 (fun c hc => Or.inl (by rw [happ]; exact hc))
        hbufne,
      lockRole := ?_, uniq := ?_, sig := ?_, nodup := ?_, pq := ?_, inpq := ?_, q4 := ?_,
      ex1 := ?_, ex2 := ?_, ex3 := ?_, ex4 := ?_ }
  · intro q
    by_cases hqg : q = g
    · subst hqg
      unfold LI; rw [hpc, hbg, hlock']
      unfold LI at hLg
      rcases hcase with ⟨nx, hp, rfl, rfl⟩ | ⟨hp, rfl, rfl⟩ | ⟨nx, hp, rfl, rfl⟩ <;>
        simp only [hp] at hLg ⊢
      · refine ⟨hLg.1, Or.inr ⟨by simp, by simp, by rw [happ, hapg], ?_⟩⟩
        rw [hsig]
        cases hs : s.mem.signal nx; · rfl
        have := (hI.sig nx hs (hNx nx rfl).1.1 (hNx nx rfl).1.2.1).1
        rw [hlkg] at this; exact absurd (Option.some_injective _ this) (hNx nx rfl).2.symm
      · exact Or.inr ⟨by simp, by rw [happ, hapg]⟩
      · refine ⟨hLg.1, Or.inr (Or.inl ⟨by simp, by simp, by rw [happ, hapg], ?_⟩)⟩
        rw [hsig]
        cases hs : s.mem.signal nx; · rfl
        have := (hI.sig nx hs (hNx nx rfl).1.1 (hNx nx rfl).1.2.1).1
        rw [hlkg] at this; exact absurd (Option.some_injective _ this) (hNx nx rfl).2.symm
    · exact LI_mono_out hI (hother q hqg) (hbq q hqg) (by rw [hpc]) (happ q)
        (fun h0 => by rw [hsig]; exact h0)
  · intro g' hg'
    rw [hlock'] at hg'
    subst hg'
    obtain ⟨⟨hE, hA, -, -⟩, hng⟩ := hNx g' rfl
    right
    refine ⟨by rw [hpc]; exact hE, by rw [happ]; exact hA, Or.inr ⟨g, ?_⟩⟩
    unfold Hands; rw [hpc, hbg]
    rcases hcase with ⟨nx, hp, hn, rfl⟩ | ⟨-, hn, -⟩ | ⟨nx, hp, hn, rfl⟩
    · cases hn; exact Or.inl ⟨hp, rfl⟩
    · cases hn
    · cases hn; exact Or.inr ⟨hp, rfl⟩
  · intro g₁ g₂ h₁ h₂; exact hI.uniq _ _ (incsx_flush_imp h₁) (incsx_flush_imp h₂)
  · intro q hs hE ha
    rw [hsig] at hs; rw [hpc] at hE; rw [happ] at ha
    have := (hI.sig q hs hE ha).1
    rw [hlkg] at this; cases this
    exact absurd hg (Inv.not_holds_of_entry hE)
  · rw [hlv.1]; exact hI.nodup
  · intro q hq
    rw [hlv.1] at hq
    obtain ⟨h1, h2, -⟩ := hI.pq q hq
    refine ⟨by rw [hpc]; exact h1, by rw [happ]; exact h2, ?_⟩
    rw [hlock']
    rintro rfl
    exact (hNx q rfl).1.2.2.1 hq
  · intro q
    rw [hlv.1, hlv.2, hpc]; exact hI.inpq q
  · intro hn
    rw [hlock'] at hn; subst hn
    rw [hm]
    rcases hcase with ⟨nx, -, hn, -⟩ | ⟨hp, -, rfl⟩ | ⟨nx, -, hn, -⟩
    · cases hn
    · unfold HC at hHC; rw [hp] at hHC
      have := hHC (by rw [hb]; simp)
      rw [hlvs] at this; simpa using this
    · cases hn
  · intro g' hg'
    rw [hpc] at hg'; rw [hent, hm]; exact hI.ex1 g' hg'
  · intro g' v hv
    rw [hent, hm]; exact hI.ex2 g' v (flush_buf_sub hv)
  · intro hpre
    rw [hent, hm]
    apply hI.ex3
    intro g'
    obtain ⟨h2, h3, h4, h5⟩ := hpre g'
    rw [hpc] at h2 h3 h4
    refine ⟨h2, h3, h4, fun v hv => ?_⟩
    by_cases hgg : g' = g
    · subst hgg
      rw [hb] at hv; simp only [List.mem_cons] at hv
      rcases hv with hv | hv
      · cases hv
      · exact h5 v (by rw [hbg]; exact hv)
    · exact h5 v (by rw [hbq g' hgg]; exact hv)
  · intro g'; exact (flush_countP_le _).trans (hI.ex4 g')

/-- Performing the hander's write `signal[nx] ← true` (statement 48). -/
lemma inv_flush_signal {s : Cfg h} (hI : Inv s) {g nx : Proc h}
    (hp : s.pc g = .x50 (some nx)) (hb : s.buf g = [.signal nx true]) : Inv (s.flush g) := by
  have hH : Hands s g nx := Or.inr ⟨hp, hb⟩
  obtain ⟨hlk, hnx, hsnx, hapg⟩ := hI.hands_lock hH
  have hm : (s.flush g).mem = s.mem.write (.signal nx true) := flush_mem hb
  have hbg : (s.flush g).buf g = [] := flush_buf_self hb
  have hbq : ∀ q, q ≠ g → (s.flush g).buf q = s.buf q := fun q hq => flush_buf_ne hb hq
  have hpc : (s.flush g).pc = s.pc := flush_pc s g
  have hent : (s.flush g).ent = s.ent := flush_ent s g
  have hgX : s.InCSX g := hI.incsx_of_hands hH
  have hother : ∀ q, q ≠ g → ¬ s.InCSX q := fun q hq hc => hq (hI.uniq _ _ hc hgX)
  have hnxh : ¬ Holds s nx := fun hh => hnx (hI.uniq _ _ (hI.incsx_of_holds hh) hgX)
  obtain ⟨hEnx, hAnx⟩ := hI.lock_entry hlk hnxh
  have hlock : (s.flush g).mem.lock = s.mem.lock := by rw [hm]; rfl
  have happ : ∀ r, (s.flush g).mem.apply r = s.mem.apply r := by intro r; rw [hm]; rfl
  have hsig : ∀ r, r ≠ nx → (s.flush g).mem.signal r = s.mem.signal r := by
    intro r hr; rw [hm]; simp [Mem.write, Function.update_of_ne hr]
  have hsignx : (s.flush g).mem.signal nx = true := by rw [hm]; simp [Mem.write]
  have hlv : (lv (s.flush g)).promQ = (lv s).promQ ∧
      ∀ r, (lv (s.flush g)).inPromQ r = (lv s).inPromQ r := by
    unfold lv; rw [hlock, hlk]; simp only
    rw [hbq nx hnx, hm]
    exact ⟨view_promQ_congr _ rfl, fun r => view_inPromQ_congr _ rfl⟩
  have hbufne : ∀ q, (s.flush g).buf q ≠ [] → s.buf q ≠ [] := by
    intro q hq
    by_cases hqg : q = g
    · subst hqg; rw [hb]; simp
    · rwa [hbq q hqg] at hq
  have hhands : ∀ g' r, Hands (s.flush g) g' r → g' ≠ g ∧ Hands s g' r := by
    intro g' r hh
    by_cases hgg : g' = g
    · subst hgg; unfold Hands at hh; rw [hpc, hbg, hp] at hh; simp at hh
    · refine ⟨hgg, ?_⟩; unfold Hands at hh ⊢; rwa [hpc, hbq g' hgg] at hh
  refine
    { loc := ?_, hc := HC_frame hI hpc hlv.1 hlv.2 (fun c hc => Or.inl (by rw [happ]; exact hc))
        hbufne,
      lockRole := ?_, uniq := ?_, sig := ?_, nodup := ?_, pq := ?_, inpq := ?_, q4 := ?_,
      ex1 := ?_, ex2 := ?_, ex3 := ?_, ex4 := ?_ }
  · intro q
    by_cases hqg : q = g
    · subst hqg
      unfold LI; rw [hpc, hbg, hp]
      exact ⟨hnx, Or.inr (Or.inr ⟨rfl, by rw [happ, hapg]⟩)⟩
    · by_cases hqn : q = nx
      · subst hqn
        exact LI_entry_applied hI hEnx hAnx (hbq q hqg) (by rw [hpc]) (happ q)
      · exact LI_mono_out hI (hother q hqg) (hbq q hqg) (by rw [hpc]) (happ q)
          (fun h0 => by rw [hsig q hqn]; exact h0)
  · intro g' hg'
    rw [hlock, hlk] at hg'; cases hg'
    right
    exact ⟨by rw [hpc]; exact hEnx, by rw [happ]; exact hAnx, Or.inl hsignx⟩
  · intro g₁ g₂ h₁ h₂; exact hI.uniq _ _ (incsx_flush_imp h₁) (incsx_flush_imp h₂)
  · intro q hs hE ha
    rw [hpc] at hE; rw [happ] at ha
    refine ⟨?_, fun g' hh => ?_⟩
    · by_cases hqn : q = nx
      · subst hqn; rw [hlock]; exact hlk
      · rw [hsig q hqn] at hs; rw [hlock]; exact (hI.sig q hs hE ha).1
    · obtain ⟨hgg, hh'⟩ := hhands g' q hh
      exact hgg (hI.uniq _ _ (hI.incsx_of_hands hh') hgX)
  · rw [hlv.1]; exact hI.nodup
  · intro q hq
    rw [hlv.1] at hq
    obtain ⟨h1, h2, h3⟩ := hI.pq q hq
    exact ⟨by rw [hpc]; exact h1, by rw [happ]; exact h2, by rw [hlock]; exact h3⟩
  · intro q
    rw [hlv.1, hlv.2, hpc]; exact hI.inpq q
  · intro hn; rw [hlock, hlk] at hn; cases hn
  · intro g' hg'
    rw [hpc] at hg'; rw [hent, hm]; exact hI.ex1 g' hg'
  · intro g' v hv
    rw [hent, hm]; exact hI.ex2 g' v (flush_buf_sub hv)
  · intro hpre
    rw [hent, hm]
    apply hI.ex3
    intro g'
    obtain ⟨h2, h3, h4, h5⟩ := hpre g'
    rw [hpc] at h2 h3 h4
    refine ⟨h2, h3, h4, fun v hv => ?_⟩
    by_cases hgg : g' = g
    · subst hgg; rw [hb] at hv; simp at hv
    · exact h5 v (by rw [hbq g' hgg]; exact hv)
  · intro g'; exact (flush_countP_le _).trans (hI.ex4 g')

/-- **Flushes preserve the invariant.** -/
theorem inv_flush {s : Cfg h} (hI : Inv s) (g : Proc h) : Inv (s.flush g) := by
  rcases hb : s.buf g with _ | ⟨w, b'⟩
  · rw [flush_of_nil s g hb]; exact hI
  have quiet : ExitType g w → Holds s g → Inv (s.flush g) := fun hX hg =>
    inv_flush_quiet hI hb hX.isLock (fun r => hX.ne_signal r true) (LI_flush_exit hI hb hg hX)
  by_cases hg : Holds s g
  · rcases hI.holder_shape hg with hA | ⟨B, nx, hp, hB, hX⟩ | ⟨B, hp, hB, hX⟩ | ⟨B, nx, hp, hB, hX⟩
    · exact quiet (hA w (by simp [hb])) hg
    · rcases B with _ | ⟨x, B⟩
      · rw [hb] at hB; simp at hB; obtain ⟨rfl, rfl⟩ := hB
        exact inv_flush_lock hI hb (Or.inl ⟨nx, hp, rfl, rfl⟩)
      · rw [hb] at hB; simp at hB; obtain ⟨rfl, -⟩ := hB
        exact quiet (hX w (by simp)) hg
    · rcases B with _ | ⟨x, B⟩
      · rw [hb] at hB; simp at hB; obtain ⟨rfl, rfl⟩ := hB
        exact inv_flush_lock hI hb (Or.inr (Or.inl ⟨hp, rfl, rfl⟩))
      · rw [hb] at hB; simp at hB; obtain ⟨rfl, -⟩ := hB
        exact quiet (hX w (by simp)) hg
    · rcases B with _ | ⟨x, B⟩
      · rw [hb] at hB; simp at hB; obtain ⟨rfl, rfl⟩ := hB
        exact inv_flush_lock hI hb (Or.inr (Or.inr ⟨nx, hp, rfl, rfl⟩))
      · rw [hb] at hB; simp at hB; obtain ⟨rfl, -⟩ := hB
        exact quiet (hX w (by simp)) hg
  · rcases hI.nonholder_buf hg w (by simp [hb]) with h1 | h1 | h1 | ⟨nx, h1⟩
    · exact inv_flush_quiet hI hb (by subst h1; rfl) (by intro r; subst h1; simp)
        (LI_flush_door hI hb (Or.inl h1))
    · exact inv_flush_quiet hI hb (by subst h1; rfl) (by intro r; subst h1; simp)
        (LI_flush_door hI hb (Or.inr (Or.inl h1)))
    · obtain ⟨i, rfl⟩ := h1
      exact inv_flush_quiet hI hb rfl (by intro r; simp)
        (LI_flush_door hI hb (Or.inr (Or.inr ⟨i, rfl⟩)))
    · subst h1
      obtain ⟨hp, hB⟩ := hI.hands_of_head_sig hb hg
      exact inv_flush_signal hI hp hB

end Podc.ConstantBarriersMutex
