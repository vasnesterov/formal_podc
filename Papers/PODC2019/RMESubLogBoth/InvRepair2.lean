import Papers.PODC2019.RMESubLogBoth.InvRepair

/-!
# The repairer's shared-memory steps (lines 46–49) preserve the invariant
-/

namespace Podc.RMESubLogBoth

variable {k : ℕ}

open Relation

/-- Adding one link `x → m` to a well-founded relation keeps it well-founded if `m` does not
reach `x`. -/
lemma wf_add_link {B B' : ℕ → ℕ → Prop} (hwf : WellFounded (flip B)) {x m : ℕ}
    (hB : ∀ a b, B' a b → B a b ∨ (a = x ∧ b = m)) (hmx : ¬ ReflTransGen B m x) :
    WellFounded (flip B') := by
  have h1 : ∀ a, ¬ ReflTransGen B a x → Acc (flip B') a := by
    intro a
    induction a using hwf.induction with
    | _ a ih =>
      intro ha
      refine Acc.intro _ (fun b hb => ?_)
      rcases hB a b hb with h | ⟨rfl, -⟩
      · exact ih b h (fun hbx => ha (.head h hbx))
      · exact absurd .refl ha
  refine ⟨fun a => ?_⟩
  induction a using hwf.induction with
  | _ a ih =>
    refine Acc.intro _ (fun b hb => ?_)
    rcases hB a b hb with h | ⟨-, rfl⟩
    · exact ih b h
    · exact h1 b hmx

section
variable {c c' : Cfg k} {own : ℕ → ℕ}

/-- Local invariants of ports outside the CS of `RLock`. -/
lemma LI.of_nonR {q : Fin k} (h : LI c own q) (hR : ¬ (c.pc q).InR) (hpc : c'.pc q = c.pc q)
    (hnode : c'.node = c.node)
    (hpq : ∀ y, c.node q = some y → c'.pred y = c.pred y ∧ c'.nn y = c.nn y ∧ c'.csig y = c.csig y)
    (hRel : c'.Rel = c.Rel)
    (h13 : ∀ y, c.pc q = .l13 y → (∀ w, ¬ c'.Bh w y) ∧ c'.tail ≠ y) : LI c' own q := by
  unfold LI at h ⊢
  rw [hpc]
  cases hq : c.pc q with
  | rem => rw [hq] at h; rwa [hnode]
  | l10 => trivial
  | l11 => rw [hq] at h; rwa [hnode]
  | l13 y =>
    rw [hq] at h; obtain ⟨h1, h2, h3, h4, -, -⟩ := h
    obtain ⟨p1, p2, p3⟩ := hpq y h1
    exact ⟨by rwa [hnode], by rwa [p1], by rwa [p2], by rwa [p3], (h13 y hq).1, (h13 y hq).2⟩
  | l14 y m =>
    rw [hq] at h; obtain ⟨h1, h2, h3, h4⟩ := h
    obtain ⟨p1, p2, p3⟩ := hpq y h1
    exact ⟨by rwa [hnode], by rwa [p1], by rwa [p2], by rwa [p3]⟩
  | l15 y m =>
    rw [hq] at h; obtain ⟨h1, h2, h3, h4⟩ := h
    obtain ⟨p1, p2, p3⟩ := hpq y h1
    exact ⟨by rwa [hnode], by rwa [p1], by rwa [p2], by rwa [p3]⟩
  | l18 y => rw [hq] at h; rwa [hnode]
  | l18w y =>
    rw [hq] at h; obtain ⟨h1, h2⟩ := h
    exact ⟨by rwa [hnode], by rwa [(hpq y h1).1]⟩
  | l19 y =>
    rw [hq] at h; obtain ⟨h1, h2⟩ := h
    exact ⟨by rwa [hnode], by rwa [(hpq y h1).1]⟩
  | l22a y =>
    rw [hq] at h; obtain ⟨h1, h2⟩ := h
    exact ⟨by rwa [hnode], by rwa [(hpq y h1).1]⟩
  | l22b => rw [hq] at h; rwa [hnode, hRel]
  | l23 y v =>
    rw [hq] at h; obtain ⟨h1, h2, h3⟩ := h
    exact ⟨by rwa [hnode], by rwa [(hpq y h1).1], h3⟩
  | l24 y v =>
    rw [hq] at h; obtain ⟨h1, h2, h3, h4⟩ := h
    exact ⟨by rwa [hnode], by rwa [(hpq y h1).1], h3, by rwa [(hpq y h1).2.1]⟩
  | l25 y v =>
    rw [hq] at h; obtain ⟨h1, h2, h3, h4⟩ := h
    exact ⟨by rwa [hnode], by rwa [(hpq y h1).1], h3, by rwa [(hpq y h1).2.1]⟩
  | l26 y =>
    rw [hq] at h; obtain ⟨h1, h2, h3⟩ := h
    exact ⟨by rwa [hnode], by rwa [(hpq y h1).1, hRel], by rwa [(hpq y h1).2.1]⟩
  | cs y =>
    rw [hq] at h; obtain ⟨h1, h2, h3⟩ := h
    exact ⟨by rwa [hnode], by rwa [(hpq y h1).1], by rwa [(hpq y h1).2.1]⟩
  | l28 y =>
    rw [hq] at h; obtain ⟨h1, h2, h3, h4⟩ := h
    obtain ⟨p1, p2, p3⟩ := hpq y h1
    exact ⟨by rwa [hnode], by rwa [p1], by rwa [p3], by rwa [p2]⟩
  | l29 => rw [hq] at h; rwa [hnode, hRel]
  | _ => exact absurd (by rw [hq]; trivial) hR

end

section
variable {c : Cfg k} {own : ℕ → ℕ}

/-- `vp` after the repairer moves to line 49 with `mypred = m`. -/
lemma vp_to_l49 (hL : ∀ j, LI c own j) {p : Fin k} {x m : ℕ} (hn : c.node p = some x)
    (hx : c.pred x = .crash) (ho : (c.pc p).ovr = none) (j : Fin k) :
    (c.setPc p (.l49 x m)).vp j = if j = p then .node m else c.vp j := by
  split_ifs with hj
  · subst hj; exact Cfg.vp_of_ovr_some (by simp)
  · exact vp_congr (by simp [hj]) rfl (fun _ _ => rfl)

lemma bh_to_l49 (hG : Glob c own) (hL : ∀ j, LI c own j) {p : Fin k} {x m : ℕ}
    (hn : c.node p = some x) (hx : c.pred x = .crash) (ho : (c.pc p).ovr = none) (a b : ℕ) :
    (c.setPc p (.l49 x m)).Bh a b ↔ c.Bh a b ∨ (a = x ∧ b = m) := by
  have hvp := vp_to_l49 hL hn hx ho (m := m)
  have hcp : c.vp p = .crash := by rw [Cfg.vp_of_ovr_none ho hn, hx]
  constructor
  · rintro ⟨j, hj, hv⟩
    rw [hvp] at hv
    split_ifs at hv with hjp
    · subst hjp; change c.node j = some a at hj; rw [hn] at hj; cases hj; cases hv
      exact .inr ⟨rfl, rfl⟩
    · exact .inl ⟨j, hj, hv⟩
  · rintro (⟨j, hj, hv⟩ | ⟨rfl, rfl⟩)
    · refine ⟨j, hj, ?_⟩
      rw [hvp]
      split_ifs with hjp
      · subst hjp; rw [hcp] at hv; cases hv
      · exact hv
    · exact ⟨p, hn, by rw [hvp]; simp⟩

/-- Lines 46/48 (attach branch): `mypred ← start(headpath)` or `&SpecialNode`. -/
lemma inv_step_l46_attach (hI : Inv c) (p : Fin k) (x tl : ℕ) (V : Finset ℕ)
    (E : Finset (ℕ × ℕ)) (mpath τ : List ℕ) (hpath : Option (List ℕ))
    (h : c.pc p = .l46 x tl V E mpath (some τ) hpath)
    (hio : (c.pred (pend τ)).isInOut = false) :
    Inv (c.setPc p (.l49 x (hstart hpath))) := by
  obtain ⟨own, hG, hL⟩ := hI
  have hl := hL p; unfold LI at hl; rw [h] at hl
  obtain ⟨hn, hx, hnn, EA, hS, hP, hnone⟩ := hl
  set m := hstart hpath with hmdef
  have hA : AttachBr c (some τ) := ⟨τ, rfl, hio⟩
  have hm : (∃ σ, hpath = some σ ∧ m = pstart σ) ∨ (hpath = none ∧ m = special) := by
    cases hpath with
    | none => exact .inr ⟨rfl, rfl⟩
    | some σ => exact .inl ⟨σ, rfl, rfl⟩
  obtain ⟨hbh, htm, hexit, hmx, hmlt, hm13⟩ :=
    hS.attach_facts hG hL hn hx hP hA (hnone hA) hm
  have ho : (c.pc p).ovr = none := by simp [h, PC.ovr]
  have hBh := bh_to_l49 hG hL hn hx ho (m := m)
  set c' := c.setPc p (.l49 x m) with hc'
  have hnoRel : ¬ c.Rel c.tail := hS.attach_not_rel_tail hG hL hP hA
  -- the new holders of the right to the CS
  have hH : ∀ w, c'.InH w → c.InH w ∨ (w = x ∧ c.Rel m ∧ ∀ v, ¬ c.InH v) ∨
      (w = m ∧ c.pred m = .exit ∧ c.csig m = false ∧ ∀ v, ¬ c.InH v) := by
    intro w ⟨hw1, hw2⟩
    rcases hw2 with h1 | ⟨z, h1, h2⟩ | ⟨h1, h2, h3⟩
    · exact .inl ⟨hw1, .inl h1⟩
    · rcases (hBh w z).mp h1 with h1 | ⟨rfl, rfl⟩
      · exact .inl ⟨hw1, .inr (.inl ⟨z, h1, h2⟩)⟩
      · exact .inr (.inl ⟨rfl, h2, hexit h2.1⟩)
    · rcases h3 with ⟨v, hv⟩ | h3
      · rcases (hBh v w).mp hv with hv | ⟨-, rfl⟩
        · exact .inl ⟨hw1, .inr (.inr ⟨h1, h2, .inl ⟨v, hv⟩⟩)⟩
        · exact .inr (.inr ⟨rfl, h1, h2, hexit h1⟩)
      · exact .inl ⟨hw1, .inr (.inr ⟨h1, h2, .inr h3⟩)⟩
  have hvp' : ∀ j, j ≠ p → c'.vp j = c.vp j := by
    intro j hj; rw [hc', vp_to_l49 hL hn hx ho]; simp [hj]
  refine ⟨own, ?_, ?_⟩
  · refine
      { own := hG.own, nodeLt := hG.nodeLt, fresh := hG.fresh, special := hG.special
        nxtPos := hG.nxtPos, table := hG.table, nnPred := hG.nnPred, csigPred := hG.csigPred
        ioNN := hG.ioNN, tailLt := hG.tailLt
        bhLt := by
          intro y z hyz
          rcases (hBh y z).mp hyz with h1 | ⟨-, rfl⟩
          · exact hG.bhLt y z h1
          · exact hmlt
        bhInj := by
          intro y y' z h1 h2
          rcases (hBh y z).mp h1 with h1 | ⟨hy1, hz1⟩ <;>
            rcases (hBh y' z).mp h2 with h2 | ⟨hy2, hz2⟩
          · exact hG.bhInj y y' z h1 h2
          · subst hz2; exact absurd h1 (hbh y)
          · subst hz1; exact absurd h2 (hbh y')
          · rw [hy1, hy2]
        noBhTail := by
          intro y hy
          rcases (hBh y c.tail).mp hy with h1 | ⟨-, h1⟩
          · exact hG.noBhTail y h1
          · exact htm h1
        hUniq := by
          intro y y' h1 h2
          rcases hH y h1 with g1 | ⟨hy1, hr, hno⟩ | ⟨hy1, he, hcs, hno⟩ <;>
            rcases hH y' h2 with g2 | ⟨hy2, hr', hno'⟩ | ⟨hy2, he', hcs', hno'⟩
          · exact hG.hUniq y y' g1 g2
          · exact absurd g1 (hno' y)
          · exact absurd g1 (hno' y)
          · exact absurd g2 (hno y')
          · rw [hy1, hy2]
          · rw [hr.2] at hcs'; cases hcs'
          · exact absurd g2 (hno y')
          · rw [hr'.2] at hcs; cases hcs
          · rw [hy1, hy2]
        relTail := fun hr => absurd hr hnoRel
        wf := wf_add_link hG.wf (fun a b hab => (hBh a b).mp hab) hmx
        holder := by
          intro q hq
          by_cases hqp : q = p
          · subst hqp; exact hG.holder q (by simp [h, PC.InR])
          · simp [c', hqp] at hq; exact hG.holder q hq }
  · intro q
    by_cases hqp : q = p
    · subst hqp; unfold LI; simp only [c', Cfg.setPc_pc_self, Cfg.setPc_node, Cfg.setPc_pred,
        Cfg.setPc_nn]
      exact ⟨hn, hx, hnn⟩
    · have hqR : ¬ (c.pc q).InR := by
        intro hq
        have h1 := hG.holder q hq
        have h2 := hG.holder p (by simp [h, PC.InR])
        rw [h1] at h2; exact hqp (Option.some.inj h2)
      refine (hL q).of_nonR hqR (by simp [c', hqp]) rfl (fun _ _ => ⟨rfl, rfl, rfl⟩) rfl ?_
      intro y hy
      have hl13 := hL q; unfold LI at hl13; rw [hy] at hl13
      refine ⟨fun w hw => ?_, hl13.2.2.2.2.2⟩
      rcases (hBh w y).mp hw with h1 | ⟨-, rfl⟩
      · exact hl13.2.2.2.2.1 w h1
      · exact hm13 q hy

/-- Line 47: `mypred ← FAS(Tail, s)`. -/
lemma inv_step_l47 (hI : Inv c) (p : Fin k) (x s : ℕ) (h : c.pc p = .l47 x s) :
    Inv { c with tail := s, pc := Function.update c.pc p (.l49 x c.tail) } := by
  obtain ⟨own, hG, hL⟩ := hI
  have hl := hL p; unfold LI at hl; rw [h] at hl
  obtain ⟨hn, hx, hnn, hbs, hts, hslt, hs13, hnr, hPL⟩ := hl
  have ho : (c.pc p).ovr = none := by simp [h, PC.ovr]
  have hBh0 := bh_to_l49 hG hL hn hx ho (m := c.tail)
  set c' : Cfg k := { c with tail := s, pc := Function.update c.pc p (.l49 x c.tail) } with hc'
  have hBh : ∀ a b, c'.Bh a b ↔ c.Bh a b ∨ (a = x ∧ b = c.tail) := by
    intro a b; rw [← hBh0]; rfl
  have hsp : c.pred s = .crash ∨ ∃ z, c.pred s = .node z := by
    rcases ReflTransGen.cases_head hPL with h1 | ⟨w, h1, -⟩
    · exact .inl (h1 ▸ hx)
    · exact .inr ⟨w, h1⟩
  have hsnr : ¬ c.Rel s := by
    intro hr; rcases hsp with h1 | ⟨z, h1⟩ <;> rw [hr.1] at h1 <;> cases h1
  have hH : ∀ w, c'.InH w → c.InH w ∨ (w = x ∧ c.Rel c.tail) := by
    intro w ⟨hw1, hw2⟩
    rcases hw2 with h1 | ⟨z, h1, h2⟩ | ⟨h1, h2, h3⟩
    · exact .inl ⟨hw1, .inl h1⟩
    · rcases (hBh w z).mp h1 with h1 | ⟨rfl, rfl⟩
      · exact .inl ⟨hw1, .inr (.inl ⟨z, h1, h2⟩)⟩
      · exact .inr ⟨rfl, h2⟩
    · left; refine ⟨hw1, .inr (.inr ⟨h1, h2, ?_⟩)⟩
      rcases h3 with ⟨v, hv⟩ | h3
      · rcases (hBh v w).mp hv with hv | ⟨-, rfl⟩
        · exact .inl ⟨v, hv⟩
        · exact .inr rfl
      · change s = w at h3; subst h3
        rcases hsp with h4 | ⟨z, h4⟩ <;> rw [h1] at h4 <;> cases h4
  refine ⟨own, ?_, ?_⟩
  · refine
      { own := hG.own, nodeLt := hG.nodeLt, fresh := hG.fresh, special := hG.special
        nxtPos := hG.nxtPos, table := hG.table, nnPred := hG.nnPred, csigPred := hG.csigPred
        ioNN := hG.ioNN, tailLt := hslt
        bhLt := by
          intro y z hyz
          rcases (hBh y z).mp hyz with h1 | ⟨-, rfl⟩
          · exact hG.bhLt y z h1
          · exact hG.tailLt
        bhInj := by
          intro y y' z h1 h2
          rcases (hBh y z).mp h1 with h1 | ⟨hy1, hz1⟩ <;>
            rcases (hBh y' z).mp h2 with h2 | ⟨hy2, hz2⟩
          · exact hG.bhInj y y' z h1 h2
          · subst hz2; exact absurd h1 (hG.noBhTail y)
          · subst hz1; exact absurd h2 (hG.noBhTail y')
          · rw [hy1, hy2]
        noBhTail := by
          intro y hy
          rcases (hBh y s).mp hy with h1 | ⟨-, h1⟩
          · exact hbs y h1
          · exact hts h1.symm
        hUniq := by
          intro y y' h1 h2
          rcases hH y h1 with g1 | ⟨hy1, hr⟩ <;> rcases hH y' h2 with g2 | ⟨hy2, hr'⟩
          · exact hG.hUniq y y' g1 g2
          · exact absurd g1 (hG.relTail hr' y)
          · exact absurd g2 (hG.relTail hr y')
          · rw [hy1, hy2]
        relTail := fun hr => absurd hr hsnr
        wf := wf_add_link hG.wf (fun a b hab => (hBh a b).mp hab) hnr
        holder := by
          intro q hq
          by_cases hqp : q = p
          · subst hqp; exact hG.holder q (by simp [h, PC.InR])
          · simp [c', hqp] at hq; exact hG.holder q hq }
  · intro q
    by_cases hqp : q = p
    · subst hqp; unfold LI; simp [c']
      exact ⟨hn, hx, hnn⟩
    · have hqR : ¬ (c.pc q).InR := by
        intro hq
        have h1 := hG.holder q hq
        have h2 := hG.holder p (by simp [h, PC.InR])
        rw [h1] at h2; exact hqp (Option.some.inj h2)
      refine (hL q).of_nonR hqR (by simp [c', hqp]) rfl (fun _ _ => ⟨rfl, rfl, rfl⟩) rfl ?_
      intro y hy
      have hl13 := hL q; unfold LI at hl13; rw [hy] at hl13
      refine ⟨fun w hw => ?_, fun h' => hs13 q (by rw [show s = y from h']; exact hy)⟩
      rcases (hBh w y).mp hw with h1 | ⟨-, rfl⟩
      · exact hl13.2.2.2.2.1 w h1
      · exact hl13.2.2.2.2.2 rfl

/-- Line 49: `mynode.Pred ← mypred`. -/
lemma inv_step_l49 (hI : Inv c) (p : Fin k) (x m : ℕ) (h : c.pc p = .l49 x m) :
    Inv { c with pred := Function.update c.pred x (.node m),
                 pc := Function.update c.pc p (.rx x (.node m)) } := by
  obtain ⟨own, hG, hL⟩ := hI
  have hl := hL p; unfold LI at hl; rw [h] at hl
  obtain ⟨hn, hx, hnn⟩ := hl
  set c' : Cfg k :=
    { c with pred := Function.update c.pred x (.node m), pc := Function.update c.pc p (.rx x (.node m)) }
    with hc'
  have hxlt := hG.nodeLt p x hn
  have hvp : ∀ j, c'.vp j = c.vp j := by
    intro j
    by_cases hj : j = p
    · subst hj
      rw [Cfg.vp_of_ovr_some (c := c) (m := m) (by simp [h])]
      rw [Cfg.vp_of_ovr_none (c := c') (by simp [c', PC.ovr]) hn]
      simp [c']
    · refine vp_congr (by simp [c', hj]) rfl (fun y hy => ?_)
      have : y ≠ x := fun hyx => hj (hG.node_inj hy (hyx ▸ hn))
      simp [c', this]
  have hBh : c'.Bh = c.Bh := Bh_congr rfl hvp
  have hRel : c'.Rel = c.Rel := by
    funext z; simp only [Cfg.Rel, c']
    by_cases hz : z = x
    · subst hz; simp [hx]
    · simp [hz]
  have hAct : c'.Act = c.Act := Act_congr rfl
  have hInH : c'.InH = c.InH := by
    funext w
    unfold Cfg.InH
    rw [hAct, hBh, hRel]
    have ht : c'.tail = c.tail := rfl
    have hcs : c'.csig = c.csig := rfl
    rw [ht, hcs]
    by_cases hw : w = x
    · subst hw
      have : c'.pred w = .node m := by simp [c']
      rw [this, hx]; simp
    · have : c'.pred w = c.pred w := by simp [c', hw]
      rw [this]
  refine ⟨own, ?_, ?_⟩
  · refine
      { own := hG.own, nodeLt := hG.nodeLt
        fresh := by
          intro a ha
          change c.nxt ≤ a at ha
          have : a ≠ x := by omega
          simpa [c', this] using hG.fresh a ha
        special := by
          have hsx : special ≠ x := fun h0 => by rw [← h0] at hxlt; exact absurd hxlt.1 (lt_irrefl 0)
          simpa [c', hsx] using hG.special
        nxtPos := hG.nxtPos
        table := by rw [hAct, hRel]; exact hG.table
        nnPred := by
          intro a ha
          by_cases hax : a = x
          · subst hax; simp [c']
          · simpa [c', hax] using hG.nnPred a ha
        csigPred := by
          intro a ha
          by_cases hax : a = x
          · subst hax; have := hG.csigPred a ha; rw [hx] at this; cases this
          · simpa [c', hax] using hG.csigPred a ha
        ioNN := by
          intro a ha
          by_cases hax : a = x
          · subst hax; simp [c'] at ha
          · exact hG.ioNN a (by simpa [c', hax] using ha)
        tailLt := hG.tailLt
        bhLt := by rw [hBh]; exact hG.bhLt
        bhInj := by rw [hBh]; exact hG.bhInj
        noBhTail := by rw [hBh]; exact hG.noBhTail
        hUniq := by rw [hInH]; exact hG.hUniq
        relTail := by rw [hRel, hInH]; exact hG.relTail
        wf := by rw [hBh]; exact hG.wf
        holder := by
          intro q hq
          by_cases hqp : q = p
          · subst hqp; exact hG.holder q (by simp [h, PC.InR])
          · simp [c', hqp] at hq; exact hG.holder q hq }
  · intro q
    by_cases hqp : q = p
    · subst hqp; unfold LI; simp [c']
      exact ⟨hn, hnn⟩
    · have hqR : ¬ (c.pc q).InR := by
        intro hq
        have h1 := hG.holder q hq
        have h2 := hG.holder p (by simp [h, PC.InR])
        rw [h1] at h2; exact hqp (Option.some.inj h2)
      refine (hL q).of_nonR hqR (by simp [c', hqp]) rfl (fun y hy => ?_) hRel ?_
      · have : y ≠ x := fun hyx => hqp (hG.node_inj hy (hyx ▸ hn))
        simp [c', this]
      · intro y hy
        have hl13 := hL q; unfold LI at hl13; rw [hy] at hl13
        rw [hBh]; exact ⟨hl13.2.2.2.2.1, hl13.2.2.2.2.2⟩

end

end Podc.RMESubLogBoth
