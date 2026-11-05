import Papers.PODC2019.RMESubLogBoth.LiveToken4

/-!
# Liveness, part 3 (cont.): the rank under lines 11–13, and the one-step lemma
-/

namespace Podc.RMESubLogBoth

variable {k : ℕ}

open Relation Classical

section
variable {c c' : Cfg k} {own : ℕ → ℕ}

/-- Lines 11–12. -/
lemma token_l11 (hG : Glob c own) (hL : ∀ q, LI c own q) {s : Fin k} (h : c.pc s = .l11)
    {yp : ℕ}
    (hc' : c' = { c with node := Function.update c.node s (some c.nxt), nxt := c.nxt + 1,
                         pc := Function.update c.pc s (.l13 c.nxt) }) :
    ¬ HO c s ∧ tokMu c' yp = tokMu c yp ∧ ∀ q, HO c' q ↔ HO c q := by
  have hLs := hL s; unfold LI at hLs; rw [h] at hLs
  have hs : ¬ HO c s := by rintro ⟨z, hz, -⟩; rw [hLs] at hz; cases hz
  have hpred : c'.pred = c.pred := by rw [hc']
  have hcsig : c'.csig = c.csig := by rw [hc']
  have htail : c'.tail = c.tail := by rw [hc']
  have hns : c'.node s = some c.nxt := by rw [hc']; simp
  have hno : ∀ j, j ≠ s → c'.node j = c.node j := fun j hj => by rw [hc']; simp [hj]
  have hpcs : c'.pc s = .l13 c.nxt := by rw [hc']; simp
  have hpco : ∀ j, j ≠ s → c'.pc j = c.pc j := fun j hj => by rw [hc']; simp [hj]
  have hfresh := hG.fresh c.nxt le_rfl
  have hRel : c'.Rel = c.Rel := Rel_congr hpred hcsig
  have hBh : ∀ a b, c'.Bh a b ↔ c.Bh a b := by
    intro a b
    constructor
    · rintro ⟨j, hj, hv⟩
      by_cases hjs : j = s
      · subst hjs
        rw [Cfg.vp_of_ovr_none (by simp [hpcs, PC.ovr]) hns, hpred, hfresh.1] at hv; cases hv
      · rw [hno j hjs] at hj
        exact ⟨j, hj, by rwa [vp_congr (by rw [hpco j hjs]) (hno j hjs)
          (fun _ _ => by rw [hpred])] at hv⟩
    · rintro ⟨j, hj, hv⟩
      have hjs : j ≠ s := fun hjs => by rw [hjs, hLs] at hj; cases hj
      exact ⟨j, by rw [hno j hjs]; exact hj,
        by rwa [vp_congr (by rw [hpco j hjs]) (hno j hjs) (fun _ _ => by rw [hpred])]⟩
  have hBh' : c'.Bh = c.Bh := by funext a b; exact propext (hBh a b)
  have hAct : ∀ y, y ≠ c.nxt → (c'.Act y ↔ c.Act y) := by
    intro y hy
    constructor
    · rintro ⟨j, hj⟩
      have hjs : j ≠ s := fun hjs => by rw [hjs, hns] at hj; exact hy (Option.some.inj hj).symm
      exact ⟨j, by rwa [hno j hjs] at hj⟩
    · rintro ⟨j, hj⟩
      have hjs : j ≠ s := fun hjs => by rw [hjs, hLs] at hj; cases hj
      exact ⟨j, by rw [hno j hjs]; exact hj⟩
  have hH : ∀ y, c'.InH y ↔ c.InH y := by
    intro y
    by_cases hy : y = c.nxt
    · subst hy
      constructor
      · rintro ⟨-, h1 | ⟨z, hz, -⟩ | ⟨h1, -⟩⟩
        · rw [hpred, hfresh.1] at h1; cases h1
        · rw [hBh'] at hz; exact absurd (hG.pos_of_bh hz).2 (lt_irrefl _)
        · rw [hpred, hfresh.1] at h1; cases h1
      · rintro ⟨⟨j, hj⟩, -⟩; exact absurd (hG.nodeLt j _ hj).2 (lt_irrefl _)
    · simp only [Cfg.InH, hAct y hy, hpred, hcsig, htail, hBh', hRel]
  have hho : ∀ q, HO c' q ↔ HO c q := by
    intro q
    by_cases hqs : q = s
    · subst hqs
      constructor
      · rintro ⟨z, hz, hz'⟩; rw [hns] at hz; cases hz; exact absurd ((hH _).mp hz') (by
          rintro ⟨⟨j, hj⟩, -⟩; exact absurd (hG.nodeLt j _ hj).2 (lt_irrefl _))
      · intro h'; exact absurd h' hs
    · simp only [HO, hno q hqs, hH]
  have ha : ∀ q, Anc c' yp q ↔ Anc c yp q := by
    intro q
    by_cases hqs : q = s
    · subst hqs
      simp only [Anc, hns, hLs, hBh', hRel]
      constructor
      · rintro ⟨z, hz, hr, -⟩; cases hz
        obtain ⟨w, -, hw⟩ := TransGen.tail'_iff.mp hr
        exact absurd (hG.bhLt _ _ hw) (lt_irrefl _)
      · rintro ⟨z, hz, -⟩; cases hz
    · simp only [Anc, hno q hqs, hBh', hRel]
  exact ⟨hs, tokMu_eq ha hho (fun q hq => hpco q (fun h' => hs (h' ▸ hq))), hho⟩

/-- Line 13 (FAS), when the right to the CS is held by somebody (so `Tail` is not released). -/
lemma token_l13 (hG : Glob c own) (hL : ∀ q, LI c own q) {s : Fin k} {x : ℕ}
    (h : c.pc s = .l13 x) {yp : ℕ} (hyp : yp ≠ x) (hnr : ¬ c.Rel c.tail)
    (hc' : c' = { c with tail := x, pc := Function.update c.pc s (.l14 x c.tail) }) :
    ¬ HO c s ∧ tokMu c' yp = tokMu c yp ∧ ∀ q, HO c' q ↔ HO c q := by
  have hLs := hL s; unfold LI at hLs; rw [h] at hLs
  obtain ⟨hn, hxn, -, -, hnb, htx⟩ := hLs
  have hvps : c.vp s = .nil := by rw [Cfg.vp_of_ovr_none (by simp [h, PC.ovr]) hn, hxn]
  have hs : ¬ HO c s := by
    rintro ⟨z, hz, ⟨-, h1 | ⟨w, hw, -⟩ | ⟨h1, -⟩⟩⟩ <;> rw [hn] at hz <;> cases hz
    · rw [hxn] at h1; cases h1
    · obtain ⟨j, hj, hv⟩ := hw
      have := hG.node_inj hj hn; subst this; rw [hvps] at hv; cases hv
    · rw [hxn] at h1; cases h1
  have hnode : c'.node = c.node := by rw [hc']
  have hpred : c'.pred = c.pred := by rw [hc']
  have hcsig : c'.csig = c.csig := by rw [hc']
  have htail : c'.tail = x := by rw [hc']
  have hpcs : c'.pc s = .l14 x c.tail := by rw [hc']; simp
  have hpco : ∀ j, j ≠ s → c'.pc j = c.pc j := fun j hj => by rw [hc']; simp [hj]
  have hRel : c'.Rel = c.Rel := Rel_congr hpred hcsig
  have hBh : ∀ a b, c'.Bh a b ↔ c.Bh a b ∨ (a = x ∧ b = c.tail) := by
    intro a b
    constructor
    · rintro ⟨j, hj, hv⟩
      rw [hnode] at hj
      by_cases hjs : j = s
      · subst hjs; rw [hn] at hj; cases hj
        rw [Cfg.vp_of_ovr_some (m := c.tail) (by simp [hpcs])] at hv; cases hv
        exact .inr ⟨rfl, rfl⟩
      · refine .inl ⟨j, hj, ?_⟩
        rw [← vp_congr (c := c) (c' := c') (by rw [hpco j hjs]) (by rw [hnode])
          (fun _ _ => by rw [hpred])]
        exact hv
    · rintro (⟨j, hj, hv⟩ | ⟨rfl, rfl⟩)
      · have hjs : j ≠ s := fun hjs => by subst hjs; rw [hvps] at hv; cases hv
        refine ⟨j, by rw [hnode]; exact hj, ?_⟩
        rw [vp_congr (c := c) (c' := c') (by rw [hpco j hjs]) (by rw [hnode])
          (fun _ _ => by rw [hpred])]
        exact hv
      · exact ⟨s, by rw [hnode]; exact hn, Cfg.vp_of_ovr_some (by simp [hpcs])⟩
  have hnbx : ∀ w, ¬ c'.Bh w x := by
    intro w hw
    rcases (hBh w x).mp hw with h1 | ⟨-, h1⟩
    · exact hnb w h1
    · exact htx h1.symm
  have hH : ∀ y, c'.InH y ↔ c.InH y := by
    intro y
    by_cases hyx : y = x
    · subst hyx
      refine ⟨fun hy => ?_, fun hy => absurd ⟨y, hn, hy⟩ hs⟩
      obtain ⟨-, h1 | ⟨z, hz, hRz⟩ | ⟨h1, -⟩⟩ := hy
      · rw [hpred, hxn] at h1; cases h1
      · rcases (hBh y z).mp hz with ⟨j, hj, hv⟩ | ⟨-, rfl⟩
        · have := hG.node_inj hj hn; subst this; rw [hvps] at hv; cases hv
        · rw [hRel] at hRz; exact absurd hRz hnr
      · rw [hpred, hxn] at h1; cases h1
    · simp only [Cfg.InH, Cfg.Act, hnode, hpred, hcsig, htail, hRel]
      constructor
      · rintro ⟨h1, h2 | ⟨z, hz, hRz⟩ | ⟨h2, h3, h4⟩⟩
        · exact ⟨h1, .inl h2⟩
        · rcases (hBh y z).mp hz with hz | ⟨h5, -⟩
          · exact ⟨h1, .inr (.inl ⟨z, hz, hRz⟩)⟩
          · exact absurd h5 hyx
        · refine ⟨h1, .inr (.inr ⟨h2, h3, ?_⟩)⟩
          rcases h4 with ⟨w, hw⟩ | h4
          · rcases (hBh w y).mp hw with hw | ⟨-, rfl⟩
            · exact .inl ⟨w, hw⟩
            · exact .inr rfl
          · exact absurd h4.symm hyx
      · rintro ⟨h1, h2 | ⟨z, hz, hRz⟩ | ⟨h2, h3, h4⟩⟩
        · exact ⟨h1, .inl h2⟩
        · exact ⟨h1, .inr (.inl ⟨z, (hBh y z).mpr (.inl hz), hRz⟩)⟩
        · refine ⟨h1, .inr (.inr ⟨h2, h3, .inl ?_⟩)⟩
          rcases h4 with ⟨w, hw⟩ | h4
          · exact ⟨w, (hBh w y).mpr (.inl hw)⟩
          · exact ⟨x, (hBh x y).mpr (.inr ⟨rfl, h4.symm⟩)⟩
  have hho : ∀ q, HO c' q ↔ HO c q := fun q => by simp only [HO, hnode, hH]
  -- reachability from `yp` does not change: nobody is behind `x`
  have hreach : ∀ z, TransGen c'.Bh yp z ↔ TransGen c.Bh yp z := by
    intro z
    constructor
    · intro hr
      have key : ∀ a, TransGen c'.Bh a z → a ≠ x → TransGen c.Bh a z := by
        intro a ha
        induction ha using TransGen.head_induction_on with
        | single e =>
          intro hax
          rcases (hBh _ _).mp e with e | ⟨h1, -⟩
          · exact .single e
          · exact absurd h1 hax
        | @head a b e _ ih =>
          intro hax
          rcases (hBh _ _).mp e with e | ⟨h1, -⟩
          · exact .head e (ih (fun hbx => hnbx a (hbx ▸ (hBh a b).mpr (.inl e))))
          · exact absurd h1 hax
      exact key yp hr hyp
    · intro hr
      exact TransGen.mono (fun a b hab => (hBh a b).mpr (.inl hab)) _ _ hr
  have ha : ∀ q, Anc c' yp q ↔ Anc c yp q := fun q => by simp only [Anc, hnode, hreach, hRel]
  exact ⟨hs, tokMu_eq ha hho (fun q hq => hpco q (fun h' => hs (h' ▸ hq))), hho⟩

/-- **One step of the token argument.** Outside the recovery code, a step of a process that does
not hold the right to the CS does not change the rank, and a step of the holder decreases it (or
brings `p` into the CS). -/
theorem token_step (hI : Inv c) (hI' : Inv c') (hNR : NoRec c) {s : Fin k} (h : Step c s c')
    {p : Fin k} {yp : ℕ} (hph : Ph2 c p yp) :
    (¬ HO c s → tokMu c' yp = tokMu c yp ∧ ∀ q, HO c' q ↔ HO c q) ∧
      (HO c s → tokMu c' yp < tokMu c yp ∨ c'.pc p = .cs yp) := by
  obtain ⟨own, hG, hL⟩ := hI
  obtain ⟨own', hG', -⟩ := hI'
  obtain ⟨s0, x0, hs0, hx0, hr0⟩ := hph.holder hG hL hNR
  have hnr : ¬ c.Rel c.tail := fun ht => hG.relTail ht x0 hx0
  -- for a holder `s` other than `p`, its node is a strict ancestor of `yp`
  have hanc : ∀ x, c.node s = some x → c.InH x → s ≠ p → TransGen c.Bh yp x := by
    intro x hx hHx hsp
    have := hG.hUniq x x0 hHx hx0; subst this
    rcases ReflTransGen.cases_tail hr0 with h1 | ⟨w, h1, h2⟩
    · exact absurd (hG.node_inj hx (h1 ▸ hph.1)) hsp
    · exact TransGen.tail'_iff.mpr ⟨w, h1, h2⟩
  have hpl := hNR.plain s
  have hpre := (hNR s).1
  have hLs := hL s
  unfold LI at hLs
  have hppc := hph.2
  cases h with
  | l10_nil h1 hn =>
    rcases h1 with h1 | h1
    · have r := token_setPc (r := .l11) (yp := yp) hG (by simpa using hG') (by simp [h1, PC.ovr])
        (fun hs => by obtain ⟨z, hz, -⟩ := hs; rw [hn] at hz; cases hz)
      exact ⟨r.1, fun hs => .inl (r.2 hs)⟩
    · simp [preW, h1, hn] at hpre
  | l10_some h1 x hn =>
    rcases h1 with h1 | h1
    · rw [h1] at hLs; rw [hLs] at hn; cases hn
    · simp [preW, h1, hn] at hpre
  | l11 h1 =>
    obtain ⟨hs, h2, h3⟩ := token_l11 (yp := yp) hG hL h1 rfl
    exact ⟨fun _ => ⟨h2, h3⟩, fun h' => absurd h' hs⟩
  | l13 x h1 =>
    have hyx : yp ≠ x := by
      intro hyx; subst hyx
      rw [h1] at hLs
      have := hG.node_inj hLs.1 hph.1; subst this
      exact hph.not_l13 _ h1
    obtain ⟨hs, h2, h3⟩ := token_l13 hG hL h1 hyx hnr rfl
    exact ⟨fun _ => ⟨h2, h3⟩, fun h' => absurd h' hs⟩
  | l14 x m h1 =>
    have r := token_l14 (yp := yp) hG hL h1 rfl hG'
    exact ⟨r.1, fun hs => .inl (r.2 hs)⟩
  | l15 x m h1 =>
    have r := token_l15 (yp := yp) hG h1 rfl hG'
    exact ⟨r.1, fun hs => .inl (r.2 hs)⟩
  | l25 x v h1 =>
    rw [h1] at hLs
    obtain ⟨-, -, ⟨m, rfl⟩, -⟩ := hLs
    simp only
    by_cases hcm : c.csig m = true
    · rw [if_pos hcm]
      have r := token_setPc (r := .l26 x) (yp := yp) hG (by simpa [hcm] using hG')
        (by simp [h1, PC.ovr]) (fun _ => by simp [h1, HW])
      exact ⟨r.1, fun hs => .inl (r.2 hs)⟩
    · rw [if_neg hcm, Cfg.setPc_eq_self h1]
      exact ⟨fun _ => ⟨rfl, fun _ => Iff.rfl⟩, fun hs => absurd (HO.l25 hG hL h1 hs) hcm⟩
  | l26 x h1 =>
    obtain ⟨hs, h2⟩ := token_l26 (yp := yp) hG hL h1 rfl hG'
    refine ⟨fun h' => absurd hs h', fun _ => ?_⟩
    rcases h2 with h2 | h2
    · exact .inl h2
    · subst h2
      rw [h1] at hLs
      have := hG.node_inj hLs.1 hph.1; subst this
      right; simp
  | cs x h1 =>
    rw [h1] at hLs
    have hsp : s ≠ p := by
      rintro rfl
      rcases hppc with ⟨m, h2⟩ | ⟨m, h2⟩ | ⟨v, h2⟩ | h2 <;> rw [h1] at h2 <;> cases h2
    have hHx : c.InH x := ⟨⟨s, hLs.1⟩, .inl hLs.2.1⟩
    obtain ⟨w, -, hw⟩ := TransGen.tail'_iff.mp (hanc x hLs.1 hHx hsp)
    obtain ⟨hs, h2⟩ := token_cs (yp := yp) hG hL h1 ⟨w, hw⟩ rfl hG'
    exact ⟨fun h' => absurd hs h', fun _ => .inl h2⟩
  | l28 x h1 =>
    have r := token_l28 (yp := yp) hG hL h1 rfl hG'
    refine ⟨r.1, fun hs => .inl (r.2 hs ?_)⟩
    rw [h1] at hLs
    have hsp : s ≠ p := by
      rintro rfl
      rcases hppc with ⟨m, h2⟩ | ⟨m, h2⟩ | ⟨v, h2⟩ | h2 <;> rw [h1] at h2 <;> cases h2
    obtain ⟨z, hz, hHz⟩ := hs
    rw [hLs.1] at hz; cases hz
    exact hanc _ hLs.1 hHz hsp
  | l29 h1 =>
    obtain ⟨hs, h2, h3⟩ := token_l29 (yp := yp) (own' := own') hG hL h1 rfl
    exact ⟨fun _ => ⟨h2, h3⟩, fun h' => absurd h' hs⟩
  | _ => exfalso; simp_all [PC.Plain]

end

end Podc.RMESubLogBoth
