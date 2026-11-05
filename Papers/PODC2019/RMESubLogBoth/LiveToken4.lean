import Papers.PODC2019.RMESubLogBoth.LiveToken3

/-!
# Liveness, part 3 (cont.): the rank under lines 27–29, 11–13
-/

namespace Podc.RMESubLogBoth

variable {k : ℕ}

open Relation Classical

section
variable {c c' : Cfg k} {own : ℕ → ℕ}

/-- Line 27 (only the holder is in the CS). -/
lemma token_cs (hG : Glob c own) (hL : ∀ q, LI c own q) {own' : ℕ → ℕ} {s : Fin k} {x : ℕ}
    (h : c.pc s = .cs x) {yp : ℕ} (hsucc : ∃ w, c.Bh w x)
    (hc' : c' = { c with pred := Function.update c.pred x .exit,
                         pc := Function.update c.pc s (.l28 x) }) (hG' : Glob c' own') :
    HO c s ∧ tokMu c' yp < tokMu c yp := by
  have hLs := hL s; unfold LI at hLs; rw [h] at hLs
  obtain ⟨hn, hxi, -⟩ := hLs
  have hHx : c.InH x := ⟨⟨s, hn⟩, .inl hxi⟩
  have hs : HO c s := ⟨x, hn, hHx⟩
  refine ⟨hs, ?_⟩
  have hcx : c.csig x = false := by
    cases hc : c.csig x
    · rfl
    · have := hG.csigPred x hc; rw [hxi] at this; cases this
  have hnode : c'.node = c.node := by rw [hc']
  have hcsig : c'.csig = c.csig := by rw [hc']
  have htail : c'.tail = c.tail := by rw [hc']
  have hpcs : c'.pc s = .l28 x := by rw [hc']; simp
  have hpco : ∀ j, j ≠ s → c'.pc j = c.pc j := fun j hj => by rw [hc']; simp [hj]
  have hpred : ∀ a, a ≠ x → c'.pred a = c.pred a := fun a ha => by rw [hc']; simp [ha]
  have hpx : c'.pred x = .exit := by rw [hc']; simp
  have hvpn : ∀ j b, c'.vp j = .node b ↔ c.vp j = .node b := by
    intro j b
    by_cases hjs : j = s
    · subst hjs
      rw [Cfg.vp_of_ovr_none (c := c') (by simp [hpcs, PC.ovr]) (by rw [hnode]; exact hn), hpx,
        Cfg.vp_of_ovr_none (c := c) (by simp [h, PC.ovr]) hn, hxi]
      simp
    · rw [vp_eq_other hG hn hjs (hpco j hjs) (by rw [hnode]) hpred]
  have hBh : c'.Bh = c.Bh := by
    funext a b; simp only [Cfg.Bh, hnode, hvpn]
  have hRel : c'.Rel = c.Rel := by
    funext z
    simp only [Cfg.Rel, hcsig]
    by_cases hz : z = x
    · subst hz; simp [hcx, hxi]
    · rw [hpred z hz]
  have hH : c'.InH = c.InH := by
    funext y
    by_cases hyx : y = x
    · subst hyx
      apply propext
      refine ⟨fun _ => hHx, fun _ => ⟨by rw [Cfg.Act, hnode]; exact ⟨s, hn⟩,
        .inr (.inr ⟨hpx, by rw [hcsig]; exact hcx, .inl ?_⟩)⟩⟩
      obtain ⟨w, hw⟩ := hsucc; exact ⟨w, by rw [hBh]; exact hw⟩
    · simp only [Cfg.InH, Cfg.Act, hnode, hpred y hyx, hcsig, htail, hRel, hBh]
  exact tokMu_view_owner hG hG' hnode hBh hRel hH hs (by simp [hpcs, h, HW])

/-- Line 28. -/
lemma token_l28 (hG : Glob c own) (hL : ∀ q, LI c own q) {own' : ℕ → ℕ} {s : Fin k} {x : ℕ}
    (h : c.pc s = .l28 x) {yp : ℕ}
    (hc' : c' = { c with csig := Function.update c.csig x true,
                         pc := Function.update c.pc s .l29 }) (hG' : Glob c' own') :
    (¬ HO c s → tokMu c' yp = tokMu c yp ∧ ∀ q, HO c' q ↔ HO c q) ∧
      (HO c s → TransGen c.Bh yp x → tokMu c' yp < tokMu c yp) := by
  have hLs := hL s; unfold LI at hLs; rw [h] at hLs
  obtain ⟨hn, hxe, hcx, -⟩ := hLs
  have hnode : c'.node = c.node := by rw [hc']
  have hpred : c'.pred = c.pred := by rw [hc']
  have htail : c'.tail = c.tail := by rw [hc']
  have hpcs : c'.pc s = .l29 := by rw [hc']; simp
  have hpco : ∀ j, j ≠ s → c'.pc j = c.pc j := fun j hj => by rw [hc']; simp [hj]
  have hcs : ∀ a, a ≠ x → c'.csig a = c.csig a := fun a ha => by rw [hc']; simp [ha]
  have hcxx : c'.csig x = true := by rw [hc']; simp
  have hvp : ∀ j, c'.vp j = c.vp j := fun j => by
    refine vp_congr ?_ (by rw [hnode]) (fun _ _ => by rw [hpred])
    by_cases hj : j = s
    · subst hj; simp [hpcs, h, PC.ovr]
    · rw [hpco j hj]
  have hBh : c'.Bh = c.Bh := Bh_congr hnode hvp
  have hRel : ∀ z, c'.Rel z ↔ c.Rel z ∨ z = x := by
    intro z
    simp only [Cfg.Rel, hpred]
    by_cases hz : z = x
    · subst hz; simp [hcxx, hxe]
    · rw [hcs z hz]; simp [hz]
  have hnobh : ∀ z, ¬ c.Bh x z := fun z hz => by
    rcases pred_of_bh hL hz with h4 | ⟨_, _, _, h4⟩ | ⟨_, _, _, h4⟩ <;> rw [hxe] at h4 <;> cases h4
  constructor
  · intro hs
    have hxH : ¬ c.InH x := fun hx => hs ⟨x, hn, hx⟩
    have hnb : ∀ w, ¬ c.Bh w x := fun w hw => hxH ⟨⟨s, hn⟩, .inr (.inr ⟨hxe, hcx, .inl ⟨w, hw⟩⟩)⟩
    have hH : ∀ y, c'.InH y ↔ c.InH y := by
      intro y
      by_cases hyx : y = x
      · subst hyx
        refine ⟨fun hy => ?_, fun hy => absurd hy hxH⟩
        obtain ⟨-, h1 | ⟨z, hz, -⟩ | ⟨-, h2, -⟩⟩ := hy
        · rw [hpred, hxe] at h1; cases h1
        · rw [hBh] at hz; exact absurd hz (hnobh z)
        · rw [hcxx] at h2; cases h2
      · simp only [Cfg.InH, Cfg.Act, hnode, hpred, htail, hBh, hcs y hyx]
        constructor
        · rintro ⟨h1, h2 | ⟨z, hz, hRz⟩ | h3⟩
          · exact ⟨h1, .inl h2⟩
          · rcases (hRel z).mp hRz with hRz | rfl
            · exact ⟨h1, .inr (.inl ⟨z, hz, hRz⟩)⟩
            · exact absurd hz (hnb y)
          · exact ⟨h1, .inr (.inr h3)⟩
        · rintro ⟨h1, h2 | ⟨z, hz, hRz⟩ | h3⟩
          · exact ⟨h1, .inl h2⟩
          · exact ⟨h1, .inr (.inl ⟨z, hz, (hRel z).mpr (.inl hRz)⟩)⟩
          · exact ⟨h1, .inr (.inr h3)⟩
    have ha : ∀ q, Anc c' yp q ↔ Anc c yp q := by
      intro q
      simp only [Anc, hnode, hBh]
      constructor
      · rintro ⟨z, hz, hr, hRz⟩; exact ⟨z, hz, hr, fun h' => hRz ((hRel z).mpr (.inl h'))⟩
      · rintro ⟨z, hz, hr, hRz⟩
        refine ⟨z, hz, hr, fun h' => ?_⟩
        rcases (hRel z).mp h' with h' | rfl
        · exact hRz h'
        · obtain ⟨w, -, hw⟩ := TransGen.tail'_iff.mp hr; exact hnb w hw
    have hho : ∀ q, HO c' q ↔ HO c q := fun q => by simp only [HO, hnode, hH]
    exact ⟨tokMu_eq ha hho (fun q hq => hpco q (fun h' => hs (h' ▸ hq))), hho⟩
  · intro hs hanc
    have hs1 : s ∈ Finset.univ.filter (Anc c yp) := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨x, hn, hanc, fun hr => by rw [hr.2] at hcx; cases hcx⟩
    have hs2 : s ∉ Finset.univ.filter (Anc c' yp) := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Anc, hnode, hn]
      rintro ⟨z, hz, -, hRz⟩; cases hz; exact hRz ((hRel _).mpr (.inr rfl))
    have hss : Finset.univ.filter (Anc c' yp) ⊆ Finset.univ.filter (Anc c yp) := by
      intro q; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Anc, hnode, hBh]
      rintro ⟨z, hz, hr, hRz⟩; exact ⟨z, hz, hr, fun h' => hRz ((hRel z).mpr (.inl h'))⟩
    have hsub := (Finset.ssubset_iff_of_subset hss).mpr ⟨s, hs1, hs2⟩
    have hlt := Finset.card_lt_card hsub
    have h1 := hstage_le (c := c') hG'
    have h2 := hstage_eq hG hs
    have h3 : HW (c.pc s) = 1 := by rw [h]; rfl
    unfold tokMu
    rw [h2, h3]; omega

/-- Line 29. -/
lemma token_l29 (hG : Glob c own) (hL : ∀ q, LI c own q) {own' : ℕ → ℕ} {s : Fin k}
    (h : c.pc s = .l29) {yp : ℕ}
    (hc' : c' = { c with node := Function.update c.node s none,
                         pc := Function.update c.pc s .rem }) :
    ¬ HO c s ∧ tokMu c' yp = tokMu c yp ∧ ∀ q, HO c' q ↔ HO c q := by
  have hLs := hL s; unfold LI at hLs; rw [h] at hLs
  obtain ⟨x, hn, hxr⟩ := hLs
  have hs : ¬ HO c s := by
    rintro ⟨z, hz, hH⟩; rw [hn] at hz; cases hz; exact InH.not_rel hG hL hH hxr
  have hpred : c'.pred = c.pred := by rw [hc']
  have hcsig : c'.csig = c.csig := by rw [hc']
  have htail : c'.tail = c.tail := by rw [hc']
  have hns : c'.node s = none := by rw [hc']; simp
  have hno : ∀ j, j ≠ s → c'.node j = c.node j := fun j hj => by rw [hc']; simp [hj]
  have hpco : ∀ j, j ≠ s → c'.pc j = c.pc j := fun j hj => by rw [hc']; simp [hj]
  have hRel : c'.Rel = c.Rel := Rel_congr hpred hcsig
  have hBh : ∀ a b, c'.Bh a b ↔ c.Bh a b := by
    intro a b
    constructor
    · rintro ⟨j, hj, hv⟩
      have hjs : j ≠ s := fun hjs => by rw [hjs, hns] at hj; cases hj
      rw [hno j hjs] at hj
      exact ⟨j, hj, by rwa [vp_congr (by rw [hpco j hjs]) (hno j hjs) (fun _ _ => by rw [hpred])]
        at hv⟩
    · rintro ⟨j, hj, hv⟩
      have hjs : j ≠ s := fun hjs => by
        subst hjs; rw [hn] at hj; cases hj; exact not_bh_of_rel hL hxr ⟨j, hn, hv⟩
      exact ⟨j, by rw [hno j hjs]; exact hj,
        by rwa [vp_congr (by rw [hpco j hjs]) (hno j hjs) (fun _ _ => by rw [hpred])]⟩
  have hBh' : c'.Bh = c.Bh := by funext a b; exact propext (hBh a b)
  have hAct : ∀ y, y ≠ x → (c'.Act y ↔ c.Act y) := by
    intro y hyx
    constructor
    · rintro ⟨j, hj⟩
      have hjs : j ≠ s := fun hjs => by rw [hjs, hns] at hj; cases hj
      exact ⟨j, by rwa [hno j hjs] at hj⟩
    · rintro ⟨j, hj⟩
      have hjs : j ≠ s := fun hjs => by rw [hjs, hn] at hj; cases hj; exact hyx rfl
      exact ⟨j, by rw [hno j hjs]; exact hj⟩
  have hH : ∀ y, c'.InH y ↔ c.InH y := by
    intro y
    by_cases hyx : y = x
    · subst hyx
      refine ⟨fun hy => ?_, fun hy => absurd hxr (InH.not_rel hG hL hy)⟩
      obtain ⟨⟨j, hj⟩, -⟩ := hy
      have hjs : j ≠ s := fun hjs => by rw [hjs, hns] at hj; cases hj
      rw [hno j hjs] at hj; exact absurd (hG.node_inj hj hn) hjs
    · simp only [Cfg.InH, hAct y hyx, hpred, hcsig, htail, hBh', hRel]
  have hho : ∀ q, HO c' q ↔ HO c q := by
    intro q
    by_cases hqs : q = s
    · subst hqs
      constructor
      · rintro ⟨z, hz, -⟩; rw [hns] at hz; cases hz
      · intro h'; exact absurd h' hs
    · simp only [HO, hno q hqs, hH]
  have ha : ∀ q, Anc c' yp q ↔ Anc c yp q := by
    intro q
    by_cases hqs : q = s
    · subst hqs
      simp only [Anc, hns, hn]
      constructor
      · rintro ⟨z, hz, -⟩; cases hz
      · rintro ⟨z, hz, -, hRz⟩; cases hz; exact absurd hxr hRz
    · simp only [Anc, hno q hqs, hBh', hRel]
  exact ⟨hs, tokMu_eq ha hho (fun q hq => hpco q (fun h' => hs (h' ▸ hq))), hho⟩

end

end Podc.RMESubLogBoth
