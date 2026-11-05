import Papers.PODC2023.DuraCAS.AInv

/-!
# Frame lemmas of the A-level invariant

A change of an object (install, move, imprint) made by one process preserves the local
invariant `Loc` of every other process (with the witness update `massWit`).
-/

namespace Podc.DuraCAS

set_option linter.unusedSectionVars false

variable {P K V : Type} [DecidableEq P] [DecidableEq K] [DecidableEq V]

/-! ### Frame lemmas -/

theorem stage_of_not {v : KV V} {need s2 : Prop} (pc : APc V) (h : ¬need) : Stage v need s2 pc := by
  rcases pc with c | ⟨c, b⟩ <;> cases c <;> simp [Stage, h]

/-- Program counters inside `TRANSFER-WRITE`. -/
def IsTw : APc V → Prop
  | .at (.tw19 _) => True
  | .at (.tw20 _ _) => True
  | .at (.tw21 _ _ _) => True
  | .aft (.tw21 _ _ _) _ => True
  | _ => False

theorem stage_np {v : KV V} {need s2 : Prop} {pc : APc V} (h : Stage v need s2 pc) (hpc : IsTw pc)
    (hn : need) : v.pend := by
  rcases pc with c | ⟨c, b⟩ <;> cases c <;> simp_all [Stage, IsTw]

theorem stage_congr {v v' : KV V} {need need' s2 : Prop} (pc : APc V) (hn : need' ↔ need)
    (h : ¬need) : Stage v' need' s2 pc :=
  stage_of_not pc (by rwa [hn])

/-- An install by another write preserves `Loc`. -/
theorem loc_inst {p : P} {v v' : KV V} {x : PV P K V} {id : ℕ} (hl : Loc p v x) (hv : v.Inv)
    (h : Inst v v' id) (hid : id ≠ x.r.id) : Loc p v' x := by
  obtain ⟨W', Z', pw', zAt', lm', sig'⟩ := v'
  obtain ⟨hnp, hW1, hWb, rfl, rfl, rfl, rfl, rfl, ha38⟩ := h
  simp only at hW1 hWb ha38
  have hpw : v.pw = none := by
    by_contra h'; exact hnp (hv.pend_iff.2 h')
  have hb : v.W.2.2 = v.Z.2.2 := not_not.1 hnp
  have hp' : (KV.pend ⟨W', v.Z, some id, v.Z.1, v.lm, v.sig⟩) := by
    unfold KV.pend; intro h'; exact hWb (h'.trans hb.symm)
  have hidq : some id ≠ some x.r.id := by simpa using hid
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hl
  refine ⟨h1, h2, fun h => ?_, fun h => hidq h.2, fun h => absurd h hidq, h6, ?_, ?_⟩
  · rcases h3 h with h | h
    · exact Or.inl h
    · simp [hpw] at h
  · intro o ho
    obtain ⟨hpc, hk⟩ := h7 o ho
    refine ⟨hpc, ?_⟩
    rcases hk with ⟨a1, a2, a3, a4, u, a5, a6, a7⟩ | ⟨a1, a2, a3, a4, old, new, a5, a6, a7, a8⟩ |
      ⟨a1, a2, a8⟩
    · exact Or.inl ⟨a1, a2, a3, by simp; omega, u, a5, a6, fun h => by simp at h; omega⟩
    · exact Or.inr (Or.inl ⟨a1, a2, a3, a4, old, new, a5, a6, a7, fun h => ⟨(a8 h).1, fun _ => by simp only at h ⊢; exact h⟩⟩)
    · obtain ⟨a3, a8⟩ := a8
      refine Or.inr (Or.inr ⟨a1, a2, a3, fun h => ?_⟩)
      exact absurd (a8 h).2 hnp
  · have hnw : needW ⟨W', v.Z, some id, v.Z.1, v.lm, v.sig⟩ x ↔ needW v x := by
      simp [needW, hpw, hid]
    have hnr : ¬ needR ⟨W', v.Z, some id, v.Z.1, v.lm, v.sig⟩ x := by simp [needR, hid]
    have hW : ∀ w : Cell V, Snap w v.W → Snap w W' ∧ W'.1 ≠ w.1 := fun w hw => by
      unfold Snap at *; omega
    have htw : ∀ r pc, IsTw pc → TwOK v x r pc →
        TwOK ⟨W', v.Z, some id, v.Z.1, v.lm, v.sig⟩ x r pc := by
      intro r pc hpc h
      obtain ⟨hg, hm⟩ := h
      refine ⟨?_, ?_⟩
      · rcases pc with c | ⟨c, b⟩ <;> cases c <;> simp only [TwGen] at hg ⊢
        · exact hg
        · exact ⟨hg.1, hg.2.1, fun h => absurd (hg.2.2 h).2 hnp⟩
      · rcases r with ⟨i, z⟩ | _ | _ | _ | _ <;> simp only at hm ⊢
        · exact hm
        · exact ⟨hm.1, stage_of_not _ (fun hn => hnp (stage_np hm.2 hpc (hnw.1 hn)))⟩
        · exact ⟨hm.1, stage_of_not _ (fun hn => hnp (stage_np hm.2 hpc (hnw.1 hn)))⟩
        · exact stage_of_not _ hnr
        · exact stage_of_not _ hnr
    clear h1 h2 h3 h4 h5 h6 h7
    rcases hpc : x.pc with c | ⟨c, b⟩ <;> rw [hpc] at h8 <;> cases c <;>
      simp only [PcOK] at h8 ⊢
    · exact h8
    · exact h8
    · obtain ⟨⟨old, new, hop, hm⟩, -⟩ := h8
      exact ⟨⟨old, new, hop, hm⟩, fun h _ => h⟩
    · exact h8
    · exact ⟨h8.1, h8.2.1, (hW _ h8.2.2.1).1, fun _ _ => hp'⟩
    · obtain ⟨⟨u, hu, -⟩, a, b, -⟩ := h8
      exact ⟨⟨u, hu, fun h => absurd h (hW _ b).2⟩, a, (hW _ b).1, fun _ _ => hp'⟩
    all_goals first
      | exact fun h => absurd h hnr
      | exact h8
      | exact ⟨h8.1, h8.2.1, fun _ => hp'⟩
      | exact htw _ _ trivial h8

theorem massWit_some {x : PV P K V} {s : V} {mv : Bool} {t w : ℕ} (h : x.wit = some w) :
    massWit x s mv t = some w := by simp [massWit, h]

theorem massWit_ne_none {x : PV P K V} {s : V} {mv : Bool} {t : ℕ} (h : x.wit ≠ none) :
    massWit x s mv t ≠ none := by
  obtain ⟨w, hw⟩ := Option.ne_none_iff_exists'.1 h; simp [massWit_some hw]

theorem massWit_wr_true {x : PV P K V} {s : V} {t : ℕ} (h : IsWr x.r.op) :
    massWit x s true t ≠ none := by
  obtain ⟨u, hu⟩ := h
  cases hw : x.wit <;> simp [massWit, hw, hu]

theorem massWit_wr_false {x : PV P K V} {s : V} {t : ℕ} (h : IsWr x.r.op) :
    massWit x s false t = x.wit := by
  obtain ⟨u, hu⟩ := h
  cases hw : x.wit <;> simp [massWit, hw, hu]

theorem massWit_cas {x : PV P K V} {s : V} {mv : Bool} {t : ℕ} {old new : V}
    (h : x.r.op = .cas old new) (hw : massWit x s mv t = none) : x.wit = none ∧ s = old := by
  cases hw' : x.wit with
  | some w => simp [massWit, hw'] at hw
  | none =>
    simp only [massWit, hw', h] at hw
    refine ⟨rfl, ?_⟩
    by_contra hs; simp [hs] at hw

theorem casMid_move {v v' : KV V} {x x' : PV P K V} {old new : V} {i : Bool} {z : Cell V}
    (hv : v.Inv) (h : Move v v') (hm : CasMid v x old new i z) (hls : x'.ls = x.ls)
    (hr : x'.r = x.r) (hw : x'.wit = none → x.wit = none ∧ v.W.2.1 = old) :
    CasMid v' x' old new i z := by
  obtain ⟨a1, a2, a3, ⟨s1, s2⟩, a5⟩ := hm
  have hZ := h.Z1
  refine ⟨by rw [hls, hr]; exact a1, a2, a3, ⟨by omega, fun e => by omega⟩, fun hw' => ?_⟩
  cases i
  · simp [h.lm]
  · obtain ⟨hw0, hWo⟩ := hw hw'
    simp only [↓reduceIte] at a5
    obtain ⟨hlm, hz⟩ := a5 hw0
    have hzZ := s2 hz.symm
    exact absurd (hWo.trans (a2.symm.trans (by rw [hzZ]))) (hv.a38 h.pend hlm)

theorem casMid_impr {v v' : KV V} {x x' : PV P K V} {old new nw : V} {i : Bool} {z : Cell V}
    (hv : v.Inv) (h : Impr v v' nw) (hm : CasMid v x old new i z) (hls : x'.ls = x.ls)
    (hr : x'.r = x.r) (hsig : x.wit = none → v.sig = old)
    (hw : x'.wit = none → x.wit = none ∧ nw = old) :
    CasMid v' x' old new i z := by
  obtain ⟨a1, a2, a3, ⟨s1, s2⟩, a5⟩ := hm
  have hZ := h.Z1
  refine ⟨by rw [hls, hr]; exact a1, a2, a3, ⟨by omega, fun e => by omega⟩, fun hw' => ?_⟩
  obtain ⟨hw0, hn⟩ := hw hw'
  exact absurd (hn.trans ((hsig hw0).symm.trans hv.sig_eq)) h.ne

/-- A move by another process preserves `Loc` (with the witness update). -/
theorem loc_move {p : P} {v v' : KV V} {x : PV P K V} (t : ℕ) (hl : Loc p v x) (hv : v.Inv)
    (h : Move v v') :
    Loc p v' { x with wit := massWit x v.W.2.1 true t, inL := x.inL ∨ v.pw = some x.r.id } := by
  have hmp := h.pend
  have hZ1 := h.Z1
  obtain ⟨W', Z', pw', zAt', lm', sig'⟩ := v'
  obtain ⟨-, rfl, -, hZ2, rfl, rfl, rfl, rfl⟩ := h
  simp only at hZ1 hZ2
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hl
  set x' : PV P K V := { x with wit := massWit x v.W.2.1 true t, inL := x.inL ∨ v.pw = some x.r.id }
  set v' : KV V := ⟨v.W, Z', none, v.zAt, true, v.W.2.1⟩
  have hM : Move v v' := ⟨hmp, rfl, hZ1, hZ2, rfl, rfl, rfl, rfl⟩
  have hnr : ¬ needR v' x' := by simp [needR, v']
  have hnw : IsWr x.r.op → ¬ needW v' x' := by
    intro hw hn
    rcases hn with hn | hn
    · simp [v'] at hn
    · exact massWit_wr_true hw hn.2
  have hcm : ∀ old new i z, x.r.op = .cas old new → CasMid v x old new i z →
      CasMid v' x' old new i z := fun old new i z hop hm =>
    casMid_move hv hM hm rfl rfl (fun hw => massWit_cas (x := x) hop hw)
  have hnp' : ¬ v'.pend := by simp [KV.pend, v', hZ2]
  have htw : ∀ r pc, IsTw pc → TwOK v x r pc → TwOK v' x' r pc := by
    intro r pc hpc h
    obtain ⟨hg, hm⟩ := h
    refine ⟨?_, ?_⟩
    · rcases pc with c | ⟨c, b⟩ <;> cases c <;> simp only [TwGen] at hg ⊢
      · have := hg.1
        exact ⟨by simp [v']; omega, fun e => by simp [v'] at e; omega⟩
      · have := hg.1.1
        exact ⟨⟨by simp [v']; omega, fun e => by simp [v'] at e; omega⟩, hg.2.1,
          fun e => by simp [v'] at e; omega⟩
    · rcases r with ⟨i, z⟩ | _ | _ | _ | _ <;> simp only at hm ⊢
      · obtain ⟨old, new, hop, hm, hc⟩ := hm
        refine ⟨old, new, hop, hcm _ _ _ _ hop hm, ?_⟩
        rcases pc with c | ⟨c, b⟩ <;> cases c <;> simp only [CasTw] at hc ⊢
        all_goals first | exact hc | (simp only [v']; omega)
      · exact ⟨hm.1, stage_of_not _ (hnw hm.1)⟩
      · exact ⟨hm.1, stage_of_not _ (hnw hm.1)⟩
      · exact stage_of_not _ hnr
      · exact stage_of_not _ hnr
  refine ⟨h1, fun h => h.elim h2 (fun h => (h5 h).1), fun h => Or.inl (h3 h), by simp [v'],
    by simp [v'], ?_, ?_, ?_⟩
  · intro old new hop hw
    exact (massWit_cas (x := x) hop hw).2
  · intro o ho
    obtain ⟨hpc, hk⟩ := h7 o ho
    refine ⟨hpc, ?_⟩
    rcases hk with ⟨a1, a2, a3, a4, u, a5, a6, a7⟩ | ⟨a1, a2, a3, a4, old, new, a5, a6, a7, a8⟩ |
      ⟨a1, a2, a3, a8⟩
    · exact Or.inl ⟨a1, a2, a3, a4, u, a5, a6, fun h => absurd hmp (a7 h).1⟩
    · exact Or.inr (Or.inl ⟨a1, a2, a3, by simp [v']; omega, old, new, a5, a6, a7,
        fun h => by simp [v'] at h; omega⟩)
    · exact Or.inr (Or.inr ⟨a1, a2, by simp [v']; omega, fun h => by simp [v'] at h; omega⟩)
  · clear h1 h2 h3 h4 h5 h6 h7
    show PcOK v' x' x.pc
    rcases hpc : x.pc with c | ⟨c, b⟩ <;> rw [hpc] at h8 <;> cases c <;>
      simp only [PcOK] at h8 ⊢
    · exact h8
    · exact ⟨h8.1, h8.2.1, fun _ _ => rfl⟩
    · obtain ⟨⟨old, new, hop, hm⟩, -⟩ := h8
      have := hm.2.2.2.1.1
      exact ⟨⟨old, new, hop, hcm _ _ _ _ hop hm⟩, fun e => by simp [v'] at e; omega⟩
    · exact h8
    · exact ⟨h8.1, h8.2.1, h8.2.2.1, fun hw => absurd hw (massWit_wr_true h8.1)⟩
    · obtain ⟨⟨u, hu, hu'⟩, a, b, -⟩ := h8
      exact ⟨⟨u, hu, fun e => absurd hmp (hu' e).1⟩, a, b,
        fun hw => absurd hw (massWit_wr_true ⟨u, hu⟩)⟩
    all_goals first
      | exact htw _ _ (by trivial) h8
      | exact fun h => absurd h hnr
      | exact ⟨h8.1, h8.2.1, fun hn => absurd hn (hnw h8.1)⟩
      | skip
    obtain ⟨a1, a2, a3⟩ := h8
    refine ⟨a1, fun hb => Or.inl (a2 hb), fun hb => ?_⟩
    obtain ⟨b1, b2, b3, b4⟩ := a3 hb
    exact ⟨b1, by simp [v']; omega, fun hi => massWit_ne_none (b3 hi), fun _ _ => rfl⟩

theorem Impr.pend_iff {v v' : KV V} {nw : V} (h : Impr v v' nw) : v'.pend ↔ v.pend := by
  unfold KV.pend; rw [h.W, h.Z2]

theorem stage_impr {v v' : KV V} {nw : V} {need s2 : Prop} {pc : APc V} (hs : Stage v need s2 pc)
    (h : Impr v v' nw) : Stage v' need s2 pc := by
  have hp := h.pend_iff
  have hZ := h.Z1
  have hzA := h.zAt
  rcases pc with c | ⟨c, b⟩ <;> cases c <;> simp only [Stage] at hs ⊢
  · exact ⟨fun hn => hp.2 (hs.1 hn), fun h2 hn => by have := hs.2 h2 hn; omega⟩
  · refine ⟨fun hn => hp.2 (hs.1 hn), fun hn => ⟨fun h2 => ?_, by rw [hzA]; exact (hs.2 hn).2⟩⟩
    obtain ⟨a, rfl⟩ := (hs.2 hn).1 h2
    have := h.i4 (hs.1 hn); omega
  · refine ⟨fun hn => hp.2 (hs.1 hn), fun hn => ⟨fun h2 => ?_, by rw [hzA]; exact (hs.2 hn).2⟩⟩
    obtain ⟨a, rfl⟩ := (hs.2 hn).1 h2
    have := h.i4 (hs.1 hn); omega
  · exact ⟨hs.1, fun hn => ⟨hp.2 (hs.2 hn).1, by have := (hs.2 hn).2; omega⟩⟩

/-- An imprint by another process preserves `Loc` (with the witness update). -/
theorem loc_impr {p : P} {v v' : KV V} {x : PV P K V} {nw : V} (t : ℕ) (hl : Loc p v x)
    (hv : v.Inv) (h : Impr v v' nw) : Loc p v' { x with wit := massWit x nw false t } := by
  have hp := h.pend_iff
  have hZ1 := h.Z1
  have hi4 := h.i4
  have hne := h.ne
  obtain ⟨W', Z', pw', zAt', lm', sig'⟩ := v'
  obtain ⟨-, rfl, -, hZ2, -, rfl, rfl, rfl, hs⟩ := h
  simp only at hZ1 hZ2 hp hs
  subst sig'
  set x' : PV P K V := { x with wit := massWit x nw false t }
  set v' : KV V := ⟨v.W, Z', v.pw, v.zAt, false, nw⟩
  have hI : Impr v v' nw := ⟨hi4, rfl, hZ1, hZ2, hne, rfl, rfl, rfl, rfl⟩
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hl
  have hcw : ∀ old new, x.r.op = .cas old new → x'.wit ≠ none := by
    intro old new hop hw
    obtain ⟨hw0, hn⟩ := massWit_cas (x := x) hop hw
    exact hne (hn.trans ((h6 old new hop hw0).symm.trans hv.sig_eq))
  have hcm : ∀ old new i z, x.r.op = .cas old new → CasMid v x old new i z →
      CasMid v' x' old new i z := fun old new i z hop hm =>
    casMid_impr hv hI hm rfl rfl (h6 old new hop) (fun hw => massWit_cas (x := x) hop hw)
  have hnw : IsWr x.r.op → (needW v' x' ↔ needW v x) := by
    intro hw
    simp only [needW, x', v', massWit_wr_false hw]
  have htw : ∀ r pc, IsTw pc → TwOK v x r pc → TwOK v' x' r pc := by
    intro r pc hpc h
    obtain ⟨hg, hm⟩ := h
    refine ⟨?_, ?_⟩
    · rcases pc with c | ⟨c, b⟩ <;> cases c <;> simp only [TwGen] at hg ⊢
      · have := hg.1
        exact ⟨by simp [v']; omega, fun e => by simp [v'] at e; omega⟩
      · have := hg.1.1
        exact ⟨⟨by simp [v']; omega, fun e => by simp [v'] at e; omega⟩, hg.2.1,
          fun e => by simp [v'] at e; omega⟩
    · rcases r with ⟨i, z⟩ | _ | _ | _ | _ <;> simp only at hm ⊢
      · obtain ⟨old, new, hop, hm, hc⟩ := hm
        refine ⟨old, new, hop, hcm _ _ _ _ hop hm, ?_⟩
        rcases pc with c | ⟨c, b⟩ <;> cases c <;> simp only [CasTw] at hc ⊢
        all_goals first | exact hc | (simp only [v']; omega)
      · exact ⟨hm.1, by rw [propext (hnw hm.1)]; exact stage_impr hm.2 hI⟩
      · exact ⟨hm.1, by rw [propext (hnw hm.1)]; exact stage_impr hm.2 hI⟩
      · exact stage_impr hm hI
      · exact stage_impr hm hI
  refine ⟨h1, h2, h3, h4, h5, ?_, ?_, ?_⟩
  · intro old new hop hw
    exact absurd hw (hcw old new hop)
  · intro o ho
    obtain ⟨hpc, hk⟩ := h7 o ho
    refine ⟨hpc, ?_⟩
    rcases hk with ⟨a1, a2, a3, a4, u, a5, a6, a7⟩ | ⟨a1, a2, a3, a4, old, new, a5, a6, a7, a8⟩ |
      ⟨a1, a2, a3, a8⟩
    · refine Or.inl ⟨a1, a2, a3, a4, u, a5, a6, fun e => ?_⟩
      obtain ⟨b1, -, b3⟩ := a7 e
      exact ⟨fun hp' => b1 (hp.1 hp'), fun hl => by simp [v'] at hl, b3⟩
    · exact Or.inr (Or.inl ⟨a1, a2, a3, by simp [v']; omega, old, new, a5, a6, a7,
        fun h => by simp [v'] at h; omega⟩)
    · exact Or.inr (Or.inr ⟨a1, a2, by simp [v']; omega, fun h => by simp [v'] at h; omega⟩)
  · clear h1 h2 h3 h4 h5 h7
    show PcOK v' x' x.pc
    rcases hpc : x.pc with c | ⟨c, b⟩ <;> rw [hpc] at h8 <;> cases c <;>
      simp only [PcOK] at h8 ⊢
    · exact h8
    · obtain ⟨⟨old, new, hop⟩, a, -⟩ := h8
      exact ⟨⟨old, new, hop⟩, a, fun _ hw => absurd hw (hcw old new hop)⟩
    · obtain ⟨⟨old, new, hop, hm⟩, -⟩ := h8
      have := hm.2.2.2.1.1
      exact ⟨⟨old, new, hop, hcm _ _ _ _ hop hm⟩, fun e => by simp [v'] at e; omega⟩
    · exact h8
    · obtain ⟨a1, a2, a3, a4⟩ := h8
      exact ⟨a1, a2, a3, fun hw e => hp.2 (a4 (by rwa [show x'.wit = x.wit from massWit_wr_false a1] at hw) e)⟩
    · obtain ⟨⟨u, hu, hu'⟩, a, b, c⟩ := h8
      exact ⟨⟨u, hu, fun e => ⟨fun hp' => (hu' e).1 (hp.1 hp'), fun hl => by simp [v'] at hl⟩⟩, a, b,
        fun hw e => hp.2 (c (by rwa [show x'.wit = x.wit from massWit_wr_false ⟨u, hu⟩] at hw) e)⟩
    all_goals first
      | exact htw _ _ (by trivial) h8
      | exact fun h => hp.2 (h8 h)
      | exact ⟨h8.1, h8.2.1, fun hn => hp.2 (h8.2.2 ((hnw h8.1).1 hn))⟩
      | skip
    obtain ⟨⟨old, new, hop⟩, a2, a3⟩ := h8
    refine ⟨⟨old, new, hop⟩, a2, fun hb => ?_⟩
    obtain ⟨b1, b2, b3, b4⟩ := a3 hb
    exact ⟨b1, by simp [v']; omega, fun hi => massWit_ne_none (b3 hi),
      fun _ hw => absurd hw (hcw old new hop)⟩

end Podc.DuraCAS
