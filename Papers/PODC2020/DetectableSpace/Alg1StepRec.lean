import Papers.PODC2020.DetectableSpace.Alg1Step

/-!
# Algorithm 1: preservation of the invariant by local steps of `Write.Recover` and `Read`
-/

set_option linter.unusedSectionVars false

namespace Papers.PODC2020.DetectableSpace

open Cslib.SharedMemory

namespace Alg1

attribute [local simp] LC LCW LCR Ph Dec Kd vw valOf progOf at20b bitOf Loc.stage Loc.isDec
  Loc.prog Loc.kd Loc.is20b Loc.is12 Loc.info

variable {V : Type} [DecidableEq V] {n : ℕ} [NeZero n] {v₀ : V}
variable {C : Cfg1 V v₀ n} {g : Ghost V n} {h : Hist V n} {L : LinL V}

/-- Line 14. -/
theorem step_r14 (hI : Inv v₀ C g h L) {r : Fin n} {a : ℕ} {o : RWOp V} {b : Bool} {v : V}
    (hr : C.ps r = .run a o b (.r14 v)) : StepOK C h (.step r) := by
  rw [StepOK, step1_pv hr rfl]
  refine ⟨⟨g.wc, g.rv, Function.update g.s r (g.s r), g.wr⟩, L, ?_⟩
  rw [List.append_nil]
  dsimp only
  have hp := hI.pi r
  rw [hr] at hp
  obtain ⟨hlc, -, hm1, hm2, -, hf1, hf1w, hf2a, hf2b, hd, hcl1, hc2⟩ := hp
  cases o with
  | read => simp at hlc
  | write v' =>
  obtain ⟨⟨rfl, rfl⟩, hcp2, hwrcp, hres, hrd, htt1, htt2⟩ := hlc
  cases hrdc : (C.pv r).rd with
  | none =>
    have hcp : (C.pv r).cp = 0 := by
      by_contra hne
      have := hrd (by omega)
      rw [hrdc] at this; simp at this
    have hwr : g.wr r = false := by
      cases hw : g.wr r
      · rfl
      · have := hwrcp hw; omega
    have hres' : (C.pv r).res = none := by
      cases hx : (C.pv r).res with
      | none => rfl
      | some x => have := (hres x hx).2; omega
    apply hI.local r _ _ (g.s r)
    · rintro a' o' b' l' h1
      simp only [PSt.run.injEq] at h1
      obtain ⟨rfl, rfl, rfl, -⟩ := h1
      exact ⟨_, _, hr⟩
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [hcp, hwr, hres']
    · rintro a' o' b' l' x h1 h2
      simp only [PSt.run.injEq] at h1
      obtain ⟨rfl, rfl, rfl, rfl⟩ := h1
      left; exact ⟨_, _, _, hr, by simpa using h2⟩
    · rintro a' v'' b' l' h1 _ h3 _
      simp only [PSt.run.injEq] at h1
      obtain ⟨rfl, -, -, -⟩ := h1
      exact ⟨_, _, _, hr, h3⟩
    · exact hI.f3 r
    · intro t p hk
      obtain ⟨ka, -, -⟩ := hk
      exact ⟨ka, by simp [hcp], by simp [hcp]⟩
    · intro hk; simp [hwr] at hk
  | some x =>
    obtain ⟨mt, tr⟩ := x
    have hvw : ∀ m : Pv V n, m.rd = some (mt, tr) →
        Loc.info (dflt v₀) m (.r14 v : Loc V n) = (tr, mt) := by
      intro m hm; simp [Loc.info, hm]
    apply hI.local r _ _ (g.s r)
    · rintro a' o' b' l' h1
      simp only [PSt.run.injEq] at h1
      obtain ⟨rfl, rfl, rfl, -⟩ := h1
      exact ⟨_, _, hr⟩
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [LC, LCW, true_and]
        refine ⟨hcp2, hwrcp, hres, fun _ => by simpa using hrdc, fun h1 h2 => ?_, fun h1 => ?_⟩
        · simpa [hrdc] using htt1 (by simpa using h1) h2
        · simpa [hrdc] using htt2 (by simpa using h1)
      · simp
      · intro a' v'' b' l' h1 h2 h3 h4
        simp only [PSt.run.injEq] at h1
        obtain ⟨rfl, -⟩ := h1
        exact hm1 _ _ _ _ rfl (by simpa using h2) h3 h4
      · intro a' v'' b' l' h1 h2
        simp only [PSt.run.injEq] at h1
        obtain ⟨rfl, -⟩ := h1
        exact hm2 _ _ _ _ rfl (by simpa using h2)
      · simp
      · intro h1 k hk1 hk2 hk3
        simpa [hrdc] using hf1 (by simpa using h1) k hk1 hk2 hk3
      · exact hf1w
      · intro h1
        simpa [hrdc] using hf2a (by simpa using h1)
      · intro h1
        simpa [hrdc] using hf2b (by simpa using h1)
      · intro h1; exact hd (by simpa using h1)
      · intro h1 hb
        exact hcl1 (by simpa using h1) (by simpa [hrdc] using hb)
      · intro h1 h2
        simpa [hrdc] using (hc2 h1 h2).1
    · rintro a' o' b' l' x h1 h2
      simp only [PSt.run.injEq] at h1
      obtain ⟨rfl, rfl, rfl, rfl⟩ := h1
      left; exact ⟨_, _, _, hr, by simpa using h2⟩
    · rintro a' v'' b' l' h1 _ h3 _
      simp only [PSt.run.injEq] at h1
      obtain ⟨rfl, -, -, -⟩ := h1
      exact ⟨_, _, _, hr, h3⟩
    · exact hI.f3 r
    · intro t p hk
      rw [hr] at hk
      obtain ⟨ka, kb, kc⟩ := hk
      exact ⟨ka, fun h1 h2 => kb (by simpa using h1) (by simpa [hrdc] using h2),
        fun h1 h2 => by simpa [hrdc] using kc (by simpa using h1) (by simpa [hrdc] using h2)⟩
    · apply hI.hkk_of
      · intro t p hk
        rw [hr] at hk
        obtain ⟨ka, kb, kc⟩ := hk
        exact ⟨ka, fun h1 h2 => kb (by simpa using h1) (by simpa [hrdc] using h2),
          fun h1 h2 => by simpa [hrdc] using kc (by simpa using h1) (by simpa [hrdc] using h2)⟩
      · intro h1
        rw [hr]
        exact ⟨by simpa using h1, by simp [hrdc]⟩

/-- Line 15. -/
theorem step_r15 (hI : Inv v₀ C g h L) {r : Fin n} {a : ℕ} {o : RWOp V} {b : Bool} {v : V}
    {tr : Trip V n} {mt : Bool} (hr : C.ps r = .run a o b (.r15 v tr mt)) :
    StepOK C h (.step r) := by
  rw [StepOK, step1_pv hr rfl]
  refine ⟨⟨g.wc, g.rv, Function.update g.s r (g.s r), g.wr⟩, L, ?_⟩
  rw [List.append_nil]
  dsimp only
  have hp := hI.pi r
  rw [hr] at hp
  obtain ⟨hlc, -, hm1, hm2, -, hf1, hf1w, hf2a, hf2b, hd, hcl1, hc2⟩ := hp
  cases o with
  | read => simp at hlc
  | write v' =>
  obtain ⟨⟨rfl, rfl⟩, hcp2, hwrcp, hres, hrd, htt1, htt2⟩ := hlc
  split_ifs with hsome
  · obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 hsome
    obtain ⟨rfl, hcp⟩ := hres x hx
    have hrd' : (C.pv r).rd = some (mt, tr) := by simpa using hrd (by omega)
    have hT : (C.pv r).T = !mt := by simpa [hx] using htt2
    apply hI.local r _ _ (g.s r)
    · rintro a' o' b' l' h1
      simp only [PSt.run.injEq] at h1
      obtain ⟨rfl, rfl, rfl, -⟩ := h1
      exact ⟨_, _, hr⟩
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp [hx, hcp, hrd', hT]
      · simp
      · intro a' v'' b' l' _ _ _ h4
        simp [hcp] at h4
      · intro a' v'' b' l' h1 _
        simp only [PSt.run.injEq] at h1
        obtain ⟨rfl, -⟩ := h1
        exact hm2 _ _ _ _ rfl (.inr (by simp [hcp]))
      · simp
      · intro h1 k hk1 hk2 hk3
        simpa [hrd'] using hf1 (by simp [hcp]) k hk1 hk2 hk3
      · exact hf1w
      · intro h1
        simpa [hrd'] using hf2a (by simp [hcp])
      · intro h1
        simpa [hrd'] using hf2b (by simp [hcp])
      · intro h1; exact hd (by simp [hcp])
      · intro h1 hb
        exact hcl1 (by simp [hcp]) (by simpa [hrd'] using hb)
      · intro _ h2; simp [hcp] at h2
    · rintro a' o' b' l' y h1 h2
      simp only [PSt.run.injEq] at h1
      obtain ⟨rfl, rfl, rfl, rfl⟩ := h1
      left; exact ⟨_, _, _, hr, by simpa using h2⟩
    · rintro a' v'' b' l' _ _ h3 _
      simp [hcp] at h3
    · exact hI.f3 r
    · intro t p hk
      rw [hr] at hk
      obtain ⟨ka, kb, kc⟩ := hk
      refine ⟨ka, fun h1 h2 => kb (by simp [hcp]) (by simpa [hrd'] using h2), fun _ h2 => ?_⟩
      exfalso
      have := (kc (by simp [hcp]) (by simpa [hrd'] using h2)).1
      rw [hT] at this
      cases mt <;> simp at this
    · intro hk; simp [hcp] at hk
  · have hres' : (C.pv r).res = none := by simpa using hsome
    apply hI.local r _ _ (g.s r)
    · rintro a' o' b' l' h1
      simp only [PSt.run.injEq] at h1
      obtain ⟨rfl, rfl, rfl, -⟩ := h1
      exact ⟨_, _, hr⟩
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [LC, LCW]
        exact ⟨⟨trivial, trivial, hres'⟩, hcp2, hwrcp, hres, hrd, fun h1 h2 => htt1 (by simpa using h1) h2,
          fun h1 => htt2 (by simpa using h1)⟩
      · simp
      · intro a' v'' b' l' h1 h2 h3 h4
        simp only [PSt.run.injEq] at h1
        obtain ⟨rfl, -⟩ := h1
        exact hm1 _ _ _ _ rfl (by simpa using h2) h3 h4
      · intro a' v'' b' l' h1 h2
        simp only [PSt.run.injEq] at h1
        obtain ⟨rfl, -⟩ := h1
        exact hm2 _ _ _ _ rfl (by simpa using h2)
      · simp
      · intro h1 k hk1 hk2 hk3
        simpa using hf1 (by simpa using h1) k hk1 hk2 hk3
      · exact hf1w
      · intro h1
        simpa using hf2a (by simpa using h1)
      · intro h1
        simpa using hf2b (by simpa using h1)
      · intro h1; exact hd (by simpa using h1)
      · intro h1 hb
        exact hcl1 (by simpa using h1) (by simpa using hb)
      · intro h1 h2
        simpa using (hc2 h1 h2).1
    · rintro a' o' b' l' y h1 h2
      simp only [PSt.run.injEq] at h1
      obtain ⟨rfl, rfl, rfl, rfl⟩ := h1
      left; exact ⟨_, _, _, hr, by simpa using h2⟩
    · rintro a' v'' b' l' h1 _ h3 _
      simp only [PSt.run.injEq] at h1
      obtain ⟨rfl, -, -, -⟩ := h1
      exact ⟨_, _, _, hr, h3⟩
    · exact hI.f3 r
    · intro t p hk
      rw [hr] at hk
      obtain ⟨ka, kb, kc⟩ := hk
      exact ⟨ka, fun h1 h2 => kb (by simpa using h1) (by simpa using h2),
        fun h1 h2 => by simpa using kc (by simpa using h1) (by simpa using h2)⟩
    · apply hI.hkk_of
      · intro t p hk
        rw [hr] at hk
        obtain ⟨ka, kb, kc⟩ := hk
        exact ⟨ka, fun h1 h2 => kb (by simpa using h1) (by simpa using h2),
          fun h1 h2 => by simpa using kc (by simpa using h1) (by simpa using h2)⟩
      · intro h1
        rw [hr]
        exact ⟨by simpa using h1, by simp⟩

/-- Line 17. -/
theorem step_r17 (hI : Inv v₀ C g h L) {r : Fin n} {a : ℕ} {o : RWOp V} {b : Bool} {v : V}
    {tr : Trip V n} {mt : Bool} (hr : C.ps r = .run a o b (.r17 v tr mt)) :
    StepOK C h (.step r) := by
  rw [StepOK, step1_pv hr rfl]
  refine ⟨⟨g.wc, g.rv, Function.update g.s r (g.s r), g.wr⟩, L, ?_⟩
  rw [List.append_nil]
  dsimp only
  have hp := hI.pi r
  rw [hr] at hp
  obtain ⟨hlc, -, hm1, hm2, -, hf1, hf1w, hf2a, hf2b, hd, hcl1, hc2⟩ := hp
  cases o with
  | read => simp at hlc
  | write v' =>
  obtain ⟨⟨rfl, rfl, hres'⟩, hcp2, hwrcp, hres, hrd, htt1, htt2⟩ := hlc
  split_ifs with hcp
  · have hwr : g.wr r = false := by
      cases hw : g.wr r
      · rfl
      · have := hwrcp hw; omega
    apply hI.local r _ _ (g.s r)
    · rintro a' o' b' l' h1
      simp only [PSt.run.injEq] at h1
      obtain ⟨rfl, rfl, rfl, -⟩ := h1
      exact ⟨_, _, hr⟩
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [hcp, hwr, hres']
    · rintro a' o' b' l' y h1 h2
      simp only [PSt.run.injEq] at h1
      obtain ⟨rfl, rfl, rfl, rfl⟩ := h1
      left; exact ⟨_, _, _, hr, by simpa using h2⟩
    · rintro a' v'' b' l' h1 _ h3 _
      simp only [PSt.run.injEq] at h1
      obtain ⟨rfl, -, -, -⟩ := h1
      exact ⟨_, _, _, hr, h3⟩
    · exact hI.f3 r
    · intro t p hk
      obtain ⟨ka, -, -⟩ := hk
      exact ⟨ka, by simp [hcp], by simp [hcp]⟩
    · intro hk; simp [hwr] at hk
  · apply hI.local r _ _ (g.s r)
    · rintro a' o' b' l' h1
      simp only [PSt.run.injEq] at h1
      obtain ⟨rfl, rfl, rfl, -⟩ := h1
      exact ⟨_, _, hr⟩
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [LC, LCW]
        exact ⟨⟨trivial, trivial, hres', hcp⟩, hcp2, hwrcp, hres, hrd, fun h1 h2 => htt1 (by simpa using h1) h2,
          fun h1 => htt2 (by simpa using h1)⟩
      · simp
      · intro a' v'' b' l' h1 h2 h3 h4
        simp only [PSt.run.injEq] at h1
        obtain ⟨rfl, -⟩ := h1
        exact hm1 _ _ _ _ rfl (by simpa using h2) h3 h4
      · intro a' v'' b' l' h1 h2
        simp only [PSt.run.injEq] at h1
        obtain ⟨rfl, -⟩ := h1
        exact hm2 _ _ _ _ rfl (by simpa using h2)
      · simp
      · intro h1 k hk1 hk2 hk3
        simpa using hf1 (by simpa using h1) k hk1 hk2 hk3
      · exact hf1w
      · intro h1
        simpa using hf2a (by simpa using h1)
      · intro h1
        simpa using hf2b (by simpa using h1)
      · intro h1; exact hd (by simpa using h1)
      · intro h1 hb
        exact hcl1 (by simpa using h1) (by simpa using hb)
      · intro h1 h2
        simpa using (hc2 h1 h2).1
    · rintro a' o' b' l' y h1 h2
      simp only [PSt.run.injEq] at h1
      obtain ⟨rfl, rfl, rfl, rfl⟩ := h1
      left; exact ⟨_, _, _, hr, by simpa using h2⟩
    · rintro a' v'' b' l' h1 _ h3 _
      simp only [PSt.run.injEq] at h1
      obtain ⟨rfl, -, -, -⟩ := h1
      exact ⟨_, _, _, hr, h3⟩
    · exact hI.f3 r
    · intro t p hk
      rw [hr] at hk
      obtain ⟨ka, kb, kc⟩ := hk
      exact ⟨ka, fun h1 h2 => kb (by simpa using h1) (by simpa using h2),
        fun h1 h2 => by simpa using kc (by simpa using h1) (by simpa using h2)⟩
    · apply hI.hkk_of
      · intro t p hk
        rw [hr] at hk
        obtain ⟨ka, kb, kc⟩ := hk
        exact ⟨ka, fun h1 h2 => kb (by simpa using h1) (by simpa using h2),
          fun h1 h2 => by simpa using kc (by simpa using h1) (by simpa using h2)⟩
      · intro h1
        rw [hr]
        exact ⟨by simpa using h1, by simp⟩

/-- Line 19. -/
theorem step_r19 (hI : Inv v₀ C g h L) {r : Fin n} {a : ℕ} {o : RWOp V} {b : Bool} {v : V}
    {tr : Trip V n} {mt : Bool} (hr : C.ps r = .run a o b (.r19 v tr mt)) :
    StepOK C h (.step r) := by
  rw [StepOK, step1_pv hr rfl]
  refine ⟨⟨g.wc, g.rv, Function.update g.s r (g.s r), g.wr⟩, L, ?_⟩
  rw [List.append_nil]
  dsimp only
  have hp := hI.pi r
  rw [hr] at hp
  obtain ⟨hlc, -, hm1, hm2, -, hf1, hf1w, hf2a, hf2b, hd, hcl1, hc2⟩ := hp
  cases o with
  | read => simp at hlc
  | write v' =>
  obtain ⟨⟨rfl, rfl, hres', hcp0⟩, hcp2, hwrcp, hres, hrd, htt1, htt2⟩ := hlc
  have hrd' : (C.pv r).rd = some (mt, tr) := by simpa using hrd (by omega)
  split_ifs with hcp
  · apply hI.local r _ _ (g.s r)
    · rintro a' o' b' l' h1
      simp only [PSt.run.injEq] at h1
      obtain ⟨rfl, rfl, rfl, -⟩ := h1
      exact ⟨_, _, hr⟩
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [LC, LCW]
        exact ⟨⟨trivial, trivial, hres', hcp⟩, hcp2, hwrcp, hres, hrd, fun h1 h2 => htt1 (by simpa using h1) h2,
          fun h1 => htt2 (by simpa using h1)⟩
      · simp
      · intro a' v'' b' l' h1 h2 h3 h4
        simp only [PSt.run.injEq] at h1
        obtain ⟨rfl, -⟩ := h1
        exact hm1 _ _ _ _ rfl (by simpa using h2) h3 h4
      · intro a' v'' b' l' h1 h2
        simp only [PSt.run.injEq] at h1
        obtain ⟨rfl, -⟩ := h1
        exact hm2 _ _ _ _ rfl (by simpa using h2)
      · simp
      · intro h1 k hk1 hk2 hk3
        simpa using hf1 (by simpa using h1) k hk1 hk2 hk3
      · exact hf1w
      · intro h1
        simpa using hf2a (by simpa using h1)
      · intro h1
        simpa using hf2b (by simpa using h1)
      · intro h1; exact hd (by simpa using h1)
      · intro h1 hb
        exact hcl1 (by simpa using h1) (by simpa using hb)
      · intro h1 h2
        simpa using (hc2 h1 h2).1
    · rintro a' o' b' l' y h1 h2
      simp only [PSt.run.injEq] at h1
      obtain ⟨rfl, rfl, rfl, rfl⟩ := h1
      left; exact ⟨_, _, _, hr, by simpa using h2⟩
    · rintro a' v'' b' l' h1 _ h3 _
      simp only [PSt.run.injEq] at h1
      obtain ⟨rfl, -, -, -⟩ := h1
      exact ⟨_, _, _, hr, h3⟩
    · exact hI.f3 r
    · intro t p hk
      rw [hr] at hk
      obtain ⟨ka, kb, kc⟩ := hk
      exact ⟨ka, fun h1 h2 => kb (by simpa using h1) (by simpa using h2),
        fun h1 h2 => by simpa using kc (by simpa using h1) (by simpa using h2)⟩
    · apply hI.hkk_of
      · intro t p hk
        rw [hr] at hk
        obtain ⟨ka, kb, kc⟩ := hk
        exact ⟨ka, fun h1 h2 => kb (by simpa using h1) (by simpa using h2),
          fun h1 h2 => by simpa using kc (by simpa using h1) (by simpa using h2)⟩
      · intro h1
        rw [hr]
        exact ⟨by simpa using h1, by simp⟩
  · have hcp2' : (C.pv r).cp = 2 := by omega
    apply hI.local r _ _ (g.s r)
    · rintro a' o' b' l' h1
      simp only [PSt.run.injEq] at h1
      obtain ⟨rfl, rfl, rfl, -⟩ := h1
      exact ⟨_, _, hr⟩
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp [hres', hrd', hcp2']
      · simp
      · intro a' v'' b' l' _ _ _ h4
        simp [hcp2'] at h4
      · intro a' v'' b' l' h1 _
        simp only [PSt.run.injEq] at h1
        obtain ⟨rfl, -⟩ := h1
        exact hm2 _ _ _ _ rfl (.inr (by simp [hcp2']))
      · simp
      · intro h1 k hk1 hk2 hk3
        simpa using hf1 (by simp [hcp2']) k hk1 hk2 hk3
      · exact hf1w
      · intro h1
        simpa using hf2a (by simp [hcp2'])
      · intro h1
        simpa using hf2b (by simp [hcp2'])
      · intro h1; exact hd (by simp [hcp2'])
      · intro h1 hb
        exact hcl1 (by simp [hcp2']) (by simpa using hb)
      · intro _ h2; simp [hcp2'] at h2
    · rintro a' o' b' l' y h1 h2
      simp only [PSt.run.injEq] at h1
      obtain ⟨rfl, rfl, rfl, rfl⟩ := h1
      left; exact ⟨_, _, _, hr, by simpa using h2⟩
    · rintro a' v'' b' l' _ _ h3 _
      simp [hcp2'] at h3
    · exact hI.f3 r
    · intro t p hk
      rw [hr] at hk
      obtain ⟨ka, kb, kc⟩ := hk
      exact ⟨ka, fun h1 h2 => kb (by simp [hcp2']) (by simpa using h2),
        fun h1 h2 => by simpa using kc (by simp [hcp2']) (by simpa using h2)⟩
    · intro hk; simp [hcp2'] at hk

lemma pv_self' (C : Cfg1 V v₀ n) (r : Fin n) : C.pv = Function.update C.pv r (C.pv r) :=
  (Function.update_eq_self r C.pv).symm

/-- Line 20, first conjunct. -/
theorem step_r20 (hI : Inv v₀ C g h L) {r : Fin n} {a : ℕ} {o : RWOp V} {b : Bool} {v : V}
    {tr : Trip V n} {mt : Bool} (hr : C.ps r = .run a o b (.r20 v tr mt)) :
    StepOK C h (.step r) := by
  rw [StepOK, step1_sh hr rfl]
  refine ⟨⟨g.wc, g.rv, Function.update g.s r (g.s r), g.wr⟩, L, ?_⟩
  rw [List.append_nil, pv_self' C r]
  dsimp only
  have hp := hI.pi r
  rw [hr] at hp
  obtain ⟨hlc, -, hm1, hm2, -, hf1, hf1w, hf2a, hf2b, hd, hcl1, hc2⟩ := hp
  cases o with
  | read => simp at hlc
  | write v' =>
  obtain ⟨⟨rfl, rfl, hres', hcp⟩, hcp2, hwrcp, hres, hrd, htt1, htt2⟩ := hlc
  have hrd' : (C.pv r).rd = some (mt, tr) := by simpa using hrd (by omega)
  have hT : (C.pv r).T = mt := by simpa using htt1 (by simp [hcp]) (by omega)
  split_ifs with hR
  · apply hI.local r _ _ (g.s r)
    · rintro a' o' b' l' h1
      simp only [PSt.run.injEq] at h1
      obtain ⟨rfl, rfl, rfl, -⟩ := h1
      exact ⟨_, _, hr⟩
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [LC, LCW]
        exact ⟨⟨trivial, trivial, hres', hcp⟩, hcp2, hwrcp, hres, hrd,
          fun h1 h2 => htt1 (by simpa using h1) h2, fun h1 => htt2 (by simpa using h1)⟩
      · simp
      · intro a' v'' b' l' h1 h2 h3 h4
        simp only [PSt.run.injEq] at h1
        obtain ⟨rfl, -⟩ := h1
        exact hm1 _ _ _ _ rfl (by simpa using h2) h3 h4
      · intro a' v'' b' l' h1 h2
        simp only [PSt.run.injEq] at h1
        obtain ⟨rfl, -⟩ := h1
        exact hm2 _ _ _ _ rfl (by simpa using h2)
      · simp
      · intro h1 k hk1 hk2 hk3
        simpa using hf1 (by simpa using h1) k hk1 hk2 hk3
      · exact hf1w
      · intro h1
        simpa using hf2a (by simpa using h1)
      · intro h1
        simpa using hf2b (by simpa using h1)
      · intro h1; exact hd (by simpa using h1)
      · intro h1 hb
        exact hcl1 (by simpa using h1) (by simpa using hb)
      · intro h1 h2
        have := (hc2 h1 h2).1
        simp only [vw, Loc.info] at this
        rcases this with h | h
        · exact absurd hR h
        · exact ⟨.inr (by simpa using h), fun _ => by simpa using h⟩
    · rintro a' o' b' l' y h1 h2
      simp only [PSt.run.injEq] at h1
      obtain ⟨rfl, rfl, rfl, rfl⟩ := h1
      left; exact ⟨_, _, _, hr, by simpa using h2⟩
    · rintro a' v'' b' l' h1 _ h3 _
      simp only [PSt.run.injEq] at h1
      obtain ⟨rfl, -, -, -⟩ := h1
      exact ⟨_, _, _, hr, h3⟩
    · exact hI.f3 r
    · intro t p hk
      rw [hr] at hk
      obtain ⟨ka, kb, kc⟩ := hk
      exact ⟨ka, fun h1 h2 => kb (by simpa using h1) (by simpa using h2),
        fun h1 h2 => by simpa using kc (by simpa using h1) (by simpa using h2)⟩
    · apply hI.hkk_of
      · intro t p hk
        rw [hr] at hk
        obtain ⟨ka, kb, kc⟩ := hk
        exact ⟨ka, fun h1 h2 => kb (by simpa using h1) (by simpa using h2),
          fun h1 h2 => by simpa using kc (by simpa using h1) (by simpa using h2)⟩
      · intro h1
        rw [hr]
        exact ⟨by simpa using h1, by simp⟩
  · have hf2a' : g.s r ≤ g.wc ∧ g.rv (g.s r) = tr := by simpa using hf2a (by simp [hcp])
    have hlt : g.s r < g.wc := by
      rcases Nat.lt_or_eq_of_le hf2a'.1 with h1 | h1
      · exact h1
      · exact absurd (by rw [hI.R, ← h1, hf2a'.2]) hR
    apply hI.local r _ _ (g.s r)
    · rintro a' o' b' l' h1
      simp only [PSt.run.injEq] at h1
      obtain ⟨rfl, rfl, rfl, -⟩ := h1
      exact ⟨_, _, hr⟩
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp [hres', hrd', hcp, hT]
      · simp
      · intro a' v'' b' l' h1 h2 h3 h4
        simp only [PSt.run.injEq] at h1
        obtain ⟨rfl, -⟩ := h1
        exact hm1 _ _ _ _ rfl (by simp [hcp]) h3 h4
      · intro a' v'' b' l' h1 _
        simp only [PSt.run.injEq] at h1
        obtain ⟨rfl, -⟩ := h1
        cases hw : g.wr r
        · exact (hm1 _ _ _ _ rfl (by simp [hcp]) hw (by omega)).2 hlt
        · exact hm2 _ _ _ _ rfl (.inl hw)
      · simp
      · intro h1 k hk1 hk2 hk3
        simpa using hf1 (by simp [hcp]) k hk1 hk2 hk3
      · exact hf1w
      · intro h1
        simpa using hf2a (by simp [hcp])
      · intro h1
        simpa using hf2b (by simp [hcp])
      · intro _; exact hlt
      · intro h1 hb
        exact hcl1 (by simp [hcp]) (by simpa using hb)
      · intro h1 h2
        refine ⟨?_, by simp⟩
        simpa using (hc2 h1 h2).1
    · rintro a' o' b' l' y h1 h2
      simp only [PSt.run.injEq] at h1
      obtain ⟨rfl, rfl, rfl, rfl⟩ := h1
      left; exact ⟨_, _, _, hr, by simpa using h2⟩
    · rintro a' v'' b' l' h1 _ h3 _
      simp only [PSt.run.injEq] at h1
      obtain ⟨rfl, -, -, -⟩ := h1
      exact ⟨_, _, _, hr, h3⟩
    · exact hI.f3 r
    · intro t p hk
      rw [hr] at hk
      obtain ⟨ka, kb, kc⟩ := hk
      exact ⟨ka, fun h1 h2 => kb (by simp [hcp]) (by simpa using h2),
        fun _ _ => ⟨hT, Nat.zero_le _⟩⟩
    · apply hI.hkk_of
      · intro t p hk
        rw [hr] at hk
        obtain ⟨ka, kb, kc⟩ := hk
        exact ⟨ka, fun h1 h2 => kb (by simp [hcp]) (by simpa using h2),
          fun _ _ => ⟨hT, Nat.zero_le _⟩⟩
      · intro h1
        rw [hr]
        exact ⟨by simpa using h1, by simp⟩

/-- Line 20, second conjunct (and line 21). -/
theorem step_r20b (hI : Inv v₀ C g h L) {r : Fin n} {a : ℕ} {o : RWOp V} {b : Bool} {v : V}
    {tr : Trip V n} {mt : Bool} (hr : C.ps r = .run a o b (.r20b v tr mt)) :
    StepOK C h (.step r) := by
  rw [StepOK, step1_sh hr rfl]
  refine ⟨⟨g.wc, g.rv, Function.update g.s r (g.s r), g.wr⟩, L, ?_⟩
  rw [List.append_nil, pv_self' C r]
  dsimp only
  have hp := hI.pi r
  rw [hr] at hp
  obtain ⟨hlc, -, hm1, hm2, -, hf1, hf1w, hf2a, hf2b, hd, hcl1, hc2⟩ := hp
  cases o with
  | read => simp at hlc
  | write v' =>
  obtain ⟨⟨rfl, rfl, hres', hcp⟩, hcp2, hwrcp, hres, hrd, htt1, htt2⟩ := hlc
  have hrd' : (C.pv r).rd = some (mt, tr) := by simpa using hrd (by omega)
  have hT : (C.pv r).T = mt := by simpa using htt1 (by simp [hcp]) (by omega)
  split_ifs with hb
  · -- line 21: return fail
    have hwr : g.wr r = false := by
      cases hw : g.wr r
      · rfl
      · have := (hc2 hw hcp).2 (by simp)
        simp only [bitOf, vw, Loc.info] at this
        rw [hb] at this; exact absurd this (by simp)
    apply hI.local r _ _ (g.s r)
    · rintro a' o' b' l' h1
      simp only [PSt.run.injEq] at h1
      obtain ⟨rfl, rfl, rfl, -⟩ := h1
      exact ⟨_, _, hr⟩
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp [hres', hrd', hcp, hwr, hT]
      · simp
      · intro a' v'' b' l' h1 h2 h3 h4
        simp only [PSt.run.injEq] at h1
        obtain ⟨rfl, -⟩ := h1
        exact hm1 _ _ _ _ rfl (by simp [hcp]) h3 h4
      · intro a' v'' b' l' h1 h2
        simp [hwr, hcp] at h2
      · simp
      · intro h1 k hk1 hk2 hk3
        simpa [hrd'] using hf1 (by simp [hcp]) k hk1 hk2 hk3
      · exact hf1w
      · intro h1
        simpa [hrd'] using hf2a (by simp [hcp])
      · intro h1
        simpa [hrd'] using hf2b (by simp [hcp])
      · intro h1; simp [hcp] at h1
      · intro h1 hb'
        exact hcl1 (by simp [hcp]) (by simpa [hrd'] using hb')
      · simp [hwr]
    · rintro a' o' b' l' y h1 h2
      simp only [PSt.run.injEq] at h1
      obtain ⟨rfl, rfl, rfl, rfl⟩ := h1
      left; exact ⟨_, _, _, hr, by simpa using h2⟩
    · rintro a' v'' b' l' h1 _ h3 _
      simp only [PSt.run.injEq] at h1
      obtain ⟨rfl, -, -, -⟩ := h1
      exact ⟨_, _, _, hr, h3⟩
    · exact hI.f3 r
    · intro t p hk
      rw [hr] at hk
      obtain ⟨ka, kb, kc⟩ := hk
      exact ⟨ka, fun h1 h2 => kb (by simp [hcp]) (by simpa [hrd'] using h2), by simp [hcp]⟩
    · intro hk; simp [hwr] at hk
  · -- the bit is set: proceed to line 22
    have hbt : C.sh.A (r, tr.2.1, !tr.2.2) = true := by simpa using hb
    have hlt : g.s r < g.wc := hcl1 (by simp [hcp]) (by simpa using hbt)
    apply hI.local r _ _ (g.s r)
    · rintro a' o' b' l' h1
      simp only [PSt.run.injEq] at h1
      obtain ⟨rfl, rfl, rfl, -⟩ := h1
      exact ⟨_, _, hr⟩
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp [hres', hrd', hcp, hT]
      · simp
      · intro a' v'' b' l' h1 h2 h3 h4
        simp only [PSt.run.injEq] at h1
        obtain ⟨rfl, -⟩ := h1
        exact hm1 _ _ _ _ rfl (by simp [hcp]) h3 h4
      · intro a' v'' b' l' h1 _
        simp only [PSt.run.injEq] at h1
        obtain ⟨rfl, -⟩ := h1
        cases hw : g.wr r
        · exact (hm1 _ _ _ _ rfl (by simp [hcp]) hw (by omega)).2 hlt
        · exact hm2 _ _ _ _ rfl (.inl hw)
      · simp
      · intro h1 k hk1 hk2 hk3
        simpa using hf1 (by simp [hcp]) k hk1 hk2 hk3
      · exact hf1w
      · intro h1
        simpa using hf2a (by simp [hcp])
      · intro h1
        simpa using hf2b (by simp [hcp])
      · intro _; exact hlt
      · intro h1 hb'
        exact hcl1 (by simp [hcp]) (by simpa using hb')
      · intro h1 h2
        exact ⟨.inr (by simpa using hbt), by simp⟩
    · rintro a' o' b' l' y h1 h2
      simp only [PSt.run.injEq] at h1
      obtain ⟨rfl, rfl, rfl, rfl⟩ := h1
      left; exact ⟨_, _, _, hr, by simpa using h2⟩
    · rintro a' v'' b' l' h1 _ h3 _
      simp only [PSt.run.injEq] at h1
      obtain ⟨rfl, -, -, -⟩ := h1
      exact ⟨_, _, _, hr, h3⟩
    · exact hI.f3 r
    · intro t p hk
      rw [hr] at hk
      obtain ⟨ka, kb, kc⟩ := hk
      exact ⟨ka, fun h1 h2 => kb (by simp [hcp]) (by simpa using h2),
        fun _ _ => ⟨hT, Nat.zero_le _⟩⟩
    · apply hI.hkk_of
      · intro t p hk
        rw [hr] at hk
        obtain ⟨ka, kb, kc⟩ := hk
        exact ⟨ka, fun h1 h2 => kb (by simp [hcp]) (by simpa using h2),
          fun _ _ => ⟨hT, Nat.zero_le _⟩⟩
      · intro h1
        rw [hr]
        exact ⟨by simpa using h1, by simp⟩

/-- `Read`, persisting the value read. -/
theorem step_d2 (hI : Inv v₀ C g h L) {r : Fin n} {a : ℕ} {o : RWOp V} {b : Bool} {x : V}
    (hr : C.ps r = .run a o b (.d2 x)) : StepOK C h (.step r) := by
  rw [StepOK, step1_pv hr rfl]
  refine ⟨⟨g.wc, g.rv, Function.update g.s r (g.s r), g.wr⟩, L, ?_⟩
  rw [List.append_nil]
  dsimp only
  have hp := hI.pi r
  rw [hr] at hp
  obtain ⟨hlc, -, -, -, hmr, -, -, -, -, -, -, -⟩ := hp
  cases o with
  | write v' => simp at hlc
  | read =>
  obtain ⟨hres, hwr⟩ := hlc
  apply hI.local r _ _ (g.s r)
  · rintro a' o' b' l' h1
    simp only [PSt.run.injEq] at h1
    obtain ⟨rfl, rfl, rfl, -⟩ := h1
    exact ⟨_, _, hr⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> try simp [hwr]
    simpa using hmr _ _ _ rfl (.inl ⟨x, rfl⟩)
  · rintro a' o' b' l' y h1 h2
    simp only [PSt.run.injEq] at h1
    obtain ⟨rfl, rfl, rfl, rfl⟩ := h1
    left; refine ⟨_, _, _, hr, .inr ?_⟩
    simp at h2; rw [h2]
  · rintro a' v'' b' l' h1
    simp at h1
  · exact hI.f3 r
  · intro t p hk
    obtain ⟨ka, -, -⟩ := hk
    exact ⟨ka, by simp, by simp⟩
  · intro hk; simp at hk

/-- `Read.Recover`. -/
theorem step_dr (hI : Inv v₀ C g h L) {r : Fin n} {a : ℕ} {o : RWOp V} {b : Bool}
    (hr : C.ps r = .run a o b .dr) : StepOK C h (.step r) := by
  rw [StepOK, step1_pv hr rfl]
  refine ⟨⟨g.wc, g.rv, Function.update g.s r (g.s r), g.wr⟩, L, ?_⟩
  rw [List.append_nil]
  dsimp only
  have hp := hI.pi r
  rw [hr] at hp
  obtain ⟨hlc, -, -, -, hmr, -, -, -, -, -, -, -⟩ := hp
  cases o with
  | write v' => simp at hlc
  | read =>
  obtain ⟨-, hwr⟩ := hlc
  cases hx : (C.pv r).res with
  | none =>
    apply hI.local r _ _ (g.s r)
    · rintro a' o' b' l' h1
      simp only [PSt.run.injEq] at h1
      obtain ⟨rfl, rfl, rfl, -⟩ := h1
      exact ⟨_, _, hr⟩
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [hwr, hx]
    · rintro a' o' b' l' y h1 h2
      simp only [PSt.run.injEq] at h1
      obtain ⟨rfl, rfl, rfl, rfl⟩ := h1
      simp [hx] at h2
    · rintro a' v'' b' l' h1
      simp at h1
    · exact hI.f3 r
    · intro t p hk
      obtain ⟨ka, -, -⟩ := hk
      exact ⟨ka, by simp, by simp⟩
    · intro hk; simp at hk
  | some x =>
    apply hI.local r _ _ (g.s r)
    · rintro a' o' b' l' h1
      simp only [PSt.run.injEq] at h1
      obtain ⟨rfl, rfl, rfl, -⟩ := h1
      exact ⟨_, _, hr⟩
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> try simp [hwr, hx]
      simpa using hmr _ _ _ rfl (.inr (by simp [hx]))
    · rintro a' o' b' l' y h1 h2
      simp only [PSt.run.injEq] at h1
      obtain ⟨rfl, rfl, rfl, rfl⟩ := h1
      left; exact ⟨_, _, _, hr, by simpa using h2⟩
    · rintro a' v'' b' l' h1
      simp at h1
    · exact hI.f3 r
    · intro t p hk
      obtain ⟨ka, -, -⟩ := hk
      exact ⟨ka, by simp, by simp⟩
    · intro hk; simp at hk

end Alg1

end Papers.PODC2020.DetectableSpace
