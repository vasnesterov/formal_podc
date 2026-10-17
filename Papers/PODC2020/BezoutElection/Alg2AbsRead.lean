import Papers.PODC2020.BezoutElection.Alg2AbsLemmas

/-!
# Algorithm 2, per-register abstraction: the invariant is preserved by reads
-/

set_option linter.unusedSectionVars false

namespace BezoutElection.Alg2

open AState

variable {Id : Type} [DecidableEq Id] {P : Type} [DecidableEq P] [Fintype P]
  {n U : ℕ} {ids : P → Id}

lemma val_setSt_copy {A : AState Id P} {p : P} {u : Reg Id}
    (h : (A.setSt p (.copy A.reg)).Val u) : A.Val u := by
  rcases val_upd h with h | ⟨h1, -⟩ | ⟨h1, -, -⟩
  · exact h
  · simp at h1
  · simp only [AStatus.copy.injEq] at h1; subst h1; exact Or.inl rfl

lemma actLoser_setSt {A : AState Id P} {p : P} {s : AStatus Id} {a : Id}
    (h : A.ActLoser ids a) : (A.setSt p s).ActLoser ids a := by
  obtain ⟨i, h1, h2, h3⟩ := h
  exact ⟨i, h1, by simpa using h2, by simpa using h3⟩

lemma threat_setSt_ne {A : AState Id P} {p j : P} {s : AStatus Id} (hj : j ≠ p) :
    (A.setSt p s).Threat ids j ↔ A.Threat ids j := threat_upd hj

lemma quiet_setSt_ne {A : AState Id P} {p ℓ j : P} {s : AStatus Id} (hj : j ≠ p) :
    (A.setSt p s).Quiet ids ℓ j ↔ A.Quiet ids ℓ j := quiet_upd hj

/-- Reading keeps `Quiet` when the register value is not a triggering value. -/
lemma quiet_read {A : AState Id P} {p ℓ j : P} (hq : A.Quiet ids ℓ j)
    (hreg : ∀ a, A.reg.id = some a → a = ids ℓ)
    (hregL : A.reg.id = some (ids ℓ) → A.reg.phase = .committing) :
    (A.setSt p (.copy A.reg)).Quiet ids ℓ j := by
  by_cases hj : j = p
  · subst hj
    obtain ⟨h1, h2, h3, h4⟩ := hq
    refine ⟨by simpa using h1, by simp, ?_, by simpa using h4⟩
    intro v hv _
    simp only [setSt_st_self, AStatus.copy.injEq] at hv
    subst hv
    cases hr : A.reg.id with
    | none => exact Or.inl rfl
    | some a =>
      have := hreg a hr; subst this
      exact Or.inr ⟨hregL hr, h4 hr⟩
  · exact (quiet_setSt_ne hj).2 hq

theorem ainv_read {A : AState Id P} {p : P}
    (hI : AInv n U ids A) (hp : (A.loc p).st = .fresh) :
    AInv n U ids (A.setSt p (.copy A.reg)) := by
  obtain ⟨B, hL⟩ := hI
  have hst : ∀ j, ((A.setSt p (.copy A.reg)).loc j).st =
      if j = p then .copy A.reg else (A.loc j).st := by
    intro j; split_ifs with h
    · subst h; simp
    · exact setSt_st_ne _ _ h
  -- copies of the new state
  have hcopy : ∀ j v, ((A.setSt p (.copy A.reg)).loc j).st = .copy v →
      (j ≠ p ∧ (A.loc j).st = .copy v) ∨ (j = p ∧ v = A.reg) := by
    intro j v h; rw [hst] at h
    split_ifs at h with hj
    · simp only [AStatus.copy.injEq] at h; exact Or.inr ⟨hj, h.symm⟩
    · exact Or.inl ⟨hj, h⟩
  have hpend : ∀ j w, ((A.setSt p (.copy A.reg)).loc j).st = .pend w → (A.loc j).st = .pend w := by
    intro j w h
    by_cases hj : j = p
    · subst hj; simp at h
    · rwa [setSt_st_ne _ _ hj] at h
  refine ⟨⟨B.lvU, by simpa using B.lvLe, ?_, ?_, ?_, ?_, by simpa using B.lagCa, ?_, ?_, ?_, ?_,
    by simpa using B.regId, by simpa using B.caAct, ?_, fun j h => B.caU j (by simpa using h), ?_,
    ?_⟩, ?_⟩
  · intro j v h
    rcases hcopy j v h with ⟨-, h⟩ | ⟨rfl, rfl⟩
    · simpa using B.copyLv j v h
    · simpa using B.lvLe j
  · intro j w h; have := B.pendLv j w (hpend j w h); simp only [setSt_lv, setSt_reg]; exact this
  · intro j v h
    rcases hcopy j v h with ⟨-, h⟩ | ⟨rfl, rfl⟩
    · simpa using B.copyLead j v h
    · simp
  · intro j v h h1 h2
    rcases hcopy j v h with ⟨hj, h⟩ | ⟨rfl, rfl⟩
    · simp only [setSt, upd_loc_ne _ _ hj, upd_reg] at h1 h2 ⊢
      exact B.dead j v h h1 h2
    · simp at h1 h2; omega
  · intro u hu a ha
    exact actLoser_setSt (B.disc u (val_setSt_copy hu) a ha)
  · intro j hj a ha
    exact actLoser_setSt (B.discLoc j (by simpa using hj) a (by simpa using ha))
  · intro j w h; simpa using B.pendId j w (hpend j w h)
  · -- nonloser
    obtain ⟨j0, hj0⟩ := B.nonloser
    by_cases hj0p : j0 = p
    · subst hj0p
      rcases hj0 with h | ⟨hlo, hth⟩
      · exact ⟨j0, Or.inl (by simpa using h)⟩
      · by_cases hT : (A.setSt j0 (.copy A.reg)).Threat ids j0
        · obtain ⟨v, hv, -, -, hv1, hv2, -⟩ := hT
          simp only [setSt_st_self, AStatus.copy.injEq] at hv
          subst hv
          obtain ⟨a, ha⟩ := Option.ne_none_iff_exists'.1 hv1
          obtain ⟨c, rfl, hc1, hc2⟩ := B.regId a ha
          refine ⟨c, Or.inr ⟨by simpa using hc2, ?_⟩⟩
          have hcp : c ≠ j0 := by
            rintro rfl; exact hv2 ha
          rw [threat_setSt_ne hcp]
          rintro ⟨v, hv, -, -, -, hv2, -⟩
          exact hv2 (by rw [B.copyOwn c v hv ha]; exact ha)
        · exact ⟨j0, Or.inr ⟨by simpa using hlo, hT⟩⟩
    · refine ⟨j0, ?_⟩
      rw [threat_setSt_ne hj0p]; simpa using hj0
  · intro j v h hr
    rcases hcopy j v h with ⟨-, h⟩ | ⟨rfl, rfl⟩
    · exact B.copyOwn j v h hr
    · rfl
  · intro a ha
    obtain ⟨c, h1, h2⟩ := B.regCa a ha
    refine ⟨c, h1, ?_⟩
    rcases h2 with h2 | ⟨w, hw, hl⟩
    · exact Or.inl (by simpa using h2)
    · have hcp : c ≠ p := by rintro rfl; rw [hp] at hw; cases hw
      exact Or.inr ⟨w, by rw [setSt_st_ne _ _ hcp]; exact hw, hl⟩
  · rcases B.wit with hP | ⟨c, hc, hT⟩ | ⟨c, w, hw, hl⟩
    · left
      obtain ⟨h1, h2, h3, h4⟩ := hP
      refine ⟨fun j hj => by simpa using h1 j (by simpa using hj), h2,
        fun j w h hl => h3 j w (hpend j w h) hl, ?_⟩
      intro j v h hl hj
      rcases hcopy j v h with ⟨-, h⟩ | ⟨rfl, rfl⟩
      · exact h4 j v h hl (by simpa using hj)
      · exact h2
    · by_cases hcp : c = p
      · subst hcp
        by_cases hT' : (A.setSt c (.copy A.reg)).Threat ids c
        · obtain ⟨v, hv, -, -, hv1, hv2, -⟩ := hT'
          simp only [setSt_st_self, AStatus.copy.injEq] at hv
          subst hv
          obtain ⟨a, ha⟩ := Option.ne_none_iff_exists'.1 hv1
          obtain ⟨c', rfl, h2⟩ := B.regCa a ha
          rcases h2 with h2 | ⟨w, hw, hl⟩
          · right; left
            have hc'p : c' ≠ c := by rintro rfl; exact hv2 ha
            refine ⟨c', by simpa using h2, ?_⟩
            rw [threat_setSt_ne hc'p]
            rintro ⟨v, hv, -, -, -, hv2', -⟩
            exact hv2' (by rw [B.copyOwn c' v hv ha]; exact ha)
          · right; right
            have hc'p : c' ≠ c := by rintro rfl; rw [hp] at hw; cases hw
            exact ⟨c', w, by rw [setSt_st_ne _ _ hc'p]; exact hw, hl⟩
        · exact Or.inr (Or.inl ⟨c, by simpa using hc, hT'⟩)
      · exact Or.inr (Or.inl ⟨c, by simpa using hc, by rw [threat_setSt_ne hcp]; exact hT⟩)
    · have hcp : c ≠ p := by rintro rfl; rw [hp] at hw; cases hw
      exact Or.inr (Or.inr ⟨c, w, by rw [setSt_st_ne _ _ hcp]; exact hw, hl⟩)
  · rcases hL with N | ⟨ℓ, E⟩
    · left
      exact ⟨fun u hu => N.valsEl u (val_setSt_copy hu), by simpa using N.phEl,
        fun j w h => N.noN11 j w (hpend j w h), by simpa using N.strict⟩
    · right
      refine ⟨ℓ, ⟨by simpa using E.act, by simpa using E.others, ?_, ?_, ?_, ?_⟩⟩
      · -- the identifier in the register is the leader's
        have hregL : ∀ a, A.reg.id = some a → a = ids ℓ := by
          intro a ha
          obtain ⟨c, rfl, hc1, hc2⟩ := B.regId a ha
          by_contra hne
          have hcl : c ≠ ℓ := fun h => hne (by rw [h])
          have := (E.others c hcl).2; rw [hc2] at this; cases this
        intro j v h h1 h2 h3 h4
        rcases hcopy j v h with ⟨-, h⟩ | ⟨rfl, rfl⟩
        · simpa using E.copyOther j v h h1 (by simpa using h2) h3 h4
        · obtain ⟨a, ha⟩ := Option.ne_none_iff_exists'.1 h3
          exact absurd (by rw [ha, hregL a ha]) h4
      · intro j v h h1 h2 h3 h4 h5
        rcases hcopy j v h with ⟨-, h⟩ | ⟨rfl, rfl⟩
        · simpa using E.copyLE j v h h1 (by simpa using h2) h3 h4 h5
        · rcases hph : (A.loc ℓ).ph with _ | _
          · exact absurd ((E.el hph).regL h3).2 h5
          · rw [((E.co hph).regL h3).1] at h4; cases h4
      · intro hph
        have El := E.el (by simpa using hph)
        refine ⟨by simpa using El.card, by simpa using El.ca, El.regL, ?_, ?_, ?_⟩
        · intro j v h h1 h2 h3
          rcases hcopy j v h with ⟨-, h⟩ | ⟨rfl, rfl⟩
          · exact El.copyL j v h h1 (by simpa using h2) h3
          · exact (El.regL h3).1
        · intro u hu; exact El.coVals u (val_setSt_copy hu)
        · intro j w h; exact El.noN11 j w (hpend j w h)
      · intro hph
        have Co := E.co (by simpa using hph)
        have hregL : ∀ a, A.reg.id = some a → a = ids ℓ := by
          intro a ha
          obtain ⟨c, rfl, hc1, hc2⟩ := B.regId a ha
          by_contra hne
          have hcl : c ≠ ℓ := fun h => hne (by rw [h])
          have := (E.others c hcl).2; rw [hc2] at this; cases this
        have hQ : ∀ j, A.Quiet ids ℓ j → (A.setSt p (.copy A.reg)).Quiet ids ℓ j :=
          fun j hq => quiet_read hq hregL (fun h => (Co.regL h).1)
        refine ⟨?_, ?_, by simpa using Co.regL, ?_, ?_, ?_, ?_, ?_, ?_,
          fun j w h h1 => Co.n11 j w (hpend j w h) h1⟩
        · intro w h; simpa using Co.closing w (hpend ℓ w h)
        · intro _
          by_cases hℓ : ℓ = p
          · subst hℓ; simpa using Co.ca (fun w h => by rw [hp] at h; cases h)
          · simpa using Co.ca (fun w h => by
              have := ‹∀ w, ((A.setSt p (.copy A.reg)).loc ℓ).st = .pend w → _› w
              rw [setSt_st_ne _ _ hℓ] at this; simpa using this h)
        · intro j v h h1 h2 h3
          rcases hcopy j v h with ⟨-, h⟩ | ⟨rfl, rfl⟩
          · simpa using Co.copyL j v h h1 (by simpa using h2) h3
          · exact ⟨fun _ => (Co.regL h3).1, fun _ => by simpa using (Co.regL h3).2⟩
        · intro h1 h2 j hj
          rcases Co.regBot h1 h2 j hj with h | h
          · exact Or.inl (by simpa using h)
          · exact Or.inr (hQ j h)
        · intro v h h1 h2 h3 j hj
          rcases hcopy ℓ v h with ⟨-, h⟩ | ⟨-, rfl⟩
          · rcases Co.copyBot v h h1 h2 h3 j hj with h | h
            · exact Or.inl (by simpa using h)
            · exact Or.inr (hQ j h)
          · rcases Co.regBot h2 h3 j hj with h | h
            · exact Or.inl (by simpa using h)
            · exact Or.inr (hQ j h)
        · intro v h h1 h2
          rcases hcopy ℓ v h with ⟨-, h⟩ | ⟨-, rfl⟩
          · exact Co.copyBotReg v h h1 h2
          · exact h2
        · intro k w h h1 h2 h3 j hj
          simpa using Co.pendBot k w (hpend k w h) h1 h2 h3 j hj
        · intro j hj; exact hQ j (Co.quiet j (by simpa using hj))

end BezoutElection.Alg2
