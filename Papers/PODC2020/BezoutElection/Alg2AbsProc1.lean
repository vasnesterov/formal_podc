import Papers.PODC2020.BezoutElection.Alg2AbsWrite

/-!
# Algorithm 2, per-register abstraction: processing a copy (part 1)

Outcomes of `procX` and the steps that do not write: discarding a copy, the level change of line
N(17) and the phase change of line 4.
-/

set_option linter.unusedSectionVars false

namespace BezoutElection.Alg2

open AState

variable {Id : Type} [DecidableEq Id] {P : Type} [DecidableEq P] [Fintype P]
  {n U : ℕ} {ids : P → Id}

/-! ### Outcomes of `procX` -/

set_option linter.deprecated false

section Cases

variable (n U : ℕ) (me : Id) (l : ALoc Id) (r : Reg Id) (ok fin : Bool)

/-- The possible outcomes of processing a copy. -/
theorem procX_cases :
    (¬(r.level = l.lv ∧ r.level < U) ∧ l.lv < r.level ∧
      procX n U me l r ok fin =
        ({ l with ph := .electing, D := ∅, lo := false, lv := l.lv + 1 }, none)) ∨
    procX n U me l r ok fin = (l, none) ∨
    (r.level = l.lv ∧ r.level < U ∧ r.phase = .committing ∧ l.ph = .electing ∧
      procX n U me l r ok fin = ({ l with ph := .committing, D := ∅ }, none)) ∨
    (r.level = l.lv ∧ r.level < U ∧ r.disc.card = n - 1 ∧ r.id ≠ none ∧
      r.phase = .committing ∧ me ∉ r.disc ∧
      procX n U me l r ok fin = ({ l with ca := false }, some ⟨none, ∅, .electing, r.level + 1,
        if fin then insert me r.leaders else r.leaders⟩)) ∨
    (r.level = l.lv ∧ r.level < U ∧ r.disc.card = n - 1 ∧ r.id ≠ none ∧ r.phase = .electing ∧
      procX n U me l r ok fin = (l, some ⟨none, ∅, .committing, r.level, r.leaders⟩)) ∨
    (r.level = l.lv ∧ r.level < U ∧ ¬(r.phase = .committing ∧ l.ph = .electing) ∧
      r.id = none ∧ l.lo = false ∧
      procX n U me l r ok fin =
        ({ l with ca := true, D := if r.phase = l.ph then l.D ∪ r.disc else l.D },
         some ⟨some me, if r.phase = l.ph then l.D ∪ r.disc else l.D, l.ph, r.level, r.leaders⟩)) ∨
    (r.level = l.lv ∧ r.level < U ∧ ¬(r.phase = .committing ∧ l.ph = .electing) ∧
      r.disc.card ≠ n - 1 ∧ r.id ≠ none ∧ r.id ≠ some me ∧ me ∉ r.disc ∧
      procX n U me l r ok fin = ({ l with ca := false, lo := true, D := insert me r.disc },
        some ⟨none, insert me r.disc, l.ph, r.level, r.leaders⟩)) := by
  unfold procX
  by_cases h1 : r.level = l.lv ∧ r.level < U
  · rw [if_pos h1]
    by_cases h2 : r.phase = .committing ∧ l.ph = .electing
    · rw [if_pos h2]; exact Or.inr (Or.inr (Or.inl ⟨h1.1, h1.2, h2.1, h2.2, rfl⟩))
    rw [if_neg h2]
    by_cases h3 : r.disc.card = n - 1 ∧ r.id ≠ none
    · rw [if_pos h3]
      by_cases h4 : r.phase = .committing
      · rw [if_pos h4]
        by_cases h5 : me ∉ r.disc
        · rw [if_pos h5]
          exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h1.1, h1.2, h3.1, h3.2, h4, h5, rfl⟩)))
        · rw [if_neg h5]; exact Or.inr (Or.inl rfl)
      · rw [if_neg h4]
        have h4' : r.phase = .electing := by cases h : r.phase <;> simp_all
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h1.1, h1.2, h3.1, h3.2, h4', rfl⟩))))
    rw [if_neg h3]
    by_cases h6 : r.id = none ∧ l.lo = false ∧ ok = true
    · rw [if_pos h6]
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h1.1, h1.2, h2, h6.1, h6.2.1, rfl⟩)))))
    rw [if_neg h6]
    by_cases h7 : r.id ≠ none ∧ r.id ≠ some me ∧ me ∉ r.disc
    · rw [if_pos h7]
      refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨h1.1, h1.2, h2, ?_, h7.1, h7.2.1,
        h7.2.2, rfl⟩)))))
      intro hc; exact h3 ⟨hc, h7.1⟩
    · rw [if_neg h7]; exact Or.inr (Or.inl rfl)
  · rw [if_neg h1]
    by_cases h8 : l.lv < r.level
    · rw [if_pos h8]; exact Or.inl ⟨h1, h8, rfl⟩
    · rw [if_neg h8]; exact Or.inr (Or.inl rfl)

lemma procL_eq {l' : ALoc Id} {o : Option (Reg Id)} (h : procX n U me l r ok fin = (l', o)) :
    procL n U me l r ok fin = { l' with st := stOf o } := by
  unfold procL; rw [h]

end Cases

/-! ### Helpers for updates without a new copy -/

lemma upd_copy {A : AState Id P} {p j : P} {l : ALoc Id} {v : Reg Id} (hl : ∀ v, l.st ≠ .copy v)
    (h : ((A.upd p l).loc j).st = .copy v) : j ≠ p ∧ (A.loc j).st = .copy v := by
  by_cases hj : j = p
  · subst hj; simp at h; exact absurd h (hl v)
  · exact ⟨hj, by rwa [upd_loc_ne _ _ hj] at h⟩

lemma upd_pend {A : AState Id P} {p j : P} {l : ALoc Id} {w : Reg Id}
    (h : ((A.upd p l).loc j).st = .pend w) :
    (j ≠ p ∧ (A.loc j).st = .pend w) ∨ (j = p ∧ l.st = .pend w) := by
  by_cases hj : j = p
  · subst hj; simp at h; exact Or.inr ⟨rfl, h⟩
  · exact Or.inl ⟨hj, by rwa [upd_loc_ne _ _ hj] at h⟩

lemma upd_val {A : AState Id P} {p : P} {l : ALoc Id} {u : Reg Id} (hl : ∀ v, l.st ≠ .copy v)
    (h : (A.upd p l).Val u) : A.Val u ∨ (l.st = .pend u ∧ u.level = A.reg.level) := by
  rcases val_upd h with h | h | ⟨h, -⟩
  · exact Or.inl h
  · exact Or.inr h
  · exact absurd h (hl u)

/-- The leader's identifier is not in any `discarded` set. -/
lemma Lead.not_actLoser {A : AState Id P} {ℓ : P} (E : Lead n ids A ℓ)
    (hid : Function.Injective ids) : ¬A.ActLoser ids (ids ℓ) := by
  rintro ⟨i, hi, -, hlo⟩
  rw [hid hi, E.act.2] at hlo; cases hlo

/-! ### Discarding a copy -/

theorem ainv_consume {A : AState Id P} {p : P} {v : Reg Id}
    (hI : AInv n U ids A) (hp : (A.loc p).st = .copy v) :
    AInv n U ids (A.setSt p .fresh) := by
  obtain ⟨B, hL⟩ := hI
  have hcopy : ∀ j v', ((A.setSt p .fresh).loc j).st = .copy v' → j ≠ p ∧ (A.loc j).st = .copy v' :=
    fun j v' h => upd_copy (by simp) h
  have hpend : ∀ j w, ((A.setSt p .fresh).loc j).st = .pend w → (A.loc j).st = .pend w := by
    intro j w h
    rcases upd_pend h with ⟨-, h⟩ | ⟨-, h⟩
    · exact h
    · cases h
  have hval : ∀ u, (A.setSt p .fresh).Val u → A.Val u := by
    intro u hu
    rcases upd_val (by simp) hu with h | ⟨h, -⟩
    · exact h
    · cases h
  have hthr : ∀ j, (A.setSt p .fresh).Threat ids j → A.Threat ids j := by
    rintro j ⟨v', h1, h2⟩; exact ⟨v', (hcopy j v' h1).2, by simpa using h2⟩
  have hQ : ∀ ℓ j, A.Quiet ids ℓ j → (A.setSt p .fresh).Quiet ids ℓ j := by
    rintro ℓ j ⟨q1, q2, q3, q4⟩
    exact ⟨by simpa using q1, fun w h => q2 w (hpend j w h),
      fun v' h h1 => q3 v' (hcopy j v' h).2 h1, q4⟩
  refine ⟨⟨B.lvU, by simpa using B.lvLe, ?_, ?_, ?_, ?_, by simpa using B.lagCa, ?_, ?_, ?_, ?_,
    by simpa using B.regId, by simpa using B.caAct, ?_, fun j h => B.caU j (by simpa using h), ?_,
    ?_⟩, ?_⟩
  · intro j v' h; simpa using B.copyLv j v' (hcopy j v' h).2
  · intro j w h; have := B.pendLv j w (hpend j w h); simp only [setSt_lv, setSt_reg]; exact this
  · intro j v' h; exact B.copyLead j v' (hcopy j v' h).2
  · intro j v' h h1 h2
    obtain ⟨hj, h⟩ := hcopy j v' h
    simp only [setSt, upd_loc_ne _ _ hj, upd_reg] at h1 h2 ⊢
    exact B.dead j v' h h1 h2
  · intro u hu a ha; exact actLoser_setSt (B.disc u (hval u hu) a ha)
  · intro j hj a ha; exact actLoser_setSt (B.discLoc j (by simpa using hj) a (by simpa using ha))
  · intro j w h; simpa using B.pendId j w (hpend j w h)
  · obtain ⟨j0, hj0⟩ := B.nonloser
    refine ⟨j0, ?_⟩
    rcases hj0 with h | ⟨h1, h2⟩
    · exact Or.inl (by simpa using h)
    · exact Or.inr ⟨by simpa using h1, fun h => h2 (hthr j0 h)⟩
  · intro j v' h hr; exact B.copyOwn j v' (hcopy j v' h).2 hr
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
      exact ⟨fun j hj => by simpa using h1 j (by simpa using hj), h2,
        fun j w h hl => h3 j w (hpend j w h) hl,
        fun j v' h hl hj => h4 j v' (hcopy j v' h).2 hl (by simpa using hj)⟩
    · exact Or.inr (Or.inl ⟨c, by simpa using hc, fun h => hT (hthr c h)⟩)
    · have hcp : c ≠ p := by rintro rfl; rw [hp] at hw; cases hw
      exact Or.inr (Or.inr ⟨c, w, by rw [setSt_st_ne _ _ hcp]; exact hw, hl⟩)
  · rcases hL with N | ⟨ℓ, E⟩
    · left
      exact ⟨fun u hu => N.valsEl u (hval u hu), by simpa using N.phEl,
        fun j w h => N.noN11 j w (hpend j w h), by simpa using N.strict⟩
    · right
      refine ⟨ℓ, ⟨by simpa using E.act, by simpa using E.others, ?_, ?_, ?_, ?_⟩⟩
      · intro j v' h h1 h2 h3 h4
        simpa using E.copyOther j v' (hcopy j v' h).2 h1 (by simpa using h2) h3 h4
      · intro j v' h h1 h2 h3 h4 h5
        simpa using E.copyLE j v' (hcopy j v' h).2 h1 (by simpa using h2) h3 h4 h5
      · intro hph
        have El := E.el (by simpa using hph)
        exact ⟨by simpa using El.card, by simpa using El.ca, El.regL,
          fun j v' h h1 h2 h3 => El.copyL j v' (hcopy j v' h).2 h1 (by simpa using h2) h3,
          fun u hu => El.coVals u (hval u hu), fun j w h => El.noN11 j w (hpend j w h)⟩
      · intro hph
        have Co := E.co (by simpa using hph)
        refine ⟨fun w h h1 => by simpa using Co.closing w (hpend ℓ w h) h1, ?_,
          by simpa using Co.regL, ?_, ?_, ?_, ?_, ?_, ?_,
          fun j w h h1 => Co.n11 j w (hpend j w h) h1⟩
        · intro _
          by_cases hℓ : ℓ = p
          · subst hℓ; simpa using Co.ca (fun w h => by rw [hp] at h; cases h)
          · simpa using Co.ca (fun w h => by
              have := ‹∀ w, ((A.setSt p .fresh).loc ℓ).st = .pend w → _› w
              rw [setSt_st_ne _ _ hℓ] at this; simpa using this h)
        · intro j v' h h1 h2 h3
          simpa using Co.copyL j v' (hcopy j v' h).2 h1 (by simpa using h2) h3
        · intro h1 h2 j hj
          rcases Co.regBot h1 h2 j hj with h | h
          · exact Or.inl (by simpa using h)
          · exact Or.inr (hQ ℓ j h)
        · intro v' h h1 h2 h3 j hj
          rcases Co.copyBot v' (hcopy ℓ v' h).2 h1 h2 h3 j hj with h | h
          · exact Or.inl (by simpa using h)
          · exact Or.inr (hQ ℓ j h)
        · intro v' h h1 h2; exact Co.copyBotReg v' (hcopy ℓ v' h).2 h1 h2
        · intro k w h h1 h2 h3 j hj
          simpa using Co.pendBot k w (hpend k w h) h1 h2 h3 j hj
        · intro j hj; exact hQ ℓ j (Co.quiet j (by simpa using hj))

end BezoutElection.Alg2
