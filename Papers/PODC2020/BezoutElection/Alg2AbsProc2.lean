import Papers.PODC2020.BezoutElection.Alg2AbsProc1

/-!
# Algorithm 2, per-register abstraction: processing a copy (part 2)

Non-writing steps: a lagging process (local level below the register's level) changing its
local variables (in particular the level change of line N(17)), and the phase change of line 4.
-/

set_option linter.unusedSectionVars false

namespace BezoutElection.Alg2

open AState

variable {Id : Type} [DecidableEq Id] {P : Type} [DecidableEq P] [Fintype P]
  {n U : ℕ} {ids : P → Id}

/-- A lagging process discards its copy and changes its local variables; if it reaches the
current level, it is a fresh electing non-loser. -/
theorem ainv_lagging {A : AState Id P} {p : P} {v : Reg Id} {l : ALoc Id}
    (hI : AInv n U ids A) (hp : (A.loc p).st = .copy v) (hlag : (A.loc p).lv < A.reg.level)
    (hst : l.st = .fresh) (hca : l.ca = false) (hlv : l.lv ≤ A.reg.level)
    (hnew : l.lv = A.reg.level → l.lo = false ∧ l.ph = .electing ∧ l.D = ∅) :
    AInv n U ids (A.upd p l) := by
  obtain ⟨B, hL⟩ := hI
  have hnc : ∀ v, l.st ≠ .copy v := by intro v h; rw [hst] at h; cases h
  have hcopy : ∀ j v', ((A.upd p l).loc j).st = .copy v' → j ≠ p ∧ (A.loc j).st = .copy v' :=
    fun j v' h => upd_copy hnc h
  have hpend : ∀ j w, ((A.upd p l).loc j).st = .pend w → j ≠ p ∧ (A.loc j).st = .pend w := by
    intro j w h
    rcases upd_pend h with h | ⟨-, h⟩
    · exact h
    · rw [hst] at h; cases h
  have hval : ∀ u, (A.upd p l).Val u → A.Val u := by
    intro u hu
    rcases upd_val hnc hu with h | ⟨h, -⟩
    · exact h
    · rw [hst] at h; cases h
  have hAL : ∀ a, A.ActLoser ids a → (A.upd p l).ActLoser ids a :=
    fun a h => actLoser_upd h (fun h1 _ => absurd h1 hlag.ne)
  -- nobody is the leader: all processes are active in `Lead`
  have hNo : NoLead n A := by
    rcases hL with N | ⟨ℓ, E⟩
    · exact N
    · exfalso
      by_cases hpℓ : p = ℓ
      · subst hpℓ; exact hlag.ne E.act.1
      · exact hlag.ne (E.others p hpℓ).1
  have hloc : ∀ j, j ≠ p → (A.upd p l).loc j = A.loc j := fun j hj => upd_loc_ne _ _ hj
  refine ⟨⟨B.lvU, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
    Or.inl ⟨?_, ?_, ?_, ?_⟩⟩
  · intro j; by_cases hj : j = p
    · subst hj; simpa using hlv
    · rw [hloc j hj]; exact B.lvLe j
  · intro j v' h; obtain ⟨hj, h⟩ := hcopy j v' h; rw [hloc j hj]; exact B.copyLv j v' h
  · intro j w h; obtain ⟨hj, h⟩ := hpend j w h; rw [hloc j hj]; exact B.pendLv j w h
  · intro j v' h; exact B.copyLead j v' (hcopy j v' h).2
  · intro j v' h; obtain ⟨hj, h⟩ := hcopy j v' h; rw [hloc j hj]; exact B.dead j v' h
  · intro j hj'; by_cases hj : j = p
    · subst hj; simpa using hca
    · rw [hloc j hj] at hj' ⊢; exact B.lagCa j hj'
  · intro u hu a ha; exact hAL a (B.disc u (hval u hu) a ha)
  · intro j hj' a ha
    by_cases hj : j = p
    · subst hj; simp at hj' ha; rw [(hnew hj').2.2] at ha; simp at ha
    · rw [hloc j hj] at hj' ha; exact hAL a (B.discLoc j hj' a ha)
  · intro j w h; obtain ⟨hj, h⟩ := hpend j w h; rw [hloc j hj]; exact B.pendId j w h
  · refine ⟨p, ?_⟩
    simp only [upd_loc_self, upd_reg]
    by_cases h : l.lv = A.reg.level
    · right; refine ⟨(hnew h).1, ?_⟩
      rintro ⟨v', h1, -⟩; simp at h1; exact hnc v' h1
    · left; omega
  · intro a ha
    obtain ⟨c, h1, h2, h3⟩ := B.regId a ha
    have hc : c ≠ p := by rintro rfl; exact hlag.ne h2
    exact ⟨c, h1, by rw [hloc c hc]; exact ⟨h2, h3⟩⟩
  · intro j h; by_cases hj : j = p
    · subst hj; simp [hca] at h
    · rw [hloc j hj] at h ⊢; exact B.caAct j h
  · intro j v' h hr; obtain ⟨hj, h⟩ := hcopy j v' h; exact B.copyOwn j v' h hr
  · intro j h; by_cases hj : j = p
    · subst hj; simp [hca] at h
    · rw [hloc j hj] at h; exact B.caU j h
  · intro a ha
    obtain ⟨c, h1, h2⟩ := B.regCa a ha
    have hcp : c ≠ p := by
      rintro rfl
      rcases h2 with h2 | ⟨w, hw, -⟩
      · rw [B.lagCa c hlag] at h2; cases h2
      · rw [hp] at hw; cases hw
    exact ⟨c, h1, by rw [hloc c hcp]; exact h2⟩
  · rcases B.wit with hP | ⟨c, hc, hT⟩ | ⟨c, w, hw, hl⟩
    · left
      obtain ⟨h1, h2, h3, h4⟩ := hP
      refine ⟨fun j hj => ?_, h2, fun j w h hl => ?_, fun j v' h hl hjl => ?_⟩
      · by_cases hjp : j = p
        · subst hjp; simp at hj ⊢; exact (hnew hj).1
        · rw [hloc j hjp] at hj ⊢; exact h1 j hj
      · obtain ⟨-, h⟩ := hpend j w h; exact h3 j w h hl
      · obtain ⟨hjp, h⟩ := hcopy j v' h; rw [hloc j hjp] at hjl; exact h4 j v' h hl hjl
    · have hcp : c ≠ p := by rintro rfl; rw [B.lagCa c hlag] at hc; cases hc
      exact Or.inr (Or.inl ⟨c, by rw [hloc c hcp]; exact hc, by rw [threat_upd hcp]; exact hT⟩)
    · have hcp : c ≠ p := by rintro rfl; rw [hp] at hw; cases hw
      exact Or.inr (Or.inr ⟨c, w, by rw [hloc c hcp]; exact hw, hl⟩)
  · intro u hu; exact hNo.valsEl u (hval u hu)
  · intro j hj'; by_cases hj : j = p
    · subst hj; simp at hj' ⊢; exact (hnew hj').2.1
    · rw [hloc j hj] at hj' ⊢; exact hNo.phEl j hj'
  · intro j w h; obtain ⟨hj, h⟩ := hpend j w h; exact hNo.noN11 j w h
  · intro c h1 h2 h3
    by_cases hcp : c = p
    · subst hcp; simp at h3; rw [hca] at h3; cases h3
    · rw [hloc c hcp] at h1 h2 h3 ⊢; exact hNo.strict c h1 h2 h3

/-- The level change of line N(17). -/
theorem ainv_lvup {A : AState Id P} {p : P} {v : Reg Id}
    (hI : AInv n U ids A) (hp : (A.loc p).st = .copy v) (h2 : (A.loc p).lv < v.level) :
    AInv n U ids (A.upd p { A.loc p with ph := .electing, D := ∅, lo := false,
                                         lv := (A.loc p).lv + 1, st := .fresh }) := by
  have hv := (hI.1.copyLv p v hp).2
  exact ainv_lagging hI hp (by omega) rfl (hI.1.lagCa p (by omega)) (by simp; omega)
    (fun _ => ⟨rfl, rfl, rfl⟩)

/-- The phase change of line 4. -/
theorem ainv_line4 {A : AState Id P} {p : P} {v : Reg Id}
    (hI : AInv n U ids A) (hp : (A.loc p).st = .copy v) (h1 : v.level = (A.loc p).lv)
    (hC : v.phase = .committing) (hE : (A.loc p).ph = .electing) :
    AInv n U ids (A.upd p { A.loc p with ph := .committing, D := ∅, st := .fresh }) := by
  rcases (hI.1.lvLe p).lt_or_eq with hlag | hact
  · exact ainv_lagging hI hp hlag rfl (hI.1.lagCa p hlag) (by simpa using (hI.1.lvLe p))
      (fun h => absurd h (by simpa using hlag.ne))
  obtain ⟨B, hL⟩ := hI
  have hvL : v.level = A.reg.level := h1.trans hact
  have hvV : A.Val v := Or.inr (Or.inr ⟨p, hp, hvL, hact⟩)
  set l : ALoc Id := { A.loc p with ph := .committing, D := ∅, st := .fresh } with hl
  have hnc : ∀ v, l.st ≠ .copy v := by intro v h; cases h
  have hcopy : ∀ j v', ((A.upd p l).loc j).st = .copy v' → j ≠ p ∧ (A.loc j).st = .copy v' :=
    fun j v' h => upd_copy hnc h
  have hpend : ∀ j w, ((A.upd p l).loc j).st = .pend w → j ≠ p ∧ (A.loc j).st = .pend w := by
    intro j w h
    rcases upd_pend h with h | ⟨-, h⟩
    · exact h
    · cases h
  have hval : ∀ u, (A.upd p l).Val u → A.Val u := by
    intro u hu
    rcases upd_val hnc hu with h | ⟨h, -⟩
    · exact h
    · cases h
  have hAL : ∀ a, A.ActLoser ids a → (A.upd p l).ActLoser ids a :=
    fun a h => actLoser_upd h (fun h1 h2 => ⟨h1, h2⟩)
  have hloc : ∀ j, j ≠ p → (A.upd p l).loc j = A.loc j := fun j hj => upd_loc_ne _ _ hj
  have hthr : ∀ j, (A.upd p l).Threat ids j → A.Threat ids j := by
    rintro j ⟨v', h1, h2, h3, h4⟩
    obtain ⟨hj, h1⟩ := hcopy j v' h1
    exact ⟨v', h1, h2, by rwa [hloc j hj] at h3, h4⟩
  have BB : Basic n U ids (A.upd p l) := by
    refine ⟨B.lvU, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro j; by_cases hj : j = p
      · subst hj; simpa using B.lvLe j
      · rw [hloc j hj]; exact B.lvLe j
    · intro j v' h; obtain ⟨hj, h⟩ := hcopy j v' h; rw [hloc j hj]; exact B.copyLv j v' h
    · intro j w h; obtain ⟨hj, h⟩ := hpend j w h; rw [hloc j hj]; exact B.pendLv j w h
    · intro j v' h; exact B.copyLead j v' (hcopy j v' h).2
    · intro j v' h; obtain ⟨hj, h⟩ := hcopy j v' h; rw [hloc j hj]; exact B.dead j v' h
    · intro j hj'; by_cases hj : j = p
      · subst hj; simp [hl] at hj'; omega
      · rw [hloc j hj] at hj' ⊢; exact B.lagCa j hj'
    · intro u hu a ha; exact hAL a (B.disc u (hval u hu) a ha)
    · intro j hj' a ha
      by_cases hj : j = p
      · subst hj; simp [hl] at ha
      · rw [hloc j hj] at hj' ha; exact hAL a (B.discLoc j hj' a ha)
    · intro j w h; obtain ⟨hj, h⟩ := hpend j w h; rw [hloc j hj]; exact B.pendId j w h
    · obtain ⟨j0, hj0⟩ := B.nonloser
      refine ⟨j0, ?_⟩
      by_cases hj : j0 = p
      · subst hj
        rcases hj0 with h | ⟨h, -⟩
        · left; simpa [hl] using h
        · right; refine ⟨by simpa [hl] using h, ?_⟩
          rintro ⟨v', h1, -⟩; simp [hl] at h1
      · rw [hloc j0 hj] at ⊢; rcases hj0 with h | ⟨h1, h2⟩
        · exact Or.inl h
        · exact Or.inr ⟨h1, fun h => h2 (hthr j0 h)⟩
    · intro a ha
      obtain ⟨c, h1, h2, h3⟩ := B.regId a ha
      refine ⟨c, h1, ?_⟩
      by_cases hc : c = p
      · subst hc; simpa [hl] using ⟨h2, h3⟩
      · rw [hloc c hc]; exact ⟨h2, h3⟩
    · intro j h; by_cases hj : j = p
      · subst hj; simpa [hl] using B.caAct j (by simpa [hl] using h)
      · rw [hloc j hj] at h ⊢; exact B.caAct j h
    · intro j v' h hr; obtain ⟨hj, h⟩ := hcopy j v' h; exact B.copyOwn j v' h hr
    · intro j h; by_cases hj : j = p
      · subst hj; exact B.caU j (by simpa [hl] using h)
      · rw [hloc j hj] at h; exact B.caU j h
    · intro a ha
      obtain ⟨c, h1, h2⟩ := B.regCa a ha
      refine ⟨c, h1, ?_⟩
      by_cases hcp : c = p
      · subst hcp
        rcases h2 with h2 | ⟨w, hw, -⟩
        · exact Or.inl (by simpa [hl] using h2)
        · rw [hp] at hw; cases hw
      · rw [hloc c hcp]; exact h2
    · rcases B.wit with hP | ⟨c, hc, hT⟩ | ⟨c, w, hw, hl'⟩
      · left
        obtain ⟨hP1, hP2, hP3, hP4⟩ := hP
        refine ⟨fun j hj => ?_, hP2, fun j w h hl' => hP3 j w (hpend j w h).2 hl',
          fun j v' h hl' hjl => ?_⟩
        · by_cases hjp : j = p
          · subst hjp; simpa [hl] using hP1 j (by simpa [hl] using hj)
          · rw [hloc j hjp] at hj ⊢; exact hP1 j hj
        · obtain ⟨hjp, h⟩ := hcopy j v' h; rw [hloc j hjp] at hjl; exact hP4 j v' h hl' hjl
      · by_cases hcp : c = p
        · subst hcp
          refine Or.inr (Or.inl ⟨c, by simpa [hl] using hc, ?_⟩)
          rintro ⟨v', h1, -⟩; simp [hl] at h1
        · exact Or.inr (Or.inl ⟨c, by rw [hloc c hcp]; exact hc, by rw [threat_upd hcp]; exact hT⟩)
      · have hcp : c ≠ p := by rintro rfl; rw [hp] at hw; cases hw
        exact Or.inr (Or.inr ⟨c, w, by rw [hloc c hcp]; exact hw, hl'⟩)
  refine ⟨BB, ?_⟩
  rcases hL with N | ⟨ℓ, E⟩
  · exact absurd hC (by rw [(N.valsEl v hvV).1]; simp)
  right
  refine ⟨ℓ, ?_⟩
  -- the leader is electing (a committing value exists only after the leader's line 8)
  by_cases hpℓ : p = ℓ
  · subst hpℓ
    have El := E.el hE
    have hrid : A.reg.id ≠ some (ids p) := by
      intro h
      have := B.copyOwn p v hp h; subst this
      exact absurd h (by rw [(El.coVals _ (Or.inl rfl) hC).1]; simp)
    refine ⟨by simpa [hl] using E.act, fun j hj => by rw [hloc j hj]; exact E.others j hj, ?_, ?_,
      fun h => by simp [hl] at h, fun _ => ?_⟩
    · intro j v' h h2 h3 h4 h5
      obtain ⟨hj, h⟩ := hcopy j v' h
      rw [hloc j hj] at h3 ⊢
      exact E.copyOther j v' h h2 h3 h4 h5
    · intro j v' h h2 h3 h4 h5 h6
      obtain ⟨hj, h⟩ := hcopy j v' h
      rw [hloc j hj] at h3 ⊢
      exact E.copyLE j v' h h2 h3 h4 h5 h6
    · refine ⟨?_, fun _ => by simpa [hl] using El.ca, fun h => absurd h hrid, ?_, ?_, ?_, ?_, ?_,
        fun j hj => by simp [hl] at hj, ?_⟩
      · intro w h; simp [hl] at h
      · intro j v' h h2 h3 h4
        obtain ⟨hj, h⟩ := hcopy j v' h
        rw [hloc j hj] at h3
        have := El.copyL j v' h h2 h3 h4
        exact ⟨fun h' => absurd h' hj, fun h' => by rw [this] at h'; cases h'⟩
      · intro h1 h2 j hj
        simp only [upd_reg] at h1 h2 hj
        rw [(El.coVals _ (Or.inl rfl) h2).2] at hj; simp at hj
      · intro v' h; simp [hl] at h
      · intro v' h; simp [hl] at h
      · intro k w h h1 h2 h3 j hj
        obtain ⟨-, h⟩ := hpend k w h
        rw [(El.coVals w (Or.inr (Or.inl ⟨k, h, h1⟩)) h3).2] at hj; simp at hj
      · intro j w h h1
        obtain ⟨-, h⟩ := hpend j w h
        have := El.noN11 j w h; simp at h1; omega
  · -- another process changes its phase
    have hQ : ∀ j, A.Quiet ids ℓ j → (A.upd p l).Quiet ids ℓ j := by
      intro j hq
      by_cases hj : j = p
      · subst hj; rw [hq.1] at hE; cases hE
      · exact (quiet_upd hj).2 hq
    refine ⟨by rw [hloc ℓ (Ne.symm hpℓ)]; exact E.act, fun j hj => ?_, ?_, ?_, ?_, ?_⟩
    · by_cases hjp : j = p
      · subst hjp; simpa [hl] using E.others j hj
      · rw [hloc j hjp]; exact E.others j hj
    · intro j v' h h2 h3 h4 h5
      obtain ⟨hj, h⟩ := hcopy j v' h
      rw [hloc j hj] at h3 ⊢
      exact E.copyOther j v' h h2 h3 h4 h5
    · intro j v' h h2 h3 h4 h5 h6
      obtain ⟨hj, h⟩ := hcopy j v' h
      rw [hloc j hj] at h3 ⊢
      exact E.copyLE j v' h h2 h3 h4 h5 h6
    · intro hph
      rw [hloc ℓ (Ne.symm hpℓ)] at hph
      have El := E.el hph
      refine ⟨by rw [hloc ℓ (Ne.symm hpℓ)]; exact El.card, by rw [hloc ℓ (Ne.symm hpℓ)]; exact El.ca,
        El.regL, ?_, fun u hu => El.coVals u (hval u hu),
        fun j w h => El.noN11 j w (hpend j w h).2⟩
      intro j v' h h2 h3 h4
      obtain ⟨hj, h⟩ := hcopy j v' h
      rw [hloc j hj] at h3
      exact El.copyL j v' h h2 h3 h4
    · intro hph
      rw [hloc ℓ (Ne.symm hpℓ)] at hph
      have Co := E.co hph
      have hℓ : (A.upd p l).loc ℓ = A.loc ℓ := hloc ℓ (Ne.symm hpℓ)
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro w h; rw [hℓ] at h ⊢; exact Co.closing w h
      · intro h; rw [hℓ] at h ⊢; exact Co.ca h
      · rw [hℓ]; exact Co.regL
      · intro j v' h h2 h3 h4
        obtain ⟨hj, h⟩ := hcopy j v' h
        rw [hloc j hj] at h3; rw [hℓ]
        exact Co.copyL j v' h h2 h3 h4
      · intro h1 h2 j hj
        rw [hℓ]
        rcases Co.regBot h1 h2 j hj with h | h
        · exact Or.inl h
        · exact Or.inr (hQ j h)
      · intro v' h h1 h2 h3 j hj
        rw [hℓ] at h ⊢
        rcases Co.copyBot v' h h1 h2 h3 j hj with h | h
        · exact Or.inl h
        · exact Or.inr (hQ j h)
      · intro v' h; rw [hℓ] at h; exact Co.copyBotReg v' h
      · intro k w h h1 h2 h3 j hj
        obtain ⟨hk, h⟩ := hpend k w h
        rw [hℓ, hloc k hk]
        exact Co.pendBot k w h h1 h2 h3 j hj
      · intro j hj; rw [hℓ] at hj; exact hQ j (Co.quiet j hj)
      · intro j w h h1; exact Co.n11 j w (hpend j w h).2 h1

end BezoutElection.Alg2
