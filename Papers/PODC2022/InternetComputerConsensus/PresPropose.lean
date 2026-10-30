import Papers.PODC2022.InternetComputerConsensus.Invariants

/-!
# Preservation of the invariant: clause (b) (proposing a block)
-/

namespace Podc.InternetComputerConsensus

open Finset Cslib.Byzantine

set_option linter.unusedSectionVars false

variable {P V : Type*} [Fintype P] [DecidableEq P] {π : Params P} {F : Finset P}

theorem Inv.propose {s : GState P V} (hI : Inv π F s) {p : P} (hp : p ∉ F) (Bp : Block P V)
    (pl : V) (hact : (s.loc p).active = true) (hprop : (s.loc p).proposed = false)
    (hBp : Bp.round + 1 = (s.loc p).round) (hBpn : Notarized (s.loc p).pool Bp) :
    Inv π F (actState s p { s.loc p with proposed := true }
      {Msg.block (.mk (s.loc p).round p Bp pl), Msg.auth (.mk (s.loc p).round p Bp pl),
        Msg.notar Bp}) := by
  set Bn : Block P V := .mk (s.loc p).round p Bp pl with hBn
  set M : Set (Msg P V) := {Msg.block Bn, Msg.auth Bn, Msg.notar Bp} with hM
  have hsub : s.sent ⊆ s.sent ∪ M := Set.subset_union_left
  have hnBp : Bp = .root ∨ NotarCert π F s.sent Bp := by
    rcases hBpn.2 with h | h
    · exact Or.inl h
    · exact hI.pool_avail p hp _ h
  have hMnotar : ∀ B', Msg.notar B' ∈ M → B' = Bp := by
    intro B' h; simpa [hM] using h
  have hMauth : ∀ B', Msg.auth B' ∈ M → B' = Bn := by
    intro B' h; simpa [hM] using h
  have hMfinal : ∀ B', Msg.final B' ∉ M := by intro B' h; simp [hM] at h
  have hMns : ∀ B' q, Msg.notarShare B' q ∉ M := by intro B' q h; simp [hM] at h
  have hMfs : ∀ B' q, Msg.finalShare B' q ∉ M := by intro B' q h; simp [hM] at h
  have hMbeacon : ∀ j q, Msg.beacon j q ∉ M := by intro j q h; simp [hM] at h
  -- no previous authenticator of `p` in this round
  have hfresh : ∀ par' pl', Msg.auth (.mk (s.loc p).round p par' pl') ∉ s.sent := by
    intro par' pl' h
    have := hI.auth_honest _ p par' pl' hp h
    rw [hprop] at this; simp at this
  constructor
  · intro q hq
    by_cases h : q = p
    · subst h; simpa using hI.round_pos q hq
    · simpa [h] using hI.round_pos q hq
  · intro q hq m hm
    by_cases h : q = p
    · subst h
      simp only [actState_loc_self, Set.mem_union] at hm
      rcases hm with hm | hm
      · exact (hI.pool_avail q hq m hm).mono hsub
      · simp only [hM, Set.mem_insert_iff, Set.mem_singleton_iff] at hm
        rcases hm with rfl | rfl | rfl
        · trivial
        · exact Or.inr (Or.inr (by simp [hM]))
        · exact hnBp.imp id (fun h => h.mono hsub)
    · simp only [actState_loc_ne _ _ _ h] at hm
      exact (hI.pool_avail q hq m hm).mono hsub
  · intro B' hB'
    rcases hB' with hB' | hB'
    · exact (hI.sent_notar B' hB').imp id (fun h => h.mono hsub)
    · rw [hMnotar B' hB']; exact hnBp.imp id (fun h => h.mono hsub)
  · intro B' hB'
    rcases hB' with hB' | hB'
    · exact (hI.sent_final B' hB').mono hsub
    · exact absurd hB' (hMfinal B')
  · intro B' hB'
    rcases hB' with hB' | hB'
    · obtain ⟨k, α, par, pl, h1, h2, h3, h4⟩ := hI.sent_auth B' hB'
      exact ⟨k, α, par, pl, h1, h2, hsub h3, hsub h4⟩
    · rw [hMauth B' hB']
      exact ⟨_, p, Bp, pl, rfl, hBp, Or.inr (by simp [hM]), Or.inr (by simp [hM])⟩
  · intro k α par pl' hα hB'
    by_cases h : α = p
    · subst h; simp only [actState_loc_self]
      rcases hB' with hB' | hB'
      · have := hI.auth_honest k α par pl' hα hB'
        rw [hprop] at this; simp at this
        exact Or.inl this
      · have := hMauth _ hB'
        simp only [hBn, Block.mk.injEq] at this
        exact Or.inr ⟨this.1, hact, by simp⟩
    · rcases hB' with hB' | hB'
      · simpa [h] using hI.auth_honest k α par pl' hα hB'
      · have := hMauth _ hB'
        simp only [hBn, Block.mk.injEq] at this
        exact absurd this.2.1 h
  · intro k α par pl₁ par' pl₂ hα h1 h2
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
    · exact hI.auth_unique k α par pl₁ par' pl₂ hα h1 h2
    · have := hMauth _ h2
      simp only [hBn, Block.mk.injEq] at this
      obtain ⟨rfl, rfl, -, -⟩ := this
      exact absurd h1 (hfresh _ _)
    · have := hMauth _ h1
      simp only [hBn, Block.mk.injEq] at this
      obtain ⟨rfl, rfl, -, -⟩ := this
      exact absurd h2 (hfresh _ _)
    · have e1 := hMauth _ h1
      have e2 := hMauth _ h2
      rw [← e1] at e2
      simp only [Block.mk.injEq] at e2
      exact ⟨e2.2.2.1.symm, e2.2.2.2.symm⟩
  · intro q hq h1 h2
    by_cases h : q = p
    · subst h; simp only [actState_loc_self]
      exact ⟨Bp, pl, Or.inr (by simp [hM, hBn])⟩
    · simp only [actState_loc_ne _ _ _ h] at h1 h2 ⊢
      obtain ⟨par, pl, h⟩ := hI.proposed_auth q hq h1 h2
      exact ⟨par, pl, hsub h⟩
  · intro B' q hB'
    rcases hB' with hB' | hB'
    · obtain ⟨h1, h2, h3, h4, h5⟩ := hI.share B' q hB'
      refine ⟨h1, hsub h2, h3, ?_, ?_⟩
      · by_cases h : q = p
        · subst h; simpa using h4
        · simpa [h] using h4
      · by_cases h : q = p
        · subst h; simpa using h5
        · simpa [h] using h5
    · exact absurd hB' (hMns _ _)
  · intro q hq h1 B' hB'
    by_cases h : q = p
    · subst h; simp only [actState_loc_self] at h1 hB' ⊢
      obtain ⟨h2, h3⟩ := hI.N_share q hq h1 B' hB'
      exact ⟨hsub h2, h3⟩
    · simp only [actState_loc_ne _ _ _ h] at h1 hB' ⊢
      obtain ⟨h2, h3⟩ := hI.N_share q hq h1 B' hB'
      exact ⟨hsub h2, h3⟩
  · intro q hq h1 B₁ hB₁ B₂ hB₂
    by_cases h : q = p
    · subst h; simp only [actState_loc_self] at h1 hB₁ hB₂
      exact hI.N_unique q hq h1 B₁ hB₁ B₂ hB₂
    · simp only [actState_loc_ne _ _ _ h] at h1 hB₁ hB₂
      exact hI.N_unique q hq h1 B₁ hB₁ B₂ hB₂
  · intro q hq h1 r hr
    have key : ∀ (h1 : (s.loc q).active = true) (hr : r ∈ (s.loc q).D), ∃ B₁ B₂ : Block P V,
        B₁ ≠ B₂ ∧ B₁.round = (s.loc q).round ∧ B₂.round = (s.loc q).round ∧
        B₁.rk π.rank = r ∧ B₂.rk π.rank = r ∧ Msg.auth B₁ ∈ s.sent ∪ M ∧
        Msg.auth B₂ ∈ s.sent ∪ M := by
      intro h1 hr
      obtain ⟨B₁, B₂, h2, h3, h4, h5, h6, h7, h8⟩ := hI.D_spec q hq h1 r hr
      exact ⟨B₁, B₂, h2, h3, h4, h5, h6, hsub h7, hsub h8⟩
    by_cases h : q = p
    · subst h; simp only [actState_loc_self] at h1 hr ⊢; exact key h1 hr
    · simp only [actState_loc_ne _ _ _ h] at h1 hr ⊢; exact key h1 hr
  · intro B' q hB'
    have hns : ∀ B'', Msg.notarShare B'' q ∈ s.sent ∪ M → Msg.notarShare B'' q ∈ s.sent := by
      intro B'' h; rcases h with h | h
      · exact h
      · exact absurd h (hMns _ _)
    rcases hB' with hB' | hB'
    · obtain ⟨h1, h2, h3⟩ := hI.fshare B' q hB'
      refine ⟨h1, ?_, fun B'' hB'' => h3 B'' (hns B'' hB'')⟩
      by_cases h : q = p
      · subst h; simpa using h2
      · simpa [h] using h2
    · exact absurd hB' (hMfs _ _)
  · intro q hq j h1 h2
    by_cases h : q = p
    · subst h; simp only [actState_loc_self] at h2
      exact hsub (hI.beacon_sent q hq j h1 h2)
    · simp only [actState_loc_ne _ _ _ h] at h2
      exact hsub (hI.beacon_sent q hq j h1 h2)
  · intro q hq h1
    by_cases h : q = p
    · subst h; simp only [actState_loc_self] at h1 ⊢
      exact hsub (hI.beacon_active q hq h1)
    · simp only [actState_loc_ne _ _ _ h] at h1 ⊢
      exact hsub (hI.beacon_active q hq h1)
  · intro q hq i h1 h2
    have h2' : i < (s.loc q).round := by
      by_cases h : q = p
      · subst h; simpa using h2
      · simpa [h] using h2
    obtain ⟨B, hB1, hB2⟩ := hI.finished q hq i h1 h2'
    exact ⟨B, hB1, hsub hB2⟩
  · intro q hq
    obtain ⟨Bq, h1, h2⟩ := hI.parent_ok q hq
    by_cases h : q = p
    · subst h
      exact ⟨Bq, by simpa using h1, h2.mono (by simp)⟩
    · exact ⟨Bq, by simpa [h] using h1, by simpa [h] using h2⟩
  · intro q hq
    by_cases h : q = p
    · subst h
      simp only [actState_loc_self]
      rcases hI.out_ok q hq with h | ⟨B, h1, h2, h3, h4⟩
      · exact Or.inl h
      · exact Or.inr ⟨B, h1, h2.mono Set.subset_union_left, h3.mono hsub, h4⟩
    · simp only [actState_loc_ne _ _ _ h]
      rcases hI.out_ok q hq with h | ⟨B, h1, h2, h3, h4⟩
      · exact Or.inl h
      · exact Or.inr ⟨B, h1, h2, h3.mono hsub, h4⟩
  · intro q hq j hj
    by_cases h : q = p
    · subst h
      simp only [actState_loc_self, actState_now] at hj ⊢
      exact hI.t0_le q hq j hj
    · simp only [actState_loc_ne _ _ _ h, actState_now] at hj ⊢
      exact hI.t0_le q hq j hj
  · intro B' q hB'
    rcases hB' with hB' | hB'
    · exact (hI.fshare_cert B' q hB').mono hsub
    · exact absurd hB' (hMfs _ _)

end Podc.InternetComputerConsensus
