import Papers.PODC2022.InternetComputerConsensus.Invariants

/-!
# Preservation of the invariant: the beacon clause
-/

namespace Podc.InternetComputerConsensus

open Finset Cslib.Byzantine

set_option linter.unusedSectionVars false

variable {P V : Type*} [Fintype P] [DecidableEq P] {π : Params P} {F : Finset P}

theorem Inv.beacon {s : GState P V} (hI : Inv π F s) {p : P} (hp : p ∉ F)
    (hact : (s.loc p).active = false) :
    Inv π F (actState s p ((s.loc p).start s.now) {Msg.beacon ((s.loc p).round + 1) p}) := by
  have hsub : s.sent ⊆ s.sent ∪ {Msg.beacon ((s.loc p).round + 1) p} := Set.subset_union_left
  constructor
  · intro q hq
    by_cases h : q = p
    · subst h; simpa [LState.start] using hI.round_pos q hq
    · simpa [h] using hI.round_pos q hq
  · intro q hq m hm
    by_cases h : q = p
    · subst h
      simp only [actState_loc_self, LState.start, Set.mem_union, Set.mem_singleton_iff] at hm
      rcases hm with hm | rfl
      · exact (hI.pool_avail q hq m hm).mono hsub
      · exact Or.inr (by simp)
    · simp only [actState_loc_ne _ _ _ h] at hm
      exact (hI.pool_avail q hq m hm).mono hsub
  · intro B hB
    simp only [actState_sent, Set.mem_union, Set.mem_singleton_iff, reduceCtorEq, or_false] at hB
    exact (hI.sent_notar B hB).imp id (fun h => h.mono hsub)
  · intro B hB
    simp only [actState_sent, Set.mem_union, Set.mem_singleton_iff, reduceCtorEq, or_false] at hB
    exact (hI.sent_final B hB).mono hsub
  · intro B hB
    simp only [actState_sent, Set.mem_union, Set.mem_singleton_iff, reduceCtorEq, or_false] at hB
    obtain ⟨k, α, par, pl, h1, h2, h3, h4⟩ := hI.sent_auth B hB
    exact ⟨k, α, par, pl, h1, h2, hsub h3, hsub h4⟩
  · intro k α par pl hα hB
    simp only [actState_sent, Set.mem_union, Set.mem_singleton_iff, reduceCtorEq, or_false] at hB
    have := hI.auth_honest k α par pl hα hB
    by_cases h : α = p
    · subst h; simp only [actState_loc_self, LState.start]
      rw [hact] at this
      simp at this
      exact Or.inl this
    · simpa [h] using this
  · intro k α par pl par' pl' hα h1 h2
    simp only [actState_sent, Set.mem_union, Set.mem_singleton_iff, reduceCtorEq, or_false] at h1 h2
    exact hI.auth_unique k α par pl par' pl' hα h1 h2
  · intro q hq h1 h2
    by_cases h : q = p
    · subst h; simp [LState.start] at h2
    · simp only [actState_loc_ne _ _ _ h] at h1 h2 ⊢
      obtain ⟨par, pl, h⟩ := hI.proposed_auth q hq h1 h2
      exact ⟨par, pl, hsub h⟩
  · intro B q hB
    simp only [actState_sent, Set.mem_union, Set.mem_singleton_iff, reduceCtorEq, or_false] at hB
    obtain ⟨h1, h2, h3, h4, h5⟩ := hI.share B q hB
    refine ⟨h1, hsub h2, h3, ?_, ?_⟩
    · by_cases h : q = p
      · subst h; simp only [actState_loc_self, LState.start]
        rw [hact] at h4; simp at h4; exact Or.inl h4
      · simpa [h] using h4
    · by_cases h : q = p
      · subst h; simp only [actState_loc_self, LState.start, actState_now]
        rw [hact] at h4; simp only [Bool.false_eq_true, false_and, and_false, or_false] at h4
        rwa [Function.update_of_ne (by omega)]
      · simpa [h] using h5
  · intro q hq h1 B hB
    by_cases h : q = p
    · subst h; simp [LState.start] at hB
    · simp only [actState_loc_ne _ _ _ h] at h1 hB ⊢
      obtain ⟨h2, h3⟩ := hI.N_share q hq h1 B hB
      exact ⟨hsub h2, h3⟩
  · intro q hq h1 B₁ hB₁ B₂ hB₂
    by_cases h : q = p
    · subst h; simp [LState.start] at hB₁
    · simp only [actState_loc_ne _ _ _ h] at h1 hB₁ hB₂
      exact hI.N_unique q hq h1 B₁ hB₁ B₂ hB₂
  · intro q hq h1 r hr
    by_cases h : q = p
    · subst h; simp [LState.start] at hr
    · simp only [actState_loc_ne _ _ _ h] at h1 hr ⊢
      obtain ⟨B₁, B₂, h2, h3, h4, h5, h6, h7, h8⟩ := hI.D_spec q hq h1 r hr
      exact ⟨B₁, B₂, h2, h3, h4, h5, h6, hsub h7, hsub h8⟩
  · intro B q hB
    simp only [actState_sent, Set.mem_union, Set.mem_singleton_iff, reduceCtorEq, or_false] at hB
    obtain ⟨h1, h2, h3⟩ := hI.fshare B q hB
    refine ⟨h1, ?_, fun B' hB' => ?_⟩
    · by_cases h : q = p
      · subst h; simpa [LState.start] using h2
      · simpa [h] using h2
    · simp only [actState_sent, Set.mem_union, Set.mem_singleton_iff, reduceCtorEq,
        or_false] at hB'
      exact h3 B' hB'
  · intro q hq j h1 h2
    by_cases h : q = p
    · subst h; simp only [actState_loc_self, LState.start] at h2
      exact hsub (hI.beacon_sent q hq j h1 h2)
    · simp only [actState_loc_ne _ _ _ h] at h2
      exact hsub (hI.beacon_sent q hq j h1 h2)
  · intro q hq h1
    by_cases h : q = p
    · subst h; simp [LState.start]
    · simp only [actState_loc_ne _ _ _ h] at h1 ⊢
      exact hsub (hI.beacon_active q hq h1)
  · intro q hq i h1 h2
    have h2' : i < (s.loc q).round := by
      by_cases h : q = p
      · subst h; simpa [LState.start] using h2
      · simpa [h] using h2
    obtain ⟨B, hB1, hB2⟩ := hI.finished q hq i h1 h2'
    exact ⟨B, hB1, hsub hB2⟩
  · intro q hq
    obtain ⟨Bp, h1, h2⟩ := hI.parent_ok q hq
    by_cases h : q = p
    · subst h
      exact ⟨Bp, by simpa [LState.start] using h1, h2.mono (by simp [LState.start])⟩
    · exact ⟨Bp, by simpa [h] using h1, by simpa [h] using h2⟩
  · intro q hq
    by_cases h : q = p
    · subst h
      simp only [actState_loc_self, LState.start]
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
      simp only [actState_loc_self, LState.start, actState_now] at hj ⊢
      rcases hj with hj | ⟨rfl, -⟩
      · rw [Function.update_of_ne (by omega)]
        exact hI.t0_le q hq j (Or.inl hj)
      · simp
    · simp only [actState_loc_ne _ _ _ h, actState_now] at hj ⊢
      exact hI.t0_le q hq j hj
  · intro B q hB
    simp only [actState_sent, Set.mem_union, Set.mem_singleton_iff, reduceCtorEq, or_false] at hB
    exact (hI.fshare_cert B q hB).mono hsub

end Podc.InternetComputerConsensus
