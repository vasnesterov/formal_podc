import Papers.PODC2022.InternetComputerConsensus.Invariants

/-!
# Preservation of the invariant: the Finalization Subprotocol (Figure 2)

The interesting field is `out_ok`: the new output extends the old one. This is the argument of
Section 3.3 ("Property P2 is used as follows"): the round-`kmax` ancestor of the newly finalized
block is notarized, hence equal to the previously finalized block by Property P2.
-/

namespace Podc.InternetComputerConsensus

open Finset Cslib.Byzantine

set_option linter.unusedSectionVars false

variable {P V : Type*} [Fintype P] [DecidableEq P] {π : Params P} {F : Finset P}

theorem Inv.final {s : GState P V} (hI : Inv π F s) (hF : #F ≤ π.t)
    (hn : 3 * π.t < Fintype.card P) {p : P} (hp : p ∉ F) (B : Block P V)
    (hBv : Valid (s.loc p).pool B) (hk : (s.loc p).kmax < B.round)
    (hBf : Msg.final B ∈ (s.loc p).pool ∨ FinalShares π (s.loc p).pool B) :
    Inv π F (actState s p
      { s.loc p with kmax := B.round, out := (s.loc p).out ++ B.chain.drop (s.loc p).kmax }
      {Msg.final B}) := by
  set M : Set (Msg P V) := {Msg.final B} with hM
  have hsub : s.sent ⊆ s.sent ∪ M := Set.subset_union_left
  have hcert : FinalCert π F s.sent B := finalCert_of_pool (hI.pool_avail p hp) hBf
  have hMfinal : ∀ B', Msg.final B' ∈ M → B' = B := by intro B' h; simpa [hM] using h
  have hMnotar : ∀ B', Msg.notar B' ∉ M := by intro B' h; simp [hM] at h
  have hMauth : ∀ B', Msg.auth B' ∉ M := by intro B' h; simp [hM] at h
  have hMns : ∀ B' q, Msg.notarShare B' q ∉ M := by intro B' q h; simp [hM] at h
  have hMfs : ∀ B' q, Msg.finalShare B' q ∉ M := by intro B' q h; simp [hM] at h
  have hMbeacon : ∀ j q, Msg.beacon j q ∉ M := by intro j q h; simp [hM] at h
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
      · rw [Set.mem_singleton_iff.1 hm]; exact hcert.mono hsub
    · simp only [actState_loc_ne _ _ _ h] at hm
      exact (hI.pool_avail q hq m hm).mono hsub
  · intro B' hB'
    rcases hB' with hB' | hB'
    · exact (hI.sent_notar B' hB').imp id (fun h => h.mono hsub)
    · exact absurd hB' (hMnotar B')
  · intro B' hB'
    rcases hB' with hB' | hB'
    · exact (hI.sent_final B' hB').mono hsub
    · rw [hMfinal B' hB']; exact hcert.mono hsub
  · intro B' hB'
    rcases hB' with hB' | hB'
    · obtain ⟨k, α, par, pl, h1, h2, h3, h4⟩ := hI.sent_auth B' hB'
      exact ⟨k, α, par, pl, h1, h2, hsub h3, hsub h4⟩
    · exact absurd hB' (hMauth B')
  · intro k α par pl hα hB'
    rcases hB' with hB' | hB'
    · have := hI.auth_honest k α par pl hα hB'
      by_cases h : α = p
      · subst h; simpa using this
      · simpa [h] using this
    · exact absurd hB' (hMauth _)
  · intro k α par pl par' pl' hα h1 h2
    rcases h1 with h1 | h1
    · rcases h2 with h2 | h2
      · exact hI.auth_unique k α par pl par' pl' hα h1 h2
      · exact absurd h2 (hMauth _)
    · exact absurd h1 (hMauth _)
  · intro q hq h1 h2
    have key : ∀ (h1 : (s.loc q).active = true) (h2 : (s.loc q).proposed = true),
        ∃ par pl, Msg.auth (.mk (s.loc q).round q par pl) ∈ s.sent ∪ M := by
      intro h1 h2
      obtain ⟨par, pl, h⟩ := hI.proposed_auth q hq h1 h2
      exact ⟨par, pl, hsub h⟩
    by_cases h : q = p
    · subst h; simp only [actState_loc_self] at h1 h2 ⊢; exact key h1 h2
    · simp only [actState_loc_ne _ _ _ h] at h1 h2 ⊢; exact key h1 h2
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
    have key : ∀ (h1 : (s.loc q).active = true) (hB' : B' ∈ (s.loc q).N),
        Msg.notarShare B' q ∈ s.sent ∪ M ∧ B'.round = (s.loc q).round := by
      intro h1 hB'
      obtain ⟨h2, h3⟩ := hI.N_share q hq h1 B' hB'
      exact ⟨hsub h2, h3⟩
    by_cases h : q = p
    · subst h; simp only [actState_loc_self] at h1 hB' ⊢; exact key h1 hB'
    · simp only [actState_loc_ne _ _ _ h] at h1 hB' ⊢; exact key h1 hB'
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
      right
      refine ⟨B, rfl, hBv.mono Set.subset_union_left, hcert.mono hsub, ?_⟩
      -- the old output is the chain of the round-`kmax` ancestor of `B`
      obtain ⟨A, hA1, hA2, hA3, hA4⟩ := hBv.chain_take (s.loc q).kmax hk.le
      have hold : (s.loc q).out = A.chain := by
        rcases hI.out_ok q hq with ⟨h0, hout⟩ | ⟨B0, h1, h2, h3, h4⟩
        · rw [hout]
          rw [h0] at hA1
          cases A with
          | root => rfl
          | mk k α par pl => simp at hA1; have := hA2.1; omega
        · rw [h4]
          rcases hA3 with rfl | hA3
          · omega
          rcases Nat.eq_zero_or_pos (s.loc q).kmax with h0 | h0
          · rw [h0] at h1 hA1
            have e : ∀ C : Block P V, Valid (s.loc q).pool C → C.round = 0 → C = .root := by
              intro C hC hC0
              cases C with
              | root => rfl
              | mk k α par pl => simp at hC0; have := hC.1; omega
            rw [e B0 h2 h1, e A hA2 hA1]
          · have hAroot : A ≠ .root := Block.ne_root_of_round (by omega)
            have hAc : NotarCert π F s.sent A :=
              (hI.pool_avail q hq _ (hA3.2.resolve_left hAroot)).resolve_left hAroot
            rw [hI.final_notar_eq hF hn h3 hAc (by omega)]
      rw [hold, ← hA4, List.take_append_drop]
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
