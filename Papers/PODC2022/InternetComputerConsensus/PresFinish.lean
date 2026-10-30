import Papers.PODC2022.InternetComputerConsensus.Invariants

/-!
# Preservation of the invariant: clause (a) (finishing a round)
-/

namespace Podc.InternetComputerConsensus

open Finset Cslib.Byzantine

set_option linter.unusedSectionVars false

variable {P V : Type*} [Fintype P] [DecidableEq P] {π : Params P} {F : Finset P}

theorem Inv.finish {s : GState P V} (hI : Inv π F s) {p : P} (hp : p ∉ F) (B : Block P V)
    (hact : (s.loc p).active = true) (hBr : B.round = (s.loc p).round)
    (hBv : Valid (s.loc p).pool B)
    (hBn : Msg.notar B ∈ (s.loc p).pool ∨ NotarShares π (s.loc p).pool B) :
    Inv π F (actState s p { s.loc p with round := (s.loc p).round + 1, active := false }
      {m | m = Msg.notar B ∨ ((s.loc p).N ⊆ {B} ∧ m = Msg.finalShare B p)}) := by
  set M : Set (Msg P V) := {m | m = Msg.notar B ∨ ((s.loc p).N ⊆ {B} ∧ m = Msg.finalShare B p)}
    with hM
  have hsub : s.sent ⊆ s.sent ∪ M := Set.subset_union_left
  have hr1 := hI.round_pos p hp
  have hBroot : B ≠ .root := Block.ne_root_of_round (by omega)
  have hcert : NotarCert π F s.sent B := notarCert_of_pool (hI.pool_avail p hp) hBroot hBn
  -- messages of `M` by kind
  have hMnotar : ∀ B', Msg.notar B' ∈ M → B' = B := by
    intro B' h; simpa [hM] using h
  have hMfinal : ∀ B', Msg.final B' ∉ M := by intro B' h; simp [hM] at h
  have hMauth : ∀ B', Msg.auth B' ∉ M := by intro B' h; simp [hM] at h
  have hMns : ∀ B' q, Msg.notarShare B' q ∉ M := by intro B' q h; simp [hM] at h
  have hMbeacon : ∀ j q, Msg.beacon j q ∉ M := by intro j q h; simp [hM] at h
  have hMfs : ∀ B' q, Msg.finalShare B' q ∈ M → B' = B ∧ q = p ∧ (s.loc p).N ⊆ {B} := by
    intro B' q h; simp only [hM, Set.mem_ofPred_eq, reduceCtorEq, false_or,
      Msg.finalShare.injEq] at h
    exact ⟨h.2.1, h.2.2, h.1⟩
  constructor
  · intro q hq
    by_cases h : q = p
    · subst h; simp
    · simpa [h] using hI.round_pos q hq
  · intro q hq m hm
    by_cases h : q = p
    · subst h
      simp only [actState_loc_self, Set.mem_union] at hm
      rcases hm with hm | hm
      · exact (hI.pool_avail q hq m hm).mono hsub
      · rcases hm with rfl | ⟨hN, rfl⟩
        · exact Or.inr (hcert.mono hsub)
        · exact Or.inr (Or.inr (Or.inr ⟨hN, rfl⟩))
    · simp only [actState_loc_ne _ _ _ h] at hm
      exact (hI.pool_avail q hq m hm).mono hsub
  · intro B' hB'
    rcases hB' with hB' | hB'
    · exact (hI.sent_notar B' hB').imp id (fun h => h.mono hsub)
    · rw [hMnotar B' hB']; exact Or.inr (hcert.mono hsub)
  · intro B' hB'
    rcases hB' with hB' | hB'
    · exact (hI.sent_final B' hB').mono hsub
    · exact absurd hB' (hMfinal B')
  · intro B' hB'
    rcases hB' with hB' | hB'
    · obtain ⟨k, α, par, pl, h1, h2, h3, h4⟩ := hI.sent_auth B' hB'
      exact ⟨k, α, par, pl, h1, h2, hsub h3, hsub h4⟩
    · exact absurd hB' (hMauth B')
  · intro k α par pl hα hB'
    rcases hB' with hB' | hB'
    · have := hI.auth_honest k α par pl hα hB'
      by_cases h : α = p
      · subst h; simp only [actState_loc_self]; left; omega
      · simpa [h] using this
    · exact absurd hB' (hMauth _)
  · intro k α par pl par' pl' hα h1 h2
    rcases h1 with h1 | h1
    · rcases h2 with h2 | h2
      · exact hI.auth_unique k α par pl par' pl' hα h1 h2
      · exact absurd h2 (hMauth _)
    · exact absurd h1 (hMauth _)
  · intro q hq h1 h2
    by_cases h : q = p
    · subst h; simp at h1
    · simp only [actState_loc_ne _ _ _ h] at h1 h2 ⊢
      obtain ⟨par, pl, h⟩ := hI.proposed_auth q hq h1 h2
      exact ⟨par, pl, hsub h⟩
  · intro B' q hB'
    rcases hB' with hB' | hB'
    · obtain ⟨h1, h2, h3, h4, h5⟩ := hI.share B' q hB'
      refine ⟨h1, hsub h2, h3, ?_, ?_⟩
      · by_cases h : q = p
        · subst h; simp only [actState_loc_self]; left; omega
        · simpa [h] using h4
      · by_cases h : q = p
        · subst h; simpa using h5
        · simpa [h] using h5
    · exact absurd hB' (hMns _ _)
  · intro q hq h1 B' hB'
    by_cases h : q = p
    · subst h; simp at h1
    · simp only [actState_loc_ne _ _ _ h] at h1 hB' ⊢
      obtain ⟨h2, h3⟩ := hI.N_share q hq h1 B' hB'
      exact ⟨hsub h2, h3⟩
  · intro q hq h1 B₁ hB₁ B₂ hB₂
    by_cases h : q = p
    · subst h; simp at h1
    · simp only [actState_loc_ne _ _ _ h] at h1 hB₁ hB₂
      exact hI.N_unique q hq h1 B₁ hB₁ B₂ hB₂
  · intro q hq h1 r hr
    by_cases h : q = p
    · subst h; simp at h1
    · simp only [actState_loc_ne _ _ _ h] at h1 hr ⊢
      obtain ⟨B₁, B₂, h2, h3, h4, h5, h6, h7, h8⟩ := hI.D_spec q hq h1 r hr
      exact ⟨B₁, B₂, h2, h3, h4, h5, h6, hsub h7, hsub h8⟩
  · intro B' q hB'
    have hns : ∀ B'', Msg.notarShare B'' q ∈ s.sent ∪ M → Msg.notarShare B'' q ∈ s.sent := by
      intro B'' h; rcases h with h | h
      · exact h
      · exact absurd h (hMns _ _)
    rcases hB' with hB' | hB'
    · obtain ⟨h1, h2, h3⟩ := hI.fshare B' q hB'
      refine ⟨h1, ?_, fun B'' hB'' => h3 B'' (hns B'' hB'')⟩
      by_cases h : q = p
      · subst h; simp; omega
      · simpa [h] using h2
    · obtain ⟨rfl, rfl, hN⟩ := hMfs B' q hB'
      refine ⟨hp, by simp [hBr], fun B'' hB'' hr => ?_⟩
      obtain ⟨-, -, -, h4, -⟩ := hI.share B'' q (hns B'' hB'')
      rcases h4 with h4 | ⟨-, -, h4⟩
      · omega
      · exact hN h4
  · intro q hq j h1 h2
    by_cases h : q = p
    · subst h; simp only [actState_loc_self] at h2
      rcases Nat.lt_or_ge j ((s.loc q).round + 1) with h3 | h3
      · exact hsub (hI.beacon_sent q hq j h1 (by omega))
      · have : j = (s.loc q).round + 1 := by omega
        subst this; exact hsub (hI.beacon_active q hq hact)
    · simp only [actState_loc_ne _ _ _ h] at h2
      exact hsub (hI.beacon_sent q hq j h1 h2)
  · intro q hq h1
    by_cases h : q = p
    · subst h; simp at h1
    · simp only [actState_loc_ne _ _ _ h] at h1 ⊢
      exact hsub (hI.beacon_active q hq h1)
  · intro q hq i h1 h2
    by_cases h : q = p
    · subst h; simp only [actState_loc_self] at h2
      rcases Nat.lt_or_ge i (s.loc q).round with h3 | h3
      · obtain ⟨B', hB1, hB2⟩ := hI.finished q hq i h1 h3
        exact ⟨B', hB1, hsub hB2⟩
      · exact ⟨B, by omega, Or.inr (Or.inl rfl)⟩
    · simp only [actState_loc_ne _ _ _ h] at h2
      obtain ⟨B', hB1, hB2⟩ := hI.finished q hq i h1 h2
      exact ⟨B', hB1, hsub hB2⟩
  · intro q hq
    by_cases h : q = p
    · subst h
      refine ⟨B, by simp [hBr], ?_⟩
      simp only [actState_loc_self]
      exact ⟨hBv.mono Set.subset_union_left, Or.inr (Or.inr (Or.inl rfl))⟩
    · obtain ⟨Bp, h1, h2⟩ := hI.parent_ok q hq
      exact ⟨Bp, by simpa [h] using h1, by simpa [h] using h2⟩
  · intro q hq
    by_cases h : q = p
    · subst h
      simp only [actState_loc_self]
      rcases hI.out_ok q hq with h | ⟨B', h1, h2, h3, h4⟩
      · exact Or.inl h
      · exact Or.inr ⟨B', h1, h2.mono Set.subset_union_left, h3.mono hsub, h4⟩
    · simp only [actState_loc_ne _ _ _ h]
      rcases hI.out_ok q hq with h | ⟨B', h1, h2, h3, h4⟩
      · exact Or.inl h
      · exact Or.inr ⟨B', h1, h2, h3.mono hsub, h4⟩
  · intro q hq j hj
    by_cases h : q = p
    · subst h
      simp only [actState_loc_self, actState_now] at hj ⊢
      rcases hj with hj | ⟨-, hj⟩
      · rcases Nat.lt_or_ge j (s.loc q).round with h3 | h3
        · exact hI.t0_le q hq j (Or.inl h3)
        · exact hI.t0_le q hq j (Or.inr ⟨by omega, hact⟩)
      · simp at hj
    · simp only [actState_loc_ne _ _ _ h, actState_now] at hj ⊢
      exact hI.t0_le q hq j hj
  · intro B' q hB'
    rcases hB' with hB' | hB'
    · exact (hI.fshare_cert B' q hB').mono hsub
    · obtain ⟨rfl, rfl, -⟩ := hMfs B' q hB'
      exact hcert.mono hsub

end Podc.InternetComputerConsensus
