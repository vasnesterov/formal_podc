import Papers.PODC2022.InternetComputerConsensus.Invariants

/-!
# Preservation of the invariant: clause (c) (echoing a block)
-/

namespace Podc.InternetComputerConsensus

open Finset Cslib.Byzantine

set_option linter.unusedSectionVars false

variable {P V : Type*} [Fintype P] [DecidableEq P] {π : Params P} {F : Finset P}

/-- The forwarded messages of an echo. -/
def echoFwd (π : Params P) (p : P) (k : ℕ) (B : Block P V) : Set (Msg P V) :=
  {m | B.rk π.rank ≠ π.rank k p ∧ (m = Msg.block B ∨ m = Msg.auth B ∨ m = Msg.notar B.parent)}

/-- When an honest party echoes a valid block of its round, the block's authenticator is
broadcast by an honest party (before or by this echo); if the proposer is honest, it was already
broadcast. -/
theorem Inv.echo_auth {s : GState P V} (hI : Inv π F s)
    (hinj : ∀ k, Function.Injective (π.rank k)) {p : P} (hp : p ∉ F) {B : Block P V}
    (hBr : B.round = (s.loc p).round) (hBv : Valid (s.loc p).pool B) :
    (Msg.auth B ∈ s.sent ∨ Msg.auth B ∈ echoFwd π p (s.loc p).round B) ∧
    (∀ k α par pl, B = .mk k α par pl → α ∉ F → Msg.auth B ∈ s.sent) := by
  cases B with
  | root => have := hI.round_pos p hp; simp at hBr; omega
  | mk k α par pl =>
    have hav := hI.pool_avail p hp _ hBv.2.2.1
    simp only [Avail] at hav
    refine ⟨?_, ?_⟩
    · rcases hav with ⟨k', α', par', pl', he, hα'⟩ | hav
      · simp only [Block.mk.injEq] at he
        obtain ⟨rfl, rfl, rfl, rfl⟩ := he
        right
        refine ⟨?_, Or.inr (Or.inl rfl)⟩
        simp only [Block.rk_mk]
        intro h
        simp only [Block.round_mk] at hBr
        subst hBr
        exact hp (hinj _ h ▸ hα')
      · exact Or.inl hav
    · rintro k' α' par' pl' he hα
      rcases hav with ⟨k'', α'', par'', pl'', he', hα''⟩ | hav
      · rw [he] at he'
        simp only [Block.mk.injEq] at he he'
        exact absurd (he'.2.1 ▸ hα'') hα
      · exact hav

theorem Inv.echoShare {s : GState P V} (hI : Inv π F s)
    (hinj : ∀ k, Function.Injective (π.rank k)) {p : P} (hp : p ∉ F) (B : Block P V)
    (hact : (s.loc p).active = true) (hBr : B.round = (s.loc p).round)
    (hBv : Valid (s.loc p).pool B) (hBN : B ∉ (s.loc p).N)
    (htime : (s.loc p).t0 (s.loc p).round + π.Δntry (B.rk π.rank) ≤ s.now)
    (hnorank : ¬ ∃ B' ∈ (s.loc p).N, B'.rk π.rank = B.rk π.rank) :
    Inv π F (actState s p { s.loc p with N := insert B (s.loc p).N }
      {m | (B.rk π.rank ≠ π.rank (s.loc p).round p ∧
              (m = Msg.block B ∨ m = Msg.auth B ∨ m = Msg.notar B.parent)) ∨
            m = Msg.notarShare B p}) := by
  set M : Set (Msg P V) := {m | (B.rk π.rank ≠ π.rank (s.loc p).round p ∧
              (m = Msg.block B ∨ m = Msg.auth B ∨ m = Msg.notar B.parent)) ∨
            m = Msg.notarShare B p} with hM
  have hsub : s.sent ⊆ s.sent ∪ M := Set.subset_union_left
  have hr1 := hI.round_pos p hp
  obtain ⟨hauth1, hauth2⟩ := hI.echo_auth hinj hp hBr hBv
  have hauth : Msg.auth B ∈ s.sent ∪ M := by
    rcases hauth1 with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  have hpar := hBv.parent_notarized (by omega)
  have hnpar : B.parent = .root ∨ NotarCert π F s.sent B.parent := by
    rcases hpar.1.2 with h | h
    · exact Or.inl h
    · exact hI.pool_avail p hp _ h
  have hMnotar : ∀ B', Msg.notar B' ∈ M → B' = B.parent := by
    intro B' h; simp [hM] at h; exact h.2
  have hMauth : ∀ B', Msg.auth B' ∈ M → B' = B := by
    intro B' h; simp [hM] at h; exact h.2
  have hMblock : ∀ B', Msg.block B' ∈ M → B' = B := by
    intro B' h; simp [hM] at h; exact h.2
  have hMfinal : ∀ B', Msg.final B' ∉ M := by intro B' h; simp [hM] at h
  have hMns : ∀ B' q, Msg.notarShare B' q ∈ M → B' = B ∧ q = p := by
    intro B' q h; simpa [hM] using h
  have hMfs : ∀ B' q, Msg.finalShare B' q ∉ M := by intro B' q h; simp [hM] at h
  have hMbeacon : ∀ j q, Msg.beacon j q ∉ M := by intro j q h; simp [hM] at h
  -- the authenticators in `s.sent ∪ M` of honest proposers are old
  have hauth_old : ∀ k α par pl, α ∉ F → Msg.auth (.mk k α par pl) ∈ s.sent ∪ M →
      Msg.auth (.mk k α par pl) ∈ s.sent := by
    intro k α par pl hα h
    rcases h with h | h
    · exact h
    · have := hMauth _ h
      rw [this]; exact hauth2 k α par pl this.symm hα
  have hBsent : Msg.notarShare B p ∈ s.sent ∪ M := Or.inr (Or.inr rfl)
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
      · rcases hm with ⟨-, rfl | rfl | rfl⟩ | rfl
        · trivial
        · exact Or.inr hauth
        · exact hnpar.imp id (fun h => h.mono hsub)
        · exact Or.inr hBsent
    · simp only [actState_loc_ne _ _ _ h] at hm
      exact (hI.pool_avail q hq m hm).mono hsub
  · intro B' hB'
    rcases hB' with hB' | hB'
    · exact (hI.sent_notar B' hB').imp id (fun h => h.mono hsub)
    · rw [hMnotar B' hB']; exact hnpar.imp id (fun h => h.mono hsub)
  · intro B' hB'
    rcases hB' with hB' | hB'
    · exact (hI.sent_final B' hB').mono hsub
    · exact absurd hB' (hMfinal B')
  · intro B' hB'
    rcases hB' with hB' | hB'
    · obtain ⟨k, α, par, pl, h1, h2, h3, h4⟩ := hI.sent_auth B' hB'
      exact ⟨k, α, par, pl, h1, h2, hsub h3, hsub h4⟩
    · have e := hMauth B' hB'
      subst e
      have hc : B'.rk π.rank ≠ π.rank (s.loc p).round p := by simp [hM] at hB'; exact hB'
      cases B' with
      | root => simp at hBr; omega
      | mk k α par pl =>
        exact ⟨k, α, par, pl, rfl, hBv.1, Or.inr (Or.inl ⟨hc, Or.inl rfl⟩),
          Or.inr (Or.inl ⟨hc, Or.inr (Or.inr rfl)⟩)⟩
  · intro k α par pl hα hB'
    have := hI.auth_honest k α par pl hα (hauth_old k α par pl hα hB')
    by_cases h : α = p
    · subst h; simpa using this
    · simpa [h] using this
  · intro k α par pl par' pl' hα h1 h2
    exact hI.auth_unique k α par pl par' pl' hα (hauth_old _ _ _ _ hα h1)
      (hauth_old _ _ _ _ hα h2)
  · intro q hq h1 h2
    by_cases h : q = p
    · subst h; simp only [actState_loc_self] at h1 h2 ⊢
      obtain ⟨par, pl, h⟩ := hI.proposed_auth q hq h1 h2
      exact ⟨par, pl, hsub h⟩
    · simp only [actState_loc_ne _ _ _ h] at h1 h2 ⊢
      obtain ⟨par, pl, h⟩ := hI.proposed_auth q hq h1 h2
      exact ⟨par, pl, hsub h⟩
  · intro B' q hB'
    rcases hB' with hB' | hB'
    · obtain ⟨h1, h2, h3, h4, h5⟩ := hI.share B' q hB'
      refine ⟨h1, hsub h2, h3, ?_, ?_⟩
      · by_cases h : q = p
        · subst h; simp only [actState_loc_self]
          rcases h4 with h4 | ⟨h4, h4', h4''⟩
          · exact Or.inl h4
          · exact Or.inr ⟨h4, h4', Set.mem_insert_of_mem _ h4''⟩
        · simpa [h] using h4
      · by_cases h : q = p
        · subst h; simpa using h5
        · simpa [h] using h5
    · obtain ⟨rfl, rfl⟩ := hMns B' q hB'
      refine ⟨hp, hauth, by omega, ?_, ?_⟩
      · simp only [actState_loc_self]
        exact Or.inr ⟨hBr, hact, Set.mem_insert _ _⟩
      · simp only [actState_loc_self, actState_now]; rw [hBr]; exact htime
  · intro q hq h1 B' hB'
    by_cases h : q = p
    · subst h; simp only [actState_loc_self, Set.mem_insert_iff] at h1 hB' ⊢
      rcases hB' with rfl | hB'
      · exact ⟨hBsent, hBr⟩
      · obtain ⟨h2, h3⟩ := hI.N_share q hq h1 B' hB'
        exact ⟨hsub h2, h3⟩
    · simp only [actState_loc_ne _ _ _ h] at h1 hB' ⊢
      obtain ⟨h2, h3⟩ := hI.N_share q hq h1 B' hB'
      exact ⟨hsub h2, h3⟩
  · intro q hq h1 B₁ hB₁ B₂ hB₂ hrk
    by_cases h : q = p
    · subst h; simp only [actState_loc_self, Set.mem_insert_iff] at h1 hB₁ hB₂
      rcases hB₁ with rfl | hB₁ <;> rcases hB₂ with rfl | hB₂
      · rfl
      · exact absurd ⟨B₂, hB₂, hrk.symm⟩ hnorank
      · exact absurd ⟨B₁, hB₁, hrk⟩ hnorank
      · exact hI.N_unique q hq h1 B₁ hB₁ B₂ hB₂ hrk
    · simp only [actState_loc_ne _ _ _ h] at h1 hB₁ hB₂
      exact hI.N_unique q hq h1 B₁ hB₁ B₂ hB₂ hrk
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
    rcases hB' with hB' | hB'
    · obtain ⟨h1, h2, h3⟩ := hI.fshare B' q hB'
      refine ⟨h1, ?_, fun B'' hB'' hr => ?_⟩
      · by_cases h : q = p
        · subst h; simpa using h2
        · simpa [h] using h2
      · rcases hB'' with hB'' | hB''
        · exact h3 B'' hB'' hr
        · obtain ⟨rfl, rfl⟩ := hMns B'' q hB''
          omega
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

theorem Inv.echoDisq {s : GState P V} (hI : Inv π F s)
    (hinj : ∀ k, Function.Injective (π.rank k)) {p : P} (hp : p ∉ F) (B : Block P V)
    (hact : (s.loc p).active = true) (hBr : B.round = (s.loc p).round)
    (hBv : Valid (s.loc p).pool B) (hBN : B ∉ (s.loc p).N)
    (htime : (s.loc p).t0 (s.loc p).round + π.Δntry (B.rk π.rank) ≤ s.now)
    (hrank : ∃ B' ∈ (s.loc p).N, B'.rk π.rank = B.rk π.rank) :
    Inv π F (actState s p { s.loc p with D := insert (B.rk π.rank) (s.loc p).D }
      {m | B.rk π.rank ≠ π.rank (s.loc p).round p ∧
              (m = Msg.block B ∨ m = Msg.auth B ∨ m = Msg.notar B.parent)}) := by
  set M : Set (Msg P V) := {m | B.rk π.rank ≠ π.rank (s.loc p).round p ∧
              (m = Msg.block B ∨ m = Msg.auth B ∨ m = Msg.notar B.parent)} with hM
  have hsub : s.sent ⊆ s.sent ∪ M := Set.subset_union_left
  have hr1 := hI.round_pos p hp
  obtain ⟨hauth1, hauth2⟩ := hI.echo_auth hinj hp hBr hBv
  have hauth : Msg.auth B ∈ s.sent ∪ M := by
    rcases hauth1 with h | h
    · exact Or.inl h
    · exact Or.inr h
  have hpar := hBv.parent_notarized (by omega)
  have hnpar : B.parent = .root ∨ NotarCert π F s.sent B.parent := by
    rcases hpar.1.2 with h | h
    · exact Or.inl h
    · exact hI.pool_avail p hp _ h
  have hMnotar : ∀ B', Msg.notar B' ∈ M → B' = B.parent := by
    intro B' h; simp [hM] at h; exact h.2
  have hMauth : ∀ B', Msg.auth B' ∈ M → B' = B := by
    intro B' h; simp [hM] at h; exact h.2
  have hMblock : ∀ B', Msg.block B' ∈ M → B' = B := by
    intro B' h; simp [hM] at h; exact h.2
  have hMfinal : ∀ B', Msg.final B' ∉ M := by intro B' h; simp [hM] at h
  have hMns : ∀ B' q, Msg.notarShare B' q ∉ M := by intro B' q h; simp [hM] at h
  have hMfs : ∀ B' q, Msg.finalShare B' q ∉ M := by intro B' q h; simp [hM] at h
  have hMbeacon : ∀ j q, Msg.beacon j q ∉ M := by intro j q h; simp [hM] at h
  -- the authenticators in `s.sent ∪ M` of honest proposers are old
  have hauth_old : ∀ k α par pl, α ∉ F → Msg.auth (.mk k α par pl) ∈ s.sent ∪ M →
      Msg.auth (.mk k α par pl) ∈ s.sent := by
    intro k α par pl hα h
    rcases h with h | h
    · exact h
    · have := hMauth _ h
      rw [this]; exact hauth2 k α par pl this.symm hα
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
      · rcases hm with ⟨-, rfl | rfl | rfl⟩
        · trivial
        · exact Or.inr hauth
        · exact hnpar.imp id (fun h => h.mono hsub)
    · simp only [actState_loc_ne _ _ _ h] at hm
      exact (hI.pool_avail q hq m hm).mono hsub
  · intro B' hB'
    rcases hB' with hB' | hB'
    · exact (hI.sent_notar B' hB').imp id (fun h => h.mono hsub)
    · rw [hMnotar B' hB']; exact hnpar.imp id (fun h => h.mono hsub)
  · intro B' hB'
    rcases hB' with hB' | hB'
    · exact (hI.sent_final B' hB').mono hsub
    · exact absurd hB' (hMfinal B')
  · intro B' hB'
    rcases hB' with hB' | hB'
    · obtain ⟨k, α, par, pl, h1, h2, h3, h4⟩ := hI.sent_auth B' hB'
      exact ⟨k, α, par, pl, h1, h2, hsub h3, hsub h4⟩
    · have e := hMauth B' hB'
      subst e
      have hc : B'.rk π.rank ≠ π.rank (s.loc p).round p := by simp [hM] at hB'; exact hB'
      cases B' with
      | root => simp at hBr; omega
      | mk k α par pl =>
        exact ⟨k, α, par, pl, rfl, hBv.1, Or.inr ⟨hc, Or.inl rfl⟩,
          Or.inr ⟨hc, Or.inr (Or.inr rfl)⟩⟩
  · intro k α par pl hα hB'
    have := hI.auth_honest k α par pl hα (hauth_old k α par pl hα hB')
    by_cases h : α = p
    · subst h; simpa using this
    · simpa [h] using this
  · intro k α par pl par' pl' hα h1 h2
    exact hI.auth_unique k α par pl par' pl' hα (hauth_old _ _ _ _ hα h1)
      (hauth_old _ _ _ _ hα h2)
  · intro q hq h1 h2
    by_cases h : q = p
    · subst h; simp only [actState_loc_self] at h1 h2 ⊢
      obtain ⟨par, pl, h⟩ := hI.proposed_auth q hq h1 h2
      exact ⟨par, pl, hsub h⟩
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
    · subst h; simp only [actState_loc_self, Set.mem_insert_iff] at h1 hr ⊢
      rcases hr with rfl | hr
      · obtain ⟨B', hB'N, hB'r⟩ := hrank
        obtain ⟨hs, hround⟩ := hI.N_share q hq h1 B' hB'N
        refine ⟨B', B, fun e => hBN (e ▸ hB'N), hround, hBr, hB'r, rfl,
          hsub (hI.share B' q hs).2.1, hauth⟩
      · exact key h1 hr
    · simp only [actState_loc_ne _ _ _ h] at h1 hr ⊢; exact key h1 hr
  · intro B' q hB'
    rcases hB' with hB' | hB'
    · obtain ⟨h1, h2, h3⟩ := hI.fshare B' q hB'
      refine ⟨h1, ?_, fun B'' hB'' hr => ?_⟩
      · by_cases h : q = p
        · subst h; simpa using h2
        · simpa [h] using h2
      · rcases hB'' with hB'' | hB''
        · exact h3 B'' hB'' hr
        · exact absurd hB'' (hMns _ _)
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
