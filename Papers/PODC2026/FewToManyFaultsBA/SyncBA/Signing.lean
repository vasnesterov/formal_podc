import Papers.PODC2026.FewToManyFaultsBA.SyncBA.Fields

/-!
# When does an honest party sign?

Characterisation of `Signed` for each kind of statement (the conditions of `ViewPartyProtocol`,
`RetrievalPartySync` and `HELP`), and the counting lemma: a valid `th`-certificate held by an
honest party has at least `th - f` honest signers.
-/

namespace Podc.FewToManyFaultsBA.Sync

open Cslib.Byzantine.LockStep Finset

variable {n : ℕ} [NeZero n] {π : Params n} {s : Scenario (Fin n) Bool (Msg n)}

/-! ### Fields at the signing rounds -/

lemma S_sign5 {w : ℕ} (hw : w < n) (q : Fin n) :
    (S π s (11 * w + 5) q).sign =
      keySign π (S π s (11 * w + 4) q) w (aib π s (11 * w + 4) q (leader w)) := by
  rw [show 11 * w + 5 = 11 * w + 4 + 1 by omega, S_view (11 * w + 4) w 4 hw (by norm_num) rfl]
  simp [viewTrans, ph4]

lemma S_sign7 {w : ℕ} (hw : w < n) (q : Fin n) :
    (S π s (11 * w + 7) q).sign =
      (ph6 π (S π s (11 * w + 6) q) w (aib π s (11 * w + 6) q)).sign := by
  rw [show 11 * w + 7 = 11 * w + 6 + 1 by omega, S_view (11 * w + 6) w 6 hw (by norm_num) rfl]
  simp [viewTrans]

lemma S_sign9 {w : ℕ} (hw : w < n) (q : Fin n) :
    (S π s (11 * w + 9) q).sign =
      (ph8 π (S π s (11 * w + 8) q) w (aib π s (11 * w + 8) q)).sign := by
  rw [show 11 * w + 9 = 11 * w + 8 + 1 by omega, S_view (11 * w + 8) w 8 hw (by norm_num) rfl]
  simp [viewTrans]

lemma S_key7 {w : ℕ} (hw : w < n) (q : Fin n) :
    (S π s (11 * w + 7) q).key =
      (ph6 π (S π s (11 * w + 6) q) w (aib π s (11 * w + 6) q)).key := by
  rw [show 11 * w + 7 = 11 * w + 6 + 1 by omega, S_view (11 * w + 6) w 6 hw (by norm_num) rfl]
  simp [viewTrans]

lemma S_lock9 {w : ℕ} (hw : w < n) (q : Fin n) :
    (S π s (11 * w + 9) q).lock =
      (ph8 π (S π s (11 * w + 8) q) w (aib π s (11 * w + 8) q)).lock := by
  rw [show 11 * w + 9 = 11 * w + 8 + 1 by omega, S_view (11 * w + 8) w 8 hw (by norm_num) rfl]
  simp [viewTrans]

/-- Activity is fixed in phase 1 for the rest of the view. -/
lemma S_active {w j : ℕ} (hw : w < n) (hj1 : 2 ≤ j) (hj2 : j ≤ 11) (q : Fin n) :
    (S π s (11 * w + j) q).active = (S π s (11 * w + 1) q).commit.isNone := by
  induction j, hj1 using Nat.le_induction with
  | base =>
    rw [show 11 * w + 2 = 11 * w + 1 + 1 by omega, S_view (11 * w + 1) w 1 hw (by norm_num) rfl]
    simp only [viewTrans]
    unfold ph1; split_ifs <;> (try split) <;> rfl
  | succ j hj ih =>
    rw [show 11 * w + (j + 1) = 11 * w + j + 1 by omega,
      S_view (11 * w + j) w j hw (by omega) rfl]
    simp only
    rw [viewTrans_active _ _ _ _ (by omega)]
    exact ih (by omega)

/-! ### Shapes of the signing decisions -/

lemma keySign_spec {st : St n} {w : ℕ} {m : Option (Msg n)} {σ : Stmt}
    (h : keySign π st w m = some σ) : ∃ b J, proposalOf m = some (b, J) ∧ st.active = true ∧
      J.valid π b w ∧ lockOK st.lock J = true ∧ σ = .key b w := by
  unfold keySign at h
  split at h
  · rename_i b J hJ
    split_ifs at h with hc
    cases h
    exact ⟨b, J, hJ, hc.1, hc.2.1, hc.2.2, rfl⟩
  · cases h

lemma ph6_sign_spec {st : St n} {w : ℕ} {ib : Fin n → Option (Msg n)} {σ : Stmt}
    (h : (ph6 π st w ib).sign = some σ) : ∃ b c, proposeLockOf (ib (leader w)) = some (b, c) ∧
      st.active = true ∧ Valid n π.k (.key b w) c ∧ σ = .lock b w ∧
      (ph6 π st w ib).key = some (b, w, c) := by
  unfold ph6 at h ⊢
  split at h
  · rename_i b c hc
    split_ifs at h ⊢ with hv
    · cases h; exact ⟨b, c, hc, hv.1, hv.2, rfl, by simp [hc, hv]⟩
  · cases h

lemma ph8_sign_spec {st : St n} {w : ℕ} {ib : Fin n → Option (Msg n)} {σ : Stmt}
    (h : (ph8 π st w ib).sign = some σ) : ∃ b c, proposeCommitOf (ib (leader w)) = some (b, c) ∧
      st.active = true ∧ Valid n π.k (.lock b w) c ∧ σ = .commit b w ∧
      (ph8 π st w ib).lock = some (b, w, c) := by
  unfold ph8 at h ⊢
  split at h
  · rename_i b c hc
    split_ifs at h ⊢ with hv
    · cases h; exact ⟨b, c, hc, hv.1, hv.2, rfl, by simp [hc, hv]⟩
  · cases h

/-- The fresh tokens of a party. -/
lemma ownToks_cases {q : Fin n} {r : ℕ} {σ : Stmt} (h : (q, σ) ∈ ownToks q (S π s r q) r) :
    (r < Rh n ∧ r % 11 = 3 ∧ (S π s r q).active = true ∧
      isRunRetr ((S π s r q).last (leader (r / 11))) = true ∧
      ∃ b, σ = .inp b ∧ ((S π s r q).vin = some b ∨ (S π s r q).vin = none)) ∨
    (r < Rh n ∧ (r % 11 = 5 ∨ r % 11 = 7 ∨ r % 11 = 9) ∧ (S π s r q).active = true ∧
      (S π s r q).sign = some σ) ∨
    (r = Rh n ∧ σ = .help ∧ (S π s r q).commit = none) := by
  unfold ownToks at h
  split_ifs at h with h1 h2 h3 h4
  · left
    refine ⟨h1, h2.1, h2.2.1, h2.2.2, ?_⟩
    unfold retrAnswer at h
    split at h
    · rename_i b hb; simp at h; exact ⟨b, h, Or.inl hb⟩
    · rename_i hb; simp at h; rcases h with h | h <;> exact ⟨_, h, Or.inr hb⟩
  · right; left
    refine ⟨h1, h3.1, h3.2, ?_⟩
    rcases hs : (S π s r q).sign with _ | σ' <;> simp [hs] at h
    rw [h]
  · simp at h
  · right; right
    simp only [mem_singleton, Prod.mk.injEq, true_and] at h
    exact ⟨h4.1, h, by simpa using h4.2⟩
  · simp at h

/-! ### `Signed` for each statement -/

/-- Signing `CheckedKey`: in phase 5 of view `v`, after the check of phase 4. -/
lemma signed_key {q : Fin n} {b : Bool} {v r : ℕ} (h : Signed π s q (.key b v) r) :
    v < n ∧ 11 * v + 5 < r ∧
      keySign π (S π s (11 * v + 4) q) v (aib π s (11 * v + 4) q (leader v)) =
        some (.key b v) := by
  obtain ⟨r', hr', hm⟩ := h
  rcases ownToks_cases hm with ⟨-, -, -, -, b', hb', -⟩ | ⟨hRh, hj, -, hs⟩ | ⟨-, hσ, -⟩
  · cases hb'
  · have hw : r' / 11 < n := by unfold Rh at hRh; omega
    rcases hj with hj | hj | hj
    · have hr : r' = 11 * (r' / 11) + 5 := by omega
      rw [hr, S_sign5 hw] at hs
      obtain ⟨b'', J, -, -, -, -, he⟩ := keySign_spec hs
      cases he
      refine ⟨hw, by omega, ?_⟩
      rw [← hs]
    · have hr : r' = 11 * (r' / 11) + 7 := by omega
      rw [hr, S_sign7 hw] at hs
      obtain ⟨_, _, _, _, _, he, _⟩ := ph6_sign_spec hs
      cases he
    · have hr : r' = 11 * (r' / 11) + 9 := by omega
      rw [hr, S_sign9 hw] at hs
      obtain ⟨_, _, _, _, _, he, _⟩ := ph8_sign_spec hs
      cases he
  · cases hσ

/-- Signing `CheckedLock`: in phase 7 of view `v`, after accepting `ProposeLock` with a valid key
certificate in phase 6 (and updating the key). -/
lemma signed_lock {q : Fin n} {b : Bool} {v r : ℕ} (h : Signed π s q (.lock b v) r) :
    v < n ∧ 11 * v + 7 < r ∧ ∃ c, proposeLockOf (aib π s (11 * v + 6) q (leader v)) = some (b, c) ∧
      (S π s (11 * v + 6) q).active = true ∧ Valid n π.k (.key b v) c ∧
      (S π s (11 * v + 7) q).key = some (b, v, c) := by
  obtain ⟨r', hr', hm⟩ := h
  rcases ownToks_cases hm with ⟨-, -, -, -, b', hb', -⟩ | ⟨hRh, hj, -, hs⟩ | ⟨-, hσ, -⟩
  · cases hb'
  · have hw : r' / 11 < n := by unfold Rh at hRh; omega
    rcases hj with hj | hj | hj
    · have hr : r' = 11 * (r' / 11) + 5 := by omega
      rw [hr, S_sign5 hw] at hs
      obtain ⟨_, _, _, _, _, _, he⟩ := keySign_spec hs
      cases he
    · have hr : r' = 11 * (r' / 11) + 7 := by omega
      rw [hr, S_sign7 hw] at hs
      obtain ⟨b'', c, hc, ha, hv, he, hk⟩ := ph6_sign_spec hs
      cases he
      refine ⟨hw, by omega, c, hc, ha, hv, ?_⟩
      rw [S_key7 hw]; exact hk
    · have hr : r' = 11 * (r' / 11) + 9 := by omega
      rw [hr, S_sign9 hw] at hs
      obtain ⟨_, _, _, _, _, he, _⟩ := ph8_sign_spec hs
      cases he
  · cases hσ

/-- Signing `CheckedCommit`: in phase 9 of view `v`, after accepting `ProposeCommit` with a valid
lock certificate in phase 8 (and updating the lock). -/
lemma signed_commit {q : Fin n} {b : Bool} {v r : ℕ} (h : Signed π s q (.commit b v) r) :
    v < n ∧ 11 * v + 9 < r ∧
      ∃ c, proposeCommitOf (aib π s (11 * v + 8) q (leader v)) = some (b, c) ∧
      (S π s (11 * v + 8) q).active = true ∧ Valid n π.k (.lock b v) c ∧
      (S π s (11 * v + 9) q).lock = some (b, v, c) := by
  obtain ⟨r', hr', hm⟩ := h
  rcases ownToks_cases hm with ⟨-, -, -, -, b', hb', -⟩ | ⟨hRh, hj, -, hs⟩ | ⟨-, hσ, -⟩
  · cases hb'
  · have hw : r' / 11 < n := by unfold Rh at hRh; omega
    rcases hj with hj | hj | hj
    · have hr : r' = 11 * (r' / 11) + 5 := by omega
      rw [hr, S_sign5 hw] at hs
      obtain ⟨_, _, _, _, _, _, he⟩ := keySign_spec hs
      cases he
    · have hr : r' = 11 * (r' / 11) + 7 := by omega
      rw [hr, S_sign7 hw] at hs
      obtain ⟨_, _, _, _, _, he, _⟩ := ph6_sign_spec hs
      cases he
    · have hr : r' = 11 * (r' / 11) + 9 := by omega
      rw [hr, S_sign9 hw] at hs
      obtain ⟨b'', c, hc, ha, hv, he, hk⟩ := ph8_sign_spec hs
      cases he
      refine ⟨hw, by omega, c, hc, ha, hv, ?_⟩
      rw [S_lock9 hw]; exact hk
  · cases hσ

/-- Signing a retrieval input. -/
lemma signed_inp {q : Fin n} {b : Bool} {r : ℕ} (h : Signed π s q (.inp b) r) :
    ∃ r' < r, r' < Rh n ∧ ((S π s r' q).vin = some b ∨ (S π s r' q).vin = none) := by
  obtain ⟨r', hr', hm⟩ := h
  rcases ownToks_cases hm with ⟨hRh, -, -, -, b', hb', hv⟩ | ⟨hRh, hj, -, hs⟩ | ⟨-, hσ, -⟩
  · cases hb'; exact ⟨r', hr', hRh, hv⟩
  · have hw : r' / 11 < n := by unfold Rh at hRh; omega
    rcases hj with hj | hj | hj
    · have hr : r' = 11 * (r' / 11) + 5 := by omega
      rw [hr, S_sign5 hw] at hs
      obtain ⟨_, _, _, _, _, _, he⟩ := keySign_spec hs
      cases he
    · have hr : r' = 11 * (r' / 11) + 7 := by omega
      rw [hr, S_sign7 hw] at hs
      obtain ⟨_, _, _, _, _, he, _⟩ := ph6_sign_spec hs
      cases he
    · have hr : r' = 11 * (r' / 11) + 9 := by omega
      rw [hr, S_sign9 hw] at hs
      obtain ⟨_, _, _, _, _, he, _⟩ := ph8_sign_spec hs
      cases he
  · cases hσ

/-- Signing `HELP`: only in round `11n`, without a commit. -/
lemma signed_help {q : Fin n} {r : ℕ} (h : Signed π s q .help r) :
    Rh n < r ∧ (S π s (Rh n) q).commit = none := by
  obtain ⟨r', hr', hm⟩ := h
  rcases ownToks_cases hm with ⟨-, -, -, -, b', hb', -⟩ | ⟨hRh, hj, -, hs⟩ | ⟨hr, -, hc⟩
  · cases hb'
  · have hw : r' / 11 < n := by unfold Rh at hRh; omega
    rcases hj with hj | hj | hj
    · have hr : r' = 11 * (r' / 11) + 5 := by omega
      rw [hr, S_sign5 hw] at hs
      obtain ⟨_, _, _, _, _, _, he⟩ := keySign_spec hs
      cases he
    · have hr : r' = 11 * (r' / 11) + 7 := by omega
      rw [hr, S_sign7 hw] at hs
      obtain ⟨_, _, _, _, _, he, _⟩ := ph6_sign_spec hs
      cases he
    · have hr : r' = 11 * (r' / 11) + 9 := by omega
      rw [hr, S_sign9 hw] at hs
      obtain ⟨_, _, _, _, _, he, _⟩ := ph8_sign_spec hs
      cases he
  · subst hr; exact ⟨hr', hc⟩

/-- An honest party signs at most one value per kind of statement and view. -/
lemma signed_key_unique {q : Fin n} {b b' : Bool} {v r r' : ℕ} (h : Signed π s q (.key b v) r)
    (h' : Signed π s q (.key b' v) r') : b = b' := by
  have := (signed_key h).2.2
  rw [(signed_key h').2.2] at this
  cases this; rfl

lemma signed_lock_unique {q : Fin n} {b b' : Bool} {v r r' : ℕ} (h : Signed π s q (.lock b v) r)
    (h' : Signed π s q (.lock b' v) r') : b = b' := by
  obtain ⟨-, -, c, -, -, -, hk⟩ := signed_lock h
  obtain ⟨-, -, c', -, -, -, hk'⟩ := signed_lock h'
  rw [hk] at hk'; cases hk'; rfl

lemma signed_commit_unique {q : Fin n} {b b' : Bool} {v r r' : ℕ}
    (h : Signed π s q (.commit b v) r) (h' : Signed π s q (.commit b' v) r') : b = b' := by
  obtain ⟨-, -, c, -, -, -, hk⟩ := signed_commit h
  obtain ⟨-, -, c', -, -, -, hk'⟩ := signed_commit h'
  rw [hk] at hk'; cases hk'; rfl

/-! ### Counting honest signers -/

variable (π s)

/-- The Byzantine parties, as a finset. -/
noncomputable def byzF : Finset (Fin n) := by
  classical exact univ.filter (· ∈ s.byz)

/-- The honest parties that produced their partial signature on `σ` before round `r`. -/
noncomputable def signers (σ : Stmt) (r : ℕ) : Finset (Fin n) := by
  classical exact univ.filter fun q => q ∉ s.byz ∧ Signed π s q σ r

variable {π s}

lemma mem_byzF {q : Fin n} : q ∈ byzF s ↔ q ∈ s.byz := by
  classical simp [byzF]

lemma mem_signers {σ : Stmt} {r : ℕ} {q : Fin n} :
    q ∈ signers π s σ r ↔ q ∉ s.byz ∧ Signed π s q σ r := by
  classical simp [signers]

lemma signers_mono {σ : Stmt} {r r' : ℕ} (h : r ≤ r') : signers π s σ r ⊆ signers π s σ r' := by
  intro q hq
  rw [mem_signers] at hq ⊢
  exact ⟨hq.1, hq.2.mono h⟩

/-- **Certificates have honest signers.** A valid `th`-certificate on `σ` held by an honest party
after `r` rounds has at least `th - f` honest signers who signed `σ` before round `r`. -/
lemma card_signers_of_valid (hrel : s.Reliable) (hA : s.AuthValid (G n) (stageA π) auth)
    {r : ℕ} {p : Fin n} (hp : p ∉ s.byz) {th : ℕ} {σ : Stmt} {c : Cert n}
    (hv : Valid n th σ c) (hc : ∀ τ ∈ c, τ ∈ (S π s r p).toks) :
    th ≤ (signers π s σ r).card + (byzF s).card := by
  classical
  have hinj : (c.image Prod.fst).card = c.card := by
    apply card_image_of_injOn
    intro x hx y hy hxy
    have := hv.1 x hx; have := hv.1 y hy
    exact Prod.ext hxy (by simp_all)
  have hsub : c.image Prod.fst ⊆ signers π s σ r ∪ byzF s := by
    intro q hq
    obtain ⟨τ, hτ, rfl⟩ := mem_image.1 hq
    rcases toks_signed hrel hA r p hp τ (hc τ hτ) with h | h
    · exact mem_union_right _ (mem_byzF.2 h)
    · by_cases hb : τ.1 ∈ s.byz
      · exact mem_union_right _ (mem_byzF.2 hb)
      · rw [hv.1 τ hτ] at h
        exact mem_union_left _ (mem_signers.2 ⟨hb, h⟩)
  calc th ≤ c.card := hv.2
    _ = (c.image Prod.fst).card := hinj.symm
    _ ≤ (signers π s σ r ∪ byzF s).card := card_le_card hsub
    _ ≤ _ := card_union_le _ _

end Podc.FewToManyFaultsBA.Sync
