import Papers.PODC2026.FewToManyFaultsBA.SyncBA.Tokens

/-!
# Evolution of the local fields along a run

Run-level descriptions of the fields of `S π s r p`: one step inside a view (`S_view`), the
fields that never change after the views, monotonicity of the commit (decisions are final), of
the key and lock views, the retrieval input, and validity of held certificates.
-/

namespace Podc.FewToManyFaultsBA.Sync

open Cslib.Byzantine.LockStep Finset

variable {n : ℕ} [NeZero n] {π : Params n} {s : Scenario (Fin n) Bool (Msg n)}

/-- One step inside a view. -/
lemma S_view (r v j : ℕ) (hv : v < n) (hj : j < 11) (hr : r = 11 * v + j) (q : Fin n) :
    S π s (r + 1) q =
      { viewTrans π q (S π s r q) v j (aib π s r q) with
        commit := (viewTrans π q (S π s r q) v j (aib π s r q)).commit.or
          (inboxCommit π.k (aib π s r q))
        last := aib π s r q } := by
  subst hr; rw [S_succ, trans_view _ _ hv hj]

/-! ### Commits only grow -/

lemma phAgg_commit (st : St n) (v j : ℕ) (ib : Fin n → Option (Msg n)) :
    (phAgg π st v j ib).commit = st.commit ∨
      ∃ b, π.k ≤ (checkedToks (.commit b v) ib).card ∧
        (phAgg π st v j ib).commit = st.commit.or (some (b, v, checkedToks (.commit b v) ib)) := by
  unfold phAgg
  split
  · split_ifs <;> simp
  · split_ifs <;> simp
  · rename_i b _ _
    split_ifs with h1 h2
    · exact Or.inr ⟨b, h2, rfl⟩
    · simp
    · simp
  · simp

lemma viewTrans_commit_cases (p : Fin n) (st : St n) (v j : ℕ) (ib : Fin n → Option (Msg n)) :
    (viewTrans π p st v j ib).commit = st.commit ∨
      (∃ c, leaderPlan π v st ib = .bcast c ∧
        (viewTrans π p st v j ib).commit = st.commit.or (some c)) ∨
      (∃ b, π.k ≤ (checkedToks (.commit b v) ib).card ∧
        (viewTrans π p st v j ib).commit = st.commit.or (some (b, v, checkedToks (.commit b v) ib))) := by
  by_cases h1 : j = 1
  · subst h1
    rcases ph1_commit (π := π) st v ib with h | h
    · exact Or.inl (by simpa [viewTrans] using h)
    · exact Or.inr (Or.inl (by simpa [viewTrans] using h))
  by_cases h9 : j = 9
  · subst h9
    rcases phAgg_commit (π := π) st v 9 ib with h | h
    · exact Or.inl (by simpa [viewTrans] using h)
    · exact Or.inr (Or.inr (by simpa [viewTrans] using h))
  · exact Or.inl (viewTrans_commit p st v ib h1 h9)

lemma viewTrans_commit_or (p : Fin n) (st : St n) (v j : ℕ) (ib : Fin n → Option (Msg n)) :
    ∃ o, (viewTrans π p st v j ib).commit = st.commit.or o := by
  rcases viewTrans_commit_cases (π := π) p st v j ib with h | ⟨c, -, h⟩ | ⟨b, -, h⟩
  · exact ⟨none, by simp [h]⟩
  · exact ⟨_, h⟩
  · exact ⟨_, h⟩

lemma trans_commit (p : Fin n) (st : St n) (r : ℕ) (ib : Fin n → Option (Msg n)) :
    (trans π p st r ib).commit =
      (if r < Rh n then (viewTrans π p st (r / 11) (r % 11) ib).commit else st.commit).or
        (if r < R0 n then inboxCommit π.k ib else none) := by
  unfold trans
  split_ifs <;> simp_all

lemma trans_commit_or (p : Fin n) (st : St n) (r : ℕ) (ib : Fin n → Option (Msg n)) :
    ∃ o, (trans π p st r ib).commit = st.commit.or o := by
  rw [trans_commit]
  split_ifs
  · obtain ⟨o, ho⟩ := viewTrans_commit_or (π := π) p st (r / 11) (r % 11) ib
    exact ⟨_, by rw [ho, Option.or_assoc]⟩
  · obtain ⟨o, ho⟩ := viewTrans_commit_or (π := π) p st (r / 11) (r % 11) ib
    exact ⟨_, by rw [ho, Option.or_assoc]⟩
  · exact ⟨_, rfl⟩
  · exact ⟨none, rfl⟩

lemma S_commit_mono {p : Fin n} {r r' : ℕ} (hr : r ≤ r') {c : Proof n}
    (h : (S π s r p).commit = some c) : (S π s r' p).commit = some c := by
  induction r', hr using Nat.le_induction with
  | base => exact h
  | succ r' _ ih =>
    rw [S_succ]
    obtain ⟨o, ho⟩ := trans_commit_or (π := π) p (S π s r' p) r' (aib π s r' p)
    rw [ho, ih, Option.some_or]

lemma S_commit_isSome_mono {p : Fin n} {r r' : ℕ} (hr : r ≤ r')
    (h : (S π s r p).commit.isSome) : (S π s r' p).commit.isSome := by
  obtain ⟨c, hc⟩ := Option.isSome_iff_exists.1 h
  rw [S_commit_mono hr hc]; rfl

/-! ### Validity of held proofs -/

lemma commitOf_valid {k : ℕ} {m : Msg n} {c : Proof n} (h : commitOf k m = some c) :
    Valid n k (.commit c.1 c.2.1) c.2.2 := by
  unfold commitOf at h
  split at h <;> (try split_ifs at h with hv) <;> (try cases h) <;> assumption

lemma inboxCommit_valid {k : ℕ} {ib : Fin n → Option (Msg n)} {c : Proof n}
    (h : inboxCommit k ib = some c) : Valid n k (.commit c.1 c.2.1) c.2.2 := by
  obtain ⟨q, -, hq⟩ := List.exists_of_findSome?_eq_some h
  obtain ⟨m, -, hc⟩ := Option.bind_eq_some_iff.1 hq
  exact commitOf_valid hc

lemma commitSugg_valid {k : ℕ} {m : Option (Msg n)} {c : Proof n} (h : commitSugg k m = some c) :
    Valid n k (.commit c.1 c.2.1) c.2.2 := by
  unfold commitSugg at h
  split at h <;> (try split_ifs at h with hv) <;> (try cases h) <;> assumption

lemma checkedToks_valid {k : ℕ} {σ : Stmt} {ib : Fin n → Option (Msg n)}
    (h : k ≤ (checkedToks σ ib).card) : Valid n k σ (checkedToks σ ib) := by
  refine ⟨fun τ hτ => ?_, h⟩
  simp only [checkedToks, mem_biUnion, mem_univ, true_and] at hτ
  obtain ⟨q, hq⟩ := hτ
  split at hq
  · split_ifs at hq with he
    · simp only [mem_singleton] at hq; subst hq; exact he
    · simp at hq
  · simp at hq

lemma retrToks_valid {th : ℕ} {σ : Stmt} {ib : Fin n → Option (Msg n)}
    (h : th ≤ (retrToks σ ib).card) : Valid n th σ (retrToks σ ib) := by
  refine ⟨fun τ hτ => ?_, h⟩
  simp only [retrToks, mem_biUnion, mem_univ, true_and] at hτ
  obtain ⟨q, hq⟩ := hτ
  split at hq
  · exact (mem_filter.1 hq).2
  · simp at hq

lemma leaderPlan_bcast_valid {v : ℕ} {st : St n} {ib : Fin n → Option (Msg n)} {c : Proof n}
    (hst : ∀ c', st.commit = some c' → Valid n π.k (.commit c'.1 c'.2.1) c'.2.2)
    (h : leaderPlan π v st ib = .bcast c) : Valid n π.k (.commit c.1 c.2.1) c.2.2 := by
  unfold leaderPlan at h
  split at h
  · rename_i c' hc; cases h; exact hst _ hc
  · split at h
    · rename_i c' hc
      cases h
      obtain ⟨q, -, hq⟩ := List.exists_of_findSome?_eq_some hc
      exact commitSugg_valid hq
    · split at h <;> cases h

/-- Every commit held by a party is a valid `k`-certificate. -/
lemma S_commit_valid : ∀ r (p : Fin n) (c : Proof n), (S π s r p).commit = some c →
    Valid n π.k (.commit c.1 c.2.1) c.2.2 := by
  intro r
  induction r with
  | zero => intro p c h; simp [St.init] at h
  | succ r ih =>
    intro p c h
    rw [S_succ, trans_commit] at h
    have hph : ∀ c', (if r < Rh n then
        (viewTrans π p (S π s r p) (r / 11) (r % 11) (aib π s r p)).commit
        else (S π s r p).commit) = some c' → Valid n π.k (.commit c'.1 c'.2.1) c'.2.2 := by
      intro c' hc'
      split_ifs at hc'
      · rcases viewTrans_commit_cases (π := π) p (S π s r p) (r / 11) (r % 11) (aib π s r p)
          with h' | ⟨c₁, hpl, h'⟩ | ⟨b, hk, h'⟩ <;> rw [h'] at hc'
        · exact ih p c' hc'
        all_goals
          rcases hst : (S π s r p).commit with _ | c₀
          · rw [hst, Option.none_or] at hc'
            cases hc'
            first
            | exact leaderPlan_bcast_valid (fun c₂ h₂ => ih p c₂ h₂) hpl
            | exact checkedToks_valid hk
          · rw [hst, Option.some_or] at hc'
            cases hc'; exact ih p _ hst
      · exact ih p c' hc'
    rcases hst : (if r < Rh n then
        (viewTrans π p (S π s r p) (r / 11) (r % 11) (aib π s r p)).commit
        else (S π s r p).commit) with _ | c₀
    · rw [hst, Option.none_or] at h
      split_ifs at h
      exact inboxCommit_valid h
    · rw [hst, Option.some_or] at h
      cases h; exact hph _ hst

/-! ### The other fields of `trans` -/

section TransFields

variable (p : Fin n) (st : St n) (r : ℕ) (ib : Fin n → Option (Msg n))

lemma trans_key : (trans π p st r ib).key =
    if r < Rh n then (viewTrans π p st (r / 11) (r % 11) ib).key else st.key := by
  unfold trans; split_ifs <;> simp_all
lemma trans_lock : (trans π p st r ib).lock =
    if r < Rh n then (viewTrans π p st (r / 11) (r % 11) ib).lock else st.lock := by
  unfold trans; split_ifs <;> simp_all
lemma trans_vin : (trans π p st r ib).vin =
    if r < Rh n then (viewTrans π p st (r / 11) (r % 11) ib).vin else st.vin := by
  unfold trans; split_ifs <;> simp_all
lemma trans_sign : (trans π p st r ib).sign =
    if r < Rh n then (viewTrans π p st (r / 11) (r % 11) ib).sign else st.sign := by
  unfold trans; split_ifs <;> simp_all
lemma trans_active : (trans π p st r ib).active =
    if r < Rh n then (viewTrans π p st (r / 11) (r % 11) ib).active else st.active := by
  unfold trans; split_ifs <;> simp_all
lemma trans_lead : (trans π p st r ib).lead =
    if r < Rh n then (viewTrans π p st (r / 11) (r % 11) ib).lead else st.lead := by
  unfold trans; split_ifs <;> simp_all
lemma trans_plan : (trans π p st r ib).plan =
    if r < Rh n then (viewTrans π p st (r / 11) (r % 11) ib).plan else st.plan := by
  unfold trans; split_ifs <;> simp_all
lemma trans_fb : (trans π p st r ib).fb =
    if r = Rh n + 1 then (ownFb π.t st.last).or (inboxFb π.t ib) else st.fb := by
  unfold trans; split_ifs <;> simp_all [viewTrans_fb]
lemma trans_last : (trans π p st r ib).last = ib := by
  unfold trans; split_ifs <;> simp_all

end TransFields

/-! ### Keys and locks -/

/-- Held keys are valid and were obtained in an earlier view. -/
lemma S_key_valid : ∀ r (p : Fin n) (k : Proof n), (S π s r p).key = some k →
    Valid n π.k (.key k.1 k.2.1) k.2.2 ∧ 11 * k.2.1 + 7 ≤ r := by
  intro r
  induction r with
  | zero => intro p k h; simp [St.init] at h
  | succ r ih =>
    intro p k h
    rw [S_succ, trans_key] at h
    split_ifs at h with hr
    · by_cases h6 : r % 11 = 6
      · rw [h6] at h
        simp only [viewTrans, ph6] at h
        split at h
        · split_ifs at h with hv
          · cases h; exact ⟨hv.2, show 11 * (r / 11) + 7 ≤ r + 1 by omega⟩
          · exact (ih p k h).imp_right (by omega)
        · exact (ih p k h).imp_right (by omega)
      · rw [viewTrans_key _ _ _ _ h6] at h
        exact (ih p k h).imp_right (by omega)
    · exact (ih p k h).imp_right (by omega)

/-- Held locks are valid and were obtained in an earlier view. -/
lemma S_lock_valid : ∀ r (p : Fin n) (k : Proof n), (S π s r p).lock = some k →
    Valid n π.k (.lock k.1 k.2.1) k.2.2 ∧ 11 * k.2.1 + 9 ≤ r := by
  intro r
  induction r with
  | zero => intro p k h; simp [St.init] at h
  | succ r ih =>
    intro p k h
    rw [S_succ, trans_lock] at h
    split_ifs at h with hr
    · by_cases h8 : r % 11 = 8
      · rw [h8] at h
        simp only [viewTrans, ph8] at h
        split at h
        · split_ifs at h with hv
          · cases h; exact ⟨hv.2, show 11 * (r / 11) + 9 ≤ r + 1 by omega⟩
          · exact (ih p k h).imp_right (by omega)
        · exact (ih p k h).imp_right (by omega)
      · rw [viewTrans_lock _ _ _ _ h8] at h
        exact (ih p k h).imp_right (by omega)
    · exact (ih p k h).imp_right (by omega)

/-- Key views never decrease. -/
lemma S_key_mono {p : Fin n} {r r' : ℕ} (hr : r ≤ r') {k : Proof n}
    (h : (S π s r p).key = some k) : ∃ k', (S π s r' p).key = some k' ∧ k.2.1 ≤ k'.2.1 := by
  induction r', hr using Nat.le_induction with
  | base => exact ⟨k, h, le_rfl⟩
  | succ r' hrr ih =>
    obtain ⟨k', hk', hle⟩ := ih
    rw [S_succ, trans_key]
    split_ifs with hr
    · by_cases h6 : r' % 11 = 6
      · rw [h6]
        simp only [viewTrans, ph6]
        split
        · split_ifs
          · refine ⟨_, rfl, ?_⟩
            have := (S_key_valid r' p k' hk').2
            simp only; omega
          · exact ⟨k', hk', hle⟩
        · exact ⟨k', hk', hle⟩
      · rw [viewTrans_key _ _ _ _ h6]; exact ⟨k', hk', hle⟩
    · exact ⟨k', hk', hle⟩

/-- Lock views never decrease. -/
lemma S_lock_mono {p : Fin n} {r r' : ℕ} (hr : r ≤ r') {k : Proof n}
    (h : (S π s r p).lock = some k) : ∃ k', (S π s r' p).lock = some k' ∧ k.2.1 ≤ k'.2.1 := by
  induction r', hr using Nat.le_induction with
  | base => exact ⟨k, h, le_rfl⟩
  | succ r' hrr ih =>
    obtain ⟨k', hk', hle⟩ := ih
    rw [S_succ, trans_lock]
    split_ifs with hr
    · by_cases h8 : r' % 11 = 8
      · rw [h8]
        simp only [viewTrans, ph8]
        split
        · split_ifs
          · refine ⟨_, rfl, ?_⟩
            have := (S_lock_valid r' p k' hk').2
            simp only; omega
          · exact ⟨k', hk', hle⟩
        · exact ⟨k', hk', hle⟩
      · rw [viewTrans_lock _ _ _ _ h8]; exact ⟨k', hk', hle⟩
    · exact ⟨k', hk', hle⟩

/-- A held lock with view `w` was set in view `w` (phase 8) from a valid lock certificate. -/
lemma S_lock_origin : ∀ r (p : Fin n) (k : Proof n), (S π s r p).lock = some k →
    k.2.1 < n ∧ 11 * k.2.1 + 9 ≤ r ∧
      (ph8 π (S π s (11 * k.2.1 + 8) p) k.2.1 (aib π s (11 * k.2.1 + 8) p)).lock = some k := by
  intro r
  induction r with
  | zero => intro p k h; simp [St.init] at h
  | succ r ih =>
    intro p k h
    rw [S_succ, trans_lock] at h
    split_ifs at h with hr
    · by_cases h8 : r % 11 = 8
      · rw [h8] at h
        have hr' : r = 11 * (r / 11) + 8 := by omega
        have hv : r / 11 < n := by unfold Rh at hr; omega
        simp only [viewTrans] at h
        have h0 := h
        unfold ph8 at h
        split at h
        · split_ifs at h with hv'
          · cases h
            refine ⟨hv, show 11 * (r / 11) + 9 ≤ r + 1 by omega, ?_⟩
            show (ph8 π (S π s (11 * (r / 11) + 8) p) (r / 11)
              (aib π s (11 * (r / 11) + 8) p)).lock = _
            rw [← hr']; exact h0
          · exact (ih p k h).imp_right fun h' => ⟨by omega, h'.2⟩
        · exact (ih p k h).imp_right fun h' => ⟨by omega, h'.2⟩
      · rw [viewTrans_lock _ _ _ _ h8] at h
        exact (ih p k h).imp_right fun h' => ⟨by omega, h'.2⟩
    · exact (ih p k h).imp_right fun h' => ⟨by omega, h'.2⟩

/-! ### The retrieval input -/

lemma S_vin : ∀ r (p : Fin n), (S π s r p).vin = some (s.input p) ∨ (S π s r p).vin = none := by
  intro r
  induction r with
  | zero => intro p; simp [St.init]
  | succ r ih =>
    intro p
    rw [S_succ, trans_vin]
    split_ifs with hr
    · by_cases h3 : r % 11 = 3
      · rw [h3]
        simp only [viewTrans, ph3]
        split_ifs <;> simp [ih p]
      · rw [viewTrans_vin _ _ _ _ h3]; exact ih p
    · exact ih p

end Podc.FewToManyFaultsBA.Sync
