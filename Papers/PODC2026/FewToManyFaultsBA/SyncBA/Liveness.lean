import Papers.PODC2026.FewToManyFaultsBA.SyncBA.Validity

/-!
# Liveness of a view with an honest leader (Lemma B.6)

If `f ≤ n - k` and the leader `L` of view `v < n` is honest, then at the end of the view every
honest party has a commit, unless `L` ran the retrieval and it failed (`view_outcome`).
-/

namespace Podc.FewToManyFaultsBA.Sync

open Cslib.Byzantine.LockStep Finset

variable {n : ℕ} [NeZero n] {π : Params n} {s : Scenario (Fin n) Bool (Msg n)}

/-! ### Generic helpers -/

lemma view_lt_R0 {v j : ℕ} (hv : v < n) (hj : j < 11) : 11 * v + j < R0 n := by
  have := view_lt_Rh (n := n) hv hj; unfold R0; unfold Rh at this; omega

lemma S_plan_succ {v j : ℕ} (hv : v < n) (hj : j < 11) (q : Fin n) :
    (S π s (11 * v + j + 1) q).plan =
      (viewTrans π q (S π s (11 * v + j) q) v j (aib π s (11 * v + j) q)).plan := by
  rw [S_view (11 * v + j) v j hv hj rfl]

lemma S_sign_succ {v j : ℕ} (hv : v < n) (hj : j < 11) (q : Fin n) :
    (S π s (11 * v + j + 1) q).sign =
      (viewTrans π q (S π s (11 * v + j) q) v j (aib π s (11 * v + j) q)).sign := by
  rw [S_view (11 * v + j) v j hv hj rfl]

lemma inboxCommit_isSome {k : ℕ} {ib : Fin n → Option (Msg n)} {q : Fin n} {m : Msg n}
    {c : Proof n} (hm : ib q = some m) (hc : commitOf k m = some c) :
    (inboxCommit k ib).isSome := by
  unfold inboxCommit
  rcases h : (List.finRange n).findSome? (fun q => (ib q).bind (commitOf k)) with _ | c'
  · have := List.findSome?_eq_none_iff.1 h q (List.mem_finRange q)
    simp [hm, hc] at this
  · rfl

/-- Receiving a valid commit in round `r < R₀` gives a commit. -/
lemma commit_of_recv {r : ℕ} (hr : r < R0 n) {p q : Fin n} {m : Msg n} {c : Proof n}
    (hm : aib π s r p q = some m) (hc : commitOf π.k m = some c) :
    (S π s (r + 1) p).commit.isSome := by
  rw [S_succ, trans_commit, if_pos hr]
  have := inboxCommit_isSome hm hc
  rcases (if r < Rh n then (viewTrans π p (S π s r p) (r / 11) (r % 11) (aib π s r p)).commit
    else (S π s r p).commit) with _ | c' <;> simp_all

lemma commitOf_sendCommit {pm : Option (PMsg n)} {c : Proof n}
    (hv : Valid n π.k (.commit c.1 c.2.1) c.2.2) :
    commitOf π.k (.view pm (some (.sendCommit c))) = some c := by
  simp [commitOf, hv]

/-! ### Phase 0–1: complaints and suggestions -/

lemma leaderPlan_of_commitSugg {v : ℕ} {st : St n} {ib : Fin n → Option (Msg n)} {q : Fin n}
    {c : Proof n} (h : commitSugg π.k (ib q) = some c) : ∃ c', leaderPlan π v st ib = .bcast c' := by
  unfold leaderPlan
  split
  · exact ⟨_, rfl⟩
  · split
    · exact ⟨_, rfl⟩
    · rename_i hn
      have := List.findSome?_eq_none_iff.1 hn q (List.mem_finRange q)
      rw [h] at this; cases this

lemma view_plan_preserved {v j : ℕ} (hv : v < n) (hj : j = 2 ∨ j = 4 ∨ j = 6 ∨ j = 8)
    (q : Fin n) : (S π s (11 * v + j + 1) q).plan = (S π s (11 * v + j) q).plan := by
  rw [S_plan_succ hv (by omega)]
  rcases hj with rfl | rfl | rfl | rfl
  · rfl
  · rfl
  · simp only [viewTrans, ph6]; split <;> (try split_ifs) <;> rfl
  · simp only [viewTrans, ph8]; split <;> (try split_ifs) <;> rfl

lemma keySugg_spec {k v : ℕ} {m : Option (Msg n)} {c : Proof n} (h : keySugg k v m = some c) :
    c.2.1 < v ∧ Valid n k (.key c.1 c.2.1) c.2.2 := by
  unfold keySugg at h
  split at h
  · split_ifs at h with hc; cases h; exact hc
  · cases h

lemma leaderPlan_cases (v : ℕ) (st : St n) (ib : Fin n → Option (Msg n)) :
    (∃ c, leaderPlan π v st ib = .bcast c) ∨
    (∃ c, bestKey π.k v ib = some c ∧ leaderPlan π v st ib = .propose c.1 (.key c.2.1 c.2.2)) ∨
    (bestKey π.k v ib = none ∧ leaderPlan π v st ib = .retr) := by
  unfold leaderPlan
  split
  · exact Or.inl ⟨_, rfl⟩
  · split
    · exact Or.inl ⟨_, rfl⟩
    · split
      · rename_i c hc; exact Or.inr (Or.inl ⟨c, hc, rfl⟩)
      · rename_i hc; exact Or.inr (Or.inr ⟨hc, rfl⟩)

lemma S_vin_none_mono {p : Fin n} {r r' : ℕ} (hr : r ≤ r') (h : (S π s r p).vin = none) :
    (S π s r' p).vin = none := by
  induction r', hr using Nat.le_induction with
  | base => exact h
  | succ r' _ ih =>
    rw [S_succ, trans_vin]
    split_ifs
    · by_cases h3 : r' % 11 = 3
      · rw [h3]; simp only [viewTrans, ph3]; split_ifs <;> simp [ih]
      · rw [viewTrans_vin _ _ _ _ h3]; exact ih
    · exact ih

variable (hg : Good π s)
include hg

/-- An honest leader's `SendCommit` with a valid commit gives every honest party a commit. -/
lemma commit_of_sendCommit {v j : ℕ} (hv : v < n) (hj : j < 11) (hL : leader v ∉ s.byz)
    {q : Fin n} (hq : q ∉ s.byz) {c : Proof n}
    (hlo : leaderOut (S π s (11 * v + j) (leader v)) j q = some (.sendCommit c))
    (hval : Valid n π.k (.commit c.1 c.2.1) c.2.2) :
    (S π s (11 * v + j + 1) q).commit.isSome := by
  obtain ⟨pm, hpm⟩ := out_leader (π := π) hv hj hlo
  exact commit_of_recv (view_lt_R0 hv hj)
    (by rw [aib_honest hg.rel (view_lt_R0 hv hj) q hL]; exact hpm) (commitOf_sendCommit hval)

/-- The honest leader's message reaches every honest party. -/
lemma recv_leader {v j : ℕ} (hv : v < n) (hj : j < 11) (hL : leader v ∉ s.byz) (q : Fin n)
    {lm : LMsg n} (hlo : leaderOut (S π s (11 * v + j) (leader v)) j q = some lm) :
    ∃ pm, aib π s (11 * v + j) q (leader v) = some (.view pm (some lm)) := by
  obtain ⟨pm, hpm⟩ := out_leader (π := π) hv hj hlo
  exact ⟨pm, by rw [aib_honest hg.rel (view_lt_R0 hv hj) q hL]; exact hpm⟩

/-- An honest party's party-role message reaches the leader. -/
lemma recv_party {v j : ℕ} (hv : v < n) (hj : j < 11) {q : Fin n} (hq : q ∉ s.byz)
    {pm : PMsg n} (hpo : partyOut q (S π s (11 * v + j) q) v j = some pm) :
    ∃ lm, aib π s (11 * v + j) (leader v) q = some (.view (some pm) lm) := by
  obtain ⟨lm, hm⟩ := out_party (π := π) hv hj hpo
  exact ⟨lm, by rw [aib_honest hg.rel (view_lt_R0 hv hj) (leader v) hq]; exact hm⟩

lemma commit_mono_isSome {p : Fin n} {r r' : ℕ} (hr : r ≤ r')
    (h : (S π s r p).commit.isSome) : (S π s r' p).commit.isSome :=
  S_commit_isSome_mono hr h


/-- With an honest leader without commit, every honest party sends its suggestion. -/
lemma honest_sugg {v : ℕ} (hv : v < n) (hL : leader v ∉ s.byz)
    (hc : (S π s (11 * v) (leader v)).commit = none) {q : Fin n} (hq : q ∉ s.byz) :
    partyOut q (S π s (11 * v + 1) q) v 1 = some (.sugg (suggOf (S π s (11 * v + 1) q))) := by
  have hreq : isReqSugg ((S π s (11 * v + 1) q).last (leader v)) = true := by
    have hlo : leaderOut (S π s (11 * v + 0) (leader v)) 0 q = some .reqSugg := by
      simp [leaderOut, hc]
    obtain ⟨pm, hpm⟩ := recv_leader hg hv (by norm_num) hL q hlo
    simp only [Nat.add_zero] at hpm
    rw [S_last, hpm]; rfl
  simp only [partyOut, one_ne_zero, ite_false, ite_true, hreq]

/-- If the leader does not broadcast a commit in phase 2, no honest party had a commit in
phase 1. -/
lemma no_commit_of_not_bcast {v : ℕ} (hv : v < n) (hL : leader v ∉ s.byz)
    (hc : (S π s (11 * v) (leader v)).commit = none)
    (hpl : ∀ c, leaderPlan π v (S π s (11 * v + 1) (leader v)) (aib π s (11 * v + 1) (leader v)) ≠
      .bcast c) {q : Fin n} (hq : q ∉ s.byz) : (S π s (11 * v + 1) q).commit = none := by
  rcases hcq : (S π s (11 * v + 1) q).commit with _ | c
  · rfl
  exfalso
  have hpo := honest_sugg hg hv hL hc hq
  simp only [suggOf, hcq] at hpo
  obtain ⟨lm, hm⟩ := recv_party hg hv (by norm_num) hq hpo
  have hval := S_commit_valid (π := π) (s := s) _ q c hcq
  have hcs : commitSugg π.k (aib π s (11 * v + 1) (leader v) q) = some c := by
    rw [hm]; simp [commitSugg, hval]
  obtain ⟨c', hc'⟩ := leaderPlan_of_commitSugg (v := v)
    (st := S π s (11 * v + 1) (leader v)) hcs
  exact hpl c' hc'

/-- **The lock check passes** (the core of Lemma B.6): if an honest party holds a lock in view
`v`, the honest leader received a valid key suggestion with at least that view. -/
lemma bestKey_of_lock {v : ℕ} (hv : v < n) (hL : leader v ∉ s.byz)
    (hc : (S π s (11 * v) (leader v)).commit = none)
    (hnc : ∀ q, q ∉ s.byz → (S π s (11 * v + 1) q).commit = none)
    {q : Fin n} (hq : q ∉ s.byz) {l : Proof n} (hl : (S π s (11 * v + 4) q).lock = some l) :
    ∃ c, bestKey π.k v (aib π s (11 * v + 1) (leader v)) = some c ∧ l.2.1 ≤ c.2.1 := by
  have hlv := (S_lock_valid (π := π) (s := s) _ q l hl).2
  obtain ⟨q', hq', hs⟩ := exists_signer hg (sup_of_lock hg hq hl) (t_lt_k hg)
  obtain ⟨-, -, c₀, -, -, -, hkey⟩ := signed_lock hs
  obtain ⟨k', hk', hle⟩ := S_key_mono (show 11 * l.2.1 + 7 ≤ 11 * v + 1 by omega) hkey
  have hpo := honest_sugg hg hv hL hc hq'
  simp only [suggOf, hnc q' hq', hk'] at hpo
  obtain ⟨lm, hm⟩ := recv_party hg hv (by norm_num) hq' hpo
  obtain ⟨hkval, hkr⟩ := S_key_valid (π := π) (s := s) _ q' k' hk'
  have hks : keySugg π.k v (aib π s (11 * v + 1) (leader v) q') = some k' := by
    rw [hm]; simp [keySugg, hkval, show k'.2.1 < v by omega]
  have hmem : k' ∈ keyCands π.k v (aib π s (11 * v + 1) (leader v)) := mem_keyCands.2 ⟨q', hks⟩
  rcases hb : bestKey π.k v (aib π s (11 * v + 1) (leader v)) with _ | c
  · rw [bestKey_none hb] at hmem; simp at hmem
  · refine ⟨c, rfl, ?_⟩
    have := (bestKey_spec hb).2 k' hmem
    simp only at hle; omega

lemma card_honest_add : s.honestFinset.card + (byzF s).card = n := by
  classical
  have hd : Disjoint s.honestFinset (byzF s) := by
    rw [Finset.disjoint_left]; intro q hq hb
    exact ((Scenario.mem_honestFinset _).1 hq) (mem_byzF.1 hb)
  have h1 : s.honestFinset ∪ byzF s = univ := by
    ext q; by_cases hq : q ∈ s.byz <;> simp [byzF, hq]
  rw [← card_union_of_disjoint hd, h1, card_univ, Fintype.card_fin]

/-- **Collecting partial signatures**: if every honest party signs `σ` in phase `j ∈ {5,7,9}`,
the honest leader gets at least `k` of them (when `f + k ≤ n`). -/
lemma collect (hfk : (byzF s).card + π.k ≤ n) {v j : ℕ} (hv : v < n) (hj : j = 5 ∨ j = 7 ∨ j = 9)
    {σ : Stmt} (hall : ∀ q, q ∉ s.byz → (S π s (11 * v + j) q).active = true ∧
      (S π s (11 * v + j) q).sign = some σ) :
    π.k ≤ (checkedToks σ (aib π s (11 * v + j) (leader v))).card := by
  have hmem : ∀ q, q ∉ s.byz → (q, σ) ∈ checkedToks σ (aib π s (11 * v + j) (leader v)) := by
    intro q hq
    obtain ⟨ha, hs⟩ := hall q hq
    have hpo : partyOut q (S π s (11 * v + j) q) v j = some (.checked (q, σ)) := by
      have h0 : j ≠ 0 := by omega
      have h1 : j ≠ 1 := by omega
      have h3 : j ≠ 3 := by omega
      simp [partyOut, h0, h1, h3, hj, hs, ha]
    obtain ⟨lm, hm⟩ := recv_party hg hv (by omega) hq hpo
    simp only [checkedToks, mem_biUnion, mem_univ, true_and]
    exact ⟨q, by rw [hm]; simp⟩
  have hsub : s.honestFinset.image (fun q => (q, σ)) ⊆
      checkedToks σ (aib π s (11 * v + j) (leader v)) := by
    intro τ hτ
    obtain ⟨q, hq, rfl⟩ := mem_image.1 hτ
    exact hmem q ((Scenario.mem_honestFinset _).1 hq)
  have hcard := card_le_card hsub
  rw [card_image_of_injective _ (fun a b h => by simpa using h)] at hcard
  have := card_honest_add hg
  omega

/-- **The four phases succeed**: an honest leader that proposes a valid key in phase 4, accepted
by every honest party's lock check, obtains a commit that every honest party receives by the end
of the view. -/
theorem propose_success (hfk : (byzF s).card + π.k ≤ n) {v : ℕ} (hv : v < n)
    (hL : leader v ∉ s.byz) (hlead : (S π s (11 * v + 1) (leader v)).lead = true)
    (hnc : ∀ q, q ∉ s.byz → (S π s (11 * v + 1) q).commit = none)
    {b : Bool} {J : Justif n} (hplan : (S π s (11 * v + 4) (leader v)).plan = .propose b J)
    (hJ : J.valid π b v) (hok : ∀ q, q ∉ s.byz → lockOK (S π s (11 * v + 4) q).lock J = true) :
    ∀ q, q ∉ s.byz → (S π s (11 * v + 11) q).commit.isSome := by
  have hld : ∀ j, 1 ≤ j → j ≤ 11 → (S π s (11 * v + j) (leader v)).lead = true :=
    fun j h1 h2 => by rw [S_lead hv h1 h2]; exact hlead
  have hact : ∀ j, 2 ≤ j → j ≤ 11 → ∀ q, q ∉ s.byz → (S π s (11 * v + j) q).active = true :=
    fun j h1 h2 q hq => by rw [S_active hv h1 h2, hnc q hq]; rfl
  -- phase 4/5: every honest party signs the key
  have hs5 : ∀ q, q ∉ s.byz → (S π s (11 * v + 5) q).active = true ∧
      (S π s (11 * v + 5) q).sign = some (.key b v) := by
    intro q hq
    refine ⟨hact 5 (by norm_num) (by norm_num) q hq, ?_⟩
    rw [S_sign5 hv]
    have hlo : leaderOut (S π s (11 * v + 4) (leader v)) 4 q = some (.proposeKey b J) := by
      simp [leaderOut, hplan]
    obtain ⟨pm, hpm⟩ := recv_leader hg hv (by norm_num) hL q hlo
    rw [hpm]
    simp [keySign, proposalOf, hact 4 (by norm_num) (by norm_num) q hq, hJ, hok q hq]
  have hc5 := collect hg hfk hv (j := 5) (by norm_num) hs5
  have hp5 : (S π s (11 * v + 5) (leader v)).plan = .propose b J := by
    rw [view_plan_preserved hv (j := 4) (by norm_num)]; exact hplan
  have hp6 : (S π s (11 * v + 6) (leader v)).plan =
      .keyC b (checkedToks (.key b v) (aib π s (11 * v + 5) (leader v))) := by
    rw [S_plan_succ hv (j := 5) (by norm_num)]
    simp [viewTrans, phAgg, hp5, hld 5 (by norm_num) (by norm_num), hc5]
  -- phase 6/7: every honest party signs the lock
  have hs7 : ∀ q, q ∉ s.byz → (S π s (11 * v + 7) q).active = true ∧
      (S π s (11 * v + 7) q).sign = some (.lock b v) := by
    intro q hq
    refine ⟨hact 7 (by norm_num) (by norm_num) q hq, ?_⟩
    rw [S_sign7 hv]
    have hlo : leaderOut (S π s (11 * v + 6) (leader v)) 6 q =
        some (.proposeLock b (checkedToks (.key b v) (aib π s (11 * v + 5) (leader v)))) := by
      simp [leaderOut, hp6]
    obtain ⟨pm, hpm⟩ := recv_leader hg hv (by norm_num) hL q hlo
    simp [ph6, proposeLockOf, hpm, hact 6 (by norm_num) (by norm_num) q hq,
      checkedToks_valid hc5]
  have hc7 := collect hg hfk hv (j := 7) (by norm_num) hs7
  have hp7 : (S π s (11 * v + 7) (leader v)).plan =
      .keyC b (checkedToks (.key b v) (aib π s (11 * v + 5) (leader v))) := by
    rw [view_plan_preserved hv (j := 6) (by norm_num)]; exact hp6
  have hp8 : (S π s (11 * v + 8) (leader v)).plan =
      .lockC b (checkedToks (.lock b v) (aib π s (11 * v + 7) (leader v))) := by
    rw [S_plan_succ hv (j := 7) (by norm_num)]
    simp [viewTrans, phAgg, hp7, hld 7 (by norm_num) (by norm_num), hc7]
  -- phase 8/9: every honest party signs the commit
  have hs9 : ∀ q, q ∉ s.byz → (S π s (11 * v + 9) q).active = true ∧
      (S π s (11 * v + 9) q).sign = some (.commit b v) := by
    intro q hq
    refine ⟨hact 9 (by norm_num) (by norm_num) q hq, ?_⟩
    rw [S_sign9 hv]
    have hlo : leaderOut (S π s (11 * v + 8) (leader v)) 8 q =
        some (.proposeCommit b (checkedToks (.lock b v) (aib π s (11 * v + 7) (leader v)))) := by
      simp [leaderOut, hp8]
    obtain ⟨pm, hpm⟩ := recv_leader hg hv (by norm_num) hL q hlo
    simp [ph8, proposeCommitOf, hpm, hact 8 (by norm_num) (by norm_num) q hq,
      checkedToks_valid hc7]
  have hc9 := collect hg hfk hv (j := 9) (by norm_num) hs9
  have hp9 : (S π s (11 * v + 9) (leader v)).plan =
      .lockC b (checkedToks (.lock b v) (aib π s (11 * v + 7) (leader v))) := by
    rw [view_plan_preserved hv (j := 8) (by norm_num)]; exact hp8
  have hp10 : (S π s (11 * v + 10) (leader v)).plan =
      .fin (b, v, checkedToks (.commit b v) (aib π s (11 * v + 9) (leader v))) := by
    rw [S_plan_succ hv (j := 9) (by norm_num)]
    simp [viewTrans, phAgg, hp9, hld 9 (by norm_num) (by norm_num), hc9]
  -- phase 10: the commit is broadcast
  intro q hq
  have hlo : leaderOut (S π s (11 * v + 10) (leader v)) 10 q =
      some (.sendCommit (b, v, checkedToks (.commit b v) (aib π s (11 * v + 9) (leader v)))) := by
    simp [leaderOut, hp10]
  exact commit_of_sendCommit hg hv (by norm_num) hL hq hlo (checkedToks_valid hc9)

lemma S_view4 {v : ℕ} (hv : v < n) (p : Fin n) :
    (S π s (11 * v + 4) p).plan = (ph3 π (S π s (11 * v + 3) p) (aib π s (11 * v + 3) p)).plan ∧
    (S π s (11 * v + 4) p).vin = (ph3 π (S π s (11 * v + 3) p) (aib π s (11 * v + 3) p)).vin := by
  rw [show 11 * v + 4 = 11 * v + 3 + 1 by omega, S_view (11 * v + 3) v 3 hv (by norm_num) rfl]
  simp [viewTrans]

/-- **Lemma B.6** (synchronous version). In a view `v < n` with an honest leader, if `f ≤ n - k`,
either every honest party has a commit at the end of the view, or the leader ran the retrieval
(all honest parties being undecided and active) and it failed: the leader set its retrieval input
to `⊥` and got fewer than `t + 1` partial signatures for each value. -/
theorem view_outcome (hfk : (byzF s).card + π.k ≤ n) {v : ℕ} (hv : v < n)
    (hL : leader v ∉ s.byz) :
    (∀ q, q ∉ s.byz → (S π s (11 * v + 11) q).commit.isSome) ∨
    ((∀ q, q ∉ s.byz → (S π s (11 * v + 1) q).commit = none) ∧
      (S π s (11 * v + 1) (leader v)).lead = true ∧
      (S π s (11 * v + 3) (leader v)).plan = .retr ∧
      (retrToks (.inp false) (aib π s (11 * v + 3) (leader v))).card < π.t + 1 ∧
      (retrToks (.inp true) (aib π s (11 * v + 3) (leader v))).card < π.t + 1 ∧
      (S π s (11 * v + 4) (leader v)).vin = none) := by
  by_cases hc0 : (S π s (11 * v) (leader v)).commit = none
  swap
  · -- the leader has a commit: it answers the complaints
    left
    obtain ⟨c, hc⟩ := Option.ne_none_iff_exists'.1 hc0
    intro q hq
    refine commit_mono_isSome hg (r := 11 * v + 1 + 1) (by omega) ?_
    by_cases hq0 : (S π s (11 * v) q).commit.isSome
    · exact commit_mono_isSome hg (by omega) hq0
    have hq0' : (S π s (11 * v + 0) q).commit = none := by simpa using hq0
    have hpo : partyOut q (S π s (11 * v + 0) q) v 0 = some .complain := by
      simp only [Nat.add_zero] at hq0'
      simp [partyOut, hq0']
    obtain ⟨lm, hm⟩ := recv_party hg hv (by norm_num) hq hpo
    simp only [Nat.add_zero] at hm
    have hcompl : isComplain ((S π s (11 * v + 1) (leader v)).last q) = true := by
      rw [S_last, hm]; rfl
    have hlead : (S π s (11 * v + 1) (leader v)).lead = false := by
      rw [S_lead1 hv, hc]; simp
    have hc1 := S_commit_mono (show 11 * v ≤ 11 * v + 1 by omega) hc
    have hlo : leaderOut (S π s (11 * v + 1) (leader v)) 1 q = some (.sendCommit c) := by
      simp [leaderOut, hc1, hlead, hcompl]
    exact commit_of_sendCommit hg hv (by norm_num) hL hq hlo (S_commit_valid _ _ _ hc1)
  have hlead : (S π s (11 * v + 1) (leader v)).lead = true := by
    rw [S_lead1 hv, hc0]; simp
  have hp2 : (S π s (11 * v + 2) (leader v)).plan =
      leaderPlan π v (S π s (11 * v + 1) (leader v)) (aib π s (11 * v + 1) (leader v)) := by
    rw [S_plan2 hv, hlead, if_pos rfl]
  rcases leaderPlan_cases (π := π) v (S π s (11 * v + 1) (leader v)) (aib π s (11 * v + 1) (leader v))
    with ⟨c, hpl⟩ | ⟨c, hbk, hpl⟩ | ⟨hbk, hpl⟩
  · -- a commit is broadcast in phase 2
    left
    intro q hq
    have hval := leaderPlan_bcast_valid (fun c' h' => S_commit_valid _ _ c' h') hpl
    have hlo : leaderOut (S π s (11 * v + 2) (leader v)) 2 q = some (.sendCommit c) := by
      simp [leaderOut, hp2, hpl]
    exact commit_mono_isSome hg (by omega)
      (commit_of_sendCommit hg hv (by norm_num) hL hq hlo hval)
  · -- the highest suggested key is proposed
    left
    have hnc := fun q hq => no_commit_of_not_bcast hg hv hL hc0 (by rw [hpl]; simp) (q := q) hq
    have hp3 : (S π s (11 * v + 3) (leader v)).plan = .propose c.1 (.key c.2.1 c.2.2) := by
      rw [S_plan3 hv, hp2, hpl]
    have hp4 : (S π s (11 * v + 4) (leader v)).plan = .propose c.1 (.key c.2.1 c.2.2) := by
      rw [(S_view4 hg hv _).1]; simp [ph3, hp3]
    have hJ : (Justif.key c.2.1 c.2.2).valid π c.1 v := by
      obtain ⟨q', hq'⟩ := mem_keyCands.1 (bestKey_spec hbk).1
      exact keySugg_spec hq'
    refine propose_success hg hfk hv hL hlead hnc hp4 hJ fun q hq => ?_
    rcases hl : (S π s (11 * v + 4) q).lock with _ | l
    · rfl
    · obtain ⟨c', hc', hle⟩ := bestKey_of_lock hg hv hL hc0 hnc hq hl
      rw [hbk] at hc'; cases hc'
      simp [lockOK, hle]
  · -- the retrieval is run
    have hnc := fun q hq => no_commit_of_not_bcast hg hv hL hc0 (by rw [hpl]; simp) (q := q) hq
    have hp3 : (S π s (11 * v + 3) (leader v)).plan = .retr := by rw [S_plan3 hv, hp2, hpl]
    have hlead3 : (S π s (11 * v + 3) (leader v)).lead = true := by
      rw [S_lead hv (by norm_num) (by norm_num)]; exact hlead
    have hnolock : ∀ q, q ∉ s.byz → (S π s (11 * v + 4) q).lock = none := by
      intro q hq
      rcases hl : (S π s (11 * v + 4) q).lock with _ | l
      · rfl
      · obtain ⟨c', hc', -⟩ := bestKey_of_lock hg hv hL hc0 hnc hq hl
        rw [hbk] at hc'; cases hc'
    have hok : ∀ J, ∀ q, q ∉ s.byz → lockOK (S π s (11 * v + 4) q).lock J = true := by
      intro J q hq; rw [hnolock q hq]; rfl
    obtain ⟨hp4, hvin4⟩ := S_view4 hg hv (leader v)
    by_cases h0 : π.t + 1 ≤ (retrToks (.inp false) (aib π s (11 * v + 3) (leader v))).card
    · left
      refine propose_success hg hfk hv hL hlead hnc (b := false)
        (J := .combine (retrToks (.inp false) (aib π s (11 * v + 3) (leader v))))
        (by rw [hp4]; simp [ph3, hlead3, hp3, h0]) (retrToks_valid h0) (hok _)
    by_cases h1 : π.t + 1 ≤ (retrToks (.inp true) (aib π s (11 * v + 3) (leader v))).card
    · left
      refine propose_success hg hfk hv hL hlead hnc (b := true)
        (J := .combine (retrToks (.inp true) (aib π s (11 * v + 3) (leader v))))
        (by rw [hp4]; simp [ph3, hlead3, hp3, h0, h1]) (retrToks_valid h1) (hok _)
    · right
      refine ⟨hnc, hlead, hp3, by omega, by omega, ?_⟩
      rw [hvin4]; simp [ph3, hlead3, hp3, h0, h1]

/-- In a retrieval run by an honest leader, every honest (undecided) party's answer arrives. -/
lemma retr_answer_mem {v : ℕ} (hv : v < n) (hL : leader v ∉ s.byz)
    (hnc : ∀ q, q ∉ s.byz → (S π s (11 * v + 1) q).commit = none)
    (hp2 : (S π s (11 * v + 2) (leader v)).plan = .retr) {q : Fin n} (hq : q ∉ s.byz) {b : Bool}
    (hb : (S π s (11 * v + 3) q).vin = some b ∨ (S π s (11 * v + 3) q).vin = none) :
    (q, Stmt.inp b) ∈ retrToks (.inp b) (aib π s (11 * v + 3) (leader v)) := by
  have hact : (S π s (11 * v + 3) q).active = true := by
    rw [S_active hv (by norm_num) (by norm_num), hnc q hq]; rfl
  have hrun : isRunRetr ((S π s (11 * v + 3) q).last (leader v)) = true := by
    rw [show 11 * v + 3 = 11 * v + 2 + 1 by omega, S_last]
    have hlo : leaderOut (S π s (11 * v + 2) (leader v)) 2 q = some .runRetr := by
      simp [leaderOut, hp2]
    obtain ⟨pm, hpm⟩ := recv_leader hg hv (by norm_num) hL q hlo
    rw [hpm]; rfl
  have hpo : partyOut q (S π s (11 * v + 3) q) v 3 =
      some (.retr (retrAnswer q (S π s (11 * v + 3) q).vin)) := by
    simp [partyOut, hact, hrun]
  obtain ⟨lm, hm⟩ := recv_party hg hv (by norm_num) hq hpo
  simp only [retrToks, mem_biUnion, mem_univ, true_and]
  refine ⟨q, ?_⟩
  rw [hm]
  simp only [mem_filter, and_true]
  rcases hb with h | h <;> rw [h] <;> cases b <;> simp [retrAnswer]

/-- **Lemma B.7.** If `f ≤ n - k`, every honest party has a commit (has decided) by the end of
view `2f`, i.e. within `11(2f+1)` rounds. -/
theorem all_commit (hfk : (byzF s).card + π.k ≤ n) :
    ∀ q, q ∉ s.byz → (S π s (11 * (2 * (byzF s).card + 1)) q).commit.isSome := by
  classical
  set f := (byzF s).card with hfdef
  have hfn : 2 * f + 1 ≤ n := by have := hg.res; have := hg.faults; omega
  by_contra hne
  push_neg at hne
  obtain ⟨q₀, hq₀, hq₀c⟩ := hne
  -- every honest-leader view among the first `2f+1` fails
  have hfail : ∀ w, w < 2 * f + 1 → leader w ∉ s.byz →
      (∀ q, q ∉ s.byz → (S π s (11 * w + 1) q).commit = none) ∧
      (S π s (11 * w + 1) (leader w)).lead = true ∧
      (S π s (11 * w + 3) (leader w)).plan = .retr ∧
      (retrToks (.inp false) (aib π s (11 * w + 3) (leader w))).card < π.t + 1 ∧
      (retrToks (.inp true) (aib π s (11 * w + 3) (leader w))).card < π.t + 1 ∧
      (S π s (11 * w + 4) (leader w)).vin = none := by
    intro w hw hL
    rcases view_outcome hg hfk (by omega) hL with h | h
    · exact absurd (commit_mono_isSome hg (r' := 11 * (2 * f + 1)) (by omega) (h q₀ hq₀)) hq₀c
    · exact h
  set H := (range (2 * f + 1)).filter fun w => leader w ∉ s.byz with hH
  have hHcard : f + 1 ≤ H.card := by
    have hB : ((range (2 * f + 1)).filter fun w => leader w ∈ s.byz).card ≤ f := by
      have : ((range (2 * f + 1)).filter fun w => leader w ∈ s.byz).image (leader (n := n)) ⊆
          byzF s := by
        intro q hq
        obtain ⟨w, hw, rfl⟩ := mem_image.1 hq
        exact mem_byzF.2 (mem_filter.1 hw).2
      rw [← card_image_of_injOn (f := leader (n := n)) (fun a ha b hb h => leader_injOn
        (by have := mem_range.1 (mem_filter.1 ha).1; omega)
        (by have := mem_range.1 (mem_filter.1 hb).1; omega) h)]
      exact (card_le_card this).trans_eq hfdef.symm
    have := card_filter_add_card_filter_not (s := range (2 * f + 1))
      (fun w => leader (n := n) w ∉ s.byz)
    simp only [not_not, card_range] at this
    have hHdef : H.card = ((range (2 * f + 1)).filter fun w => leader (n := n) w ∉ s.byz).card :=
      rfl
    omega
  have hHne : H.Nonempty := by rw [← card_pos]; omega
  set v := H.max' hHne
  have hvH : v ∈ H := max'_mem H hHne
  have hv2 : v < 2 * f + 1 := mem_range.1 (mem_filter.1 hvH).1
  have hvL : leader v ∉ s.byz := (mem_filter.1 hvH).2
  have hvn : v < n := by omega
  obtain ⟨hnc, hlead, hp3, h0, h1, -⟩ := hfail v hv2 hvL
  have hp2 : (S π s (11 * v + 2) (leader v)).plan = .retr := by rwa [← S_plan3 hvn]
  -- the earlier failed honest leaders have retrieval input `⊥`
  set E := H.filter (· < v)
  have hE : f ≤ E.card := by
    have : E = H.erase v := by
      ext w
      simp only [E, mem_filter, mem_erase]
      constructor
      · rintro ⟨hw, hlt⟩; exact ⟨by omega, hw⟩
      · rintro ⟨hne, hw⟩; exact ⟨hw, lt_of_le_of_ne (le_max' H w hw) hne⟩
    rw [this, card_erase_of_mem hvH]; omega
  have hEvin : E.image (leader (n := n)) ⊆
      s.honestFinset.filter fun q => (S π s (11 * v + 3) q).vin = none := by
    intro q hq
    obtain ⟨w, hw, rfl⟩ := mem_image.1 hq
    obtain ⟨hwH, hwv⟩ := mem_filter.1 hw
    have hw2 := mem_range.1 (mem_filter.1 hwH).1
    have hwL := (mem_filter.1 hwH).2
    refine mem_filter.2 ⟨(Scenario.mem_honestFinset _).2 hwL, ?_⟩
    exact S_vin_none_mono (show 11 * w + 4 ≤ 11 * v + 3 by omega) (hfail w hw2 hwL).2.2.2.2.2
  have hcE : f ≤ (s.honestFinset.filter fun q => (S π s (11 * v + 3) q).vin = none).card := by
    have := card_le_card hEvin
    rw [card_image_of_injOn (f := leader (n := n)) (fun a ha b hb h => leader_injOn
      (by have := mem_range.1 (mem_filter.1 (mem_filter.1 ha).1).1; omega)
      (by have := mem_range.1 (mem_filter.1 (mem_filter.1 hb).1).1; omega) h)] at this
    omega
  -- count the honest retrieval answers
  set P0 := s.honestFinset.filter fun q => (S π s (11 * v + 3) q).vin ≠ some true
  set P1 := s.honestFinset.filter fun q => (S π s (11 * v + 3) q).vin ≠ some false
  have hP : ∀ (b : Bool) (P : Finset (Fin n)),
      (∀ q ∈ P, q ∉ s.byz ∧ ((S π s (11 * v + 3) q).vin = some b ∨
        (S π s (11 * v + 3) q).vin = none)) →
      P.card ≤ (retrToks (.inp b) (aib π s (11 * v + 3) (leader v))).card := by
    intro b P hPq
    have hsub : P.image (fun q => (q, Stmt.inp b)) ⊆
        retrToks (.inp b) (aib π s (11 * v + 3) (leader v)) := by
      intro τ hτ
      obtain ⟨q, hq, rfl⟩ := mem_image.1 hτ
      exact retr_answer_mem hg hvn hvL hnc hp2 (hPq q hq).1 (hPq q hq).2
    have := card_le_card hsub
    rwa [card_image_of_injective _ (fun a b h => by simpa using h)] at this
  have hc0 := hP false P0 (by
    intro q hq
    obtain ⟨hq, hne⟩ := mem_filter.1 hq
    refine ⟨(Scenario.mem_honestFinset _).1 hq, ?_⟩
    rcases S_vin (π := π) (s := s) (11 * v + 3) q with h | h
    · left; rw [h] at hne ⊢; cases hx : s.input q <;> simp_all
    · right; exact h)
  have hc1 := hP true P1 (by
    intro q hq
    obtain ⟨hq, hne⟩ := mem_filter.1 hq
    refine ⟨(Scenario.mem_honestFinset _).1 hq, ?_⟩
    rcases S_vin (π := π) (s := s) (11 * v + 3) q with h | h
    · left; rw [h] at hne ⊢; cases hx : s.input q <;> simp_all
    · right; exact h)
  have hunion : P0 ∪ P1 = s.honestFinset := by
    ext q
    simp only [P0, P1, mem_union, mem_filter]
    constructor
    · rintro (⟨h, -⟩ | ⟨h, -⟩) <;> exact h
    · intro h
      by_cases ht : (S π s (11 * v + 3) q).vin = some true
      · right; exact ⟨h, by rw [ht]; simp⟩
      · left; exact ⟨h, ht⟩
  have hinter : s.honestFinset.filter (fun q => (S π s (11 * v + 3) q).vin = none) ⊆ P0 ∩ P1 := by
    intro q hq
    obtain ⟨hq, hn⟩ := mem_filter.1 hq
    simp [P0, P1, hq, hn]
  have := card_union_add_card_inter P0 P1
  rw [hunion] at this
  have := card_le_card hinter
  have := card_honest_add hg
  have := hg.res
  have := hg.faults
  omega

end Podc.FewToManyFaultsBA.Sync
