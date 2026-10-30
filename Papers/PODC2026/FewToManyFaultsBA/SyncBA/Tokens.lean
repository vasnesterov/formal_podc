import Papers.PODC2026.FewToManyFaultsBA.SyncBA.Phases

/-!
# Unforgeability: every honest partial signature in circulation was really produced

`St.toks` are the tokens held in a local state, `ownToks p st r` the fresh partial signatures that
`p` produces in round `r`. Stage A is unforging (`stageA_unforging`), and in every authenticated
run every token with an honest signer `q` that is held by an honest party after `r` rounds was
produced by `q` itself in an earlier round (`toks_signed`).
-/

namespace Podc.FewToManyFaultsBA.Sync

open Cslib.Byzantine.LockStep Finset

variable {n : ℕ} [NeZero n]

/-- Tokens of an optional proof. -/
def optToks (o : Option (Proof n)) : Cert n := (o.map fun c => c.2.2).getD ∅

/-- Tokens of a plan. -/
def Plan.toks : Plan n → Cert n
  | .bcast c => c.2.2
  | .propose _ J => J.toks
  | .keyC _ c => c
  | .lockC _ c => c
  | .fin c => c.2.2
  | _ => ∅

/-- Tokens of an optional message. -/
def omToks (m : Option (Msg n)) : Cert n := (m.map Msg.toks).getD ∅

/-- Tokens of an inbox. -/
def ibToks (ib : Fin n → Option (Msg n)) : Set (Tok n) := {τ | ∃ q, τ ∈ omToks (ib q)}

/-- Tokens held in a local state. -/
def St.toks (st : St n) : Set (Tok n) :=
  ↑(optToks st.key) ∪ ↑(optToks st.lock) ∪ ↑(optToks st.commit) ∪ ↑st.plan.toks ∪
    ibToks st.last ∪ ↑(st.fb.getD ∅)

/-- The fresh partial signatures `p` produces in round `r`. -/
def ownToks (p : Fin n) (st : St n) (r : ℕ) : Cert n :=
  if r < Rh n then
    (if r % 11 = 3 ∧ st.active ∧ isRunRetr (st.last (leader (r / 11))) = true then
      retrAnswer p st.vin
    else if (r % 11 = 5 ∨ r % 11 = 7 ∨ r % 11 = 9) ∧ st.active then
      (st.sign.map fun s => {(p, s)}).getD ∅
    else ∅)
  else if r = Rh n ∧ st.commit.isNone then {(p, .help)} else ∅

/-! ### Inbox readers only return tokens of the inbox -/

section Readers

variable {ib : Fin n → Option (Msg n)}

lemma retrToks_sub {s : Stmt} {τ : Tok n} (h : τ ∈ retrToks s ib) : τ ∈ ibToks ib := by
  simp only [retrToks, mem_biUnion, mem_univ, true_and] at h
  obtain ⟨q, hq⟩ := h
  refine ⟨q, ?_⟩
  split at hq
  · rename_i c hc
    simp only [omToks, hc, Option.map_some, Option.getD_some, Msg.toks, Option.map_some,
      Option.getD_some, PMsg.toks]
    exact mem_union_left _ (mem_filter.1 hq).1
  · simp at hq

lemma checkedToks_sub {s : Stmt} {τ : Tok n} (h : τ ∈ checkedToks s ib) : τ ∈ ibToks ib := by
  simp only [checkedToks, mem_biUnion, mem_univ, true_and] at h
  obtain ⟨q, hq⟩ := h
  refine ⟨q, ?_⟩
  split at hq
  · rename_i τ' hc
    split_ifs at hq
    · simp only [mem_singleton] at hq
      subst hq
      simp [omToks, hc, Msg.toks, PMsg.toks]
    · simp at hq
  · simp at hq

lemma helpToks_sub {τ : Tok n} (h : τ ∈ helpToks ib) : τ ∈ ibToks ib := by
  simp only [helpToks, mem_biUnion, mem_univ, true_and] at h
  obtain ⟨q, hq⟩ := h
  refine ⟨q, ?_⟩
  split at hq
  · rename_i τ' hc
    split_ifs at hq
    · simp only [mem_singleton] at hq
      subst hq
      simp [omToks, hc, Msg.toks]
    · simp at hq
  · simp at hq

lemma commitOf_toks {k : ℕ} {m : Msg n} {c : Proof n} (h : commitOf k m = some c) :
    c.2.2 ⊆ m.toks := by
  unfold commitOf at h
  split at h
  · split_ifs at h; cases h; intro τ hτ; simp [Msg.toks, LMsg.toks, hτ]
  · split_ifs at h; cases h; intro τ hτ; simp [Msg.toks, hτ]
  · cases h

lemma inboxCommit_toks {k : ℕ} {c : Proof n} (h : inboxCommit k ib = some c) {τ : Tok n}
    (hτ : τ ∈ c.2.2) : τ ∈ ibToks ib := by
  unfold inboxCommit at h
  obtain ⟨q, -, hq⟩ := List.exists_of_findSome?_eq_some h
  obtain ⟨m, hm, hc⟩ := Option.bind_eq_some_iff.1 hq
  exact ⟨q, by simp [omToks, hm, commitOf_toks hc hτ]⟩

lemma inboxFb_toks {t : ℕ} {c : Cert n} (h : inboxFb t ib = some c) {τ : Tok n} (hτ : τ ∈ c) :
    τ ∈ ibToks ib := by
  unfold inboxFb at h
  obtain ⟨q, -, hq⟩ := List.exists_of_findSome?_eq_some h
  refine ⟨q, ?_⟩
  split at hq
  · rename_i pr c' hc
    split_ifs at hq
    cases hq
    simp [omToks, hc, Msg.toks, hτ]
  · cases hq

lemma ownFb_toks {t : ℕ} {c : Cert n} (h : ownFb t ib = some c) {τ : Tok n} (hτ : τ ∈ c) :
    τ ∈ ibToks ib := by
  unfold ownFb at h
  split_ifs at h
  cases h
  exact helpToks_sub hτ

lemma commitSugg_toks {k : ℕ} {m : Option (Msg n)} {c : Proof n} (h : commitSugg k m = some c)
    {τ : Tok n} (hτ : τ ∈ c.2.2) : τ ∈ omToks m := by
  unfold commitSugg at h
  split at h
  · split_ifs at h; cases h; simp [omToks, Msg.toks, PMsg.toks, Sugg.toks, hτ]
  · cases h

lemma keySugg_toks {k v : ℕ} {m : Option (Msg n)} {c : Proof n} (h : keySugg k v m = some c)
    {τ : Tok n} (hτ : τ ∈ c.2.2) : τ ∈ omToks m := by
  unfold keySugg at h
  split at h
  · split_ifs at h; cases h; simp [omToks, Msg.toks, PMsg.toks, Sugg.toks, hτ]
  · cases h

lemma mem_keyCands {k v : ℕ} {c : Proof n} :
    c ∈ keyCands k v ib ↔ ∃ q, keySugg k v (ib q) = some c := by
  simp only [keyCands, mem_biUnion, mem_univ, true_and]
  constructor
  · rintro ⟨q, hq⟩
    rcases h : keySugg k v (ib q) with _ | c'
    · simp [h] at hq
    · simp [h] at hq; exact ⟨q, hq ▸ h⟩
  · rintro ⟨q, hq⟩; exact ⟨q, by simp [hq]⟩

lemma bestKey_spec {k v : ℕ} {c : Proof n} (h : bestKey k v ib = some c) :
    c ∈ keyCands k v ib ∧ ∀ c' ∈ keyCands k v ib, c'.2.1 ≤ c.2.1 := by
  unfold bestKey at h
  split_ifs at h with hne
  cases h
  exact Classical.choose_spec (exists_max_image (keyCands k v ib) (fun c => c.2.1) hne)

lemma bestKey_none {k v : ℕ} (h : bestKey k v ib = none) : keyCands k v ib = ∅ := by
  unfold bestKey at h
  split_ifs at h with hne
  exact not_nonempty_iff_eq_empty.1 hne

lemma bestKey_toks {k v : ℕ} {c : Proof n} (h : bestKey k v ib = some c) {τ : Tok n}
    (hτ : τ ∈ c.2.2) : τ ∈ ibToks ib := by
  obtain ⟨q, hq⟩ := mem_keyCands.1 (bestKey_spec h).1
  exact ⟨q, keySugg_toks hq hτ⟩

lemma mem_lockCands {k : ℕ} {c : Proof n} :
    c ∈ lockCands k ib ↔ ∃ q, lockMsg k (ib q) = some c := by
  simp only [lockCands, mem_biUnion, mem_univ, true_and]
  constructor
  · rintro ⟨q, hq⟩
    rcases h : lockMsg k (ib q) with _ | c'
    · simp [h] at hq
    · simp [h] at hq; exact ⟨q, hq ▸ h⟩
  · rintro ⟨q, hq⟩; exact ⟨q, by simp [hq]⟩

lemma bestLock_spec {k : ℕ} {c : Proof n} (h : bestLock k ib = some c) :
    c ∈ lockCands k ib ∧ ∀ c' ∈ lockCands k ib, c'.2.1 ≤ c.2.1 := by
  unfold bestLock at h
  split_ifs at h with hne
  cases h
  exact Classical.choose_spec (exists_max_image (lockCands k ib) (fun c => c.2.1) hne)

lemma bestLock_none {k : ℕ} (h : bestLock k ib = none) : lockCands k ib = ∅ := by
  unfold bestLock at h
  split_ifs at h with hne
  exact not_nonempty_iff_eq_empty.1 hne

lemma lockMsg_spec {k : ℕ} {m : Option (Msg n)} {c : Proof n} (h : lockMsg k m = some c) :
    m = some (.lock c) ∧ Valid n k (.lock c.1 c.2.1) c.2.2 := by
  unfold lockMsg at h
  split at h
  · split_ifs at h with hv; cases h; exact ⟨rfl, hv⟩
  · cases h

lemma proposalOf_toks {m : Option (Msg n)} {b : Bool} {J : Justif n}
    (h : proposalOf m = some (b, J)) {τ : Tok n} (hτ : τ ∈ J.toks) : τ ∈ omToks m := by
  unfold proposalOf at h
  split at h
  · cases h; simp [omToks, Msg.toks, LMsg.toks, hτ]
  · cases h

lemma proposeLockOf_toks {m : Option (Msg n)} {b : Bool} {c : Cert n}
    (h : proposeLockOf m = some (b, c)) {τ : Tok n} (hτ : τ ∈ c) : τ ∈ omToks m := by
  unfold proposeLockOf at h
  split at h
  · cases h; simp [omToks, Msg.toks, LMsg.toks, hτ]
  · cases h

lemma proposeCommitOf_toks {m : Option (Msg n)} {b : Bool} {c : Cert n}
    (h : proposeCommitOf m = some (b, c)) {τ : Tok n} (hτ : τ ∈ c) : τ ∈ omToks m := by
  unfold proposeCommitOf at h
  split at h
  · cases h; simp [omToks, Msg.toks, LMsg.toks, hτ]
  · cases h

end Readers

/-! ### Tokens of outgoing messages -/

section Out

variable {π : Params n}

lemma mem_toks_key {st : St n} {τ : Tok n} (h : τ ∈ optToks st.key) : τ ∈ st.toks := by
  simp [St.toks, h]
lemma mem_toks_lock {st : St n} {τ : Tok n} (h : τ ∈ optToks st.lock) : τ ∈ st.toks := by
  simp [St.toks, h]
lemma mem_toks_commit {st : St n} {τ : Tok n} (h : τ ∈ optToks st.commit) : τ ∈ st.toks := by
  simp [St.toks, h]
lemma mem_toks_plan {st : St n} {τ : Tok n} (h : τ ∈ st.plan.toks) : τ ∈ st.toks := by
  simp [St.toks, h]
lemma mem_toks_last {st : St n} {τ : Tok n} (h : τ ∈ ibToks st.last) : τ ∈ st.toks := by
  simp only [St.toks, Set.mem_union]; tauto
lemma mem_toks_fb {st : St n} {τ : Tok n} (h : τ ∈ st.fb.getD ∅) : τ ∈ st.toks := by
  simp [St.toks, h]

lemma partyOut_toks {p : Fin n} {st : St n} {v j : ℕ} {pm : PMsg n}
    (h : partyOut p st v j = some pm) {τ : Tok n} (hτ : τ ∈ pm.toks) :
    τ ∈ st.toks ∨ (j = 3 ∧ st.active ∧ isRunRetr (st.last (leader v)) = true ∧
      τ ∈ retrAnswer p st.vin) ∨
      ((j = 5 ∨ j = 7 ∨ j = 9) ∧ st.active ∧ ∃ s, st.sign = some s ∧ τ = (p, s)) := by
  unfold partyOut at h
  by_cases h0 : j = 0
  · simp only [h0, ite_true] at h; split_ifs at h; cases h; simp [PMsg.toks] at hτ
  by_cases h1 : j = 1
  · simp only [h0, h1, ite_true, ite_false, one_ne_zero] at h
    split_ifs at h; cases h
    left
    rcases hc : st.commit with _ | c <;> rcases hk : st.key with _ | c' <;>
      simp_all [PMsg.toks, Sugg.toks, suggOf] <;>
      first | exact mem_toks_commit (by simp only [optToks, hc]; exact hτ)
            | exact mem_toks_key (by simp only [optToks, hk]; exact hτ)
  by_cases h3 : j = 3
  · simp only [h0, h1, h3, ite_true, ite_false, OfNat.ofNat_ne_zero, OfNat.ofNat_ne_one] at h
    split_ifs at h with ha; cases h
    right; left; exact ⟨h3, ha.1, ha.2, by simpa [PMsg.toks] using hτ⟩
  by_cases h5 : j = 5 ∨ j = 7 ∨ j = 9
  · simp only [h0, h1, h3, h5, ite_true, ite_false] at h
    rcases hs : st.sign with _ | s'
    · simp [hs] at h
    · simp only [hs] at h
      split_ifs at h with ha; cases h
      right; right
      simp only [PMsg.toks, mem_singleton] at hτ
      exact ⟨h5, ha, s', rfl, hτ⟩
  · simp [h0, h1, h3, h5] at h

lemma leaderOut_toks {st : St n} {j : ℕ} {q : Fin n} {lm : LMsg n}
    (h : leaderOut st j q = some lm) {τ : Tok n} (hτ : τ ∈ lm.toks) : τ ∈ st.toks := by
  unfold leaderOut at h
  split_ifs at h <;> (try split at h) <;> (try split_ifs at h) <;> (try cases h) <;>
    simp_all [LMsg.toks, mem_toks_commit, mem_toks_plan, optToks, Plan.toks, Justif.toks]
  all_goals first
    | exact mem_toks_commit (by simp_all [optToks])
    | exact mem_toks_plan (by simp_all [Plan.toks])
    | skip

lemma partyOut_toks' {p : Fin n} {st : St n} {r : ℕ} (hr : r < Rh n) {τ : Tok n}
    (hτ : τ ∈ (Option.map PMsg.toks (partyOut p st (r / 11) (r % 11))).getD ∅) :
    τ ∈ st.toks ∨ τ ∈ ownToks p st r := by
  rcases hpo : partyOut p st (r / 11) (r % 11) with _ | pm
  · simp [hpo] at hτ
  · simp only [hpo, Option.map_some, Option.getD_some] at hτ
    rcases partyOut_toks hpo hτ with h1 | ⟨h3, ha, hrr, hm⟩ | ⟨h5, ha, s, hs, rfl⟩
    · exact Or.inl h1
    · right; simp [ownToks, hr, h3, ha, hrr, hm]
    · right
      have : ¬ r % 11 = 3 := by omega
      simp [ownToks, hr, this, h5, ha, hs]

lemma leaderOut_toks' {st : St n} {j : ℕ} {q : Fin n} {τ : Tok n}
    (hτ : τ ∈ (Option.map LMsg.toks (leaderOut st j q)).getD ∅) : τ ∈ st.toks := by
  rcases hlo : leaderOut st j q with _ | lm
  · simp [hlo] at hτ
  · simp only [hlo, Option.map_some, Option.getD_some] at hτ
    exact leaderOut_toks hlo hτ

lemma out_toks {p : Fin n} {st : St n} {r : ℕ} {q : Fin n} {m : Msg n}
    (h : out π p st r q = some m) {τ : Tok n} (hτ : τ ∈ m.toks) :
    τ ∈ st.toks ∨ τ ∈ ownToks p st r := by
  unfold out at h
  by_cases hr : r < Rh n
  · simp only [hr, ite_true] at h
    split_ifs at h <;> cases h <;>
      simp only [Msg.toks, mem_union, Option.map_none, Option.getD_none, notMem_empty,
        false_or, or_false] at hτ
    · rcases hτ with hτ | hτ
      · exact partyOut_toks' hr hτ
      · exact Or.inl (leaderOut_toks' hτ)
    · exact partyOut_toks' hr hτ
    · exact Or.inl (leaderOut_toks' hτ)
  · simp only [hr, ite_false] at h
    by_cases h0 : r = Rh n
    · subst h0
      simp only [ite_true] at h
      split_ifs at h with hc
      cases h
      right
      simp only [Msg.toks, mem_singleton] at hτ
      subst hτ
      simp [ownToks, hc]
    · simp only [h0, ite_false] at h
      by_cases h1 : r = Rh n + 1
      · simp only [h1, ite_true] at h
        left
        have hfb : τ ∈ (ownFb π.t st.last).getD ∅ → τ ∈ st.toks := by
          intro hτ
          rcases hf : ownFb π.t st.last with _ | c
          · simp [hf] at hτ
          · simp only [hf, Option.getD_some] at hτ
            exact mem_toks_last (ownFb_toks hf hτ)
        split_ifs at h <;> cases h <;>
          simp only [Msg.toks, mem_union, Option.map_none, Option.getD_none, notMem_empty,
            false_or, or_false] at hτ
        · rcases hτ with hτ | hτ
          · exact mem_toks_commit (by simpa [optToks] using hτ)
          · exact hfb hτ
        · exact hfb hτ
      · simp only [h1, ite_false] at h
        by_cases h2 : r = Rh n + 2
        · simp only [h2, ite_true] at h
          rcases hl : st.lock with _ | c
          · simp [hl] at h
          · simp only [hl] at h
            split_ifs at h
            cases h
            left
            exact mem_toks_lock (by simpa [optToks, hl, Msg.toks] using hτ)
        · simp [h2] at h

lemma mem_St_toks {st : St n} {τ : Tok n} : τ ∈ st.toks ↔
    τ ∈ optToks st.key ∨ τ ∈ optToks st.lock ∨ τ ∈ optToks st.commit ∨ τ ∈ st.plan.toks ∨
      τ ∈ ibToks st.last ∨ τ ∈ st.fb.getD ∅ := by
  simp only [St.toks, Set.mem_union, Finset.mem_coe]; tauto

lemma leaderPlan_toks {v : ℕ} {st : St n} {ib : Fin n → Option (Msg n)} {τ : Tok n}
    (h : τ ∈ (leaderPlan π v st ib).toks) : τ ∈ optToks st.commit ∨ τ ∈ ibToks ib := by
  unfold leaderPlan at h
  split at h
  · rename_i c hc; left; simpa [Plan.toks, optToks, hc] using h
  · split at h
    · rename_i c hc
      right
      obtain ⟨q, -, hq⟩ := List.exists_of_findSome?_eq_some hc
      exact ⟨q, commitSugg_toks hq (by simpa [Plan.toks] using h)⟩
    · split at h
      · rename_i c hc
        right
        exact bestKey_toks hc (by simpa [Plan.toks, Justif.toks] using h)
      · simp [Plan.toks] at h

lemma ph1_plan (st : St n) (v : ℕ) (ib : Fin n → Option (Msg n)) :
    (ph1 π st v ib).plan = if st.lead then leaderPlan π v st ib else st.plan := by
  unfold ph1; split_ifs <;> (try split) <;> simp_all

lemma ph1_commit (st : St n) (v : ℕ) (ib : Fin n → Option (Msg n)) :
    (ph1 π st v ib).commit = st.commit ∨
      ∃ c, leaderPlan π v st ib = .bcast c ∧ (ph1 π st v ib).commit = st.commit.or (some c) := by
  unfold ph1; split_ifs <;> (try split) <;> simp_all

lemma viewTrans_toks {p : Fin n} {st : St n} {v j : ℕ} {ib : Fin n → Option (Msg n)} {τ : Tok n}
    (h : τ ∈ (viewTrans π p st v j ib).toks) : τ ∈ st.toks ∨ τ ∈ ibToks ib := by
  rw [mem_St_toks] at h
  have hl := viewTrans_last (π := π) p st v ib j
  have hf := viewTrans_fb (π := π) p st v ib j
  rw [hl, hf] at h
  rcases h with h | h | h | h | h | h
  · by_cases hj : j = 6
    · subst hj
      simp only [viewTrans, ph6] at h
      split at h
      · rename_i b c hc
        split_ifs at h
        · right; exact ⟨_, proposeLockOf_toks hc (by simpa [optToks] using h)⟩
        · exact Or.inl (mem_toks_key h)
      · exact Or.inl (mem_toks_key h)
    · rw [viewTrans_key p st v ib hj] at h; exact Or.inl (mem_toks_key h)
  · by_cases hj : j = 8
    · subst hj
      simp only [viewTrans, ph8] at h
      split at h
      · rename_i b c hc
        split_ifs at h
        · right; exact ⟨_, proposeCommitOf_toks hc (by simpa [optToks] using h)⟩
        · exact Or.inl (mem_toks_lock h)
      · exact Or.inl (mem_toks_lock h)
    · rw [viewTrans_lock p st v ib hj] at h; exact Or.inl (mem_toks_lock h)
  · by_cases h1 : j = 1
    · subst h1
      simp only [viewTrans] at h
      rcases ph1_commit (π := π) st v ib with hc | ⟨c, hc, hc'⟩
      · rw [hc] at h; exact Or.inl (mem_toks_commit h)
      · rw [hc'] at h
        rcases hcm : st.commit with _ | c'
        · simp only [hcm, Option.none_or, optToks, Option.map_some, Option.getD_some] at h
          rcases leaderPlan_toks (π := π) (τ := τ) (by rw [hc]; simpa [Plan.toks] using h) with
            h' | h'
          · simp [optToks, hcm] at h'
          · exact Or.inr h'
        · simp only [hcm, Option.some_or] at h
          exact Or.inl (mem_toks_commit (by rw [hcm]; exact h))
    by_cases h9 : j = 9
    · subst h9
      simp only [viewTrans, phAgg] at h
      split at h <;> (try (exfalso; omega)) <;> (try split_ifs at h) <;>
        first
        | exact Or.inl (mem_toks_commit h)
        | (simp only [optToks] at h
           rcases hcm : st.commit with _ | c'
           · simp only [hcm, Option.none_or, Option.map_some, Option.getD_some] at h
             exact Or.inr (checkedToks_sub h)
           · simp only [hcm, Option.some_or] at h
             exact Or.inl (mem_toks_commit (by simpa [optToks, hcm] using h)))
    · rw [viewTrans_commit p st v ib h1 h9] at h; exact Or.inl (mem_toks_commit h)
  · -- the plan
    unfold viewTrans at h
    split at h
    · simp [ph0, Plan.toks] at h
    · rw [ph1_plan] at h
      split_ifs at h
      · rcases leaderPlan_toks (π := π) h with h' | h'
        · exact Or.inl (mem_toks_commit h')
        · exact Or.inr h'
      · exact Or.inl (mem_toks_plan h)
    · simp only [ph3] at h
      split_ifs at h <;>
        first
        | exact Or.inl (mem_toks_plan h)
        | exact Or.inr (retrToks_sub (by simpa [Plan.toks, Justif.toks] using h))
        | (simp [Plan.toks] at h; done)
    · exact Or.inl (mem_toks_plan h)
    all_goals first
      | exact Or.inl (mem_toks_plan h)
      | (simp only [ph6, ph8] at h; split at h <;> (try split_ifs at h) <;>
          exact Or.inl (mem_toks_plan h))
      | (simp only [phAgg] at h
         split at h <;> (try split_ifs at h) <;>
           first
           | exact Or.inl (mem_toks_plan h)
           | exact Or.inr (checkedToks_sub (by simpa [Plan.toks] using h))
           | (simp [Plan.toks] at h))
  · exact Or.inl (mem_toks_last h)
  · exact Or.inl (mem_toks_fb h)

/-- Transitions only add tokens of the inbox. -/
lemma trans_toks {p : Fin n} {st : St n} {r : ℕ} {ib : Fin n → Option (Msg n)} {τ : Tok n}
    (h : τ ∈ (trans π p st r ib).toks) : τ ∈ st.toks ∨ τ ∈ ibToks ib := by
  -- generic shape: the last inbox, a commit update, and a phase update
  have key : ∀ st₁ : St n, (∀ τ, τ ∈ st₁.toks → τ ∈ st.toks ∨ τ ∈ ibToks ib) →
      τ ∈ ({ st₁ with commit := st₁.commit.or (inboxCommit π.k ib), last := ib } : St n).toks →
        τ ∈ st.toks ∨ τ ∈ ibToks ib := by
    intro st₁ h₁ hτ
    rw [mem_St_toks] at hτ
    simp only at hτ
    rcases hτ with h' | h' | h' | h' | h' | h'
    · exact h₁ τ (mem_toks_key h')
    · exact h₁ τ (mem_toks_lock h')
    · rcases hc : st₁.commit with _ | c
      · rw [hc, Option.none_or] at h'
        rcases hi : inboxCommit π.k ib with _ | c'
        · simp [hi, optToks] at h'
        · rw [hi] at h'
          exact Or.inr (inboxCommit_toks hi (by simpa [optToks] using h'))
      · rw [hc, Option.some_or] at h'
        exact h₁ τ (mem_toks_commit (by rw [hc]; exact h'))
    · exact h₁ τ (mem_toks_plan h')
    · exact Or.inr h'
    · exact h₁ τ (mem_toks_fb h')
  unfold trans at h
  by_cases hr : r < Rh n
  · have hr0 : r < R0 n := by unfold R0; unfold Rh at hr; omega
    simp only [hr, hr0, ite_true] at h
    exact key _ (fun τ hτ => viewTrans_toks hτ) h
  · simp only [hr, ite_false] at h
    by_cases h1 : r = Rh n + 1
    · subst h1
      have hr0 : Rh n + 1 < R0 n := by unfold R0 Rh; omega
      simp only [hr0, ite_true] at h
      refine key { st with fb := (ownFb π.t st.last).or (inboxFb π.t ib) } (fun τ hτ => ?_) h
      rw [mem_St_toks] at hτ
      simp only at hτ
      rcases hτ with h' | h' | h' | h' | h' | h'
      · exact Or.inl (mem_toks_key h')
      · exact Or.inl (mem_toks_lock h')
      · exact Or.inl (mem_toks_commit h')
      · exact Or.inl (mem_toks_plan h')
      · exact Or.inl (mem_toks_last h')
      · rcases hf : ownFb π.t st.last with _ | c
        · rw [hf, Option.none_or] at h'
          rcases hi : inboxFb π.t ib with _ | c'
          · simp [hi] at h'
          · rw [hi] at h'; exact Or.inr (inboxFb_toks hi h')
        · rw [hf, Option.some_or] at h'
          exact Or.inl (mem_toks_last (ownFb_toks hf h'))
    · simp only [h1, ite_false] at h
      by_cases hr0 : r < R0 n
      · simp only [hr0, ite_true] at h
        exact key st (fun τ hτ => Or.inl hτ) h
      · simp only [hr0, ite_false] at h
        rw [mem_St_toks] at h
        simp only at h
        rcases h with h' | h' | h' | h' | h' | h'
        · exact Or.inl (mem_toks_key h')
        · exact Or.inl (mem_toks_lock h')
        · exact Or.inl (mem_toks_commit h')
        · exact Or.inl (mem_toks_plan h')
        · exact Or.inr h'
        · exact Or.inl (mem_toks_fb h')

end Out

end Podc.FewToManyFaultsBA.Sync

/-! ### The global unforgeability invariant -/

namespace Podc.FewToManyFaultsBA.Sync

open Cslib.Byzantine.LockStep Finset

variable {n : ℕ} [NeZero n] (π : Params n) (s : Scenario (Fin n) Bool (Msg n))

/-- `q` produced its partial signature on `σ` before round `r`. -/
def Signed (q : Fin n) (σ : Stmt) (r : ℕ) : Prop :=
  ∃ r' < r, (q, σ) ∈ ownToks q (S π s r' q) r'

variable {π s}

lemma Signed.mono {q : Fin n} {σ : Stmt} {r r' : ℕ} (h : Signed π s q σ r) (hr : r ≤ r') :
    Signed π s q σ r' := by
  obtain ⟨r₀, hr₀, h⟩ := h; exact ⟨r₀, by omega, h⟩

lemma ownToks_fst {p : Fin n} {st : St n} {r : ℕ} {τ : Tok n} (h : τ ∈ ownToks p st r) :
    τ.1 = p := by
  unfold ownToks at h
  split_ifs at h <;> simp_all [retrAnswer]
  · split at h <;> simp_all
    rcases h with rfl | rfl <;> rfl
  · rcases hs : st.sign with _ | σ <;> simp_all

lemma init_toks (x : Bool) : (St.init x : St n).toks = ∅ := by
  ext τ
  simp [St.toks, St.init, optToks, Plan.toks, ibToks, omToks]

lemma out_none_ge {p : Fin n} {st : St n} {r : ℕ} (hr : R0 n ≤ r) (q : Fin n) :
    out π p st r q = none := by
  have h1 : ¬ r < Rh n := by unfold R0 at hr; unfold Rh; omega
  have h2 : r ≠ Rh n := by unfold R0 at hr; unfold Rh; omega
  have h3 : r ≠ Rh n + 1 := by unfold R0 at hr; unfold Rh; omega
  have h4 : r ≠ Rh n + 2 := by unfold R0 at hr; unfold Rh; omega
  simp [out, h1, h2, h3, h4]

/-- **Unforgeability.** In an authenticated reliable run of stage A, every token held by an honest
party with an honest signer `q` was produced by `q` itself earlier. -/
theorem toks_signed (hrel : s.Reliable) (hA : s.AuthValid (G n) (stageA π) auth) :
    ∀ r, ∀ p ∉ s.byz, ∀ τ ∈ (S π s r p).toks, τ.1 ∈ s.byz ∨ Signed π s τ.1 τ.2 r := by
  intro r
  induction r using Nat.strong_induction_on with
  | _ r ih =>
  -- messages sent by honest parties before round `r`
  have sent : ∀ r' < r, ∀ p ∉ s.byz, ∀ q m, out π p (S π s r' p) r' q = some m →
      ∀ τ ∈ m.toks, τ.1 ∈ s.byz ∨ Signed π s τ.1 τ.2 r := by
    intro r' hr' p hp q m hm τ hτ
    rcases out_toks hm hτ with h | h
    · rcases ih r' hr' p hp τ h with h' | h'
      · exact Or.inl h'
      · exact Or.inr (h'.mono hr'.le)
    · right
      have := ownToks_fst h
      obtain ⟨a, σ⟩ := τ
      simp only at this
      subst this
      exact ⟨r', hr', h⟩
  intro p hp τ hτ
  rcases r with _ | r
  · simp [init_toks] at hτ
  rw [S_succ] at hτ
  rcases trans_toks hτ with h | ⟨q, hq⟩
  · rcases ih r (by omega) p hp τ h with h' | h'
    · exact Or.inl h'
    · exact Or.inr (h'.mono (by omega))
  rcases hm : aib π s r p q with _ | m
  · simp [hm, omToks] at hq
  simp only [hm, omToks, Option.map_some, Option.getD_some] at hq
  by_cases hqb : q ∈ s.byz
  · have hqp : q ≠ p := fun h => hp (h ▸ hqb)
    rw [aib_byz hqb hqp] at hm
    rcases hA r q p m hqb hp (by simpa [G] using hqp) hm τ (by simpa [auth] using hq) with
      h | ⟨r', hr', p', hp', q', -, m', hm', hτ'⟩
    · exact Or.inl h
    · simp only [stageA, length_hist] at hm'
      split_ifs at hm' with hlt
      exact sent r' (by omega) p' hp' q' m' hm' τ (by simpa [auth] using hτ')
  · by_cases hr0 : r < R0 n
    · rw [aib_honest hrel hr0 p hqb] at hm
      exact sent r (by omega) q hqb p m hm τ hq
    · by_cases hqp : q = p
      · subst hqp
        rw [aib_self, out_none_ge (not_lt.1 hr0)] at hm; cases hm
      · rw [aib_honest_ge (not_lt.1 hr0) hqp hqb] at hm; cases hm

/-- Messages of honest parties only carry produced tokens. -/
theorem sent_signed (hrel : s.Reliable) (hA : s.AuthValid (G n) (stageA π) auth) {r : ℕ}
    {p q : Fin n} (hp : p ∉ s.byz) {m : Msg n} (hm : out π p (S π s r p) r q = some m)
    {τ : Tok n} (hτ : τ ∈ m.toks) : τ.1 ∈ s.byz ∨ Signed π s τ.1 τ.2 (r + 1) := by
  rcases out_toks hm hτ with h | h
  · rcases toks_signed hrel hA r p hp τ h with h' | h'
    · exact Or.inl h'
    · exact Or.inr (h'.mono (by omega))
  · right
    have := ownToks_fst h
    obtain ⟨a, σ⟩ := τ
    simp only at this
    subst this
    exact ⟨r, by omega, h⟩

end Podc.FewToManyFaultsBA.Sync
