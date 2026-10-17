import Papers.PODC2021.FastByzantineConsensus.Implementation

/-!
# The concrete protocol: weak validity and the two-step property

* `algo_validity`: weak validity.
* `algo_twoStep`: "The protocol presented in Section 3 is `t`-two-step" (Section 4.1), for
  `δ ≥ 2` and views longer than `2δ + 1`.
-/

set_option linter.unusedSectionVars false

namespace FastByzantineConsensus.Impl

open Cslib.Byzantine.PartialSync FastByzantineConsensus.Protocol Finset

variable {P V : Type*} [Fintype P] [DecidableEq P] [DecidableEq V]
variable {pr : Params P} {L δ : ℕ}

/-! ### Weak validity -/

theorem of_mem_filter' {α : Type*} {p : α → Prop} {inst : DecidablePred p} {s : Finset α}
    {a : α} (h : a ∈ @Finset.filter α p inst s) : p a :=
  ((@Finset.mem_filter α p inst s a).mp h).2

theorem mem_filter_of' {α : Type*} {p : α → Prop} {inst : DecidablePred p} {s : Finset α}
    {a : α} (hs : a ∈ s) (hp : p a) : a ∈ @Finset.filter α p inst s :=
  (@Finset.mem_filter α p inst s a).mpr ⟨hs, hp⟩

section Validity

/-- Every value carried by a token is `x`. -/
def VOK (x : V) : Tok P V → Prop
  | .propose _ y _ => y = x
  | .ack _ y _ => y = x
  | .certAck _ y _ => y = x
  | .commit _ y _ => y = x
  | .vote _ _ b c => (∀ y u, b = some (y, u) → y = x) ∧ (∀ y u, c = some (y, u) → y = x)

/-- Every value occurring in the local state is `x`. -/
def SOK (x : V) (s : LState P V) : Prop :=
  s.input = x ∧ (∀ k ∈ s.known, VOK x k) ∧ (∀ y u, s.ballot = some (y, u) → y = x) ∧
    (∀ y u, s.cc = some (y, u) → y = x)

theorem sel_of_vok {K : Finset (Tok P V)} {v : ℕ} {x y : V} (hK : ∀ k ∈ K, VOK x k)
    (h : Sel pr K v y) : Sel pr K v x := by
  obtain ⟨S, bal, cc, hV, hS⟩ := h
  refine ⟨S, bal, cc, hV, ?_⟩
  have hb : ∀ s ∈ S, ∀ y u, bal s = some (y, u) → y = x := fun s hs => by
    have := hK _ (hV.2 s hs).1
    simp only [VOK] at this
    exact this.1
  rcases hS with h0 | ⟨w, h1, h2, -⟩
  · exact Or.inl h0
  · exact Or.inr ⟨w, h1, h2, Or.inl fun s hs y' h => hb s hs y' w h⟩

theorem leaderChoice_vok {K : Finset (Tok P V)} {v : ℕ} {x : V} (hK : ∀ k ∈ K, VOK x k) :
    leaderChoice pr K v x = x := by
  unfold leaderChoice
  split_ifs with h1 h2
  · rfl
  · exact absurd (sel_of_vok hK (Classical.choose_spec h2)) h1
  · rfl

theorem sok_vote {x : V} (p : P) (old : LState P V) (v : ℕ) {s : LState P V} (h : SOK x s) :
    SOK x (actVote L p old v s) := by
  unfold actVote
  split_ifs
  · refine ⟨h.1, forall_mem_insert _ _ _ |>.mpr ⟨?_, h.2.1⟩, h.2.2⟩
    exact ⟨h.2.2.1, h.2.2.2⟩
  · exact h

theorem sok_leaderCA {x : V} (p : P) (v : ℕ) {s : LState P V} (h : SOK x s) :
    SOK x (actLeaderCA pr p v s) := by
  unfold actLeaderCA
  split_ifs
  · refine ⟨h.1, forall_mem_insert _ _ _ |>.mpr ⟨?_, h.2.1⟩, h.2.2⟩
    show leaderChoice pr s.known v s.input = x
    rw [h.1]; exact leaderChoice_vok h.2.1
  · exact h

theorem sok_verify {x : V} (p : P) (v : ℕ) {s : LState P V} (h : SOK x s) :
    SOK x (actVerify pr p v s) := by
  unfold actVerify
  split_ifs with hh
  · refine ⟨h.1, forall_mem_insert _ _ _ |>.mpr ⟨?_, h.2.1⟩, h.2.2⟩
    have := h.2.1 _ (Classical.choose_spec hh).1
    exact this
  · exact h

theorem sok_propose {x : V} (p : P) (v : ℕ) {s : LState P V} (h : SOK x s) :
    SOK x (actPropose pr p v s) := by
  unfold actPropose
  split_ifs with hh
  · refine ⟨h.1, forall_mem_insert _ _ _ |>.mpr ⟨?_, h.2.1⟩, h.2.2⟩
    have hc := Classical.choose_spec hh.2.2.2
    obtain ⟨r, -, hr⟩ := hc.exists_correct_signer (F := ∅) le_rfl (Nat.succ_pos _)
    have := h.2.1 _ (Finset.mem_coe.mp hr)
    exact this
  · exact h

theorem sok_ack {x : V} (p : P) (v : ℕ) {s : LState P V} (h : SOK x s) :
    SOK x (actAck pr p v s) := by
  unfold actAck
  split_ifs with hh
  · have hy : Classical.choose hh.2 = x := h.2.1 _ (Classical.choose_spec hh.2).1
    refine ⟨h.1, forall_mem_insert _ _ _ |>.mpr ⟨hy, h.2.1⟩, ?_, h.2.2.2⟩
    rintro y u hyu
    simp only [Option.some.injEq, Prod.mk.injEq] at hyu
    rw [← hyu.1]; exact hy
  · exact h

theorem sok_commit {x : V} (p : P) (v : ℕ) {s : LState P V} (h : SOK x s) :
    SOK x (actCommit pr p v s) := by
  unfold actCommit
  split_ifs with hh
  · have hc := (Classical.choose_spec hh).1
    obtain ⟨r, -, hr⟩ := hc.exists_correct_signer (F := ∅) le_rfl
      (show 0 < pr.qc by unfold Params.qc; omega)
    have hy : Classical.choose hh = x := h.2.1 _ (Finset.mem_coe.mp hr)
    refine ⟨h.1, forall_mem_insert _ _ _ |>.mpr ⟨hy, h.2.1⟩, h.2.2.1, ?_⟩
    rintro y u hyu
    simp only [Option.some.injEq, Prod.mk.injEq] at hyu
    rw [← hyu.1]; exact hy
  · exact h

theorem sok_stepFn {x : V} (p : P) (s : LState P V) (ib : P → List (Tok P V)) (hs : SOK x s)
    (hib : ∀ r, ∀ k ∈ ib r, VOK x k) : SOK x (stepFn pr L p s ib) := by
  rw [stepFn_eq]
  simp only [Function.comp]
  apply sok_commit; apply sok_ack; apply sok_propose; apply sok_verify; apply sok_leaderCA
  apply sok_vote
  refine ⟨hs.1, fun k hk => ?_, hs.2.2⟩
  rcases mem_union.mp hk with hk | hk
  · exact hs.2.1 k hk
  · obtain ⟨q, -, hq⟩ := mem_biUnion.mp hk
    exact hib q k (List.mem_toFinset.mp hq)

/-- **Weak validity.** (Needs `t < n`: otherwise the empty set of acks is a fast quorum and every
value counts as decided.) -/
theorem algo_validity (hL : 0 < L) (ht : pr.t < Fintype.card P) (R : Run P (Tok P V) V)
    (hRa : R.AuthValid auth (algo pr L)) :
    ∀ p ∉ R.faulty, ∀ v, R.Decides (algo pr L) p v → v ∈ weakValidity P V R.inputConf := by
  rintro p - v ⟨τ, hτ⟩ x hx
  have hq : ∀ q, q ∉ R.faulty ∧ R.inp q = x := by
    intro q
    have := hx q
    simp only [Run.inputConf] at this
    split_ifs at this with h
    exact ⟨h, Option.some.inj this⟩
  have hinv : ∀ τ q, SOK x (R.st (algo pr L) τ q) := by
    intro τ
    induction τ using Nat.strong_induction_on with
    | _ τ ih =>
      intro q
      rcases τ with _ | τ
      · refine ⟨(hq q).2, fun k hk => ?_, fun _ _ h => by simp [algo] at h,
          fun _ _ h => by simp [algo] at h⟩
        simp only [Run.st_zero, algo] at hk
        split_ifs at hk
        · rw [mem_singleton] at hk; subst hk; exact (hq q).2
        · simp at hk
      · rw [st_succ_eq]
        refine sok_stepFn q _ _ (ih τ (by omega) q) fun r k hk => ?_
        obtain ⟨σ, hσ, -, hk⟩ := Run.mem_inbox.mp hk
        rw [out_correct _ (hq r).1] at hk
        exact (ih σ (by omega) r).2.1 k (by simpa using hk)
  have hK := (hinv τ p).2.1
  simp only [algo] at hτ
  split_ifs at hτ with h
  obtain ⟨w, hw⟩ := Classical.choose_spec h
  rw [Option.some.injEq] at hτ
  subst hτ
  rcases hw with hw | hw
  · obtain ⟨r, hr⟩ := card_pos.mp (Nat.lt_of_lt_of_le
      (show 0 < Fintype.card P - pr.t by omega) hw)
    unfold ackers at hr
    have hr' := of_mem_filter' hr
    exact hK _ (Finset.mem_coe.mp hr')
  · obtain ⟨r, hr⟩ := card_pos.mp (Nat.lt_of_lt_of_le
      (show 0 < pr.qc by unfold Params.qc; omega) hw)
    unfold committers at hr
    have hr' := of_mem_filter' hr
    exact hK _ (Finset.mem_coe.mp hr')

end Validity

/-! ### The two-step property -/

section TwoStepProof

/-- View-0 proposals are the leader's, and view-0 proposals and acks carry the value `a`. -/
def G0 (ℓ : P) (a : V) : Tok P V → Prop
  | .propose p y v => v = 0 → p = ℓ ∧ y = a
  | .ack _ y v => v = 0 → y = a
  | _ => True

variable {ℓ : P} {a : V}

theorem g0_vote (p : P) (old : LState P V) (v : ℕ) {s : LState P V}
    (h : ∀ k ∈ s.known, G0 ℓ a k) : ∀ k ∈ (actVote L p old v s).known, G0 ℓ a k := by
  unfold actVote
  split_ifs
  · exact forall_mem_insert _ _ _ |>.mpr ⟨trivial, h⟩
  · exact h

theorem g0_leaderCA (p : P) (v : ℕ) {s : LState P V}
    (h : ∀ k ∈ s.known, G0 ℓ a k) : ∀ k ∈ (actLeaderCA pr p v s).known, G0 ℓ a k := by
  unfold actLeaderCA
  split_ifs
  · exact forall_mem_insert _ _ _ |>.mpr ⟨trivial, h⟩
  · exact h

theorem g0_verify (p : P) (v : ℕ) {s : LState P V}
    (h : ∀ k ∈ s.known, G0 ℓ a k) : ∀ k ∈ (actVerify pr p v s).known, G0 ℓ a k := by
  unfold actVerify
  split_ifs
  · exact forall_mem_insert _ _ _ |>.mpr ⟨trivial, h⟩
  · exact h

theorem g0_propose (p : P) (v : ℕ) {s : LState P V}
    (h : ∀ k ∈ s.known, G0 ℓ a k) : ∀ k ∈ (actPropose pr p v s).known, G0 ℓ a k := by
  unfold actPropose
  split_ifs with hh
  · exact forall_mem_insert _ _ _ |>.mpr ⟨fun hv => absurd hv hh.2.1, h⟩
  · exact h

theorem g0_ack (p : P) (v : ℕ) {s : LState P V}
    (h : ∀ k ∈ s.known, G0 ℓ a k) : ∀ k ∈ (actAck pr p v s).known, G0 ℓ a k := by
  unfold actAck
  split_ifs with hh
  · exact forall_mem_insert _ _ _ |>.mpr
      ⟨fun hv => (h _ (Classical.choose_spec hh.2).1 hv).2, h⟩
  · exact h

theorem g0_commit (p : P) (v : ℕ) {s : LState P V}
    (h : ∀ k ∈ s.known, G0 ℓ a k) : ∀ k ∈ (actCommit pr p v s).known, G0 ℓ a k := by
  unfold actCommit
  split_ifs
  · exact forall_mem_insert _ _ _ |>.mpr ⟨trivial, h⟩
  · exact h

theorem g0_stepFn (p : P) (s : LState P V) (ib : P → List (Tok P V))
    (hs : ∀ k ∈ s.known, G0 ℓ a k) (hib : ∀ r, ∀ k ∈ ib r, G0 ℓ a k) :
    ∀ k ∈ (stepFn pr L p s ib).known, G0 ℓ a k := by
  rw [stepFn_eq]
  simp only [Function.comp]
  apply g0_commit; apply g0_ack; apply g0_propose; apply g0_verify; apply g0_leaderCA
  apply g0_vote
  intro k hk
  rcases mem_union.mp hk with hk | hk
  · exact hs k hk
  · obtain ⟨q, -, hq⟩ := mem_biUnion.mp hk
    exact hib q k (List.mem_toFinset.mp hq)

theorem g0_init (I : P → V) (q : P) :
    ∀ k ∈ ((algo pr L).init q (I q)).known, G0 (pr.leader 0) (I (pr.leader 0)) k := by
  intro k hk
  simp only [algo] at hk
  split_ifs at hk with h
  · rw [mem_singleton] at hk
    subst hk h
    exact fun _ => ⟨rfl, rfl⟩
  · simp at hk

theorem g0_quiet (I : P → V) (q : P) : ∀ τ,
    ∀ k ∈ (quiet (algo pr L) q (I q) τ).known, G0 (pr.leader 0) (I (pr.leader 0)) k
  | 0 => g0_init I q
  | τ + 1 => g0_stepFn (pr := pr) (L := L) q _ _ (g0_quiet I q τ) (by simp)

theorem ack_actAck (p : P) (s : LState P V) {y : V}
    (hy : Tok.propose (pr.leader 0) y 0 ∈ s.known) :
    ∃ y', Tok.ack p y' 0 ∈ (actAck pr p 0 s).known := by
  unfold actAck
  split_ifs with h
  · exact ⟨_, mem_insert_self _ _⟩
  · by_contra hc
    push Not at hc
    exact h ⟨hc, y, hy, Or.inl rfl⟩

/-- **The protocol is `t`-two-step** (Section 4.1), for `δ ≥ 2` and views longer than `2δ + 1`. -/
theorem algo_twoStep (hδ : 2 ≤ δ) (hL : 2 * δ + 2 ≤ L) (ht : pr.t ≤ pr.f)
    (hn : 3 * pr.f + 2 * pr.t - 1 ≤ Fintype.card P) :
    TwoStep (algo (V := V) pr L) pr.t δ := by
  intro I T hT x hx
  set R := tsRun (algo (V := V) pr L) δ I T with hR
  set ℓ := pr.leader 0 with hℓ
  -- invariant: view-0 proposals and acks carry `I ℓ`
  have hinv : ∀ τ q, ∀ k ∈ (R.st (algo pr L) τ q).known, G0 ℓ (I ℓ) k := by
    intro τ
    induction τ using Nat.strong_induction_on with
    | _ τ ih =>
      intro q
      rcases τ with _ | τ
      · exact g0_init I q
      · rw [st_succ_eq]
        refine g0_stepFn q _ _ (ih τ (by omega) q) fun r k hk => ?_
        obtain ⟨σ, hσ, -, hk⟩ := Run.mem_inbox.mp hk
        by_cases hr : r ∈ T
        · rw [Run.out_of_faulty _ _ (show r ∈ R.faulty from hr)] at hk
          simp only [R, tsRun] at hk
          split_ifs at hk
          · exact g0_quiet I r σ k (by simpa [algo] using hk)
          · simp at hk
        · rw [out_correct _ (show r ∉ R.faulty from hr)] at hk
          exact ih σ (by omega) r k (by simpa using hk)
  -- every correct process acks in view 0 at step `δ`
  have hv0 : (δ + 1) / L = 0 := Nat.div_eq_of_lt (by omega)
  have hack : ∀ c ∉ T, Tok.ack c (I ℓ) 0 ∈ (R.st (algo pr L) (δ + 1) c).known := by
    intro c hc
    have hprop : Tok.propose ℓ (I ℓ) 0 ∈ R.inbox (algo pr L) c δ ℓ := by
      rw [Run.mem_inbox]
      refine ⟨0, Nat.zero_le _, nextRound_of_lt (by omega), ?_⟩
      by_cases hl : ℓ ∈ T
      · rw [Run.out_of_faulty _ _ (show ℓ ∈ R.faulty from hl)]
        simp [R, tsRun, show 0 < δ by omega, quiet, algo, hℓ]
      · rw [out_correct _ (show ℓ ∉ R.faulty from hl)]
        simp [algo, R, tsRun, hℓ]
    have hex : ∃ y, Tok.ack c y 0 ∈ (R.st (algo pr L) (δ + 1) c).known := by
      rw [st_succ_eq, stepFn_eq, st_clock, hv0]
      simp only [Function.comp]
      have hg := grows_comp (grows_propose (pr := pr) c 0) (grows_comp
        (grows_verify (pr := pr) c 0) (grows_comp (grows_leaderCA (pr := pr) c 0)
        (grows_vote (L := L) c (R.st (algo pr L) δ c) 0)))
      have hmem : Tok.propose (pr.leader 0) (I ℓ) 0 ∈ ({ R.st (algo pr L) δ c with
          clock := δ + 1, known := (R.st (algo pr L) δ c).known ∪
            univ.biUnion fun q => (R.inbox (algo pr L) c δ q).toFinset } : LState P V).known :=
        mem_union_right _ (mem_biUnion.mpr ⟨ℓ, mem_univ _, List.mem_toFinset.mpr hprop⟩)
      obtain ⟨y, hy⟩ := ack_actAck c _ ((hg _).1 hmem)
      exact ⟨y, (grows_commit c 0 _).1 hy⟩
    obtain ⟨y, hy⟩ := hex
    have := hinv _ _ _ hy rfl
    rwa [this] at hy
  -- the acks reach `x` at time `2δ`
  have hrecv : ∀ c ∉ T, Tok.ack c (I ℓ) 0 ∈ (R.st (algo pr L) (2 * δ + 1) x).known := by
    intro c hc
    apply mem_known_of_inbox (r := c)
    rw [Run.mem_inbox]
    refine ⟨δ + 1, by omega, nextRound_of_lt_two (by omega) (by omega), ?_⟩
    rw [out_correct _ (show c ∉ R.faulty from hc)]
    simpa using hack c hc
  have hD : Decided pr (↑(R.st (algo pr L) (2 * δ + 1) x).known : Set (Tok P V)) (I ℓ) := by
    refine ⟨0, Or.inl ?_⟩
    have hsub : univ \ T ⊆ ackers (↑(R.st (algo pr L) (2 * δ + 1) x).known : Set (Tok P V))
        (I ℓ) 0 := by
      intro c hc
      unfold ackers
      exact mem_filter_of' (mem_univ _) (hrecv c (mem_sdiff.mp hc).2)
    have := card_le_card hsub
    rwa [card_sdiff_of_subset (subset_univ T), card_univ, hT] at this
  have hex : ∃ y, Decided pr (↑(R.st (algo pr L) (2 * δ + 1) x).known : Set (Tok P V)) y :=
    ⟨_, hD⟩
  exact ⟨Classical.choose hex, 2 * δ + 1, le_rfl, dite_eq_left hex⟩

end TwoStepProof

end FastByzantineConsensus.Impl
