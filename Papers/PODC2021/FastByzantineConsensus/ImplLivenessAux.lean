import Papers.PODC2021.FastByzantineConsensus.Implementation

/-!
# Auxiliary lemmas for the termination proof of the concrete protocol

* shape of the actions (each action keeps `known` or inserts one token of a given form) and their
  progress properties (an enabled action adds a token);
* decomposition of a step of a run into reception and the six actions.
-/

set_option linter.unusedSectionVars false

namespace FastByzantineConsensus.Impl

open Cslib.Byzantine.PartialSync FastByzantineConsensus.Protocol Finset

variable {P V : Type*} [Fintype P] [DecidableEq P] [DecidableEq V]
variable {pr : Params P} {L δ : ℕ}

/-! ### Shape of the actions -/

section Shape

theorem actVote_shape (p : P) (old : LState P V) (v : ℕ) (s : LState P V) :
    (actVote L p old v s).known = s.known ∨
      ∃ b c, (actVote L p old v s).known = insert (Tok.vote p v b c) s.known := by
  unfold actVote; split_ifs
  · exact Or.inr ⟨_, _, rfl⟩
  · exact Or.inl rfl

theorem actVote_mem (p : P) (old : LState P V) (v : ℕ) (s : LState P V) (h : v ≠ old.clock / L) :
    Tok.vote p v s.ballot s.cc ∈ (actVote L p old v s).known := by
  unfold actVote; split_ifs
  · exact mem_insert_self _ _

theorem actLeaderCA_shape (p : P) (v : ℕ) (s : LState P V) :
    (actLeaderCA pr p v s).known = s.known ∨
      ∃ x, (actLeaderCA pr p v s).known = insert (Tok.certAck p x v) s.known ∧
        (∀ y, Tok.certAck p y v ∉ s.known) := by
  unfold actLeaderCA; split_ifs with h
  · exact Or.inr ⟨_, rfl, h.2.2.1⟩
  · exact Or.inl rfl

theorem actVerify_shape (p : P) (v : ℕ) (s : LState P V) :
    (actVerify pr p v s).known = s.known ∨
      ∃ x, (actVerify pr p v s).known = insert (Tok.certAck p x v) s.known ∧
        Tok.certAck (pr.leader v) x v ∈ s.known ∧ Tok.certAck p x v ∉ s.known := by
  unfold actVerify; split_ifs with h
  · exact Or.inr ⟨_, rfl, (Classical.choose_spec h).1, (Classical.choose_spec h).2.1⟩
  · exact Or.inl rfl

theorem actPropose_shape (p : P) (v : ℕ) (s : LState P V) :
    (actPropose pr p v s).known = s.known ∨
      ∃ x, (actPropose pr p v s).known = insert (Tok.propose p x v) s.known ∧
        Certified pr (↑s.known : Set (Tok P V)) x v := by
  unfold actPropose; split_ifs with h
  · exact Or.inr ⟨_, rfl, Classical.choose_spec h.2.2.2⟩
  · exact Or.inl rfl

theorem actAck_shape (p : P) (v : ℕ) (s : LState P V) :
    (actAck pr p v s).known = s.known ∨
      ∃ x, (actAck pr p v s).known = insert (Tok.ack p x v) s.known := by
  unfold actAck; split_ifs with h
  · exact Or.inr ⟨_, rfl⟩
  · exact Or.inl rfl

theorem actCommit_shape (p : P) (v : ℕ) (s : LState P V) :
    (actCommit pr p v s).known = s.known ∨
      ∃ x, (actCommit pr p v s).known = insert (Tok.commit p x v) s.known := by
  unfold actCommit; split_ifs with h
  · exact Or.inr ⟨_, rfl⟩
  · exact Or.inl rfl

end Shape

/-! ### Progress of the actions -/

section Progress

theorem Sel.mono {K K' : Finset (Tok P V)} (h : K ⊆ K') {v : ℕ} {x : V} (hs : Sel pr K v x) :
    Sel pr K' v x := by
  obtain ⟨S, bal, cc, h1, h2⟩ := hs
  exact ⟨S, bal, cc, ValidVotes.mono pr (by exact_mod_cast h) h1, h2⟩

theorem actLeaderCA_progress {p : P} {v : ℕ} {s : LState P V} (hl : pr.leader v = p)
    (hv : v ≠ 0) {x : V} (hx : Sel pr s.known v x) :
    ∃ y, Tok.certAck p y v ∈ (actLeaderCA pr p v s).known := by
  unfold actLeaderCA
  split_ifs with h
  · exact ⟨_, mem_insert_self _ _⟩
  · have : ¬ ∀ y, Tok.certAck p y v ∉ s.known := fun h' => h ⟨hl, hv, h', x, hx⟩
    push Not at this
    exact this

theorem actVerify_progress {p : P} {v : ℕ} {s : LState P V} {x : V}
    (hl : Tok.certAck (pr.leader v) x v ∈ s.known) (hx : Sel pr s.known v x) :
    ∃ y, Tok.certAck (pr.leader v) y v ∈ s.known ∧
      Tok.certAck p y v ∈ (actVerify pr p v s).known := by
  by_cases hm : Tok.certAck p x v ∈ s.known
  · exact ⟨x, hl, (grows_verify (pr := pr) p v s).1 hm⟩
  · have h : ∃ x, Tok.certAck (pr.leader v) x v ∈ s.known ∧ Tok.certAck p x v ∉ s.known ∧
        Sel pr s.known v x := ⟨x, hl, hm, hx⟩
    unfold actVerify
    split_ifs
    exact ⟨_, (Classical.choose_spec h).1, mem_insert_self _ _⟩

theorem actPropose_progress {p : P} {v : ℕ} {s : LState P V} (hl : pr.leader v = p)
    (hv : v ≠ 0) {x : V} (hx : Certified pr (↑s.known : Set (Tok P V)) x v) :
    ∃ y, Tok.propose p y v ∈ (actPropose pr p v s).known := by
  unfold actPropose
  split_ifs with h
  · exact ⟨_, mem_insert_self _ _⟩
  · have : ¬ ∀ y, Tok.propose p y v ∉ s.known := fun h' => h ⟨hl, hv, h', x, hx⟩
    push Not at this
    exact this

theorem actAck_progress {p : P} {v : ℕ} {s : LState P V} {x : V}
    (hp : Tok.propose (pr.leader v) x v ∈ s.known)
    (hx : Certified pr (↑s.known : Set (Tok P V)) x v) :
    ∃ y, Tok.ack p y v ∈ (actAck pr p v s).known := by
  unfold actAck
  split_ifs with h
  · exact ⟨_, mem_insert_self _ _⟩
  · have : ¬ ∀ y, Tok.ack p y v ∉ s.known := fun h' => h ⟨h', x, hp, Or.inr hx⟩
    push Not at this
    exact this

theorem actCommit_progress {p : P} {v : ℕ} {s : LState P V} {x : V}
    (hx : HasCC pr (↑s.known : Set (Tok P V)) x v) :
    ∃ y, HasCC pr (↑s.known : Set (Tok P V)) y v ∧
      Tok.commit p y v ∈ (actCommit pr p v s).known := by
  by_cases hm : Tok.commit p x v ∈ s.known
  · exact ⟨x, hx, (grows_commit (pr := pr) p v s).1 hm⟩
  · have h : ∃ x, HasCC pr (↑s.known : Set (Tok P V)) x v ∧ Tok.commit p x v ∉ s.known :=
      ⟨x, hx, hm⟩
    unfold actCommit
    split_ifs
    exact ⟨_, (Classical.choose_spec h).1, mem_insert_self _ _⟩

end Progress

/-! ### Decomposition of a step of a run -/

section Decomp

variable (R : Run P (Tok P V) V)

/-- The state after a step, as the six actions applied to the state after reception. -/
theorem st_succ_decomp (τ : ℕ) (q : P) :
    ∃ s1 : LState P V, (R.st (algo pr L) τ q).known ⊆ s1.known ∧
      (∀ k ∈ s1.known, k ∈ (R.st (algo pr L) τ q).known ∨ ∃ r, k ∈ R.inbox (algo pr L) q τ r) ∧
      s1.ballot = (R.st (algo pr L) τ q).ballot ∧ s1.cc = (R.st (algo pr L) τ q).cc ∧
      R.st (algo pr L) (τ + 1) q = actCommit pr q ((τ + 1) / L) (actAck pr q ((τ + 1) / L)
        (actPropose pr q ((τ + 1) / L) (actVerify pr q ((τ + 1) / L)
        (actLeaderCA pr q ((τ + 1) / L) (actVote L q (R.st (algo pr L) τ q) ((τ + 1) / L) s1))))) := by
  refine ⟨{ R.st (algo pr L) τ q with clock := τ + 1, known := (R.st (algo pr L) τ q).known ∪
      (univ.biUnion fun r => (R.inbox (algo pr L) q τ r).toFinset) }, subset_union_left, ?_, rfl, rfl,
      ?_⟩
  · intro k hk
    rcases mem_union.mp hk with h | h
    · exact Or.inl h
    · obtain ⟨r, -, hr⟩ := mem_biUnion.mp h
      exact Or.inr ⟨r, List.mem_toFinset.mp hr⟩
  · rw [st_succ_eq, stepFn_eq, st_clock]
    rfl

end Decomp


/-! ### Chains of actions only grow `known` -/

section Chain

theorem sub_chain1 (p : P) (v : ℕ) (X : LState P V) : X.known ⊆ (actCommit pr p v X).known :=
  (grows_commit p v X).1

theorem sub_chain2 (p : P) (v : ℕ) (X : LState P V) :
    X.known ⊆ (actCommit pr p v (actAck pr p v X)).known :=
  (grows_ack p v X).1.trans (sub_chain1 p v _)

theorem sub_chain3 (p : P) (v : ℕ) (X : LState P V) :
    X.known ⊆ (actCommit pr p v (actAck pr p v (actPropose pr p v X))).known :=
  (grows_propose p v X).1.trans (sub_chain2 p v _)

theorem sub_chain4 (p : P) (v : ℕ) (X : LState P V) :
    X.known ⊆ (actCommit pr p v (actAck pr p v (actPropose pr p v (actVerify pr p v X)))).known :=
  (grows_verify p v X).1.trans (sub_chain3 p v _)

theorem sub_chain5 (p : P) (v : ℕ) (X : LState P V) :
    X.known ⊆ (actCommit pr p v (actAck pr p v (actPropose pr p v (actVerify pr p v
      (actLeaderCA pr p v X))))).known :=
  (grows_leaderCA p v X).1.trans (sub_chain4 p v _)

theorem sub_chain6 (p : P) (old : LState P V) (v : ℕ) (X : LState P V) :
    X.known ⊆ (actCommit pr p v (actAck pr p v (actPropose pr p v (actVerify pr p v
      (actLeaderCA pr p v (actVote L p old v X)))))).known :=
  (grows_vote p old v X).1.trans (sub_chain5 p v _)

end Chain

/-! ### Run-level lemmas -/

section RunLemmas

variable (pr L) in
/-- Tokens signed by a correct process `q` and known to a correct process are known to `q`
(this is `known_signed` of `ImplSafety.lean`; here it is a hypothesis). -/
def KnownSigned (R : Run P (Tok P V) V) : Prop :=
  ∀ q c τ (k : Tok P V), q ∉ R.faulty → c ∉ R.faulty → k ∈ (R.st (algo pr L) τ c).known →
    k.signer = q → k ∈ (R.st (algo pr L) τ q).known

variable {R : Run P (Tok P V) V}

/-- A received token signed by the (correct) receiver is already known to it. -/
theorem inbox_signed (hRa : R.AuthValid auth (algo pr L)) (hsig : KnownSigned pr L R) {q r : P}
    (hq : q ∉ R.faulty) {τ : ℕ} {k : Tok P V} (hk : k ∈ R.inbox (algo pr L) q τ r)
    (hs : k.signer = q) : k ∈ (R.st (algo pr L) τ q).known := by
  obtain ⟨σ, hσ, -, hm⟩ := Run.mem_inbox.mp hk
  by_cases hr : r ∈ R.faulty
  · rw [Run.out_of_faulty (algo pr L) R hr] at hm
    rcases hRa r hr σ q hq k hm k (Set.mem_singleton k) with h | ⟨σ', hσ', q', hq', r', m, hm', hkm⟩
    · exact absurd (hs ▸ h) hq
    · have hkm' : k = m := Set.mem_singleton_iff.mp hkm
      subst hkm'
      rw [out_correct R hq'] at hm'
      exact known_mono R (by omega) q (hsig q q' σ' k hq hq' (Finset.mem_toList.mp hm') hs)
  · rw [out_correct R hr] at hm
    exact known_mono R hσ q (hsig q r σ k hq hr (Finset.mem_toList.mp hm) hs)

/-- **Gossip.** After GST, what a correct process knows at `τ` is known to every correct process
at `τ + δ + 1`. -/
theorem gossip (hR : R.Valid pr.f δ) {p q : P} (hp : p ∉ R.faulty) (hq : q ∉ R.faulty) {τ : ℕ}
    (hτ : R.gst ≤ τ) :
    (R.st (algo pr L) τ p).known ⊆ (R.st (algo pr L) (τ + δ + 1) q).known := by
  intro k hk
  have h1 := hR.dl_ge p τ q hp hq
  have h2 := hR.dl_le p τ q hp hq
  rw [max_eq_left hτ] at h2
  have : k ∈ R.inbox (algo pr L) q (R.dl p τ q) p :=
    Run.mem_inbox.mpr ⟨τ, h1, rfl, by rw [out_correct R hp]; exact Finset.mem_toList.mpr hk⟩
  exact known_mono R (by omega) q (mem_known_of_inbox R this)

theorem mem_E {c : P} (hc : c ∉ R.faulty) {τ : ℕ} {k : Tok P V}
    (hk : k ∈ (R.st (algo pr L) τ c).known) : k ∈ (absState pr L R τ).E :=
  ⟨c, hc, hk⟩

theorem coe_sub_E {c : P} (hc : c ∉ R.faulty) (τ : ℕ) :
    (↑(R.st (algo pr L) τ c).known : Set (Tok P V)) ⊆ (absState pr L R τ).E :=
  fun _ hk => mem_E hc hk

theorem E_mono {τ τ' : ℕ} (h : τ ≤ τ') : (absState pr L R τ).E ⊆ (absState pr L R τ').E := by
  rintro k ⟨c, hc, hk⟩
  exact ⟨c, hc, known_mono R h c hk⟩

theorem E_sub (hR : R.Valid pr.f δ) {q : P} (hq : q ∉ R.faulty) {τ : ℕ} (hτ : R.gst ≤ τ) :
    (absState pr L R τ).E ⊆ ↑(R.st (algo pr L) (τ + δ + 1) q).known := by
  rintro k ⟨c, hc, hk⟩
  exact gossip hR hc hq hτ hk

theorem E_sub_le (hR : R.Valid pr.f δ) {q : P} (hq : q ∉ R.faulty) {τ T : ℕ} (hτ : R.gst ≤ τ)
    (hT : τ + δ + 1 ≤ T) : (absState pr L R τ).E ⊆ ↑(R.st (algo pr L) T q).known :=
  (E_sub hR hq hτ).trans (Finset.coe_subset.mpr (known_mono R hT q))

theorem loc_absState {c : P} (hc : c ∉ R.faulty) (τ : ℕ) :
    (absState pr L R τ).loc c =
      ⟨τ / L, (R.st (algo pr L) τ c).ballot, (R.st (algo pr L) τ c).cc⟩ := by
  simp [absState, hc]

end RunLemmas

/-! ### The leader's invariant: one `CertAck` per view, certified proposals -/

section LeaderInv

variable (pr) in
/-- Invariant of the known tokens `K` of the correct leader `p` of view `v ≠ 0`: it signed at most
one `CertAck` in view `v`, and its proposals of view `v` are certified. -/
def LInv (p : P) (v : ℕ) (K : Finset (Tok P V)) : Prop :=
  (∀ x y, Tok.certAck p x v ∈ K → Tok.certAck p y v ∈ K → x = y) ∧
    ∀ y, Tok.propose p y v ∈ K → Certified pr (↑K : Set (Tok P V)) y v

theorem LInv.ins {p : P} {v : ℕ} {K : Finset (Tok P V)} (h : LInv pr p v K) {k : Tok P V}
    (hc : ∀ x, k = Tok.certAck p x v → ∀ y, Tok.certAck p y v ∉ K)
    (hp : ∀ x, k = Tok.propose p x v → Certified pr (↑K : Set (Tok P V)) x v) :
    LInv pr p v (insert k K) := by
  have hsub : (↑K : Set (Tok P V)) ⊆ ↑(insert k K) :=
    Finset.coe_subset.mpr (Finset.subset_insert _ _)
  refine ⟨fun x y hx hy => ?_, fun y hy => ?_⟩
  · rcases mem_insert.mp hx with hx | hx <;> rcases mem_insert.mp hy with hy | hy
    · have := hx.trans hy.symm
      simpa using this
    · exact absurd hy (hc x hx.symm y)
    · exact absurd hx (hc y hy.symm x)
    · exact h.1 x y hx hy
  · rcases mem_insert.mp hy with hy | hy
    · exact Certified.mono pr hsub (hp y hy.symm)
    · exact Certified.mono pr hsub (h.2 y hy)

theorem LInv.of_sub {p : P} {v : ℕ} {K K' : Finset (Tok P V)} (h : LInv pr p v K) (hsub : K ⊆ K')
    (hback : ∀ k ∈ K', k.signer = p → k ∈ K) : LInv pr p v K' := by
  refine ⟨fun x y hx hy => h.1 x y (hback _ hx rfl) (hback _ hy rfl), fun y hy => ?_⟩
  exact Certified.mono pr (Finset.coe_subset.mpr hsub) (h.2 y (hback _ hy rfl))

theorem linv_vote {p : P} {v : ℕ} (old : LState P V) (v' : ℕ) (s : LState P V)
    (h : LInv pr p v s.known) : LInv pr p v (actVote L p old v' s).known := by
  rcases actVote_shape p old v' s with e | ⟨b, c, e⟩ <;> rw [e]
  · exact h
  · exact h.ins (fun x hx => by cases hx) (fun x hx => by cases hx)

theorem linv_leaderCA {p : P} {v : ℕ} (v' : ℕ) (s : LState P V) (h : LInv pr p v s.known) :
    LInv pr p v (actLeaderCA pr p v' s).known := by
  rcases actLeaderCA_shape (pr := pr) p v' s with e | ⟨x, e, hg⟩ <;> rw [e]
  · exact h
  · refine h.ins (fun x' hx' => ?_) (fun x' hx' => by cases hx')
    injection hx' with h1 h2 h3
    subst h3
    exact hg

theorem linv_verify {p : P} {v : ℕ} (hl : pr.leader v = p) (v' : ℕ) (s : LState P V)
    (h : LInv pr p v s.known) : LInv pr p v (actVerify pr p v' s).known := by
  rcases actVerify_shape (pr := pr) p v' s with e | ⟨x, e, hm, hn⟩ <;> rw [e]
  · exact h
  · refine h.ins (fun x' hx' => ?_) (fun x' hx' => by cases hx')
    injection hx' with h1 h2 h3
    subst h3
    rw [hl] at hm
    exact absurd hm hn

theorem linv_propose {p : P} {v : ℕ} (v' : ℕ) (s : LState P V) (h : LInv pr p v s.known) :
    LInv pr p v (actPropose pr p v' s).known := by
  rcases actPropose_shape (pr := pr) p v' s with e | ⟨x, e, hc⟩ <;> rw [e]
  · exact h
  · refine h.ins (fun x' hx' => by cases hx') (fun x' hx' => ?_)
    injection hx' with h1 h2 h3
    subst h2 h3
    exact hc

theorem linv_ack {p : P} {v : ℕ} (v' : ℕ) (s : LState P V) (h : LInv pr p v s.known) :
    LInv pr p v (actAck pr p v' s).known := by
  rcases actAck_shape (pr := pr) p v' s with e | ⟨x, e⟩ <;> rw [e]
  · exact h
  · exact h.ins (fun x hx => by cases hx) (fun x hx => by cases hx)

theorem linv_commit {p : P} {v : ℕ} (v' : ℕ) (s : LState P V) (h : LInv pr p v s.known) :
    LInv pr p v (actCommit pr p v' s).known := by
  rcases actCommit_shape (pr := pr) p v' s with e | ⟨x, e⟩ <;> rw [e]
  · exact h
  · exact h.ins (fun x hx => by cases hx) (fun x hx => by cases hx)

variable {R : Run P (Tok P V) V}

/-- The leader invariant holds at all times. -/
theorem linv_all (hRa : R.AuthValid auth (algo pr L)) (hsig : KnownSigned pr L R) {p : P}
    (hp : p ∉ R.faulty) {v : ℕ} (hv : v ≠ 0) (hl : pr.leader v = p) :
    ∀ τ, LInv pr p v (R.st (algo pr L) τ p).known := by
  intro τ
  induction τ with
  | zero =>
    show LInv pr p v (if pr.leader 0 = p then {Tok.propose p (R.inp p) 0} else ∅)
    split_ifs
    · refine ⟨fun x y hx => by simp at hx, fun y hy => ?_⟩
      simp only [mem_singleton, Tok.propose.injEq] at hy
      exact absurd hy.2.2 hv
    · exact ⟨fun x y hx => by simp at hx, fun y hy => by simp at hy⟩
  | succ τ ih =>
    obtain ⟨s1, hsub, hback, -, -, e⟩ := st_succ_decomp (pr := pr) (L := L) R τ p
    have h1 : LInv pr p v s1.known := ih.of_sub hsub fun k hk hs => by
      rcases hback k hk with h | ⟨r, hr⟩
      · exact h
      · exact inbox_signed hRa hsig hp hr hs
    rw [e]
    exact linv_commit _ _ (linv_ack _ _ (linv_propose _ _ (linv_verify hl _ _
      (linv_leaderCA _ _ (linv_vote _ _ _ h1)))))

end LeaderInv

/-! ### One step of a correct process in a view -/

section Steps

variable {R : Run P (Tok P V) V} {c : P} {τ v : ℕ}

theorem view_eq (h1 : v * L ≤ τ + 1) (h2 : τ + 1 < v * L + L) : (τ + 1) / L = v :=
  Nat.div_eq_of_lt_le h1 (by rw [Nat.add_mul, one_mul]; exact h2)

/-- Entering view `v`: the vote. -/
theorem step_vote (hv : (τ + 1) / L = v) (hne : v ≠ τ / L) :
    Tok.vote c v (R.st (algo pr L) τ c).ballot (R.st (algo pr L) τ c).cc ∈
      (R.st (algo pr L) (τ + 1) c).known := by
  obtain ⟨s1, -, -, hb, hc, e⟩ := st_succ_decomp (pr := pr) (L := L) R τ c
  rw [e, hv]
  apply sub_chain5
  rw [← hb, ← hc]
  exact actVote_mem c _ v s1 (by rw [st_clock]; exact hne)

/-- The leader signs a `CertAck` once a selection is possible. -/
theorem step_leaderCA (hv : (τ + 1) / L = v) (hl : pr.leader v = c) (hv0 : v ≠ 0) {x : V}
    (hx : Sel pr (R.st (algo pr L) τ c).known v x) :
    ∃ y, Tok.certAck c y v ∈ (R.st (algo pr L) (τ + 1) c).known := by
  obtain ⟨s1, hsub, -, -, -, e⟩ := st_succ_decomp (pr := pr) (L := L) R τ c
  rw [e, hv]
  obtain ⟨y, hy⟩ := actLeaderCA_progress (s := actVote L c (R.st (algo pr L) τ c) v s1) hl hv0
    (hx.mono (hsub.trans (grows_vote c _ v s1).1))
  exact ⟨y, sub_chain4 c v _ hy⟩

/-- A verifier signs a `CertAck` for a value the leader certified. -/
theorem step_verify (hv : (τ + 1) / L = v) {x : V}
    (hl : Tok.certAck (pr.leader v) x v ∈ (R.st (algo pr L) τ c).known)
    (hx : Sel pr (R.st (algo pr L) τ c).known v x) :
    ∃ y, Tok.certAck (pr.leader v) y v ∈ (R.st (algo pr L) (τ + 1) c).known ∧
      Tok.certAck c y v ∈ (R.st (algo pr L) (τ + 1) c).known := by
  obtain ⟨s1, hsub, -, -, -, e⟩ := st_succ_decomp (pr := pr) (L := L) R τ c
  rw [e, hv]
  have hX : (R.st (algo pr L) τ c).known ⊆
      (actLeaderCA pr c v (actVote L c (R.st (algo pr L) τ c) v s1)).known :=
    hsub.trans ((grows_vote c _ v s1).1.trans (grows_leaderCA c v _).1)
  obtain ⟨y, hy1, hy2⟩ := actVerify_progress (p := c) (hX hl) (hx.mono hX)
  exact ⟨y, sub_chain4 c v _ hy1, sub_chain3 c v _ hy2⟩

/-- The leader proposes once it has a progress certificate. -/
theorem step_propose (hv : (τ + 1) / L = v) (hl : pr.leader v = c) (hv0 : v ≠ 0) {x : V}
    (hx : Certified pr (↑(R.st (algo pr L) τ c).known : Set (Tok P V)) x v) :
    ∃ y, Tok.propose c y v ∈ (R.st (algo pr L) (τ + 1) c).known := by
  obtain ⟨s1, hsub, -, -, -, e⟩ := st_succ_decomp (pr := pr) (L := L) R τ c
  rw [e, hv]
  have hX : (R.st (algo pr L) τ c).known ⊆ (actVerify pr c v
      (actLeaderCA pr c v (actVote L c (R.st (algo pr L) τ c) v s1))).known :=
    hsub.trans ((grows_vote c _ v s1).1.trans ((grows_leaderCA c v _).1.trans
      (grows_verify c v _).1))
  obtain ⟨y, hy⟩ := actPropose_progress (p := c) hl hv0
    (Certified.mono pr (Finset.coe_subset.mpr hX) hx)
  exact ⟨y, sub_chain2 c v _ hy⟩

/-- A process acknowledges once it knows a certified proposal of the view. -/
theorem step_ack (hv : (τ + 1) / L = v) {x : V}
    (hp : Tok.propose (pr.leader v) x v ∈ (R.st (algo pr L) τ c).known)
    (hx : Certified pr (↑(R.st (algo pr L) τ c).known : Set (Tok P V)) x v) :
    ∃ y, Tok.ack c y v ∈ (R.st (algo pr L) (τ + 1) c).known := by
  obtain ⟨s1, hsub, -, -, -, e⟩ := st_succ_decomp (pr := pr) (L := L) R τ c
  rw [e, hv]
  have hX : (R.st (algo pr L) τ c).known ⊆ (actPropose pr c v (actVerify pr c v
      (actLeaderCA pr c v (actVote L c (R.st (algo pr L) τ c) v s1)))).known :=
    hsub.trans ((grows_vote c _ v s1).1.trans ((grows_leaderCA c v _).1.trans
      ((grows_verify c v _).1.trans (grows_propose c v _).1)))
  obtain ⟨y, hy⟩ := actAck_progress (p := c) (hX hp)
    (Certified.mono pr (Finset.coe_subset.mpr hX) hx)
  exact ⟨y, sub_chain1 c v _ hy⟩

/-- A process sends `Commit` once it knows a commit certificate of the view. -/
theorem step_commit (hv : (τ + 1) / L = v) {x : V}
    (hx : HasCC pr (↑(R.st (algo pr L) τ c).known : Set (Tok P V)) x v) :
    ∃ y, HasCC pr (↑(R.st (algo pr L) (τ + 1) c).known : Set (Tok P V)) y v ∧
      Tok.commit c y v ∈ (R.st (algo pr L) (τ + 1) c).known := by
  obtain ⟨s1, hsub, -, -, -, e⟩ := st_succ_decomp (pr := pr) (L := L) R τ c
  rw [e, hv]
  have hX : (R.st (algo pr L) τ c).known ⊆ (actAck pr c v (actPropose pr c v (actVerify pr c v
      (actLeaderCA pr c v (actVote L c (R.st (algo pr L) τ c) v s1))))).known :=
    hsub.trans ((grows_vote c _ v s1).1.trans ((grows_leaderCA c v _).1.trans
      ((grows_verify c v _).1.trans ((grows_propose c v _).1.trans (grows_ack c v _).1))))
  obtain ⟨y, hy1, hy2⟩ := actCommit_progress (p := c)
    (HasCC.mono pr (Finset.coe_subset.mpr hX) hx)
  exact ⟨y, HasCC.mono pr (Finset.coe_subset.mpr (sub_chain1 c v _)) hy1, hy2⟩

end Steps

/-! ### Existence of a selection -/

omit [DecidableEq V] in
open Classical in
/-- On a vote set in which only processes outside `S` equivocated (two different values acked in
the same view), the selection algorithm has an outcome. -/
theorem exists_selects (v : ℕ) (S : Finset P) (bal cc : P → Option (V × ℕ)) (x₀ : V)
    (hS : Fintype.card P - pr.f ≤ S.card)
    (heq : ∀ s₁ ∈ S, ∀ s₂ ∈ S, ∀ y₁ y₂ w, bal s₁ = some (y₁, w) → bal s₂ = some (y₂, w) →
      y₁ ≠ y₂ → pr.leader w ∉ S) :
    ∃ x, Selects pr v S bal cc x := by
  by_cases hnil : ∀ s ∈ S, bal s = none
  · exact ⟨x₀, Or.inl hnil⟩
  push Not at hnil
  obtain ⟨s₀', hs₀', hb₀'⟩ := hnil
  let g : P → ℕ := fun s => ((bal s).map Prod.snd).getD 0
  have hne : (S.filter fun s => bal s ≠ none).Nonempty := ⟨s₀', mem_filter.mpr ⟨hs₀', hb₀'⟩⟩
  obtain ⟨s₀, hs₀, hmax⟩ := exists_max_image _ g hne
  obtain ⟨hs₀S, hb₀⟩ := mem_filter.mp hs₀
  obtain ⟨⟨y₀, w⟩, hyw⟩ := Option.ne_none_iff_exists'.mp hb₀
  have hgw : g s₀ = w := by simp [g, hyw]
  have hw : ∃ s ∈ S, ∃ y, bal s = some (y, w) := ⟨s₀, hs₀S, y₀, hyw⟩
  have hmax' : ∀ s ∈ S, ∀ y u, bal s = some (y, u) → u ≤ w := by
    intro s hs y u h
    have := hmax s (mem_filter.mpr ⟨hs, by simp [h]⟩)
    simpa [g, h, hgw] using this
  by_cases hsingle : ∀ s ∈ S, ∀ y, bal s = some (y, w) → y = y₀
  · exact ⟨y₀, Or.inr ⟨w, hw, hmax', Or.inl hsingle⟩⟩
  push Not at hsingle
  obtain ⟨s₁, hs₁, y₁, hb₁, hy₁⟩ := hsingle
  have hl : pr.leader w ∉ S := heq s₁ hs₁ s₀ hs₀S y₁ y₀ w hb₁ hyw hy₁
  have hE : S.erase (pr.leader w) = S := erase_eq_of_notMem hl
  have hequiv : ∃ s₁ ∈ S, ∃ s₂ ∈ S, ∃ y₁ y₂, bal s₁ = some (y₁, w) ∧ bal s₂ = some (y₂, w) ∧
      y₁ ≠ y₂ := ⟨s₁, hs₁, s₀, hs₀S, y₁, y₀, hb₁, hyw, hy₁⟩
  have hcard : Fintype.card P - pr.f ≤ (S.erase (pr.leader w)).card := by rw [hE]; exact hS
  by_cases h1 : ∃ s ∈ S.erase (pr.leader w), ∃ x, cc s = some (x, w)
  · obtain ⟨s, hs, x, hx⟩ := h1
    exact ⟨x, Or.inr ⟨w, hw, hmax', Or.inr ⟨hequiv, hcard, Or.inl ⟨s, hs, hx⟩⟩⟩⟩
  have h1' : ∀ s ∈ S.erase (pr.leader w), ∀ y, cc s ≠ some (y, w) := by
    intro s hs y h; exact h1 ⟨s, hs, y, h⟩
  by_cases h2 : ∃ x, pr.f + pr.t ≤
      ((S.erase (pr.leader w)).filter fun s => bal s = some (x, w)).card
  · obtain ⟨x, hx⟩ := h2
    exact ⟨x, Or.inr ⟨w, hw, hmax', Or.inr ⟨hequiv, hcard, Or.inr (Or.inl ⟨h1', hx⟩)⟩⟩⟩
  · push Not at h2
    exact ⟨y₀, Or.inr ⟨w, hw, hmax', Or.inr ⟨hequiv, hcard, Or.inr (Or.inr ⟨h1', h2⟩)⟩⟩⟩

/-! ### Termination -/

section Main

variable {R : Run P (Tok P V) V}

/-- **Termination**, given the facts `known_signed` and `reachable_absState` of `ImplSafety.lean`
(as hypotheses `hsig`, `hinv`). The first view `v` starting after GST whose leader is `ℓ`
completes within `6δ + 12` time units. -/
theorem termination_of (hL : 6 * δ + 12 ≤ L)
    (hlead : ∀ v₀ q, ∃ v ≥ v₀, pr.leader v = q) (ht : 1 ≤ pr.t)
    (hn : 3 * pr.f + 2 * pr.t - 1 ≤ Fintype.card P)
    (hR : R.Valid pr.f δ) (hRa : R.AuthValid auth (algo pr L)) (hsig : KnownSigned pr L R)
    (hinv : ∀ τ, Inv pr R.faulty (absState pr L R τ)) :
    ∀ p ∉ R.faulty, ∃ v, R.Decides (algo pr L) p v := by
  intro ℓ hℓ
  have hL0 : 0 < L := by omega
  obtain ⟨v, hv, hlv⟩ := hlead (R.gst / L + 1) ℓ
  have hv0 : v ≠ 0 := Nat.pos_iff_ne_zero.mp (Nat.le_trans (Nat.le_add_left 1 _) hv)
  obtain ⟨s, hs⟩ : ∃ s, s = v * L := ⟨_, rfl⟩
  have hgs : R.gst < s := by
    have h1 := Nat.div_add_mod' R.gst L
    have h2 := Nat.mod_lt R.gst hL0
    have h3 : (R.gst / L + 1) * L ≤ v * L := Nat.mul_le_mul_right L hv
    rw [Nat.add_mul, one_mul] at h3
    omega
  have hB := hR.card_faulty
  -- the correct processes
  let C : Finset P := univ.filter (· ∉ R.faulty)
  have hmemC : ∀ c, c ∈ C ↔ c ∉ R.faulty := by simp [C]
  have hCcard : Fintype.card P - pr.f ≤ C.card := by
    have h1 : univ ⊆ C ∪ R.faulty := fun c _ => by
      by_cases h : c ∈ R.faulty <;> simp [C, h]
    have h2 := card_le_card h1
    have h3 := card_union_le C R.faulty
    rw [card_univ] at h2
    omega
  have hqc : pr.qc ≤ Fintype.card P - pr.f := by unfold Params.qc; omega
  have hfq : pr.f + 1 ≤ pr.qc := by unfold Params.qc; omega
  have hfC : pr.f + 1 ≤ Fintype.card P - pr.f := by omega
  -- the step entering view `v`
  obtain ⟨τ0, hτ0⟩ : ∃ τ0, τ0 + 1 = s := ⟨s - 1, by omega⟩
  have hτ0v : (τ0 + 1) / L = v := by rw [hτ0, hs]; exact Nat.mul_div_cancel v hL0
  have hτ0L : τ0 / L < v := (Nat.div_lt_iff_lt_mul hL0).mpr (by omega)
  let bal : P → Option (V × ℕ) := fun c => (R.st (algo pr L) τ0 c).ballot
  let cc : P → Option (V × ℕ) := fun c => (R.st (algo pr L) τ0 c).cc
  have I0 := hinv τ0
  have hsub0 := E_mono (pr := pr) (L := L) (R := R) (Nat.le_succ τ0)
  have hVV : ValidVotes pr (absState pr L R (τ0 + 1)).E v C bal cc := by
    refine ⟨hCcard, fun c hc => ?_⟩
    have hc' := (hmemC c).mp hc
    have hloc := loc_absState (pr := pr) (L := L) hc' τ0
    refine ⟨mem_E hc' (step_vote hτ0v (by omega)), ?_, ?_⟩
    · show ValidBallot pr _ v (R.st (algo pr L) τ0 c).ballot
      rcases hb : (R.st (algo pr L) τ0 c).ballot with _ | ⟨x, u⟩
      · trivial
      · have h := I0.ballot_loc c hc' x u (by rw [hloc]; exact hb)
        rw [hloc] at h
        have hu : u ≤ τ0 / L := h.2
        obtain ⟨h1, h2⟩ := I0.ack_valid c hc' x u h.1
        exact ⟨by omega, hsub0 h1, h2.imp id (Certified.mono pr hsub0)⟩
    · show ValidCC pr _ v (R.st (algo pr L) τ0 c).cc
      rcases hb : (R.st (algo pr L) τ0 c).cc with _ | ⟨x, u⟩
      · trivial
      · have h := I0.cc_loc c hc' x u (by rw [hloc]; exact hb)
        rw [hloc] at h
        have hu : u ≤ τ0 / L := h.2
        exact ⟨by omega, HasCC.mono pr hsub0 h.1⟩
  obtain ⟨x₁, hx₁⟩ := exists_selects (pr := pr) v C bal cc (R.inp ℓ) hCcard (by
    intro s₁ hs₁ s₂ hs₂ y₁ y₂ w hb₁ hb₂ hne hlw
    have hlw' := (hmemC _).mp hlw
    have hc1 := (hmemC _).mp hs₁
    have hc2 := (hmemC _).mp hs₂
    have a1 := (I0.ballot_loc s₁ hc1 y₁ w (by rw [loc_absState hc1]; exact hb₁)).1
    have a2 := (I0.ballot_loc s₂ hc2 y₂ w (by rw [loc_absState hc2]; exact hb₂)).1
    exact hne (I0.propose_uniq _ hlw' y₁ y₂ w (I0.ack_valid _ hc1 _ _ a1).1
      (I0.ack_valid _ hc2 _ _ a2).1))
  -- the leader's `CertAck` (step at `T1`)
  obtain ⟨T1, hT1⟩ : ∃ T, T = s + δ + 1 := ⟨_, rfl⟩
  have hsel1 : Sel pr (R.st (algo pr L) T1 ℓ).known v x₁ :=
    ⟨C, bal, cc, ValidVotes.mono pr (E_sub_le hR hℓ (by omega) (by omega)) hVV, hx₁⟩
  obtain ⟨xs, hxs⟩ := step_leaderCA (view_eq (by omega) (by omega)) hlv hv0 hsel1
  obtain ⟨S', bal', cc', hVV', hsel'⟩ :=
    (hinv (T1 + 1)).certAck_valid ℓ hℓ xs v (mem_E hℓ hxs)
  have hLI := linv_all hRa hsig hℓ hv0 hlv
  -- the verifiers' `CertAck`s (steps at `T2`)
  obtain ⟨T2, hT2⟩ : ∃ T, T = T1 + 1 + δ + 1 := ⟨_, rfl⟩
  have hca : ∀ c ∉ R.faulty, Tok.certAck c xs v ∈ (R.st (algo pr L) (T2 + 1) c).known := by
    intro c hc
    have hE := E_sub_le (L := L) (q := c) hR hc (τ := T1 + 1) (T := T2) (by omega) (by omega)
    have hl : Tok.certAck (pr.leader v) xs v ∈ (R.st (algo pr L) T2 c).known := by
      rw [hlv]; exact hE (mem_E hℓ hxs)
    obtain ⟨y, hy1, hy2⟩ := step_verify (view_eq (by omega) (by omega)) hl
      ⟨S', bal', cc', ValidVotes.mono pr hE hVV', hsel'⟩
    rw [hlv] at hy1
    have e : y = xs := (hLI (T2 + 1)).1 y xs (hsig ℓ c _ _ hℓ hc hy1 rfl)
      (known_mono R (by omega) ℓ hxs)
    rw [e] at hy2
    exact hy2
  -- the proposal (step at `T3`)
  obtain ⟨T3, hT3⟩ : ∃ T, T = T2 + 1 + δ + 1 := ⟨_, rfl⟩
  have hcert : Certified pr (↑(R.st (algo pr L) T3 ℓ).known : Set (Tok P V)) xs v := by
    refine le_trans hfC (le_trans hCcard (card_le_card fun c hc => ?_))
    have hc' := (hmemC c).mp hc
    exact mem_certAckers.mpr (Finset.mem_coe.mpr (gossip hR hc' hℓ (τ := T2 + 1) (by omega)
      |>.trans (known_mono R (by omega) ℓ) (hca c hc')))
  obtain ⟨y, hy⟩ := step_propose (view_eq (by omega) (by omega)) hlv hv0 hcert
  have hyc : Certified pr (↑(R.st (algo pr L) (T3 + 1) ℓ).known : Set (Tok P V)) y v :=
    (hLI (T3 + 1)).2 y hy
  -- all acknowledgements of view `v` by correct processes are for `y`
  have huniq : ∀ τ z, ∀ c ∉ R.faulty, Tok.ack c z v ∈ (absState pr L R τ).E → T3 + 1 ≤ τ →
      z = y := by
    intro τ z c hc h hτ
    have h1 := ((hinv τ).ack_valid c hc z v h).1
    rw [hlv] at h1
    exact (hinv τ).propose_uniq ℓ hℓ z y v h1 (E_mono hτ (mem_E hℓ hy))
  -- the acknowledgements (steps at `T4`)
  obtain ⟨T4, hT4⟩ : ∃ T, T = T3 + 1 + δ + 1 := ⟨_, rfl⟩
  have hack : ∀ c ∉ R.faulty, Tok.ack c y v ∈ (R.st (algo pr L) (T4 + 1) c).known := by
    intro c hc
    have hE := E_sub_le (L := L) (q := c) hR hc (τ := T3 + 1) (T := T4) (by omega) (by omega)
    have hp : Tok.propose (pr.leader v) y v ∈ (R.st (algo pr L) T4 c).known := by
      rw [hlv]; exact hE (mem_E hℓ hy)
    obtain ⟨y', hy'⟩ := step_ack (view_eq (by omega) (by omega)) hp
      (Certified.mono pr ((coe_sub_E hℓ _).trans hE) hyc)
    have e : y' = y := huniq _ y' c hc (mem_E hc hy') (by omega)
    rw [e] at hy'
    exact hy'
  -- the commits (steps at `T5`)
  obtain ⟨T5, hT5⟩ : ∃ T, T = T4 + 1 + δ + 1 := ⟨_, rfl⟩
  have hcom : ∀ c ∉ R.faulty, Tok.commit c y v ∈ (R.st (algo pr L) (T5 + 1) c).known := by
    intro c hc
    have hcc : HasCC pr (↑(R.st (algo pr L) T5 c).known : Set (Tok P V)) y v := by
      refine le_trans hqc (le_trans hCcard (card_le_card fun c' hc' => ?_))
      have hc'' := (hmemC c').mp hc'
      exact mem_ackers.mpr (Finset.mem_coe.mpr (gossip hR hc'' hc (τ := T4 + 1) (by omega)
        |>.trans (known_mono R (by omega) c) (hack c' hc'')))
    obtain ⟨y', hy'1, hy'2⟩ := step_commit (view_eq (by omega) (by omega)) hcc
    obtain ⟨c', hc'1, hc'2⟩ := exists_not_mem_of_card_lt
      (X := ackers (↑(R.st (algo pr L) (T5 + 1) c).known : Set (Tok P V)) y' v) (B := R.faulty)
      (by unfold HasCC at hy'1; omega)
    have e : y' = y :=
      huniq _ y' c' hc'2 (mem_E hc (Finset.mem_coe.mp (mem_ackers.mp hc'1))) (by omega)
    rw [e] at hy'2
    exact hy'2
  -- the decision (at `T6`)
  obtain ⟨T6, hT6⟩ : ∃ T, T = T5 + 1 + δ + 1 := ⟨_, rfl⟩
  have hdec : Decided pr (↑(R.st (algo pr L) T6 ℓ).known : Set (Tok P V)) y := by
    refine ⟨v, Or.inr (le_trans hqc (le_trans hCcard (card_le_card fun c hc => ?_)))⟩
    have hc' := (hmemC c).mp hc
    exact mem_committers.mpr (Finset.mem_coe.mpr (gossip hR hc' hℓ (τ := T5 + 1) (by omega)
      |>.trans (known_mono R (by omega) ℓ) (hcom c hc')))
  have hex : ∃ x, Decided pr (↑(R.st (algo pr L) T6 ℓ).known : Set (Tok P V)) x := ⟨y, hdec⟩
  refine ⟨Classical.choose hex, T6, ?_⟩
  exact dite_eq_left_of_eq_true (eq_true hex)

end Main

end FastByzantineConsensus.Impl
