import Papers.PODC2019.HotStuff.Basic.HandlerFields

/-!
# Basic HotStuff implementation: local invariants (for liveness)

State-local invariants of every replica (they hold for all computed states, faulty or not),
mostly about the ghost variables: what was proposed and sent as a leader, what a vote was based
on, and the content of new-view messages.
-/

namespace HotStuff.Basic

open Classical Cslib.Byzantine.PartialSync

variable {P C : Type*} [Fintype P] [DecidableEq P]

/-- The local invariant of replica `p` in state `s`. -/
structure LI (f : ℕ) (leader : ℕ → P) (p : P) (s : RState P C) : Prop where
  out_sent : ∀ q m, m ∈ s.out q → (q, m) ∈ s.sent
  props_ok : ∀ w x j, (w, x, j) ∈ s.props → p = leader w ∧ w ≤ s.view ∧
    x = s.inp.2 w :: j.qc.node ∧ j.ok f ∧
    (∃ S : Finset P, Fintype.card P - f ≤ S.card ∧ ∀ q ∈ S, ∃ j', j'.ok f ∧
      j'.qc.view ≤ j.qc.view ∧ (q, Msg.newView (w - 1) j') ∈ s.buf) ∧
    (j = QCm.gen ∨ ∃ q, (q, Msg.newView (w - 1) j) ∈ s.buf) ∧
    ∀ q, (q, Msg.prepare w x j) ∈ s.sent
  props_uniq : ∀ w x j x' j', (w, x, j) ∈ s.props → (w, x', j') ∈ s.props → x = x' ∧ j = j'
  props_cur : 1 ≤ s.lphase → (s.view, s.prop, s.high) ∈ s.props
  props_lph : ∀ x j, (s.view, x, j) ∈ s.props → 1 ≤ s.lphase
  made_ok : ∀ c ∈ s.made, ∃ k, 1 ≤ k ∧ k ≤ 3 ∧ c.qc.ty = lty k ∧
    (∃ j, (c.qc.view, c.qc.node, j) ∈ s.props) ∧ (∀ q, (q, Msg.cert c) ∈ s.sent) ∧
    (∀ k', 1 ≤ k' → k' < k → ∃ c' ∈ s.made, c'.qc = ⟨lty k', c.qc.view, c.qc.node⟩) ∧
    (c.qc.view = s.view → k + 1 ≤ s.lphase)
  made_cur : ∀ k, 1 ≤ k → k ≤ 3 → k + 1 ≤ s.lphase →
    ∃ c ∈ s.made, c.qc = ⟨lty k, s.view, s.prop⟩
  sent_prep : ∀ q w x j, (q, Msg.prepare w x j) ∈ s.sent → (w, x, j) ∈ s.props
  sent_cert : ∀ q c, (q, Msg.cert c) ∈ s.sent → c ∈ s.made
  votes_sent : ∀ u ∈ s.votes, (leader u.view, Msg.vote p u) ∈ s.sent
  votes_view : ∀ u ∈ s.votes, u.view ≤ s.view
  nv_cur : ∃ j, (leader s.view, Msg.newView (s.view - 1) j) ∈ s.sent
  nv_sent : ∀ q w j, (q, Msg.newView w j) ∈ s.sent → w + 1 ≤ s.view ∧ j.ok f ∧
    ∀ u ∈ s.votes, u.ty = .precommit → u.view ≤ w → u.view ≤ j.qc.view
  prep_ok : s.prepQC.ok f
  prep_ge : ∀ u ∈ s.votes, u.ty = .precommit → u.view ≤ s.prepQC.qc.view
  lock_src : s.lock = QCm.gen ∨
    (s.lock.ok f ∧ s.lock.qc.ty = .precommit ∧ ∃ q, (q, Msg.cert s.lock) ∈ s.buf)
  lock_view : s.lock.qc.view ≤ s.view ∧ (s.lock.qc.view = s.view → 3 ≤ s.phase)
  r1_ok : ∀ w x j l, (w, x, j, l) ∈ s.r1 → l.view < w ∧
    (l = QC.genesis ∨ ∃ c q, c.ok f ∧ c.qc = l ∧ l.ty = .precommit ∧ (q, Msg.cert c) ∈ s.buf)
  ph1 : 1 ≤ s.phase → ∃ x j l, (s.view, x, j, l) ∈ s.r1 ∧
    (leader s.view, Msg.prepare s.view x j) ∈ s.buf ∧
    ((j.ok f ∧ j.qc.node <:+ x ∧ SafeNode l x j.qc) → (⟨.prepare, s.view, x⟩ : QC C) ∈ s.votes)
  ph2 : 2 ≤ s.phase → ∃ c, (leader s.view, Msg.cert c) ∈ s.buf ∧ c.qc.ty = .prepare ∧
    c.qc.view = s.view ∧ (⟨.precommit, s.view, c.qc.node⟩ : QC C) ∈ s.votes
  ph3 : 3 ≤ s.phase → ∃ c, (leader s.view, Msg.cert c) ∈ s.buf ∧ c.qc.ty = .precommit ∧
    c.qc.view = s.view ∧ (⟨.commit, s.view, c.qc.node⟩ : QC C) ∈ s.votes
  decs_ok : ∀ w x, (w, x) ∈ s.decs → x ∈ s.committed ∧ ∃ c, (leader w, Msg.cert c) ∈ s.buf ∧
    c.qc.ty = .commit ∧ c.qc.view = w ∧ c.qc.node = x
  view_pos : 1 ≤ s.view

variable {f : ℕ} {leader : ℕ → P} {p : P}

theorem LI.init (i : Inp C) : LI f leader p (RState.init leader i : RState P C) where
  out_sent q m hm := by
    simp only [RState.init] at hm ⊢
    rw [mem_to1 hm]; simp only [to1] at hm; split_ifs at hm with h <;> simp_all
  props_ok := by simp [RState.init]
  props_uniq := by simp [RState.init]
  props_cur := by simp [RState.init]
  props_lph := by simp [RState.init]
  made_ok := by simp [RState.init]
  made_cur := by simp [RState.init]
  sent_prep := by simp [RState.init]
  sent_cert := by simp [RState.init]
  votes_sent := by simp [RState.init]
  votes_view := by simp [RState.init]
  nv_cur := ⟨QCm.gen, by simp [RState.init]⟩
  nv_sent := by
    simp only [RState.init, Set.mem_singleton_iff, Prod.mk.injEq, Msg.newView.injEq]
    rintro q w j ⟨-, rfl, rfl⟩
    exact ⟨le_rfl, Or.inl ⟨rfl, rfl⟩, by simp⟩
  prep_ok := Or.inl ⟨rfl, rfl⟩
  prep_ge := by simp [RState.init]
  lock_src := Or.inl rfl
  lock_view := by simp [RState.init, QCm.gen, QC.genesis]
  r1_ok := by simp [RState.init]
  ph1 := by simp [RState.init]
  ph2 := by simp [RState.init]
  ph3 := by simp [RState.init]
  decs_ok := by simp [RState.init]
  view_pos := le_rfl

theorem LI.of_recv {s : RState P C} (h : LI f leader p s) (inbox : P → List (Msg P C)) :
    LI f leader p (HotStuff.Basic.recv s inbox) := by
  have hb : ∀ qm, qm ∈ s.buf → qm ∈ (HotStuff.Basic.recv s inbox).buf := fun qm h => by
    simp [HotStuff.Basic.recv, h]
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h17, h18, h19,
    h20, h21, h22, h23, h24⟩ := h
  refine ⟨?_, ?_, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, ?_, h18, ?_, ?_, ?_,
    ?_, ?_, h24⟩
  · intro q m hm; simp [HotStuff.Basic.recv] at hm
  · intro w x j hx
    obtain ⟨a1, a2, a3, a4, ⟨S, hS, hS'⟩, a6, a7⟩ := h2 w x j hx
    refine ⟨a1, a2, a3, a4, ⟨S, hS, fun q hq => ?_⟩, ?_, a7⟩
    · obtain ⟨j', b1, b2, b3⟩ := hS' q hq; exact ⟨j', b1, b2, hb _ b3⟩
    · rcases a6 with a6 | ⟨q, hq⟩
      · exact Or.inl a6
      · exact Or.inr ⟨q, hb _ hq⟩
  · rcases h17 with h17 | ⟨b1, b2, q, hq⟩
    · exact Or.inl h17
    · exact Or.inr ⟨b1, b2, q, hb _ hq⟩
  · intro w x j l hx
    obtain ⟨a1, a2⟩ := h19 w x j l hx
    refine ⟨a1, ?_⟩
    rcases a2 with a2 | ⟨c, q, b1, b2, b3, b4⟩
    · exact Or.inl a2
    · exact Or.inr ⟨c, q, b1, b2, b3, hb _ b4⟩
  · intro hp
    obtain ⟨x, j, l, a1, a2, a3⟩ := h20 hp
    exact ⟨x, j, l, a1, hb _ a2, a3⟩
  · intro hp
    obtain ⟨c, a1, a2⟩ := h21 hp
    exact ⟨c, hb _ a1, a2⟩
  · intro hp
    obtain ⟨c, a1, a2⟩ := h22 hp
    exact ⟨c, hb _ a1, a2⟩
  · intro w x hx
    obtain ⟨a1, c, a2, a3⟩ := h23 w x hx
    exact ⟨a1, c, hb _ a2, a3⟩

theorem mem_sent_send {s : RState P C} {g : P → List (Msg P C)} {qm : P × Msg P C} :
    qm ∈ (s.send g).sent ↔ qm ∈ s.sent ∨ qm.2 ∈ g qm.1 := by
  simp [RState.send]

theorem mem_out_send {s : RState P C} {g : P → List (Msg P C)} {q : P} {m : Msg P C} :
    m ∈ (s.send g).out q ↔ m ∈ s.out q ∨ m ∈ g q := by
  simp [RState.send]

theorem mem_nvJ_iff {w : ℕ} {m : Msg P C} {j : QCm P C} :
    nvJ f w m = some j ↔ m = .newView w j ∧ j.ok f := by
  refine ⟨mem_nvJ, ?_⟩
  rintro ⟨rfl, h⟩
  simp [nvJ, h]

theorem LI.L1 {s : RState P C} (h : LI f leader p s) : LI f leader p (L1 f leader p s) := by
  unfold HotStuff.Basic.L1
  split_ifs with hc
  swap; · exact h
  set l := s.buf.filterMap fun m => nvJ f (s.view - 1) m.2 with hl
  set hq := bestQC l with hhq
  have hok : hq.ok f := by
    rcases bestQC_cases l with e | e
    · rw [hhq, e]; exact Or.inl ⟨rfl, rfl⟩
    · rw [hl, List.mem_filterMap] at e
      obtain ⟨qm, -, e⟩ := e
      exact (mem_nvJ e).2
  have hsrc : hq = QCm.gen ∨ ∃ q, (q, Msg.newView (s.view - 1) hq) ∈ s.buf := by
    rcases bestQC_cases l with e | e
    · exact Or.inl e
    · rw [hl, List.mem_filterMap] at e
      obtain ⟨⟨q, m⟩, hqm, e⟩ := e
      obtain ⟨rfl, -⟩ := mem_nvJ e
      exact Or.inr ⟨q, hqm⟩
  have hS : ∃ S : Finset P, Fintype.card P - f ≤ S.card ∧ ∀ q ∈ S, ∃ j', j'.ok f ∧
      j'.qc.view ≤ hq.qc.view ∧ (q, Msg.newView (s.view - 1) j') ∈ s.buf := by
    refine ⟨nvSenders f s, hc.2.2, fun q hqS => ?_⟩
    simp only [nvSenders, Finset.mem_filter, Finset.mem_univ, true_and] at hqS
    obtain ⟨j', hj', hok'⟩ := hqS
    refine ⟨j', hok', le_bestQC l j' ?_, hj'⟩
    rw [hl, List.mem_filterMap]
    exact ⟨(q, .newView (s.view - 1) j'), hj', mem_nvJ_iff.mpr ⟨rfl, hok'⟩⟩
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h17, h18, h19,
    h20, h21, h22, h23, h24⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, h11, ?_, ?_, h14, h15, h17, h18, h19, h20, h21,
    h22, h23, h24⟩
  · intro q m hm
    rw [mem_out_send] at hm
    rw [mem_sent_send]
    exact hm.imp (h1 q m) id
  · intro w x j hx
    rcases Set.mem_insert_iff.mp hx with e | hx
    · simp only [Prod.mk.injEq] at e
      obtain ⟨rfl, rfl, rfl⟩ := e
      exact ⟨hc.2.1, le_rfl, rfl, hok, hS, hsrc, fun q => mem_sent_send.mpr (Or.inr (by simp [bcast]))⟩
    · obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := h2 w x j hx
      exact ⟨a1, a2, a3, a4, a5, a6, fun q => mem_sent_send.mpr (Or.inl (a7 q))⟩
  · intro w x j x' j' hx hx'
    rcases Set.mem_insert_iff.mp hx with e | hx <;> rcases Set.mem_insert_iff.mp hx' with e' | hx'
    · simp only [Prod.mk.injEq] at e e'; exact ⟨e.2.1.trans e'.2.1.symm, e.2.2.trans e'.2.2.symm⟩
    · simp only [Prod.mk.injEq] at e; rw [e.1] at hx'; have := h5 _ _ hx'; omega
    · simp only [Prod.mk.injEq] at e'; rw [e'.1] at hx; have := h5 _ _ hx; omega
    · exact h3 w x j x' j' hx hx'
  · intro _; exact Set.mem_insert _ _
  · intro _ _ _; exact le_rfl
  · intro c hc'
    obtain ⟨k, a1, a2, a3, ⟨j, a4⟩, a5, a6, a7⟩ := h6 c hc'
    refine ⟨k, a1, a2, a3, ⟨j, Set.mem_insert_of_mem _ a4⟩,
      fun q => mem_sent_send.mpr (Or.inl (a5 q)), a6, fun e => ?_⟩
    have := a7 e; omega
  · intro k hk1 _ hk; simp at hk; omega
  · intro q w x j hs'
    rcases mem_sent_send.mp hs' with hs' | hs'
    · exact Set.mem_insert_of_mem _ (h8 q w x j hs')
    · simp only [bcast, List.mem_singleton, Msg.prepare.injEq] at hs'
      obtain ⟨rfl, rfl, rfl⟩ := hs'
      exact Set.mem_insert _ _
  · intro q c hs'
    rcases mem_sent_send.mp hs' with hs' | hs'
    · exact h9 q c hs'
    · simp [bcast] at hs'
  · intro u hu; exact mem_sent_send.mpr (Or.inl (h10 u hu))
  · obtain ⟨j, hj⟩ := h12; exact ⟨j, mem_sent_send.mpr (Or.inl hj)⟩
  · intro q w j hs'
    rcases mem_sent_send.mp hs' with hs' | hs'
    · exact h13 q w j hs'
    · simp [bcast] at hs'

theorem LI.LQ {s : RState P C} (h : LI f leader p s) {k : ℕ} (hk1 : 1 ≤ k) (hk3 : k ≤ 3) :
    LI f leader p (LQ f leader p k s) := by
  unfold HotStuff.Basic.LQ
  split_ifs with hc
  swap; · exact h
  set c : QCm P C := ⟨⟨lty k, s.view, s.prop⟩, voters s ⟨lty k, s.view, s.prop⟩⟩ with hcdef
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h17, h18, h19,
    h20, h21, h22, h23, h24⟩ := h
  refine ⟨?_, ?_, h3, ?_, ?_, ?_, ?_, ?_, ?_, ?_, h11, ?_, ?_, h14, h15, h17, h18, h19, h20, h21,
    h22, h23, h24⟩
  · intro q m hm
    rw [mem_out_send] at hm
    rw [mem_sent_send]
    exact hm.imp (h1 q m) id
  · intro w x j hx
    obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := h2 w x j hx
    exact ⟨a1, a2, a3, a4, a5, a6, fun q => mem_sent_send.mpr (Or.inl (a7 q))⟩
  · intro _; exact h4 (by omega)
  · intro _ _ _; simp
  · intro c' hc'
    rcases Set.mem_insert_iff.mp hc' with rfl | hc'
    · refine ⟨k, hk1, hk3, rfl, ⟨s.high, h4 (by omega)⟩,
        fun q => mem_sent_send.mpr (Or.inr (by simp [bcast])), fun k' hk' hkk => ?_,
        fun _ => by simp⟩
      obtain ⟨c'', hc'', e⟩ := h7 k' hk' (by omega) (by omega)
      exact ⟨c'', Set.mem_insert_of_mem _ hc'', e⟩
    · obtain ⟨k₀, a1, a2, a3, a4, a5, a6, a7⟩ := h6 c' hc'
      refine ⟨k₀, a1, a2, a3, a4, fun q => mem_sent_send.mpr (Or.inl (a5 q)), fun k' hk' hkk => ?_,
        fun e => by have := a7 e; simp; omega⟩
      obtain ⟨c'', hc'', e⟩ := a6 k' hk' hkk
      exact ⟨c'', Set.mem_insert_of_mem _ hc'', e⟩
  · intro k' hk1' hk3' hk'
    simp only at hk'
    rcases Nat.lt_or_ge k' k with hlt | hge
    · obtain ⟨c'', hc'', e⟩ := h7 k' hk1' hk3' (by omega)
      exact ⟨c'', Set.mem_insert_of_mem _ hc'', e⟩
    · obtain rfl : k' = k := by omega
      exact ⟨c, Set.mem_insert _ _, rfl⟩
  · intro q w x j hs'
    rcases mem_sent_send.mp hs' with hs' | hs'
    · exact h8 q w x j hs'
    · simp [bcast] at hs'
  · intro q c' hs'
    rcases mem_sent_send.mp hs' with hs' | hs'
    · exact Set.mem_insert_of_mem _ (h9 q c' hs')
    · simp only [bcast, List.mem_singleton, Msg.cert.injEq] at hs'
      rw [hs']; exact Set.mem_insert _ _
  · intro u hu; exact mem_sent_send.mpr (Or.inl (h10 u hu))
  · obtain ⟨j, hj⟩ := h12; exact ⟨j, mem_sent_send.mpr (Or.inl hj)⟩
  · intro q w j hs'
    rcases mem_sent_send.mp hs' with hs' | hs'
    · exact h13 q w j hs'
    · simp [bcast] at hs'

theorem LI.r1_entry {s : RState P C} (h : LI f leader p s) (h0 : s.phase = 0) :
    s.lock.qc.view < s.view ∧ (s.lock.qc = QC.genesis ∨ ∃ c q, c.ok f ∧ c.qc = s.lock.qc ∧
      s.lock.qc.ty = .precommit ∧ (q, Msg.cert c) ∈ s.buf) := by
  refine ⟨?_, ?_⟩
  · rcases Nat.lt_or_ge s.lock.qc.view s.view with e | e
    · exact e
    · have := h.lock_view.2 (le_antisymm h.lock_view.1 e); omega
  · rcases h.lock_src with e | ⟨a1, a2, q, a3⟩
    · left; rw [e]; rfl
    · exact Or.inr ⟨s.lock, q, a1, rfl, a2, a3⟩

theorem LI.R1 {s : RState P C} (h : LI f leader p s) : LI f leader p (R1 f leader p s) := by
  unfold HotStuff.Basic.R1
  split_ifs with hc
  swap; · exact h
  dsimp only
  set xj := Classical.choose hc.2 with hxj
  have hmem : (leader s.view, Msg.prepare s.view xj.1 xj.2) ∈ s.buf := Classical.choose_spec hc.2
  have hent := h.r1_entry hc.1
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h17, h18, h19,
    h20, h21, h22, h23, h24⟩ := h
  split_ifs with hg
  · refine ⟨?_, ?_, h3, h4, h5, ?_, h7, ?_, ?_, ?_, ?_, ?_, ?_, h14, ?_, h17, ?_, ?_, ?_, ?_, ?_,
      h23, h24⟩
    · intro q m hm
      rw [mem_out_send] at hm
      rw [mem_sent_send]
      exact hm.imp (h1 q m) id
    · intro w x j hx
      obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := h2 w x j hx
      exact ⟨a1, a2, a3, a4, a5, a6, fun q => mem_sent_send.mpr (Or.inl (a7 q))⟩
    · intro c' hc'
      obtain ⟨k₀, a1, a2, a3, a4, a5, a6, a7⟩ := h6 c' hc'
      exact ⟨k₀, a1, a2, a3, a4, fun q => mem_sent_send.mpr (Or.inl (a5 q)), a6, a7⟩
    · intro q w x j hs'
      rcases mem_sent_send.mp hs' with hs' | hs'
      · exact h8 q w x j hs'
      · simp [to1] at hs'
    · intro q c' hs'
      rcases mem_sent_send.mp hs' with hs' | hs'
      · exact h9 q c' hs'
      · simp [to1] at hs'
    · intro u hu
      rcases Set.mem_insert_iff.mp hu with rfl | hu
      · exact mem_sent_send.mpr (Or.inr (by simp [to1]))
      · exact mem_sent_send.mpr (Or.inl (h10 u hu))
    · intro u hu
      rcases Set.mem_insert_iff.mp hu with rfl | hu
      · exact le_rfl
      · exact h11 u hu
    · obtain ⟨j, hj⟩ := h12; exact ⟨j, mem_sent_send.mpr (Or.inl hj)⟩
    · intro q w j hs'
      rcases mem_sent_send.mp hs' with hs' | hs'
      · obtain ⟨a1, a2, a3⟩ := h13 q w j hs'
        refine ⟨a1, a2, fun u hu ht hw => ?_⟩
        rcases Set.mem_insert_iff.mp hu with rfl | hu
        · cases ht
        · exact a3 u hu ht hw
      · simp [to1] at hs'
    · intro u hu ht
      rcases Set.mem_insert_iff.mp hu with rfl | hu
      · cases ht
      · exact h15 u hu ht
    · exact ⟨h18.1, fun e => by have := h18.2 e; omega⟩
    · intro w x j l hx
      rcases Set.mem_insert_iff.mp hx with e | hx
      · simp only [Prod.mk.injEq] at e
        obtain ⟨rfl, rfl, rfl, rfl⟩ := e
        exact hent
      · exact h19 w x j l hx
    · intro _
      exact ⟨xj.1, xj.2, s.lock.qc, Set.mem_insert _ _, hmem, fun _ => Set.mem_insert _ _⟩
    · intro e; simp at e
    · intro e; simp at e
  · refine ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h17,
      ⟨h18.1, fun e => by have := h18.2 e; omega⟩, ?_, ?_, ?_, ?_, h23, h24⟩
    · intro w x j l hx
      rcases Set.mem_insert_iff.mp hx with e | hx
      · simp only [Prod.mk.injEq] at e
        obtain ⟨rfl, rfl, rfl, rfl⟩ := e
        exact hent
      · exact h19 w x j l hx
    · intro _
      exact ⟨xj.1, xj.2, s.lock.qc, Set.mem_insert _ _, hmem, fun hg' => absurd hg' hg⟩
    · intro e; simp at e
    · intro e; simp at e

theorem LI.R2 {s : RState P C} (h : LI f leader p s) : LI f leader p (R2 f leader p s) := by
  unfold HotStuff.Basic.R2
  split_ifs with hc
  swap; · exact h
  set c := Classical.choose hc.2 with hcd
  have hmem : HasCert f leader .prepare s c := Classical.choose_spec hc.2
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h17, h18, h19,
    h20, h21, h22, h23, h24⟩ := h
  refine ⟨?_, ?_, h3, h4, h5, ?_, h7, ?_, ?_, ?_, ?_, ?_, ?_, hmem.2.2.2, ?_, h17, ?_, h19, ?_, ?_,
    ?_, h23, h24⟩
  · intro q m hm
    rw [mem_out_send] at hm
    rw [mem_sent_send]
    exact hm.imp (h1 q m) id
  · intro w x j hx
    obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := h2 w x j hx
    exact ⟨a1, a2, a3, a4, a5, a6, fun q => mem_sent_send.mpr (Or.inl (a7 q))⟩
  · intro c' hc'
    obtain ⟨k₀, a1, a2, a3, a4, a5, a6, a7⟩ := h6 c' hc'
    exact ⟨k₀, a1, a2, a3, a4, fun q => mem_sent_send.mpr (Or.inl (a5 q)), a6, a7⟩
  · intro q w x j hs'
    rcases mem_sent_send.mp hs' with hs' | hs'
    · exact h8 q w x j hs'
    · simp [to1] at hs'
  · intro q c' hs'
    rcases mem_sent_send.mp hs' with hs' | hs'
    · exact h9 q c' hs'
    · simp [to1] at hs'
  · intro u hu
    rcases Set.mem_insert_iff.mp hu with rfl | hu
    · exact mem_sent_send.mpr (Or.inr (by simp [to1]))
    · exact mem_sent_send.mpr (Or.inl (h10 u hu))
  · intro u hu
    rcases Set.mem_insert_iff.mp hu with rfl | hu
    · exact le_rfl
    · exact h11 u hu
  · obtain ⟨j, hj⟩ := h12; exact ⟨j, mem_sent_send.mpr (Or.inl hj)⟩
  · intro q w j hs'
    rcases mem_sent_send.mp hs' with hs' | hs'
    · obtain ⟨a1, a2, a3⟩ := h13 q w j hs'
      refine ⟨a1, a2, fun u hu ht hw => ?_⟩
      rcases Set.mem_insert_iff.mp hu with rfl | hu
      · simp at hw; omega
      · exact a3 u hu ht hw
    · simp [to1] at hs'
  · intro u hu _
    rw [hmem.2.2.1]
    rcases Set.mem_insert_iff.mp hu with rfl | hu
    · exact le_rfl
    · exact h11 u hu
  · exact ⟨h18.1, fun e => by have := h18.2 e; omega⟩
  · intro _
    obtain ⟨x, j, l, a1, a2, a3⟩ := h20 (by omega)
    exact ⟨x, j, l, a1, a2, fun g => Set.mem_insert_of_mem _ (a3 g)⟩
  · intro _
    exact ⟨c, hmem.1, hmem.2.1, hmem.2.2.1, Set.mem_insert _ _⟩
  · intro e; simp at e

theorem LI.R3 {s : RState P C} (h : LI f leader p s) : LI f leader p (R3 f leader p s) := by
  unfold HotStuff.Basic.R3
  split_ifs with hc
  swap; · exact h
  set c := Classical.choose hc.2 with hcd
  have hmem : HasCert f leader .precommit s c := Classical.choose_spec hc.2
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h17, h18, h19,
    h20, h21, h22, h23, h24⟩ := h
  refine ⟨?_, ?_, h3, h4, h5, ?_, h7, ?_, ?_, ?_, ?_, ?_, ?_, h14, ?_, ?_, ?_, h19, ?_, ?_,
    ?_, h23, h24⟩
  · intro q m hm
    rw [mem_out_send] at hm
    rw [mem_sent_send]
    exact hm.imp (h1 q m) id
  · intro w x j hx
    obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := h2 w x j hx
    exact ⟨a1, a2, a3, a4, a5, a6, fun q => mem_sent_send.mpr (Or.inl (a7 q))⟩
  · intro c' hc'
    obtain ⟨k₀, a1, a2, a3, a4, a5, a6, a7⟩ := h6 c' hc'
    exact ⟨k₀, a1, a2, a3, a4, fun q => mem_sent_send.mpr (Or.inl (a5 q)), a6, a7⟩
  · intro q w x j hs'
    rcases mem_sent_send.mp hs' with hs' | hs'
    · exact h8 q w x j hs'
    · simp [to1] at hs'
  · intro q c' hs'
    rcases mem_sent_send.mp hs' with hs' | hs'
    · exact h9 q c' hs'
    · simp [to1] at hs'
  · intro u hu
    rcases Set.mem_insert_iff.mp hu with rfl | hu
    · exact mem_sent_send.mpr (Or.inr (by simp [to1]))
    · exact mem_sent_send.mpr (Or.inl (h10 u hu))
  · intro u hu
    rcases Set.mem_insert_iff.mp hu with rfl | hu
    · exact le_rfl
    · exact h11 u hu
  · obtain ⟨j, hj⟩ := h12; exact ⟨j, mem_sent_send.mpr (Or.inl hj)⟩
  · intro q w j hs'
    rcases mem_sent_send.mp hs' with hs' | hs'
    · obtain ⟨a1, a2, a3⟩ := h13 q w j hs'
      refine ⟨a1, a2, fun u hu ht hw => ?_⟩
      rcases Set.mem_insert_iff.mp hu with rfl | hu
      · cases ht
      · exact a3 u hu ht hw
    · simp [to1] at hs'
  · intro u hu ht
    rcases Set.mem_insert_iff.mp hu with rfl | hu
    · cases ht
    · exact h15 u hu ht
  · exact Or.inr ⟨hmem.2.2.2, hmem.2.1, _, hmem.1⟩
  · exact ⟨by simp [hmem.2.2.1, RState.send], fun _ => by simp⟩
  · intro _
    obtain ⟨x, j, l, a1, a2, a3⟩ := h20 (by omega)
    exact ⟨x, j, l, a1, a2, fun g => Set.mem_insert_of_mem _ (a3 g)⟩
  · intro _
    obtain ⟨c', a1, a2, a3, a4⟩ := h21 (by omega)
    exact ⟨c', a1, a2, a3, Set.mem_insert_of_mem _ a4⟩
  · intro _
    exact ⟨c, hmem.1, hmem.2.1, hmem.2.2.1, Set.mem_insert _ _⟩

theorem LI.enterView {s : RState P C} (h : LI f leader p s) :
    LI f leader p (enterView leader s) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h17, h18, h19,
    h20, h21, h22, h23, h24⟩ := h
  refine ⟨?_, ?_, h3, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, h14, h15, h17, ?_, h19, ?_, ?_,
    ?_, h23, by simp⟩
  · intro q m hm
    rw [enterView_out, List.mem_append] at hm
    show (q, m) ∈ (s.send _).sent
    rw [mem_sent_send]
    exact hm.imp (h1 q m) id
  · intro w x j hx
    obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := h2 w x j hx
    exact ⟨a1, by simp; omega, a3, a4, a5, a6, fun q => mem_sent_send.mpr (Or.inl (a7 q))⟩
  · intro e; simp at e
  · intro x j hx
    have := (h2 _ x j hx).2.1; simp at this
  · intro c' hc'
    obtain ⟨k₀, a1, a2, a3, ⟨j, a4⟩, a5, a6, a7⟩ := h6 c' hc'
    refine ⟨k₀, a1, a2, a3, ⟨j, a4⟩, fun q => mem_sent_send.mpr (Or.inl (a5 q)), a6, fun e => ?_⟩
    have := (h2 _ _ j a4).2.1; simp at e; omega
  · intro k hk1 _ hk; simp at hk
  · intro q w x j hs'
    rcases mem_sent_send.mp hs' with hs' | hs'
    · exact h8 q w x j hs'
    · simp [to1] at hs'
  · intro q c' hs'
    rcases mem_sent_send.mp hs' with hs' | hs'
    · exact h9 q c' hs'
    · simp [to1] at hs'
  · intro u hu; exact mem_sent_send.mpr (Or.inl (h10 u hu))
  · intro u hu; have := h11 u hu; simp; omega
  · exact ⟨s.prepQC, mem_sent_send.mpr (Or.inr (by simp [to1]))⟩
  · intro q w j hs'
    rcases mem_sent_send.mp hs' with hs' | hs'
    · obtain ⟨a1, a2, a3⟩ := h13 q w j hs'
      exact ⟨by simp; omega, a2, a3⟩
    · simp only [to1] at hs'
      split_ifs at hs' with e
      · simp only [List.mem_singleton, Msg.newView.injEq] at hs'
        obtain ⟨rfl, rfl⟩ := hs'
        exact ⟨by simp, h14, fun u hu ht _ => h15 u hu ht⟩
      · simp at hs'
  · exact ⟨by simp; omega, fun e => by simp at e; omega⟩
  · intro e; simp at e
  · intro e; simp at e
  · intro e; simp at e

theorem LI.commitNode {s : RState P C} (h : LI f leader p s) (h3 : s.phase = 3) {c : QCm P C}
    (hc : HasCert f leader .commit s c) : LI f leader p (s.commitNode c.qc.node) := by
  obtain ⟨h1, h2, h3', h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h17, h18, h19,
    h20, h21, h22, h23, h24⟩ := h
  refine ⟨h1, h2, h3', h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h17,
    ⟨h18.1, fun _ => by simp [RState.commitNode]⟩, h19, fun _ => h20 (by omega),
    fun _ => h21 (by omega), fun _ => h22 (by omega), ?_, h24⟩
  intro w x hx
  simp only [RState.commitNode, Set.mem_insert_iff, Prod.mk.injEq] at hx ⊢
  rcases hx with ⟨rfl, rfl⟩ | hx
  · exact ⟨Or.inl rfl, c, hc.1, hc.2.1, hc.2.2.1, rfl⟩
  · obtain ⟨a1, a2⟩ := h23 w x hx
    exact ⟨Or.inr a1, a2⟩

theorem LI.R4 {s : RState P C} (h : LI f leader p s) : LI f leader p (R4 f leader s) := by
  unfold HotStuff.Basic.R4
  split_ifs with hc
  swap; · exact h
  exact (h.commitNode hc.1 (Classical.choose_spec hc.2)).enterView

theorem LI.stepR {s : RState P C} (h : LI f leader p s) (inbox : P → List (Msg P C)) :
    LI f leader p (stepR f leader p s inbox) := by
  have h' := ((((((((h.of_recv inbox).L1).LQ (k := 1) le_rfl (by norm_num)).LQ (k := 2)
    (by norm_num) (by norm_num)).LQ (k := 3) (by norm_num) le_rfl).R1).R2).R3).R4
  unfold HotStuff.Basic.stepR
  dsimp only
  split_ifs
  · exact h'.enterView
  · exact h'

end HotStuff.Basic
