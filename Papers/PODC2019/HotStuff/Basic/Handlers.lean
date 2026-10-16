import Papers.PODC2019.HotStuff.Basic.Impl

/-!
# Basic HotStuff implementation: one step refines the abstract system

Every handler of a replica either leaves the abstract local state unchanged or performs one
step of the abstract system `LStep`, provided every *locally valid* QC in the buffer is valid in
the abstract sense (`BufValid`). Handlers also only emit signature tokens that the replica owns
(its own votes) or has received (`TokOK`), i.e. the implementation is unforging.
-/

namespace HotStuff.Basic

open Classical Cslib.Byzantine.PartialSync

variable {P C : Type*} [Fintype P] [DecidableEq P] {f : ℕ} {F : Finset P} {leader : ℕ → P}

/-- QCs carried by a message. -/
def Msg.qcs : Msg P C → Set (QCm P C)
  | .newView _ j => {j}
  | .prepare _ _ j => {j}
  | .cert j => {j}
  | .vote _ _ => ∅

theorem Msg.toks_of_qcs {m : Msg P C} {j : QCm P C} (hj : j ∈ m.qcs) : j.toks ⊆ m.toks := by
  cases m <;> simp_all [Msg.qcs, Msg.toks]

/-- Every locally valid QC in the buffer is valid w.r.t. the abstract votes `V`. -/
def BufValid (f : ℕ) (F : Finset P) (V : Set (P × QC C)) (s : RState P C) : Prop :=
  ∀ q m, (q, m) ∈ s.buf → ∀ j ∈ m.qcs, j.ok f → Valid f F V j.qc

/-- Tokens of buffered messages. -/
def bufToks (s : RState P C) : Set (Tok P C) := {k | ∃ qm ∈ s.buf, k ∈ qm.2.toks}

/-- Token discipline of replica `p`: outgoing tokens are own votes or received tokens; the stored
QCs only contain received tokens. -/
structure TokOK (p : P) (s : RState P C) : Prop where
  out : ∀ q, ∀ m ∈ s.out q, ∀ k ∈ m.toks, (k.1 = p ∧ k.2 ∈ s.votes) ∨ k ∈ bufToks s
  prep : s.prepQC.toks ⊆ bufToks s
  lock : s.lock.toks ⊆ bufToks s

/-- Abstract local reachability of a single replica, with fixed global votes `V`. -/
def LR (f : ℕ) (F : Finset P) (V : Set (P × QC C)) : Loc C × Set (QC C) → Loc C × Set (QC C) → Prop :=
  Relation.ReflTransGen fun a b => ∃ o, LStep f F V a.1 b.1 o ∧ b.2 = a.2 ∪ {q | o = some q}

/-- The properties of a handler, from `s` to `s'`. -/
structure HStep (f : ℕ) (F : Finset P) (V : Set (P × QC C)) (p : P) (s s' : RState P C) : Prop where
  buf : s'.buf = s.buf
  inp : s'.inp = s.inp
  clock : s'.clock = s.clock
  votes : s.votes ⊆ s'.votes
  lr : BufValid f F V s → LR f F V (s.toLoc, s.votes) (s'.toLoc, s'.votes)
  tok : TokOK p s → TokOK p s'
  /-- Votes are only added for the current or a later view. -/
  vview : ∀ q ∈ s'.votes, q ∉ s.votes → s.view ≤ q.view
  /-- The view only increases. -/
  view : s.view ≤ s'.view
  /-- Committed nodes are only added. -/
  committed : s.committed ⊆ s'.committed

theorem HStep.refl (s : RState P C) {V : Set (P × QC C)} {p : P} : HStep f F V p s s where
  buf := rfl
  inp := rfl
  clock := rfl
  votes := le_rfl
  lr _ := Relation.ReflTransGen.refl
  tok h := h
  vview _ h h' := absurd h h'
  view := le_rfl
  committed := le_rfl

theorem HStep.trans {V : Set (P × QC C)} {p : P} {s s' s'' : RState P C}
    (h₁ : HStep f F V p s s') (h₂ : HStep f F V p s' s'') : HStep f F V p s s'' where
  buf := h₂.buf.trans h₁.buf
  inp := h₂.inp.trans h₁.inp
  clock := h₂.clock.trans h₁.clock
  votes := h₁.votes.trans h₂.votes
  lr hb := (h₁.lr hb).trans (h₂.lr (by unfold BufValid at hb ⊢; rw [h₁.buf]; exact hb))
  tok h := h₂.tok (h₁.tok h)
  vview q hq hq' := by
    by_cases h : q ∈ s'.votes
    · exact h₁.vview q h hq'
    · exact h₁.view.trans (h₂.vview q hq h)
  view := h₁.view.trans h₂.view
  committed := h₁.committed.trans h₂.committed

theorem LR.single {V : Set (P × QC C)} {l l' : Loc C} {o : Option (QC C)} {m : Set (QC C)}
    (h : LStep f F V l l' o) : LR f F V (l, m) (l', m ∪ {q | o = some q}) :=
  Relation.ReflTransGen.single ⟨o, h, rfl⟩

/-! ### Auxiliary facts -/

theorem bestQC_cases (l : List (QCm P C)) : bestQC l = QCm.gen ∨ bestQC l ∈ l := by
  induction l with
  | nil => exact Or.inl rfl
  | cons j js ih =>
    simp only [bestQC]
    split_ifs
    · exact Or.inr (List.mem_cons_self ..)
    · rcases ih with h | h
      · exact Or.inl h
      · exact Or.inr (List.mem_cons_of_mem _ h)

theorem le_bestQC (l : List (QCm P C)) : ∀ j ∈ l, j.qc.view ≤ (bestQC l).qc.view := by
  induction l with
  | nil => simp
  | cons j js ih =>
    intro j' hj'
    simp only [bestQC]
    rcases List.mem_cons.mp hj' with rfl | hj'
    · split_ifs with h
      · exact le_rfl
      · omega
    · have := ih j' hj'
      split_ifs with h
      · omega
      · exact this

@[simp] theorem QCm.toks_gen : (QCm.gen : QCm P C).toks = ∅ := by
  ext k; simp [QCm.toks, QCm.gen]

theorem mem_nvJ {w : ℕ} {m : Msg P C} {j : QCm P C} (h : nvJ f w m = some j) :
    m = .newView w j ∧ j.ok f := by
  cases m with
  | newView w' j' =>
    simp only [nvJ] at h
    split_ifs at h with h'
    · cases h; exact ⟨by rw [h'.1], h'.2⟩
  | _ => simp [nvJ] at h

/-- The justification chosen by the leader only contains buffered tokens. -/
theorem best_toks (s : RState P C) (w : ℕ) :
    (bestQC (s.buf.filterMap fun m => nvJ f w m.2)).toks ⊆ bufToks s := by
  rcases bestQC_cases (s.buf.filterMap fun m => nvJ f w m.2) with h | h
  · rw [h]; simp
  · rw [List.mem_filterMap] at h
    obtain ⟨qm, hqm, hj⟩ := h
    obtain ⟨hm, -⟩ := mem_nvJ hj
    intro k hk
    exact ⟨qm, hqm, by rw [hm]; exact hk⟩

theorem TokOK.send {p : P} {s : RState P C} (h : TokOK p s) {g : P → List (Msg P C)}
    (hg : ∀ q, ∀ m ∈ g q, ∀ k ∈ m.toks, (k.1 = p ∧ k.2 ∈ s.votes) ∨ k ∈ bufToks s) :
    TokOK p (s.send g) where
  out q m hm k hk := by
    simp only [RState.send, List.mem_append] at hm
    rcases hm with hm | hm
    · exact h.out q m hm k hk
    · exact hg q m hm k hk
  prep := h.prep
  lock := h.lock

theorem mem_to1 {q q' : P} {m m' : Msg P C} (h : m' ∈ to1 q m q') : m' = m := by
  simp only [to1] at h; split_ifs at h <;> simp_all

/-! ### Handlers -/

variable (V : Set (P × QC C)) (p : P)

theorem hstep_L1 (s : RState P C) : HStep f F V p s (L1 f leader p s) := by
  unfold L1
  split_ifs with h
  · refine ⟨rfl, rfl, rfl, le_rfl, fun _ => Relation.ReflTransGen.refl, fun ht => ?_,
      fun _ h h' => absurd h h', le_rfl, le_rfl⟩
    have := ht.send (g := bcast (.prepare s.view (s.inp.2 s.view ::
      (bestQC (s.buf.filterMap fun m => nvJ f (s.view - 1) m.2)).qc.node)
      (bestQC (s.buf.filterMap fun m => nvJ f (s.view - 1) m.2)))) (by
        intro q m hm k hk
        simp only [bcast, List.mem_singleton] at hm
        subst hm
        exact Or.inr (best_toks s _ hk))
    exact ⟨this.out, this.prep, this.lock⟩
  · exact HStep.refl s

theorem hstep_LQ (k : ℕ) (s : RState P C) : HStep f F V p s (LQ f leader p k s) := by
  unfold LQ
  split_ifs with h
  · refine ⟨rfl, rfl, rfl, le_rfl, fun _ => Relation.ReflTransGen.refl, fun ht => ?_,
      fun _ h h' => absurd h h', le_rfl, le_rfl⟩
    have := ht.send (g := bcast (.cert ⟨⟨lty k, s.view, s.prop⟩,
      voters s ⟨lty k, s.view, s.prop⟩⟩)) (by
        intro q m hm t ht
        simp only [bcast, List.mem_singleton] at hm
        subst hm
        simp only [Msg.toks, QCm.toks, Set.mem_ofPred_eq, voters, Finset.mem_filter,
          Finset.mem_univ, true_and] at ht
        obtain ⟨⟨q', hq'⟩, h2⟩ := ht
        right
        refine ⟨(q', .vote t.1 ⟨lty k, s.view, s.prop⟩), hq', ?_⟩
        simp [Msg.toks, ← h2])
    exact ⟨this.out, this.prep, this.lock⟩
  · exact HStep.refl s

variable {V p} in
theorem TokOK.mk' {s s' : RState P C} (h : TokOK p s) (hb : s'.buf = s.buf)
    (hv : s.votes ⊆ s'.votes) {g : P → List (Msg P C)} (ho : ∀ q, s'.out q = s.out q ++ g q)
    (hg : ∀ q, ∀ m ∈ g q, ∀ k ∈ m.toks, (k.1 = p ∧ k.2 ∈ s'.votes) ∨ k ∈ bufToks s)
    (hp : s'.prepQC.toks ⊆ bufToks s) (hl : s'.lock.toks ⊆ bufToks s) : TokOK p s' where
  out q m hm k hk := by
    have hbt : bufToks s' = bufToks s := by simp [bufToks, hb]
    rw [hbt]
    rw [ho, List.mem_append] at hm
    rcases hm with hm | hm
    · rcases h.out q m hm k hk with h' | h'
      · exact Or.inl ⟨h'.1, hv h'.2⟩
      · exact Or.inr h'
    · exact hg q m hm k hk
  prep := by simp only [bufToks, hb]; exact hp
  lock := by simp only [bufToks, hb]; exact hl

theorem hstep_enterView (s : RState P C) : HStep f F V p s (enterView leader s) := by
  refine ⟨rfl, rfl, rfl, le_rfl, fun _ => ?_, fun ht => ?_, fun _ h h' => absurd h h', ?_, le_rfl⟩
  · exact Relation.ReflTransGen.single ⟨none, LStep.newView s.toLoc (s.view + 1) (by simp [RState.toLoc]),
      by simp [enterView, RState.send]⟩
  · refine ht.mk' rfl le_rfl (g := to1 (leader (s.view + 1)) (.newView s.view s.prepQC))
      (fun q => rfl) ?_ ht.prep ht.lock
    intro q m hm k hk
    rw [mem_to1 hm] at hk
    exact Or.inr (ht.prep hk)
  · simp [enterView, RState.send]

theorem hstep_R1 (s : RState P C) : HStep f F V p s (R1 f leader p s) := by
  unfold R1
  split_ifs with h
  swap
  · exact HStep.refl s
  dsimp only
  split_ifs with h'
  · set xj := Classical.choose h.2 with hxj
    have hmem := Classical.choose_spec h.2
    refine ⟨rfl, rfl, rfl, Set.subset_insert _ _, fun hb => ?_, fun ht => ?_, ?_, le_rfl, le_rfl⟩
    · have hst := LStep.prepVote (f := f) (F := F) (V := V) s.toLoc xj.1 xj.2.qc h.1
        (hb _ _ hmem xj.2 (by simp [Msg.qcs, xj]) h'.1) h'.2.1 h'.2.2
      convert LR.single (m := s.votes) hst using 2 <;> (try rfl) <;> (ext q; simp [eq_comm, or_comm, RState.toLoc])
    · refine ht.mk' rfl (Set.subset_insert _ _)
        (g := to1 (leader s.view) (.vote p ⟨.prepare, s.view, xj.1⟩)) (fun q => rfl) ?_
        ht.prep ht.lock
      intro q m hm k hk
      rw [mem_to1 hm] at hk
      simp only [Msg.toks, Set.mem_singleton_iff] at hk
      subst hk
      exact Or.inl ⟨rfl, Set.mem_insert _ _⟩
    · intro q hq hq'
      rcases Set.mem_insert_iff.mp hq with rfl | hq
      · exact le_rfl
      · exact absurd hq hq'
  · refine ⟨rfl, rfl, rfl, le_rfl, fun _ => ?_, fun ht => ⟨ht.out, ht.prep, ht.lock⟩,
      fun _ h h' => absurd h h', le_rfl, le_rfl⟩
    convert LR.single (m := s.votes) (LStep.prepSkip (f := f) (F := F) (V := V) s.toLoc h.1)
      using 2 <;> (try rfl) <;> simp

theorem hstep_R2 (s : RState P C) : HStep f F V p s (R2 f leader p s) := by
  unfold R2
  split_ifs with h
  · set j := Classical.choose h.2 with hj
    have hc : HasCert f leader .prepare s j := Classical.choose_spec h.2
    refine ⟨rfl, rfl, rfl, Set.subset_insert _ _, fun hb => ?_, fun ht => ?_, ?_, le_rfl, le_rfl⟩
    · have hst := LStep.precommitVote (f := f) (F := F) (V := V) s.toLoc j.qc h.1
        (hb _ _ hc.1 j (by simp [Msg.qcs]) hc.2.2.2) hc.2.1 hc.2.2.1
      convert LR.single (m := s.votes) hst using 2 <;> (try rfl) <;> (ext q; simp [eq_comm, or_comm, RState.toLoc])
    · refine ht.mk' rfl (Set.subset_insert _ _)
        (g := to1 (leader s.view) (.vote p ⟨.precommit, s.view, j.qc.node⟩)) (fun q => rfl) ?_
        ?_ ht.lock
      · intro q m hm k hk
        rw [mem_to1 hm] at hk
        simp only [Msg.toks, Set.mem_singleton_iff] at hk
        subst hk
        exact Or.inl ⟨rfl, Set.mem_insert _ _⟩
      · intro k hk; exact ⟨_, hc.1, by simpa [Msg.toks] using hk⟩
    · intro q hq hq'
      rcases Set.mem_insert_iff.mp hq with rfl | hq
      · exact le_rfl
      · exact absurd hq hq'
  · exact HStep.refl s

theorem hstep_R3 (s : RState P C) : HStep f F V p s (R3 f leader p s) := by
  unfold R3
  split_ifs with h
  · set j := Classical.choose h.2 with hj
    have hc : HasCert f leader .precommit s j := Classical.choose_spec h.2
    refine ⟨rfl, rfl, rfl, Set.subset_insert _ _, fun hb => ?_, fun ht => ?_, ?_, le_rfl, le_rfl⟩
    · have hst := LStep.commitVote (f := f) (F := F) (V := V) s.toLoc j.qc h.1
        (hb _ _ hc.1 j (by simp [Msg.qcs]) hc.2.2.2) hc.2.1 hc.2.2.1
      convert LR.single (m := s.votes) hst using 2 <;> (try rfl) <;> (ext q; simp [eq_comm, or_comm, RState.toLoc])
    · refine ht.mk' rfl (Set.subset_insert _ _)
        (g := to1 (leader s.view) (.vote p ⟨.commit, s.view, j.qc.node⟩)) (fun q => rfl) ?_
        ht.prep ?_
      · intro q m hm k hk
        rw [mem_to1 hm] at hk
        simp only [Msg.toks, Set.mem_singleton_iff] at hk
        subst hk
        exact Or.inl ⟨rfl, Set.mem_insert _ _⟩
      · intro k hk; exact ⟨_, hc.1, by simpa [Msg.toks] using hk⟩
    · intro q hq hq'
      rcases Set.mem_insert_iff.mp hq with rfl | hq
      · exact le_rfl
      · exact absurd hq hq'
  · exact HStep.refl s

theorem hstep_R4 (s : RState P C) : HStep f F V p s (R4 f leader s) := by
  unfold R4
  split_ifs with h
  · set j := Classical.choose h.2 with hj
    have hc : HasCert f leader .commit s j := Classical.choose_spec h.2
    refine HStep.trans (s' := s.commitNode j.qc.node)
      ⟨rfl, rfl, rfl, le_rfl, fun hb => ?_, fun ht => ⟨ht.out, ht.prep, ht.lock⟩,
        fun _ h h' => absurd h h', le_rfl, Set.subset_insert _ _⟩ (hstep_enterView V p _)
    have hst := LStep.decide (f := f) (F := F) (V := V) s.toLoc j.qc h.1
      (hb _ _ hc.1 j (by simp [Msg.qcs]) hc.2.2.2) hc.2.1 hc.2.2.1
    convert LR.single (m := s.votes) hst using 2 <;> (try rfl) <;> simp [RState.commitNode]
  · exact HStep.refl s

theorem mem_received {inbox : P → List (Msg P C)} {q : P} {m : Msg P C} :
    (q, m) ∈ received inbox ↔ m ∈ inbox q := by
  classical
  simp [received, List.mem_flatMap]

@[simp] theorem recv_toLoc (s : RState P C) (inbox : P → List (Msg P C)) :
    (recv s inbox).toLoc = s.toLoc := rfl

theorem TokOK.recv {s : RState P C} (h : TokOK p s) (inbox : P → List (Msg P C)) :
    TokOK p (recv s inbox) where
  out q m hm := by simp [HotStuff.Basic.recv] at hm
  prep k hk := by
    obtain ⟨qm, hqm, hk'⟩ := h.prep hk
    exact ⟨qm, by simp [HotStuff.Basic.recv, hqm], hk'⟩
  lock k hk := by
    obtain ⟨qm, hqm, hk'⟩ := h.lock hk
    exact ⟨qm, by simp [HotStuff.Basic.recv, hqm], hk'⟩

/-- The handlers of one step, after receiving the inbox. -/
theorem hstep_stepR (s : RState P C) (inbox : P → List (Msg P C)) :
    HStep f F V p (recv s inbox) (stepR f leader p s inbox) := by
  have h₁ := (hstep_L1 (leader := leader) (f := f) (F := F) V p (recv s inbox)).trans
    ((hstep_LQ (leader := leader) V p 1 _).trans ((hstep_LQ (leader := leader) V p 2 _).trans
      (hstep_LQ (leader := leader) V p 3 _)))
  have h₂ := h₁.trans ((hstep_R1 (leader := leader) V p _).trans
    ((hstep_R2 (leader := leader) V p _).trans ((hstep_R3 (leader := leader) V p _).trans
    (hstep_R4 (leader := leader) V p _))))
  unfold stepR
  dsimp only
  split_ifs
  · exact h₂.trans (hstep_enterView V p _)
  · exact h₂

end HotStuff.Basic
