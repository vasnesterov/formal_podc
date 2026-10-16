import Papers.PODC2019.HotStuff.Basic.LocalInv

/-!
# Basic HotStuff implementation: handler lemmas for the liveness proof

Monotonicity of the ghost variables, "every newly logged message is in the outbox", and the
firing conditions of the handlers.
-/

namespace HotStuff.Basic

open Classical Cslib.Byzantine.PartialSync

variable {P C : Type*} [Fintype P] [DecidableEq P] {f : ℕ} {leader : ℕ → P} {p : P}

/-- Growth of the logs along a handler. -/
structure Grow (s s' : RState P C) : Prop where
  sent : s.sent ⊆ s'.sent
  props : s.props ⊆ s'.props
  made : s.made ⊆ s'.made
  decs : s.decs ⊆ s'.decs
  votes : s.votes ⊆ s'.votes
  buf : ∀ qm ∈ s.buf, qm ∈ s'.buf

theorem Grow.refl (s : RState P C) : Grow s s := ⟨le_rfl, le_rfl, le_rfl, le_rfl, le_rfl, fun _ h => h⟩

theorem Grow.trans {s s' s'' : RState P C} (h : Grow s s') (h' : Grow s' s'') : Grow s s'' :=
  ⟨h.sent.trans h'.sent, h.props.trans h'.props, h.made.trans h'.made, h.decs.trans h'.decs,
    h.votes.trans h'.votes, fun qm hq => h'.buf qm (h.buf qm hq)⟩

/-- Newly logged messages are in the outbox (and the outbox only grows). -/
structure SentNew (s s' : RState P C) : Prop where
  out : OutMono s s'
  new : ∀ qm ∈ s'.sent, qm ∈ s.sent ∨ qm.2 ∈ s'.out qm.1

theorem SentNew.refl (s : RState P C) : SentNew s s := ⟨fun _ _ h => h, fun _ h => Or.inl h⟩

theorem SentNew.trans {s s' s'' : RState P C} (h : SentNew s s') (h' : SentNew s' s'') :
    SentNew s s'' :=
  ⟨h.out.trans h'.out, fun qm hq => by
    rcases h'.new qm hq with e | e
    · rcases h.new qm e with e' | e'
      · exact Or.inl e'
      · exact Or.inr (h'.out _ _ e')
    · exact Or.inr e⟩

theorem grow_send (s : RState P C) (g : P → List (Msg P C)) : Grow s (s.send g) :=
  ⟨fun _ h => mem_sent_send.mpr (Or.inl h), le_rfl, le_rfl, le_rfl, le_rfl, fun _ h => h⟩

theorem sentNew_send (s : RState P C) (g : P → List (Msg P C)) : SentNew s (s.send g) :=
  ⟨outMono_send s g, fun qm hq => by
    rcases mem_sent_send.mp hq with e | e
    · exact Or.inl e
    · exact Or.inr (mem_out_send.mpr (Or.inr e))⟩

theorem grow_enterView (s : RState P C) : Grow s (enterView leader s) :=
  ⟨fun _ h => by simp [enterView, RState.send, h], le_rfl, le_rfl, le_rfl, le_rfl, fun _ h => h⟩

theorem sentNew_enterView (s : RState P C) : SentNew s (enterView leader s) :=
  ⟨fun q m hm => by simp [enterView, RState.send, hm], fun qm hq => by
    simp only [enterView, RState.send, Set.mem_union, Set.mem_ofPred_eq, List.mem_append] at hq ⊢; tauto⟩

theorem grow_L1 (s : RState P C) : Grow s (L1 f leader p s) := by
  unfold L1; split_ifs
  · exact ⟨fun _ h => by simp [RState.send, h], Set.subset_insert _ _, le_rfl, le_rfl, le_rfl,
      fun _ h => h⟩
  · exact Grow.refl s

theorem sentNew_L1 (s : RState P C) : SentNew s (L1 f leader p s) := by
  unfold L1; split_ifs
  · exact ⟨fun q m hm => by simp [RState.send, hm], fun qm hq => by
      simp only [RState.send, Set.mem_union, Set.mem_ofPred_eq, List.mem_append] at hq ⊢; tauto⟩
  · exact SentNew.refl s

theorem grow_LQ (k : ℕ) (s : RState P C) : Grow s (LQ f leader p k s) := by
  unfold LQ; split_ifs
  · exact ⟨fun _ h => by simp [RState.send, h], le_rfl, Set.subset_insert _ _, le_rfl, le_rfl,
      fun _ h => h⟩
  · exact Grow.refl s

theorem sentNew_LQ (k : ℕ) (s : RState P C) : SentNew s (LQ f leader p k s) := by
  unfold LQ; split_ifs
  · exact ⟨fun q m hm => by simp [RState.send, hm], fun qm hq => by
      simp only [RState.send, Set.mem_union, Set.mem_ofPred_eq, List.mem_append] at hq ⊢; tauto⟩
  · exact SentNew.refl s

theorem grow_R1 (s : RState P C) : Grow s (R1 f leader p s) := by
  unfold R1; split_ifs
  · dsimp only; split_ifs
    · exact ⟨fun _ h => by simp [RState.send, h], le_rfl, le_rfl, le_rfl, Set.subset_insert _ _,
        fun _ h => h⟩
    · exact ⟨le_rfl, le_rfl, le_rfl, le_rfl, le_rfl, fun _ h => h⟩
  · exact Grow.refl s

theorem sentNew_R1 (s : RState P C) : SentNew s (R1 f leader p s) := by
  unfold R1; split_ifs
  · dsimp only; split_ifs
    · exact ⟨fun q m hm => by simp [RState.send, hm], fun qm hq => by
        simp only [RState.send, Set.mem_union, Set.mem_ofPred_eq, List.mem_append] at hq ⊢; tauto⟩
    · exact ⟨fun _ _ h => h, fun _ h => Or.inl h⟩
  · exact SentNew.refl s

theorem grow_R2 (s : RState P C) : Grow s (R2 f leader p s) := by
  unfold R2; split_ifs
  · exact ⟨fun _ h => by simp [RState.send, h], le_rfl, le_rfl, le_rfl, Set.subset_insert _ _,
      fun _ h => h⟩
  · exact Grow.refl s

theorem sentNew_R2 (s : RState P C) : SentNew s (R2 f leader p s) := by
  unfold R2; split_ifs
  · exact ⟨fun q m hm => by simp [RState.send, hm], fun qm hq => by
      simp only [RState.send, Set.mem_union, Set.mem_ofPred_eq, List.mem_append] at hq ⊢; tauto⟩
  · exact SentNew.refl s

theorem grow_R3 (s : RState P C) : Grow s (R3 f leader p s) := by
  unfold R3; split_ifs
  · exact ⟨fun _ h => by simp [RState.send, h], le_rfl, le_rfl, le_rfl, Set.subset_insert _ _,
      fun _ h => h⟩
  · exact Grow.refl s

theorem sentNew_R3 (s : RState P C) : SentNew s (R3 f leader p s) := by
  unfold R3; split_ifs
  · exact ⟨fun q m hm => by simp [RState.send, hm], fun qm hq => by
      simp only [RState.send, Set.mem_union, Set.mem_ofPred_eq, List.mem_append] at hq ⊢; tauto⟩
  · exact SentNew.refl s

theorem grow_R4 (s : RState P C) : Grow s (R4 f leader s) := by
  unfold R4; split_ifs
  · exact (show Grow s (s.commitNode _) from ⟨le_rfl, le_rfl, le_rfl, Set.subset_insert _ _,
      le_rfl, fun _ h => h⟩).trans (grow_enterView _)
  · exact Grow.refl s

theorem sentNew_R4 (s : RState P C) : SentNew s (R4 f leader s) := by
  unfold R4; split_ifs
  · exact (show SentNew s (s.commitNode _) from ⟨fun _ _ h => h, fun _ h => Or.inl h⟩).trans
      (sentNew_enterView _)
  · exact SentNew.refl s

theorem grow_recv (s : RState P C) (inbox : P → List (Msg P C)) : Grow s (recv s inbox) :=
  ⟨le_rfl, le_rfl, le_rfl, le_rfl, le_rfl, fun _ h => by simp [recv, h]⟩

/-- The handlers of a step, after receiving. -/
noncomputable def handlers (f : ℕ) (leader : ℕ → P) (p : P) (s : RState P C) : RState P C :=
  R4 f leader (R3 f leader p (R2 f leader p (R1 f leader p
    (LQ f leader p 3 (LQ f leader p 2 (LQ f leader p 1 (L1 f leader p s)))))))

theorem stepR_eq (s : RState P C) (inbox : P → List (Msg P C)) :
    stepR f leader p s inbox = if s.inp.1 s.clock then enterView leader
      (handlers f leader p (recv s inbox)) else handlers f leader p (recv s inbox) := rfl

theorem grow_handlers (s : RState P C) : Grow s (handlers f leader p s) :=
  (grow_L1 s).trans <| (grow_LQ 1 _).trans <| (grow_LQ 2 _).trans <| (grow_LQ 3 _).trans <|
    (grow_R1 _).trans <| (grow_R2 _).trans <| (grow_R3 _).trans (grow_R4 _)

theorem sentNew_handlers (s : RState P C) : SentNew s (handlers f leader p s) :=
  (sentNew_L1 s).trans <| (sentNew_LQ 1 _).trans <| (sentNew_LQ 2 _).trans <|
    (sentNew_LQ 3 _).trans <| (sentNew_R1 _).trans <| (sentNew_R2 _).trans <|
    (sentNew_R3 _).trans (sentNew_R4 _)

theorem grow_stepR (s : RState P C) (inbox : P → List (Msg P C)) :
    Grow s (stepR f leader p s inbox) := by
  rw [stepR_eq]; split_ifs
  · exact ((grow_recv s inbox).trans (grow_handlers _)).trans (grow_enterView _)
  · exact (grow_recv s inbox).trans (grow_handlers _)

/-- New log entries of a step are in the new outbox. -/
theorem sentNew_stepR (s : RState P C) (inbox : P → List (Msg P C)) :
    ∀ qm ∈ (stepR f leader p s inbox).sent, qm ∈ s.sent ∨
      qm.2 ∈ (stepR f leader p s inbox).out qm.1 := by
  have h : SentNew (recv s inbox) (stepR f leader p s inbox) := by
    rw [stepR_eq]; split_ifs
    · exact (sentNew_handlers _).trans (sentNew_enterView _)
    · exact sentNew_handlers _
  intro qm hq
  rcases h.new qm hq with e | e
  · exact Or.inl e
  · exact Or.inr e

/-! ### Firing conditions -/

theorem L1_of_ne {s : RState P C} (h : s.lphase ≠ 0) : L1 f leader p s = s := by
  unfold L1; rw [if_neg (by tauto)]

theorem LQ_of_ne {s : RState P C} {k : ℕ} (h : s.lphase ≠ k) : LQ f leader p k s = s := by
  unfold LQ; rw [if_neg (by tauto)]

theorem L1_fires {s : RState P C} (h0 : s.lphase = 0) (hp : p = leader s.view)
    (hc : Fintype.card P - f ≤ (nvSenders f s).card) : 1 ≤ (L1 f leader p s).lphase ∧
    ∃ x j, (s.view, x, j) ∈ (L1 f leader p s).props := by
  unfold L1; rw [if_pos ⟨h0, hp, hc⟩]
  exact ⟨le_rfl, _, _, Set.mem_insert _ _⟩

theorem LQ_fires {s : RState P C} {k : ℕ} (h0 : s.lphase = k) (hp : p = leader s.view)
    (hc : Fintype.card P - f ≤ (voters s ⟨lty k, s.view, s.prop⟩).card) :
    ∃ c ∈ (LQ f leader p k s).made, c.qc = ⟨lty k, s.view, s.prop⟩ := by
  unfold LQ; rw [if_pos ⟨h0, hp, hc⟩]
  exact ⟨_, Set.mem_insert _ _, rfl⟩

theorem R1_phase (s : RState P C) : s.phase ≤ (R1 f leader p s).phase := by
  unfold R1; split_ifs with h
  · dsimp only; split_ifs <;> simp [RState.send, h.1]
  · exact le_rfl

theorem R1_fires {s : RState P C} (h0 : s.phase = 0)
    (hm : ∃ xj : Node C × QCm P C, (leader s.view, Msg.prepare s.view xj.1 xj.2) ∈ s.buf) :
    1 ≤ (R1 f leader p s).phase := by
  unfold R1; rw [dif_pos ⟨h0, hm⟩]; dsimp only; split_ifs <;> simp [RState.send]

theorem R2_phase (s : RState P C) : s.phase ≤ (R2 f leader p s).phase := by
  unfold R2; split_ifs with h
  · simp [RState.send, h.1]
  · exact le_rfl

theorem R2_fires {s : RState P C} (h0 : s.phase = 1)
    (hm : ∃ c, HasCert f leader .prepare s c) : 2 ≤ (R2 f leader p s).phase := by
  unfold R2; rw [dif_pos ⟨h0, hm⟩]

theorem R3_phase (s : RState P C) : s.phase ≤ (R3 f leader p s).phase := by
  unfold R3; split_ifs with h
  · simp [RState.send, h.1]
  · exact le_rfl

theorem R3_fires {s : RState P C} (h0 : s.phase = 2)
    (hm : ∃ c, HasCert f leader .precommit s c) : 3 ≤ (R3 f leader p s).phase := by
  unfold R3; rw [dif_pos ⟨h0, hm⟩]

theorem R4_cases (s : RState P C) : (R4 f leader s = s) ∨
    ((R4 f leader s).view = s.view + 1 ∧ ∃ y, (s.view, y) ∈ (R4 f leader s).decs) := by
  unfold R4; split_ifs
  · right; exact ⟨rfl, _, Set.mem_insert _ _⟩
  · left; rfl

theorem R4_fires {s : RState P C} (h0 : s.phase = 3)
    (hm : ∃ c, HasCert f leader .commit s c) : ∃ y, (s.view, y) ∈ (R4 f leader s).decs := by
  unfold R4; rw [dif_pos ⟨h0, hm⟩]
  exact ⟨_, Set.mem_insert _ _⟩

/-! ### QCs formed by a leader are locally valid -/

/-- Made QCs are locally valid. -/
def MadeOk (f : ℕ) (s : RState P C) : Prop := ∀ c ∈ s.made, c.ok f

theorem madeOk_LQ {s : RState P C} (h : MadeOk f s) (k : ℕ) : MadeOk f (LQ f leader p k s) := by
  unfold LQ; split_ifs with hc
  · intro c hc'
    rcases Set.mem_insert_iff.mp hc' with rfl | hc'
    · exact Or.inr hc.2.2
    · exact h c hc'
  · exact h

theorem madeOk_handlers {s : RState P C} (h : MadeOk f s) : MadeOk f (handlers f leader p s) := by
  have h1 : MadeOk f (LQ f leader p 3 (LQ f leader p 2 (LQ f leader p 1 (L1 f leader p s)))) :=
    madeOk_LQ (madeOk_LQ (madeOk_LQ (fun c hc => h c (by rwa [L1_made] at hc)) 1) 2) 3
  intro c hc
  simp only [handlers, R4_made, R3_made, R2_made, R1_made] at hc
  exact h1 c hc

@[simp] theorem recv_made (s : RState P C) (inbox : P → List (Msg P C)) :
    (recv s inbox).made = s.made := rfl

theorem MadeOk.of_eq {s s' : RState P C} (h : MadeOk f s) (e : s'.made = s.made) :
    MadeOk f s' := fun c hc => h c (e ▸ hc)

theorem madeOk_stepR {s : RState P C} (h : MadeOk f s) (inbox : P → List (Msg P C)) :
    MadeOk f (stepR f leader p s inbox) := by
  have h0 : MadeOk f (recv s inbox) := h.of_eq (recv_made s inbox)
  have h' := ((((madeOk_LQ (leader := leader) (p := p) (madeOk_LQ (leader := leader) (p := p)
    (madeOk_LQ (leader := leader) (p := p) ((h0.of_eq (L1_made (leader := leader) (p := p)
    f _))) 1) 2) 3).of_eq (R1_made f leader p _)).of_eq (R2_made f leader p _)).of_eq
    (R3_made f leader p _)).of_eq (R4_made f leader _)
  unfold HotStuff.Basic.stepR
  dsimp only
  split_ifs
  · exact h'.of_eq (enterView_made leader _)
  · exact h'

end HotStuff.Basic
