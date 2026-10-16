import Papers.PODC2019.HotStuff.Basic.Refinement

/-!
# Basic HotStuff implementation: field lemmas for the handlers

Which state components each handler leaves unchanged, and that handlers only append to the
outbox. Used in the liveness proof.
-/

namespace HotStuff.Basic

open Classical Cslib.Byzantine.PartialSync

variable {P C : Type*} [Fintype P] [DecidableEq P] (f : ℕ) (leader : ℕ → P) (p : P)
variable (s : RState P C)

@[simp] theorem L1_view : (L1 f leader p s).view = s.view := by unfold L1; split_ifs <;> rfl
@[simp] theorem L1_phase : (L1 f leader p s).phase = s.phase := by unfold L1; split_ifs <;> rfl
@[simp] theorem L1_lock : (L1 f leader p s).lock = s.lock := by unfold L1; split_ifs <;> rfl
@[simp] theorem L1_prepQC : (L1 f leader p s).prepQC = s.prepQC := by unfold L1; split_ifs <;> rfl
@[simp] theorem L1_committed : (L1 f leader p s).committed = s.committed := by unfold L1; split_ifs <;> rfl
@[simp] theorem L1_votes : (L1 f leader p s).votes = s.votes := by unfold L1; split_ifs <;> rfl
@[simp] theorem L1_buf : (L1 f leader p s).buf = s.buf := by unfold L1; split_ifs <;> rfl
@[simp] theorem L1_inp : (L1 f leader p s).inp = s.inp := by unfold L1; split_ifs <;> rfl
@[simp] theorem L1_decs : (L1 f leader p s).decs = s.decs := by unfold L1; split_ifs <;> rfl
@[simp] theorem L1_clock : (L1 f leader p s).clock = s.clock := by unfold L1; split_ifs <;> rfl
@[simp] theorem L1_made : (L1 f leader p s).made = s.made := by unfold L1; split_ifs <;> rfl

@[simp] theorem LQ_view (k : ℕ) : (LQ f leader p k s).view = s.view := by unfold LQ; split_ifs <;> rfl
@[simp] theorem LQ_phase (k : ℕ) : (LQ f leader p k s).phase = s.phase := by unfold LQ; split_ifs <;> rfl
@[simp] theorem LQ_lock (k : ℕ) : (LQ f leader p k s).lock = s.lock := by unfold LQ; split_ifs <;> rfl
@[simp] theorem LQ_prepQC (k : ℕ) : (LQ f leader p k s).prepQC = s.prepQC := by unfold LQ; split_ifs <;> rfl
@[simp] theorem LQ_committed (k : ℕ) : (LQ f leader p k s).committed = s.committed := by unfold LQ; split_ifs <;> rfl
@[simp] theorem LQ_votes (k : ℕ) : (LQ f leader p k s).votes = s.votes := by unfold LQ; split_ifs <;> rfl
@[simp] theorem LQ_buf (k : ℕ) : (LQ f leader p k s).buf = s.buf := by unfold LQ; split_ifs <;> rfl
@[simp] theorem LQ_inp (k : ℕ) : (LQ f leader p k s).inp = s.inp := by unfold LQ; split_ifs <;> rfl
@[simp] theorem LQ_decs (k : ℕ) : (LQ f leader p k s).decs = s.decs := by unfold LQ; split_ifs <;> rfl
@[simp] theorem LQ_clock (k : ℕ) : (LQ f leader p k s).clock = s.clock := by unfold LQ; split_ifs <;> rfl
@[simp] theorem LQ_props (k : ℕ) : (LQ f leader p k s).props = s.props := by unfold LQ; split_ifs <;> rfl

@[simp] theorem R1_view : (R1 f leader p s).view = s.view := by unfold R1; dsimp only; split_ifs <;> rfl
@[simp] theorem R1_lphase : (R1 f leader p s).lphase = s.lphase := by unfold R1; dsimp only; split_ifs <;> rfl
@[simp] theorem R1_prop : (R1 f leader p s).prop = s.prop := by unfold R1; dsimp only; split_ifs <;> rfl
@[simp] theorem R1_high : (R1 f leader p s).high = s.high := by unfold R1; dsimp only; split_ifs <;> rfl
@[simp] theorem R1_props : (R1 f leader p s).props = s.props := by unfold R1; dsimp only; split_ifs <;> rfl
@[simp] theorem R1_made : (R1 f leader p s).made = s.made := by unfold R1; dsimp only; split_ifs <;> rfl
@[simp] theorem R1_buf : (R1 f leader p s).buf = s.buf := by unfold R1; dsimp only; split_ifs <;> rfl
@[simp] theorem R1_inp : (R1 f leader p s).inp = s.inp := by unfold R1; dsimp only; split_ifs <;> rfl
@[simp] theorem R1_committed : (R1 f leader p s).committed = s.committed := by unfold R1; dsimp only; split_ifs <;> rfl
@[simp] theorem R1_decs : (R1 f leader p s).decs = s.decs := by unfold R1; dsimp only; split_ifs <;> rfl
@[simp] theorem R1_clock : (R1 f leader p s).clock = s.clock := by unfold R1; dsimp only; split_ifs <;> rfl
@[simp] theorem R1_prepQC : (R1 f leader p s).prepQC = s.prepQC := by unfold R1; dsimp only; split_ifs <;> rfl
@[simp] theorem R1_lock : (R1 f leader p s).lock = s.lock := by unfold R1; dsimp only; split_ifs <;> rfl

@[simp] theorem R2_view : (R2 f leader p s).view = s.view := by unfold R2; split_ifs <;> rfl
@[simp] theorem R2_lphase : (R2 f leader p s).lphase = s.lphase := by unfold R2; split_ifs <;> rfl
@[simp] theorem R2_prop : (R2 f leader p s).prop = s.prop := by unfold R2; split_ifs <;> rfl
@[simp] theorem R2_high : (R2 f leader p s).high = s.high := by unfold R2; split_ifs <;> rfl
@[simp] theorem R2_props : (R2 f leader p s).props = s.props := by unfold R2; split_ifs <;> rfl
@[simp] theorem R2_made : (R2 f leader p s).made = s.made := by unfold R2; split_ifs <;> rfl
@[simp] theorem R2_buf : (R2 f leader p s).buf = s.buf := by unfold R2; split_ifs <;> rfl
@[simp] theorem R2_inp : (R2 f leader p s).inp = s.inp := by unfold R2; split_ifs <;> rfl
@[simp] theorem R2_committed : (R2 f leader p s).committed = s.committed := by unfold R2; split_ifs <;> rfl
@[simp] theorem R2_decs : (R2 f leader p s).decs = s.decs := by unfold R2; split_ifs <;> rfl
@[simp] theorem R2_clock : (R2 f leader p s).clock = s.clock := by unfold R2; split_ifs <;> rfl
@[simp] theorem R2_lock : (R2 f leader p s).lock = s.lock := by unfold R2; split_ifs <;> rfl

@[simp] theorem R3_view : (R3 f leader p s).view = s.view := by unfold R3; split_ifs <;> rfl
@[simp] theorem R3_lphase : (R3 f leader p s).lphase = s.lphase := by unfold R3; split_ifs <;> rfl
@[simp] theorem R3_prop : (R3 f leader p s).prop = s.prop := by unfold R3; split_ifs <;> rfl
@[simp] theorem R3_high : (R3 f leader p s).high = s.high := by unfold R3; split_ifs <;> rfl
@[simp] theorem R3_props : (R3 f leader p s).props = s.props := by unfold R3; split_ifs <;> rfl
@[simp] theorem R3_made : (R3 f leader p s).made = s.made := by unfold R3; split_ifs <;> rfl
@[simp] theorem R3_buf : (R3 f leader p s).buf = s.buf := by unfold R3; split_ifs <;> rfl
@[simp] theorem R3_inp : (R3 f leader p s).inp = s.inp := by unfold R3; split_ifs <;> rfl
@[simp] theorem R3_committed : (R3 f leader p s).committed = s.committed := by unfold R3; split_ifs <;> rfl
@[simp] theorem R3_decs : (R3 f leader p s).decs = s.decs := by unfold R3; split_ifs <;> rfl
@[simp] theorem R3_clock : (R3 f leader p s).clock = s.clock := by unfold R3; split_ifs <;> rfl
@[simp] theorem R3_prepQC : (R3 f leader p s).prepQC = s.prepQC := by unfold R3; split_ifs <;> rfl

@[simp] theorem R4_buf : (R4 f leader s).buf = s.buf := by unfold R4; split_ifs <;> rfl
@[simp] theorem R4_inp : (R4 f leader s).inp = s.inp := by unfold R4; split_ifs <;> rfl
@[simp] theorem R4_props : (R4 f leader s).props = s.props := by unfold R4; split_ifs <;> rfl
@[simp] theorem R4_made : (R4 f leader s).made = s.made := by unfold R4; split_ifs <;> rfl
@[simp] theorem R4_clock : (R4 f leader s).clock = s.clock := by unfold R4; split_ifs <;> rfl
@[simp] theorem R4_prepQC : (R4 f leader s).prepQC = s.prepQC := by unfold R4; split_ifs <;> rfl
@[simp] theorem R4_lock : (R4 f leader s).lock = s.lock := by unfold R4; split_ifs <;> rfl
@[simp] theorem R4_votes : (R4 f leader s).votes = s.votes := by unfold R4; split_ifs <;> rfl

@[simp] theorem enterView_buf : (enterView leader s).buf = s.buf := by rfl
@[simp] theorem enterView_inp : (enterView leader s).inp = s.inp := by rfl
@[simp] theorem enterView_props : (enterView leader s).props = s.props := by rfl
@[simp] theorem enterView_made : (enterView leader s).made = s.made := by rfl
@[simp] theorem enterView_clock : (enterView leader s).clock = s.clock := by rfl
@[simp] theorem enterView_prepQC : (enterView leader s).prepQC = s.prepQC := by rfl
@[simp] theorem enterView_lock : (enterView leader s).lock = s.lock := by rfl
@[simp] theorem enterView_votes : (enterView leader s).votes = s.votes := by rfl
@[simp] theorem enterView_committed : (enterView leader s).committed = s.committed := by rfl
@[simp] theorem enterView_decs : (enterView leader s).decs = s.decs := by rfl

@[simp] theorem enterView_view : (enterView leader s).view = s.view + 1 := rfl
@[simp] theorem enterView_phase : (enterView leader s).phase = 0 := rfl
@[simp] theorem enterView_lphase : (enterView leader s).lphase = 0 := rfl

theorem enterView_out (q : P) :
    (enterView leader s).out q = s.out q ++ to1 (leader (s.view + 1)) (.newView s.view s.prepQC) q :=
  rfl

/-- Handlers only append to the outbox. -/
def OutMono (s s' : RState P C) : Prop := ∀ q, ∀ m ∈ s.out q, m ∈ s'.out q

theorem OutMono.trans {s s' s'' : RState P C} (h : OutMono s s') (h' : OutMono s' s'') :
    OutMono s s'' := fun q m hm => h' q m (h q m hm)

theorem outMono_send (g : P → List (Msg P C)) : OutMono s (s.send g) := by
  intro q m hm; simp [RState.send, hm]

theorem outMono_enterView : OutMono s (enterView leader s) := by
  intro q m hm; simp [enterView_out, hm]

theorem outMono_L1 : OutMono s (L1 f leader p s) := by
  unfold L1; split_ifs
  · intro q m hm; simp [RState.send, hm]
  · exact fun _ _ h => h

theorem outMono_LQ (k : ℕ) : OutMono s (LQ f leader p k s) := by
  unfold LQ; split_ifs
  · intro q m hm; simp [RState.send, hm]
  · exact fun _ _ h => h

theorem outMono_R1 : OutMono s (R1 f leader p s) := by
  unfold R1; split_ifs
  · dsimp only; split_ifs
    · intro q m hm; simp [RState.send, hm]
    · exact fun _ _ h => h
  · exact fun _ _ h => h

theorem outMono_R2 : OutMono s (R2 f leader p s) := by
  unfold R2; split_ifs
  · intro q m hm; simp [RState.send, hm]
  · exact fun _ _ h => h

theorem outMono_R3 : OutMono s (R3 f leader p s) := by
  unfold R3; split_ifs
  · intro q m hm; simp [RState.send, hm]
  · exact fun _ _ h => h

theorem outMono_R4 : OutMono s (R4 f leader s) := by
  unfold R4; split_ifs
  · intro q m hm; simp [enterView_out, RState.commitNode, hm]
  · exact fun _ _ h => h

end HotStuff.Basic
