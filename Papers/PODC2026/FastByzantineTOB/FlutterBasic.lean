import Papers.PODC2026.FastByzantineTOB.FlutterModel

set_option linter.unusedSectionVars false

/-!
# Flutter: basic lemmas about the model

Projection lemmas for the state updates, and monotonicity of the history variables along steps.
-/

namespace Podc.FastByzantineTOB.Flutter

variable {P C M T : Type*} [LinearOrder C] [LinearOrder M] [LinearOrder T] [AddCommMonoid T]
  [Fintype P] [DecidableEq P] [DecidableEq C]

/-! ### Lock time -/

section LockTime

variable {q : ℕ} {rt rt' : P → WithBot T}

/-- Characterization of `lock_time()` (Observation 6): `t ≤ lock_time()` iff at least `q` entries
of `remote_times` are `≥ t`. -/
lemma le_lockTime_iff (hq : 1 ≤ q) (t : T) :
    (t : WithBot T) ≤ lockTime q rt ↔ q ≤ (Finset.univ.filter fun ρ => (t : WithBot T) ≤ rt ρ).card := by
  unfold lockTime
  constructor
  · intro h
    obtain ⟨σ, hσ, hle⟩ := (Finset.le_sup_iff (WithBot.bot_lt_coe t)).mp h
    rw [Finset.mem_filter] at hσ
    refine hσ.2.trans (Finset.card_le_card fun ρ hρ => ?_)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hρ ⊢
    exact hle.trans hρ
  · intro h
    set A := Finset.univ.filter fun ρ => (t : WithBot T) ≤ rt ρ
    have hA : A.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨σ, hσA, hmin⟩ := A.exists_min_image rt hA
    have hσ : (t : WithBot T) ≤ rt σ := (Finset.mem_filter.mp hσA).2
    refine hσ.trans (Finset.le_sup (f := rt) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩))
    refine h.trans (Finset.card_le_card fun ρ hρ => ?_)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hmin ρ hρ

/-- Observation 6: `lock_time()` is monotone in `remote_times`. -/
lemma lockTime_mono (hq : 1 ≤ q) (h : ∀ σ, rt σ ≤ rt' σ) : lockTime q rt ≤ lockTime q rt' := by
  cases hl : lockTime q rt with
  | bot => exact bot_le
  | coe t =>
    have := (le_lockTime_iff hq t).mp hl.symm.le
    rw [le_lockTime_iff hq]
    exact this.trans (Finset.card_le_card fun ρ hρ => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hρ ⊢
      exact hρ.trans (h ρ))

lemma lockTime_bot (hq : 1 ≤ q) : lockTime q (fun _ : P => (⊥ : WithBot T)) = ⊥ := by
  cases hl : lockTime q (fun _ : P => (⊥ : WithBot T)) with
  | bot => rfl
  | coe t =>
    have := (le_lockTime_iff hq t).mp hl.symm.le
    simp at this
    omega

end LockTime

section Simp

variable (s : State P C M T)

@[simp] lemma updSrv_srv (p : P) (f) : (s.updSrv p f).srv = Function.update s.srv p (f (s.srv p)) :=
  rfl
@[simp] lemma updSrv_cli (p : P) (f) : (s.updSrv p f).cli = s.cli := rfl
@[simp] lemma updSrv_sent (p : P) (f) : (s.updSrv p f).sent = s.sent := rfl
@[simp] lemma updSrv_dlv (p : P) (f) : (s.updSrv p f).dlv = s.dlv := rfl
@[simp] lemma updCli_srv (θ : C) (f) : (s.updCli θ f).srv = s.srv := rfl
@[simp] lemma updCli_cli (θ : C) (f) :
    (s.updCli θ f).cli = Function.update s.cli θ (f (s.cli θ)) := rfl
@[simp] lemma updCli_sent (θ : C) (f) : (s.updCli θ f).sent = s.sent := rfl
@[simp] lemma updCli_dlv (θ : C) (f) : (s.updCli θ f).dlv = s.dlv := rfl
@[simp] lemma bump_srv (a b : Node P C) : (s.bump a b).srv = s.srv := rfl
@[simp] lemma bump_cli (a b : Node P C) : (s.bump a b).cli = s.cli := rfl
@[simp] lemma bump_sent (a b : Node P C) : (s.bump a b).sent = s.sent := rfl
lemma bump_dlv (a b : Node P C) :
    (s.bump a b).dlv = Function.update s.dlv a (Function.update (s.dlv a) b (s.dlv a b + 1)) := rfl

variable (S : Setup P C T)

/-- The candidates after `spot`. -/
noncomputable def spotCands (S : Setup P C T) (l : SState P C M T) (x : Tag C M T) :
    Finset (Tag C M T) :=
  if lockTime S.q l.remote < (x.bet : WithBot T) then insert x l.cands else l.cands

lemma spot_srv (p : P) (x : Tag C M T) : (s.spot S p x).srv = Function.update s.srv p
    { s.srv p with
      cands := spotCands S (s.srv p) x
      observed := insert x (s.srv p).observed
      obox := if x ∈ (s.srv p).observed then (s.srv p).obox
        else (s.srv p).obox ++ [.observe x] } := by
  unfold State.spot
  ext1 q
  by_cases hq : q = p
  · subst hq
    by_cases h1 : lockTime S.q (s.srv q).remote < (x.bet : WithBot T) <;>
      by_cases h2 : x ∈ (s.srv q).observed <;> simp [h1, h2, spotCands]
  · by_cases h1 : lockTime S.q (s.srv p).remote < (x.bet : WithBot T) <;>
      by_cases h2 : x ∈ (s.srv p).observed <;> simp [h1, h2, hq]

@[simp] lemma spot_cli (p : P) (x : Tag C M T) : (s.spot S p x).cli = s.cli := by
  unfold State.spot; split_ifs <;> simp

@[simp] lemma spot_dlv (p : P) (x : Tag C M T) : (s.spot S p x).dlv = s.dlv := by
  unfold State.spot; split_ifs <;> simp

lemma spot_sent (p : P) (x : Tag C M T) : (s.spot S p x).sent =
    if x ∈ (s.srv p).observed then s.sent else sendAll s.sent (.inl p) (.observe x) := by
  unfold State.spot; split_ifs <;> simp

@[simp] lemma recv_srv (a b : Node P C) : (s.recv S a b).srv = s.srv := by
  unfold State.recv; split_ifs <;> rfl
@[simp] lemma recv_cli (a b : Node P C) : (s.recv S a b).cli = s.cli := by
  unfold State.recv; split_ifs <;> rfl
@[simp] lemma recv_sent (a b : Node P C) : (s.recv S a b).sent = s.sent := by
  unfold State.recv; split_ifs <;> rfl

@[simp] lemma submit_srv (θ : C) (m : M) (r : ℕ) : (s.submit S θ m r).srv = s.srv := rfl
@[simp] lemma submit_dlv (θ : C) (m : M) (r : ℕ) : (s.submit S θ m r).dlv = s.dlv := rfl
lemma submit_sent (θ : C) (m : M) (r : ℕ) : (s.submit S θ m r).sent =
    sendAll s.sent (.inr θ) (.message m ((s.cli θ).clock + 2 ^ r • S.dEst + S.eps)) := rfl
lemma submit_cli (θ : C) (m : M) (r : ℕ) : (s.submit S θ m r).cli = Function.update s.cli θ
    { s.cli θ with
      subs := Function.update (s.cli θ).subs m (some (r, (s.cli θ).clock + 2 ^ r • S.dEst + S.eps))
      cbox := (s.cli θ).cbox ++ [.message m ((s.cli θ).clock + 2 ^ r • S.dEst + S.eps)] }
    := rfl

end Simp

/-! ### Message lists only grow -/

lemma sendAll_prefix (sent : Node P C → Node P C → List (Msg C M T)) (a : Node P C) (msg)
    (x y : Node P C) : sent x y <+: sendAll sent a msg x y := by
  unfold sendAll; split_ifs <;> simp

lemma send1_prefix (sent : Node P C → Node P C → List (Msg C M T)) (a b : Node P C) (msg)
    (x y : Node P C) : sent x y <+: send1 sent a b msg x y := by
  unfold send1
  by_cases hx : x = a
  · subst hx
    by_cases hy : y = b
    · subst hy; simp
    · simp [hy]
  · simp [hx]

variable (S : Setup P C T)

lemma spot_sent_prefix (s : State P C M T) (p : P) (x : Tag C M T) (a b : Node P C) :
    s.sent a b <+: (s.spot S p x).sent a b := by
  rw [spot_sent]; split_ifs
  · exact List.prefix_refl _
  · exact sendAll_prefix _ _ _ _ _

lemma onSrv_sent_prefix (s : State P C M T) (p σ : P) (msg : Msg C M T) (a b : Node P C) :
    s.sent a b <+: (s.onSrv S p σ msg).sent a b := by
  cases msg
  · exact List.prefix_refl _
  · exact spot_sent_prefix S _ _ _ _ _
  · exact List.prefix_refl _
  · exact List.prefix_refl _

lemma accept_sent_prefix (s : State P C M T) (p : P) (x : Tag C M T) (a b : Node P C) :
    s.sent a b <+: (s.accept S p x).sent a b := by
  simp only [State.accept]; split_ifs
  · exact spot_sent_prefix S _ _ _ _ _
  · exact spot_sent_prefix S _ _ _ _ _

lemma onCli_sent_prefix (s : State P C M T) (p : P) (θ : C) (msg : Msg C M T) (a b : Node P C) :
    s.sent a b <+: (s.onCli S p θ msg).sent a b := by
  cases msg
  · exact List.prefix_refl _
  · exact List.prefix_refl _
  · exact accept_sent_prefix S _ _ _ _ _
  · exact List.prefix_refl _

lemma onDec_sent (s : State P C M T) (θ : C) (σ : P) (msg : Msg C M T) :
    (s.onDec θ σ msg).sent = s.sent := by
  cases msg <;> rfl

lemma exec_sent_prefix (s : State P C M T) (act : Action P C M T) (a b : Node P C) :
    s.sent a b <+: (exec S s act).sent a b := by
  cases act with
  | tick => exact List.prefix_refl _
  | beat => exact sendAll_prefix _ _ _ _ _
  | srvRecv p σ msg => simpa [exec] using onSrv_sent_prefix S (s.recv S _ _) p σ msg a b
  | cliMsg p θ msg => simpa [exec] using onCli_sent_prefix S (s.recv S _ _) p θ msg a b
  | proposeFalse => exact List.prefix_refl _
  | decide => exact send1_prefix _ _ _ _ _ _
  | process => exact List.prefix_refl _
  | cTick => exact List.prefix_refl _
  | cBroadcast => exact sendAll_prefix _ _ _ _ _
  | cRecv θ σ msg => simp [exec, onDec_sent]
  | cRetry θ m =>
    simp only [exec]
    split
    · exact sendAll_prefix _ _ _ _ _
    · exact List.prefix_refl _

end Podc.FastByzantineTOB.Flutter
