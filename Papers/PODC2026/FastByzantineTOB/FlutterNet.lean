import Papers.PODC2026.FastByzantineTOB.FlutterLocal

set_option linter.unusedSectionVars false

/-!
# Flutter: how a step changes the links

Characterization lemmas: which messages a step appends to which link, when `observed`, `props`,
`remote_times` and the delivery counters change.
-/

namespace Podc.FastByzantineTOB.Flutter

variable {P C M T : Type*} [LinearOrder C] [LinearOrder M] [LinearOrder T] [AddCommMonoid T]
  [Fintype P] [DecidableEq P] [DecidableEq C]

variable (S : Setup P C T)

lemma sendAll_apply (sent : Node P C → Node P C → List (Msg C M T)) (a x y : Node P C) (msg) :
    sendAll sent a msg x y = if x = a ∧ y.isLeft then sent x y ++ [msg] else sent x y := rfl

lemma send1_inl_inl (sent : Node P C → Node P C → List (Msg C M T)) (a : Node P C) (θ : C) (msg)
    (ρ σ : P) : send1 sent a (.inr θ) msg (.inl ρ) (.inl σ) = sent (.inl ρ) (.inl σ) := by
  unfold send1
  by_cases h : (Sum.inl ρ : Node P C) = a
  · subst h; simp
  · simp [h]

lemma send1_inr (sent : Node P C → Node P C → List (Msg C M T)) (p : P) (b : Node P C) (msg)
    (θ : C) (y : Node P C) : send1 sent (.inl p) b msg (.inr θ) y = sent (.inr θ) y := by
  simp [send1]

lemma spot_obox_sent (s : State P C M T) (p : P) (x : Tag C M T) (ρ σ : P)
    (h : s.sent (.inl ρ) (.inl σ) = (s.srv ρ).obox) :
    (s.spot S p x).sent (.inl ρ) (.inl σ) = ((s.spot S p x).srv ρ).obox := by
  rw [spot_sent, spot_srv]
  by_cases hρ : ρ = p
  · subst hρ
    rw [Function.update_self]
    split_ifs with hx
    · exact h
    · simp [sendAll_apply, h]
  · rw [Function.update_of_ne hρ]
    split_ifs
    · exact h
    · simp [sendAll_apply, hρ, h]

lemma accept_obox_sent (s : State P C M T) (p : P) (x : Tag C M T) (ρ σ : P)
    (h : s.sent (.inl ρ) (.inl σ) = (s.srv ρ).obox) :
    (s.accept S p x).sent (.inl ρ) (.inl σ) = ((s.accept S p x).srv ρ).obox := by
  have := spot_obox_sent S s p x ρ σ h
  simp only [State.accept]
  split_ifs
  · exact this
  · by_cases hρ : ρ = p
    · subst hρ; simpa using this
    · simpa [Function.update_of_ne hρ] using this

/-- Server-to-server links carry exactly the sender's `obox` (all such sends go to every server). -/
lemma exec_sent_obox (s : State P C M T) (a : Action P C M T)
    (h : ∀ ρ σ : P, s.sent (.inl ρ) (.inl σ) = (s.srv ρ).obox) (ρ σ : P) :
    (exec S s a).sent (.inl ρ) (.inl σ) = ((exec S s a).srv ρ).obox := by
  cases a with
  | tick p t =>
    by_cases hρ : ρ = p
    · subst hρ; simpa [exec] using h ρ σ
    · simpa [exec, Function.update_of_ne hρ] using h ρ σ
  | beat p =>
    by_cases hρ : ρ = p
    · subst hρ; simp [exec, sendAll_apply, h]
    · simp [exec, sendAll_apply, hρ, Function.update_of_ne hρ, h]
  | srvRecv p σ' msg =>
    cases msg with
    | time t =>
      by_cases hρ : ρ = p
      · subst hρ; simpa [exec, State.onSrv] using h ρ σ
      · simpa [exec, State.onSrv, Function.update_of_ne hρ] using h ρ σ
    | observe x =>
      simpa [exec, State.onSrv] using spot_obox_sent S (s.recv S _ _) p x ρ σ (by simpa using h ρ σ)
    | _ => simpa [exec, State.onSrv] using h ρ σ
  | cliMsg p θ msg =>
    cases msg with
    | message m b =>
      simpa [exec, State.onCli] using
        accept_obox_sent S (s.recv S _ _) p ⟨b, θ, m⟩ ρ σ (by simpa using h ρ σ)
    | _ => simpa [exec, State.onCli] using h ρ σ
  | proposeFalse p x =>
    by_cases hρ : ρ = p
    · subst hρ; simpa [exec] using h ρ σ
    · simpa [exec, Function.update_of_ne hρ] using h ρ σ
  | decide p x v =>
    simp only [exec, send1_inl_inl]
    by_cases hρ : ρ = p
    · subst hρ; simpa using h ρ σ
    · simpa [Function.update_of_ne hρ] using h ρ σ
  | process p x v =>
    by_cases hρ : ρ = p
    · subst hρ
      simp only [exec, updSrv_sent, updSrv_srv, Function.update_self, h ρ σ]
      split_ifs <;> simp [SState.order] <;> split_ifs <;> rfl
    · simpa [exec, Function.update_of_ne hρ] using h ρ σ
  | cTick θ t => simpa [exec] using h ρ σ
  | cBroadcast θ m => simpa [exec, submit_sent, sendAll_apply] using h ρ σ
  | cRecv θ σ' msg => cases msg <;> simpa [exec, State.onDec] using h ρ σ
  | cRetry θ m =>
    simp only [exec]; split
    · simpa [submit_sent, sendAll_apply] using h ρ σ
    · exact h ρ σ

lemma onSrv_cli (s : State P C M T) (p σ : P) (msg : Msg C M T) : (s.onSrv S p σ msg).cli = s.cli := by
  cases msg <;> simp [State.onSrv]

lemma onCli_cli (s : State P C M T) (p : P) (θ : C) (msg : Msg C M T) :
    (s.onCli S p θ msg).cli = s.cli := by
  cases msg <;> simp [State.onCli, State.accept] <;> split_ifs <;> simp

lemma onSrv_sent_inr (s : State P C M T) (p σ : P) (msg : Msg C M T) (θ : C) (b : Node P C) :
    (s.onSrv S p σ msg).sent (.inr θ) b = s.sent (.inr θ) b := by
  cases msg <;> simp [State.onSrv, spot_sent] <;> split_ifs <;> simp [sendAll_apply]

lemma onCli_sent_inr (s : State P C M T) (p : P) (θ' : C) (msg : Msg C M T) (θ : C)
    (b : Node P C) : (s.onCli S p θ' msg).sent (.inr θ) b = s.sent (.inr θ) b := by
  cases msg
  all_goals simp only [State.onCli, State.accept]
  all_goals (try split_ifs) <;> simp [spot_sent] <;> split_ifs <;> simp [sendAll_apply]

/-- Client-to-server links carry exactly the client's `cbox`. -/
lemma exec_sent_cbox (s : State P C M T) (a : Action P C M T)
    (h : ∀ (θ : C) (σ : P), s.sent (.inr θ) (.inl σ) = (s.cli θ).cbox) (θ : C) (σ : P) :
    (exec S s a).sent (.inr θ) (.inl σ) = ((exec S s a).cli θ).cbox := by
  cases a with
  | beat p => simpa [exec, sendAll_apply] using h θ σ
  | srvRecv p σ' msg => simpa [exec, onSrv_cli, onSrv_sent_inr] using h θ σ
  | cliMsg p θ' msg => simpa [exec, onCli_cli, onCli_sent_inr] using h θ σ
  | decide p x v => simpa [exec, send1_inr] using h θ σ
  | cTick θ' t =>
    by_cases hθ : θ = θ'
    · subst hθ; simpa [exec] using h θ σ
    · simpa [exec, Function.update_of_ne hθ] using h θ σ
  | cBroadcast θ' m =>
    by_cases hθ : θ = θ'
    · subst hθ; simp [exec, submit_sent, submit_cli, sendAll_apply, h]
    · simp [exec, submit_sent, submit_cli, sendAll_apply, hθ, Function.update_of_ne hθ, h]
  | cRecv θ' σ' msg =>
    cases msg with
    | decision m b v =>
      by_cases hθ : θ = θ'
      · subst hθ; simpa [exec, State.onDec] using h θ σ
      · simpa [exec, State.onDec, Function.update_of_ne hθ] using h θ σ
    | _ => simpa [exec, State.onDec] using h θ σ
  | cRetry θ' m =>
    simp only [exec]; split
    · by_cases hθ : θ = θ'
      · subst hθ; simp [submit_sent, submit_cli, sendAll_apply, h]
      · simp [submit_sent, submit_cli, sendAll_apply, hθ, Function.update_of_ne hθ, h]
    · exact h θ σ
  | _ => simpa [exec] using h θ σ

/-- Client invariant: messages sent by a client were broadcast (Lemmas 7 and 8). -/
structure CInv (l : CState P C M T) : Prop where
  /-- Lemma 8. -/
  cbox : ∀ m b, Msg.message m b ∈ l.cbox → m ∈ l.bcast
  /-- Lemma 7. -/
  subs : ∀ m, l.subs m ≠ none → m ∈ l.bcast

lemma exec_cinv (s : State P C M T) (a : Action P C M T) (h : ∀ θ, CInv (s.cli θ)) (θ : C) :
    CInv ((exec S s a).cli θ) := by
  cases a with
  | cTick θ' t =>
    by_cases hθ : θ = θ'
    · subst hθ; simp only [exec, updCli_cli, Function.update_self]; exact ⟨(h θ).cbox, (h θ).subs⟩
    · simpa [exec, Function.update_of_ne hθ] using h θ
  | cBroadcast θ' m =>
    by_cases hθ : θ = θ'
    · subst hθ
      simp only [exec, updCli_cli, submit_cli, Function.update_self]
      constructor
      · intro m' b hm
        simp only [List.mem_append, List.mem_singleton, Msg.message.injEq] at hm
        rcases hm with hm | ⟨rfl, -⟩
        · exact Finset.mem_insert_of_mem ((h θ).cbox m' b hm)
        · exact Finset.mem_insert_self _ _
      · intro m' hm
        by_cases hmm : m' = m
        · subst hmm; exact Finset.mem_insert_self _ _
        · simp only [Function.update_of_ne hmm] at hm; exact Finset.mem_insert_of_mem ((h θ).subs m' hm)
    · simpa [exec, submit_cli, Function.update_of_ne hθ] using h θ
  | cRecv θ' σ' msg =>
    cases msg with
    | decision m b v =>
      by_cases hθ : θ = θ'
      · subst hθ
        simp only [exec, State.onDec, recv_cli, updCli_cli, Function.update_self]
        exact ⟨(h θ).cbox, (h θ).subs⟩
      · simpa [exec, State.onDec, Function.update_of_ne hθ] using h θ
    | _ => simpa [exec, State.onDec] using h θ
  | cRetry θ' m =>
    simp only [exec]; split
    · rename_i r b hrb
      by_cases hθ : θ = θ'
      · subst hθ
        simp only [submit_cli, Function.update_self]
        have hm : m ∈ (s.cli θ).bcast := (h θ).subs m (by simp [hrb])
        constructor
        · intro m' b' hm'
          simp only [List.mem_append, List.mem_singleton, Msg.message.injEq] at hm'
          rcases hm' with hm' | ⟨rfl, -⟩
          · exact (h θ).cbox m' b' hm'
          · exact hm
        · intro m' hm'
          by_cases hmm : m' = m
          · subst hmm; exact hm
          · simp only [Function.update_of_ne hmm] at hm'; exact (h θ).subs m' hm'
      · simpa [submit_cli, Function.update_of_ne hθ] using h θ
    · exact h θ
  | beat p => simpa [exec] using h θ
  | srvRecv p σ' msg => simpa [exec, onSrv_cli] using h θ
  | cliMsg p θ' msg => simpa [exec, onCli_cli] using h θ
  | _ => simpa [exec] using h θ

/-! ### Delivery counters -/

lemma onSrv_dlv (s : State P C M T) (p σ : P) (msg : Msg C M T) : (s.onSrv S p σ msg).dlv = s.dlv := by
  cases msg <;> simp [State.onSrv]

lemma onCli_dlv (s : State P C M T) (p : P) (θ : C) (msg : Msg C M T) :
    (s.onCli S p θ msg).dlv = s.dlv := by
  cases msg <;> simp [State.onCli, State.accept] <;> split_ifs <;> simp

lemma onDec_dlv (s : State P C M T) (θ : C) (σ : P) (msg : Msg C M T) :
    (s.onDec θ σ msg).dlv = s.dlv := by
  cases msg <;> rfl

lemma recv_dlv (s : State P C M T) (a b : Node P C) : (s.recv S a b).dlv =
    if S.Byz a then s.dlv
    else Function.update s.dlv a (Function.update (s.dlv a) b (s.dlv a b + 1)) := by
  unfold State.recv
  split_ifs <;> rfl

lemma recv_dlv_le (s : State P C M T) (a b x y : Node P C) : s.dlv x y ≤ (s.recv S a b).dlv x y := by
  rw [recv_dlv]
  split_ifs
  · exact le_rfl
  · by_cases hx : x = a
    · subst hx
      by_cases hy : y = b
      · subst hy; simp
      · simp [hy]
    · simp [hx]

/-- Delivery counters never decrease. -/
lemma exec_dlv_mono (s : State P C M T) (a : Action P C M T) (x y : Node P C) :
    s.dlv x y ≤ (exec S s a).dlv x y := by
  cases a with
  | srvRecv p σ msg => rw [exec, onSrv_dlv]; exact recv_dlv_le S _ _ _ _ _
  | cliMsg p θ msg => rw [exec, onCli_dlv]; exact recv_dlv_le S _ _ _ _ _
  | cRecv θ σ msg => rw [exec, onDec_dlv]; exact recv_dlv_le S _ _ _ _ _
  | cRetry θ m => simp only [exec]; split <;> simp
  | cBroadcast => simp [exec]
  | _ => simp [exec]

lemma recv_dlv_of_ne (s : State P C M T) (a b x y : Node P C) (h : ¬ (x = a ∧ y = b)) :
    (s.recv S a b).dlv x y = s.dlv x y := by
  rw [recv_dlv]
  split_ifs
  · rfl
  · by_cases hx : x = a
    · subst hx
      have hy : y ≠ b := fun hy => h ⟨rfl, hy⟩
      simp [hy]
    · simp [hx]

/-- The counter of a server-to-server link from a correct sender `ρ` to `p` changes only by a
delivery at `p` from `ρ`, by one. -/
lemma exec_dlv_srv (s : State P C M T) (a : Action P C M T) (ρ p : P) :
    (exec S s a).dlv (.inl ρ) (.inl p) = s.dlv (.inl ρ) (.inl p) ∨
    ∃ msg, a = .srvRecv p ρ msg ∧ ρ ∉ S.F ∧
      (exec S s a).dlv (.inl ρ) (.inl p) = s.dlv (.inl ρ) (.inl p) + 1 := by
  cases a with
  | srvRecv p' σ msg =>
    rw [exec, onSrv_dlv]
    by_cases h : ρ = σ ∧ p = p'
    · obtain ⟨rfl, rfl⟩ := h
      rw [recv_dlv]
      split_ifs with hF
      · exact Or.inl rfl
      · exact Or.inr ⟨msg, rfl, hF, by simp⟩
    · left
      exact recv_dlv_of_ne S _ _ _ _ _ (by simpa using h)
  | cliMsg p' θ msg =>
    left; rw [exec, onCli_dlv]; exact recv_dlv_of_ne S _ _ _ _ _ (by simp)
  | cRecv θ σ msg =>
    left; rw [exec, onDec_dlv]; exact recv_dlv_of_ne S _ _ _ _ _ (by simp)
  | cRetry θ m => left; simp only [exec]; split <;> simp
  | cBroadcast => left; simp [exec]
  | _ => left; simp [exec]

/-- Delivery counters stay within the sent lists. -/
lemma exec_dlv_le (s : State P C M T) (a : Action P C M T) (ha : Enabled S s a)
    (h : ∀ x y, s.dlv x y ≤ (s.sent x y).length) (x y : Node P C) :
    (exec S s a).dlv x y ≤ ((exec S s a).sent x y).length := by
  have hpre := (exec_sent_prefix S s a x y).length_le
  have key : ∀ (a' b' : Node P C) (msg : Msg C M T), s.next a' b' = some msg →
      (s.recv S a' b').dlv x y ≤ (s.sent x y).length := by
    intro a' b' msg hn
    by_cases hxy : x = a' ∧ y = b'
    · obtain ⟨rfl, rfl⟩ := hxy
      rw [recv_dlv]
      split_ifs
      · exact h _ _
      · simp only [Function.update_self]
        have := (List.getElem?_eq_some_iff.mp hn).1
        omega
    · rw [recv_dlv_of_ne S _ _ _ _ _ hxy]; exact h x y
  cases a with
  | srvRecv p σ msg =>
    rw [exec, onSrv_dlv]
    refine le_trans ?_ (by simpa [exec] using (exec_sent_prefix S s (.srvRecv p σ msg) x y).length_le)
    rcases ha.2 with hF | hn
    · rw [recv_dlv, ite_eq_left (show S.Byz (.inl σ) from hF)]; exact h x y
    · exact key _ _ _ hn
  | cliMsg p θ msg =>
    rw [exec, onCli_dlv]
    refine le_trans ?_ (by simpa [exec] using (exec_sent_prefix S s (.cliMsg p θ msg) x y).length_le)
    rcases ha.2 with hG | hn
    · rw [recv_dlv, ite_eq_left (show S.Byz (.inr θ) from hG)]; exact h x y
    · exact key _ _ _ hn
  | cRecv θ σ msg =>
    rw [exec, onDec_dlv]
    refine le_trans ?_ (by simpa [exec] using (exec_sent_prefix S s (.cRecv θ σ msg) x y).length_le)
    rcases ha.2 with hF | hn
    · rw [recv_dlv, ite_eq_left (show S.Byz (.inl σ) from hF)]; exact h x y
    · exact key _ _ _ hn
  | cRetry θ m =>
    have := h x y
    revert hpre
    simp only [exec]; split <;> simp <;> omega
  | cBroadcast => have := h x y; simp [exec] at hpre ⊢; omega
  | _ => have := h x y; simp [exec] at hpre ⊢; omega

lemma prefix_getElem? {α : Type*} {l l' : List α} (h : l <+: l') {i : ℕ}
    {a : α} (hi : l[i]? = some a) : l'[i]? = some a := by
  obtain ⟨hlt, rfl⟩ := List.getElem?_eq_some_iff.mp hi
  exact List.prefix_iff_getElem?.mp h i hlt

/-! ### Changes of `remote_times`, proposals and client boxes -/

lemma exec_remote (s : State P C M T) (a : Action P C M T) (p ρ : P) :
    ((exec S s a).srv p).remote ρ = (s.srv p).remote ρ ∨
    ∃ t, a = .srvRecv p ρ (.time t) ∧
      ((exec S s a).srv p).remote ρ = max ((s.srv p).remote ρ) (t : WithBot T) := by
  by_cases hact : a.srvActor = some p
  · cases a with
    | srvRecv p' σ msg =>
      simp [Action.srvActor] at hact; subst hact
      cases msg with
      | time t =>
        by_cases hρ : ρ = σ
        · subst hρ; right; exact ⟨t, rfl, by simp [exec, State.onSrv]⟩
        · left; simp [exec, State.onSrv, Function.update_of_ne hρ]
      | observe x => left; simp [exec, State.onSrv, spot_srv_self, SState.spotL]
      | _ => left; simp [exec, State.onSrv]
    | cliMsg p' θ msg =>
      simp [Action.srvActor] at hact; subst hact
      cases msg with
      | message m b =>
        left; simp only [exec, State.onCli, accept_srv_self, recv_srv, SState.acceptL]
        split_ifs <;> simp [SState.spotL]
      | _ => left; simp [exec, State.onCli]
    | process p' x v =>
      simp [Action.srvActor] at hact; subst hact
      left; simp only [exec, updSrv_srv, Function.update_self]
      split_ifs <;> simp [SState.order] <;> split_ifs <;> simp
    | _ => (simp [Action.srvActor] at hact) <;> (subst hact; left; simp [exec])
  · left; rw [exec_srv_ne S s a p hact]

lemma exec_props (s : State P C M T) (a : Action P C M T) (ρ : P) (y : Tag C M T)
    (h : (y, true) ∈ ((exec S s a).srv ρ).props) :
    (y, true) ∈ (s.srv ρ).props ∨ a = .cliMsg ρ y.client (.message y.msg y.bet) := by
  by_cases hact : a.srvActor = some ρ
  · cases a with
    | srvRecv p' σ msg =>
      simp [Action.srvActor] at hact; subst hact
      cases msg <;> simp [exec, State.onSrv, spot_srv_self, SState.spotL] at h <;> exact Or.inl h
    | cliMsg p' θ msg =>
      simp [Action.srvActor] at hact; subst hact
      cases msg with
      | message m b =>
        simp only [exec, State.onCli, accept_srv_self, recv_srv, SState.acceptL] at h
        split_ifs at h
        · exact Or.inl (by simpa [SState.spotL] using h)
        · simp only [SState.spotL, Finset.mem_insert, Prod.mk.injEq] at h
          rcases h with ⟨rfl, -⟩ | h
          · exact Or.inr rfl
          · exact Or.inl h
      | _ => simp [exec, State.onCli] at h; exact Or.inl h
    | proposeFalse p' x =>
      simp [Action.srvActor] at hact; subst hact
      simp [exec] at h; exact Or.inl h
    | process p' x v =>
      simp [Action.srvActor] at hact; subst hact
      simp only [exec, updSrv_srv, Function.update_self] at h
      left; split_ifs at h <;> (try simp only [SState.order] at h) <;> (try split_ifs at h) <;>
        simpa using h
    | _ => (simp [Action.srvActor] at hact) <;> (subst hact; left; simpa [exec] using h)
  · left; rwa [exec_srv_ne S s a ρ hact] at h

lemma exec_cbox_prefix (s : State P C M T) (a : Action P C M T) (θ : C) :
    (s.cli θ).cbox <+: ((exec S s a).cli θ).cbox := by
  cases a with
  | srvRecv => simp [exec, onSrv_cli]
  | cliMsg => simp [exec, onCli_cli]
  | cTick θ' t =>
    by_cases hθ : θ = θ'
    · subst hθ; simp [exec]
    · simp [exec, Function.update_of_ne hθ]
  | cBroadcast θ' m =>
    by_cases hθ : θ = θ'
    · subst hθ; simp [exec, submit_cli]
    · simp [exec, submit_cli, Function.update_of_ne hθ]
  | cRecv θ' σ msg =>
    cases msg with
    | decision m b v =>
      by_cases hθ : θ = θ'
      · subst hθ; simp [exec, State.onDec]
      · simp [exec, State.onDec, Function.update_of_ne hθ]
    | _ => simp [exec, State.onDec]
  | cRetry θ' m =>
    simp only [exec]; split
    · by_cases hθ : θ = θ'
      · subst hθ; simp [submit_cli]
      · simp [submit_cli, Function.update_of_ne hθ]
    · exact List.prefix_refl _
  | _ => simp [exec]

/-! ### The global invariant -/

/-- The global invariant of Flutter. -/
structure GInv (s : State P C M T) : Prop where
  /-- Server-to-server links carry the sender's `obox`. -/
  srv : ∀ ρ σ : P, s.sent (.inl ρ) (.inl σ) = (s.srv ρ).obox
  /-- Client-to-server links carry the client's `cbox`. -/
  cli : ∀ (θ : C) (σ : P), s.sent (.inr θ) (.inl σ) = (s.cli θ).cbox
  /-- Delivery counters are within the sent lists. -/
  dlv : ∀ x y, s.dlv x y ≤ (s.sent x y).length
  /-- Local invariants of all servers. -/
  linv : ∀ p, LInv S (s.srv p)
  /-- Client invariants. -/
  cinv : ∀ θ, CInv (s.cli θ)
  /-- `remote_times[ρ]` (for a correct `ρ`) is a `Time` message of `ρ` already delivered. -/
  remote : ∀ p ρ, ρ ∉ S.F → ∀ t : T, (s.srv p).remote ρ = t →
    ∃ i < s.dlv (.inl ρ) (.inl p), (s.srv ρ).obox[i]? = some (.time t)
  /-- A correct server proposes `True` only for messages received from the client
  (authenticated links). -/
  props : ∀ ρ x, (x, true) ∈ (s.srv ρ).props → x.client ∉ S.G →
    Msg.message x.msg x.bet ∈ (s.cli x.client).cbox

lemma GInv.init (c0 : P → T) (d0 : C → T) :
    GInv S (State.init c0 d0 : State P C M T) where
  srv := by simp [State.init, SState.init]
  cli := by simp [State.init, CState.init]
  dlv := by simp [State.init]
  linv := fun p => LInv.init S (c0 p)
  cinv := fun θ => ⟨by simp [State.init, CState.init], by simp [State.init, CState.init]⟩
  remote := by simp [State.init, SState.init]
  props := by simp [State.init, SState.init]

lemma GInv.step (hq : 1 ≤ S.q) {s : State P C M T} (hI : GInv S s) (a : Action P C M T)
    (ha : Enabled S s a) : GInv S (exec S s a) := by
  refine ⟨exec_sent_obox S s a hI.srv, exec_sent_cbox S s a hI.cli, exec_dlv_le S s a ha hI.dlv,
    fun p => (hI.linv p).step S hq (exec_srv_lstep S s a ha p), exec_cinv S s a hI.cinv, ?_, ?_⟩
  · intro p ρ hρ t ht
    have hpre := (exec_srv_lstep S s a ha ρ).obox_prefix
    have hdl := exec_dlv_mono S s a (.inl ρ) (.inl p)
    have old : (s.srv p).remote ρ = t → ∃ i < (exec S s a).dlv (.inl ρ) (.inl p),
        ((exec S s a).srv ρ).obox[i]? = some (.time t) := fun h' => by
      obtain ⟨i, hi, hi'⟩ := hI.remote p ρ hρ t h'
      exact ⟨i, by omega, prefix_getElem? hpre hi'⟩
    rcases exec_remote S s a p ρ with h | ⟨t', rfl, h⟩
    · exact old (h ▸ ht)
    · rw [h] at ht
      rcases le_total ((s.srv p).remote ρ) (t' : WithBot T) with hle | hle
      · rw [max_eq_right hle, WithBot.coe_inj] at ht
        subst ht
        have hn := ha.2.resolve_left hρ
        rcases exec_dlv_srv S s (.srvRecv p ρ (.time t')) ρ p with hd | ⟨msg, hm, -, hd⟩
        · exfalso
          rw [exec, onSrv_dlv, recv_dlv, ite_eq_right (show ¬ S.Byz (.inl ρ) from hρ)] at hd
          simp at hd
        · refine ⟨s.dlv (.inl ρ) (.inl p), by omega, prefix_getElem? hpre ?_⟩
          rw [← hI.srv ρ p]; exact hn
      · rw [max_eq_left hle] at ht; exact old ht
  · intro ρ x hx hG
    have hpre := exec_cbox_prefix S s a x.client
    rcases exec_props S s a ρ x hx with h | rfl
    · exact hpre.subset (hI.props ρ x h hG)
    · have hn := ha.2.resolve_left hG
      apply hpre.subset
      rw [← hI.cli x.client ρ]
      exact List.mem_of_getElem? hn

end Podc.FastByzantineTOB.Flutter
