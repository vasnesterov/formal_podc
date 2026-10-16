import Papers.PODC2025.TwoStepConsensusLB.ImplInv

/-!
# Termination and wait-freedom of the protocol of Figure 1

Let `b ≥ 1` be a ballot that starts after GST (`gst ≤ ballotStart b = T`) and whose owner `L` is
correct. Then (§C.1):
* at `T` the leader `L` sends `1A(b)` (no ballot `≥ b` exists before `T`);
* at `T + 1` every correct process adopts `b` and replies `1B(b)`;
* at `T + 2` the leader receives `n - f` replies `1B(b)` and sends `2A(b, w)` (`w ≠ ⊥` as soon as
  the leader has an initial value — task — or has an initial value or a vote — object);
* at `T + 3` every correct process (still in ballot `b`: ballots `> b` start at `T + 5`) accepts
  `2A(b, w)` and replies `2B(b, w)`;
* at `T + 4` the leader receives `n - f` replies `2B(b, w)` and decides (`leader_decides`).

Termination of the task (`task_termination`) and wait-freedom of the object
(`object_waitFree`) follow by choosing such a ballot owned by the process in question.
-/

set_option linter.unusedSectionVars false

namespace TwoStepConsensus.Impl

variable {P V : Type*} [Fintype P] [DecidableEq P] [LinearOrder V]

/-! ### Handler lemmas -/

section Handlers

variable (c : Cfg P) (p : P)

@[simp] theorem tryDecide_bal (s : St P V) : (tryDecide c p s).bal = s.bal := by
  rcases tryDecide_cases c p s with h | ⟨v, h⟩ <;> rw [h]; rfl

@[simp] theorem tryDecide_oneBs (s : St P V) : (tryDecide c p s).oneBs = s.oneBs := by
  rcases tryDecide_cases c p s with h | ⟨v, h⟩ <;> rw [h]; rfl

@[simp] theorem timer_bal (τ : ℕ) (s : St P V) : (timer c p τ s).bal = s.bal := by
  unfold timer; split_ifs <;> rfl

@[simp] theorem timer_oneBs (τ : ℕ) (s : St P V) : (timer c p τ s).oneBs = s.oneBs := by
  unfold timer; split_ifs <;> rfl

@[simp] theorem invoke_bal (inv : Option V) (s : St P V) : (invoke inv s).bal = s.bal := by
  cases inv
  · rfl
  · simp only [invoke, onInv]; split_ifs <;> rfl

@[simp] theorem invoke_oneBs (inv : Option V) (s : St P V) : (invoke inv s).oneBs = s.oneBs := by
  cases inv
  · rfl
  · simp only [invoke, onInv]; split_ifs <;> rfl

@[simp] theorem lead_oneBs (b : ℕ) (s : St P V) : (lead c b s).oneBs = s.oneBs := by
  unfold lead; split <;> rfl

theorem ballotStart_le_iff {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    ballotStart a ≤ ballotStart b ↔ a ≤ b := by
  unfold ballotStart; omega

/-- How a handler changes the ballot. -/
theorem handle_bal_cases (s : St P V) (q : P) (m : Msg P V) :
    (handle c p s (q, m)).bal = s.bal ∨
      (∃ b, m = .oneA b ∧ s.bal < b ∧ (handle c p s (q, m)).bal = b ∧
        ∃ d, (Dest.to q, Msg.oneB b d) ∈ (handle c p s (q, m)).out) ∨
      (∃ b v, m = .twoA b v ∧ s.bal ≤ b ∧ (handle c p s (q, m)).bal = b) := by
  unfold handle
  rw [tryDecide_bal]
  have hout : ∀ x, x ∈ (handleRaw c s (q, m)).out →
      x ∈ (tryDecide c p (handleRaw c s (q, m))).out :=
    fun x hx => (grows_tryDecide c p _).out.subset hx
  cases m with
  | propose v =>
    left; simp only [handleRaw, onPropose]; split_ifs <;> rfl
  | twoB b v => left; rfl
  | decide b v => left; rfl
  | oneA b =>
    simp only [handleRaw, onOneA] at hout ⊢
    split_ifs at hout ⊢ with h
    · exact Or.inr (Or.inl ⟨b, rfl, h, rfl, _, hout _ (List.mem_append_right _
        (List.mem_singleton_self _))⟩)
    · exact Or.inl rfl
  | oneB b d =>
    left
    simp only [handleRaw, onOneB]
    split_ifs
    · rfl
    · unfold lead; split <;> rfl
    · rfl
  | twoA b v =>
    simp only [handleRaw, onTwoA]
    split_ifs with h
    · exact Or.inr (Or.inr ⟨b, v, rfl, h, rfl⟩)
    · exact Or.inl rfl

/-- Handling `1A(b)` leaves the process in a ballot `≥ b`. -/
theorem handle_oneA_bal (s : St P V) (q : P) (b : ℕ) : b ≤ (handle c p s (q, .oneA b)).bal := by
  simp only [handle, tryDecide_bal, handleRaw, onOneA]
  split_ifs with h
  · exact le_rfl
  · omega

/-- A process in a ballot `≤ b` accepts `2A(b, v)` (line 40) and replies `2B(b, v)`. -/
theorem handle_twoA_out {s : St P V} {b : ℕ} (hb : s.bal ≤ b) (q : P) (v : V) :
    (Dest.to q, Msg.twoB b v) ∈ (handle c p s (q, .twoA b v)).out := by
  unfold handle
  refine (grows_tryDecide c p _).out.subset ?_
  simp [handleRaw, onTwoA, hb]

theorem handle_twoB_mem (s : St P V) (q : P) (b : ℕ) (v : V) :
    (q, b, v) ∈ (handle c p s (q, .twoB b v)).twoBs :=
  (grows_tryDecide c p _).twoBs _ (by simp [handleRaw, onTwoB])

theorem senders1B_append (s : St P V) (q : P) (b b' : ℕ) (d : OneB P V) :
    senders1B { s with oneBs := s.oneBs ++ [(q, b', d)] } b =
      if b' = b then insert q (senders1B s b) else senders1B s b := by
  unfold senders1B
  split_ifs with h
  · subst h; ext x; simp
  · ext x; simp [h]

theorem mem_senders1B {s : St P V} {q : P} {b : ℕ} :
    q ∈ senders1B s b ↔ ∃ d, (q, b, d) ∈ s.oneBs := by
  simp [senders1B]

theorem senders1B_mono {s s' : St P V} (h : Grows s s') (b : ℕ) :
    senders1B s b ⊆ senders1B s' b := by
  intro q hq
  obtain ⟨d, hd⟩ := mem_senders1B.1 hq
  exact mem_senders1B.2 ⟨d, h.oneBs _ hd⟩

theorem handle_oneB_mem (s : St P V) (q : P) (b : ℕ) (d : OneB P V) :
    q ∈ senders1B (handle c p s (q, .oneB b d)) b := by
  by_cases h : q ∈ senders1B s b
  · exact senders1B_mono (grows_handle c p s _) b h
  · have hg : Grows { s with oneBs := s.oneBs ++ [(q, b, d)] } (handle c p s (q, .oneB b d)) := by
      unfold handle
      refine Grows.trans ?_ (grows_tryDecide c p _)
      simp only [handleRaw, onOneB, h, ite_false]
      split_ifs
      · exact grows_lead c b _
      · exact Grows.refl _
    apply senders1B_mono hg
    rw [senders1B_append]
    simp

@[simp] theorem senders1B_tryDecide (s : St P V) (b : ℕ) :
    senders1B (tryDecide c p s) b = senders1B s b := by
  simp [senders1B]

@[simp] theorem senders1B_lead (b' : ℕ) (s : St P V) (b : ℕ) :
    senders1B (lead c b' s) b = senders1B s b := by
  simp [senders1B]

theorem lead_out {s : St P V} {b : ℕ} (hfb : fallback c s ≠ none)
    (hO : ∀ x ∈ s.oneBs, x.2.2.vbal ≠ 0 → x.2.2.val ≠ none) :
    ∃ w, (Dest.all, Msg.twoA b w) ∈ (lead c b s).out := by
  unfold lead
  split
  · exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _)⟩
  · rename_i h
    refine absurd h (proposal_ne_none _ _ _ hfb ?_)
    intro x hx
    simp only [quorum1B, List.mem_map, List.mem_filter] at hx
    obtain ⟨y, ⟨hy, -⟩, rfl⟩ := hx
    exact hO y hy

/-- **Crossing the `1B` threshold.** The handler that brings the number of senders of `1B(b)` to
`n - f` sends `2A(b, w)` (if the leader has a fallback value). -/
theorem handle_cross {s : St P V} {b : ℕ} (hfb : fallback c s ≠ none)
    (hO : ∀ x ∈ s.oneBs, x.2.2.vbal ≠ 0 → x.2.2.val ≠ none) {q : P} {m : Msg P V}
    (hm : ∀ b' d, m = .oneB b' d → d.vbal ≠ 0 → d.val ≠ none)
    (hlt : (senders1B s b).card < Fintype.card P - c.f)
    (hge : Fintype.card P - c.f ≤ (senders1B (handle c p s (q, m)) b).card) :
    ∃ w, (Dest.all, Msg.twoA b w) ∈ (handle c p s (q, m)).out := by
  unfold handle at hge ⊢
  rw [senders1B_tryDecide] at hge
  suffices ∃ w, (Dest.all, Msg.twoA b w) ∈ (handleRaw c s (q, m)).out by
    obtain ⟨w, hw⟩ := this
    exact ⟨w, (grows_tryDecide c p _).out.subset hw⟩
  have hsame : ∀ s', s'.oneBs = s.oneBs → ¬ Fintype.card P - c.f ≤ (senders1B s' b).card := by
    intro s' h1 h2
    have : senders1B s' b = senders1B s b := by simp [senders1B, h1]
    rw [this] at h2
    omega
  cases m with
  | propose v =>
    exfalso; refine hsame _ ?_ hge
    simp only [handleRaw, onPropose]; split_ifs <;> rfl
  | twoB b' v => exact absurd hge (hsame _ rfl)
  | decide b v => exact absurd hge (hsame _ rfl)
  | oneA b' =>
    exfalso; refine hsame _ ?_ hge
    simp only [handleRaw, onOneA]; split_ifs <;> rfl
  | twoA b' v =>
    exfalso; refine hsame _ ?_ hge
    simp only [handleRaw, onTwoA]; split_ifs <;> rfl
  | oneB b' d =>
    have hd := hm b' d rfl
    simp only [handleRaw, onOneB] at hge ⊢
    split_ifs at hge ⊢ with h1 h2
    · exact absurd hge (hsame _ rfl)
    · rw [senders1B_lead, senders1B_append] at hge
      by_cases hb : b' = b
      · subst hb
        apply lead_out c
        · simpa [fallback] using hfb
        · intro x hx
          simp only [List.mem_append, List.mem_singleton] at hx
          rcases hx with hx | rfl
          · exact hO x hx
          · exact hd
      · simp only [hb, ite_false] at hge; omega
    · rw [senders1B_append] at hge
      by_cases hb : b' = b
      · subst hb
        simp only [ite_true] at hge
        rw [Finset.card_insert_of_notMem h1] at hge
        omega
      · simp only [hb, ite_false] at hge; omega

/-- Handlers keep the ballot `≤ b` as long as no message of a ballot `> b` can exist. -/
theorem handle_bal_le {s : St P V} {b : ℕ} (hb : 1 ≤ b) (hs : s.bal ≤ b) {q : P} {m : Msg P V}
    {τ' : ℕ} (hm : MsgT c q m τ') (hτ' : τ' ≤ ballotStart b + 4) :
    (handle c p s (q, m)).bal ≤ b := by
  rcases handle_bal_cases c p s q m with h | ⟨b', rfl, -, h, -⟩ | ⟨b', v, rfl, -, h⟩
  · omega
  · simp only [MsgT] at hm
    rw [h]; unfold ballotStart at hm hτ'; omega
  · simp only [MsgT] at hm
    rw [h]; unfold ballotStart at hm hτ'; omega

theorem timer_sends {b : ℕ} (hb : 1 ≤ b) (hown : c.owner b = p) {s : St P V} (hs : s.bal < b) :
    (Dest.all, Msg.oneA b) ∈ (timer c p (ballotStart b) s).out := by
  have h : (ballotStart b + 3) / 5 = b := by unfold ballotStart; omega
  unfold timer
  rw [h, ite_eq_left ⟨hb, rfl, hown, hs⟩]
  exact List.mem_append_right _ (List.mem_singleton_self _)

theorem fallback_grows {s s' : St P V} (h : Grows s s') (hs : fallback c s ≠ none) :
    fallback c s' ≠ none := by
  unfold fallback at hs ⊢
  split_ifs at hs ⊢
  · rcases hi : s.initVal with _ | u
    · rw [hi] at hs
      have hv : s.val ≠ none := by simpa using hs
      rcases hi' : s'.initVal with _ | u'
      · simpa using h.val hv
      · simp
    · have := h.initVal (by simp [hi])
      rcases hi' : s'.initVal with _ | u'
      · exact absurd hi' this
      · simp
  · exact h.initVal hs

end Handlers

/-! ### The run-level argument -/

section RunLevel

variable {c : Cfg P} {R : Run P V (Msg P V)}

theorem st_succ_correct {x : P} (hx : R.crash x = none) (τ : ℕ) :
    R.st (fig1 c) (τ + 1) x =
      stepFn c x τ (R.st (fig1 c) τ x) (R.inv x τ) (R.inbox (fig1 c) x τ) :=
  Run.st_succ_of_alive _ _ (R.alive_of_crash_none hx τ)

/-- A property of the state that only depends on its monotone components persists. -/
theorem st_grow (Φ : St P V → Prop) (hΦ : ∀ s s', Grows { s with out := [] } s' → Φ s → Φ s')
    (p : P) {τ τ' : ℕ} (h : τ ≤ τ') (hτ : Φ (R.st (fig1 c) τ p)) : Φ (R.st (fig1 c) τ' p) :=
  Run.st_mono _ R Φ (fun τ s inv l h => hΦ s _ (grows_stepFn c p τ s inv l) h) h hτ

/-- A step of a correct process preserves an invariant `J` of the handlers and the timer. -/
theorem step_inv {x : P} (hx : R.crash x = none) {τ : ℕ} (J : St P V → Prop)
    (hJ0 : J (invoke (R.inv x τ) { R.st (fig1 c) τ x with out := [] }))
    (hJ : ∀ s qm, qm ∈ R.inbox (fig1 c) x τ → J s → J (handle c x s qm))
    (hJT : ∀ s, J s → J (timer c x τ s)) : J (R.st (fig1 c) (τ + 1) x) := by
  rw [st_succ_correct hx]
  exact hJT _ (foldl_inv _ J hJ hJ0)

/-- If handling a delivered message establishes a monotone property `Q` (from any state satisfying
an invariant `J` of the handlers), then `Q` holds after the step. -/
theorem step_mem {x : P} (hx : R.crash x = none) {τ : ℕ} (J Q : St P V → Prop)
    (hQG : ∀ s s', Grows s s' → Q s → Q s')
    (hJ0 : J (invoke (R.inv x τ) { R.st (fig1 c) τ x with out := [] }))
    (hJ : ∀ s qm, qm ∈ R.inbox (fig1 c) x τ → J s → J (handle c x s qm))
    {qm₀ : P × Msg P V} (hqm : qm₀ ∈ R.inbox (fig1 c) x τ) (h₀ : ∀ s, J s → Q (handle c x s qm₀)) :
    Q (R.st (fig1 c) (τ + 1) x) := by
  rw [st_succ_correct hx]
  refine hQG _ _ (grows_timer c x τ _) ?_
  exact foldl_mem _ J Q hJ (fun s y _ _ hs => hQG _ _ (grows_handle c x s y) hs) hqm h₀ hJ0

/-- The correct processes. -/
def correctSet (R : Run P V (Msg P V)) : Finset P := Finset.univ.filter fun x => R.crash x = none

theorem mem_correctSet {x : P} : x ∈ correctSet R ↔ R.crash x = none := by simp [correctSet]

theorem card_correct_ge {f : ℕ} (hR : R.Valid f) : Fintype.card P - f ≤ (correctSet R).card := by
  have h1 := hR.card_faulty
  have h2 := Finset.card_filter_add_card_filter_not (s := Finset.univ)
    (fun x : P => R.crash x = none)
  simp only [Run.faulty, ne_eq] at h1
  rw [Finset.card_univ] at h2
  unfold correctSet
  have : Fintype.card P - f ≤
      Fintype.card P - (Finset.univ.filter fun a : P => ¬R.crash a = none).card :=
    Nat.sub_le_sub_left h1 _
  omega

theorem lt_of_timing {a b : ℕ} (hb : 1 ≤ b) (h : a = 0 ∨ ballotStart a + 2 ≤ ballotStart b + 1) :
    a < b := by
  unfold ballotStart at h; omega

/-- Ballots: no process is in a ballot `> b` before time `ballotStart b + 7`. -/
theorem bal_le_of_time (hR : IsOrder R.ord) {b τ : ℕ} (hb : 1 ≤ b) (hτ : τ ≤ ballotStart b + 6)
    (x : P) : (R.st (fig1 c) τ x).bal ≤ b := by
  rcases (timing_st (c := c) hR τ x).1 with h | h
  · omega
  · unfold ballotStart at h hτ; omega

variable (hR : R.Valid c.f) {b : ℕ} (hb : 1 ≤ b) (hgst : R.gst ≤ ballotStart b)
  (hL : R.crash (c.owner b) = none)
include hR hb hgst hL

/-- At time `T = ballotStart b` the (correct) owner of `b` sends `1A(b)`; it is delivered to every
correct process at `T + 1`. -/
theorem oneA_delivered {x : P} (hx : R.crash x = none) :
    (c.owner b, Msg.oneA b) ∈ R.inbox (fig1 c) x (ballotStart b + 1) := by
  apply Run.mem_inbox_of_gst _ R hR hL hx hgst
  rw [Run.out_of_alive _ _ (R.alive_of_crash_none hL _), mem_send]
  refine ⟨Dest.all, ?_, rfl⟩
  have hlt : (R.st (fig1 c) (ballotStart b + 1) (c.owner b)).bal < b :=
    lt_of_timing hb (timing_st (c := c) hR.ord_perm (ballotStart b + 1) (c.owner b)).1
  rw [st_succ_correct hL] at hlt ⊢
  rw [stepFn, timer_bal] at hlt
  exact timer_sends c _ hb rfl hlt

/-- At `T + 1` every correct process adopts ballot `b` and replies `1B(b)` to the leader. -/
theorem oneB_sent {x : P} (hx : R.crash x = none) :
    (R.st (fig1 c) (ballotStart b + 2) x).bal = b ∧
      ∃ d, (Dest.to (c.owner b), Msg.oneB b d) ∈ (R.st (fig1 c) (ballotStart b + 2) x).out := by
  set J : St P V → Prop := fun s =>
    s.bal ≤ b ∧ (s.bal = b → ∃ d, (Dest.to (c.owner b), Msg.oneB b d) ∈ s.out) with hJdef
  have hJ : ∀ s qm, qm ∈ R.inbox (fig1 c) x (ballotStart b + 1) → J s → J (handle c x s qm) := by
    rintro s ⟨q, m⟩ hqm ⟨h1, h2⟩
    obtain ⟨τ', hτ', hm⟩ := timing_inbox hR.ord_perm hqm
    have hg := grows_handle c x s (q, m)
    rcases handle_bal_cases c x s q m with h | ⟨b', rfl, hlt, h, d, hd⟩ | ⟨b', v, rfl, -, h⟩
    · refine ⟨h ▸ h1, fun h' => ?_⟩
      obtain ⟨d, hd⟩ := h2 (h ▸ h')
      exact ⟨d, hg.out.subset hd⟩
    · simp only [MsgT] at hm
      have : b' ≤ b := by unfold ballotStart at hm hτ'; omega
      refine ⟨by rw [h]; exact this, fun h' => ?_⟩
      rw [h] at h'
      subst h'
      obtain ⟨-, -, h4⟩ := hm
      subst h4
      exact ⟨d, hd⟩
    · simp only [MsgT] at hm
      have : b' < b := by unfold ballotStart at hm hτ'; omega
      exact ⟨by rw [h]; omega, fun h' => by rw [h] at h'; omega⟩
  have hJT : ∀ s, J s → J (timer c x (ballotStart b + 1) s) := by
    intro s ⟨h1, h2⟩
    have hg := grows_timer c x (ballotStart b + 1) s
    refine ⟨by rw [timer_bal]; exact h1, fun h' => ?_⟩
    obtain ⟨d, hd⟩ := h2 (by rwa [timer_bal] at h')
    exact ⟨d, hg.out.subset hd⟩
  have hJ0 : J (invoke (R.inv x (ballotStart b + 1)) { R.st (fig1 c) (ballotStart b + 1) x with
      out := [] }) := by
    have : (R.st (fig1 c) (ballotStart b + 1) x).bal < b :=
      lt_of_timing hb (timing_st (c := c) hR.ord_perm (ballotStart b + 1) x).1
    refine ⟨by rw [invoke_bal]; exact this.le, fun h => ?_⟩
    rw [invoke_bal] at h
    exact absurd h this.ne
  have hfin := step_inv hx J hJ0 hJ hJT
  have hge : b ≤ (R.st (fig1 c) (ballotStart b + 1 + 1) x).bal :=
    step_mem hx J (fun s => b ≤ s.bal) (fun s s' h hs => hs.trans h.bal) hJ0 hJ
      (oneA_delivered hR hb hgst hL hx) (fun s _ => handle_oneA_bal c x s _ b)
  exact ⟨le_antisymm hfin.1 hge, hfin.2 (le_antisymm hfin.1 hge)⟩

/-- Correct processes stay in ballot `b` from `T + 2` to `T + 6`. -/
theorem bal_eq {x : P} (hx : R.crash x = none) {τ : ℕ} (h1 : ballotStart b + 2 ≤ τ)
    (h2 : τ ≤ ballotStart b + 6) : (R.st (fig1 c) τ x).bal = b := by
  refine le_antisymm (bal_le_of_time hR.ord_perm hb h2 x) ?_
  exact st_grow (fun s => b ≤ s.bal) (fun s s' h hs => hs.trans h.bal) x h1
    (oneB_sent hR hb hgst hL hx).1.ge

/-- At `T + 2` the leader receives `1B(b)` from all correct processes and sends `2A(b, w)`. -/
theorem twoA_sent (hfn : c.f < Fintype.card P)
    (hP : fallback c (R.st (fig1 c) (ballotStart b + 2) (c.owner b)) ≠ none) :
    ∃ w, (Dest.all, Msg.twoA b w) ∈ (R.st (fig1 c) (ballotStart b + 3) (c.owner b)).out := by
  set L := c.owner b
  set τ := ballotStart b + 2
  set J : St P V → Prop := fun s => WT c L τ s ∧ fallback c s ≠ none
  have hJ : ∀ s qm, qm ∈ R.inbox (fig1 c) L τ → J s → J (handle c L s qm) := by
    rintro s ⟨q, m⟩ hqm ⟨h1, h2⟩
    exact ⟨h1.handle c L (timing_inbox hR.ord_perm hqm),
      fallback_grows c (grows_handle c L s _) h2⟩
  set s₀ := invoke (R.inv L τ) { R.st (fig1 c) τ L with out := [] }
  have hJ0 : J s₀ := by
    have h0 : WT c L τ { R.st (fig1 c) τ L with out := [] } :=
      ⟨StT.mono (k' := 1) (τ' := τ) (timing_st (c := c) hR.ord_perm τ L) (by omega), by simp⟩
    refine ⟨WT.invoke c L h0 _, ?_⟩
    exact fallback_grows c (grows_invoke _ _) hP
  -- no `1B(b)` has been received before `T + 2`
  have hcnt0 : (senders1B s₀ b).card = 0 := by
    rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    intro q hq
    obtain ⟨d, hd⟩ := mem_senders1B.1 hq
    simp only [s₀, invoke_oneBs] at hd
    have := ((timing_st (c := c) hR.ord_perm τ L).2.2 _ hd).2.1
    simp only [τ] at this; omega
  -- after the step, all correct processes are senders of `1B(b)`
  have hC : ∀ x ∈ correctSet R,
      x ∈ senders1B ((R.inbox (fig1 c) L τ).foldl (handle c L) s₀) b := by
    intro x hx
    have hx : R.crash x = none := mem_correctSet.1 hx
    obtain ⟨-, d, hd⟩ := oneB_sent hR hb hgst hL hx
    have hdel : (x, Msg.oneB b d) ∈ R.inbox (fig1 c) L τ := by
      apply Run.mem_inbox_of_gst _ R hR hx hL (by omega)
      rw [Run.out_of_alive _ _ (R.alive_of_crash_none hx _), mem_send]
      exact ⟨_, hd, by simp [Dest.incl, L]⟩
    exact foldl_mem _ J (fun s => x ∈ senders1B s b) hJ
      (fun s y _ _ hs => senders1B_mono (grows_handle c L s y) b hs) hdel
      (fun s _ => handle_oneB_mem c L s x b d) hJ0
  have hcard : Fintype.card P - c.f ≤
      (senders1B ((R.inbox (fig1 c) L τ).foldl (handle c L) s₀) b).card :=
    (card_correct_ge hR).trans (Finset.card_le_card hC)
  have hQ := foldl_cross (handle c L) J (fun s => ∃ w, (Dest.all, Msg.twoA b w) ∈ s.out)
    (fun s => (senders1B s b).card) (Fintype.card P - c.f) hJ
    (fun s y _ _ ⟨w, hw⟩ => ⟨w, (grows_handle c L s y).out.subset hw⟩)
    (fun s y hy hs hlt hge => by
      obtain ⟨q, m⟩ := y
      obtain ⟨τ', -, hm⟩ := timing_inbox hR.ord_perm hy
      refine handle_cross c L hs.2 (fun z hz => (hs.1.1.2.2 z hz).2.2) ?_ hlt hge
      rintro b' d rfl
      exact hm.2.2) hJ0 (by rw [hcnt0]; omega) hcard
  obtain ⟨w, hw⟩ := hQ
  refine ⟨w, ?_⟩
  rw [show ballotStart b + 3 = τ + 1 by omega, st_succ_correct hL]
  exact (grows_timer c L τ _).out.subset hw

/-- **The leader of a ballot starting after GST decides** (by `T + 5`), provided it has a value
to propose at `T + 2`. -/
theorem leader_decides (hfn : c.f < Fintype.card P)
    (hP : fallback c (R.st (fig1 c) (ballotStart b + 2) (c.owner b)) ≠ none) :
    (R.st (fig1 c) (ballotStart b + 5) (c.owner b)).decided ≠ none := by
  set L := c.owner b
  obtain ⟨w, hw⟩ := twoA_sent hR hb hgst hL hfn hP
  -- at `T + 3`, every correct process replies `2B(b, w)`
  have h2B : ∀ x ∈ correctSet R, (Dest.to L, Msg.twoB b w) ∈
      (R.st (fig1 c) (ballotStart b + 3 + 1) x).out := by
    intro x hx
    have hx : R.crash x = none := mem_correctSet.1 hx
    have hdel : (L, Msg.twoA b w) ∈ R.inbox (fig1 c) x (ballotStart b + 3) := by
      apply Run.mem_inbox_of_gst _ R hR hL hx (by omega)
      rw [Run.out_of_alive _ _ (R.alive_of_crash_none hL _), mem_send]
      exact ⟨_, hw, rfl⟩
    refine step_mem hx (fun s => s.bal ≤ b) _ (fun s s' h hs => h.out.subset hs) ?_ ?_ hdel
      (fun s hs => handle_twoA_out c x hs L w)
    · rw [invoke_bal]; exact bal_le_of_time hR.ord_perm hb (by omega) x
    · rintro s ⟨q, m⟩ hqm hs
      obtain ⟨τ', hτ', hm⟩ := timing_inbox hR.ord_perm hqm
      exact handle_bal_le c x hb hs hm (by omega)
  -- at `T + 4`, the leader receives them
  have hmem : ∀ x ∈ correctSet R, (x, b, w) ∈ (R.st (fig1 c) (ballotStart b + 4 + 1) L).twoBs := by
    intro x hx
    have hx' : R.crash x = none := mem_correctSet.1 hx
    have hdel : (x, Msg.twoB b w) ∈ R.inbox (fig1 c) L (ballotStart b + 4) := by
      apply Run.mem_inbox_of_gst _ R hR hx' hL (by omega)
      rw [Run.out_of_alive _ _ (R.alive_of_crash_none hx' _), mem_send]
      exact ⟨_, h2B x hx, by simp [Dest.incl]⟩
    exact step_mem hL (fun _ => True) _ (fun s s' h hs => h.twoBs _ hs) trivial
      (fun _ _ _ _ => trivial) hdel (fun s _ => handle_twoB_mem c L s x b w)
  have hbal : (R.st (fig1 c) (ballotStart b + 5) L).bal = b :=
    bal_eq hR hb hgst hL hL (by omega) (by omega)
  obtain ⟨x₀, hx₀⟩ : (correctSet R).Nonempty := by
    rw [← Finset.card_pos]; have := card_correct_ge hR; omega
  refine decided_of_noPending c L (noPending_st _ L) (hmem x₀ hx₀) hbal.symm ?_
  rw [hbal]
  simp only [canDecide, show b ≠ 0 by omega, ite_false, decide_eq_true_eq]
  refine (card_correct_ge hR).trans (Finset.card_le_card fun x hx => ?_)
  simp only [senders2B, List.mem_toFinset, List.mem_map, List.mem_filter]
  exact ⟨(x, b, w), ⟨hmem x hx, by simp⟩, rfl⟩

end RunLevel

/-! ### Termination and wait-freedom -/

theorem fallback_invoke (c : Cfg P) {s : St P V} (v : V) (h : c.obj = true ∨ s.val = none) :
    fallback c (invoke (some v) s) ≠ none := by
  simp only [invoke, onInv]
  split_ifs with hv
  · unfold fallback; split_ifs <;> simp
  · rcases h with h | h
    · simp only [fallback, h, ite_true]
      rcases s.initVal <;> simp [hv]
    · exact absurd h hv

/-- A process that is correct and has invoked `propose(v)` at `τ₀` (with `obj = true`, or with
`val = ⊥` at that time) decides, provided it owns ballots starting arbitrarily late. -/
theorem decides_of_invoked {c : Cfg P} {R : Run P V (Msg P V)} (hR : R.Valid c.f)
    (hfn : c.f < Fintype.card P) (hown : ∀ p k, ∃ b, k ≤ b ∧ c.owner b = p) {p : P}
    (hp : R.crash p = none) {τ₀ : ℕ} {v : V} (hinv : R.inv p τ₀ = some v)
    (hval : c.obj = true ∨ (R.st (fig1 c) τ₀ p).val = none) :
    ∃ τ w, τ₀ < τ ∧ R.DecidesAt (fig1 c) p τ w := by
  obtain ⟨b, hb, rfl⟩ := hown p (R.gst + τ₀ + 1)
  have hb1 : 1 ≤ b := by omega
  have hT : R.gst + τ₀ + 1 ≤ ballotStart b := by unfold ballotStart; omega
  have h1 : fallback c (R.st (fig1 c) (τ₀ + 1) (c.owner b)) ≠ none := by
    rw [st_succ_correct hp, stepFn, hinv]
    refine fallback_grows c (grows_timer c _ _ _) (fallback_grows c (grows_foldl c _ _ _) ?_)
    exact fallback_invoke c v hval
  have h2 : fallback c (R.st (fig1 c) (ballotStart b + 2) (c.owner b)) ≠ none :=
    st_grow (fun s => fallback c s ≠ none) (fun s s' h hs => fallback_grows c h hs) _
      (by omega) h1
  have := leader_decides hR hb1 (by omega) hp hfn h2
  obtain ⟨w, hw⟩ := Option.ne_none_iff_exists'.1 this
  exact ⟨ballotStart b + 5, w, by omega, hw⟩

/-- **Termination** of the consensus task (Theorem 1, "if"; Ω replaced by rotating ballots):
every correct process eventually decides. Needs only `f < n` and that every process owns ballots
starting arbitrarily late (e.g. `rrOwner`). -/
theorem task_termination (c : Cfg P) (hfn : c.f < Fintype.card P)
    (hown : ∀ p k, ∃ b, k ≤ b ∧ c.owner b = p) (R : Run P V (Msg P V)) (I : P → V)
    (hR : R.Valid c.f) (hinv : R.inv = taskInv I) (p : P) (hp : R.crash p = none) :
    ∃ τ v, R.DecidesAt (fig1 c) p τ v := by
  obtain ⟨τ, w, -, h⟩ := decides_of_invoked hR hfn hown hp (τ₀ := 0) (v := I p)
    (by simp [hinv, taskInv]) (Or.inr (by simp [fig1]))
  exact ⟨τ, w, h⟩

/-- **Wait-freedom** of the consensus object (Theorem 2, "if"; with our fix of lines 37–38 and
Ω replaced by rotating ballots): every invocation by a correct process returns. -/
theorem object_waitFree (c : Cfg P) (hobj : c.obj = true) (hfn : c.f < Fintype.card P)
    (hown : ∀ p k, ∃ b, k ≤ b ∧ c.owner b = p) (R : Run P V (Msg P V)) (hR : R.Valid c.f)
    (_hwf : R.WellFormed) (p : P) (τ₀ : ℕ) (v : V) (hp : R.crash p = none)
    (hinv : R.inv p τ₀ = some v) : ∃ τ w, R.RespondsAt (fig1 c) p τ w := by
  obtain ⟨τ, w, hτ, h⟩ := decides_of_invoked hR hfn hown hp hinv (Or.inl hobj)
  exact ⟨τ, w, ⟨τ₀, hτ, by simp [hinv]⟩, h⟩

end TwoStepConsensus.Impl
