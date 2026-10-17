import Papers.PODC2025.TwoStepConsensusLB.ImplBasic
import Podc.Computability.Distributed.CrashPartialSync.Model

/-!
# System invariants of the implementation of Figure 1

* **Timing** (`MsgT`, `StT`): a message `1A(b)` is sent only by `owner b` at time `ballotStart b`;
  `1B(b)`, `2A(b)`, `2B(b)` (`b ≥ 1`) only at times `≥ ballotStart b + 1, + 2, + 3`; a process has
  `bal = b ≥ 1` only from time `ballotStart b + 2` on. Also, a vote in a slow ballot carries a
  value (`vbal ≠ 0 → val ≠ ⊥`). (`timing_st`, `timing_out`, `timing_inbox`.)
* **Values** (`MsgV`, `StV`): every value in the state of a process at time `τ` or in a message
  sent before `τ` was invoked (proposed) by some process at a time `< τ` (`values_st`,
  `values_out`).
* `noPending_st`: every state satisfies `NoPending`.
-/

set_option linter.unusedSectionVars false

namespace TwoStepConsensus.Impl

open _root_.Cslib.CrashPartialSync

variable {P V : Type*} [Fintype P] [DecidableEq P] [LinearOrder V]

theorem mem_send {c : Cfg P} {p q : P} {s : St P V} {m : Msg P V} :
    m ∈ (fig1 c).send p s q ↔ ∃ d, (d, m) ∈ s.out ∧ d.incl p q = true := by
  simp [fig1]

/-! ### Timing -/

section Timing

variable (c : Cfg P)

/-- Timing invariant of a message sent by `q` at time `τ`. -/
def MsgT (q : P) (m : Msg P V) (τ : ℕ) : Prop :=
  match m with
  | .oneA b => 1 ≤ b ∧ ballotStart b = τ ∧ c.owner b = q
  | .oneB b d => 1 ≤ b ∧ ballotStart b + 1 ≤ τ ∧ (d.vbal ≠ 0 → d.val ≠ none)
  | .twoA b _ => 1 ≤ b ∧ ballotStart b + 2 ≤ τ
  | .twoB b _ => b = 0 ∨ ballotStart b + 3 ≤ τ
  | .propose _ => True
  | .decide _ _ => True

/-- Timing invariant of a state at time `τ` (`k = 2`), or during the step at time `τ` (`k = 1`). -/
def StT (k τ : ℕ) (s : St P V) : Prop :=
  (s.bal = 0 ∨ ballotStart s.bal + k ≤ τ) ∧ (s.vbal ≠ 0 → s.val ≠ none) ∧
  ∀ x ∈ s.oneBs, 1 ≤ x.2.1 ∧ ballotStart x.2.1 + k + 1 ≤ τ ∧ (x.2.2.vbal ≠ 0 → x.2.2.val ≠ none)

/-- Timing invariant during the step of `p` at time `τ`. -/
def WT (p : P) (τ : ℕ) (s : St P V) : Prop := StT 1 τ s ∧ ∀ dm ∈ s.out, MsgT c p dm.2 τ

variable (p : P)

theorem WT.decideV {τ : ℕ} {s : St P V} (h : WT c p τ s) (v : V) : WT c p τ (decideV v s) := by
  obtain ⟨⟨h1, -, h3⟩, h4⟩ := h
  refine ⟨⟨h1, by simp [Impl.decideV], h3⟩, ?_⟩
  simp only [Impl.decideV, List.mem_append, List.mem_singleton]
  rintro dm (h | rfl)
  · exact h4 dm h
  · trivial

theorem WT.tryDecide {τ : ℕ} {s : St P V} (h : WT c p τ s) : WT c p τ (tryDecide c p s) := by
  rcases tryDecide_cases c p s with h' | ⟨v, h'⟩ <;> rw [h']
  · exact h
  · exact h.decideV c p v

theorem WT.lead {τ : ℕ} {s : St P V} (h : WT c p τ s) {b : ℕ} (hb : 1 ≤ b)
    (hbτ : ballotStart b + 2 ≤ τ) : WT c p τ (lead c b s) := by
  unfold Impl.lead
  split
  · obtain ⟨h1, h4⟩ := h
    refine ⟨h1, ?_⟩
    simp only [List.mem_append, List.mem_singleton]
    rintro dm (h | rfl)
    · exact h4 dm h
    · exact ⟨hb, hbτ⟩
  · exact h

theorem WT.handleRaw {τ : ℕ} {s : St P V} (h : WT c p τ s) {q : P} {m : Msg P V}
    (hm : ∃ τ' < τ, MsgT c q m τ') : WT c p τ (Impl.handleRaw c s (q, m)) := by
  obtain ⟨τ', hτ', hm⟩ := hm
  obtain ⟨⟨h1, h2, h3⟩, h4⟩ := h
  cases m with
  | propose v =>
    simp only [Impl.handleRaw, onPropose]
    split_ifs
    · refine ⟨⟨h1, by simp, h3⟩, ?_⟩
      simp only [List.mem_append, List.mem_singleton]
      rintro dm (h | rfl)
      · exact h4 dm h
      · exact Or.inl rfl
    · exact ⟨⟨h1, h2, h3⟩, h4⟩
  | twoB b v => exact ⟨⟨h1, h2, h3⟩, h4⟩
  | decide b v => exact ⟨⟨h1, by simp [Impl.handleRaw, onDecide], h3⟩, h4⟩
  | oneA b =>
    simp only [MsgT] at hm
    simp only [Impl.handleRaw, onOneA]
    split_ifs
    · refine ⟨⟨Or.inr (by dsimp only; omega), h2, h3⟩, ?_⟩
      simp only [List.mem_append, List.mem_singleton]
      rintro dm (h | rfl)
      · exact h4 dm h
      · exact ⟨hm.1, by omega, h2⟩
    · exact ⟨⟨h1, h2, h3⟩, h4⟩
  | oneB b d =>
    simp only [MsgT] at hm
    simp only [Impl.handleRaw, onOneB]
    have hW : WT c p τ { s with oneBs := s.oneBs ++ [(q, b, d)] } := by
      refine ⟨⟨h1, h2, ?_⟩, h4⟩
      simp only [List.mem_append, List.mem_singleton]
      rintro x (hx | rfl)
      · exact h3 x hx
      · exact ⟨hm.1, by dsimp only; omega, hm.2.2⟩
    split_ifs
    · exact ⟨⟨h1, h2, h3⟩, h4⟩
    · exact hW.lead c p hm.1 (by omega)
    · exact hW
  | twoA b v =>
    simp only [MsgT] at hm
    simp only [Impl.handleRaw, onTwoA]
    split_ifs
    · refine ⟨⟨Or.inr (by dsimp only; omega), by simp, h3⟩, ?_⟩
      simp only [List.mem_append, List.mem_singleton]
      rintro dm (h | rfl)
      · exact h4 dm h
      · exact Or.inr (by omega)
    · exact ⟨⟨h1, h2, h3⟩, h4⟩

theorem WT.handle {τ : ℕ} {s : St P V} (h : WT c p τ s) {q : P} {m : Msg P V}
    (hm : ∃ τ' < τ, MsgT c q m τ') : WT c p τ (Impl.handle c p s (q, m)) :=
  (h.handleRaw c p hm).tryDecide c p

theorem WT.timer {τ : ℕ} {s : St P V} (h : WT c p τ s) : WT c p τ (Impl.timer c p τ s) := by
  unfold Impl.timer
  split_ifs with hc
  · obtain ⟨h1, h4⟩ := h
    refine ⟨h1, ?_⟩
    simp only [List.mem_append, List.mem_singleton]
    rintro dm (h | rfl)
    · exact h4 dm h
    · exact ⟨hc.1, hc.2.1, hc.2.2.1⟩
  · exact h

theorem WT.invoke {τ : ℕ} {s : St P V} (h : WT c p τ s) (inv : Option V) :
    WT c p τ (Impl.invoke inv s) := by
  cases inv with
  | none => exact h
  | some v =>
    simp only [Impl.invoke, onInv]
    split_ifs
    · obtain ⟨h1, h4⟩ := h
      refine ⟨h1, ?_⟩
      simp only [List.mem_append, List.mem_singleton]
      rintro dm (h | rfl)
      · exact h4 dm h
      · trivial
    · exact h

theorem StT.mono {k k' τ τ' : ℕ} {s : St P V} (h : StT k τ s) (hk : k' + τ ≤ k + τ') :
    StT k' τ' s := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨h1.imp_right fun h => by omega, h2, fun x hx => ?_⟩
  obtain ⟨a, b, d⟩ := h3 x hx
  exact ⟨a, by omega, d⟩

/-- One step preserves the timing invariant, and the messages it sends satisfy `MsgT`. -/
theorem timing_stepFn {τ : ℕ} {s : St P V} (h : StT 2 τ s) (inv : Option V)
    {l : List (P × Msg P V)} (hl : ∀ q m, (q, m) ∈ l → ∃ τ' < τ, MsgT c q m τ') :
    StT 2 (τ + 1) (stepFn c p τ s inv l) ∧ ∀ dm ∈ (stepFn c p τ s inv l).out, MsgT c p dm.2 τ := by
  have h0 : WT c p τ { s with out := [] } := ⟨h.mono (by omega), by simp⟩
  have := ((foldl_inv (handle c p) (WT c p τ) (l := l)
    (fun s x hx hs => by obtain ⟨q, m⟩ := x; exact hs.handle c p (hl q m hx))
    (h0.invoke c p inv))).timer c p
  exact ⟨this.1.mono (by omega), this.2⟩

end Timing

section RunInv

variable {c : Cfg P} {R : Run P V (Msg P V)}

theorem timing_all (hR : IsOrder R.ord) (τ : ℕ) :
    (∀ p, StT 2 τ (R.st (fig1 c) τ p)) ∧
      ∀ τ' < τ, ∀ q x m, m ∈ R.out (fig1 c) q τ' x → MsgT c q m τ' := by
  refine Run.invariant (fig1 c) R hR (fun τ _ s => StT 2 τ s) (fun τ q m => MsgT c q m τ)
    (fun p => ⟨Or.inl rfl, by simp [fig1], by simp [fig1]⟩) (fun τ p s h => h.mono (by omega))
    ?_ τ
  intro τ p ha hs hin
  rw [Run.st_succ_of_alive _ _ ha]
  have := timing_stepFn c p hs (R.inv p τ) hin
  refine ⟨this.1, fun x m hm => ?_⟩
  rw [Run.out_of_alive _ _ ha, Run.st_succ_of_alive _ _ ha, mem_send] at hm
  obtain ⟨d, hd, -⟩ := hm
  exact this.2 _ hd

/-- Timing invariant of the states. -/
theorem timing_st (hR : IsOrder R.ord) (τ : ℕ) (p : P) : StT 2 τ (R.st (fig1 c) τ p) :=
  (timing_all hR τ).1 p

/-- Timing invariant of the messages. -/
theorem timing_out (hR : IsOrder R.ord) {τ : ℕ} {q x : P} {m : Msg P V}
    (hm : m ∈ R.out (fig1 c) q τ x) : MsgT c q m τ :=
  (timing_all hR (τ + 1)).2 τ (by omega) q x m hm

theorem timing_inbox (hR : IsOrder R.ord) {τ : ℕ} {q x : P} {m : Msg P V}
    (hm : (q, m) ∈ R.inbox (fig1 c) x τ) : ∃ τ' < τ, MsgT c q m τ' := by
  obtain ⟨τ', hτ', -, h⟩ := (Run.mem_inbox _ R hR).1 hm
  exact ⟨τ', hτ', timing_out hR h⟩

theorem noPending_st (τ : ℕ) (p : P) : NoPending c p (R.st (fig1 c) τ p) := by
  induction τ with
  | zero => intro _ x hx; simp [fig1] at hx
  | succ τ ih =>
    rw [Run.st_succ]
    split_ifs
    · exact noPending_stepFn c p τ ih _ _
    · exact ih

end RunInv

/-! ### Values -/

section Values

/-- All values of a `1B` message satisfy `G`. -/
def OneBV (G : V → Prop) (d : OneB P V) : Prop :=
  (∀ v, d.val = some v → G v) ∧ (∀ v, d.dec = some v → G v)

/-- All values of a message satisfy `G`. -/
def MsgV (G : V → Prop) : Msg P V → Prop
  | .propose v => G v
  | .twoB _ v => G v
  | .decide _ v => G v
  | .oneA _ => True
  | .oneB _ d => OneBV G d
  | .twoA _ v => G v

/-- All values of a local state (including its outbox) satisfy `G`. -/
def StV (G : V → Prop) (s : St P V) : Prop :=
  (∀ v, s.initVal = some v → G v) ∧ (∀ v, s.val = some v → G v) ∧
  (∀ v, s.decided = some v → G v) ∧ (∀ x ∈ s.twoBs, G x.2.2) ∧ (∀ x ∈ s.oneBs, OneBV G x.2.2) ∧
  ∀ dm ∈ s.out, MsgV G dm.2

variable {G G' : V → Prop}

theorem OneBV.mono (hG : ∀ v, G v → G' v) {d : OneB P V} (h : OneBV G d) : OneBV G' d :=
  ⟨fun v hv => hG v (h.1 v hv), fun v hv => hG v (h.2 v hv)⟩

theorem MsgV.mono (hG : ∀ v, G v → G' v) {m : Msg P V} (h : MsgV G m) : MsgV G' m := by
  cases m <;> simp only [MsgV] at h ⊢
  all_goals first | exact hG _ h | trivial | exact h.mono hG

theorem StV.mono (hG : ∀ v, G v → G' v) {s : St P V} (h : StV G s) : StV G' s :=
  ⟨fun v hv => hG v (h.1 v hv), fun v hv => hG v (h.2.1 v hv), fun v hv => hG v (h.2.2.1 v hv),
    fun x hx => hG _ (h.2.2.2.1 x hx), fun x hx => (h.2.2.2.2.1 x hx).mono hG,
    fun dm hdm => (h.2.2.2.2.2 dm hdm).mono hG⟩

variable (c : Cfg P) (p : P)

theorem StV.decideV {s : St P V} (h : StV G s) {v : V} (hv : G v) : StV G (decideV v s) := by
  obtain ⟨h1, -, -, h4, h5, h6⟩ := h
  refine ⟨h1, by simp [Impl.decideV, hv], by simp [Impl.decideV, hv], h4, h5, ?_⟩
  simp only [Impl.decideV, List.mem_append, List.mem_singleton]
  rintro dm (h | rfl)
  · exact h6 dm h
  · exact hv

theorem StV.tryDecide {s : St P V} (h : StV G s) : StV G (tryDecide c p s) := by
  unfold Impl.tryDecide
  split_ifs
  · split
    · rename_i x hx
      exact h.decideV (h.2.2.2.1 x (List.mem_of_find?_eq_some hx))
    · exact h
  · exact h

theorem StV.lead {s : St P V} (h : StV G s) (b : ℕ) : StV G (lead c b s) := by
  unfold Impl.lead
  split
  · rename_i w hw
    refine ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, ?_⟩
    simp only [List.mem_append, List.mem_singleton]
    rintro dm (hd | rfl)
    · exact h.2.2.2.2.2 dm hd
    · show G w
      rcases proposal_mem _ _ _ hw with ⟨x, hx, hxv⟩ | hfb
      · simp only [quorum1B, List.mem_map, List.mem_filter] at hx
        obtain ⟨y, ⟨hy, -⟩, rfl⟩ := hx
        have := h.2.2.2.2.1 y hy
        rcases hxv with hxv | hxv
        · exact this.2 w hxv
        · exact this.1 w hxv
      · unfold fallback at hfb
        split_ifs at hfb
        · rcases hiv : s.initVal with _ | u
          · rw [hiv] at hfb
            exact h.2.1 w (by simpa using hfb)
          · rw [hiv] at hfb
            cases hfb
            exact h.1 _ hiv
        · exact h.1 w hfb
  · exact h

theorem StV.handleRaw {s : St P V} (h : StV G s) {q : P} {m : Msg P V} (hm : MsgV G m) :
    StV G (Impl.handleRaw c s (q, m)) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  have hout : ∀ dm, (∀ d ∈ s.out, MsgV G d.2) → MsgV G dm.2 →
      ∀ d ∈ s.out ++ [dm], MsgV G d.2 := by
    intro dm h hdm d hd
    simp only [List.mem_append, List.mem_singleton] at hd
    rcases hd with hd | rfl
    · exact h d hd
    · exact hdm
  cases m with
  | propose v =>
    simp only [Impl.handleRaw, onPropose]
    split_ifs
    · exact ⟨h1, by simpa [MsgV] using hm, h3, h4, h5, hout _ h6 hm⟩
    · exact ⟨h1, h2, h3, h4, h5, h6⟩
  | twoB b v =>
    refine ⟨h1, h2, h3, ?_, h5, h6⟩
    simp only [Impl.handleRaw, onTwoB, List.mem_append, List.mem_singleton]
    rintro x (hx | rfl)
    · exact h4 x hx
    · exact hm
  | decide b v =>
    exact ⟨h1, by simpa [Impl.handleRaw, onDecide, MsgV] using hm,
      by simpa [Impl.handleRaw, onDecide, MsgV] using hm, h4, h5, h6⟩
  | oneA b =>
    simp only [Impl.handleRaw, onOneA]
    split_ifs
    · exact ⟨h1, h2, h3, h4, h5, hout _ h6 ⟨h2, h3⟩⟩
    · exact ⟨h1, h2, h3, h4, h5, h6⟩
  | oneB b d =>
    simp only [Impl.handleRaw, onOneB]
    have hW : StV G { s with oneBs := s.oneBs ++ [(q, b, d)] } := by
      refine ⟨h1, h2, h3, h4, ?_, h6⟩
      simp only [List.mem_append, List.mem_singleton]
      rintro x (hx | rfl)
      · exact h5 x hx
      · exact hm
    split_ifs
    · exact ⟨h1, h2, h3, h4, h5, h6⟩
    · exact hW.lead c b
    · exact hW
  | twoA b v =>
    simp only [Impl.handleRaw, onTwoA]
    split_ifs
    · exact ⟨h1, by simpa [MsgV] using hm, h3, h4, h5, hout _ h6 hm⟩
    · exact ⟨h1, h2, h3, h4, h5, h6⟩

theorem StV.handle {s : St P V} (h : StV G s) {q : P} {m : Msg P V} (hm : MsgV G m) :
    StV G (Impl.handle c p s (q, m)) :=
  (h.handleRaw c hm).tryDecide c p

theorem StV.timer {s : St P V} (h : StV G s) (τ : ℕ) : StV G (Impl.timer c p τ s) := by
  unfold Impl.timer
  split_ifs
  · refine ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, ?_⟩
    simp only [List.mem_append, List.mem_singleton]
    rintro dm (hd | rfl)
    · exact h.2.2.2.2.2 dm hd
    · trivial
  · exact h

theorem StV.invoke {s : St P V} (h : StV G s) {inv : Option V} (hinv : ∀ v, inv = some v → G v) :
    StV G (Impl.invoke inv s) := by
  cases inv with
  | none => exact h
  | some v =>
    have hv := hinv v rfl
    simp only [Impl.invoke, onInv]
    split_ifs
    · refine ⟨by simpa using hv, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, ?_⟩
      simp only [List.mem_append, List.mem_singleton]
      rintro dm (hd | rfl)
      · exact h.2.2.2.2.2 dm hd
      · exact hv
    · exact h

theorem StV.stepFn {s : St P V} (h : StV G s) (τ : ℕ) {inv : Option V}
    (hinv : ∀ v, inv = some v → G v) {l : List (P × Msg P V)} (hl : ∀ q m, (q, m) ∈ l → MsgV G m) :
    StV G (Impl.stepFn c p τ s inv l) := by
  have h0 : StV G { s with out := [] } :=
    ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, by simp⟩
  exact (foldl_inv (Impl.handle c p) (StV G) (l := l) (fun s x hx hs => by
    obtain ⟨q, m⟩ := x; exact hs.handle c p (hl q m hx)) (h0.invoke hinv)).timer c p τ

end Values

section RunValues

variable {c : Cfg P} {R : Run P V (Msg P V)}

/-- The values invoked (by alive processes) before time `τ`. -/
def Invoked (R : Run P V (Msg P V)) (τ : ℕ) (v : V) : Prop :=
  ∃ q τ₁, τ₁ < τ ∧ R.alive q τ₁ ∧ R.inv q τ₁ = some v

theorem Invoked.mono {τ τ' : ℕ} (h : τ ≤ τ') {v : V} (hv : Invoked R τ v) : Invoked R τ' v := by
  obtain ⟨q, τ₁, h1, h2, h3⟩ := hv
  exact ⟨q, τ₁, by omega, h2, h3⟩

theorem values_all (hR : IsOrder R.ord) (τ : ℕ) :
    (∀ p, StV (Invoked R τ) (R.st (fig1 c) τ p)) ∧
      ∀ τ' < τ, ∀ q x m, m ∈ R.out (fig1 c) q τ' x → MsgV (Invoked R (τ' + 1)) m := by
  refine Run.invariant (fig1 c) R hR (fun τ _ s => StV (Invoked R τ) s)
    (fun τ _ m => MsgV (Invoked R (τ + 1)) m)
    (fun p => by simp [StV, fig1]) (fun τ p s h => h.mono fun v hv => hv.mono (by omega)) ?_ τ
  intro τ p ha hs hin
  rw [Run.st_succ_of_alive _ _ ha]
  have := (StV.mono (G' := Invoked R (τ + 1)) (fun v hv => hv.mono (by omega)) hs).stepFn c p τ
    (inv := R.inv p τ)
    (fun v hv => ⟨p, τ, by omega, ha, hv⟩) (l := R.inbox (fig1 c) p τ) (fun q m hm => by
      obtain ⟨τ', hτ', h⟩ := hin q m hm
      exact h.mono fun v hv => hv.mono (by omega))
  refine ⟨this, fun x m hm => ?_⟩
  rw [Run.out_of_alive _ _ ha, Run.st_succ_of_alive _ _ ha, mem_send] at hm
  obtain ⟨d, hd, -⟩ := hm
  exact this.2.2.2.2.2 _ hd

/-- Every value in the state of a process at time `τ` was invoked before `τ`. -/
theorem values_st (hR : IsOrder R.ord) (τ : ℕ) (p : P) :
    StV (Invoked R τ) (R.st (fig1 c) τ p) := (values_all hR τ).1 p

/-- Every value in a message sent at time `τ` was invoked at a time `≤ τ`. -/
theorem values_out (hR : IsOrder R.ord) {τ : ℕ} {q x : P} {m : Msg P V}
    (hm : m ∈ R.out (fig1 c) q τ x) : MsgV (Invoked R (τ + 1)) m :=
  (values_all hR (τ + 1)).2 τ (by omega) q x m hm

theorem values_inbox (hR : IsOrder R.ord) {τ : ℕ} {q x : P} {m : Msg P V}
    (hm : (q, m) ∈ R.inbox (fig1 c) x τ) : MsgV (Invoked R τ) m := by
  obtain ⟨τ', hτ', -, h⟩ := (Run.mem_inbox _ R hR).1 hm
  exact (values_out hR h).mono fun v hv => hv.mono (by omega)

end RunValues

end TwoStepConsensus.Impl
