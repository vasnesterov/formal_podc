import Papers.PODC2025.TwoStepConsensusLB.Fig1Protocol

/-!
# Basic invariants of the protocol of Fig. 1 (Ryabinin–Gotsman–Sutra, PODC 2025)

Local-state and message-provenance invariants (`Basic`) of the transition system of
`Fig1Protocol.lean`; they hold in every reachable state as soon as `f < n`. The safety argument
proper is in `Fig1Safety.lean`.
-/

set_option linter.unusedSimpArgs false

namespace TwoStepConsensus.Fig1

variable {P V : Type*} [Fintype P] [DecidableEq P] [LinearOrder V]

/-- Basic (mostly local) invariants of the protocol of Fig. 1. -/
structure Basic (cfg : Config P V) (s : State P V) : Prop where
  vbal_le_bal : ∀ q, (s.loc q).vbal ≤ (s.loc q).bal
  val_of_decided : ∀ q, (s.loc q).decided ≠ none → (s.loc q).val ≠ none
  val_eq_decided : ∀ q a, (s.loc q).decided = some a → (s.loc q).vbal = 0 →
    (s.loc q).val = some a
  vbal_pos : ∀ q, 0 < (s.loc q).vbal → (s.loc q).decided = none →
    ∃ u, (s.loc q).val = some u ∧ .twoA (s.loc q).vbal u ∈ s.msgs
  zero_vote : ∀ q w, (s.loc q).decided = none → (s.loc q).vbal = 0 → (s.loc q).val = some w →
    ∃ p, (s.loc q).proposer = some p ∧ .twoB q p 0 w ∈ s.msgs
  decided_msg : ∀ q a, (s.loc q).decided = some a → ∃ x b, .decide x b a ∈ s.msgs
  initVal_task : cfg.ver = .task → ∀ q, (s.loc q).initVal = some (cfg.input q)
  initVal_obj : cfg.ver = .object → ∀ q a, (s.loc q).initVal = some a → (s.loc q).inv = some a
  propose_initVal : ∀ p w, .propose p w ∈ s.msgs → (s.loc p).initVal = some w
  twoB0 : ∀ q p w, .twoB q p 0 w ∈ s.msgs → .propose p w ∈ s.msgs ∧ q ≠ p ∧
    (s.loc q).proposer = some p ∧ (s.loc q).val ≠ none ∧ Accepts cfg.ver (s.loc q).initVal w
  twoB0_unique : ∀ q p p' w w', .twoB q p 0 w ∈ s.msgs → .twoB q p' 0 w' ∈ s.msgs →
    p = p' ∧ w = w'
  twoB0_val : ∀ q p w, .twoB q p 0 w ∈ s.msgs → (s.loc q).decided = none →
    (s.loc q).vbal = 0 → (s.loc q).val = some w
  twoB_vbal : ∀ q z b w, .twoB q z b w ∈ s.msgs → b ≤ (s.loc q).vbal
  twoB_twoA : ∀ q z b w, .twoB q z b w ∈ s.msgs → 0 < b → .twoA b w ∈ s.msgs
  twoA_unique : ∀ b w w', .twoA b w ∈ s.msgs → .twoA b w' ∈ s.msgs → w = w'
  twoA_quorum : ∀ b w, .twoA b w ∈ s.msgs → 0 < b ∧
    ∃ Q : Finset P, Q.card = Fintype.card P - cfg.f ∧ ∀ y ∈ Q, ∃ d, .oneB y b d ∈ s.msgs
  oneB_bal : ∀ y c d, .oneB y c d ∈ s.msgs → 0 < c ∧ c ≤ (s.loc y).bal
  oneB_order : ∀ y c d z b w, .oneB y c d ∈ s.msgs → .twoB y z b w ∈ s.msgs → b < c →
    b ≤ d.vbal
  oneB_vbal : ∀ y c d, .oneB y c d ∈ s.msgs → 0 < d.vbal → d.decided = none →
    ∃ u, d.val = some u ∧ .twoA d.vbal u ∈ s.msgs
  oneB_zero : ∀ y c d w, .oneB y c d ∈ s.msgs → d.decided = none → d.vbal = 0 →
    d.val = some w → ∃ p, d.proposer = some p ∧ .twoB y p 0 w ∈ s.msgs
  oneB_vote : ∀ y c d p w, .oneB y c d ∈ s.msgs → .twoB y p 0 w ∈ s.msgs →
    d.decided = none → d.vbal = 0 → d.val = some w ∧ d.proposer = some p
  oneB_decided : ∀ y c d a, .oneB y c d ∈ s.msgs → d.decided = some a →
    ∃ x b, .decide x b a ∈ s.msgs
  decide_decided : ∀ p b v, .decide p b v ∈ s.msgs → (s.loc p).decided ≠ none
  decide_fast : ∀ p v, .decide p 0 v ∈ s.msgs →
    (∃ P' : Finset P, P'.Nonempty ∧ Fintype.card P - cfg.e ≤ (insert p P').card ∧
      ∀ q ∈ P', .twoB q p 0 v ∈ s.msgs) ∧
    ∀ c d, .oneB p c d ∈ s.msgs → d.decided ≠ none
  decide_slow : ∀ p b v, .decide p b v ∈ s.msgs → 0 < b →
    ∃ P' : Finset P, Fintype.card P - cfg.f ≤ P'.card ∧ ∀ q ∈ P', .twoB q p b v ∈ s.msgs

theorem basic_init (cfg : Config P V) : Basic cfg (init cfg) := by
  constructor <;> intros <;> simp_all [init]

theorem basic_step_invoke {cfg : Config P V} {s s' : State P V} {p : P}
    (hI : Basic cfg s) (h : Step cfg p .invoke s s') : Basic cfg s' := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
    h20, h21, h22, h23, h24, h25⟩ := hI
  cases h; constructor
  all_goals intros
  all_goals simp only [State.set_loc, State.set_msgs, State.send_loc, State.mem_send_msgs] at *
  all_goals (try grind [Loc.snap])

theorem basic_step_sendPropose {cfg : Config P V} {s s' : State P V} {p : P}
    (hI : Basic cfg s) (h : Step cfg p .sendPropose s s') : Basic cfg s' := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
    h20, h21, h22, h23, h24, h25⟩ := hI
  cases h; constructor
  all_goals intros
  all_goals simp only [State.set_loc, State.set_msgs, State.send_loc, State.mem_send_msgs] at *
  all_goals (try grind [Loc.snap])

theorem basic_step_recvPropose {cfg : Config P V} {s s' : State P V} {p : P}
    (hI : Basic cfg s) (h : Step cfg p .recvPropose s s') : Basic cfg s' := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
    h20, h21, h22, h23, h24, h25⟩ := hI
  cases h; constructor
  all_goals intros
  all_goals simp only [State.set_loc, State.set_msgs, State.send_loc, State.mem_send_msgs] at *
  all_goals (try grind [Loc.snap])

theorem basic_step_fastDecide {cfg : Config P V} {s s' : State P V} {p : P}
    (hI : Basic cfg s) (h : Step cfg p .fastDecide s s') : Basic cfg s' := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
    h20, h21, h22, h23, h24, h25⟩ := hI
  cases h; constructor
  all_goals intros
  all_goals simp only [State.set_loc, State.set_msgs, State.send_loc, State.mem_send_msgs] at *
  case decided_msg q a ha =>
    by_cases hq : q = p
    · subst hq; simp only [ite_true] at ha; cases ha; exact ⟨q, 0, Or.inl rfl⟩
    · simp only [hq, ite_false] at ha; obtain ⟨x, b, hx⟩ := h6 q a ha; exact ⟨x, b, Or.inr hx⟩
  all_goals (try grind [Loc.snap])

theorem basic_step_slowDecide {cfg : Config P V} {s s' : State P V} {p : P}
    (hI : Basic cfg s) (h : Step cfg p .slowDecide s s') : Basic cfg s' := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
    h20, h21, h22, h23, h24, h25⟩ := hI
  cases h; constructor
  all_goals intros
  all_goals simp only [State.set_loc, State.set_msgs, State.send_loc, State.mem_send_msgs] at *
  case decided_msg q a ha =>
    by_cases hq : q = p
    · subst hq; simp only [ite_true] at ha; cases ha; exact ⟨q, (s.loc q).bal, Or.inl rfl⟩
    · simp only [hq, ite_false] at ha; obtain ⟨x, b, hx⟩ := h6 q a ha; exact ⟨x, b, Or.inr hx⟩
  all_goals (try grind [Loc.snap])

theorem basic_step_recvDecide {cfg : Config P V} {s s' : State P V} {p : P}
    (hI : Basic cfg s) (h : Step cfg p .recvDecide s s') : Basic cfg s' := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
    h20, h21, h22, h23, h24, h25⟩ := hI
  cases h; constructor
  all_goals intros
  all_goals simp only [State.set_loc, State.set_msgs, State.send_loc, State.mem_send_msgs] at *
  all_goals (try grind [Loc.snap])

theorem basic_step_recv1A {cfg : Config P V} {s s' : State P V} {p : P}
    (hI : Basic cfg s) (h : Step cfg p .recv1A s s') : Basic cfg s' := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
    h20, h21, h22, h23, h24, h25⟩ := hI
  cases h; constructor
  all_goals intros
  all_goals simp only [State.set_loc, State.set_msgs, State.send_loc, State.mem_send_msgs] at *
  all_goals (try grind [Loc.snap])

theorem basic_step_start1A {cfg : Config P V} {s s' : State P V} {p : P}
    (hI : Basic cfg s) (h : Step cfg p .start1A s s') : Basic cfg s' := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
    h20, h21, h22, h23, h24, h25⟩ := hI
  cases h; constructor
  all_goals intros
  all_goals simp only [State.set_loc, State.set_msgs, State.send_loc, State.mem_send_msgs] at *
  all_goals (try grind [Loc.snap])

theorem basic_step_send2A {cfg : Config P V} (hf : cfg.f < Fintype.card P) {s s' : State P V}
    {p : P}
    (hI : Basic cfg s) (h : Step cfg p .send2A s s') : Basic cfg s' := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
    h20, h21, h22, h23, h24, h25⟩ := hI
  cases h with
  | send2A Q rep how hno hcard hQ hsel => ?_
  constructor
  all_goals intros
  all_goals simp only [State.set_loc, State.set_msgs, State.send_loc, State.mem_send_msgs] at *
  case twoA_quorum b' w hm =>
    rcases hm with hm | hm
    · simp only [Msg.twoA.injEq] at hm
      obtain ⟨rfl, rfl⟩ := hm
      obtain ⟨q, hq⟩ : Q.Nonempty := by rw [← Finset.card_pos]; omega
      exact ⟨(h17 _ _ _ (hQ q hq)).1, Q, hcard, fun y hy => ⟨rep y, Or.inr (hQ y hy)⟩⟩
    · obtain ⟨hb, Q', h1', h2'⟩ := h16 _ _ hm
      exact ⟨hb, Q', h1', fun y hy => (h2' y hy).imp fun d hd => Or.inr hd⟩
  all_goals (try grind [Loc.snap])

theorem basic_step_recv2A {cfg : Config P V} {s s' : State P V} {p : P}
    (hI : Basic cfg s) (h : Step cfg p .recv2A s s') : Basic cfg s' := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
    h20, h21, h22, h23, h24, h25⟩ := hI
  cases h; constructor
  all_goals intros
  all_goals simp only [State.set_loc, State.set_msgs, State.send_loc, State.mem_send_msgs] at *
  all_goals (try grind [Loc.snap])

theorem basic_step {cfg : Config P V} (hf : cfg.f < Fintype.card P) {s s' : State P V} {p : P}
    {k : Kind}
    (hI : Basic cfg s) (h : Step cfg p k s s') : Basic cfg s' := by
  cases k
  · exact basic_step_invoke hI h
  · exact basic_step_sendPropose hI h
  · exact basic_step_recvPropose hI h
  · exact basic_step_fastDecide hI h
  · exact basic_step_slowDecide hI h
  · exact basic_step_recvDecide hI h
  · exact basic_step_recv1A hI h
  · exact basic_step_start1A hI h
  · exact basic_step_send2A hf hI h
  · exact basic_step_recv2A hI h

/-- The basic invariants hold in every reachable state (if `f < n`). -/
theorem basic_of_reachable {cfg : Config P V} (hf : cfg.f < Fintype.card P) {s : State P V}
    (h : Reachable cfg s) : Basic cfg s := by
  induction h with
  | refl => exact basic_init cfg
  | tail _ hst ih => obtain ⟨p, k, hst⟩ := hst; exact basic_step hf ih hst

/-- Every step only adds messages. -/
theorem Step.msgs_mono {cfg : Config P V} {s s' : State P V} {p : P} {k : Kind}
    (h : Step cfg p k s s') : s.msgs ⊆ s'.msgs := by
  cases h <;> intro m hm <;> simp [hm]

/-- Ballots never decrease. -/
theorem Step.bal_mono {cfg : Config P V} {s s' : State P V} {p : P} {k : Kind}
    (h : Step cfg p k s s') (q : P) : (s.loc q).bal ≤ (s'.loc q).bal := by
  cases h <;> simp only [State.set_loc, State.send_loc] <;> (try split_ifs) <;> simp_all; omega

end TwoStepConsensus.Fig1
