import Papers.PODC2019.AbortableMutexAmortized.InvEasy
import Papers.PODC2019.AbortableMutexAmortized.InvLines

/-!
# The invariant holds in every reachable configuration; the canonical queue
-/

namespace Podc.AbortableMutexAmortized

variable {n : ℕ}

theorem inv_init : Inv (init : State n) := by
  refine ⟨[], none, ⟨⟨by simp, by simp, fun p q h => by simpa [init] using h, by simp⟩, rfl,
    fun q => ?_, fun p => by simp [init]⟩, ?_⟩
  · simp [InQ, init, PC.act, PC.ab]
  · constructor <;> intros <;> simp_all [init, InQ, PC.act, PC.ab]

theorem inv_fasPred {s : State n} {Q : List (Fin n)} {a0 : Node n} (hs : Struct s Q a0)
    (hl : Loc s a0) {p : Fin n} (hp : (s.pc p).act = true) (h7 : s.pc p ≠ .l7) :
    ∃ Q', Struct (fasPred s p) Q' a0 ∧ Loc (fasPred s p) a0 ∧ QStep p Q Q' := by
  have hpQ : InQ s p := Or.inl hp
  rw [fasPred_eq]
  rcases hs.pred_cases hpQ with hpa | ⟨x, hxQ, hpx⟩
  · rw [hpa, hl.token_of hs hpQ hpa h7]
    have := inv_fas_head hs hl hp h7 hpa (w := .go p) (Or.inl rfl)
    exact ⟨Q, this.1, this.2, .same Q⟩
  · by_cases hx : (s.pc x).act = true
    · have ho : s.node (s.pred p) = .nil ∨ s.node (s.pred p) = .go p := by
        rw [hpx]
        rcases hl.i7 x hx with h | ⟨y, hy, hyx, h⟩
        · exact Or.inl h
        · have := hs.pred_inj hy hpQ (hyx.trans hpx.symm); subst this; exact Or.inr h
      have hc : loopPC (s.node (s.pred p)) = .l4 := by rcases ho with h | h <;> rw [h] <;> rfl
      rw [hc]
      have := inv_fas_act hs hl hp hpx hx (w := .go p) (c := .l4) (Or.inl ⟨rfl, rfl⟩)
      exact ⟨Q, this.1, this.2, .same Q⟩
    · have hx' : (s.pc x).act = false := by simpa using hx
      have hc : loopPC (s.node (s.pred p)) = .l6 := by
        rw [hpx, (InQ.ab_cases hxQ hx').2]; rfl
      rw [hc]
      obtain ⟨L, R, hQ, h1, h2⟩ := inv_fas_splice hs hl hp hpx hxQ hx' (w := .go p) (c := .l6)
        (Or.inl ⟨rfl, rfl⟩)
      exact ⟨_, h1, h2, hQ ▸ .splice L x R⟩

theorem inv_line9 {s : State n} {Q : List (Fin n)} {a0 : Node n} (hs : Struct s Q a0)
    (hl : Loc s a0) {p : Fin n} (hp : (s.pc p).act = true) (h7 : s.pc p ≠ .l7) :
    ∃ Q', Struct (line9 s p) Q' a0 ∧ Loc (line9 s p) a0 ∧ QStep p Q Q' := by
  have hpQ : InQ s p := Or.inl hp
  rw [line9_eq]
  rcases hs.pred_cases hpQ with hpa | ⟨x, hxQ, hpx⟩
  · rw [hpa, hl.token_of hs hpQ hpa h7, if_pos rfl]
    have := inv_fas_head hs hl hp h7 hpa (w := .nil) (Or.inr rfl)
    exact ⟨Q, this.1, this.2, .same Q⟩
  · by_cases hx : (s.pc x).act = true
    · have ho : s.node (s.pred p) = .nil ∨ s.node (s.pred p) = .go p := by
        rw [hpx]
        rcases hl.i7 x hx with h | ⟨y, hy, hyx, h⟩
        · exact Or.inl h
        · have := hs.pred_inj hy hpQ (hyx.trans hpx.symm); subst this; exact Or.inr h
      have hc : (if s.node (s.pred p) = .token then PC.l7 else .l10) = .l10 := by
        rcases ho with h | h <;> rw [h] <;> rfl
      rw [hc]
      have := inv_fas_act hs hl hp hpx hx (w := .nil) (c := .l10) (Or.inr ⟨rfl, rfl⟩)
      exact ⟨Q, this.1, this.2, .same Q⟩
    · have hx' : (s.pc x).act = false := by simpa using hx
      have hc : (if s.node (s.pred p) = .token then PC.l7 else .l10) = .l10 := by
        rw [hpx, (InQ.ab_cases hxQ hx').2]; rfl
      rw [hc]
      obtain ⟨L, R, hQ, h1, h2⟩ := inv_fas_splice hs hl hp hpx hxQ hx' (w := .nil) (c := .l10)
        (Or.inr ⟨rfl, rfl⟩)
      exact ⟨_, h1, h2, hQ ▸ .splice L x R⟩

/-- The invariant is preserved by every step, and the queue changes as described by `QStep`. -/
theorem inv_step {s : State n} {Q : List (Fin n)} {a0 : Node n} (hs : Struct s Q a0)
    (hl : Loc s a0) (p : Fin n) (ab : Bool) :
    ∃ Q' a0', Struct (step s p ab) Q' a0' ∧ Loc (step s p ab) a0' ∧ QStep p Q Q' := by
  cases hp : s.pc p with
  | l1 =>
    have h := inv_l1 hs hl hp
    have e : step s p ab = l1Upd s p
        (if s.node (s.mynode p) = .addr (s.pred p) then .l3 else .l2) := by
      unfold step; rw [hp]; rfl
    rw [e]; exact ⟨Q, a0, h.1, h.2, .same Q⟩
  | l2 =>
    have h := inv_l2 hs hl hp
    have e : step s p ab = l2Upd s p := by unfold step; rw [hp]; rfl
    rw [e]; exact ⟨_, a0, h.1, h.2, .enq Q⟩
  | l3 =>
    have e : step s p ab = fasPred s p := by unfold step; rw [hp]
    obtain ⟨Q', h1, h2, h3⟩ := inv_fasPred hs hl (p := p) (by simp [hp]) (by simp [hp])
    rw [e]; exact ⟨Q', a0, h1, h2, h3⟩
  | l4 =>
    cases ab with
    | true =>
      have e : step s p true = line9 s p := by unfold step; rw [hp]; rfl
      obtain ⟨Q', h1, h2, h3⟩ := inv_line9 hs hl (p := p) (by simp [hp]) (by simp [hp])
      rw [e]; exact ⟨Q', a0, h1, h2, h3⟩
    | false =>
      by_cases hg : s.go p = true
      · have e : step s p false = { s with pc := Function.update s.pc p .l5 } := by
          unfold step; rw [hp]; simp [hg]
        have h := inv_l4_go hs hl hp hg
        rw [e]; exact ⟨Q, a0, h.1, h.2, .same Q⟩
      · have e : step s p false = s := by unfold step; rw [hp]; simp [hg]
        rw [e]; exact ⟨Q, a0, hs, hl, .same Q⟩
  | l5 =>
    cases ab with
    | true =>
      have e : step s p true = line9 s p := by unfold step; rw [hp]; rfl
      obtain ⟨Q', h1, h2, h3⟩ := inv_line9 hs hl (p := p) (by simp [hp]) (by simp [hp])
      rw [e]; exact ⟨Q', a0, h1, h2, h3⟩
    | false =>
      have e : step s p false =
          { s with go := Function.update s.go p false, pc := Function.update s.pc p .l6 } := by
        unfold step; rw [hp]; rfl
      have h := inv_l5 hs hl hp
      rw [e]; exact ⟨Q, a0, h.1, h.2, .same Q⟩
  | l6 =>
    cases ab with
    | true =>
      have e : step s p true = line9 s p := by unfold step; rw [hp]; rfl
      obtain ⟨Q', h1, h2, h3⟩ := inv_line9 hs hl (p := p) (by simp [hp]) (by simp [hp])
      rw [e]; exact ⟨Q', a0, h1, h2, h3⟩
    | false =>
      have e : step s p false = fasPred s p := by unfold step; rw [hp]; rfl
      obtain ⟨Q', h1, h2, h3⟩ := inv_fasPred hs hl (p := p) (by simp [hp]) (by simp [hp])
      rw [e]; exact ⟨Q', a0, h1, h2, h3⟩
  | l7 =>
    have e : step s p ab = l7Upd s p := by unfold step; rw [hp]; rfl
    obtain ⟨R, hQ, h1, h2⟩ := inv_l7 hs hl hp
    rw [e]; exact ⟨R, _, h1, h2, hQ ▸ .deq R⟩
  | l8 =>
    have e : step s p ab = wake s p := by unfold step; rw [hp]
    have h := inv_wake hs hl (Or.inl hp)
    rw [e]; exact ⟨Q, a0, h.1, h.2, .same Q⟩
  | l9 =>
    have e : step s p ab = line9 s p := by unfold step; rw [hp]
    obtain ⟨Q', h1, h2, h3⟩ := inv_line9 hs hl (p := p) (by simp [hp]) (by simp [hp])
    rw [e]; exact ⟨Q', a0, h1, h2, h3⟩
  | l10 =>
    have e : step s p ab = l10Upd s p := by unfold step; rw [hp]; rfl
    have h := inv_l10 hs hl hp
    rw [e]; exact ⟨Q, a0, h.1, h.2, .same Q⟩
  | l11 =>
    have e : step s p ab = wake s p := by unfold step; rw [hp]
    have h := inv_wake hs hl (Or.inr hp)
    rw [e]; exact ⟨Q, a0, h.1, h.2, .same Q⟩

theorem Reachable.inv {s : State n} (h : Reachable s) : Inv s := by
  induction h with
  | init => exact inv_init
  | step p ab _ ih =>
    obtain ⟨Q, a0, hs, hl⟩ := ih
    obtain ⟨Q', a0', hs', hl', -⟩ := inv_step hs hl p ab
    exact ⟨Q', a0', hs', hl'⟩

/-- `a₀` is the unique node that is nobody's `mynode`. -/
theorem a0_unique {s : State n} {a0 a0' : Node n} (h : Function.Injective s.mynode)
    (h0 : ∀ p, s.mynode p ≠ a0) (h0' : ∀ p, s.mynode p ≠ a0') : a0 = a0' := by
  by_contra hne
  have hsub : Finset.univ.image s.mynode ⊆ (Finset.univ.erase a0).erase a0' := by
    intro x hx
    obtain ⟨p, -, rfl⟩ := Finset.mem_image.1 hx
    simp [h0 p, h0' p]
  have := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ h, Finset.card_erase_of_mem (by simp [Ne.symm hne]),
    Finset.card_erase_of_mem (by simp)] at this
  simp at this
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rcases a0 with _ | ⟨⟨_, h⟩⟩ <;> rcases a0' with _ | ⟨⟨_, h'⟩⟩ <;> simp_all <;> omega
  · omega

/-- `Q` and `a₀` are determined by the configuration (the "uniqueness" part of Theorem 4.1). -/
theorem struct_unique {s : State n} {Q Q' : List (Fin n)} {a0 a0' : Node n}
    (h : Struct s Q a0) (h' : Struct s Q' a0') : Q = Q' ∧ a0 = a0' := by
  have ha : a0 = a0' := a0_unique h.ok.inj h.a0_ne h'.a0_ne
  subst ha
  exact ⟨h.ok.unique h'.ok (fun x => (h.mem x).trans (h'.mem x).symm), rfl⟩

open Classical in
/-- The queue `Q` of a configuration satisfying the invariant (`[]` otherwise). -/
noncomputable def Qof (s : State n) : List (Fin n) :=
  if h : ∃ Q a0, Struct s Q a0 then h.choose else []

open Classical in
/-- The node `a₀` of a configuration satisfying the invariant. -/
noncomputable def a0of (s : State n) : Node n :=
  if h : ∃ Q a0, Struct s Q a0 then h.choose_spec.choose else none

theorem Struct.Qof_eq {s : State n} {Q : List (Fin n)} {a0 : Node n} (h : Struct s Q a0) :
    Qof s = Q ∧ a0of s = a0 := by
  have hex : ∃ Q a0, Struct s Q a0 := ⟨Q, a0, h⟩
  have := struct_unique hex.choose_spec.choose_spec h
  simp only [Qof, a0of, dite_eq_left_of_eq_true (eq_true hex)]
  exact this

theorem Inv.struct {s : State n} (h : Inv s) : Struct s (Qof s) (a0of s) := by
  obtain ⟨Q, a0, hs, -⟩ := h
  obtain ⟨h1, h2⟩ := hs.Qof_eq
  rw [h1, h2]; exact hs

theorem Inv.loc {s : State n} (h : Inv s) : Loc s (a0of s) := by
  obtain ⟨Q, a0, hs, hl⟩ := h
  rw [hs.Qof_eq.2]; exact hl

theorem Inv.stepInv {s : State n} (h : Inv s) (p : Fin n) (ab : Bool) : Inv (step s p ab) := by
  obtain ⟨Q', a0', hs', hl', -⟩ := inv_step h.struct h.loc p ab
  exact ⟨Q', a0', hs', hl'⟩

/-- How the canonical queue changes in a step. -/
theorem Inv.qstep {s : State n} (h : Inv s) (p : Fin n) (ab : Bool) :
    QStep p (Qof s) (Qof (step s p ab)) := by
  obtain ⟨Q', a0', hs', -, hq⟩ := inv_step h.struct h.loc p ab
  rw [hs'.Qof_eq.1]; exact hq

theorem Inv.mem_Qof {s : State n} (h : Inv s) {q : Fin n} : q ∈ Qof s ↔ InQ s q :=
  h.struct.mem q

end Podc.AbortableMutexAmortized
