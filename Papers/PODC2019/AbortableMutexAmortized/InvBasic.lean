import Papers.PODC2019.AbortableMutexAmortized.InvDefs

/-!
# Basic consequences of the structural invariant
-/

namespace Podc.AbortableMutexAmortized

variable {n : ℕ} {s : State n} {Q : List (Fin n)} {a0 : Node n}

@[simp] theorem PC.act_l1 : PC.l1.act = false := rfl
@[simp] theorem PC.act_l2 : PC.l2.act = false := rfl
@[simp] theorem PC.act_l3 : PC.l3.act = true := rfl
@[simp] theorem PC.act_l4 : PC.l4.act = true := rfl
@[simp] theorem PC.act_l5 : PC.l5.act = true := rfl
@[simp] theorem PC.act_l6 : PC.l6.act = true := rfl
@[simp] theorem PC.act_l7 : PC.l7.act = true := rfl
@[simp] theorem PC.act_l8 : PC.l8.act = false := rfl
@[simp] theorem PC.act_l9 : PC.l9.act = true := rfl
@[simp] theorem PC.act_l10 : PC.l10.act = true := rfl
@[simp] theorem PC.act_l11 : PC.l11.act = false := rfl
@[simp] theorem PC.ab_l1 : PC.l1.ab = true := rfl
@[simp] theorem PC.ab_l2 : PC.l2.ab = false := rfl
@[simp] theorem PC.ab_l3 : PC.l3.ab = false := rfl
@[simp] theorem PC.ab_l4 : PC.l4.ab = false := rfl
@[simp] theorem PC.ab_l5 : PC.l5.ab = false := rfl
@[simp] theorem PC.ab_l6 : PC.l6.ab = false := rfl
@[simp] theorem PC.ab_l7 : PC.l7.ab = false := rfl
@[simp] theorem PC.ab_l8 : PC.l8.ab = false := rfl
@[simp] theorem PC.ab_l9 : PC.l9.ab = false := rfl
@[simp] theorem PC.ab_l10 : PC.l10.ab = false := rfl
@[simp] theorem PC.ab_l11 : PC.l11.ab = true := rfl

theorem PC.act_or_ab (c : PC) : c.act = true ∨ c.ab = true ∨ c = .l2 ∨ c = .l8 := by
  cases c <;> simp

theorem InQ.of_act {q : Fin n} (h : (s.pc q).act = true) : InQ s q := Or.inl h

theorem InQ.of_pc {q : Fin n} {c : PC} (h : s.pc q = c) (hc : c.act = true) : InQ s q :=
  Or.inl (h ▸ hc)

theorem InQ.node_eq {q : Fin n} (h : InQ s q) (hc : (s.pc q).act = false) :
    s.node (s.mynode q) = .addr (s.pred q) := by
  rcases h with h | h
  · simp_all
  · exact h.2

theorem not_InQ_l2 {q : Fin n} (h : s.pc q = .l2) : ¬ InQ s q := by
  simp [InQ, h]

theorem not_InQ_l8 {q : Fin n} (h : s.pc q = .l8) : ¬ InQ s q := by
  simp [InQ, h]

namespace Struct

variable (hs : Struct s Q a0)
include hs

theorem inj : Function.Injective s.mynode := hs.ok.inj

theorem pred_inj {y y' : Fin n} (hy : InQ s y) (hy' : InQ s y') (e : s.pred y = s.pred y') :
    y = y' := hs.ok.pred_inj ((hs.mem y).2 hy) ((hs.mem y').2 hy') e

theorem pred_cases {y : Fin n} (hy : InQ s y) :
    s.pred y = a0 ∨ ∃ x, InQ s x ∧ s.pred y = s.mynode x := by
  rcases hs.ok.chain.pred_mem ((hs.mem y).2 hy) with h | ⟨x, hx, h⟩
  · exact Or.inl h
  · exact Or.inr ⟨x, (hs.mem x).1 hx, h⟩

theorem pred_ne_mynode_self {y : Fin n} (hy : InQ s y) : s.pred y ≠ s.mynode y := by
  intro e
  obtain ⟨L, R, h⟩ := hs.ok.adj ((hs.mem y).2 hy) ((hs.mem y).2 hy) e
  have := hs.ok.nodup
  rw [h] at this
  simp [List.nodup_append, List.nodup_cons] at this

theorem pred_ne_tail {y : Fin n} (hy : InQ s y) : s.pred y ≠ s.tail := by
  rw [← hs.last]; exact hs.ok.pred_ne_last ((hs.mem y).2 hy)

theorem mynode_ne_a0 (p : Fin n) : s.mynode p ≠ a0 := hs.a0_ne p

/-- A queue member that is nobody's predecessor is the last one. -/
theorem tail_of_no_succ {x : Fin n} (hx : InQ s x) (h : ∀ y, InQ s y → s.pred y ≠ s.mynode x) :
    s.mynode x = s.tail := by
  rw [← hs.last]
  exact hs.ok.last_of_mem ((hs.mem x).2 hx) (fun y hy => h y ((hs.mem y).1 hy))

theorem succ_of_ne_tail {x : Fin n} (hx : InQ s x) (h : s.mynode x ≠ s.tail) :
    ∃ y, InQ s y ∧ s.pred y = s.mynode x := by
  rw [← hs.last] at h
  obtain ⟨y, hy, e⟩ := hs.ok.succ_exists ((hs.mem x).2 hx) h
  exact ⟨y, (hs.mem y).1 hy, e⟩

theorem empty_or_tail (h : ∀ x, s.mynode x ≠ s.tail) : Q = [] ∧ s.tail = a0 := by
  cases Q with
  | nil => exact ⟨rfl, hs.last.symm⟩
  | cons q R =>
    exfalso
    rcases lastN_mem (my := s.mynode) (s.mynode q) R with e | ⟨x, -, e⟩
    · exact h q (by rw [← hs.last, lastN_cons, e])
    · exact h x (by rw [← hs.last, lastN_cons, e])

/-- Only queue members have their node as `tail`, unless the queue is empty. -/
theorem tail_cases : s.tail = a0 ∨ ∃ x, InQ s x ∧ s.mynode x = s.tail := by
  rw [← hs.last]
  rcases lastN_mem (my := s.mynode) a0 Q with e | ⟨x, hx, e⟩
  · exact Or.inl e
  · exact Or.inr ⟨x, (hs.mem x).1 hx, e.symm⟩

theorem tail_inQ {x : Fin n} (h : s.mynode x = s.tail) : InQ s x := by
  rcases hs.tail_cases with e | ⟨y, hy, e⟩
  · exact absurd (h.trans e) (hs.a0_ne x)
  · exact (hs.inj (h.trans e.symm)) ▸ hy

end Struct

end Podc.AbortableMutexAmortized
