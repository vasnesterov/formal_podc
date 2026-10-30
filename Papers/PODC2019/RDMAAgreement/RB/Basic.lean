import Papers.PODC2019.RDMAAgreement.RB.Model

/-!
# Algorithm 2 — simp lemmas for the state operations
-/

set_option linter.unusedSectionVars false

namespace Podc.RDMAAgreement.RB

/-- The phase (`state[q]`) a program counter belongs to (`none`: the `checkL2proof` part). -/
def PC.ph {P M : Type} : PC P M → Option Phase
  | .rdSnd => some .wfs
  | .wrEcho _ => some .wfs
  | .rdVal _ _ _ => some .wfl1
  | .wrL1 _ => some .wfl1
  | .rdL1 _ _ _ => some .wfl2
  | .wrL2 _ => some .wfl2
  | _ => none

namespace St

variable {P M : Type} [Fintype P] [DecidableEq P] [DecidableEq M]

@[simp] lemma upd2_apply {X : Type} (g : P → P → X) (p q : P) (x : X) (p' q' : P) :
    upd2 g p q x p' q' = if p' = p ∧ q' = q then x else g p' q' := by
  unfold upd2
  by_cases h : p' = p
  · subst h; by_cases h' : q' = q
    · subst h'; simp
    · simp [h']
  · simp [h]

lemma upd3_apply {X : Type} (g : P → P → ℕ → X) (p q : P) (k : ℕ) (x : X) (p' q' : P)
    (k' : ℕ) :
    upd3 g p q k x p' q' k' = if p' = p ∧ q' = q ∧ k' = k then x else g p' q' k' := by
  unfold upd3
  by_cases h : p' = p
  · subst h; by_cases h' : q' = q
    · subst h'; by_cases h'' : k' = k
      · subst h''; simp
      · simp [h'']
    · simp [h']
  · simp [h]

@[simp] lemma upd3_apply2 {X : Type} (g : P → P → ℕ → X) (p q : P) (k : ℕ) (x : X) (p' q' : P) :
    upd3 g p q k x p' q' = if p' = p ∧ q' = q then Function.update (g p q) k x else g p' q' := by
  funext k'; rw [upd3_apply]
  by_cases h : p' = p ∧ q' = q
  · obtain ⟨rfl, rfl⟩ := h; simp [Function.update_apply]
  · simp only [h, if_false]; simp only [not_and] at h; split_ifs with h' <;> tauto

variable (s : St P M) (p q : P) (c : PC P M)

section go

@[simp] lemma go_now : (s.go p q c).now = s.now := by unfold go; split <;> rfl
@[simp] lemma go_mem : (s.go p q c).mem = s.mem := by unfold go; split <;> rfl
@[simp] lemma go_pc : (s.go p q c).pc = upd2 s.pc p q c := by unfold go; split <;> rfl
@[simp] lemma go_last : (s.go p q c).last = s.last := by unfold go; split <;> rfl
@[simp] lemma go_phase : (s.go p q c).phase = s.phase := by unfold go; split <;> rfl
@[simp] lemma go_scanT : (s.go p q c).scanT = s.scanT := by unfold go; split <;> rfl
@[simp] lemma go_bnext : (s.go p q c).bnext = s.bnext := by unfold go; split <;> rfl
@[simp] lemma go_bpend : (s.go p q c).bpend = s.bpend := by unfold go; split <;> rfl
@[simp] lemma go_signed : (s.go p q c).signed = s.signed := by unfold go; split <;> rfl
@[simp] lemma go_bc : (s.go p q c).bc = s.bc := by unfold go; split <;> rfl
@[simp] lemma go_dlv : (s.go p q c).dlv = s.dlv := by unfold go; split <;> rfl
@[simp] lemma go_echo : (s.go p q c).echo = s.echo := by unfold go; split <;> rfl
@[simp] lemma go_echoT : (s.go p q c).echoT = s.echoT := by unfold go; split <;> rfl
@[simp] lemma go_l1 : (s.go p q c).l1 = s.l1 := by unfold go; split <;> rfl

@[simp] lemma key_go : (s.go p q c).key = s.key := by unfold key; simp

end go

@[simp] lemma key_tick : s.tick.key = s.key := rfl
@[simp] lemma key_write (r : Reg P) (v : Val P M) : (s.write r v).key = s.key := rfl
@[simp] lemma key_sign (x : P × Sig P M) : (s.sign x).key = s.key := rfl
@[simp] lemma key_setPhase (ph : Phase) : (s.setPhase p q ph).key = s.key := rfl

/-- Membership in a pending-write set. -/
lemma mem_pendW (r : Reg P) (x : Val P M) :
    x ∈ s.pendW r ↔ (∃ p q, (s.pc p q).wr p q (s.key p q) = some (r, x)) ∨
      ∃ p b, s.bpend p = some b ∧ r = ⟨.val, p, b.key, p⟩ ∧ x = .cp ⟨p, b⟩ := Iff.rfl

lemma mem_addCand (r : Reg P) (v x : Val P M) (p' q' : P) :
    x ∈ s.addCand r v p' q' ↔
      x ∈ s.cand p' q' ∨ ((s.pc p' q').rd q' (s.key p' q') = some r ∧ x = v) := by
  unfold addCand; split_ifs with h <;> simp [h, or_comm]

/-- Candidate sets after thread `(p,q)` invokes the operation designated by `c`. -/
lemma mem_go_cand (x : Val P M) (p' q' : P) :
    x ∈ (s.go p q c).cand p' q' ↔
      if p' = p ∧ q' = q then
        (∀ r, c.rd q (s.key p q) = some r → x = s.mem r ∨
            x ∈ ({ s with pc := upd2 s.pc p q c } : St P M).pendW r) ∧
        (c.rd q (s.key p q) = none → x ∈ s.cand p q)
      else x ∈ s.cand p' q' ∨
        ∃ r v, c.wr p q (s.key p q) = some (r, v) ∧ (s.pc p' q').rd q' (s.key p' q') = some r ∧
          x = v := by
  unfold go
  rcases hrd : c.rd q (s.key p q) with _ | r <;> rcases hwr : c.wr p q (s.key p q) with _ | ⟨r', v⟩
  · cases c <;> simp_all [PC.rd, PC.wr]
  · by_cases h : p' = p ∧ q' = q
    · obtain ⟨rfl, rfl⟩ := h
      simp only [mem_addCand, key, upd2_apply, and_self, ite_true]
      cases c <;> simp_all [PC.rd, PC.wr, key]
    · simp only [mem_addCand, key, upd2_apply, h, ite_false]
      simp only [key] at hwr
      simp [eq_comm, and_comm]
  · by_cases h : p' = p ∧ q' = q
    · obtain ⟨rfl, rfl⟩ := h; simp [key]
    · simp only [upd2_apply, h, ite_false]
      cases c <;> simp_all [PC.rd, PC.wr, key]
  · cases c <;> simp_all [PC.rd, PC.wr]

end St

end Podc.RDMAAgreement.RB
