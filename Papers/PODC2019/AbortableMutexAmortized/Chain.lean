import Mathlib

/-!
# Pointer chains

A list `Q = [q₁, …, q_k]` of processes forms a *chain from the node `a`* (for the maps
`pr` = `pred` and `my` = `mynode`) if `pr q₁ = a` and `pr q_{i+1} = my q_i`. This is the paper's
queue structure (invariants `I1`–`I4`): `a₀ = a`, `a_i = my q_i`, `pred q_i = a_{i-1}`, and the
chain ends at `lastN my a Q = a_k` (= `tail`).
-/

-- CSLib candidate (generic pointer chains for queue locks)
namespace Podc.AbortableMutexAmortized

variable {α β : Type*}

/-- `Q` is a chain starting at the node `a`: `pr q₁ = a`, `pr q_{i+1} = my q_i`. -/
def Chain (pr my : α → β) : β → List α → Prop
  | _, [] => True
  | a, q :: Q => pr q = a ∧ Chain pr my (my q) Q

/-- The last node of the chain (`a` if the chain is empty, else `my q_k`). -/
def lastN (my : α → β) : β → List α → β
  | a, [] => a
  | _, q :: Q => lastN my (my q) Q

variable {pr my : α → β}

@[simp] theorem chain_nil (a : β) : Chain pr my a [] := trivial

@[simp] theorem chain_cons (a : β) (q : α) (Q : List α) :
    Chain pr my a (q :: Q) ↔ pr q = a ∧ Chain pr my (my q) Q := Iff.rfl

@[simp] theorem lastN_nil (a : β) : lastN my a [] = a := rfl

@[simp] theorem lastN_cons (a : β) (q : α) (Q : List α) :
    lastN my a (q :: Q) = lastN my (my q) Q := rfl

theorem chain_append (a : β) (Q R : List α) :
    Chain pr my a (Q ++ R) ↔ Chain pr my a Q ∧ Chain pr my (lastN my a Q) R := by
  induction Q generalizing a with
  | nil => simp
  | cons q Q ih => simp [ih, and_assoc]

theorem lastN_append (a : β) (Q R : List α) :
    lastN my a (Q ++ R) = lastN my (lastN my a Q) R := by
  induction Q generalizing a with
  | nil => rfl
  | cons q Q ih => simp [ih]

theorem lastN_concat (a : β) (Q : List α) (x : α) : lastN my a (Q ++ [x]) = my x := by
  rw [lastN_append]; rfl

theorem lastN_mem (a : β) (Q : List α) : lastN my a Q = a ∨ ∃ x ∈ Q, lastN my a Q = my x := by
  induction Q generalizing a with
  | nil => simp
  | cons q Q ih =>
    rcases ih (my q) with h | ⟨x, hx, h⟩
    · exact Or.inr ⟨q, by simp, by simpa using h⟩
    · exact Or.inr ⟨x, by simp [hx], by simpa using h⟩

theorem chain_congr {pr' my' : α → β} {a : β} {Q : List α}
    (h : ∀ q ∈ Q, pr q = pr' q ∧ my q = my' q) : Chain pr my a Q ↔ Chain pr' my' a Q := by
  induction Q generalizing a with
  | nil => simp
  | cons q Q ih =>
    have hq := h q (by simp)
    simp only [chain_cons, hq.1, hq.2]
    rw [ih (fun r hr => h r (by simp [hr]))]

theorem lastN_congr {my' : α → β} {a : β} {Q : List α} (h : ∀ q ∈ Q, my q = my' q) :
    lastN my a Q = lastN my' a Q := by
  induction Q generalizing a with
  | nil => rfl
  | cons q Q ih =>
    simp only [lastN_cons, h q (by simp)]
    exact ih (fun r hr => h r (by simp [hr]))

/-- The predecessor node of a chain member is the start or a member's node. -/
theorem Chain.pred_mem {a : β} {Q : List α} (h : Chain pr my a Q) {y : α} (hy : y ∈ Q) :
    pr y = a ∨ ∃ x ∈ Q, pr y = my x := by
  induction Q generalizing a with
  | nil => simp at hy
  | cons q Q ih =>
    rcases List.mem_cons.1 hy with rfl | hy
    · exact Or.inl h.1
    · rcases ih h.2 hy with h' | ⟨x, hx, h'⟩
      · exact Or.inr ⟨q, by simp, h'⟩
      · exact Or.inr ⟨x, by simp [hx], h'⟩

/-- Standing assumptions on a chain: no repetitions, `my` injective, the start is no member's
node. -/
structure ChainOK (pr my : α → β) (a : β) (Q : List α) : Prop where
  chain : Chain pr my a Q
  nodup : Q.Nodup
  inj : Function.Injective my
  start : ∀ x ∈ Q, my x ≠ a

namespace ChainOK

variable {a : β} {Q : List α}

theorem tail {q : α} (h : ChainOK pr my a (q :: Q)) : ChainOK pr my (my q) Q where
  chain := h.chain.2
  nodup := (List.nodup_cons.1 h.nodup).2
  inj := h.inj
  start := fun x hx hx' => (List.nodup_cons.1 h.nodup).1 (by rw [← h.inj hx']; exact hx)

/-- Distinct members have distinct predecessor nodes. -/
theorem pred_inj (h : ChainOK pr my a Q) {y y' : α} (hy : y ∈ Q) (hy' : y' ∈ Q)
    (e : pr y = pr y') : y = y' := by
  induction Q generalizing a with
  | nil => simp at hy
  | cons q Q ih =>
    have h1 : pr q = a := h.chain.1
    have hne : ∀ z ∈ Q, pr z ≠ a := by
      intro z hz e'
      rcases h.chain.2.pred_mem hz with h2 | ⟨x, hx, h2⟩
      · exact h.start q (by simp) (h2 ▸ e')
      · exact h.start x (by simp [hx]) (h2 ▸ e')
    rcases List.mem_cons.1 hy with h2 | h2 <;> rcases List.mem_cons.1 hy' with h3 | h3
    · rw [h2, h3]
    · subst h2; exact absurd (e ▸ h1) (hne y' h3)
    · subst h3; exact absurd (e ▸ h1) (hne y h2)
    · exact ih h.tail h2 h3

/-- No member's predecessor node is the last node. -/
theorem pred_ne_last (h : ChainOK pr my a Q) {y : α} (hy : y ∈ Q) : pr y ≠ lastN my a Q := by
  induction Q generalizing a with
  | nil => simp at hy
  | cons q Q ih =>
    rcases List.mem_cons.1 hy with rfl | hy
    · rw [h.chain.1, lastN_cons]
      rcases lastN_mem (my := my) (my y) Q with e | ⟨x, hx, e⟩
      · rw [e]; exact (h.start y (by simp)).symm
      · rw [e]; exact (h.start x (by simp [hx])).symm
    · exact ih h.tail hy

/-- The start node is not a member's node, and no member's node is a member's predecessor
unless they are adjacent: if `pr y = my x` then `x` immediately precedes `y`. -/
theorem adj (h : ChainOK pr my a Q) {x y : α} (hx : x ∈ Q) (hy : y ∈ Q) (e : pr y = my x) :
    ∃ L R, Q = L ++ x :: y :: R := by
  induction Q generalizing a with
  | nil => simp at hy
  | cons q Q ih =>
    rcases List.mem_cons.1 hy with h2 | h2
    · subst h2; exact absurd (h.chain.1 ▸ e).symm (h.start x hx)
    rcases List.mem_cons.1 hx with h3 | h3
    · subst h3
      cases Q with
      | nil => simp at h2
      | cons y' R =>
        have := h.tail.pred_inj h2 (by simp) (e.trans h.chain.2.1.symm)
        subst this
        exact ⟨[], R, rfl⟩
    · obtain ⟨L, R, rfl⟩ := ih h.tail h3 h2
      exact ⟨q :: L, R, rfl⟩

/-- The member whose predecessor is the start node is the head. -/
theorem head (h : ChainOK pr my a Q) {y : α} (hy : y ∈ Q) (e : pr y = a) : ∃ R, Q = y :: R := by
  cases Q with
  | nil => simp at hy
  | cons q R =>
    have := h.pred_inj hy (by simp) (e.trans h.chain.1.symm)
    subst this; exact ⟨R, rfl⟩

/-- A member that is not last has a successor. -/
theorem succ_exists (h : ChainOK pr my a Q) {x : α} (hx : x ∈ Q) (hl : my x ≠ lastN my a Q) :
    ∃ y ∈ Q, pr y = my x := by
  induction Q generalizing a with
  | nil => simp at hx
  | cons q Q ih =>
    rcases List.mem_cons.1 hx with rfl | hx
    · cases Q with
      | nil => simp at hl
      | cons y R => exact ⟨y, by simp, h.chain.2.1⟩
    · obtain ⟨y, hy, e⟩ := ih h.tail hx hl
      exact ⟨y, by simp [hy], e⟩

/-- The last member's node is the last node. -/
theorem last_of_mem (h : ChainOK pr my a Q) {x : α} (hx : x ∈ Q)
    (hl : ∀ y ∈ Q, pr y ≠ my x) : my x = lastN my a Q := by
  by_contra hne
  obtain ⟨y, hy, e⟩ := h.succ_exists hx hne
  exact hl y hy e

/-- A chain is determined by its start and its set of members. -/
theorem unique (h : ChainOK pr my a Q) {Q' : List α} (h' : ChainOK pr my a Q')
    (hmem : ∀ x, x ∈ Q ↔ x ∈ Q') : Q = Q' := by
  induction Q generalizing a Q' with
  | nil =>
    cases Q' with
    | nil => rfl
    | cons q' R' => exact absurd ((hmem q').2 (by simp)) (by simp)
  | cons q Q ih =>
    cases Q' with
    | nil => exact absurd ((hmem q).1 (by simp)) (by simp)
    | cons q' R' =>
      have hq : q = q' := h'.pred_inj ((hmem q).1 (by simp)) (by simp)
        (h.chain.1.trans h'.chain.1.symm)
      subst hq
      have := ih h.tail (h'.tail) (fun x => by
        constructor
        · intro hx
          have hx' := (hmem x).1 (by simp [hx])
          rcases List.mem_cons.1 hx' with rfl | hx'
          · exact absurd hx (List.nodup_cons.1 h.nodup).1
          · exact hx'
        · intro hx
          have hx' := (hmem x).2 (by simp [hx])
          rcases List.mem_cons.1 hx' with rfl | hx'
          · exact absurd hx (List.nodup_cons.1 h'.nodup).1
          · exact hx')
      rw [this]

end ChainOK

end Podc.AbortableMutexAmortized
