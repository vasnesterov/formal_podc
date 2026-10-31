import Mathlib

/-!
# The system model of Section 2 (highly available replicated objects)

Attiya, Burckhardt, Gotsman, Morrison, Yang, Zawirski. *Specification and space complexity of
collaborative text editing.* TCS 855 (2021); PODC 2016.

* A **protocol** (`Protocol`) gives every replica `r` a deterministic state machine whose state is a
  pair `σ = (q, buf)` of an internal state `q : Q` and a send buffer `buf : Option M` (`none` = `⊥`).
  User operations `do(op, v)` are always enabled; their response `v = resp r σ op` is a function of
  the whole replica state `σ` (as in PODC 2016; the TCS version additionally requires it to depend on
  `q` only), and they may change the whole state (`doStep`). A `send` is enabled iff the buffer is
  non-empty; it broadcasts the buffered message, empties the buffer and moves to the internal state
  `sendStep r σ`, an arbitrary function of the state (PODC 2016: `Δ((q, m), send(m)) = (q′, ⊥)` for
  some `q′`). A `receive` is always enabled (`recvStep`). One common type `Q` serves all replicas (a
  family `Q r` embeds into a sigma type), so nothing is lost.
* An **execution** is a list of actions. Messages are instrumented with unique ids: a receive
  names the *position* of the send event whose message it delivers (`Act.recv r src`). Broadcast
  goes to every replica, including the sender.
* `exec P α` replays `α` from the initial configuration; `WF P α` is well-formedness: every send is
  enabled, every receive refers to an earlier send.
* `HB α` is Lamport's happens-before on positions (replica order, send → receive, transitivity);
  `CausalBroadcast`, `CausalAtomic` are Definitions 2 and 3.

-- CSLib candidate: the whole file is independent of lists (generic replicated objects).
-/

namespace Podc.CollaborativeListSpec

/-- A protocol (Section 2): one deterministic state machine per replica. -/
structure Protocol (Rep Op Val Q M : Type) where
  /-- Initial internal state `q₀` of each replica (the initial buffer is empty). -/
  init : Rep → Q
  /-- Response of `do(op, _)`: a function of the whole replica state `(q, buf)`. -/
  resp : Rep → Q × Option M → Op → Val
  /-- State change of `do(op, _)`. -/
  doStep : Rep → Q × Option M → Op → Q × Option M
  /-- New internal state after `send(m)` from state `(q, some m)`; the buffer becomes `⊥`. -/
  sendStep : Rep → Q × Option M → Q
  /-- State change of `receive(m)`. -/
  recvStep : Rep → Q × Option M → M → Q × Option M

/-- Actions (events) of an execution. `recv r src` delivers at `r` the message of the send event
at position `src`. -/
inductive Act (Rep Op : Type) where
  | doOp (r : Rep) (op : Op)
  | send (r : Rep)
  | recv (r : Rep) (src : ℕ)
  deriving DecidableEq

namespace Act

variable {Rep Op : Type}

/-- The replica at which an action occurs. -/
def rep : Act Rep Op → Rep
  | doOp r _ => r
  | send r => r
  | recv r _ => r

/-- The send position named by a receive. -/
def src? : Act Rep Op → Option ℕ
  | recv _ s => some s
  | _ => none

@[simp] theorem rep_doOp (r : Rep) (op : Op) : (doOp r op).rep = r := rfl
@[simp] theorem rep_send (r : Rep) : (send r : Act Rep Op).rep = r := rfl
@[simp] theorem rep_recv (r : Rep) (s : ℕ) : (recv r s : Act Rep Op).rep = r := rfl
@[simp] theorem src?_doOp (r : Rep) (op : Op) : (doOp r op).src? = none := rfl
@[simp] theorem src?_send (r : Rep) : (send r : Act Rep Op).src? = none := rfl
@[simp] theorem src?_recv (r : Rep) (s : ℕ) : (recv r s : Act Rep Op).src? = some s := rfl

end Act

/-- A global configuration: the state of every replica and the payload of every event so far
(`some m` for a send of `m`, `none` otherwise). -/
structure Cfg (Rep Q M : Type) where
  st : Rep → Q × Option M
  sent : List (Option M)

variable {Rep Op Val Q M : Type} [DecidableEq Rep] (P : Protocol Rep Op Val Q M)

/-- Enabledness of the action at position `n` (Section 2): sends need a pending message, receives
refer to an earlier send. -/
def Enabled {Rep Op Q M : Type} (α : List (Act Rep Op)) (c : Cfg Rep Q M) (n : ℕ) :
    Act Rep Op → Prop
  | .doOp _ _ => True
  | .send r => (c.st r).2.isSome
  | .recv _ src => src < n ∧ ∃ r', α[src]? = some (.send r')

namespace Protocol

/-- The initial configuration. -/
def init₀ : Cfg Rep Q M := ⟨fun r => (P.init r, none), []⟩

/-- One step of the global transition system. -/
def step (c : Cfg Rep Q M) : Act Rep Op → Cfg Rep Q M
  | .doOp r op => ⟨Function.update c.st r (P.doStep r (c.st r) op), c.sent ++ [none]⟩
  | .send r => ⟨Function.update c.st r (P.sendStep r (c.st r), none), c.sent ++ [(c.st r).2]⟩
  | .recv r src =>
      ⟨match (c.sent[src]?).join with
        | some m => Function.update c.st r (P.recvStep r (c.st r) m)
        | none => c.st, c.sent ++ [none]⟩

/-- Replay of an execution. -/
def exec (α : List (Act Rep Op)) : Cfg Rep Q M := α.foldl P.step P.init₀

/-- The state of replica `r` just before position `p` of `α`. -/
def stBefore (α : List (Act Rep Op)) (p : ℕ) (r : Rep) : Q × Option M :=
  (P.exec (α.take p)).st r

/-- Well-formed executions. -/
def WF (α : List (Act Rep Op)) : Prop :=
  ∀ p (hp : p < α.length), Enabled α (P.exec (α.take p)) p α[p]

/-- Replica `r` has a message pending after the event at position `p`. -/
def Pending (α : List (Act Rep Op)) (p : ℕ) (r : Rep) : Prop :=
  p < α.length ∧ ((P.exec (α.take (p + 1))).st r).2.isSome

/-- The history of `do` events of an execution, indexed by position: replica, operation and
response. -/
def hist (α : List (Act Rep Op)) (p : ℕ) : Option (Rep × Op × Val) :=
  match α[p]? with
  | some (.doOp r op) => some (r, op, P.resp r (P.stBefore α p r) op)
  | _ => none

end Protocol

/-- The event at position `p` is a `do` event. -/
def IsDo {Rep Op : Type} (α : List (Act Rep Op)) (p : ℕ) : Prop :=
  ∃ r op, α[p]? = some (.doOp r op)

/-- The event at position `p` is a send. -/
def IsSend {Rep Op : Type} (α : List (Act Rep Op)) (p : ℕ) : Prop :=
  ∃ r, α[p]? = some (.send r)

/-- Immediate happens-before: replica order or message delivery. -/
def Imm {Rep Op : Type} (α : List (Act Rep Op)) (i j : ℕ) : Prop :=
  i < j ∧ ∃ a b, α[i]? = some a ∧ α[j]? = some b ∧ (a.rep = b.rep ∨ b.src? = some i)

/-- Happens-before (Section 2), on positions. -/
def HB {Rep Op : Type} (α : List (Act Rep Op)) : ℕ → ℕ → Prop :=
  Relation.TransGen (Imm α)

/-- Definition 2 (causal broadcast). -/
def CausalBroadcast {Rep Op : Type} (α : List (Act Rep Op)) : Prop :=
  ∀ (s s' : ℕ) (r : Rep) (q : ℕ), IsSend α s → IsSend α s' → HB α s s' → α[q]? = some (Act.recv r s') →
    ∃ q' < q, α[q']? = some (Act.recv r s)

/-- Definition 3 (causal atomic broadcast). -/
def CausalAtomic {Rep Op : Type} (α : List (Act Rep Op)) : Prop :=
  CausalBroadcast α ∧
  (∀ (q q' : ℕ) (r : Rep) (s : ℕ), α[q]? = some (Act.recv r s) → α[q']? = some (Act.recv r s) → q = q') ∧
  (∀ (r r' : Rep) (s s' q₁ q₂ q₃ : ℕ), α[q₁]? = some (Act.recv r s) → α[q₂]? = some (Act.recv r s') → q₁ < q₂ →
    α[q₃]? = some (Act.recv r' s') → ∃ q₄ < q₃, α[q₄]? = some (Act.recv r' s))

theorem CausalAtomic.causal {Rep Op : Type} {α : List (Act Rep Op)} (h : CausalAtomic α) :
    CausalBroadcast α := h.1

theorem List.IsPrefix.getElem?_of_lt {α : Type} {l₁ l₂ : List α} (h : l₁ <+: l₂) {i : ℕ}
    (hi : i < l₁.length) : l₁[i]? = l₂[i]? := by
  obtain ⟨t, rfl⟩ := h; rw [List.getElem?_append_left hi]

theorem List.IsPrefix.getElem?_of_some {α : Type} {l₁ l₂ : List α} (h : l₁ <+: l₂) {i : ℕ}
    {a : α} (hi : l₁[i]? = some a) : l₂[i]? = some a := by
  obtain ⟨t, rfl⟩ := h
  have : i < l₁.length := by
    by_contra hc; rw [List.getElem?_eq_none (by omega)] at hi; cases hi
  rw [List.getElem?_append_left this, hi]

/-! ### Basic facts on replay -/

namespace Protocol

variable {P}

@[simp] theorem exec_nil : P.exec ([] : List (Act Rep Op)) = P.init₀ := rfl

theorem exec_append (α β : List (Act Rep Op)) :
    P.exec (α ++ β) = β.foldl P.step (P.exec α) := by
  simp [exec, List.foldl_append]

@[simp] theorem exec_concat (α : List (Act Rep Op)) (a : Act Rep Op) :
    P.exec (α ++ [a]) = P.step (P.exec α) a := by
  simp [exec_append]

@[simp] theorem step_sent_length (c : Cfg Rep Q M) (a : Act Rep Op) :
    (P.step c a).sent.length = c.sent.length + 1 := by
  cases a <;> simp [step]

@[simp] theorem exec_sent_length (α : List (Act Rep Op)) :
    (P.exec α).sent.length = α.length := by
  induction α using List.reverseRecOn with
  | nil => rfl
  | append_singleton α a ih => simp [ih]

theorem step_sent_prefix (c : Cfg Rep Q M) (a : Act Rep Op) : c.sent <+: (P.step c a).sent := by
  cases a <;> simp [step]

theorem exec_sent_prefix (α β : List (Act Rep Op)) :
    (P.exec α).sent <+: (P.exec (α ++ β)).sent := by
  induction β using List.reverseRecOn with
  | nil => simp
  | append_singleton β a ih =>
    rw [← List.append_assoc, exec_concat]
    exact ih.trans (step_sent_prefix _ _)

/-- The payload recorded at position `p` only depends on the prefix up to `p`. -/
theorem exec_sent_getElem?_take (α : List (Act Rep Op)) {p n : ℕ} (h : p < n) :
    (P.exec (α.take n)).sent[p]? = (P.exec α).sent[p]? := by
  have := exec_sent_prefix (P := P) (α.take n) (α.drop n)
  rw [List.take_append_drop] at this
  rcases le_or_gt α.length n with hn | hn
  · rw [List.take_of_length_le hn]
  · have hl : p < (P.exec (α.take n)).sent.length := by simp; omega
    rw [List.IsPrefix.getElem?_of_lt this hl]

/-- The payload of a send event: the buffer of the sender just before it. -/
theorem exec_sent_send (α : List (Act Rep Op)) {p : ℕ} {r : Rep}
    (h : α[p]? = some (.send r)) :
    (P.exec α).sent[p]? = some (P.stBefore α p r).2 := by
  have hp : p < α.length := by
    by_contra hc; rw [List.getElem?_eq_none (by omega)] at h; cases h
  rw [← exec_sent_getElem?_take α (show p < p + 1 by omega)]
  have ht : α.take (p + 1) = α.take p ++ [.send r] := by
    rw [List.take_succ, h]; rfl
  rw [ht, exec_concat]
  simp [step, stBefore, List.getElem?_append_right, hp.le]

theorem exec_sent_not_send (α : List (Act Rep Op)) {p : ℕ}
    (h : ∀ r, α[p]? ≠ some (.send r)) : (P.exec α).sent[p]? = none ∨ (P.exec α).sent[p]? = some none := by
  rcases lt_or_ge p α.length with hp | hp
  · right
    rw [← exec_sent_getElem?_take α (show p < p + 1 by omega)]
    have ht : α.take (p + 1) = α.take p ++ [α[p]] := by
      rw [List.take_succ, List.getElem?_eq_getElem hp]; rfl
    rw [ht, exec_concat]
    have hlen : (P.exec (α.take p)).sent.length = p := by simp; omega
    have h' := h
    rw [List.getElem?_eq_getElem hp] at h'
    rcases hα : α[p] with ⟨r, op⟩ | r | ⟨r, s⟩
    · simp [step, List.getElem?_append_right, hlen]
    · exact absurd (by rw [hα]) (h' r)
    · simp [step, List.getElem?_append_right, hlen]
  · left; simp; omega

/-- The payload appended by a step. -/
def payload (c : Cfg Rep Q M) : Act Rep Op → Option M
  | .send r => (c.st r).2
  | _ => none

theorem step_sent (c : Cfg Rep Q M) (a : Act Rep Op) :
    (P.step c a).sent = c.sent ++ [payload c a] := by
  cases a <;> rfl

/-- Replay is a congruence: from configurations with the same replica states that agree on the
payloads of the messages the remaining actions receive, the same actions lead to the same replica
states. -/
theorem foldl_step_congr : ∀ (β : List (Act Rep Op)) (G : Set ℕ) (c c' : Cfg Rep Q M),
    c.st = c'.st → c.sent.length = c'.sent.length → (∀ s ∈ G, c.sent[s]? = c'.sent[s]?) →
    (∀ a ∈ β, ∀ s, a.src? = some s → s ∈ G ∨ c.sent.length ≤ s) →
    (β.foldl P.step c).st = (β.foldl P.step c').st
  | [], _, _, _, hst, _, _, _ => hst
  | a :: β, G, c, c', hst, hlen, hG, hβ => by
    have hsent : ∀ s, s ∈ G ∨ c.sent.length ≤ s → c.sent[s]? = c'.sent[s]? := by
      rintro s (hs | hs)
      · exact hG s hs
      · rw [List.getElem?_eq_none hs, List.getElem?_eq_none (by omega)]
    have hst' : (P.step c a).st = (P.step c' a).st := by
      cases a with
      | doOp r op => simp [step, hst]
      | send r => simp [step, hst]
      | recv r s =>
        simp only [step]
        rw [hsent s (hβ _ List.mem_cons_self s rfl), hst]
    have hpay : payload c a = payload c' a := by cases a <;> simp [payload, hst]
    refine foldl_step_congr β {s | s ∈ G ∨ c.sent.length ≤ s} (P.step c a) (P.step c' a) hst'
      (by simp [hlen]) ?_ ?_
    · rintro s hs
      rw [step_sent, step_sent]
      rcases lt_or_ge s c.sent.length with h | h
      · rw [List.getElem?_append_left h, List.getElem?_append_left (by omega)]
        exact hsent s hs
      · rw [List.getElem?_append_right h, List.getElem?_append_right (by omega), hlen, hpay]
    · intro b hb s hs
      rcases hβ b (List.mem_cons_of_mem _ hb) s hs with h | h
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr h)

/-- A replica that does not act keeps its initial state. -/
theorem exec_st_of_not_acting (α : List (Act Rep Op)) (r : Rep) (h : ∀ a ∈ α, a.rep ≠ r) :
    (P.exec α).st r = (P.init r, none) := by
  induction α using List.reverseRecOn with
  | nil => rfl
  | append_singleton α a ih =>
    rw [exec_concat]
    have ha := h a (by simp)
    have ih := ih (fun b hb => h b (by simp [hb]))
    cases a with
    | doOp r' op => simp at ha; simp [step, Function.update_of_ne (Ne.symm ha), ih]
    | send r' => simp at ha; simp [step, Function.update_of_ne (Ne.symm ha), ih]
    | recv r' s =>
      simp at ha; simp only [step]
      cases hx : ((P.exec α).sent[s]?).join <;> simp [Function.update_of_ne (Ne.symm ha), ih]

end Protocol

/-! ### Happens-before -/

section HB

variable {Rep Op : Type} {α β : List (Act Rep Op)}

theorem Imm.lt {i j : ℕ} (h : Imm α i j) : i < j := h.1

theorem Imm.lt_length {i j : ℕ} (h : Imm α i j) : j < α.length := by
  obtain ⟨-, a, b, -, hb, -⟩ := h
  by_contra hc; rw [List.getElem?_eq_none (by omega)] at hb; cases hb

theorem HB.lt {i j : ℕ} (h : HB α i j) : i < j := by
  induction h with
  | single h => exact h.lt
  | tail _ h ih => exact ih.trans h.lt

theorem HB.lt_length {i j : ℕ} (h : HB α i j) : j < α.length := by
  cases h with
  | single h => exact h.lt_length
  | tail _ h => exact h.lt_length

theorem HB.irrefl (i : ℕ) : ¬ HB α i i := fun h => lt_irrefl _ h.lt

theorem HB.trans {i j k : ℕ} (h₁ : HB α i j) (h₂ : HB α j k) : HB α i k :=
  Relation.TransGen.trans h₁ h₂

/-- Replica order is part of happens-before. -/
theorem HB.of_rep {i j : ℕ} {a b : Act Rep Op} (hij : i < j) (ha : α[i]? = some a)
    (hb : α[j]? = some b) (hr : a.rep = b.rep) : HB α i j :=
  Relation.TransGen.single ⟨hij, a, b, ha, hb, Or.inl hr⟩

/-- Message delivery is part of happens-before. -/
theorem HB.of_recv {i j : ℕ} {a : Act Rep Op} {r : Rep} (hij : i < j) (ha : α[i]? = some a)
    (hb : α[j]? = some (Act.recv r i)) : HB α i j :=
  Relation.TransGen.single ⟨hij, a, _, ha, hb, Or.inr rfl⟩

/-- Upper bounds on happens-before through downward closed sets. -/
theorem HB.mem_of_closed {S : Set ℕ} (hS : ∀ i j, Imm α i j → j ∈ S → i ∈ S) {i j : ℕ}
    (h : HB α i j) (hj : j ∈ S) : i ∈ S := by
  induction h with
  | single h => exact hS _ _ h hj
  | tail _ h ih => exact ih (hS _ _ h hj)

theorem Imm.of_prefix (hαβ : α <+: β) {i j : ℕ} (h : Imm α i j) : Imm β i j := by
  obtain ⟨hij, a, b, ha, hb, h⟩ := h
  exact ⟨hij, a, b, List.IsPrefix.getElem?_of_some hαβ ha,
    List.IsPrefix.getElem?_of_some hαβ hb, h⟩

theorem HB.of_prefix (hαβ : α <+: β) {i j : ℕ} (h : HB α i j) : HB β i j :=
  Relation.TransGen.mono (fun _ _ (h : Imm α _ _) => h.of_prefix hαβ) _ _ h

theorem HB.to_prefix (hαβ : α <+: β) {i j : ℕ} (h : HB β i j) (hj : j < α.length) :
    HB α i j := by
  have himm : ∀ i j, Imm β i j → j < α.length → Imm α i j := by
    rintro i j ⟨hij, a, b, ha, hb, h⟩ hj
    refine ⟨hij, a, b, ?_, ?_, h⟩
    · rw [← ha]; exact List.IsPrefix.getElem?_of_lt hαβ (by omega)
    · rw [← hb]; exact List.IsPrefix.getElem?_of_lt hαβ hj
  induction h with
  | single h => exact Relation.TransGen.single (himm _ _ h hj)
  | tail _ h ih => exact Relation.TransGen.tail (ih (by have := h.lt; omega)) (himm _ _ h hj)

theorem HB.prefix_iff (hαβ : α <+: β) {i j : ℕ} (hj : j < α.length) :
    HB α i j ↔ HB β i j :=
  ⟨HB.of_prefix hαβ, fun h => h.to_prefix hαβ hj⟩

/-- The last step into `j`. -/
theorem HB.cases_last {i j : ℕ} (h : HB α i j) : ∃ k, (i = k ∨ HB α i k) ∧ Imm α k j := by
  rcases Relation.TransGen.tail'_iff.1 h with ⟨k, hk, hkj⟩
  rcases Relation.ReflTransGen.cases_tail hk with rfl | hk'
  · exact ⟨_, Or.inl rfl, hkj⟩
  · exact ⟨k, Or.inr (Relation.TransGen.tail'_iff.2 hk'), hkj⟩

/-- Happens-before into a non-receive event goes through an earlier event of the same replica. -/
theorem HB.of_not_recv {i j : ℕ} {b : Act Rep Op} (hb : α[j]? = some b) (hnr : b.src? = none)
    (h : HB α i j) : ∃ k a, k < j ∧ α[k]? = some a ∧ a.rep = b.rep ∧ (i = k ∨ HB α i k) := by
  obtain ⟨k, hik, hkj, a, b', ha, hb', hab⟩ := h.cases_last
  rw [hb] at hb'; cases hb'
  rcases hab with hab | hab
  · exact ⟨k, a, hkj, ha, hab, hik⟩
  · rw [hnr] at hab; cases hab

end HB

/-- Causal atomic broadcast is preserved by prefixes. -/
theorem CausalAtomic.take {Rep Op : Type} {α : List (Act Rep Op)} (h : CausalAtomic α) (n : ℕ) :
    CausalAtomic (α.take n) := by
  obtain ⟨hc, hd, ho⟩ := h
  have hp : α.take n <+: α := List.take_prefix n α
  have get : ∀ {q : ℕ} {a : Act Rep Op}, (α.take n)[q]? = some a → q < n ∧ α[q]? = some a := by
    intro q a hq
    rw [List.getElem?_take] at hq
    split_ifs at hq with h; exact ⟨h, hq⟩
  have put : ∀ {q : ℕ} {a : Act Rep Op}, q < n → α[q]? = some a → (α.take n)[q]? = some a := by
    intro q a h hq; rw [List.getElem?_take, if_pos h, hq]
  refine ⟨?_, ?_, ?_⟩
  · rintro s s' r q ⟨r₁, h₁⟩ ⟨r₂, h₂⟩ hss hq
    obtain ⟨hqn, hq⟩ := get hq
    obtain ⟨q', hq'q, hq'⟩ := hc s s' r q ⟨r₁, (get h₁).2⟩ ⟨r₂, (get h₂).2⟩ (hss.of_prefix hp) hq
    exact ⟨q', hq'q, put (by omega) hq'⟩
  · intro q q' r s h₁ h₂
    exact hd q q' r s (get h₁).2 (get h₂).2
  · intro r r' s s' q₁ q₂ q₃ h₁ h₂ h12 h₃
    obtain ⟨hq₃, h₃⟩ := get h₃
    obtain ⟨q₄, h43, h₄⟩ := ho r r' s s' q₁ q₂ q₃ (get h₁).2 (get h₂).2 h12 h₃
    exact ⟨q₄, h43, put (by omega) h₄⟩

end Podc.CollaborativeListSpec
