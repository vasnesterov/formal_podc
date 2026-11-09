import Mathlib

-- CSLib candidate: Cslib/Computability/Distributed/MessagePassing/Causality/Basic.lean

/-!
# Executions of asynchronous message-passing systems and Lamport's happened-before

An execution of an asynchronous message-passing system is recorded as the list of its events in
real-time order (`Exec P`, processes `P`); an event is identified by its position in the list.
An event is a send (`send p q`: `p` sends one message to `q`), a receive (`recv p m`: `p`
receives the message sent at position `m`) or a local computation step (`comp p`).

* `Exec.WF`: every receive refers to an earlier send addressed to the receiver, and each message
  is received at most once. Channels are reliable but **not** FIFO; message delays are arbitrary.
* `Exec.OnGraph G`: every message is sent along an edge of the communication graph `G`.
* `Exec.prev j`: the previous event of the process of `j`; `Exec.Step` = immediate
  predecessor at the same process or send → receive; `Exec.HB` = its transitive closure, Lamport's
  happened-before relation `→`.
* `Exec.idx i`: the (1-based) index of event `i` at its process (`index(e)` of the papers).
-/

namespace Cslib.Causality

/-- An event of an asynchronous message-passing execution. -/
inductive Act (P : Type*) where
  /-- `p` sends one message to `q` (unicast). -/
  | send (p q : P)
  /-- `p` receives the message sent at position `m` of the execution. -/
  | recv (p : P) (m : ℕ)
  /-- A local computation step of `p`. -/
  | comp (p : P)
  deriving DecidableEq

namespace Act

variable {P : Type*}

/-- The process at which the event takes place. -/
def proc : Act P → P
  | send p _ => p
  | recv p _ => p
  | comp p => p

@[simp] lemma proc_send (p q : P) : (send p q).proc = p := rfl
@[simp] lemma proc_recv (p : P) (m : ℕ) : (recv p m).proc = p := rfl
@[simp] lemma proc_comp (p : P) : (comp p).proc = p := rfl

end Act

/-- An execution: its events in real-time order. Event `i` is the `i`-th entry. -/
abbrev Exec (P : Type*) := List (Act P)

namespace Exec

variable {P : Type*} [DecidableEq P] (ex : Exec P)

/-- The process of event `i` (`none` if there is no such event). -/
def procAt (i : ℕ) : Option P := ex[i]?.map Act.proc

/-- The last event of process `p` strictly before position `k`. -/
def lastBefore (p : P) : ℕ → Option ℕ
  | 0 => none
  | k + 1 => if ex.procAt k = some p then some k else lastBefore p k

/-- The previous event at the process of event `j`. -/
def prev (j : ℕ) : Option ℕ :=
  match ex[j]? with
  | none => none
  | some a => ex.lastBefore a.proc j

/-- Immediate causal predecessor: the previous event at the same process, or the send event of
a receive. -/
inductive Step : ℕ → ℕ → Prop
  | po {i j : ℕ} : ex.prev j = some i → Step i j
  | msg {i j : ℕ} {p : P} : ex[j]? = some (.recv p i) → Step i j

/-- Lamport's happened-before relation `→`. -/
def HB : ℕ → ℕ → Prop := Relation.TransGen ex.Step

/-- Reflexive happened-before (`e = f ∨ e → f`). -/
def HBeq (i j : ℕ) : Prop := i = j ∨ ex.HB i j

/-- Well-formedness: every receive refers to an earlier send addressed to the receiver, and
every message is received at most once. -/
structure WF : Prop where
  recv_lt : ∀ {j : ℕ} {p : P} {m : ℕ}, ex[j]? = some (.recv p m) → m < j
  recv_send : ∀ {j : ℕ} {p : P} {m : ℕ}, ex[j]? = some (.recv p m) → ∃ q, ex[m]? = some (.send q p)
  recv_unique : ∀ {j j' : ℕ} {p p' : P} {m : ℕ}, ex[j]? = some (.recv p m) →
    ex[j']? = some (.recv p' m) → j = j'

/-- Every message is sent along an edge of the communication graph `G`. -/
def OnGraph (G : SimpleGraph P) : Prop :=
  ∀ {j : ℕ} {p q : P}, ex[j]? = some (.send p q) → G.Adj p q

/-- Number of events of `p` strictly before position `k`. -/
def cnt (p : P) : ℕ → ℕ
  | 0 => 0
  | k + 1 => cnt p k + if ex.procAt k = some p then 1 else 0

/-- The 1-based index of event `i` at its process (`0` if there is no event `i`). -/
def idx (i : ℕ) : ℕ :=
  match ex.procAt i with
  | some p => ex.cnt p i + 1
  | none => 0

variable {ex}

/-! ### Basic lemmas -/

omit [DecidableEq P] in
lemma procAt_eq_some {i : ℕ} {p : P} :
    ex.procAt i = some p ↔ ∃ a, ex[i]? = some a ∧ a.proc = p := by
  simp [procAt]

omit [DecidableEq P] in
lemma procAt_of_get {i : ℕ} {a : Act P} (h : ex[i]? = some a) : ex.procAt i = some a.proc := by
  simp [procAt, h]

omit [DecidableEq P] in
lemma lt_length_of_procAt {i : ℕ} {p : P} (h : ex.procAt i = some p) : i < ex.length := by
  obtain ⟨a, ha, -⟩ := procAt_eq_some.1 h
  exact (List.getElem?_eq_some_iff.1 ha).1

lemma lastBefore_eq_some_iff {p : P} {k i : ℕ} :
    ex.lastBefore p k = some i ↔
      i < k ∧ ex.procAt i = some p ∧ ∀ l, i < l → l < k → ex.procAt l ≠ some p := by
  induction k with
  | zero => simp [lastBefore]
  | succ k ih =>
    simp only [lastBefore]
    split_ifs with h
    · constructor
      · rintro ⟨⟩
        exact ⟨by omega, h, fun l h1 h2 => by omega⟩
      · rintro ⟨h1, h2, h3⟩
        by_contra hne
        have : i < k := by
          rcases Nat.lt_succ_iff_lt_or_eq.1 h1 with h1 | h1
          · exact h1
          · exact absurd (by simp [h1]) hne
        exact h3 k this (by omega) h
    · rw [ih]
      constructor
      · rintro ⟨h1, h2, h3⟩
        refine ⟨by omega, h2, fun l hl1 hl2 => ?_⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 hl2 with hl2 | hl2
        · exact h3 l hl1 hl2
        · exact hl2 ▸ h
      · rintro ⟨h1, h2, h3⟩
        have : i ≠ k := fun e => h (e ▸ h2)
        exact ⟨by omega, h2, fun l hl1 hl2 => h3 l hl1 (by omega)⟩

lemma lastBefore_eq_none_iff {p : P} {k : ℕ} :
    ex.lastBefore p k = none ↔ ∀ l, l < k → ex.procAt l ≠ some p := by
  induction k with
  | zero => simp [lastBefore]
  | succ k ih =>
    simp only [lastBefore]
    split_ifs with h
    · simp only [false_iff, not_forall, not_not]
      exact ⟨k, by omega, h⟩
    · rw [ih]
      constructor
      · intro H l hl
        rcases Nat.lt_succ_iff_lt_or_eq.1 hl with hl | hl
        · exact H l hl
        · exact hl ▸ h
      · intro H l hl
        exact H l (by omega)

lemma prev_eq_some_iff {j i : ℕ} :
    ex.prev j = some i ↔ ∃ p, ex.procAt j = some p ∧ ex.lastBefore p j = some i := by
  unfold prev procAt
  cases ex[j]? <;> simp

lemma prev_spec {j i : ℕ} (h : ex.prev j = some i) :
    i < j ∧ j < ex.length ∧ ex.procAt i = ex.procAt j ∧
      ∀ l, i < l → l < j → ex.procAt l ≠ ex.procAt j := by
  obtain ⟨p, hp, hl⟩ := prev_eq_some_iff.1 h
  obtain ⟨h1, h2, h3⟩ := lastBefore_eq_some_iff.1 hl
  exact ⟨h1, lt_length_of_procAt hp, h2.trans hp.symm, fun l a b => hp ▸ h3 l a b⟩

lemma prev_eq_none_iff {j : ℕ} {p : P} (hp : ex.procAt j = some p) :
    ex.prev j = none ↔ ∀ l, l < j → ex.procAt l ≠ some p := by
  rw [← lastBefore_eq_none_iff]
  unfold prev
  obtain ⟨a, ha, rfl⟩ := procAt_eq_some.1 hp
  simp [ha]

/-- If `i < j` are events of the same process, `prev j` exists and lies in `[i, j)`. -/
lemma exists_prev_of_lt {i j : ℕ} {p : P} (hij : i < j) (hi : ex.procAt i = some p)
    (hj : ex.procAt j = some p) : ∃ i', ex.prev j = some i' ∧ i ≤ i' := by
  cases h : ex.prev j with
  | none => exact absurd hi ((prev_eq_none_iff hj).1 h i hij)
  | some i' =>
    refine ⟨i', rfl, ?_⟩
    obtain ⟨h1, -, h3, h4⟩ := prev_spec h
    by_contra hlt
    exact h4 i (by omega) hij (hi.trans hj.symm)

lemma Step.lt (hwf : ex.WF) {i j : ℕ} (h : ex.Step i j) : i < j := by
  cases h with
  | po h => exact (prev_spec h).1
  | msg h => exact hwf.recv_lt h

lemma Step.lt_length {i j : ℕ} (h : ex.Step i j) : j < ex.length := by
  cases h with
  | po h => exact (prev_spec h).2.1
  | msg h => exact (List.getElem?_eq_some_iff.1 h).1

lemma HB.lt (hwf : ex.WF) {i j : ℕ} (h : ex.HB i j) : i < j := by
  induction h with
  | single h => exact h.lt hwf
  | tail _ h ih => exact ih.trans (h.lt hwf)

lemma HB.lt_length {i j : ℕ} (h : ex.HB i j) : j < ex.length := by
  induction h with
  | single h => exact h.lt_length
  | tail _ h _ => exact h.lt_length

lemma HB.trans {i j k : ℕ} (h₁ : ex.HB i j) (h₂ : ex.HB j k) : ex.HB i k :=
  Relation.TransGen.trans h₁ h₂

lemma HB.irrefl (hwf : ex.WF) (i : ℕ) : ¬ ex.HB i i := fun h => lt_irrefl _ (h.lt hwf)

lemma HB.asymm (hwf : ex.WF) {i j : ℕ} (h : ex.HB i j) : ¬ ex.HB j i := fun h' =>
  HB.irrefl hwf i (h.trans h')

lemma HBeq.refl (i : ℕ) : ex.HBeq i i := Or.inl rfl

lemma HBeq.trans {i j k : ℕ} (h₁ : ex.HBeq i j) (h₂ : ex.HBeq j k) : ex.HBeq i k := by
  rcases h₁ with rfl | h₁
  · exact h₂
  · rcases h₂ with rfl | h₂
    · exact Or.inr h₁
    · exact Or.inr (h₁.trans h₂)

lemma HBeq.trans_hb {i j k : ℕ} (h₁ : ex.HBeq i j) (h₂ : ex.HB j k) : ex.HB i k := by
  rcases h₁ with rfl | h₁
  · exact h₂
  · exact h₁.trans h₂

lemma HB.trans_hbeq {i j k : ℕ} (h₁ : ex.HB i j) (h₂ : ex.HBeq j k) : ex.HB i k := by
  rcases h₂ with rfl | h₂
  · exact h₁
  · exact h₁.trans h₂

lemma HBeq.le (hwf : ex.WF) {i j : ℕ} (h : ex.HBeq i j) : i ≤ j := by
  rcases h with rfl | h
  · exact le_rfl
  · exact (h.lt hwf).le

lemma step_iff {i j : ℕ} :
    ex.Step i j ↔ ex.prev j = some i ∨ ∃ p, ex[j]? = some (.recv p i) := by
  constructor
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr ⟨_, h⟩
  · rintro (h | ⟨p, h⟩)
    · exact .po h
    · exact .msg h

/-- To show that happened-before is contained in a transitive relation, check the steps. -/
lemma HB.le_of_step {R : ℕ → ℕ → Prop} (htrans : ∀ i j k, R i j → R j k → R i k)
    (hstep : ∀ i j, ex.Step i j → R i j) {i j : ℕ} (h : ex.HB i j) : R i j := by
  induction h with
  | single h => exact hstep _ _ h
  | tail _ h ih => exact htrans _ _ _ ih (hstep _ _ h)

lemma HB.of_step {i j : ℕ} (h : ex.Step i j) : ex.HB i j := Relation.TransGen.single h

/-- `i → j` iff `i` happened-before or equals an immediate predecessor of `j`. -/
lemma HB.exists_step {i j : ℕ} (h : ex.HB i j) : ∃ k, ex.HBeq i k ∧ ex.Step k j := by
  induction h with
  | single h => exact ⟨_, HBeq.refl _, h⟩
  | tail h₁ h₂ _ => exact ⟨_, Or.inr h₁, h₂⟩

/-- Same-process events are ordered by happened-before according to their positions. -/
lemma hb_of_lt {i j : ℕ} {p : P} (hij : i < j) (hi : ex.procAt i = some p)
    (hj : ex.procAt j = some p) : ex.HB i j := by
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    obtain ⟨i', hi', hle⟩ := exists_prev_of_lt hij hi hj
    have hst : ex.Step i' j := .po hi'
    rcases hle.lt_or_eq with hlt | rfl
    · obtain ⟨h1, -, h3, -⟩ := prev_spec hi'
      exact (ih i' h1 hlt (h3.trans hj)).trans (.of_step hst)
    · exact .of_step hst

lemma hbeq_of_le {i j : ℕ} {p : P} (hij : i ≤ j) (hi : ex.procAt i = some p)
    (hj : ex.procAt j = some p) : ex.HBeq i j := by
  rcases hij.lt_or_eq with h | rfl
  · exact Or.inr (hb_of_lt h hi hj)
  · exact HBeq.refl _

/-- Events of the same process are totally ordered by happened-before. -/
lemma hb_total {i j : ℕ} {p : P} (hi : ex.procAt i = some p) (hj : ex.procAt j = some p) :
    ex.HB i j ∨ i = j ∨ ex.HB j i := by
  rcases lt_trichotomy i j with h | h | h
  · exact Or.inl (hb_of_lt h hi hj)
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (hb_of_lt h hj hi))

/-! ### Counting events and indices -/

lemma cnt_mono (p : P) {k l : ℕ} (h : k ≤ l) : ex.cnt p k ≤ ex.cnt p l := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => exact ih.trans (by simp [cnt])

lemma cnt_succ_of_procAt {p : P} {k : ℕ} (h : ex.procAt k = some p) :
    ex.cnt p (k + 1) = ex.cnt p k + 1 := by simp [cnt, h]

lemma idx_of_procAt {i : ℕ} {p : P} (h : ex.procAt i = some p) : ex.idx i = ex.cnt p i + 1 := by
  simp [idx, h]

lemma idx_lt_idx {i j : ℕ} {p : P} (hij : i < j) (hi : ex.procAt i = some p)
    (hj : ex.procAt j = some p) : ex.idx i < ex.idx j := by
  rw [idx_of_procAt hi, idx_of_procAt hj, ← cnt_succ_of_procAt hi]
  exact Nat.lt_succ_of_le (cnt_mono p hij)

lemma idx_le_idx_iff {i j : ℕ} {p : P} (hi : ex.procAt i = some p) (hj : ex.procAt j = some p) :
    ex.idx i ≤ ex.idx j ↔ i ≤ j := by
  constructor
  · intro h
    by_contra h'
    exact absurd (idx_lt_idx (not_le.1 h') hj hi) (not_lt.2 h)
  · intro h
    rcases h.lt_or_eq with h | rfl
    · exact (idx_lt_idx h hi hj).le
    · exact le_rfl

lemma cnt_eq_of_no_between {p : P} {k l : ℕ} (hkl : k ≤ l)
    (h : ∀ m, k ≤ m → m < l → ex.procAt m ≠ some p) : ex.cnt p l = ex.cnt p k := by
  induction l, hkl using Nat.le_induction with
  | base => rfl
  | succ l hkl ih =>
    simp only [cnt, h l hkl (by omega), ite_false, add_zero]
    exact ih fun m h1 h2 => h m h1 (by omega)

lemma idx_prev {i j : ℕ} (h : ex.prev j = some i) : ex.idx j = ex.idx i + 1 := by
  obtain ⟨p, hp, hl⟩ := prev_eq_some_iff.1 h
  obtain ⟨h1, h2, h3⟩ := lastBefore_eq_some_iff.1 hl
  rw [idx_of_procAt hp, idx_of_procAt h2, ← cnt_succ_of_procAt h2,
    cnt_eq_of_no_between (k := i + 1) (l := j) (by omega) (fun m hm1 hm2 => h3 m (by omega) hm2)]

lemma idx_of_prev_none {j : ℕ} {p : P} (hp : ex.procAt j = some p) (h : ex.prev j = none) :
    ex.idx j = 1 := by
  rw [idx_of_procAt hp, cnt_eq_of_no_between (Nat.zero_le j)
    (fun m _ hm => (prev_eq_none_iff hp).1 h m hm)]
  rfl

lemma pos_of_idx {i : ℕ} {p : P} (h : ex.procAt i = some p) : 0 < ex.idx i := by
  rw [idx_of_procAt h]; omega

/-! ### Extensions of executions -/

section Append

variable (l : Exec P)

omit [DecidableEq P] in
lemma getElem?_append_of_lt {i : ℕ} (h : i < ex.length) : (ex ++ l)[i]? = ex[i]? :=
  List.getElem?_append_left h

omit [DecidableEq P] in
lemma procAt_append_of_lt {i : ℕ} (h : i < ex.length) : (ex ++ l).procAt i = ex.procAt i := by
  simp [procAt, getElem?_append_of_lt l h]

lemma lastBefore_append {p : P} {k : ℕ} (hk : k ≤ ex.length) :
    (ex ++ l).lastBefore p k = ex.lastBefore p k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [lastBefore, procAt_append_of_lt l (by omega : k < ex.length), ih (by omega)]

lemma prev_append {j : ℕ} (hj : j < ex.length) : (ex ++ l).prev j = ex.prev j := by
  unfold prev
  rw [getElem?_append_of_lt l hj]
  cases ex[j]? with
  | none => rfl
  | some a => exact lastBefore_append l hj.le

lemma Step.append {i j : ℕ} (h : ex.Step i j) : (ex ++ l).Step i j := by
  cases h with
  | po h => exact .po ((prev_append l (prev_spec h).2.1).trans h)
  | msg h =>
    exact .msg ((getElem?_append_of_lt l (List.getElem?_eq_some_iff.1 h).1).trans h)

lemma HB.append {i j : ℕ} (h : ex.HB i j) : (ex ++ l).HB i j := by
  induction h with
  | single h => exact .of_step (h.append l)
  | tail _ h ih => exact ih.trans (.of_step (h.append l))

lemma HBeq.append {i j : ℕ} (h : ex.HBeq i j) : (ex ++ l).HBeq i j :=
  h.imp id (HB.append l)

lemma idx_append {i : ℕ} (hi : i < ex.length) : (ex ++ l).idx i = ex.idx i := by
  have hc : ∀ p k, k ≤ ex.length → (ex ++ l).cnt p k = ex.cnt p k := by
    intro p k hk
    induction k with
    | zero => rfl
    | succ k ih =>
      simp only [cnt, ih (by omega), procAt_append_of_lt l (by omega : k < ex.length)]
  simp only [idx, procAt_append_of_lt l hi]
  cases ex.procAt i with
  | none => rfl
  | some p => simp [hc p i hi.le]

end Append

/-- If `e → f` and `f` is at another process, then the causal chain leaves the process of `e`
through a message: some send `s` at the process of `e`, at or after `e`, whose receive `r`
satisfies `r = f ∨ r → f`. -/
lemma HB.exists_send_out {e f : ℕ} {p : P} (hep : ex.procAt e = some p)
    (h : ex.HB e f) (hf : ex.procAt f ≠ some p) :
    ∃ s r q, e ≤ s ∧ ex.procAt s = some p ∧ ex[r]? = some (.recv q s) ∧ ex.HBeq r f := by
  induction h using Relation.TransGen.head_induction_on generalizing p with
  | single h =>
    cases h with
    | po h =>
      obtain ⟨-, -, h3, -⟩ := prev_spec h
      exact absurd (h3.symm.trans hep) hf
    | msg h => exact ⟨_, _, _, le_rfl, hep, h, HBeq.refl _⟩
  | head h hrest ih =>
    cases h with
    | po h =>
      obtain ⟨h1, -, h3, -⟩ := prev_spec h
      obtain ⟨s, r, q, hs, hsp, hr, hrf⟩ := ih (h3.symm.trans hep) hf
      exact ⟨s, r, q, by omega, hsp, hr, hrf⟩
    | msg h => exact ⟨_, _, _, le_rfl, hep, h, Or.inr hrest⟩

/-! ### Messages: receive events, `outbound`, FIFO channels -/

open Classical in
/-- The receive event of the message sent at position `s` (if it is received). -/
noncomputable def recvOf (ex : Exec P) (s : ℕ) : Option ℕ :=
  if h : ∃ r, ∃ q, ex[r]? = some (.recv q s) then some (Nat.find h) else none

/-- The index of the receive event of the message sent at `s` (`⊤` if it is not received). -/
noncomputable def recvIdx (ex : Exec P) (s : ℕ) : ℕ∞ :=
  (ex.recvOf s).elim ⊤ fun r => (ex.idx r : ℕ∞)

open Classical in
/-- `outbound(q, e)` at time `t` (Section 2 of Vaidya–Kulkarni): the first send of `p` to `q`
at a position in `[e, t]`. -/
noncomputable def outbound (ex : Exec P) (p q : P) (e t : ℕ) : Option ℕ :=
  if h : ∃ s, e ≤ s ∧ s ≤ t ∧ ex[s]? = some (.send p q) then some (Nat.find h) else none

/-- FIFO channels: messages from `p` to `q` are received in the order in which they were sent. -/
def FIFO (ex : Exec P) : Prop :=
  ∀ {s₁ s₂ r₂ : ℕ} {p q : P}, s₁ < s₂ → ex[s₁]? = some (.send p q) →
    ex[s₂]? = some (.send p q) → ex[r₂]? = some (.recv q s₂) →
    ∃ r₁, r₁ < r₂ ∧ ex[r₁]? = some (.recv q s₁)

omit [DecidableEq P] in
open Classical in
lemma recvOf_eq (hwf : ex.WF) {r s : ℕ} {q : P} (h : ex[r]? = some (.recv q s)) :
    ex.recvOf s = some r := by
  have hex : ∃ r, ∃ q, ex[r]? = some (Act.recv q s) := ⟨r, q, h⟩
  rw [recvOf, dite_eq_left_of_eq_true (eq_true hex)]
  obtain ⟨q', hq'⟩ := Nat.find_spec hex
  rw [hwf.recv_unique hq' h]

lemma recvIdx_eq (hwf : ex.WF) {r s : ℕ} {q : P} (h : ex[r]? = some (.recv q s)) :
    ex.recvIdx s = ex.idx r := by
  simp [recvIdx, recvOf_eq hwf h]

open Classical in
lemma recvIdx_ne_top {s : ℕ} (h : ex.recvIdx s ≠ ⊤) :
    ∃ r q, ex[r]? = some (.recv q s) ∧ ex.recvIdx s = ex.idx r := by
  unfold recvIdx recvOf at *
  split_ifs at * with hex
  · obtain ⟨q, hq⟩ := Nat.find_spec hex
    exact ⟨_, q, hq, rfl⟩
  · simp at h

open Classical in
lemma outbound_spec {p q : P} {e t s : ℕ} (h : ex.outbound p q e t = some s) :
    e ≤ s ∧ s ≤ t ∧ ex[s]? = some (.send p q) ∧
      ∀ s', e ≤ s' → s' ≤ t → ex[s']? = some (.send p q) → s ≤ s' := by
  unfold outbound at h
  split_ifs at h with hex
  cases h
  obtain ⟨h1, h2, h3⟩ := Nat.find_spec hex
  exact ⟨h1, h2, h3, fun s' a b c => Nat.find_min' hex ⟨a, b, c⟩⟩

open Classical in
lemma outbound_isSome {p q : P} {e t s : ℕ} (h1 : e ≤ s) (h2 : s ≤ t)
    (h3 : ex[s]? = some (.send p q)) : ∃ s', ex.outbound p q e t = some s' := by
  unfold outbound
  rw [dite_eq_left_of_eq_true (eq_true ⟨s, h1, h2, h3⟩)]
  exact ⟨_, rfl⟩

end Exec

/-! ### Timestamping algorithms -/

/-- The timestamps assigned by an online algorithm `A`: the timestamp of event `i` is computed
when the event occurs, i.e. from the prefix of the execution ending with `i`. The algorithm may
use the whole prefix (global knowledge, including real-time order), which only strengthens lower
bounds. -/
def onlineTs {P V : Type*} (A : Exec P → V) (ex : Exec P) (i : ℕ) : V := A (ex.take (i + 1))

/-- Timestamps `τ` of the events of `ex` are distinct and capture causality:
`e → f ↔ τ e < τ f`. -/
def CapturesCausality {P V : Type*} [DecidableEq P] [LT V] (ex : Exec P) (τ : ℕ → V) : Prop :=
  ∀ i j, i < ex.length → j < ex.length →
    (ex.HB i j ↔ τ i < τ j) ∧ (i ≠ j → τ i ≠ τ j)

/-- An online timestamping algorithm for the communication graph `G` (Section 3 of the paper):
on every well-formed execution over `G`, its timestamps are distinct and capture causality. -/
def IsOnlineTimestamping {P V : Type*} [DecidableEq P] [LT V] (G : SimpleGraph P)
    (A : Exec P → V) : Prop :=
  ∀ ex : Exec P, ex.WF → ex.OnGraph G → CapturesCausality ex (onlineTs A ex)

end Cslib.Causality
