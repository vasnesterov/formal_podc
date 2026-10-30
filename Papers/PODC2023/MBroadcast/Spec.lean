import Mathlib.Data.List.Basic
import Mathlib.Data.List.Count
import Mathlib.Data.List.TakeDrop
import Mathlib.Order.Basic
import Mathlib.Tactic

/-!
# The MBroadcast abstraction (Déprés, Mostéfaoui, Perrin, Raynal, PODC 2023), Section 3

An *MBroadcast trace* is the list of the events of the abstraction, in real-time order:
`bc p m` (`p` invokes `mbroadcast(m)`) and `dl p q m` (`p` mdelivers `m` from `q`).

The safety properties of MBroadcast and of its enrichments are properties of finite traces:

* `Validity`, `NoDuplication`, `MutualOrdering` (the defining properties);
* `FifoOrdering`, `CausalOrdering` (fifo- and causal-MBroadcast).

"`p` mdelivers `m` before `m'`" is read, as for the FIFO and causal ordering properties of the
paper, as "when `p` mdelivers `m`, it has not mdelivered `m'`" (`DelivBefore`): this includes the
case where `p` never mdelivers `m'`. This is the reading of the paper's message pattern `MP1`
("when a process delivers its own message, it has no information on the other one"), and it is
the reading under which Property 1 and Theorem 2 hold. The literal alternative ("`p` mdelivers
both, `m` first", `WeakMutualOrdering`) makes Property 1 false (`property1_false_weak`).

The liveness properties (Local termination, Global CS- and CF-termination) depend on the notion of
correct process of each model; they are stated in the model files.
-/

namespace Podc.MBroadcast

/-- Events of the MBroadcast abstraction. -/
inductive Ev (P M : Type) where
  /-- `p` invokes `mbroadcast(m)`. -/
  | bc (p : P) (m : M)
  /-- `p` mdelivers `m` from `q`. -/
  | dl (p q : P) (m : M)
  deriving DecidableEq

variable {P M : Type} [DecidableEq P] [DecidableEq M]

section Props

variable (tr : List (Ev P M))

/-- **Validity.** If `p` mdelivers `m` from `q`, then `q` previously invoked `mbroadcast(m)`. -/
def Validity : Prop :=
  ∀ i p q m, tr[i]? = some (.dl p q m) → .bc q m ∈ tr.take i

/-- **No-duplication.** A process mdelivers a message (from a given sender) at most once. -/
def NoDuplication : Prop :=
  ∀ p q m, tr.count (.dl p q m) ≤ 1

/-- The paper's assumption that all mbroadcast messages are different (per sender: the message
identity is the pair (sender, message)). -/
def UniqueBc : Prop :=
  ∀ p m, tr.count (.bc p m) ≤ 1

/-- `p` mdelivers its own message `m` at a time when it has not mdelivered `m'` from `q`. -/
def DelivBefore (p : P) (m : M) (q : P) (m' : M) : Prop :=
  ∃ i, tr[i]? = some (.dl p p m) ∧ .dl p q m' ∉ tr.take i

/-- **Mutual ordering.** For any processes `p`, `p'` and messages `m` (mbroadcast by `p`) and
`m'` (mbroadcast by `p'`), it is not possible that `p` mdelivers `m` before `m'` and `p'`
mdelivers `m'` before `m`. -/
def MutualOrdering : Prop :=
  ∀ p m p' m', (p, m) ≠ (p', m') → ¬ (DelivBefore tr p m p' m' ∧ DelivBefore tr p' m' p m)

/-- The safety part of MBroadcast. -/
structure Safe (tr : List (Ev P M)) : Prop where
  validity : Validity tr
  noDup : NoDuplication tr
  mutualOrd : MutualOrdering tr

/-- **FIFO ordering.** If a process mbroadcasts `m` and then `m'`, no process mdelivers `m'`
before `m`. -/
def FifoOrdering : Prop :=
  ∀ (p : P) (m m' : M) (i j : ℕ), tr[i]? = some (.bc p m) → tr[j]? = some (.bc p m') → i < j →
    ∀ (q : P) (k : ℕ), tr[k]? = some (.dl q p m') → .dl q p m ∈ tr.take k

/-- **Causal ordering.** If a process mdelivers `m` (from `q`) and then mbroadcasts `m'`, no
process mdelivers `m'` before `m`. -/
def CausalOrdering : Prop :=
  ∀ (p q : P) (m m' : M) (i j : ℕ), tr[i]? = some (.dl p q m) → tr[j]? = some (.bc p m') → i < j →
    ∀ (r : P) (k : ℕ), tr[k]? = some (.dl r p m') → .dl r q m ∈ tr.take k

/-- The *literal* reading of mutual ordering: "`p` mdelivers both messages, `m` first". -/
def WeakDelivBefore (p : P) (m : M) (q : P) (m' : M) : Prop :=
  ∃ i j : ℕ, i < j ∧ tr[i]? = some (.dl p p m) ∧ tr[j]? = some (.dl p q m')

/-- Mutual ordering under the literal reading. -/
def WeakMutualOrdering : Prop :=
  ∀ p m p' m', (p, m) ≠ (p', m') →
    ¬ (WeakDelivBefore tr p m p' m' ∧ WeakDelivBefore tr p' m' p m)

end Props

/-! ## Basic facts -/

section Basic

variable {tr : List (Ev P M)}

lemma mem_take_of_getElem? {i j : ℕ} {e : Ev P M} (h : tr[j]? = some e) (hji : j < i) :
    e ∈ tr.take i := by
  have hj : j < tr.length := by
    by_contra hc; rw [List.getElem?_eq_none (by omega)] at h; cases h
  rw [List.getElem?_eq_getElem hj] at h
  have h' : (tr.take i)[j]? = some e := by
    rw [List.getElem?_take]; simp [hji, List.getElem?_eq_getElem hj, h]
  exact List.mem_of_getElem? h'

lemma exists_lt_of_mem_take {i : ℕ} {e : Ev P M} (h : e ∈ tr.take i) :
    ∃ j < i, tr[j]? = some e := by
  obtain ⟨j, hj, hje⟩ := List.getElem_of_mem h
  refine ⟨j, ?_, ?_⟩
  · have := List.length_take_le' i tr; simp at hj; omega
  · simp at hj
    rw [← hje, List.getElem_take]; exact List.getElem?_eq_getElem _

lemma mem_take_iff {i : ℕ} {e : Ev P M} : e ∈ tr.take i ↔ ∃ j < i, tr[j]? = some e :=
  ⟨exists_lt_of_mem_take, fun ⟨_, hj, he⟩ => mem_take_of_getElem? he hj⟩

/-- Two occurrences of an element of count `≤ 1` are at the same position. -/
lemma eq_of_count_le_one {α : Type} [DecidableEq α] {l : List α} {a : α} (h : l.count a ≤ 1)
    {i j : ℕ} (hi : l[i]? = some a) (hj : l[j]? = some a) : i = j := by
  by_contra hne
  wlog hlt : i < j generalizing i j
  · exact this hj hi (Ne.symm hne) (by omega)
  have hjl : j < l.length := by
    by_contra hc; rw [List.getElem?_eq_none (by omega)] at hj; cases hj
  -- `l = take j l ++ drop j l`, `a ∈ take j l` and `a` is the head of `drop j l`
  have h1 : a ∈ l.take j := by
    have h' : (l.take j)[i]? = some a := by rw [List.getElem?_take]; simp [hlt, hi]
    exact List.mem_of_getElem? h'
  have h2 : (l.drop j).count a ≥ 1 := by
    rw [List.getElem?_eq_getElem hjl] at hj
    rw [List.drop_eq_getElem_cons hjl]; simp [Option.some.inj hj]
  have h3 : (l.take j).count a ≥ 1 := List.count_pos_iff.2 h1
  have := List.count_append (a := a) (l₁ := l.take j) (l₂ := l.drop j)
  rw [List.take_append_drop] at this
  omega

/-- Mutual ordering holds automatically for two messages of the same process. -/
lemma not_delivBefore_same {p : P} {m m' : M} (hne : m ≠ m') :
    ¬ (DelivBefore tr p m p m' ∧ DelivBefore tr p m' p m) := by
  rintro ⟨⟨i, hi, hi'⟩, ⟨j, hj, hj'⟩⟩
  rcases lt_trichotomy i j with h | h | h
  · exact hj' (mem_take_of_getElem? hi h)
  · subst h; rw [hi] at hj; cases hj; exact hne rfl
  · exact hi' (mem_take_of_getElem? hj h)

/-- The prefix of a trace (any `take`). -/
lemma getElem?_take_of_lt {l : List (Ev P M)} {i k : ℕ} (h : i < k) : (l.take k)[i]? = l[i]? := by
  rw [List.getElem?_take]; simp [h]

end Basic

/-! ## Prefix closure of the safety properties -/

section Prefix

variable {tr tr' : List (Ev P M)}

lemma Validity.of_append (h : Validity (tr ++ tr')) : Validity tr := by
  intro i p q m hi
  have hil : i < tr.length := by
    by_contra hc; rw [List.getElem?_eq_none (by omega)] at hi; cases hi
  have := h i p q m (by rw [List.getElem?_append_left hil]; exact hi)
  rwa [List.take_append_of_le_length hil.le] at this

lemma NoDuplication.of_append (h : NoDuplication (tr ++ tr')) : NoDuplication tr := by
  intro p q m; have := h p q m; rw [List.count_append] at this; omega

lemma UniqueBc.of_append (h : UniqueBc (tr ++ tr')) : UniqueBc tr := by
  intro p m; have := h p m; rw [List.count_append] at this; omega

lemma DelivBefore.append {p q : P} {m m' : M} (h : DelivBefore tr p m q m') :
    DelivBefore (tr ++ tr') p m q m' := by
  obtain ⟨i, hi, hi'⟩ := h
  have hil : i < tr.length := by
    by_contra hc; rw [List.getElem?_eq_none (by omega)] at hi; cases hi
  refine ⟨i, by rw [List.getElem?_append_left hil]; exact hi, ?_⟩
  rwa [List.take_append_of_le_length hil.le]

lemma MutualOrdering.of_append (h : MutualOrdering (tr ++ tr')) : MutualOrdering tr :=
  fun p m p' m' hne ⟨h1, h2⟩ => h p m p' m' hne ⟨h1.append, h2.append⟩

lemma Safe.of_append (h : Safe (tr ++ tr')) : Safe tr :=
  ⟨h.validity.of_append, h.noDup.of_append, h.mutualOrd.of_append⟩

end Prefix

/-! ## Property 1: the real-time property of `synchro_mbroadcast` -/

/-- **Property 1** (Section 3, Figure 1). If `p` returns from `synchro_mbroadcast(m)` (i.e. it
mdelivers its own `m`, at position `i`) before `p'` invokes `synchro_mbroadcast(m')` (position
`j`), then `p'` cannot return from `synchro_mbroadcast(m')` (mdeliver its own `m'`, position `k`)
before it has mdelivered `m`. -/
theorem property1 {tr : List (Ev P M)} (hv : Validity tr) (hmo : MutualOrdering tr)
    (hu : UniqueBc tr) {p p' : P} {m m' : M} {i j k : ℕ}
    (hi : tr[i]? = some (.dl p p m)) (hj : tr[j]? = some (.bc p' m')) (hij : i < j)
    (hk : tr[k]? = some (.dl p' p' m')) : .dl p' p m ∈ tr.take k := by
  -- `m'` is not mdelivered by `p` before position `i`: it is broadcast only at `j > i`
  have h1 : DelivBefore tr p m p' m' := by
    refine ⟨i, hi, fun hmem => ?_⟩
    obtain ⟨l, hl, hl'⟩ := exists_lt_of_mem_take hmem
    obtain ⟨l', hl'', hbc⟩ := exists_lt_of_mem_take (hv l p p' m' hl')
    have := eq_of_count_le_one (hu p' m') hbc hj
    omega
  have hne : (p, m) ≠ (p', m') := by
    intro he
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    obtain ⟨l, hl, hbc⟩ := exists_lt_of_mem_take (hv i p p m hi)
    have := eq_of_count_le_one (hu p m) hbc hj
    omega
  by_contra hc
  exact hmo p m p' m' hne ⟨h1, k, hk, hc⟩

/-! ## The literal reading of mutual ordering is too weak -/

/-- A trace in which `p₀ = 0` returns from `synchro_mbroadcast(0)` (and then crashes), after
which `p₁ = 1` invokes and returns from `synchro_mbroadcast(1)` without mdelivering `0`. -/
def weakTrace : List (Ev Bool Bool) :=
  [.bc false false, .dl false false false, .bc true true, .dl true true true]

/-- Under the literal reading of mutual ordering, Property 1 is false: the trace `weakTrace`
satisfies validity, no-duplication, unique broadcasts and the literal mutual ordering (no
process mdelivers both messages), and is compatible with Global CS-termination (the sender of the
undelivered message is faulty), but `p₁` returns from `synchro_mbroadcast` without having
mdelivered the message of `p₀` that was mdelivered before its invocation. -/
theorem property1_false_weak :
    Validity weakTrace ∧ NoDuplication weakTrace ∧ UniqueBc weakTrace ∧
      WeakMutualOrdering weakTrace ∧
      weakTrace[1]? = some (.dl false false false) ∧ weakTrace[2]? = some (.bc true true) ∧
      weakTrace[3]? = some (.dl true true true) ∧
      .dl true false false ∉ weakTrace.take 3 := by
  refine ⟨?_, ?_, ?_, ?_, rfl, rfl, rfl, by decide⟩
  · intro i p q m hi
    match i, hi with
    | 1, hi => simp [weakTrace] at hi; obtain ⟨rfl, rfl, rfl⟩ := hi; decide
    | 3, hi => simp [weakTrace] at hi; obtain ⟨rfl, rfl, rfl⟩ := hi; decide
    | 0, hi => simp [weakTrace] at hi
    | 2, hi => simp [weakTrace] at hi
    | n + 4, hi => simp [weakTrace] at hi
  · intro p q m; revert p q m; decide
  · intro p m; revert p m; decide
  · rintro p m p' m' hne ⟨⟨i, j, hij, hi, hj⟩, -⟩
    match j, hj with
    | 0, hj => simp [weakTrace] at hj
    | 2, hj => simp [weakTrace] at hj
    | n + 4, hj => simp [weakTrace] at hj
    | 1, hj =>
      simp [weakTrace] at hj; obtain ⟨rfl, rfl, rfl⟩ := hj
      match i, hi with
      | 0, hi => simp [weakTrace] at hi
    | 3, hj =>
      simp [weakTrace] at hj; obtain ⟨rfl, rfl, rfl⟩ := hj
      match i, hi with
      | 0, hi => simp [weakTrace] at hi
      | 1, hi => simp [weakTrace] at hi
      | 2, hi => simp [weakTrace] at hi

/-- Under the reading `DelivBefore`, `weakTrace` violates mutual ordering (as it must, by
Property 1). -/
theorem weakTrace_not_mutualOrdering : ¬ MutualOrdering weakTrace := by
  intro h
  exact h false false true true (by decide)
    ⟨⟨1, rfl, by decide⟩, ⟨3, rfl, by decide⟩⟩

/-! ## Decision procedures for concrete traces -/

section Decide

/-- Boolean check of `Validity`. -/
def validB (tr : List (Ev P M)) : Bool :=
  (List.range tr.length).all fun i =>
    match tr[i]? with
    | some (.dl _ q m) => decide (Ev.bc q m ∈ tr.take i)
    | _ => true

lemma validity_of_validB {tr : List (Ev P M)} (h : validB tr = true) : Validity tr := by
  intro i p q m hi
  have hil : i < tr.length := by
    by_contra hc; rw [List.getElem?_eq_none (by omega)] at hi; cases hi
  have := List.all_eq_true.1 h i (List.mem_range.2 hil)
  rw [hi] at this
  simpa using this

/-- Boolean check of `NoDuplication`. -/
def noDupB (tr : List (Ev P M)) : Bool :=
  tr.all fun e =>
    match e with
    | .dl _ _ _ => decide (tr.count e ≤ 1)
    | _ => true

lemma noDuplication_of_noDupB {tr : List (Ev P M)} (h : noDupB tr = true) :
    NoDuplication tr := by
  intro p q m
  by_cases hm : Ev.dl p q m ∈ tr
  · have := List.all_eq_true.1 h _ hm
    simpa using this
  · rw [List.count_eq_zero_of_not_mem hm]; omega

/-- Boolean check of `UniqueBc`. -/
def uniqueBcB (tr : List (Ev P M)) : Bool :=
  tr.all fun e =>
    match e with
    | .bc _ _ => decide (tr.count e ≤ 1)
    | _ => true

lemma uniqueBc_of_uniqueBcB {tr : List (Ev P M)} (h : uniqueBcB tr = true) : UniqueBc tr := by
  intro p m
  by_cases hm : Ev.bc p m ∈ tr
  · have := List.all_eq_true.1 h _ hm
    simpa using this
  · rw [List.count_eq_zero_of_not_mem hm]; omega

/-- If every mdelivery is of the deliverer's own message, the literal mutual ordering holds
(given no-duplication). -/
lemma weakMutualOrdering_of_own {tr : List (Ev P M)} (hnd : NoDuplication tr)
    (hown : ∀ p q m, Ev.dl p q m ∈ tr → p = q) : WeakMutualOrdering tr := by
  rintro p m p' m' hne ⟨⟨i, j, hij, hi, hj⟩, ⟨i', j', hij', hi', hj'⟩⟩
  have hpp : p = p' := hown _ _ _ (List.mem_of_getElem? hj)
  subst hpp
  have e1 := eq_of_count_le_one (hnd p p m) hi hj'
  have e2 := eq_of_count_le_one (hnd p p m') hj hi'
  omega

/-- Boolean check of `MutualOrdering`. -/
def moB (tr : List (Ev P M)) : Bool :=
  (List.range tr.length).all fun i => (List.range tr.length).all fun j =>
    match tr[i]?, tr[j]? with
    | some (.dl p p₁ m), some (.dl p' p₁' m') =>
      if p = p₁ ∧ p' = p₁' ∧ (p, m) ≠ (p', m') then
        decide (Ev.dl p p' m' ∈ tr.take i ∨ Ev.dl p' p m ∈ tr.take j)
      else true
    | _, _ => true

lemma mutualOrdering_of_moB {tr : List (Ev P M)} (h : moB tr = true) : MutualOrdering tr := by
  rintro p m p' m' hne ⟨⟨i, hi, hi'⟩, ⟨j, hj, hj'⟩⟩
  have hil : i < tr.length := by
    by_contra hc; rw [List.getElem?_eq_none (by omega)] at hi; cases hi
  have hjl : j < tr.length := by
    by_contra hc; rw [List.getElem?_eq_none (by omega)] at hj; cases hj
  have := List.all_eq_true.1 (List.all_eq_true.1 h i (List.mem_range.2 hil)) j
    (List.mem_range.2 hjl)
  rw [hi, hj] at this
  simp only [true_and, ne_eq, hne, not_false_eq_true, ite_true, decide_eq_true_eq] at this
  rcases this with h1 | h1
  · exact hi' h1
  · exact hj' h1

end Decide

end Podc.MBroadcast
