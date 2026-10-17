import Mathlib
import Papers.PODC2023.RuntimeVerification.Similarity

/-!
# Timed histories

A *timed history* describes a finite history by its operations and the times of their
invocations and responses: process `p` invoked the operations `0, …, m p - 1` (arguments
`op p k`), of which `0, …, c p - 1` completed (responses `res p k`), at times `ti p k` / `tr p k`
in a linear order `T`. The list history `toList h` lists the events in increasing order of time.

Timed histories are the bridge between executions (whose events have times) and the list
histories on which linearizability / `GenLin` are defined: all real-time questions about
`toList h` reduce to comparisons of times (`precedes_toList`).

-- CSLib candidate: the whole file (timed histories ↔ Herlihy–Wing histories).
-/

namespace Podc2023.RuntimeVerification

open Cslib.SharedMemory.HerlihyWing

/-- A timed history. -/
structure TH (P Op R T : Type) where
  /-- Number of operations invoked by `p`. -/
  m : P → ℕ
  /-- Number of operations of `p` that completed. -/
  c : P → ℕ
  /-- Argument of the `k`-th operation of `p`. -/
  op : P → ℕ → Op
  /-- Response of the `k`-th operation of `p`. -/
  res : P → ℕ → R
  /-- Invocation time of the `k`-th operation of `p`. -/
  ti : P → ℕ → T
  /-- Response time of the `k`-th operation of `p`. -/
  tr : P → ℕ → T

namespace TH

variable {P Op R T : Type}

/-- Event keys: `(p, k, false)` is the invocation of the `k`-th operation of `p`,
`(p, k, true)` its response. -/
abbrev Key (P : Type) := P × ℕ × Bool

/-- The key denotes an event of `h`. -/
def Valid (h : TH P Op R T) (x : Key P) : Prop :=
  if x.2.2 then x.2.1 < h.c x.1 else x.2.1 < h.m x.1

/-- Time of an event. -/
def time (h : TH P Op R T) (x : Key P) : T :=
  if x.2.2 then h.tr x.1 x.2.1 else h.ti x.1 x.2.1

/-- The history event of a key. -/
def event (h : TH P Op R T) (x : Key P) : Event P Unit Op R :=
  if x.2.2 then .res x.1 () (h.res x.1 x.2.1) else .inv x.1 () (h.op x.1 x.2.1)

variable [Fintype P] [DecidableEq P]

/-- All event keys of `h`. -/
noncomputable def keys (h : TH P Op R T) : List (Key P) :=
  (Finset.univ : Finset P).toList.flatMap fun p =>
    (List.range (h.m p)).map (fun k => (p, k, false)) ++
      (List.range (h.c p)).map (fun k => (p, k, true))

variable [LinearOrder T]

/-- The list history: the events sorted by time. -/
noncomputable def toList (h : TH P Op R T) : Hist P Op R :=
  ((h.keys).mergeSort (fun x y => decide (h.time x ≤ h.time y))).map h.event

/-- Well-formedness of a timed history: each process is sequential (only its last operation may
be pending, invocations precede responses which precede the next invocation) and distinct events
happen at distinct times. -/
structure WF (h : TH P Op R T) : Prop where
  c_le_m : ∀ p, h.c p ≤ h.m p
  m_le_c : ∀ p, h.m p ≤ h.c p + 1
  inv_lt_res : ∀ p k, k < h.c p → h.ti p k < h.tr p k
  res_lt_inv : ∀ p k, k + 1 < h.m p → h.tr p k < h.ti p (k + 1)
  inj : ∀ x y, h.Valid x → h.Valid y → h.time x = h.time y → x = y

variable {h : TH P Op R T}

/-! ### Auxiliary list lemmas -/

section Aux

variable {α β : Type*}

/-- Two lists strictly sorted by `f` with the same members are equal. -/
theorem eq_of_pairwise_lt [LinearOrder β] (f : α → β) {l₁ l₂ : List α}
    (h₁ : l₁.Pairwise (fun x y => f x < f y)) (h₂ : l₂.Pairwise (fun x y => f x < f y))
    (hm : ∀ x, x ∈ l₁ ↔ x ∈ l₂) : l₁ = l₂ :=
  haveI : Std.Irrefl (fun x y : α => f x < f y) := ⟨fun _ => lt_irrefl _⟩
  haveI : Std.Antisymm (fun x y : α => f x < f y) := ⟨fun _ _ h h' => absurd h' h.asymm⟩
  h₁.eq_of_mem_iff h₂ hm

theorem filterMap_eq_map_filter_of (q : α → Bool) (g : α → β) (F : α → Option β)
    (hF : ∀ x, F x = if q x then some (g x) else none) (l : List α) :
    l.filterMap F = (l.filter q).map g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.filterMap_cons, hF, List.filter_cons]
    by_cases ha : q a <;> simp [ha, ih]

/-- A prefix of `(range c).map g` (with `g` injective) is `(range j).map g`. -/
theorem lt_length_iff_of_prefix_map_range {g : ℕ → α} (hg : Function.Injective g) {l : List α}
    {c : ℕ} (hl : l <+: (List.range c).map g) (k : ℕ) : k < l.length ↔ g k ∈ l := by
  have hlen : l.length ≤ c := by simpa using hl.length_le
  rw [List.prefix_iff_eq_take] at hl
  conv_rhs => rw [hl]
  rw [← List.map_take, List.take_range, List.mem_map]
  simp only [List.mem_range, hg.eq_iff, exists_eq_right]
  omega

/-- Filtering a strictly sorted list by a time bound gives a prefix. -/
theorem filter_lt_prefix [LinearOrder β] (f : α → β) (t : β) :
    ∀ {l : List α}, l.Pairwise (fun x y => f x < f y) →
      l.filter (fun x => decide (f x < t)) <+: l
  | [], _ => List.prefix_refl _
  | a :: l, hl => by
    rw [List.pairwise_cons] at hl
    by_cases ha : f a < t
    · rw [List.filter_cons_of_pos (by simpa using ha)]
      exact List.cons_prefix_cons.2 ⟨rfl, filter_lt_prefix f t hl.2⟩
    · have : l.filter (fun x => decide (f x < t)) = [] := by
        rw [List.filter_eq_nil_iff]
        intro x hx
        have := hl.1 x hx
        simp only [decide_eq_true_eq, not_lt]
        exact le_of_lt (lt_of_le_of_lt (not_lt.1 ha) this)
      rw [List.filter_cons_of_neg (by simpa using ha), this]
      exact List.nil_prefix

/-- Filtering `range m` by a downward closed predicate gives an initial segment. -/
theorem lt_length_filter_range (q : ℕ → Bool) : ∀ {m : ℕ},
    (∀ k k', k < k' → k' < m → q k' = true → q k = true) → ∀ k,
      (k < ((List.range m).filter q).length ↔ k < m ∧ q k = true)
  | 0, _, k => by simp
  | m + 1, hd, k => by
    have ih := lt_length_filter_range q (m := m) (fun k k' h1 h2 h3 => hd k k' h1 (by omega) h3)
    rw [List.range_succ, List.filter_append, List.length_append]
    by_cases hm : q m = true
    · have hall : ∀ j, j < m → q j = true := fun j hj => hd j m hj (by omega) hm
      have hlen : ((List.range m).filter q).length = m := by
        apply le_antisymm
        · by_contra hc
          push Not at hc
          exact absurd ((ih m).1 hc).1 (lt_irrefl _)
        · by_contra hc
          push Not at hc
          exact absurd ((ih _).2 ⟨hc, hall _ hc⟩) (lt_irrefl _)
      rw [hlen]
      simp only [List.filter_cons, hm, ↓reduceIte, List.filter_nil, List.length_cons,
        List.length_nil]
      constructor
      · intro hk
        refine ⟨by omega, ?_⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 (show k < m + 1 by omega) with h' | h'
        · exact hall _ h'
        · subst h'; exact hm
      · exact fun h' => by omega
    · simp only [List.filter_cons, hm, Bool.false_eq_true, ↓reduceIte, List.filter_nil,
        List.length_nil, Nat.add_zero]
      rw [ih k]
      constructor
      · exact fun h' => ⟨by omega, h'.2⟩
      · intro h'
        refine ⟨?_, h'.2⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 h'.1 with h'' | h''
        · exact h''
        · subst h''; exact absurd h'.2 hm

theorem map_range_two_mul (g : ℕ → α) (c : ℕ) :
    (List.range (2 * c)).map g = (List.range c).flatMap (fun k => [g (2 * k), g (2 * k + 1)]) := by
  induction c with
  | zero => simp
  | succ c ih =>
    rw [show 2 * (c + 1) = 2 * c + 1 + 1 by ring, List.range_succ, List.range_succ,
      List.range_succ, List.flatMap_append, List.map_append, List.map_append, ih]
    simp

end Aux

/-! ### Sorted keys -/

/-- The event keys sorted by time. -/
noncomputable def sortedKeys (h : TH P Op R T) : List (Key P) :=
  h.keys.mergeSort (fun x y => decide (h.time x ≤ h.time y))

omit [DecidableEq P] in
theorem toList_def : h.toList = h.sortedKeys.map h.event := rfl

omit [Fintype P] [DecidableEq P] [LinearOrder T] in
@[simp] theorem time_inv (p : P) (k : ℕ) : h.time (p, k, false) = h.ti p k := rfl
omit [Fintype P] [DecidableEq P] [LinearOrder T] in
@[simp] theorem time_res (p : P) (k : ℕ) : h.time (p, k, true) = h.tr p k := rfl
omit [Fintype P] [DecidableEq P] [LinearOrder T] in
@[simp] theorem event_inv (p : P) (k : ℕ) : h.event (p, k, false) = .inv p () (h.op p k) := rfl
omit [Fintype P] [DecidableEq P] [LinearOrder T] in
@[simp] theorem event_res (p : P) (k : ℕ) : h.event (p, k, true) = .res p () (h.res p k) := rfl
omit [Fintype P] [DecidableEq P] [LinearOrder T] in
@[simp] theorem valid_inv (p : P) (k : ℕ) : h.Valid (p, k, false) ↔ k < h.m p := Iff.rfl
omit [Fintype P] [DecidableEq P] [LinearOrder T] in
@[simp] theorem valid_res (p : P) (k : ℕ) : h.Valid (p, k, true) ↔ k < h.c p := Iff.rfl

omit [DecidableEq P] [LinearOrder T] in
theorem mem_keys {x : Key P} : x ∈ h.keys ↔ h.Valid x := by
  obtain ⟨p, k, b⟩ := x
  cases b <;> simp [keys]

omit [DecidableEq P] in
theorem mem_sortedKeys {x : Key P} : x ∈ h.sortedKeys ↔ h.Valid x := by
  simp [sortedKeys, mem_keys]

omit [DecidableEq P] [LinearOrder T] in
theorem nodup_keys : h.keys.Nodup := by
  unfold keys
  rw [List.nodup_flatMap]
  refine ⟨fun p _ => ?_, ?_⟩
  · rw [List.nodup_append]
    refine ⟨List.nodup_range.map (fun a b hab => by simpa using hab),
      List.nodup_range.map (fun a b hab => by simpa using hab), ?_⟩
    simp
  · refine (Finset.nodup_toList _).pairwise_of_forall_ne fun p _ q _ hpq => ?_
    simp only [Function.onFun, List.disjoint_left, List.mem_append, List.mem_map, List.mem_range]
    rintro x (⟨k, _, rfl⟩ | ⟨k, _, rfl⟩) (⟨j, _, hj⟩ | ⟨j, _, hj⟩) <;> simp_all

omit [DecidableEq P] in
theorem pairwise_sortedKeys (hw : h.WF) :
    h.sortedKeys.Pairwise (fun x y => h.time x < h.time y) := by
  have h1 : h.sortedKeys.Pairwise (fun x y => decide (h.time x ≤ h.time y) = true) :=
    List.pairwise_mergeSort (fun a b c hab hbc => by simp at *; exact le_trans hab hbc)
      (fun a b => by simpa using le_total _ _) _
  have hnd : h.sortedKeys.Nodup := (List.mergeSort_perm _ _).nodup_iff.2 nodup_keys
  refine (h1.and hnd).imp_of_mem fun hx hy hxy => lt_of_le_of_ne (by simpa using hxy.1) ?_
  exact fun he => hxy.2 (hw.inj _ _ (mem_sortedKeys.1 hx) (mem_sortedKeys.1 hy) he)

omit [DecidableEq P] in
theorem filter_sortedKeys_eq (hw : h.WF) (q : Key P → Bool) {l : List (Key P)}
    (hl : l.Pairwise (fun x y => h.time x < h.time y))
    (hmem : ∀ x, x ∈ l ↔ h.Valid x ∧ q x = true) :
    h.sortedKeys.filter q = l :=
  eq_of_pairwise_lt h.time ((pairwise_sortedKeys hw).filter q) hl fun x => by
    rw [List.mem_filter, mem_sortedKeys, hmem]

/-! ### The events of one process -/

/-- The `n`-th event key of process `p`: invocations at even, responses at odd ranks. -/
def pkey (p : P) (n : ℕ) : Key P := (p, n / 2, decide (n % 2 = 1))

omit [Fintype P] [DecidableEq P] in
theorem pkey_two_mul (p : P) (k : ℕ) : pkey p (2 * k) = (p, k, false) := by
  have e1 : 2 * k / 2 = k := by omega
  simp [pkey, e1]

omit [Fintype P] [DecidableEq P] in
theorem pkey_two_mul_add_one (p : P) (k : ℕ) : pkey p (2 * k + 1) = (p, k, true) := by
  have e1 : (2 * k + 1) / 2 = k := by omega
  have e2 : (2 * k + 1) % 2 = 1 := by omega
  simp [pkey, e1, e2]

omit [Fintype P] [DecidableEq P] in
theorem valid_pkey_iff (hw : h.WF) (p : P) (n : ℕ) :
    h.Valid (pkey p n) ↔ n < h.m p + h.c p := by
  have := hw.c_le_m p
  have := hw.m_le_c p
  rcases Nat.mod_two_eq_zero_or_one n with h0 | h0
  · obtain ⟨k, rfl⟩ : ∃ k, n = 2 * k := ⟨n / 2, by omega⟩
    rw [pkey_two_mul, valid_inv]; omega
  · obtain ⟨k, rfl⟩ : ∃ k, n = 2 * k + 1 := ⟨n / 2, by omega⟩
    rw [pkey_two_mul_add_one, valid_res]; omega

omit [Fintype P] [DecidableEq P] in
theorem time_pkey_lt_succ (hw : h.WF) (p : P) {n : ℕ} (hn : n + 1 < h.m p + h.c p) :
    h.time (pkey p n) < h.time (pkey p (n + 1)) := by
  have := hw.c_le_m p
  have := hw.m_le_c p
  rcases Nat.mod_two_eq_zero_or_one n with h0 | h0
  · obtain ⟨k, rfl⟩ : ∃ k, n = 2 * k := ⟨n / 2, by omega⟩
    rw [pkey_two_mul, pkey_two_mul_add_one, time_inv, time_res]
    exact hw.inv_lt_res p k (by omega)
  · obtain ⟨k, rfl⟩ : ∃ k, n = 2 * k + 1 := ⟨n / 2, by omega⟩
    rw [pkey_two_mul_add_one, show 2 * k + 1 + 1 = 2 * (k + 1) by ring, pkey_two_mul, time_inv,
      time_res]
    exact hw.res_lt_inv p k (by omega)

omit [Fintype P] [DecidableEq P] in
theorem time_pkey_lt (hw : h.WF) (p : P) {n n' : ℕ} (hlt : n < n') (hn' : n' < h.m p + h.c p) :
    h.time (pkey p n) < h.time (pkey p n') := by
  induction n' with
  | zero => omega
  | succ n' ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.1 hlt with h1 | h1
    · exact (ih h1 (by omega)).trans (time_pkey_lt_succ hw p hn')
    · subst h1; exact time_pkey_lt_succ hw p hn'

omit [Fintype P] [DecidableEq P] in
theorem ti_lt_ti (hw : h.WF) {p : P} {k k' : ℕ} (hk : k < k') (hk' : k' < h.m p) :
    h.ti p k < h.ti p k' := by
  have := hw.c_le_m p
  have := hw.m_le_c p
  have := time_pkey_lt hw p (n := 2 * k) (n' := 2 * k') (by omega) (by omega)
  rwa [pkey_two_mul, pkey_two_mul] at this

omit [Fintype P] [DecidableEq P] in
theorem tr_lt_tr (hw : h.WF) {p : P} {k k' : ℕ} (hk : k < k') (hk' : k' < h.c p) :
    h.tr p k < h.tr p k' := by
  have := hw.c_le_m p
  have := time_pkey_lt hw p (n := 2 * k + 1) (n' := 2 * k' + 1) (by omega) (by omega)
  rwa [pkey_two_mul_add_one, pkey_two_mul_add_one] at this

/-- The event keys of process `p`, in their order. -/
def procKeys (h : TH P Op R T) (p : P) : List (Key P) := (List.range (h.m p + h.c p)).map (pkey p)

theorem filter_proc (hw : h.WF) (p : P) :
    h.sortedKeys.filter (fun x => decide (x.1 = p)) = h.procKeys p := by
  apply filter_sortedKeys_eq hw
  · unfold procKeys
    rw [List.pairwise_map]
    exact List.pairwise_lt_range.imp_of_mem fun _ hb hab =>
      time_pkey_lt hw p hab (List.mem_range.1 hb)
  · rintro ⟨q, k, b⟩
    simp only [procKeys, List.mem_map, List.mem_range, decide_eq_true_eq]
    constructor
    · rintro ⟨n, hn, he⟩
      have hv := (valid_pkey_iff hw p n).2 hn
      rw [he] at hv
      refine ⟨hv, ?_⟩
      have : (pkey p n).1 = p := rfl
      rw [he] at this
      exact this
    · rintro ⟨hv, rfl⟩
      cases b
      · exact ⟨2 * k, (valid_pkey_iff hw q _).1 (by rwa [pkey_two_mul]), pkey_two_mul q k⟩
      · exact ⟨2 * k + 1, (valid_pkey_iff hw q _).1 (by rwa [pkey_two_mul_add_one]),
          pkey_two_mul_add_one q k⟩

omit [Fintype P] [DecidableEq P] [LinearOrder T] in
theorem event_proc (x : Key P) : (h.event x).proc = x.1 := by
  unfold event; split <;> rfl

theorem restrictP_toList (hw : h.WF) (p : P) :
    restrictP h.toList p = (h.procKeys p).map h.event := by
  unfold restrictP
  rw [toList_def, List.filter_map, ← filter_proc hw p]
  congr 1
  apply List.filter_congr
  intro x _
  simp [event_proc]

omit [Fintype P] [DecidableEq P] in
theorem isSeq_procKeys (hw : h.WF) (p : P) : IsSeq ((h.procKeys p).map h.event) := by
  let M : List (OpRec P Unit Op R) :=
    (List.range (h.c p)).map (fun k => ⟨p, (), h.op p k, h.res p k⟩)
  have hM : (List.range (2 * h.c p)).map (h.event ∘ pkey p) = seqHist M := by
    rw [map_range_two_mul]
    simp only [seqHist, M, List.flatMap_map]
    congr 1
    funext k
    simp [pkey_two_mul, pkey_two_mul_add_one, OpRec.events]
  refine ⟨M, ?_⟩
  unfold procKeys
  rw [List.map_map]
  rcases (hw.c_le_m p).eq_or_lt with hc | hc
  · left
    rw [← hc, ← two_mul]
    exact hM
  · right
    refine ⟨p, (), h.op p (h.c p), ?_⟩
    have : h.m p + h.c p = 2 * h.c p + 1 := by have := hw.m_le_c p; omega
    rw [this, List.range_succ, List.map_append, hM]
    simp [pkey_two_mul]

theorem wellFormed_toList (hw : h.WF) : WellFormed h.toList := fun p => by
  rw [restrictP_toList hw p]
  exact isSeq_procKeys hw p

/-! ### Operations and responses of one process -/

omit [Fintype P] [LinearOrder T] in
theorem opsOf_map_event (L : List (Key P)) (p : P) :
    opsOf (L.map h.event) p () =
      (L.filter (fun x => decide (x.1 = p) && !x.2.2)).map (fun x => h.op p x.2.1) := by
  unfold opsOf
  rw [List.filterMap_map]
  apply filterMap_eq_map_filter_of
  rintro ⟨q, k, b⟩
  by_cases hq : q = p
  · subst hq; cases b <;> simp
  · cases b <;> simp [hq]

omit [Fintype P] [LinearOrder T] in
theorem ressOf_map_event (L : List (Key P)) (p : P) :
    ressOf (L.map h.event) p () =
      (L.filter (fun x => decide (x.1 = p) && x.2.2)).map (fun x => h.res p x.2.1) := by
  unfold ressOf
  rw [List.filterMap_map]
  apply filterMap_eq_map_filter_of
  rintro ⟨q, k, b⟩
  by_cases hq : q = p
  · subst hq; cases b <;> simp
  · cases b <;> simp [hq]

theorem filter_inv (hw : h.WF) (p : P) :
    h.sortedKeys.filter (fun x => decide (x.1 = p) && !x.2.2) =
      (List.range (h.m p)).map (fun k => (p, k, false)) := by
  apply filter_sortedKeys_eq hw
  · rw [List.pairwise_map]
    exact List.pairwise_lt_range.imp_of_mem fun _ hb hab => by
      simpa using ti_lt_ti hw hab (List.mem_range.1 hb)
  · rintro ⟨q, k, b⟩
    cases b
    · simp only [List.mem_map, List.mem_range, Prod.mk.injEq, valid_inv, Bool.not_false,
        Bool.and_true, decide_eq_true_eq, and_true]
      constructor
      · rintro ⟨j, hj, rfl, rfl⟩; exact ⟨hj, rfl⟩
      · rintro ⟨hk, rfl⟩; exact ⟨k, hk, rfl, rfl⟩
    · simp

theorem filter_res (hw : h.WF) (p : P) :
    h.sortedKeys.filter (fun x => decide (x.1 = p) && x.2.2) =
      (List.range (h.c p)).map (fun k => (p, k, true)) := by
  apply filter_sortedKeys_eq hw
  · rw [List.pairwise_map]
    exact List.pairwise_lt_range.imp_of_mem fun _ hb hab => by
      simpa using tr_lt_tr hw hab (List.mem_range.1 hb)
  · rintro ⟨q, k, b⟩
    cases b
    · simp
    · simp only [List.mem_map, List.mem_range, Prod.mk.injEq, valid_res,
        Bool.and_true, decide_eq_true_eq, and_true]
      constructor
      · rintro ⟨j, hj, rfl, rfl⟩; exact ⟨hj, rfl⟩
      · rintro ⟨hk, rfl⟩; exact ⟨k, hk, rfl, rfl⟩

theorem opsOf_toList (hw : h.WF) (p : P) :
    opsOf h.toList p () = (List.range (h.m p)).map (h.op p) := by
  rw [toList_def, opsOf_map_event, filter_inv hw, List.map_map]
  rfl

theorem ressOf_toList (hw : h.WF) (p : P) :
    ressOf h.toList p () = (List.range (h.c p)).map (h.res p) := by
  rw [toList_def, ressOf_map_event, filter_res hw, List.map_map]
  rfl

theorem invoked_toList (hw : h.WF) {a : OpId P Unit} : Invoked h.toList a ↔ a.k < h.m a.p := by
  obtain ⟨p, ⟨⟩, k⟩ := a
  simp [Invoked, opsOf_toList hw]

theorem completed_toList (hw : h.WF) {a : OpId P Unit} :
    Completed h.toList a ↔ a.k < h.c a.p := by
  obtain ⟨p, ⟨⟩, k⟩ := a
  simp [Completed, ressOf_toList hw]

theorem opOf_toList (hw : h.WF) {a : OpId P Unit} (ha : a.k < h.m a.p) :
    opOf h.toList a = some (h.op a.p a.k) := by
  obtain ⟨p, ⟨⟩, k⟩ := a
  simp [opOf, opsOf_toList hw, ha]

theorem resOf_toList (hw : h.WF) {a : OpId P Unit} (ha : a.k < h.c a.p) :
    resOf h.toList a = some (h.res a.p a.k) := by
  obtain ⟨p, ⟨⟩, k⟩ := a
  simp [resOf, ressOf_toList hw, ha]

/-! ### Real-time order -/

omit [Fintype P] in
theorem precedes_map_iff {α : Type*} (ev : α → Event P Unit Op R) (L : List α)
    (a b : OpId P Unit) :
    Precedes (L.map ev) a b ↔
      ∃ n, Completed ((L.take n).map ev) a ∧ ¬ Invoked ((L.take n).map ev) b := by
  constructor
  · rintro ⟨β, γ, hβγ, hc, hi⟩
    refine ⟨β.length, ?_⟩
    have : (L.take β.length).map ev = β := by
      rw [List.map_take, hβγ, List.take_left]
    rw [this]
    exact ⟨hc, hi⟩
  · rintro ⟨n, hc, hi⟩
    exact ⟨_, (L.drop n).map ev, by rw [← List.map_append, List.take_append_drop], hc, hi⟩

theorem completed_take_iff_mem (hw : h.WF) (n : ℕ) (a : OpId P Unit) :
    Completed ((h.sortedKeys.take n).map h.event) a ↔ (a.p, a.k, true) ∈ h.sortedKeys.take n := by
  obtain ⟨p, ⟨⟩, k⟩ := a
  unfold Completed
  rw [ressOf_map_event, List.length_map]
  have hpre : (h.sortedKeys.take n).filter (fun x => decide (x.1 = p) && x.2.2) <+:
      (List.range (h.c p)).map (fun k => (p, k, true)) := by
    rw [← filter_res hw p]
    exact (List.take_prefix _ _).filter _
  rw [lt_length_iff_of_prefix_map_range (fun a b hab => by simpa using hab) hpre, List.mem_filter]
  simp

theorem invoked_take_iff_mem (hw : h.WF) (n : ℕ) (a : OpId P Unit) :
    Invoked ((h.sortedKeys.take n).map h.event) a ↔ (a.p, a.k, false) ∈ h.sortedKeys.take n := by
  obtain ⟨p, ⟨⟩, k⟩ := a
  unfold Invoked
  rw [opsOf_map_event, List.length_map]
  have hpre : (h.sortedKeys.take n).filter (fun x => decide (x.1 = p) && !x.2.2) <+:
      (List.range (h.m p)).map (fun k => (p, k, false)) := by
    rw [← filter_inv hw p]
    exact (List.take_prefix _ _).filter _
  rw [lt_length_iff_of_prefix_map_range (fun a b hab => by simpa using hab) hpre, List.mem_filter]
  simp

/-- Real-time order of `toList h` is the order of the times. -/
theorem precedes_toList (hw : h.WF) {a b : OpId P Unit} :
    Precedes h.toList a b ↔
      a.k < h.c a.p ∧ (b.k < h.m b.p → h.tr a.p a.k < h.ti b.p b.k) := by
  rw [toList_def, precedes_map_iff]
  simp only [completed_take_iff_mem hw, invoked_take_iff_mem hw]
  have hs := pairwise_sortedKeys hw
  constructor
  · rintro ⟨n, hx, hy⟩
    have hxv : h.Valid (a.p, a.k, true) := mem_sortedKeys.1 (List.mem_of_mem_take hx)
    refine ⟨hxv, fun hb => ?_⟩
    have hyv : (b.p, b.k, false) ∈ h.sortedKeys := mem_sortedKeys.2 hb
    rw [← List.take_append_drop n h.sortedKeys] at hyv hs
    rcases List.mem_append.1 hyv with hy' | hy'
    · exact absurd hy' hy
    · rw [List.pairwise_append] at hs
      simpa using hs.2.2 _ hx _ hy'
  · rintro ⟨ha, hb⟩
    have hxm : (a.p, a.k, true) ∈ h.sortedKeys := mem_sortedKeys.2 ha
    obtain ⟨s, t, hst⟩ := List.append_of_mem hxm
    refine ⟨s.length + 1, ?_, ?_⟩
    · rw [hst, List.take_append]; simp
    · intro hy
      have hyv : b.k < h.m b.p := mem_sortedKeys.1 (List.mem_of_mem_take hy)
      have hlt := hb hyv
      have htk : (s ++ (a.p, a.k, true) :: t).take (s.length + 1) = s ++ [(a.p, a.k, true)] := by
        rw [List.take_append]; simp
      rw [hst, htk] at hy
      rw [hst, List.pairwise_append] at hs
      rcases List.mem_append.1 hy with hy' | hy'
      · have := hs.2.2 _ hy' (a.p, a.k, true) (by simp)
        simp only [time_inv, time_res] at this
        exact lt_asymm hlt this
      · simp at hy'

/-! ## Truncation -/

/-- The events strictly before time `t`. -/
def cut (h : TH P Op R T) (t : T) : TH P Op R T :=
  { h with
    m := fun p => ((List.range (h.m p)).filter (fun k => decide (h.ti p k < t))).length
    c := fun p => ((List.range (h.c p)).filter (fun k => decide (h.tr p k < t))).length }

omit [Fintype P] [DecidableEq P] in
theorem cut_m_iff' (hw : h.WF) (t : T) (p : P) (k : ℕ) :
    k < (h.cut t).m p ↔ k < h.m p ∧ h.ti p k < t := by
  show k < ((List.range (h.m p)).filter (fun k => decide (h.ti p k < t))).length ↔ _
  rw [lt_length_filter_range _ (fun k k' hkk' hk' hq => by
    simp only [decide_eq_true_eq] at hq ⊢
    exact (ti_lt_ti hw hkk' hk').trans hq)]
  simp

omit [Fintype P] [DecidableEq P] in
theorem cut_c_iff' (hw : h.WF) (t : T) (p : P) (k : ℕ) :
    k < (h.cut t).c p ↔ k < h.c p ∧ h.tr p k < t := by
  show k < ((List.range (h.c p)).filter (fun k => decide (h.tr p k < t))).length ↔ _
  rw [lt_length_filter_range _ (fun k k' hkk' hk' hq => by
    simp only [decide_eq_true_eq] at hq ⊢
    exact (tr_lt_tr hw hkk' hk').trans hq)]
  simp

omit [Fintype P] [DecidableEq P] in
theorem valid_cut_iff (hw : h.WF) (t : T) (x : Key P) :
    (h.cut t).Valid x ↔ h.Valid x ∧ h.time x < t := by
  obtain ⟨p, k, b⟩ := x
  cases b
  · exact cut_m_iff' hw t p k
  · exact cut_c_iff' hw t p k

theorem WF.cut (hw : h.WF) (t : T) : (h.cut t).WF where
  c_le_m p := by
    by_contra hcon
    push Not at hcon
    have h1 := (cut_c_iff' hw t p ((h.cut t).m p)).1 hcon
    have h2 : (h.cut t).m p < (h.cut t).m p :=
      (cut_m_iff' hw t p _).2 ⟨by have := hw.c_le_m p; omega, (hw.inv_lt_res p _ h1.1).trans h1.2⟩
    exact lt_irrefl _ h2
  m_le_c p := by
    by_contra hcon
    push Not at hcon
    have h1 := (cut_m_iff' hw t p ((h.cut t).c p + 1)).1 (by omega)
    have hjc : (h.cut t).c p < h.c p := by have := hw.m_le_c p; omega
    have h2 : (h.cut t).c p < (h.cut t).c p :=
      (cut_c_iff' hw t p _).2 ⟨hjc, (hw.res_lt_inv p _ h1.1).trans h1.2⟩
    exact lt_irrefl _ h2
  inv_lt_res p k hk := hw.inv_lt_res p k ((cut_c_iff' hw t p k).1 hk).1
  res_lt_inv p k hk := hw.res_lt_inv p k ((cut_m_iff' hw t p _).1 hk).1
  inj x y hx hy he :=
    hw.inj x y ((valid_cut_iff hw t x).1 hx).1 ((valid_cut_iff hw t y).1 hy).1 he

/-- `k < (h.cut t).m p` iff the `k`-th operation of `p` was invoked before `t`. -/
theorem cut_m_iff (hw : h.WF) (t : T) (p : P) (k : ℕ) :
    k < (h.cut t).m p ↔ k < h.m p ∧ h.ti p k < t :=
  cut_m_iff' hw t p k

theorem cut_c_iff (hw : h.WF) (t : T) (p : P) (k : ℕ) :
    k < (h.cut t).c p ↔ k < h.c p ∧ h.tr p k < t :=
  cut_c_iff' hw t p k

theorem sortedKeys_cut (hw : h.WF) (t : T) :
    (h.cut t).sortedKeys = h.sortedKeys.filter (fun x => decide (h.time x < t)) := by
  symm
  apply filter_sortedKeys_eq hw
  · exact pairwise_sortedKeys (hw.cut t)
  · intro x
    rw [mem_sortedKeys, valid_cut_iff hw t, decide_eq_true_eq]

/-- Truncating a timed history yields a prefix of its list history. -/
theorem toList_cut_prefix (hw : h.WF) (t : T) : (h.cut t).toList <+: h.toList := by
  show (h.cut t).sortedKeys.map h.event <+: h.sortedKeys.map h.event
  rw [sortedKeys_cut hw t]
  exact (filter_lt_prefix h.time t (pairwise_sortedKeys hw)).map h.event

/-! ## Changing responses, changing times -/

/-- Map the responses. -/
def mapRes {R' : Type} (h : TH P Op R T) (f : R → R') : TH P Op R' T :=
  { h with res := fun p k => f (h.res p k) }

/-- Map the responses of a history event. -/
def evMap {R' : Type} (f : R → R') : Event P Unit Op R → Event P Unit Op R'
  | .inv p x o => .inv p x o
  | .res p x r => .res p x (f r)

theorem WF.mapRes {R' : Type} (hw : h.WF) (f : R → R') : (h.mapRes f).WF :=
  ⟨hw.1, hw.2, hw.3, hw.4, hw.5⟩

theorem toList_mapRes {R' : Type} (f : R → R') : (h.mapRes f).toList = h.toList.map (evMap f) := by
  show h.sortedKeys.map (h.mapRes f).event = (h.sortedKeys.map h.event).map (evMap f)
  rw [List.map_map]
  apply List.map_congr_left
  rintro ⟨p, k, b⟩ _
  cases b <;> rfl

/-- The list history depends only on the relative order of the times. -/
theorem toList_eq_of_iso {T' : Type} [LinearOrder T'] {h' : TH P Op R T'} (hw : h.WF)
    (hw' : h'.WF) (hm : ∀ p, h.m p = h'.m p) (hc : ∀ p, h.c p = h'.c p)
    (hop : ∀ p k, k < h.m p → h.op p k = h'.op p k)
    (hres : ∀ p k, k < h.c p → h.res p k = h'.res p k)
    (hlt : ∀ x y, h.Valid x → h.Valid y → (h.time x < h.time y ↔ h'.time x < h'.time y)) :
    h.toList = h'.toList := by
  have hv : ∀ x, h'.Valid x ↔ h.Valid x := by
    rintro ⟨p, k, b⟩; cases b <;> simp [hm, hc]
  have hs : h'.sortedKeys = h.sortedKeys := by
    symm
    apply eq_of_pairwise_lt h.time (pairwise_sortedKeys hw)
    · exact (pairwise_sortedKeys hw').imp_of_mem fun hx hy hxy =>
        (hlt _ _ ((hv _).1 (mem_sortedKeys.1 hx)) ((hv _).1 (mem_sortedKeys.1 hy))).2 hxy
    · intro x
      rw [mem_sortedKeys, mem_sortedKeys, hv]
  rw [toList_def, toList_def, hs]
  apply List.map_congr_left
  rintro ⟨p, k, b⟩ hx
  have hxv := mem_sortedKeys.1 hx
  cases b
  · simp [hop p k hxv]
  · simp [hres p k hxv]

/-! ## Similarity of timed histories -/

/-- Timed version of `SimS`. -/
structure SimTH {T' : Type} [LinearOrder T'] (h : TH P Op R T) (h' : TH P Op R T') : Prop where
  m_le : ∀ p, h'.m p ≤ h.m p
  op_eq : ∀ p k, k < h'.m p → h.op p k = h'.op p k
  c_le : ∀ p, h.c p ≤ h'.c p
  res_eq : ∀ p k, k < h.c p → h.res p k = h'.res p k
  prec : ∀ p k q j, k < h.c p → j < h'.m q → h.tr p k < h.ti q j → h'.tr p k < h'.ti q j

theorem SimTH.simS {T' : Type} [LinearOrder T'] {h' : TH P Op R T'} (hw : h.WF) (hw' : h'.WF)
    (hs : SimTH h h') : SimS h.toList h'.toList where
  wfE := wellFormed_toList hw
  wfF := wellFormed_toList hw'
  op_eq a ha := by
    rw [invoked_toList hw'] at ha
    rw [opOf_toList hw (lt_of_lt_of_le ha (hs.m_le _)), opOf_toList hw' ha, hs.op_eq _ _ ha]
  res_eq a ha := by
    rw [completed_toList hw] at ha
    rw [resOf_toList hw ha, resOf_toList hw' (lt_of_lt_of_le ha (hs.c_le _)), hs.res_eq _ _ ha]
  prec a b hab hb := by
    rw [precedes_toList hw] at hab
    rw [invoked_toList hw'] at hb
    rw [precedes_toList hw']
    exact ⟨lt_of_lt_of_le hab.1 (hs.c_le _), fun _ =>
      hs.prec _ _ _ _ hab.1 hb (hab.2 (lt_of_lt_of_le hb (hs.m_le _)))⟩

theorem SimTH.mapRes {T' : Type} [LinearOrder T'] {h' : TH P Op R T'} {R' : Type} (f : R → R')
    (hs : SimTH h h') : SimTH (h.mapRes f) (h'.mapRes f) where
  m_le := hs.m_le
  op_eq := hs.op_eq
  c_le := hs.c_le
  res_eq p k hk := by simp only [TH.mapRes]; rw [hs.res_eq p k hk]
  prec := hs.prec

/-- A timed history without events has the empty list history. -/
theorem toList_eq_nil (hm : ∀ p, h.m p = 0) (hc : ∀ p, h.c p = 0) : h.toList = [] := by
  have hk : h.keys = [] := by simp [keys, hm, hc]
  rw [toList, hk, List.mergeSort_nil, List.map_nil]

end TH

end Podc2023.RuntimeVerification
