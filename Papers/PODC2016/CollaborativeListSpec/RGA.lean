import Papers.PODC2016.CollaborativeListSpec.Spec
import Papers.PODC2016.CollaborativeListSpec.TITree
import Papers.PODC2016.CollaborativeListSpec.HBLemmas

/-!
# The RGA protocol (Section 4.2) and Theorem 1

The state of a replica is `(N, T)` (a TI tree and a tombstone set) plus the send buffer `(A, K)`
(`none` stands for `(∅, ∅)`). Timestamps are `(x, i)` with `x` one more than the largest first
component in `N` and `i` the replica id.

**Correction.** The paper builds the new node "as described in the Insert procedure of
Section 4.1", which takes the parent at position `k - 1` of `s(N)`, i.e. counting tombstones. Then
condition (1c) fails (`RGALiteral.lean`). We take the parent at position `min k n - 1` of the
*visible* list `s(N) \ T` (of length `n`), as in the original RGA and as the positions of
`ins(a, k)` (Section 3) refer to the user-visible list.

**Proof structure.** `Inv` (Lemmas 3 and 4): the tree (tombstones) of replica `r` after a prefix
consists of the nodes (elements) of the inserts (deletes) that happen before or are an event of
`r` in that prefix, and the send buffer holds those of `r`'s updates since its last send
(`inv`, using causal broadcast through `known_succ_recv`). Lemma 5: the nodes of all inserts form
a TI tree `Nall` (`isTITree_Nall`) and every replica tree is a sub-TI tree (`isTITree_st`). The
list order is `lo a b :↔ [a, b]` is a subsequence of `s(Nall)`; Lemma 6 (`s_sublist`) gives (1b),
`s_cons_max` gives (1c) (`ins_resp`).
-/

namespace Podc.CollaborativeListSpec

namespace RGA

variable {U : Type} [DecidableEq U] {n : ℕ}

/-- Internal state `(N, T)`. -/
abbrev St (U : Type) := List (Node U) × List U

/-- Messages `(A, K)`. -/
abbrev Msg (U : Type) := List (Node U) × List U

/-- The largest first timestamp component in `N` (`0` if `N = ∅`). -/
def maxX (N : List (Node U)) : ℕ := (N.map fun m => (ofLex m.t).1).foldr max 0

/-- The timestamp of a new node at replica `i`. -/
def newTS (N : List (Node U)) (i : Fin n) : TS := toLex (maxX N + 1, i.val)

/-- The user-visible list `s(N) \ T`. -/
def visible (q : St U) : List U := (s q.1).filter (· ∉ q.2)

/-- The parent for `ins(a, k)`: the visible element at position `min k n - 1`, or the root. -/
def parentFor (q : St U) (k : ℕ) : Option U :=
  if min k (visible q).length = 0 then none else (visible q)[min k (visible q).length - 1]?

/-- The node created by `ins(a, k)` at replica `i` in state `q`. -/
def newNode (q : St U) (i : Fin n) (a : U) (k : ℕ) : Node U := ⟨a, newTS q.1 i, parentFor q k⟩

/-- The protocol `R_rga^n` (with the corrected insert). -/
def protocol (U : Type) [DecidableEq U] (n : ℕ) : Protocol (Fin n) (LOp U) (List U) (St U) (Msg U) where
  init _ := ([], [])
  resp i σ
    | .ins a k => visible (newNode σ.1 i a k :: σ.1.1, σ.1.2)
    | .del a => visible (σ.1.1, a :: σ.1.2)
    | .read => visible σ.1
  doStep i σ
    | .ins a k =>
      let m := newNode σ.1 i a k
      ((m :: σ.1.1, σ.1.2), some ((σ.2.getD ([], [])).1 ++ [m], (σ.2.getD ([], [])).2))
    | .del a => ((σ.1.1, a :: σ.1.2), some ((σ.2.getD ([], [])).1, (σ.2.getD ([], [])).2 ++ [a]))
    | .read => σ
  sendStep _ σ := σ.1
  recvStep _ σ m := ((m.1.union σ.1.1, σ.1.2 ++ m.2), σ.2)

variable (U n)

/-- The executions considered for RGA: causal broadcast and the user assumptions. -/
def Adm (α : List (Act (Fin n) (LOp U))) : Prop :=
  CausalBroadcast α ∧ UserOK (protocol U n) α

variable {U n}

/-! ### List lemmas -/

theorem insAfter_nil (p : Option U) (x : U) : insAfter p x [] = if p = none then [x] else [] := by
  cases p <;> simp [insAfter]

theorem insAfter_some_cons (b x y : U) (l : List U) :
    insAfter (some b) x (y :: l) = if y = b then y :: x :: l else y :: insAfter (some b) x l := by
  simp only [insAfter]
  by_cases hyb : y = b
  · subst hyb; simp [List.idxOf?_cons]
  · simp only [hyb, ↓reduceIte]
    rw [List.idxOf?_cons]; simp only [beq_iff_eq, hyb, ↓reduceIte]
    cases List.idxOf? b l <;> simp

/-- Filtering commutes with insertion after a kept element. -/
theorem filter_insAfter (f : U → Bool) {b x : U} (hb : f b) (hx : f x) (l : List U) :
    (insAfter (some b) x l).filter f = insAfter (some b) x (l.filter f) := by
  induction l with
  | nil => simp [insAfter_nil]
  | cons y l ih =>
    rw [insAfter_some_cons]
    by_cases hyb : y = b
    · subst hyb; simp [hb, hx, insAfter_some_cons]
    · simp only [hyb, ↓reduceIte]; rw [List.filter_cons, List.filter_cons, ih]
      split_ifs <;> simp [insAfter_some_cons, hyb]

theorem insertIdx_eq_insAfter {v : List U} (hv : v.Nodup) (x : U) {j : ℕ} (hj0 : 0 < j)
    (hj : j ≤ v.length) : v.insertIdx j x = insAfter (some (v[j - 1]'(by omega))) x v := by
  induction v generalizing j with
  | nil => simp at hj; omega
  | cons y v ih =>
    obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    rcases j with _ | j
    · simp [insAfter_some_cons]
    · simp only [Nat.add_sub_cancel, List.getElem_cons_succ, List.insertIdx_succ_cons]
      have hjv : j < v.length := by simp at hj; omega
      have hne : y ≠ v[j] := fun h => (List.nodup_cons.1 hv).1 (h ▸ List.getElem_mem _)
      rw [insAfter_some_cons, ih hv.of_cons (by omega) (by simp at hj; omega)]
      simp [hne]

omit [DecidableEq U] in
/-- `[a, b]` as a sublist of a cons. -/
theorem pair_sublist_cons {a b x : U} {l : List U} :
    List.Sublist [a, b] (x :: l) ↔ (a = x ∧ b ∈ l) ∨ List.Sublist [a, b] l := by
  rw [List.sublist_cons_iff]
  constructor
  · rintro (h | ⟨r, hr, h⟩)
    · exact Or.inr h
    · simp only [List.cons.injEq] at hr; obtain ⟨rfl, rfl⟩ := hr
      exact Or.inl ⟨rfl, List.singleton_sublist.1 h⟩
  · rintro (⟨rfl, h⟩ | h)
    · exact Or.inr ⟨[b], rfl, List.singleton_sublist.2 h⟩
    · exact Or.inl h

omit [DecidableEq U] in
theorem pair_sublist_trans {l : List U} (hl : l.Nodup) {a b c : U} (hab : List.Sublist [a, b] l)
    (hbc : List.Sublist [b, c] l) : List.Sublist [a, c] l := by
  induction l with
  | nil => simp at hab
  | cons x l ih =>
    have hx := (List.nodup_cons.1 hl).1
    rw [pair_sublist_cons] at hab hbc ⊢
    rcases hab with ⟨rfl, hb⟩ | hab
    · rcases hbc with ⟨rfl, -⟩ | hbc
      · exact absurd hb hx
      · exact Or.inl ⟨rfl, List.singleton_sublist.1 ((List.sublist_cons_self _ _).trans hbc |>.trans
          (by simp))⟩
    · rcases hbc with ⟨rfl, -⟩ | hbc
      · exact absurd (List.singleton_sublist.1 ((List.sublist_cons_self _ _).trans hab |>.trans
          (by simp))) hx
      · exact Or.inr (ih hl.of_cons hab hbc)

omit [DecidableEq U] in
theorem pair_sublist_total {l : List U} {a b : U} (ha : a ∈ l) (hb : b ∈ l) (hab : a ≠ b) :
    List.Sublist [a, b] l ∨ List.Sublist [b, a] l := by
  induction l with
  | nil => simp at ha
  | cons x l ih =>
    simp only [pair_sublist_cons]
    rcases List.mem_cons.1 ha with hax | hal
    · exact Or.inl (Or.inl ⟨hax, (List.mem_cons.1 hb).resolve_left (hax ▸ Ne.symm hab)⟩)
    rcases List.mem_cons.1 hb with hbx | hbl
    · exact Or.inr (Or.inl ⟨hbx, hal⟩)
    rcases ih hal hbl with h | h
    · exact Or.inl (Or.inr h)
    · exact Or.inr (Or.inr h)

/-- Elements of `s N` are elements of nodes of `N` (for any list of nodes). -/
theorem exists_of_mem_walk {N : List (Node U)} {p : Option U} {t : WithBot TS} {a : U}
    (h : a ∈ walk N p t) : ∃ x ∈ N, x.a = a := by
  induction p, t using walk.induct N with
  | case1 p t ih =>
    rw [walk] at h
    obtain ⟨m, -, hm⟩ := List.mem_flatMap.1 h
    rcases List.mem_cons.1 hm with rfl | hm
    · exact ⟨m.1, (mem_children.1 m.2).1, rfl⟩
    · exact ih m hm

/-! ### Timestamps -/

omit [DecidableEq U] in
theorem le_maxX {N : List (Node U)} {x : Node U} (hx : x ∈ N) : (ofLex x.t).1 ≤ maxX N := by
  induction N with
  | nil => simp at hx
  | cons y N ih =>
    simp only [maxX, List.map_cons, List.foldr_cons] at *
    rcases List.mem_cons.1 hx with rfl | hx
    · exact le_max_left _ _
    · exact (ih hx).trans (le_max_right _ _)

@[simp] theorem newNode_a (q : St U) (i : Fin n) (a : U) (k : ℕ) : (newNode q i a k).a = a := rfl

@[simp] theorem newNode_p (q : St U) (i : Fin n) (a : U) (k : ℕ) :
    (newNode q i a k).p = parentFor q k := rfl

theorem newNode_t (q : St U) (i : Fin n) (a : U) (k : ℕ) :
    (newNode q i a k).t = toLex (maxX q.1 + 1, i.val) := rfl

theorem t_lt_of_fst_lt {t t' : TS} (h : (ofLex t).1 < (ofLex t').1) : t < t' :=
  Prod.Lex.lt_iff.2 (Or.inl h)

theorem lt_newNode {q : St U} {x : Node U} (hx : x ∈ q.1) (i : Fin n) (a : U) (k : ℕ) :
    x.t < (newNode q i a k).t :=
  t_lt_of_fst_lt (by rw [newNode_t]; have := le_maxX hx; simp; omega)

/-! ### The invariant (Lemmas 3 and 4) -/

section Inv

variable {α : List (Act (Fin n) (LOp U))}

/-- The node created by the insert at position `q` (if any). -/
def nodeAt (α : List (Act (Fin n) (LOp U))) (q : ℕ) : Option (Node U) :=
  match α[q]? with
  | some (.doOp r (.ins a k)) => some (newNode ((protocol U n).stBefore α q r).1 r a k)
  | _ => none

theorem nodeAt_eq_some {q : ℕ} {x : Node U} : nodeAt α q = some x ↔
    ∃ r a k, α[q]? = some (.doOp r (.ins a k)) ∧
      x = newNode ((protocol U n).stBefore α q r).1 r a k := by
  unfold nodeAt
  split
  · rename_i r a k h; simp [h, eq_comm]
  · rename_i h; simp only [reduceCtorEq, false_iff]; rintro ⟨r, a, k, h', -⟩; exact h r a k h'

theorem nodeAt_of_getElem? {q : ℕ} {r : Fin n} {a : U} {k : ℕ}
    (h : α[q]? = some (.doOp r (.ins a k))) :
    nodeAt α q = some (newNode ((protocol U n).stBefore α q r).1 r a k) :=
  nodeAt_eq_some.2 ⟨r, a, k, h, rfl⟩

/-- The element deleted by the event at position `q` (if any). -/
def delAt (α : List (Act (Fin n) (LOp U))) (q : ℕ) : Option U :=
  match α[q]? with
  | some (.doOp _ (.del b)) => some b
  | _ => none

omit [DecidableEq U] in
theorem delAt_eq_some {q : ℕ} {b : U} : delAt α q = some b ↔ ∃ r, α[q]? = some (.doOp r (.del b)) := by
  unfold delAt
  split
  · rename_i r b' h; simp [h, eq_comm]
  · rename_i h; simp only [reduceCtorEq, false_iff]; rintro ⟨r, h'⟩; exact h r b h'

omit [DecidableEq U] in
theorem delAt_of_getElem? {q : ℕ} {r : Fin n} {b : U} (h : α[q]? = some (.doOp r (.del b))) :
    delAt α q = some b := delAt_eq_some.2 ⟨r, h⟩

omit [DecidableEq U] in
theorem delAt_eq_none {q : ℕ} (h : ∀ r b, α[q]? ≠ some (.doOp r (.del b))) : delAt α q = none := by
  rcases hq : delAt α q with _ | b
  · rfl
  · obtain ⟨r, h'⟩ := delAt_eq_some.1 hq; exact absurd h' (h r b)

theorem nodeAt_eq_none {q : ℕ} (h : ∀ r a k, α[q]? ≠ some (.doOp r (.ins a k))) :
    nodeAt α q = none := by
  rcases hq : nodeAt α q with _ | x
  · rfl
  · obtain ⟨r, a, k, h', -⟩ := nodeAt_eq_some.1 hq; exact absurd h' (h r a k)

/-- The invariant of replica `r` after the first `m` events (Lemmas 3 and 4 of the paper, and
the content of the send buffer). -/
structure Inv (α : List (Act (Fin n) (LOp U))) (m : ℕ) (r : Fin n) : Prop where
  nodup : ((protocol U n).stBefore α m r).1.1.Nodup
  N : ∀ x, x ∈ ((protocol U n).stBefore α m r).1.1 ↔ ∃ q, nodeAt α q = some x ∧ Known α m r q
  T : ∀ b, b ∈ ((protocol U n).stBefore α m r).1.2 ↔ ∃ q, delAt α q = some b ∧ Known α m r q
  A : ∀ x, x ∈ (((protocol U n).stBefore α m r).2.getD ([], [])).1 ↔
    ∃ q, nodeAt α q = some x ∧ Window α m r q
  K : ∀ b, b ∈ (((protocol U n).stBefore α m r).2.getD ([], [])).2 ↔
    ∃ q, delAt α q = some b ∧ Window α m r q

theorem Inv.transfer {m m' : ℕ} {r : Fin n} (h : Inv α m r)
    (hst : (protocol U n).stBefore α m' r = (protocol U n).stBefore α m r)
    (hK : ∀ q, Known α m' r q ↔ Known α m r q) (hW : ∀ q, Window α m' r q ↔ Window α m r q) :
    Inv α m' r := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp only [hst, hK, hW] <;> assumption

theorem stBefore_succ {m : ℕ} {a : Act (Fin n) (LOp U)} (hm : α[m]? = some a) (r : Fin n) :
    (protocol U n).stBefore α (m + 1) r =
      ((protocol U n).step ((protocol U n).exec (α.take m)) a).st r := by
  have : α.take (m + 1) = α.take m ++ [a] := by rw [List.take_add_one, hm]; rfl
  simp [Protocol.stBefore, this]

theorem recvOfSend (hwf : (protocol U n).WF α) : RecvOfSend α := by
  intro c r s h
  have hc : c < α.length := by
    by_contra hc; rw [List.getElem?_eq_none (by omega)] at h; cases h
  have := hwf c hc
  rw [List.getElem?_eq_getElem hc, Option.some.injEq] at h
  rw [h] at this
  exact this

theorem inv_zero (r : Fin n) : Inv α 0 r where
  nodup := by simp [Protocol.stBefore, Protocol.exec, Protocol.init₀, protocol]
  N x := by simp [Protocol.stBefore, Protocol.exec, Protocol.init₀, protocol, Known]
  T b := by simp [Protocol.stBefore, Protocol.exec, Protocol.init₀, protocol, Known]
  A x := by simp [Protocol.stBefore, Protocol.exec, Protocol.init₀, protocol, Window]
  K b := by simp [Protocol.stBefore, Protocol.exec, Protocol.init₀, protocol, Window]

omit [DecidableEq U] in
theorem ex_succ_iff {β : Type} {f : ℕ → Option β} {K K' : ℕ → Prop} {m : ℕ}
    (hK : ∀ q, K' q ↔ K q ∨ q = m) (x : β) :
    (∃ q, f q = some x ∧ K' q) ↔ f m = some x ∨ ∃ q, f q = some x ∧ K q := by
  simp only [hK]
  constructor
  · rintro ⟨q, hq, hk | rfl⟩
    · exact Or.inr ⟨q, hq, hk⟩
    · exact Or.inl hq
  · rintro (h | ⟨q, hq, hk⟩)
    · exact ⟨m, h, Or.inr rfl⟩
    · exact ⟨q, hq, Or.inl hk⟩

omit [DecidableEq U] in
theorem ex_recv_iff {β : Type} {f : ℕ → Option β} {K K' W : ℕ → Prop}
    (hK : ∀ q, (f q).isSome → (K' q ↔ K q ∨ W q)) (x : β) :
    (∃ q, f q = some x ∧ K' q) ↔ (∃ q, f q = some x ∧ W q) ∨ ∃ q, f q = some x ∧ K q := by
  constructor
  · rintro ⟨q, hq, hk⟩
    rcases (hK q (by simp [hq])).1 hk with hk | hk
    · exact Or.inr ⟨q, hq, hk⟩
    · exact Or.inl ⟨q, hq, hk⟩
  · rintro (⟨q, hq, hk⟩ | ⟨q, hq, hk⟩)
    · exact ⟨q, hq, (hK q (by simp [hq])).2 (Or.inr hk)⟩
    · exact ⟨q, hq, (hK q (by simp [hq])).2 (Or.inl hk)⟩

theorem inv_succ_other {m : ℕ} {a : Act (Fin n) (LOp U)} (hm : α[m]? = some a) {r : Fin n}
    (hr : a.rep ≠ r) (hst : (protocol U n).stBefore α (m + 1) r = (protocol U n).stBefore α m r)
    (h : Inv α m r) : Inv α (m + 1) r :=
  h.transfer hst (known_succ_of_ne hm hr) (window_succ_of_ne hm hr)

theorem inv_succ_doOp {m : ℕ} {r0 : Fin n} {op : LOp U} (hm : α[m]? = some (.doOp r0 op))
    (ih : ∀ r, Inv α m r) (r : Fin n) : Inv α (m + 1) r := by
  by_cases hr : r0 = r
  swap
  · refine inv_succ_other hm hr ?_ (ih r)
    rw [stBefore_succ hm]; simp [Protocol.step, Function.update_of_ne (Ne.symm hr)]; rfl
  subst hr
  have hK := known_succ_of_not_recv hm rfl
  have hW := window_succ_self hm (by simp)
  simp only [Act.rep_doOp] at hK hW
  obtain ⟨h1, h2, h3, h4, h5⟩ := ih r0
  have hst : (protocol U n).stBefore α (m + 1) r0 =
      (protocol U n).doStep r0 ((protocol U n).stBefore α m r0) op := by
    rw [stBefore_succ hm]; simp [Protocol.step]; rfl
  set σ := (protocol U n).stBefore α m r0 with hσ
  cases op with
  | ins b k =>
    have hn := nodeAt_of_getElem? hm
    rw [← hσ] at hn
    have hd : delAt α m = none := delAt_eq_none (by simp [hm])
    have hst' : (protocol U n).stBefore α (m + 1) r0 = ((newNode σ.1 r0 b k :: σ.1.1, σ.1.2),
        some ((σ.2.getD ([], [])).1 ++ [newNode σ.1 r0 b k], (σ.2.getD ([], [])).2)) := hst
    refine ⟨?_, fun x => ?_, fun x => ?_, fun x => ?_, fun x => ?_⟩
    · rw [hst']; exact List.nodup_cons.2 ⟨fun h => lt_irrefl _ (lt_newNode h r0 b k), h1⟩
    · rw [hst', ex_succ_iff hK, hn, ← h2]; simp [eq_comm]
    · rw [hst', ex_succ_iff hK, hd, ← h3]; simp
    · rw [hst', ex_succ_iff hW, hn, ← h4]; simp [eq_comm, or_comm]
    · rw [hst', ex_succ_iff hW, hd, ← h5]; simp
  | del b =>
    have hn : nodeAt α m = none := nodeAt_eq_none (by simp [hm])
    have hd := delAt_of_getElem? hm
    have hst' : (protocol U n).stBefore α (m + 1) r0 = ((σ.1.1, b :: σ.1.2),
        some ((σ.2.getD ([], [])).1, (σ.2.getD ([], [])).2 ++ [b])) := hst
    refine ⟨?_, fun x => ?_, fun x => ?_, fun x => ?_, fun x => ?_⟩
    · rw [hst']; exact h1
    · rw [hst', ex_succ_iff hK, hn, ← h2]; simp
    · rw [hst', ex_succ_iff hK, hd, ← h3]; simp [eq_comm]
    · rw [hst', ex_succ_iff hW, hn, ← h4]; simp
    · rw [hst', ex_succ_iff hW, hd, ← h5]; simp [eq_comm, or_comm]
  | read =>
    have hn : nodeAt α m = none := nodeAt_eq_none (by simp [hm])
    have hd : delAt α m = none := delAt_eq_none (by simp [hm])
    have hst' : (protocol U n).stBefore α (m + 1) r0 = σ := hst
    refine ⟨?_, fun x => ?_, fun x => ?_, fun x => ?_, fun x => ?_⟩
    · rw [hst']; exact h1
    · rw [hst', ex_succ_iff hK, hn, ← h2]; simp
    · rw [hst', ex_succ_iff hK, hd, ← h3]; simp
    · rw [hst', ex_succ_iff hW, hn, ← h4]; simp
    · rw [hst', ex_succ_iff hW, hd, ← h5]; simp

theorem inv_succ_send {m : ℕ} {r0 : Fin n} (hm : α[m]? = some (.send r0))
    (ih : ∀ r, Inv α m r) (r : Fin n) : Inv α (m + 1) r := by
  by_cases hr : r0 = r
  swap
  · refine inv_succ_other hm hr ?_ (ih r)
    rw [stBefore_succ hm]; simp [Protocol.step, Function.update_of_ne (Ne.symm hr)]; rfl
  subst hr
  have hK := known_succ_of_not_recv hm rfl
  simp only [Act.rep_send] at hK
  obtain ⟨h1, h2, h3, h4, h5⟩ := ih r0
  have hst : (protocol U n).stBefore α (m + 1) r0 = (((protocol U n).stBefore α m r0).1, none) := by
    rw [stBefore_succ hm]; simp [Protocol.step]; rfl
  have hn : nodeAt α m = none := nodeAt_eq_none (by simp [hm])
  have hd : delAt α m = none := delAt_eq_none (by simp [hm])
  refine ⟨?_, fun x => ?_, fun x => ?_, fun x => ?_, fun x => ?_⟩
  · rw [hst]; exact h1
  · rw [hst, ex_succ_iff hK, hn, ← h2]; simp
  · rw [hst, ex_succ_iff hK, hd, ← h3]; simp
  · rw [hst]; simp only [Option.getD_none, List.not_mem_nil, false_iff, not_exists, not_and]
    intro q hq hw; rw [window_succ_send hm hw, hn] at hq; cases hq
  · rw [hst]; simp only [Option.getD_none, List.not_mem_nil, false_iff, not_exists, not_and]
    intro q hq hw; rw [window_succ_send hm hw, hd] at hq; cases hq

/-- The payload of a received message. -/
theorem sent_of_send (hwf : (protocol U n).WF α) {m src : ℕ} {r'' : Fin n} (hsm : src < m)
    (hsrc : α[src]? = some (.send r'')) :
    ∃ msg, ((protocol U n).exec (α.take m)).sent[src]? = some (some msg) ∧
      ((protocol U n).stBefore α src r'').2 = some msg := by
  have h1 : (α.take m)[src]? = some (.send r'') := by rw [List.getElem?_take]; simp [hsm, hsrc]
  have h2 := Protocol.exec_sent_send (P := protocol U n) (α.take m) h1
  have h3 : (protocol U n).stBefore (α.take m) src r'' = (protocol U n).stBefore α src r'' := by
    simp [Protocol.stBefore, List.take_take, Nat.min_eq_left hsm.le]
  have hs : src < α.length := by
    by_contra hc; rw [List.getElem?_eq_none (by omega)] at hsrc; cases hsrc
  have h4 := hwf src hs
  rw [List.getElem?_eq_getElem hs, Option.some.injEq] at hsrc
  rw [hsrc] at h4
  obtain ⟨msg, hmsg⟩ := Option.isSome_iff_exists.1 h4
  exact ⟨msg, by rw [h2, h3]; exact congrArg _ hmsg, hmsg⟩

theorem inv_succ_recv (hwf : (protocol U n).WF α) (hC : CausalBroadcast α) {m : ℕ} {r0 : Fin n}
    {src : ℕ} (hm : α[m]? = some (.recv r0 src)) (ih : ∀ m' ≤ m, ∀ r, Inv α m' r) (r : Fin n) :
    Inv α (m + 1) r := by
  have hR := recvOfSend hwf
  obtain ⟨hsm, r'', hsrc⟩ := hR _ _ _ hm
  obtain ⟨msg, hsent, hmsg⟩ := sent_of_send hwf hsm hsrc
  by_cases hr : r0 = r
  swap
  · refine inv_succ_other hm hr ?_ (ih m le_rfl r)
    rw [stBefore_succ hm]; simp [Protocol.step, hsent, Function.update_of_ne (Ne.symm hr)]; rfl
  subst hr
  have hst : (protocol U n).stBefore α (m + 1) r0 =
      ((msg.1.union ((protocol U n).stBefore α m r0).1.1,
        ((protocol U n).stBefore α m r0).1.2 ++ msg.2), ((protocol U n).stBefore α m r0).2) := by
    rw [stBefore_succ hm]; simp [Protocol.step, hsent]; rfl
  have hW := window_succ_self hm (by simp)
  simp only [Act.rep_recv] at hW
  have hKn : ∀ q, (nodeAt α q).isSome →
      (Known α (m + 1) r0 q ↔ Known α m r0 q ∨ Window α src r'' q) := by
    intro q hq
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 hq
    obtain ⟨r1, a, k, h, -⟩ := nodeAt_eq_some.1 hx
    exact known_succ_recv hR hC hm hsrc h
  have hKd : ∀ q, (delAt α q).isSome →
      (Known α (m + 1) r0 q ↔ Known α m r0 q ∨ Window α src r'' q) := by
    intro q hq
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 hq
    obtain ⟨r1, h⟩ := delAt_eq_some.1 hx
    exact known_succ_recv hR hC hm hsrc h
  have hn : nodeAt α m = none := nodeAt_eq_none (by simp [hm])
  have hd : delAt α m = none := delAt_eq_none (by simp [hm])
  obtain ⟨h1, h2, h3, h4, h5⟩ := ih m le_rfl r0
  obtain ⟨-, -, -, g4, g5⟩ := ih src hsm.le r''
  rw [hmsg] at g4 g5
  refine ⟨?_, fun x => ?_, fun x => ?_, fun x => ?_, fun x => ?_⟩
  · rw [hst]; exact List.Nodup.union _ h1
  · rw [hst, ex_recv_iff hKn, ← g4, ← h2, Option.getD_some]; exact List.mem_union_iff
  · rw [hst, ex_recv_iff hKd, ← g5, ← h3, Option.getD_some, List.mem_append, or_comm]
  · rw [hst, ex_succ_iff hW, hn, ← h4]; simp
  · rw [hst, ex_succ_iff hW, hd, ← h5]; simp

/-- The invariant holds for all prefixes. -/
theorem inv (hwf : (protocol U n).WF α) (hC : CausalBroadcast α) :
    ∀ m ≤ α.length, ∀ r, Inv α m r := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rcases m with _ | m
    · intro _ r; exact inv_zero r
    intro hm r
    have hlt : m < α.length := by omega
    have ih' : ∀ m' ≤ m, ∀ r, Inv α m' r := fun m' h => ih m' (by omega) (by omega)
    obtain ⟨a, ha⟩ : ∃ a, α[m]? = some a := ⟨α[m], List.getElem?_eq_getElem hlt⟩
    cases a with
    | doOp r0 op => exact inv_succ_doOp ha (ih' m le_rfl) r
    | send r0 => exact inv_succ_send ha (ih' m le_rfl) r
    | recv r0 src => exact inv_succ_recv hwf hC ha ih' r

end Inv


/-! ### TI trees (Lemma 5) -/

omit [DecidableEq U] in
/-- A duplicate-free, parent-closed subset of a TI tree is a TI tree. -/
theorem tiTree_of_subset {A B : List (Node U)} (hB : IsTITree B) (hA : A.Nodup)
    (hsub : ∀ x ∈ A, x ∈ B) (hpar : ∀ x ∈ A, ∀ b, x.p = some b → ∃ y ∈ A, y.a = b) :
    IsTITree A where
  nodup := hA
  uniq x hx y hy h := hB.uniq x (hsub x hx) y (hsub y hy) h
  parent := hpar
  older x hx y hy h := hB.older x (hsub x hx) y (hsub y hy) h

section Tree

variable {α : List (Act (Fin n) (LOp U))}

/-- All nodes created in the execution. -/
def Nall (α : List (Act (Fin n) (LOp U))) : List (Node U) :=
  (List.range α.length).filterMap (nodeAt α)

theorem lt_length_of_nodeAt {q : ℕ} {x : Node U} (h : nodeAt α q = some x) : q < α.length := by
  obtain ⟨r, a, k, hq, -⟩ := nodeAt_eq_some.1 h
  by_contra hc; rw [List.getElem?_eq_none (by omega)] at hq; cases hq

theorem mem_Nall {x : Node U} : x ∈ Nall α ↔ ∃ q, nodeAt α q = some x := by
  simp only [Nall, List.mem_filterMap, List.mem_range]
  exact ⟨fun ⟨q, _, h⟩ => ⟨q, h⟩, fun ⟨q, h⟩ => ⟨q, lt_length_of_nodeAt h, h⟩⟩

omit [DecidableEq U] in
theorem Known.lt {m : ℕ} {r : Fin n} {q : ℕ} (h : Known α m r q) : q < m := by
  obtain ⟨e, a, he, -, -, hq⟩ := h
  rcases hq with rfl | hq
  · exact he
  · exact hq.lt.trans he

variable (hwf : (protocol U n).WF α) (hC : CausalBroadcast α)
include hwf hC

theorem mem_Nall_of_mem {m : ℕ} (hm : m ≤ α.length) {r : Fin n} {x : Node U}
    (hx : x ∈ ((protocol U n).stBefore α m r).1.1) : x ∈ Nall α := by
  obtain ⟨q, hq, -⟩ := ((inv hwf hC m hm r).N x).1 hx
  exact mem_Nall.2 ⟨q, hq⟩

/-- A node created at replica `r` is in the tree of `r` afterwards. -/
theorem mem_of_nodeAt {q : ℕ} {x : Node U} (hq : nodeAt α q = some x) {m : ℕ} (hqm : q < m)
    (hm : m ≤ α.length) : ∃ r a k, α[q]? = some (.doOp r (.ins a k)) ∧
      x ∈ ((protocol U n).stBefore α m r).1.1 := by
  obtain ⟨r, a, k, h, -⟩ := nodeAt_eq_some.1 hq
  exact ⟨r, a, k, h, ((inv hwf hC m hm r).N x).2 ⟨q, hq, q, _, hqm, h, rfl, Or.inl rfl⟩⟩

omit hwf hC in
/-- The parent of a created node is in the tree of its replica at creation time. -/
theorem parent_mem {q : ℕ} {r : Fin n} {a : U} {k : ℕ} {b : U} (hb : (newNode ((protocol U n).stBefore α q r).1 r a k).p = some b) :
    ∃ y ∈ ((protocol U n).stBefore α q r).1.1, y.a = b := by
  simp only [newNode_p, parentFor] at hb
  split_ifs at hb
  have hbv := List.mem_of_getElem? hb
  simp only [visible, List.mem_filter] at hbv
  exact exists_of_mem_walk hbv.1

omit hwf hC in
theorem nodeAt_a {q : ℕ} {x : Node U} (hq : nodeAt α q = some x) :
    ∃ r k, α[q]? = some (.doOp r (.ins x.a k)) := by
  obtain ⟨r, a, k, h, rfl⟩ := nodeAt_eq_some.1 hq
  exact ⟨r, k, h⟩

variable (hU : UniqueIns α)
include hU

omit hwf hC in
theorem eq_of_nodeAt_a {q q' : ℕ} {x x' : Node U} (hq : nodeAt α q = some x)
    (hq' : nodeAt α q' = some x') (h : x.a = x'.a) : q = q' := by
  obtain ⟨r, k, h1⟩ := nodeAt_a hq
  obtain ⟨r', k', h2⟩ := nodeAt_a hq'
  rw [h] at h1
  exact hU _ _ _ _ _ _ _ h1 h2

omit hU in
theorem eq_of_nodeAt_t {q q' : ℕ} {x x' : Node U} (hq : nodeAt α q = some x)
    (hq' : nodeAt α q' = some x') (h : x.t = x'.t) : q = q' := by
  have key : ∀ q q' (x x' : Node U), nodeAt α q = some x → nodeAt α q' = some x' → x.t = x'.t →
      q < q' → False := by
    intro q q' x x' hq hq' h hlt
    obtain ⟨r, a, k, h1, rfl⟩ := nodeAt_eq_some.1 hq
    obtain ⟨r', a', k', h2, rfl⟩ := nodeAt_eq_some.1 hq'
    simp only [newNode_t] at h
    have h' := congrArg ofLex h
    simp only [ofLex_toLex, Prod.mk.injEq] at h'
    have hr : r = r' := Fin.ext h'.2
    subst hr
    have hx := ((inv hwf hC q' (lt_length_of_nodeAt hq').le r).N _).2
      ⟨q, hq, q, _, hlt, h1, rfl, Or.inl rfl⟩
    have := le_maxX hx
    simp only [newNode_t, ofLex_toLex] at this
    omega
  rcases lt_trichotomy q q' with hlt | heq | hgt
  · exact (key q q' x x' hq hq' h hlt).elim
  · exact heq
  · exact (key q' q x' x hq' hq h.symm hgt).elim

/-- **Lemma 5** (for the set of all created nodes). -/
theorem isTITree_Nall : IsTITree (Nall α) where
  nodup := List.Nodup.filterMap (fun q q' x hq hq' => eq_of_nodeAt_a hU hq hq' rfl)
    List.nodup_range
  uniq x hx y hy h := by
    obtain ⟨q, hq⟩ := mem_Nall.1 hx
    obtain ⟨q', hq'⟩ := mem_Nall.1 hy
    have : q = q' := by
      rcases h with h | h
      · exact eq_of_nodeAt_t hwf hC hq hq' h
      · exact eq_of_nodeAt_a hU hq hq' h
    subst this
    rw [hq] at hq'; exact Option.some.inj hq'
  parent x hx b hb := by
    obtain ⟨q, hq⟩ := mem_Nall.1 hx
    obtain ⟨r, a, k, h, rfl⟩ := nodeAt_eq_some.1 hq
    obtain ⟨y, hy, hya⟩ := parent_mem hb
    exact ⟨y, mem_Nall_of_mem hwf hC (lt_length_of_nodeAt hq).le hy, hya⟩
  older x hx y hy h := by
    obtain ⟨q, hq⟩ := mem_Nall.1 hx
    obtain ⟨q', hq'⟩ := mem_Nall.1 hy
    obtain ⟨r, a, k, h', rfl⟩ := nodeAt_eq_some.1 hq'
    obtain ⟨z, hz, hza⟩ := parent_mem h
    obtain ⟨qz, hqz, -⟩ := ((inv hwf hC q' (lt_length_of_nodeAt hq').le r).N z).1 hz
    have := eq_of_nodeAt_a hU hqz hq hza
    subst this
    rw [hqz] at hq; cases hq
    exact lt_newNode hz r a k

/-- **Lemma 5**: the tree of every replica is a TI tree. -/
theorem isTITree_st {m : ℕ} (hm : m ≤ α.length) (r : Fin n) :
    IsTITree ((protocol U n).stBefore α m r).1.1 := by
  have hI := inv hwf hC m hm r
  refine tiTree_of_subset (isTITree_Nall hwf hC hU) hI.nodup
    (fun x hx => mem_Nall_of_mem hwf hC hm hx) ?_
  intro x hx b hb
  obtain ⟨q, hq, hk⟩ := (hI.N x).1 hx
  obtain ⟨r', a, k, h', rfl⟩ := nodeAt_eq_some.1 hq
  obtain ⟨y, hy, hya⟩ := parent_mem hb
  obtain ⟨q'', hq'', hk''⟩ := ((inv hwf hC q (lt_length_of_nodeAt hq).le r').N y).1 hy
  refine ⟨y, (hI.N y).2 ⟨q'', hq'', ?_⟩, hya⟩
  obtain ⟨e, c, he, hec, hcr, hqe⟩ := hk''
  have heq : HB α e q := HB.of_rep he hec h' hcr
  rcases hqe with rfl | hqe
  · exact hk.of_hb heq
  · exact hk.of_hb (hqe.trans heq)

end Tree

/-! ### The strong list specification -/

section Spec

variable {α : List (Act (Fin n) (LOp U))}

omit [DecidableEq U] in
theorem lt_length_of_getElem? {β : Type} {l : List β} {p : ℕ} {b : β} (h : l[p]? = some b) :
    p < l.length := by
  by_contra hc; rw [List.getElem?_eq_none (by omega)] at h; cases h

/-- The response of a `do` event is the visible list of the state right after it. -/
theorem resp_eq {p : ℕ} {r : Fin n} {op : LOp U} (hp : α[p]? = some (.doOp r op)) :
    (protocol U n).resp r ((protocol U n).stBefore α p r) op =
      visible ((protocol U n).stBefore α (p + 1) r).1 := by
  rw [stBefore_succ hp]; cases op <;> simp [Protocol.step] <;> rfl

theorem insVis_iff {p : ℕ} (hp : IsDo α p) {a : U} :
    InsVis ((protocol U n).hist α) (visHB α) p a ↔
      ∃ q x, nodeAt α q = some x ∧ x.a = a ∧ (q = p ∨ HB α q p) := by
  constructor
  · rintro ⟨q, r, k, w, hv, hq⟩
    obtain ⟨hq', -⟩ := hist_eq_some hq
    refine ⟨q, _, nodeAt_of_getElem? hq', rfl, ?_⟩
    rcases hv with rfl | hv
    · exact Or.inl rfl
    · exact Or.inr hv.1
  · rintro ⟨q, x, hq, rfl, hqp⟩
    obtain ⟨r, k, h⟩ := nodeAt_a hq
    refine ⟨q, r, k, _, ?_, hist_of_getElem? h⟩
    rcases hqp with rfl | hqp
    · exact Or.inl rfl
    · exact Or.inr ⟨hqp, ⟨_, _, h⟩, hp⟩

theorem delVis_iff {p : ℕ} (hp : IsDo α p) {a : U} :
    DelVis ((protocol U n).hist α) (visHB α) p a ↔
      ∃ q, delAt α q = some a ∧ (q = p ∨ HB α q p) := by
  constructor
  · rintro ⟨q, r, w, hv, hq⟩
    obtain ⟨hq', -⟩ := hist_eq_some hq
    refine ⟨q, delAt_of_getElem? hq', ?_⟩
    rcases hv with rfl | hv
    · exact Or.inl rfl
    · exact Or.inr hv.1
  · rintro ⟨q, hq, hqp⟩
    obtain ⟨r, h⟩ := delAt_eq_some.1 hq
    refine ⟨q, r, _, ?_, hist_of_getElem? h⟩
    rcases hqp with rfl | hqp
    · exact Or.inl rfl
    · exact Or.inr ⟨hqp, ⟨_, _, h⟩, hp⟩

theorem mem_elems_of_mem_s {a : U} (h : a ∈ s (Nall α)) : a ∈ elems ((protocol U n).hist α) := by
  obtain ⟨x, hx, rfl⟩ := exists_of_mem_walk h
  obtain ⟨q, hq⟩ := mem_Nall.1 hx
  obtain ⟨r, k, h⟩ := nodeAt_a hq
  exact ⟨q, r, k, _, hist_of_getElem? h⟩

variable (hwf : (protocol U n).WF α) (hC : CausalBroadcast α)
include hwf hC

theorem mem_N_succ {p : ℕ} {r : Fin n} {op : LOp U} (hp : α[p]? = some (.doOp r op))
    (x : Node U) : x ∈ ((protocol U n).stBefore α (p + 1) r).1.1 ↔
      ∃ q, nodeAt α q = some x ∧ (q = p ∨ HB α q p) := by
  have := known_succ_iff hp
  simp only [Act.rep_doOp] at this
  rw [(inv hwf hC (p + 1) (lt_length_of_getElem? hp) r).N x]
  simp only [this]

theorem mem_T_succ {p : ℕ} {r : Fin n} {op : LOp U} (hp : α[p]? = some (.doOp r op))
    (b : U) : b ∈ ((protocol U n).stBefore α (p + 1) r).1.2 ↔
      ∃ q, delAt α q = some b ∧ (q = p ∨ HB α q p) := by
  have := known_succ_iff hp
  simp only [Act.rep_doOp] at this
  rw [(inv hwf hC (p + 1) (lt_length_of_getElem? hp) r).T b]
  simp only [this]

theorem mem_s_Nall_of_elems (hU : UniqueIns α) {a : U} (h : a ∈ elems ((protocol U n).hist α)) :
    a ∈ s (Nall α) := by
  obtain ⟨p, r, k, w, hp⟩ := h
  obtain ⟨hp', -⟩ := hist_eq_some hp
  exact (mem_s (isTITree_Nall hwf hC hU)).2
    ⟨_, mem_Nall.2 ⟨p, nodeAt_of_getElem? hp'⟩, rfl⟩

/-- Deleted elements are not tombstones when they are inserted (uses the user assumptions). -/
theorem not_mem_tomb (hU : UniqueIns α) (hD : DelOK (protocol U n) α) {p : ℕ} {r : Fin n} {a : U}
    {k : ℕ} (hp : α[p]? = some (.doOp r (.ins a k))) :
    a ∉ ((protocol U n).stBefore α p r).1.2 := by
  intro haT
  obtain ⟨q, hq, hk⟩ := ((inv hwf hC p (lt_length_of_getElem? hp).le r).T a).1 haT
  obtain ⟨r', hq'⟩ := delAt_eq_some.1 hq
  have hqp : HB α q p := by
    obtain ⟨e, c, he, hec, hcr, hqe⟩ := hk
    have hep : HB α e p := HB.of_rep he hec hp hcr
    rcases hqe with rfl | hqe
    · exact hep
    · exact hqe.trans hep
  obtain ⟨q0, hq0q, op0, v0, hh0, hav, -⟩ := hD q r' a hq'
  obtain ⟨hα0, rfl⟩ := hist_eq_some hh0
  rw [resp_eq hα0] at hav
  simp only [visible, List.mem_filter] at hav
  obtain ⟨x, hx, hxa⟩ := exists_of_mem_walk hav.1
  obtain ⟨q1, hq1, hq1k⟩ := (mem_N_succ hwf hC hα0 x).1 hx
  have h0q : HB α q0 q := HB.of_rep hq0q hα0 hq' rfl
  have h1p : HB α q1 p := by
    rcases hq1k with rfl | h
    · exact h0q.trans hqp
    · exact (h.trans h0q).trans hqp
  obtain ⟨r1, k1, h1⟩ := nodeAt_a hq1
  rw [hxa] at h1
  have := hU _ _ _ _ _ _ _ h1 hp
  subst this
  exact HB.irrefl _ h1p

/-- Condition (1c): the inserted element is at the requested position of the response. -/
theorem ins_resp (hU : UniqueIns α) (hD : DelOK (protocol U n) α) {p : ℕ} {r : Fin n} {a : U}
    {k : ℕ} (hp : α[p]? = some (.doOp r (.ins a k))) :
    (visible ((protocol U n).stBefore α (p + 1) r).1)[min k
      ((visible ((protocol U n).stBefore α (p + 1) r).1).length - 1)]? = some a := by
  set σ := (protocol U n).stBefore α p r with hσ
  have hst : ((protocol U n).stBefore α (p + 1) r).1 = (newNode σ.1 r a k :: σ.1.1, σ.1.2) := by
    rw [stBefore_succ hp]; simp [Protocol.step]; rfl
  have hlen := lt_length_of_getElem? hp
  have hTI' : IsTITree (newNode σ.1 r a k :: σ.1.1) := by
    have := isTITree_st hwf hC hU (m := p + 1) hlen r
    rwa [hst] at this
  have hTI : IsTITree σ.1.1 := isTITree_st hwf hC hU hlen.le r
  have hs := s_cons_max hTI' (fun m hm => lt_newNode hm r a k)
  have haT : a ∉ σ.1.2 := not_mem_tomb hwf hC hU hD hp
  rw [hst]
  simp only [visible]
  rw [hs, newNode_p, newNode_a]
  set v := (s σ.1.1).filter (fun x => decide (x ∉ σ.1.2)) with hv
  have hvis : visible σ.1 = v := rfl
  have hvnd : v.Nodup := (s_nodup hTI).filter _
  have key : (insAfter (parentFor σ.1 k) a (s σ.1.1)).filter (fun x => decide (x ∉ σ.1.2)) =
      v.insertIdx (min k v.length) a := by
    unfold parentFor
    rw [hvis]
    split_ifs with h0
    · rw [h0]; simp [insAfter, haT, hv]
    · have hj : min k v.length - 1 < v.length := by omega
      have hvT : ∀ y ∈ v, y ∉ σ.1.2 := fun y hy => by
        rw [hv, List.mem_filter] at hy; simpa using hy.2
      rw [List.getElem?_eq_getElem hj, filter_insAfter _ (by
          simpa using hvT _ (List.getElem_mem hj)) (by simpa using haT),
        ← insertIdx_eq_insAfter hvnd a (by omega) (by omega)]
  rw [key, List.length_insertIdx_of_le_length (by omega), Nat.add_sub_cancel,
    List.getElem?_insertIdx_self]
  simp

end Spec

/-- The abstract execution with visibility = happens-before is in `A_strong`, with the list order
`lo a b` iff `a` precedes `b` in `s` of the tree of all created nodes. -/
theorem strong {α : List (Act (Fin n) (LOp U))} (hwf : (protocol U n).WF α) (hadm : Adm U n α) :
    Strong ((protocol U n).hist α) (visHB α) := by
  obtain ⟨hC, hU, hD⟩ := hadm
  have hT := isTITree_Nall hwf hC hU
  have hnd := s_nodup hT
  refine ⟨fun a b => List.Sublist [a, b] (s (Nall α)), ?_, ?_, ?_, ?_, ?_⟩
  · intro a b h
    exact ⟨mem_elems_of_mem_s (h.subset (by simp)), mem_elems_of_mem_s (h.subset (by simp))⟩
  · intro p r op w hp
    obtain ⟨hα, rfl⟩ := hist_eq_some hp
    have hlen := lt_length_of_getElem? hα
    have hTI := isTITree_st hwf hC hU (m := p + 1) hlen r
    have hpd : IsDo α p := ⟨_, _, hα⟩
    rw [resp_eq hα]
    refine ⟨fun a => ?_, ?_, ?_⟩
    · rw [insVis_iff hpd, delVis_iff hpd, ← mem_T_succ hwf hC hα]
      simp only [visible, List.mem_filter, decide_eq_true_eq]
      rw [mem_s hTI]
      constructor
      · rintro ⟨⟨x, hx, rfl⟩, h⟩
        obtain ⟨q, hq, hqp⟩ := (mem_N_succ hwf hC hα x).1 hx
        exact ⟨⟨q, x, hq, rfl, hqp⟩, h⟩
      · rintro ⟨⟨q, x, hq, rfl, hqp⟩, h⟩
        exact ⟨⟨x, (mem_N_succ hwf hC hα x).2 ⟨q, hq, hqp⟩, rfl⟩, h⟩
    · refine List.pairwise_iff_forall_sublist.2 fun h => h.trans ?_
      exact List.filter_sublist.trans (s_sublist hTI hT fun x hx => mem_Nall_of_mem hwf hC hlen hx)
    · rintro a k rfl
      exact ins_resp hwf hC hU hD hα
  · intro a b c hab hbc
    exact pair_sublist_trans hnd hab hbc
  · intro a h
    exact List.nodup_iff_sublist.1 hnd a h
  · intro a ha b hb hab
    exact pair_sublist_total (mem_s_Nall_of_elems hwf hC hU ha) (mem_s_Nall_of_elems hwf hC hU hb)
      hab

theorem pending_of_update {α : List (Act (Fin n) (LOp U))} {p : ℕ} {r : Fin n} {op : LOp U}
    (hp : α[p]? = some (.doOp r op)) (hop : op ≠ .read) : (protocol U n).Pending α p r := by
  refine ⟨lt_length_of_getElem? hp, ?_⟩
  have := stBefore_succ hp r
  simp only [Protocol.stBefore] at this
  rw [this]
  cases op with
  | ins a k => simp [Protocol.step, protocol]
  | del a => simp [Protocol.step, protocol]
  | read => exact absurd rfl hop

/-- **Theorem 1** (safety part): every well-formed execution of `R_rga^n` satisfying causal
broadcast (and the user assumptions) complies with the abstract execution whose visibility is
happens-before, and this abstract execution belongs to `A_strong`. Visibility goes forward in the
execution, so the execution order itself is a valid `H`. -/
theorem theorem1_strong (α : List (Act (Fin n) (LOp U))) (hwf : (protocol U n).WF α)
    (hadm : Adm U n α) :
    AbsWF ((protocol U n).hist α) (visHB α) ∧ (∀ i j, visHB α i j → i < j) ∧
      Strong ((protocol U n).hist α) (visHB α) :=
  ⟨visHB_absWF α, fun _ _ h => visHB_lt h, strong hwf hadm⟩

/-- RGA is push-based (remark after Definition 13). -/
theorem pushBased : PushBased (protocol U n) Strong (Adm U n) where
  ins α hwf hadm p r a k h := pending_of_update h (by simp)
  del α hwf hadm p r a h _ := pending_of_update h (by simp)
  spec α hwf hadm := (theorem1_strong α hwf hadm).2.2

/-- **Theorem 1** (safety part, Definition 6 form): `R_rga^n` satisfies the strong list
specification. -/
theorem satisfies_strong : Satisfies (protocol U n) Strong (Adm U n) :=
  pushBased.satisfies

end RGA

end Podc.CollaborativeListSpec
