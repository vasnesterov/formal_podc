import Mathlib

/-!
# Timestamped insertion trees (Section 4.1)

A node `(a, t, p)` stores an element `a`, a timestamp `t` and the parent element `p`
(`none` = the root `◦`). Timestamps are pairs `(x, i)` ordered lexicographically (`TS`).

`s N` is the paper's read procedure: depth-first traversal from the root, parents before children,
children in decreasing timestamp order. The paper defines the parent relation on a set of nodes;
we represent a finite set of nodes by a list `N` (duplicates are excluded by `IsTITree.nodup`; for TI
trees `s N` only depends on the set, `s_perm`). The traversal only descends to children with a
larger timestamp than their parent; for TI trees this is no restriction (Definition 12 (3)), and it
makes the traversal terminate on arbitrary lists.

Main results: Lemma 6 (`s_sublist`: `A ⊆ B` TI trees ⇒ `s A` is a subsequence of `s B`) and the
fact behind the insert procedure (`s_cons_max`: adding a node with the largest timestamp puts its
element right after its parent).
-/

namespace Podc.CollaborativeListSpec

/-- Timestamps `(x, i)` with the lexicographic order. -/
abbrev TS := ℕ ×ₗ ℕ

/-- A node `(a, t, p)` of a TI tree. -/
structure Node (U : Type) where
  a : U
  t : TS
  p : Option U
  deriving DecidableEq

variable {U : Type} [DecidableEq U]

/-- **Definition 12** (TI tree), for a duplicate-free list of nodes. -/
structure IsTITree (N : List (Node U)) : Prop where
  nodup : N.Nodup
  /-- (1) timestamps or symbols uniquely identify nodes. -/
  uniq : ∀ n ∈ N, ∀ n' ∈ N, (n.t = n'.t ∨ n.a = n'.a) → n = n'
  /-- (2) all parents are present. -/
  parent : ∀ n ∈ N, ∀ b, n.p = some b → ∃ n' ∈ N, n'.a = b
  /-- (3) parents are older than their children. -/
  older : ∀ n ∈ N, ∀ n' ∈ N, n'.p = some n.a → n.t < n'.t

/-- The children of `p` (with timestamp above `t`), in decreasing timestamp order. -/
def children (N : List (Node U)) (p : Option U) (t : WithBot TS) : List (Node U) :=
  (N.filter (fun m => m.p = p ∧ t < (m.t : WithBot TS))).mergeSort
    (fun x y => decide (y.t ≤ x.t))

theorem mem_children {N : List (Node U)} {p : Option U} {t : WithBot TS} {m : Node U} :
    m ∈ children N p t ↔ m ∈ N ∧ m.p = p ∧ t < (m.t : WithBot TS) := by
  simp [children, List.mem_mergeSort]

theorem countP_lt_countP {α : Type} {p q : α → Bool} {l : List α} {m : α}
    (hpq : ∀ x ∈ l, p x → q x) (hm : m ∈ l) (hq : q m) (hp : ¬ p m) :
    l.countP p < l.countP q := by
  induction l with
  | nil => simp at hm
  | cons y l ih =>
    simp only [List.countP_cons]
    have h1 := List.countP_mono_left (fun x hx => hpq x (List.mem_cons_of_mem _ hx))
    rcases List.mem_cons.1 hm with rfl | hm
    · simp [hq, hp]; omega
    · have := ih (fun x hx => hpq x (List.mem_cons_of_mem _ hx)) hm
      have h2 := hpq y (by simp)
      split_ifs at * <;> simp_all

/-- Depth-first traversal of the subtree below `p` (whose timestamp is `t`). -/
def walk (N : List (Node U)) (p : Option U) (t : WithBot TS) : List U :=
  (children N p t).attach.flatMap fun m => m.1.a :: walk N (some m.1.a) m.1.t
termination_by (N.filter (fun m => t < (m.t : WithBot TS))).length
decreasing_by
  obtain ⟨m, hm⟩ := m
  rw [mem_children] at hm
  simp only [← List.countP_eq_length_filter]
  refine countP_lt_countP (m := m) ?_ hm.1 (by simpa using hm.2.2) (by simp)
  intro x _ hx
  simp only [decide_eq_true_eq] at hx ⊢
  exact lt_trans hm.2.2 (by exact_mod_cast hx)

/-- The read procedure: `s(N)`. -/
def s (N : List (Node U)) : List U := walk N none ⊥

/-- Insert `x` right after `p` (at the front if `p = ◦`; unchanged if `p` does not occur). -/
def insAfter (p : Option U) (x : U) (l : List U) : List U :=
  match p with
  | none => x :: l
  | some b =>
    match l.idxOf? b with
    | some i => l.insertIdx (i + 1) x
    | none => l

/-! ### Auxiliary lemmas -/

/-- Unfolding equation for `walk` without `attach`. -/
theorem walk_eq (N : List (Node U)) (p : Option U) (t : WithBot TS) :
    walk N p t = (children N p t).flatMap fun m => m.a :: walk N (some m.a) m.t := by
  rw [walk]; simp

omit [DecidableEq U] in
/-- Induction principle following the recursion of `walk`. -/
theorem walk_induction (N : List (Node U)) {P : Option U → WithBot TS → Prop}
    (h : ∀ p t, (∀ m ∈ N, m.p = p → t < (m.t : WithBot TS) → P (some m.a) m.t) → P p t) :
    ∀ p t, P p t := by
  intro p t
  induction hk : (N.filter (fun m => t < (m.t : WithBot TS))).length using Nat.strong_induction_on
    generalizing p t with
  | _ k ih =>
    apply h
    intro m hm _ hmt
    refine ih _ ?_ _ _ rfl
    rw [← hk]
    simp only [← List.countP_eq_length_filter]
    refine countP_lt_countP (m := m) ?_ hm (by simpa using hmt) (by simp)
    intro x _ hx
    simp only [decide_eq_true_eq] at hx ⊢
    exact lt_trans hmt (by exact_mod_cast hx)

/-- Every element output by `walk N p t` is the element of a node of `N` younger than `t`. -/
theorem mem_walk {N : List (Node U)} {p : Option U} {t : WithBot TS} {x : U}
    (hx : x ∈ walk N p t) : ∃ m ∈ N, m.a = x ∧ t < (m.t : WithBot TS) := by
  revert x
  refine walk_induction N (P := fun p t => ∀ {x}, x ∈ walk N p t →
    ∃ m ∈ N, m.a = x ∧ t < (m.t : WithBot TS)) ?_ p t
  intro p t ih x hx
  rw [walk_eq, List.mem_flatMap] at hx
  obtain ⟨m, hm, hx⟩ := hx
  rw [mem_children] at hm
  rcases List.mem_cons.1 hx with rfl | hx
  · exact ⟨m, hm.1, rfl, hm.2.2⟩
  · obtain ⟨m', hm', rfl, hlt⟩ := ih m hm.1 hm.2.1 hm.2.2 hx
    exact ⟨m', hm', rfl, lt_trans hm.2.2 hlt⟩

omit [DecidableEq U] in
/-- Sorting nodes by decreasing timestamp yields a strictly decreasing list when timestamps
are distinct. -/
theorem pairwise_mergeSort_lt {l : List (Node U)} (hnd : l.Nodup)
    (hinj : ∀ x ∈ l, ∀ y ∈ l, x.t = y.t → x = y) :
    (l.mergeSort (fun x y => decide (y.t ≤ x.t))).Pairwise (fun x y => y.t < x.t) := by
  have hs := List.pairwise_mergeSort (le := fun x y : Node U => decide (y.t ≤ x.t))
    (fun a b c hab hbc => by simp only [decide_eq_true_eq] at *; exact le_trans hbc hab)
    (fun a b => by simpa using le_total b.t a.t) l
  have hp := List.mergeSort_perm l (fun x y => decide (y.t ≤ x.t))
  have hnd' : (l.mergeSort (fun x y => decide (y.t ≤ x.t))).Nodup := hp.nodup_iff.2 hnd
  refine (hs.and hnd').imp_of_mem ?_
  intro a b ha hb ⟨hab, hne⟩
  simp only [decide_eq_true_eq] at hab
  refine lt_of_le_of_ne hab fun heq => hne ?_
  exact (hinj b (hp.subset hb) a (hp.subset ha) heq).symm

omit [DecidableEq U] in
theorem eq_of_perm_of_pairwise_lt {l₁ l₂ : List (Node U)}
    (h₁ : l₁.Pairwise (fun x y => y.t < x.t)) (h₂ : l₂.Pairwise (fun x y => y.t < x.t))
    (h : l₁.Perm l₂) : l₁ = l₂ :=
  List.Perm.eq_of_pairwise (fun _ _ _ _ hab hba => absurd (lt_trans hab hba) (lt_irrefl _))
    h₁ h₂ h

/-- `children` only depends on the set of nodes (for duplicate-free lists with distinct
timestamps). -/
theorem children_perm {N N' : List (Node U)} (h : N.Perm N') (hnd : N.Nodup)
    (hinj : ∀ x ∈ N, ∀ y ∈ N, x.t = y.t → x = y) (p : Option U) (t : WithBot TS) :
    children N p t = children N' p t := by
  unfold children
  have hf := h.filter (fun m => decide (m.p = p ∧ t < (m.t : WithBot TS)))
  refine eq_of_perm_of_pairwise_lt (pairwise_mergeSort_lt (hnd.filter _) ?_)
    (pairwise_mergeSort_lt (hf.nodup_iff.1 (hnd.filter _)) ?_) ?_
  · intro x hx y hy; exact hinj x (List.mem_of_mem_filter hx) y (List.mem_of_mem_filter hy)
  · intro x hx y hy
    exact hinj x (List.mem_of_mem_filter (hf.symm.subset hx)) y
      (List.mem_of_mem_filter (hf.symm.subset hy))
  · exact (List.mergeSort_perm _ _).trans (hf.trans (List.mergeSort_perm _ _).symm)

/-- Children after adding a node with the largest timestamp. -/
theorem children_cons_max {N : List (Node U)} {n : Node U} (hnd : (n :: N).Nodup)
    (hinj : ∀ x ∈ n :: N, ∀ y ∈ n :: N, x.t = y.t → x = y) (hmax : ∀ m ∈ N, m.t < n.t)
    (p : Option U) (t : WithBot TS) :
    children (n :: N) p t =
      if n.p = p ∧ t < (n.t : WithBot TS) then n :: children N p t else children N p t := by
  unfold children
  split_ifs with hn
  · have hf : (n :: N).filter (fun m => decide (m.p = p ∧ t < (m.t : WithBot TS))) =
        n :: N.filter (fun m => decide (m.p = p ∧ t < (m.t : WithBot TS))) :=
      List.filter_cons_of_pos (by simpa using hn)
    rw [hf]
    refine eq_of_perm_of_pairwise_lt (pairwise_mergeSort_lt ?_ ?_) ?_ ?_
    · exact hf ▸ hnd.filter _
    · intro x hx y hy
      exact hinj x (by simpa using (List.mem_cons.1 hx).imp id List.mem_of_mem_filter) y
        (by simpa using (List.mem_cons.1 hy).imp id List.mem_of_mem_filter)
    · refine List.Pairwise.cons ?_ (pairwise_mergeSort_lt ((List.nodup_cons.1 hnd).2.filter _) ?_)
      · intro m hm
        exact hmax m (List.mem_of_mem_filter ((List.mergeSort_perm _ _).subset hm))
      · intro x hx y hy
        exact hinj x (List.mem_cons_of_mem _ (List.mem_of_mem_filter hx)) y
          (List.mem_cons_of_mem _ (List.mem_of_mem_filter hy))
    · exact (List.mergeSort_perm _ _).trans ((List.mergeSort_perm _ _).symm.cons n)
  · have hf : (n :: N).filter (fun m => decide (m.p = p ∧ t < (m.t : WithBot TS))) =
        N.filter (fun m => decide (m.p = p ∧ t < (m.t : WithBot TS))) :=
      List.filter_cons_of_neg (by simpa using hn)
    rw [hf]

/-- Insert `x` after every occurrence of `p` (nothing happens for `p = ◦`). For duplicate-free
lists this is `insAfter` (`insEvery_eq_insAfter`); unlike `insAfter` it commutes with `flatMap`. -/
def insEvery (p : Option U) (x : U) (l : List U) : List U :=
  l.flatMap fun y => if some y = p then [y, x] else [y]

@[simp] theorem insEvery_nil (p : Option U) (x : U) : insEvery p x [] = [] := rfl

theorem insEvery_cons (p : Option U) (x y : U) (l : List U) :
    insEvery p x (y :: l) = (if some y = p then [y, x] else [y]) ++ insEvery p x l := by
  simp [insEvery]

theorem insEvery_flatMap {α : Type} (p : Option U) (x : U) (L : List α) (f : α → List U) :
    insEvery p x (L.flatMap f) = L.flatMap fun a => insEvery p x (f a) := by
  simp [insEvery, List.flatMap_assoc]

theorem insEvery_of_forall_ne {p : Option U} {x : U} {l : List U} (h : ∀ y ∈ l, some y ≠ p) :
    insEvery p x l = l := by
  induction l with
  | nil => rfl
  | cons y l ih =>
    rw [insEvery_cons, ite_eq_right (h y (by simp)), ih fun z hz => h z (List.mem_cons_of_mem _ hz)]
    rfl

@[simp] theorem insEvery_none (x : U) (l : List U) : insEvery none x l = l :=
  insEvery_of_forall_ne (by simp)

theorem insEvery_of_not_mem {b x : U} {l : List U} (h : b ∉ l) : insEvery (some b) x l = l :=
  insEvery_of_forall_ne fun _ hy he => h (Option.some_injective _ he ▸ hy)

theorem insAfter_some_cons (b x y : U) (l : List U) :
    insAfter (some b) x (y :: l) =
      if y = b then y :: x :: l else y :: insAfter (some b) x l := by
  by_cases h : y = b
  · subst h; simp [insAfter, List.idxOf?_cons]
  · simp only [insAfter, List.idxOf?_cons, beq_iff_eq, h, ite_false]
    cases hi : l.idxOf? b with
    | none => simp
    | some i => simp [List.insertIdx_succ_cons]

theorem insAfter_of_not_mem {b x : U} {l : List U} (h : b ∉ l) : insAfter (some b) x l = l := by
  induction l with
  | nil => rfl
  | cons y l ih =>
    rw [insAfter_some_cons, ite_eq_right (fun e => h (by subst e; simp)),
      ih fun hb => h (List.mem_cons_of_mem _ hb)]

theorem insEvery_eq_insAfter {b x : U} {l : List U} (hl : l.Nodup) :
    insEvery (some b) x l = insAfter (some b) x l := by
  induction l with
  | nil => rfl
  | cons y l ih =>
    rw [insEvery_cons, insAfter_some_cons]
    rw [List.nodup_cons] at hl
    split_ifs with h1 h2 h2
    · subst h2; simp [insEvery_of_not_mem hl.1]
    · exact absurd (Option.some_injective _ h1) h2
    · exact absurd (congrArg some h2) h1
    · simp [ih hl.2]

theorem insEvery_perm {b x : U} {l : List U} (hl : l.Nodup) (hb : b ∈ l) :
    (insEvery (some b) x l).Perm (x :: l) := by
  induction l with
  | nil => simp at hb
  | cons y l ih =>
    rw [insEvery_cons]
    rw [List.nodup_cons] at hl
    split_ifs with h
    · cases Option.some_injective _ h
      rw [insEvery_of_not_mem hl.1]
      exact List.Perm.swap _ _ _
    · have hb' : b ∈ l := by
        rcases List.mem_cons.1 hb with rfl | hb
        · exact absurd rfl h
        · exact hb
      exact ((ih hl.2 hb').cons y).trans (List.Perm.swap _ _ _)

theorem sublist_insEvery (p : Option U) (x : U) (l : List U) : l.Sublist (insEvery p x l) := by
  induction l with
  | nil => simp
  | cons y l ih =>
    rw [insEvery_cons]
    split_ifs
    · exact (ih.cons_cons y).trans (List.Sublist.cons_cons y (List.sublist_cons_self _ _))
    · exact ih.cons_cons y

theorem Sublist.insEvery {l₁ l₂ : List U} (h : l₁.Sublist l₂) (p : Option U) (x : U) :
    (insEvery p x l₁).Sublist (insEvery p x l₂) :=
  h.flatMap _

/-! ### TI trees -/

omit [DecidableEq U] in
theorem IsTITree.perm {N N' : List (Node U)} (hN : IsTITree N) (h : N.Perm N') :
    IsTITree N' where
  nodup := h.nodup_iff.1 hN.nodup
  uniq n hn n' hn' := hN.uniq n (h.symm.subset hn) n' (h.symm.subset hn')
  parent n hn b hb := by
    obtain ⟨n', hn', e⟩ := hN.parent n (h.symm.subset hn) b hb
    exact ⟨n', h.subset hn', e⟩
  older n hn n' hn' := hN.older n (h.symm.subset hn) n' (h.symm.subset hn')

omit [DecidableEq U] in
theorem IsTITree.of_cons_max {N : List (Node U)} {n : Node U} (hN : IsTITree (n :: N))
    (hmax : ∀ m ∈ N, m.t < n.t) : IsTITree N where
  nodup := (List.nodup_cons.1 hN.nodup).2
  uniq m hm m' hm' := hN.uniq m (List.mem_cons_of_mem _ hm) m' (List.mem_cons_of_mem _ hm')
  parent m hm b hb := by
    obtain ⟨n', hn', e⟩ := hN.parent m (List.mem_cons_of_mem _ hm) b hb
    rcases List.mem_cons.1 hn' with rfl | hn'
    · have := hN.older n' List.mem_cons_self m (List.mem_cons_of_mem _ hm) (e ▸ hb)
      exact absurd (lt_trans this (hmax m hm)) (lt_irrefl _)
    · exact ⟨n', hn', e⟩
  older m hm m' hm' := hN.older m (List.mem_cons_of_mem _ hm) m' (List.mem_cons_of_mem _ hm')

omit [DecidableEq U] in
theorem IsTITree.inj {N : List (Node U)} (hN : IsTITree N) :
    ∀ x ∈ N, ∀ y ∈ N, x.t = y.t → x = y :=
  fun x hx y hy h => hN.uniq x hx y hy (Or.inl h)

/-- In a TI tree, nothing below `m` is older than `m` (no cycles). -/
theorem not_mem_walk_of_le {N : List (Node U)} (hN : IsTITree N) {m m' : Node U}
    (hm' : m' ∈ N) (hle : m'.t ≤ m.t) : m'.a ∉ walk N (some m.a) m.t := by
  intro h
  obtain ⟨k, hk, e, hlt⟩ := mem_walk h
  cases hN.uniq k hk m' hm' (Or.inr e)
  exact absurd (lt_of_lt_of_le (WithBot.coe_lt_coe.1 hlt) hle) (lt_irrefl _)

/-- Removing a node with the largest timestamp from a nonempty TI tree. -/
theorem exists_cons_max {N : List (Node U)} (hN : IsTITree N) (hne : N ≠ []) :
    ∃ n ∈ N, N.Perm (n :: N.erase n) ∧ IsTITree (n :: N.erase n) ∧
      ∀ m ∈ N.erase n, m.t < n.t := by
  obtain ⟨n, hn, hmax⟩ : ∃ n ∈ N, ∀ m ∈ N, m.t ≤ n.t := by
    clear hN
    induction N with
    | nil => exact absurd rfl hne
    | cons y l ih =>
      by_cases hl : l = []
      · subst hl; exact ⟨y, by simp, by simp⟩
      obtain ⟨n, hn, h⟩ := ih hl
      rcases le_total y.t n.t with hyn | hny
      · exact ⟨n, List.mem_cons_of_mem _ hn, by simpa [hyn] using h⟩
      · exact ⟨y, by simp, by simpa using fun m hm => (h m hm).trans hny⟩
  have hp := List.perm_cons_erase hn
  refine ⟨n, hn, hp, hN.perm hp, fun m hm => ?_⟩
  rw [hN.nodup.mem_erase_iff] at hm
  exact lt_of_le_of_ne (hmax m hm.2) fun e => hm.1 (hN.inj m hm.2 n hn e)

/-- The key computation behind `s_cons_max`: adding a node `n` with the largest timestamp
inserts `n.a` right after every occurrence of its parent, below any (valid) node `p`. -/
theorem walk_cons_max {N : List (Node U)} {n : Node U} (hN : IsTITree (n :: N))
    (hmax : ∀ m ∈ N, m.t < n.t) (p : Option U) (t : WithBot TS)
    (hv : (p = none ∧ t = ⊥) ∨ ∃ m ∈ N, p = some m.a ∧ t = m.t) :
    walk (n :: N) p t =
      if n.p = p then n.a :: walk N p t else insEvery n.p n.a (walk N p t) := by
  have hN' := hN.of_cons_max hmax
  revert hv
  refine walk_induction N (P := fun p t => ((p = none ∧ t = ⊥) ∨ ∃ m ∈ N, p = some m.a ∧ t = m.t) →
    walk (n :: N) p t =
      if n.p = p then n.a :: walk N p t else insEvery n.p n.a (walk N p t)) ?_ p t
  intro p t ih hv
  have hlt : n.p = p → t < (n.t : WithBot TS) := by
    intro hp
    rcases hv with ⟨_, rfl⟩ | ⟨m, hm, rfl, rfl⟩
    · exact WithBot.bot_lt_coe _
    · exact WithBot.coe_lt_coe.2 (hN.older m (List.mem_cons_of_mem _ hm) n List.mem_cons_self hp)
  have hch := children_cons_max hN.nodup hN.inj hmax p t
  have hrec : ∀ m ∈ children N p t, walk (n :: N) (some m.a) m.t =
      if n.p = some m.a then n.a :: walk N (some m.a) m.t
      else insEvery n.p n.a (walk N (some m.a) m.t) := by
    intro m hm
    rw [mem_children] at hm
    exact ih m hm.1 hm.2.1 hm.2.2 (Or.inr ⟨m, hm.1, rfl, rfl⟩)
  rw [walk_eq, walk_eq (N := N), hch]
  by_cases hp : n.p = p
  · rw [ite_eq_left ⟨hp, hlt hp⟩, ite_eq_left hp, List.flatMap_cons]
    have hleaf : walk (n :: N) (some n.a) n.t = [] := by
      rw [walk_eq, List.flatMap_eq_nil_iff]
      intro m hm
      rw [mem_children] at hm
      rcases List.mem_cons.1 hm.1 with rfl | hm1
      · exact absurd (WithBot.coe_lt_coe.1 hm.2.2) (lt_irrefl _)
      · exact absurd (lt_trans (WithBot.coe_lt_coe.1 hm.2.2) (hmax m hm1)) (lt_irrefl _)
    rw [hleaf]
    simp only [List.cons_append, List.nil_append, List.cons.injEq, true_and]
    refine List.flatMap_congr fun m hm => ?_
    rw [hrec m hm]
    rw [mem_children] at hm
    have hne : n.p ≠ some m.a := by
      intro e
      have := hN'.older m hm.1 m hm.1 (hm.2.1.trans (hp.symm.trans e))
      exact lt_irrefl _ this
    rw [ite_eq_right hne]
    congr 1
    rcases hv with ⟨rfl, _⟩ | ⟨mb, hmb, rfl, rfl⟩
    · rw [hp, insEvery_none]
    · rw [hp, insEvery_of_not_mem (not_mem_walk_of_le hN' hmb
        (le_of_lt (WithBot.coe_lt_coe.1 hm.2.2)))]
  · rw [ite_eq_right (fun h => hp h.1), ite_eq_right hp, insEvery_flatMap]
    refine List.flatMap_congr fun m hm => ?_
    rw [hrec m hm, insEvery_cons]
    rw [mem_children] at hm
    split_ifs with h1 h2 h2
    · rw [h1, insEvery_of_not_mem (not_mem_walk_of_le hN' hm.1 le_rfl)]; rfl
    · exact absurd h1.symm h2
    · exact absurd h2.symm h1
    · rfl

/-- General form of `s_cons_max` (no duplicate-freeness of `s N` needed). -/
theorem s_cons_max' {N : List (Node U)} {n : Node U} (hN : IsTITree (n :: N))
    (hmax : ∀ m ∈ N, m.t < n.t) :
    s (n :: N) = if n.p = none then n.a :: s N else insEvery n.p n.a (s N) :=
  walk_cons_max hN hmax none ⊥ (Or.inl ⟨rfl, rfl⟩)

theorem walk_perm {N N' : List (Node U)} (hN : IsTITree N) (h : N.Perm N') :
    ∀ p t, walk N p t = walk N' p t :=
  walk_induction N fun p t ih => by
    rw [walk_eq, walk_eq (N := N'), ← children_perm h hN.nodup hN.inj p t]
    refine List.flatMap_congr fun m hm => ?_
    rw [mem_children] at hm
    rw [ih m hm.1 hm.2.1 hm.2.2]

@[simp] theorem s_nil : s ([] : List (Node U)) = [] := by
  rw [s, walk_eq]; simp [children]

theorem s_nodup_and_mem (k : ℕ) : ∀ N : List (Node U), N.length = k → IsTITree N →
    (s N).Nodup ∧ ∀ a, a ∈ s N ↔ ∃ n ∈ N, n.a = a := by
  induction k with
  | zero =>
    intro N hk _
    rw [List.length_eq_zero_iff.1 hk]
    simp
  | succ k ih =>
    intro N hk hN
    have hne : N ≠ [] := by rintro rfl; simp at hk
    obtain ⟨n, hn, hp, hT, hmax⟩ := exists_cons_max hN hne
    have hN' := hT.of_cons_max hmax
    obtain ⟨ihn, ihm⟩ := ih (N.erase n) (by rw [List.length_erase_of_mem hn]; omega) hN'
    have hnN' : n ∉ N.erase n := (List.nodup_cons.1 hT.nodup).1
    have hna : n.a ∉ s (N.erase n) := fun h => by
      obtain ⟨m, hm, e⟩ := (ihm _).1 h
      exact hnN' (hT.uniq m (List.mem_cons_of_mem _ hm) n List.mem_cons_self (Or.inr e) ▸ hm)
    have hperm : (s (n :: N.erase n)).Perm (n.a :: s (N.erase n)) := by
      rw [s_cons_max' hT hmax]
      split_ifs with hnp
      · exact List.Perm.refl _
      · obtain ⟨b, hb⟩ := Option.ne_none_iff_exists'.1 hnp
        rw [hb]
        refine insEvery_perm ihn ?_
        obtain ⟨n', hn', e⟩ := hT.parent n List.mem_cons_self b hb
        rcases List.mem_cons.1 hn' with rfl | hn'
        · exact absurd (hT.older n' List.mem_cons_self n' List.mem_cons_self (e ▸ hb))
            (lt_irrefl _)
        · exact (ihm b).2 ⟨n', hn', e⟩
    have hsN : s N = s (n :: N.erase n) := walk_perm hN hp none ⊥
    rw [hsN]
    refine ⟨hperm.nodup_iff.2 (List.nodup_cons.2 ⟨hna, ihn⟩), fun a => ?_⟩
    rw [hperm.mem_iff, List.mem_cons, ihm]
    simp only [hp.mem_iff, List.mem_cons, or_and_right, exists_or, exists_eq_left]
    exact or_congr_left eq_comm

/-- The elements of a TI tree are exactly the elements of `s N`, without repetitions. -/
theorem s_nodup {N : List (Node U)} (hN : IsTITree N) : (s N).Nodup :=
  (s_nodup_and_mem _ N rfl hN).1

theorem mem_s {N : List (Node U)} (hN : IsTITree N) {a : U} : a ∈ s N ↔ ∃ n ∈ N, n.a = a :=
  (s_nodup_and_mem _ N rfl hN).2 a

/-- `s N` depends only on the set of nodes. -/
theorem s_perm {N N' : List (Node U)} (hN : IsTITree N) (h : N.Perm N') : s N = s N' :=
  walk_perm hN h none ⊥

/-- Adding a node with the largest timestamp places its element right after its parent (the
remark after the insert procedure of Section 4.1). -/
theorem s_cons_max {N : List (Node U)} {n : Node U} (hN : IsTITree (n :: N))
    (hmax : ∀ m ∈ N, m.t < n.t) : s (n :: N) = insAfter n.p n.a (s N) := by
  rw [s_cons_max' hN hmax]
  cases hnp : n.p with
  | none => rfl
  | some b => exact insEvery_eq_insAfter (s_nodup (hN.of_cons_max hmax))

/-- **Lemma 6.** If `A ⊆ B` are TI trees, then `s(A)` is a subsequence of `s(B)`. -/
theorem s_sublist {A B : List (Node U)} (hA : IsTITree A) (hB : IsTITree B)
    (hAB : ∀ n ∈ A, n ∈ B) : (s A).Sublist (s B) := by
  induction hk : B.length generalizing A B with
  | zero =>
    rw [List.length_eq_zero_iff] at hk
    subst hk
    have hA0 : A = [] := List.eq_nil_iff_forall_not_mem.2 fun n hn => by simpa using hAB n hn
    subst hA0
    simp
  | succ k ih =>
    have hne : B ≠ [] := by rintro rfl; simp at hk
    obtain ⟨n, hn, hp, hT, hmax⟩ := exists_cons_max hB hne
    have hB' := hT.of_cons_max hmax
    have hk' : (B.erase n).length = k := by rw [List.length_erase_of_mem hn]; omega
    rw [s_perm hB hp, s_cons_max' hT hmax]
    by_cases hnA : n ∈ A
    · have hpA := List.perm_cons_erase hnA
      have hsub : ∀ m ∈ A.erase n, m ∈ B.erase n := by
        intro m hm
        rw [hA.nodup.mem_erase_iff] at hm
        rw [hB.nodup.mem_erase_iff]
        exact ⟨hm.1, hAB m hm.2⟩
      have hTA := hA.perm hpA
      have hmaxA : ∀ m ∈ A.erase n, m.t < n.t := fun m hm => hmax m (hsub m hm)
      have := ih (hTA.of_cons_max hmaxA) hB' hsub hk'
      rw [s_perm hA hpA, s_cons_max' hTA hmaxA]
      split_ifs
      · exact this.cons_cons _
      · exact Sublist.insEvery this _ _
    · have hsub : ∀ m ∈ A, m ∈ B.erase n := by
        intro m hm
        rw [hB.nodup.mem_erase_iff]
        exact ⟨fun e => hnA (e ▸ hm), hAB m hm⟩
      refine (ih hA hB' hsub hk').trans ?_
      split_ifs
      · exact List.sublist_cons_self _ _
      · exact sublist_insEvery _ _ _

end Podc.CollaborativeListSpec
