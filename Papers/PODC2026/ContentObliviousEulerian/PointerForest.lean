import Mathlib

-- CSLib candidate: Cslib/Foundations/Combinatorics/PointerForest.lean (max-neighbour pointer forests)

/-!
# Pointer forests of a merging phase

Pure combinatorics behind one GHS-style merging phase of the content-oblivious leader election
algorithm ("Brief Announcement: Toward Uniform Content-Oblivious Leader Election on General
Graphs", PODC 2026).

We have a finite set `α` of *circuits* (vertices of a contracted graph), a symmetric irreflexive
adjacency `adj` in which every vertex has a neighbour, and injective IDs `id`. Every vertex `x`
points to its neighbour `ptr x` of maximal ID. A vertex `x` is a *root* if `x` and `ptr x` point
to each other and `x` is the larger of the two. Every non-root merges along the link
`x — ptr x`.

Main results:
* `iterate_ne_self`: the pointer graph has no cycles through non-roots (its only cycles are
  2-cycles, each containing a root);
* `top`: the first root on the pointer chain of a vertex;
* `addLink_equivalence`, `linkRel_equivalence`: executing merge links keeps an equivalence;
* `not_linkRel_of_nodup`: the merge links form a forest — each executed link joins two
  *different* current classes;
* `linkRel_iff_top`: after all links, two vertices are merged iff they have the same `top`;
* `id_le_id_top_of_top_eq`: the root is the maximum-ID element of its class;
* `two_mul_card_image_top_le`: the number of classes at least halves.
-/

namespace Podc.ContentObliviousEulerian.Pointer

open Classical

/-- The setting of one merging phase: a finite symmetric irreflexive adjacency without isolated
vertices, and injective IDs. -/
structure Setting (α : Type*) [Fintype α] [DecidableEq α] where
  /-- Adjacency between circuits. -/
  adj : α → α → Prop
  /-- Adjacency is symmetric. -/
  symm : ∀ {x y}, adj x y → adj y x
  /-- Adjacency is irreflexive. -/
  irrefl : ∀ x, ¬ adj x x
  /-- The ID (of the leader) of each circuit. -/
  id : α → ℕ
  /-- IDs are distinct. -/
  id_inj : Function.Injective id
  /-- Every circuit has a neighbour. -/
  exists_adj : ∀ x, ∃ y, adj x y

variable {α : Type*} [Fintype α] [DecidableEq α] (S : Setting α)

/-- Every vertex has a neighbour of maximal ID. -/
theorem exists_ptr (x : α) : ∃ z, S.adj x z ∧ ∀ y, S.adj x y → S.id y ≤ S.id z := by
  obtain ⟨y0, hy0⟩ := S.exists_adj x
  obtain ⟨z, hz, hmax⟩ := Set.exists_max_image {y | S.adj x y} S.id (Set.toFinite _) ⟨y0, hy0⟩
  exact ⟨z, hz, hmax⟩

/-- The pointer of `x`: its neighbour with maximal ID. -/
noncomputable def ptr (x : α) : α := Classical.choose (exists_ptr S x)

/-- The pointer of `x` is a neighbour of `x`. -/
theorem adj_ptr (x : α) : S.adj x (ptr S x) := (Classical.choose_spec (exists_ptr S x)).1

/-- The pointer of `x` has the maximal ID among the neighbours of `x`. -/
theorem id_le_id_ptr {x y : α} (h : S.adj x y) : S.id y ≤ S.id (ptr S x) :=
  (Classical.choose_spec (exists_ptr S x)).2 y h

/-- The pointer is uniquely characterized by its specification. -/
theorem eq_ptr_iff {x z : α} :
    z = ptr S x ↔ S.adj x z ∧ ∀ y, S.adj x y → S.id y ≤ S.id z := by
  constructor
  · rintro rfl
    exact ⟨adj_ptr S x, fun y h => id_le_id_ptr S h⟩
  · rintro ⟨hz, hmax⟩
    exact S.id_inj (le_antisymm (id_le_id_ptr S hz) (hmax _ (adj_ptr S x)))

/-- No vertex points to itself. -/
theorem ptr_ne (x : α) : ptr S x ≠ x := by
  intro h
  have := adj_ptr S x
  rw [h] at this
  exact S.irrefl x this

/-- Two pointer steps never decrease the ID: `x` is a neighbour of `ptr x`. -/
theorem id_le_id_ptr_ptr (x : α) : S.id x ≤ S.id (ptr S (ptr S x)) :=
  id_le_id_ptr S (S.symm (adj_ptr S x))

/-- Two pointer steps keep the ID iff they return to the start. -/
theorem id_ptr_ptr_eq_iff (x : α) : S.id (ptr S (ptr S x)) = S.id x ↔ ptr S (ptr S x) = x :=
  ⟨fun h => S.id_inj h, fun h => by rw [h]⟩

/-- A root: `x` and `ptr x` point to each other and `x` has the larger ID (so `x` does not
merge). -/
def IsRoot (x : α) : Prop := ptr S (ptr S x) = x ∧ S.id (ptr S x) < S.id x

/-- The pointer of a root is not a root. -/
theorem not_isRoot_ptr {r : α} (hr : IsRoot S r) : ¬ IsRoot S (ptr S r) := by
  rintro ⟨-, h⟩
  rw [hr.1] at h
  exact lt_asymm h hr.2

/-- Every nonempty set closed under `ptr` contains a root (its maximum-ID element). -/
theorem exists_isRoot_of_closed {s : Set α} (hne : s.Nonempty)
    (hcl : ∀ x ∈ s, ptr S x ∈ s) : ∃ x ∈ s, IsRoot S x := by
  obtain ⟨c, hc, hmax⟩ := Set.exists_max_image s S.id (Set.toFinite _) hne
  have h1 := hcl _ hc
  have h2 := hcl _ h1
  have heq : ptr S (ptr S c) = c :=
    S.id_inj (le_antisymm (hmax _ h2) (id_le_id_ptr_ptr S c))
  refine ⟨c, hc, heq, lt_of_le_of_ne (hmax _ h1) ?_⟩
  intro h
  exact ptr_ne S c (S.id_inj h)

/-- Acyclicity through non-roots: a pointer chain that avoids roots never returns to its start.
(The only cycles of the pointer graph are 2-cycles, and each of them contains a root.) -/
theorem iterate_ne_self {x : α} {k : ℕ} (hk : 0 < k)
    (hnr : ∀ i < k, ¬ IsRoot S ((ptr S)^[i] x)) : (ptr S)^[k] x ≠ x := by
  intro hx
  have hcl : ∀ y ∈ {y | ∃ i < k, (ptr S)^[i] x = y}, ptr S y ∈ {y | ∃ i < k, (ptr S)^[i] x = y} := by
    rintro _ ⟨i, hi, rfl⟩
    by_cases h : i + 1 < k
    · exact ⟨i + 1, h, Function.iterate_succ_apply' _ _ _⟩
    · refine ⟨0, hk, ?_⟩
      have hik : i + 1 = k := by omega
      have : (ptr S)^[k] x = ptr S ((ptr S)^[i] x) := by
        rw [← hik, Function.iterate_succ_apply']
      rw [← this, hx, Function.iterate_zero_apply]
  obtain ⟨c, ⟨i, hi, rfl⟩, hc⟩ := exists_isRoot_of_closed S (s := {y | ∃ i < k, (ptr S)^[i] x = y}) ⟨x, 0, hk, rfl⟩ hcl
  exact hnr i hi hc

/-- Every pointer chain reaches a root. -/
theorem exists_iterate_isRoot (x : α) : ∃ n, IsRoot S ((ptr S)^[n] x) := by
  obtain ⟨c, ⟨n, rfl⟩, hc⟩ := exists_isRoot_of_closed S (s := Set.range fun n => (ptr S)^[n] x)
    (show (Set.range fun n => (ptr S)^[n] x).Nonempty from ⟨x, 0, rfl⟩) (by rintro _ ⟨n, rfl⟩; exact ⟨n + 1, Function.iterate_succ_apply' _ _ _⟩)
  exact ⟨n, hc⟩

/-! ### First hit of a predicate along a pointer chain -/

/-- The first element of the chain `x, ptr x, ptr² x, …` satisfying `P` (or `x` if there is
none). -/
noncomputable def stopAt (P : α → Prop) (x : α) : α :=
  if h : ∃ n, P ((ptr S)^[n] x) then (ptr S)^[Nat.find h] x else x

/-- Specification of `stopAt`. -/
theorem stopAt_spec {P : α → Prop} {x : α} (h : ∃ n, P ((ptr S)^[n] x)) :
    ∃ n, stopAt S P x = (ptr S)^[n] x ∧ P ((ptr S)^[n] x) ∧ ∀ i < n, ¬ P ((ptr S)^[i] x) :=
  ⟨Nat.find h, by rw [stopAt, dite_eq_left h], Nat.find_spec h, fun _ hi => Nat.find_min h hi⟩

/-- `stopAt` satisfies `P` (when `P` is reached). -/
theorem stopAt_mem {P : α → Prop} {x : α} (h : ∃ n, P ((ptr S)^[n] x)) : P (stopAt S P x) := by
  obtain ⟨n, hn, hP, -⟩ := stopAt_spec S h
  rw [hn]; exact hP

/-- If `x` satisfies `P`, the chain stops at `x`. -/
theorem stopAt_of {P : α → Prop} {x : α} (hx : P x) : stopAt S P x = x := by
  have h : ∃ n, P ((ptr S)^[n] x) := ⟨0, hx⟩
  rw [stopAt, dite_eq_left h]
  have : Nat.find h = 0 := (Nat.find_eq_zero h).2 hx
  rw [this, Function.iterate_zero_apply]

/-- If `x` does not satisfy `P`, the chain of `x` stops where the chain of `ptr x` stops. -/
theorem stopAt_ptr {P : α → Prop} {x : α} (hx : ¬ P x) (h : ∃ n, P ((ptr S)^[n] x)) :
    stopAt S P (ptr S x) = stopAt S P x := by
  obtain ⟨n, hn, hP, hmin⟩ := stopAt_spec S h
  have hn0 : n ≠ 0 := by rintro rfl; exact hx hP
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn0
  have h' : ∃ n, P ((ptr S)^[n] (ptr S x)) := ⟨m, by rwa [← Function.iterate_succ_apply]⟩
  obtain ⟨m', hm', hP', hmin'⟩ := stopAt_spec S h'
  rw [hn, hm', ← Function.iterate_succ_apply]
  congr 1
  rcases lt_trichotomy m' m with hlt | heq | hgt
  · exact absurd (by rwa [← Function.iterate_succ_apply] at hP') (hmin _ (Nat.succ_lt_succ hlt))
  · rw [heq]
  · exact absurd (by rwa [Function.iterate_succ_apply] at hP) (hmin' _ hgt)

/-- Following the chain for `n` steps without meeting `P` does not change `stopAt P`. -/
theorem stopAt_iterate {P : α → Prop} (hP : ∀ y, ∃ n, P ((ptr S)^[n] y)) :
    ∀ (n : ℕ) (x : α), (∀ i < n, ¬ P ((ptr S)^[i] x)) → stopAt S P x = stopAt S P ((ptr S)^[n] x)
  | 0, _, _ => rfl
  | n + 1, x, h => by
    rw [← stopAt_ptr S (P := P) (x := x) (h 0 (Nat.succ_pos _)) (hP x), Function.iterate_succ_apply]
    exact stopAt_iterate hP n _ fun i hi => by
      rw [← Function.iterate_succ_apply]; exact h _ (Nat.succ_lt_succ hi)

/-- For a stronger stopping predicate `P' → P`, stopping first at `P` does not change the
`P'`-stop. -/
theorem stopAt_stopAt {P P' : α → Prop} (hPP : ∀ y, P' y → P y)
    (hP' : ∀ y, ∃ n, P' ((ptr S)^[n] y)) (x : α) :
    stopAt S P' (stopAt S P x) = stopAt S P' x := by
  have h : ∃ n, P ((ptr S)^[n] x) := by
    obtain ⟨n, hn⟩ := hP' x; exact ⟨n, hPP _ hn⟩
  obtain ⟨n, hn, -, hmin⟩ := stopAt_spec S h
  rw [hn, stopAt_iterate S hP' n x fun i hi h' => hmin i hi (hPP _ h')]

/-! ### The top (root) of a chain -/

/-- The first root on the pointer chain `x, ptr x, ptr² x, …`. -/
noncomputable def top (x : α) : α := stopAt S (IsRoot S) x

/-- The top of a chain is a root. -/
theorem isRoot_top (x : α) : IsRoot S (top S x) := stopAt_mem S (exists_iterate_isRoot S x)

/-- A root is its own top. -/
theorem top_of_isRoot {x : α} (hx : IsRoot S x) : top S x = x := stopAt_of S hx

/-- A non-root has the same top as its pointer. -/
theorem top_ptr {x : α} (hx : ¬ IsRoot S x) : top S (ptr S x) = top S x :=
  stopAt_ptr S hx (exists_iterate_isRoot S x)

/-- The pointer of a root `r` has top `r`. -/
theorem top_ptr_of_isRoot {r : α} (hr : IsRoot S r) : top S (ptr S r) = r := by
  rw [← top_ptr S (not_isRoot_ptr S hr), hr.1, top_of_isRoot S hr]

/-- An even number of pointer steps never decreases the ID. -/
theorem id_le_id_iterate_two_mul : ∀ (k : ℕ) (z : α), S.id z ≤ S.id ((ptr S)^[2 * k] z)
  | 0, _ => le_rfl
  | k + 1, z => by
    rw [show 2 * (k + 1) = 2 * k + 2 by ring, Function.iterate_add_apply]
    exact (id_le_id_ptr_ptr S z).trans (id_le_id_iterate_two_mul k _)

/-- Every vertex has ID at most that of its top. -/
theorem id_le_id_top (y : α) : S.id y ≤ S.id (top S y) := by
  obtain ⟨n, hn, hR, -⟩ := stopAt_spec S (exists_iterate_isRoot S y)
  change top S y = _ at hn
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' n
  · rw [hn]; exact id_le_id_iterate_two_mul S k y
  · have h1 := id_le_id_iterate_two_mul S (k + 1) y
    rw [show 2 * (k + 1) = (2 * k + 1) + 1 by ring, Function.iterate_succ_apply', ← hn] at h1
    exact h1.trans (isRoot_top S y).2.le

/-- The root is the maximum-ID element of its class. -/
theorem id_le_id_top_of_top_eq {x y : α} (h : top S x = top S y) :
    S.id y ≤ S.id (top S x) := by
  rw [h]; exact id_le_id_top S y

/-- Halving: the number of classes (roots reached as tops) is at most half the number of
vertices, since each class contains its root `r` and the distinct non-root `ptr r`. -/
theorem two_mul_card_image_top_le :
    2 * (Finset.univ.image (top S)).card ≤ Fintype.card α := by
  set R := Finset.univ.image (top S)
  have hR : ∀ r ∈ R, IsRoot S r := by
    intro r hr
    obtain ⟨x, -, rfl⟩ := Finset.mem_image.1 hr
    exact isRoot_top S x
  have hinj : Set.InjOn (ptr S) R := fun a ha b hb hab => by
    rw [← (hR a ha).1, ← (hR b hb).1, hab]
  have hdisj : Disjoint R (R.image (ptr S)) := by
    rw [Finset.disjoint_left]
    intro a ha hb
    obtain ⟨b, hb', rfl⟩ := Finset.mem_image.1 hb
    exact not_isRoot_ptr S (hR b hb') (hR _ ha)
  have := Finset.card_le_univ (R ∪ R.image (ptr S))
  rw [Finset.card_union_of_disjoint hdisj, Finset.card_image_of_injOn hinj] at this
  omega

/-! ### Executing the merge links -/

/-- Add the link `s — t` to a relation (one merge). -/
def addLink (r : α → α → Prop) (s t : α) : α → α → Prop :=
  fun x y => r x y ∨ ((r s x ∨ r t x) ∧ (r s y ∨ r t y))

omit [Fintype α] [DecidableEq α] in
/-- Adding a link to an equivalence relation gives an equivalence relation. -/
theorem addLink_equivalence {r : α → α → Prop} (hr : Equivalence r) (s t : α) :
    Equivalence (addLink r s t) where
  refl x := Or.inl (hr.refl x)
  symm := by
    rintro x y (h | ⟨h1, h2⟩)
    · exact Or.inl (hr.symm h)
    · exact Or.inr ⟨h2, h1⟩
  trans := by
    have hA : ∀ {x y}, r x y → (r s x ∨ r t x) → (r s y ∨ r t y) := by
      rintro x y hxy (h | h)
      · exact Or.inl (hr.trans h hxy)
      · exact Or.inr (hr.trans h hxy)
    rintro x y z (h | ⟨h1, h2⟩) (h' | ⟨h1', h2'⟩)
    · exact Or.inl (hr.trans h h')
    · exact Or.inr ⟨hA (hr.symm h) h1', h2'⟩
    · exact Or.inr ⟨h1, hA h' h2⟩
    · exact Or.inr ⟨h1, h2'⟩

omit [Fintype α] [DecidableEq α] in
/-- Adding a link that is already present does not change an equivalence relation. -/
theorem addLink_iff_of_rel {r : α → α → Prop} (hr : Equivalence r) {s t : α} (hst : r s t)
    (x y : α) : addLink r s t x y ↔ r x y := by
  refine ⟨?_, Or.inl⟩
  have hA : ∀ {x}, (r s x ∨ r t x) → r s x := by
    rintro x (h | h)
    · exact h
    · exact hr.trans hst h
  rintro (h | ⟨h1, h2⟩)
  · exact h
  · exact hr.trans (hr.symm (hA h1)) (hA h2)

/-- The relation after executing the links `s — ptr s`, `s ∈ l`, in order. -/
def linkRel (l : List α) : α → α → Prop := l.foldl (fun r s => addLink r s (ptr S s)) Eq

/-- Unfolding the last executed link. -/
theorem linkRel_append_singleton (l : List α) (s : α) :
    linkRel S (l ++ [s]) = addLink (linkRel S l) s (ptr S s) := by
  simp [linkRel, List.foldl_append]

/-- `linkRel l` is an equivalence relation. -/
theorem linkRel_equivalence (l : List α) : Equivalence (linkRel S l) := by
  induction l using List.reverseRecOn with
  | nil => exact ⟨fun _ => rfl, fun h => h.symm, fun h h' => h.trans h'⟩
  | append_singleton l s ih =>
    rw [linkRel_append_singleton]
    exact addLink_equivalence ih s _

/-- If all elements of `l` are non-roots, every chain eventually leaves `l`. -/
theorem exists_iterate_notMem {l : List α} (hl : ∀ s ∈ l, ¬ IsRoot S s) (x : α) :
    ∃ n, (ptr S)^[n] x ∉ l := by
  by_contra h
  simp only [not_exists, not_not] at h
  obtain ⟨n, hn⟩ := exists_iterate_isRoot S x
  exact hl _ (h n) hn

/-- Forest property of the pointer chains: for a non-root `s` and a list `l` of non-roots,
the chain of `ptr s` does not first leave `l` at `s` (that would close a cycle of non-roots). -/
theorem stopAt_ptr_ne {l : List α} (hl : ∀ x ∈ l, ¬ IsRoot S x) {s : α}
    (hsr : ¬ IsRoot S s) : stopAt S (· ∉ l) (ptr S s) ≠ s := by
  obtain ⟨n, hn, -, hmin⟩ := stopAt_spec S (P := (· ∉ l)) (exists_iterate_notMem S hl (ptr S s))
  rw [hn]
  intro heq
  refine iterate_ne_self S (x := s) (k := n + 1) (Nat.succ_pos _) ?_
    (by rw [Function.iterate_succ_apply, heq])
  intro i hi
  rcases i with _ | j
  · exact hsr
  · rw [Function.iterate_succ_apply]
    exact hl _ (not_not.1 (hmin j (by omega)))

/-- Invariant: after executing the links of a prefix `l` of non-roots, two vertices are related
iff their chains first leave `l` at the same vertex. -/
theorem linkRel_iff_stopAt {l : List α} (hl : ∀ s ∈ l, ¬ IsRoot S s) (x y : α) :
    linkRel S l x y ↔ stopAt S (· ∉ l) x = stopAt S (· ∉ l) y := by
  induction l using List.reverseRecOn generalizing x y with
  | nil =>
    rw [stopAt_of S (List.not_mem_nil (a := x)), stopAt_of S (List.not_mem_nil (a := y))]
    rfl
  | append_singleton l s ih =>
    have hl' : ∀ x ∈ l, ¬ IsRoot S x := fun x hx => hl x (List.mem_append_left _ hx)
    have hsr : ¬ IsRoot S s := hl s (List.mem_append_right _ (List.mem_singleton_self _))
    have ih := ih hl'
    rw [linkRel_append_singleton]
    by_cases hs : s ∈ l
    · have hP : (fun x => x ∉ l ++ [s]) = (fun x => x ∉ l) := by
        funext x; simp only [List.mem_append, List.mem_singleton]
        apply propext; constructor
        · exact fun h h' => h (Or.inl h')
        · rintro h (h' | rfl) <;> [exact h h'; exact h hs]
      rw [hP, addLink_iff_of_rel (linkRel_equivalence S l) ((ih _ _).2 _), ih]
      exact (stopAt_ptr S (P := (· ∉ l)) (not_not.2 hs) (exists_iterate_notMem S hl' s)).symm
    · set T := stopAt S (· ∉ l) with hT
      set T' := stopAt S (· ∉ l ++ [s]) with hT'
      set u := T (ptr S s) with hu
      have hus : u ≠ s := stopAt_ptr_ne S hl' hsr
      have hTs : T s = s := stopAt_of S hs
      have huM : u ∉ l := stopAt_mem S (P := (· ∉ l)) (exists_iterate_notMem S hl' _)
      have hreach' := exists_iterate_notMem S hl
      have hTT : ∀ x, T' (T x) = T' x := fun x =>
        stopAt_stopAt S (P := (· ∉ l)) (P' := (· ∉ l ++ [s]))
          (fun y hy h => hy (List.mem_append_left _ h)) hreach' x
      have hfix : ∀ z, z ∉ l → z ≠ s → T' z = z := fun z hz hzs =>
        stopAt_of S (P := (· ∉ l ++ [s])) (by simp [hz, hzs])
      have hT'x : ∀ x, T' x = if T x = s then u else T x := by
        intro x
        rw [← hTT x]
        split_ifs with h
        · rw [h, show T' s = T' (ptr S s) from
            (stopAt_ptr S (P := (· ∉ l ++ [s])) (by simp) (hreach' s)).symm, ← hTT, ← hu,
            hfix u huM hus]
        · exact hfix _ (stopAt_mem S (P := (· ∉ l)) (exists_iterate_notMem S hl' x)) h
      simp only [addLink, ih, hT'x, hTs, ← hu]
      by_cases hx : T x = s <;> by_cases hy : T y = s <;>
        simp only [hx, hy, ite_true, ite_false] <;> grind

/-- Forest property: when the links `s — ptr s` of a duplicate-free list `l` of non-roots are
executed in order, each link joins two *different* current classes. -/
theorem not_linkRel_of_nodup {l l₁ l₂ : List α} {s : α} (hnd : l.Nodup)
    (hl : ∀ x ∈ l, ¬ IsRoot S x) (hs : l = l₁ ++ s :: l₂) : ¬ linkRel S l₁ s (ptr S s) := by
  subst hs
  have hl₁ : ∀ x ∈ l₁, ¬ IsRoot S x := fun x hx => hl x (List.mem_append_left _ hx)
  have hsr : ¬ IsRoot S s := hl s (List.mem_append_right _ (List.mem_cons_self))
  have hsl : s ∉ l₁ := fun h =>
    (List.nodup_append.1 hnd).2.2 s h s List.mem_cons_self rfl
  rw [linkRel_iff_stopAt S hl₁, stopAt_of S (P := (· ∉ l₁)) hsl]
  exact fun h => stopAt_ptr_ne S hl₁ hsr h.symm

/-- Final classes: after executing the links of all non-roots (each once), two vertices are in
the same class iff they have the same top (root). -/
theorem linkRel_iff_top {l : List α} (hmem : ∀ x, x ∈ l ↔ ¬ IsRoot S x) (x y : α) :
    linkRel S l x y ↔ top S x = top S y := by
  have hl : ∀ x ∈ l, ¬ IsRoot S x := fun x hx => (hmem x).1 hx
  have hP : (fun x => x ∉ l) = IsRoot S := by
    funext x; rw [hmem x, not_not]
  rw [linkRel_iff_stopAt S hl, hP]
  rfl

end Podc.ContentObliviousEulerian.Pointer
