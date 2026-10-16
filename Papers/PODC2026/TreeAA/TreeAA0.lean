import Papers.PODC2026.TreeAA.Protocol

/-!
# The initial protocol `TreeAA₀` (Section 4.3): Lemmas 3–5 and Theorem 3

* `children`, `tourAux`, `listConstruction` — `ListConstruction(T, v_root)`: the depth-first
  traversal list (Euler tour) of the tree rooted at `r`, children visited in label order.
* `listConstruction_adj`, `length_listConstruction_le`, `mem_listConstruction`,
  `subtree_iff_indices`, `exists_median_between` — **Lemma 3** (properties 1–4).
* `rpath_listConstruction_meets_hull` — **Lemma 4**.
* `pathsFinder0_spec` — **Lemma 5** (spec level).
* `treeAA0_spec` — the correctness argument of **Theorem 3** at spec level.
* `treeAA0`, `treeAA0_solves` — **Theorem 3** in the lock-step model: two RealAA black boxes run
  sequentially; within `R_RealAA(2|V(T)|, 1) + R_RealAA(D(T), 1)` rounds.

Indices are 0-based (the paper's are 1-based).

Proof structure for Lemma 3: `tourAux_decomp` (block structure: the traversal from `v` contains
the traversal from each descendant `w` as a contiguous block, outside of which no vertex of the
subtree of `w` occurs, followed by the parent of `w`), `mem_tourAux`, `length_tourAux`
(`|tour v| = 2·|subtree v| - 1`), `isChain_tourAux`. Lemma 3.2–3.4 need `T` to be a tree
(`include hT`); e.g. for the 4-cycle `r–a–b–c–r` the traversal is `r a b a r c b c r`, of
length `9 > 2·4`.
-/

namespace TreeAA

open Cslib.Byzantine.LockStep SimpleGraph

variable {V : Type*} [Fintype V] [LinearOrder V] {T : SimpleGraph V} (hT : T.IsTree)

/-! ### ListConstruction (Euler tour) -/

open Classical in
/-- The children of `v` in `T` rooted at `r` (the neighbours one step farther from `r`), sorted
by label. -/
noncomputable def children (r v : V) : List V :=
  (Finset.univ.filter fun w => T.Adj v w ∧ T.dist r w = T.dist r v + 1).sort

/-- The depth-first traversal from `v` (with fuel `n`): `v`, then for every child `c` in order,
the traversal from `c` followed by `v` again. -/
noncomputable def tourAux (r : V) : ℕ → V → List V
  | 0, v => [v]
  | n + 1, v => v :: (children (T := T) r v).flatMap fun c => tourAux r n c ++ [v]

/-- **`ListConstruction(T, v_root)`**: the depth-first traversal list from the root (the fuel
`|V|` exceeds the height of the tree). -/
noncomputable def listConstruction (r : V) : List V := tourAux (T := T) r (Fintype.card V) r

/-! #### Structure of the traversal -/

section Tour

variable {r : V}

/-- Consecutive entries of the traversal: adjacent, one a child of the other. -/
def TourStep (r a b : V) : Prop :=
  T.Adj a b ∧ (T.dist r b = T.dist r a + 1 ∨ T.dist r a = T.dist r b + 1)

/-- The fuel `n` suffices for the traversal from `v`: the subtree of `v` has height `≤ n`. -/
def Fuel (r : V) (n : ℕ) (v : V) : Prop := ∀ u, Btw T r v u → T.dist r u ≤ T.dist r v + n

/-- The subtree of `v` (w.r.t. the root `r`): the vertices `u` with `v` on the path `r – u`. -/
noncomputable def subtree (r v : V) : Finset V := by
  classical exact Finset.univ.filter fun u => Btw T r v u

omit [LinearOrder V] in
lemma mem_subtree {v u : V} : u ∈ subtree (T := T) r v ↔ Btw T r v u := by
  classical
  unfold subtree; simp

lemma mem_children {v c : V} :
    c ∈ children (T := T) r v ↔ T.Adj v c ∧ T.dist r c = T.dist r v + 1 := by
  unfold children; simp

lemma children_nodup (r v : V) : (children (T := T) r v).Nodup := Finset.sort_nodup _ _

lemma btw_of_mem_children {v c : V} (hc : c ∈ children (T := T) r v) : Btw T r v c := by
  obtain ⟨hadj, hd⟩ := mem_children.1 hc
  unfold Btw; rw [dist_eq_one_iff_adj.2 hadj, hd]

lemma tourAux_succ (n : ℕ) (v : V) : tourAux (T := T) r (n + 1) v =
    v :: (children (T := T) r v).flatMap fun c => tourAux (T := T) r n c ++ [v] := rfl

lemma tourAux_eq_cons (n : ℕ) (v : V) : ∃ l, tourAux (T := T) r n v = v :: l := by
  cases n <;> simp [tourAux]

lemma tourAux_eq_concat (n : ℕ) (v : V) : ∃ l, tourAux (T := T) r n v = l ++ [v] := by
  cases n with
  | zero => exact ⟨[], rfl⟩
  | succ n =>
    rcases List.eq_nil_or_concat (children (T := T) r v) with h | ⟨cs, c, h⟩
    · exact ⟨[], by simp [tourAux, h]⟩
    · exact ⟨v :: ((cs.flatMap fun c => tourAux (T := T) r n c ++ [v]) ++ tourAux (T := T) r n c),
        by simp [tourAux, h, List.flatMap_append]⟩

lemma tourAux_ne_nil (n : ℕ) (v : V) : tourAux (T := T) r n v ≠ [] := by
  obtain ⟨l, hl⟩ := tourAux_eq_cons (T := T) (r := r) n v; rw [hl]; exact List.cons_ne_nil _ _

lemma tourAux_length_pos (n : ℕ) (v : V) : 0 < (tourAux (T := T) r n v).length := by
  obtain ⟨l, hl⟩ := tourAux_eq_cons (T := T) (r := r) n v; rw [hl]; simp

lemma tourAux_getElem_zero (n : ℕ) (v : V) :
    (tourAux (T := T) r n v)[0]'(tourAux_length_pos n v) = v := by
  obtain ⟨l, hl⟩ := tourAux_eq_cons (T := T) (r := r) n v; simp [hl]

lemma tourAux_getElem_last (n : ℕ) (v : V) :
    (tourAux (T := T) r n v)[(tourAux (T := T) r n v).length - 1]'(by
      have := tourAux_length_pos (T := T) (r := r) n v; omega) = v := by
  rw [← List.getLast_eq_getElem (tourAux_ne_nil n v)]
  obtain ⟨l, hl⟩ := tourAux_eq_concat (T := T) (r := r) n v; simp [hl]

/-- Consecutive entries of a traversal are parent and child. -/
lemma isChain_tourAux (n : ℕ) (v : V) : (tourAux (T := T) r n v).IsChain (TourStep (T := T) r) := by
  induction n generalizing v with
  | zero => exact List.isChain_singleton v
  | succ n ih =>
    rw [tourAux_succ]
    suffices h : ∀ cs : List V, (∀ c ∈ cs, c ∈ children (T := T) r v) →
        (v :: cs.flatMap fun c => tourAux (T := T) r n c ++ [v]).IsChain (TourStep (T := T) r) from
      h _ fun _ h => h
    intro cs hcs
    induction cs with
    | nil => exact List.isChain_singleton v
    | cons c cs ihc =>
      have hc := mem_children.1 (hcs c List.mem_cons_self)
      obtain ⟨l, hl⟩ := tourAux_eq_cons (T := T) (r := r) n c
      obtain ⟨l', hl'⟩ := tourAux_eq_concat (T := T) (r := r) n c
      have e : v :: (c :: cs).flatMap (fun c => tourAux (T := T) r n c ++ [v]) =
          (v :: tourAux (T := T) r n c) ++
            (v :: cs.flatMap fun c => tourAux (T := T) r n c ++ [v]) := by simp
      rw [e, List.isChain_append]
      refine ⟨?_, ihc fun c' h => hcs c' (List.mem_cons_of_mem _ h), ?_⟩
      · rw [hl, List.isChain_cons_cons, ← hl]
        exact ⟨⟨hc.1, Or.inl hc.2⟩, ih c⟩
      · intro a ha b hb
        rw [hl', ← List.cons_append, List.getLast?_append] at ha
        simp only [List.getLast?_singleton, Option.some_or, Option.mem_def,
          Option.some.injEq] at ha
        simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hb
        subst ha hb
        exact ⟨hc.1.symm, Or.inr hc.2⟩

/-! Tree-specific facts (from here on `T` is a tree). -/

include hT

omit [Fintype V] in
/-- Two vertices on the path from `r` to `u` at the same depth coincide. -/
lemma eq_of_btw_of_dist_eq_dist {z z' u : V} (hz : Btw T r z u) (hz' : Btw T r z' u)
    (hd : T.dist r z = T.dist r z') : z = z' := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ((mem_rpath hT).2 hz)
  obtain ⟨i', hi', rfl⟩ := List.getElem_of_mem ((mem_rpath hT).2 hz')
  have h1 := dist_rpath_getElem hT r u hi
  have h2 := dist_rpath_getElem hT r u hi'
  have : i = i' := by omega
  subst this; rfl

lemma btw_of_btw_child {v c u : V} (hc : c ∈ children (T := T) r v) (hu : Btw T r c u) :
    Btw T r v u := hu.trans hT.connected (btw_of_mem_children hc)

/-- Every proper descendant of `v` is in the subtree of a child of `v`. -/
lemma exists_child {v u : V} (hu : Btw T r v u) (huv : u ≠ v) :
    ∃ c ∈ children (T := T) r v, Btw T r c u := by
  obtain ⟨i, hi, hiv⟩ := List.getElem_of_mem ((mem_rpath hT).2 hu)
  have hdi := dist_rpath_getElem hT r u hi
  rw [hiv] at hdi
  have hlen := length_rpath hT r u
  have hlt : T.dist r v < T.dist r u := by
    rcases lt_or_eq_of_le (dist_le_of_btw hT.connected hu) with h | h
    · exact h
    · exact absurd (eq_of_btw_of_dist_eq hT.connected hu h).symm huv
  have hi1 : i + 1 < (rpath hT r u).length := by omega
  refine ⟨(rpath hT r u)[i + 1], mem_children.2 ⟨?_, ?_⟩, (mem_rpath hT).1 (List.getElem_mem _)⟩
  · rw [← hiv]; exact List.isChain_iff_getElem.1 (rpath_isChain hT r u) i hi1
  · rw [dist_rpath_getElem hT r u hi1]; omega

/-- The child of `v` above a given descendant is unique. -/
lemma child_unique {v c c' u : V} (hc : c ∈ children (T := T) r v)
    (hc' : c' ∈ children (T := T) r v) (hu : Btw T r c u) (hu' : Btw T r c' u) : c = c' :=
  eq_of_btw_of_dist_eq_dist hT hu hu' (by rw [(mem_children.1 hc).2, (mem_children.1 hc').2])

lemma fuel_child {n : ℕ} {v c : V} (hf : Fuel (T := T) r (n + 1) v)
    (hc : c ∈ children (T := T) r v) : Fuel (T := T) r n c := by
  intro u hu
  have := hf u (btw_of_btw_child hT hc hu)
  have := (mem_children.1 hc).2
  omega

omit [Fintype V] [LinearOrder V] in
lemma fuel_zero {v u : V} (hf : Fuel (T := T) r 0 v) (hu : Btw T r v u) : u = v :=
  (eq_of_btw_of_dist_eq hT.connected hu (le_antisymm (dist_le_of_btw hT.connected hu) (hf u hu))).symm

lemma fuel_root (r : V) : Fuel (T := T) r (Fintype.card V) r := by
  intro u _
  have h1 := (rpath_nodup hT r u).length_le_card
  rw [length_rpath] at h1
  simp only [SimpleGraph.dist_self, zero_add]
  omega

/-- The traversal from `v` consists of the vertices of the subtree of `v`. -/
lemma mem_tourAux {n : ℕ} {v : V} (hf : Fuel (T := T) r n v) {u : V} :
    u ∈ tourAux (T := T) r n v ↔ Btw T r v u := by
  induction n generalizing v with
  | zero =>
    simp only [tourAux, List.mem_singleton]
    constructor
    · rintro rfl; exact btw_right r u
    · exact fuel_zero hT hf
  | succ n ih =>
    simp only [tourAux, List.mem_cons, List.mem_flatMap, List.mem_append, List.mem_nil_iff,
      or_false]
    constructor
    · rintro (rfl | ⟨c, hc, hu | rfl⟩)
      · exact btw_right r u
      · exact btw_of_btw_child hT hc ((ih (fuel_child hT hf hc)).1 hu)
      · exact btw_right r u
    · intro h
      by_cases huv : u = v
      · exact Or.inl huv
      · obtain ⟨c, hc, hcu⟩ := exists_child hT h huv
        exact Or.inr ⟨c, hc, Or.inl ((ih (fuel_child hT hf hc)).2 hcu)⟩

/-- Length of the traversal: `2 · |subtree| - 1`. -/
lemma length_tourAux {n : ℕ} {v : V} (hf : Fuel (T := T) r n v) :
    (tourAux (T := T) r n v).length + 1 = 2 * (subtree (T := T) r v).card := by
  induction n generalizing v with
  | zero =>
    have : subtree (T := T) r v = {v} := by
      ext u; rw [mem_subtree, Finset.mem_singleton]
      exact ⟨fuel_zero hT hf, by rintro rfl; exact btw_right r u⟩
    simp [this, tourAux]
  | succ n ih =>
    have hlist : ∀ cs : List V, cs.Nodup → (∀ c ∈ cs, c ∈ children (T := T) r v) →
        (cs.flatMap fun c => tourAux (T := T) r n c ++ [v]).length =
          2 * (cs.toFinset.biUnion (subtree (T := T) r)).card := by
      intro cs hnd hcs
      induction cs with
      | nil => simp
      | cons c cs ihc =>
        rw [List.nodup_cons] at hnd
        have hc := hcs c List.mem_cons_self
        have hdisj : Disjoint (subtree (T := T) r c) (cs.toFinset.biUnion (subtree (T := T) r)) := by
          rw [Finset.disjoint_left]
          intro u hu hu'
          obtain ⟨c', hc', hu'⟩ := Finset.mem_biUnion.1 hu'
          rw [List.mem_toFinset] at hc'
          have := child_unique hT hc (hcs c' (List.mem_cons_of_mem _ hc'))
            (mem_subtree.1 hu) (mem_subtree.1 hu')
          exact hnd.1 (this ▸ hc')
        rw [List.flatMap_cons, List.length_append, List.toFinset_cons, Finset.biUnion_insert,
          Finset.card_union_of_disjoint hdisj, ihc hnd.2 fun c' h => hcs c' (List.mem_cons_of_mem _ h),
          List.length_append, List.length_singleton, ih (fuel_child hT hf hc)]
        ring
    have hsub : subtree (T := T) r v =
        insert v ((children (T := T) r v).toFinset.biUnion (subtree (T := T) r)) := by
      ext u
      simp only [Finset.mem_insert, Finset.mem_biUnion, List.mem_toFinset, mem_subtree]
      constructor
      · intro h
        by_cases huv : u = v
        · exact Or.inl huv
        · exact Or.inr (exists_child hT h huv)
      · rintro (rfl | ⟨c, hc, hcu⟩)
        · exact btw_right r u
        · exact btw_of_btw_child hT hc hcu
    have hv : v ∉ (children (T := T) r v).toFinset.biUnion (subtree (T := T) r) := by
      simp only [Finset.mem_biUnion, List.mem_toFinset, mem_subtree, not_exists, not_and]
      intro c hc hcv
      have := dist_le_of_btw hT.connected hcv
      have := (mem_children.1 hc).2
      omega
    rw [hsub, Finset.card_insert_of_notMem hv, tourAux_succ, List.length_cons,
      hlist _ (children_nodup r v) fun _ h => h]
    ring

/-- **Block structure** of the traversal: for every `w` in the subtree of `v`, the traversal from
`v` contains a full traversal from `w` as a contiguous block; no vertex of the subtree of `w`
occurs outside that block, and (if `w ≠ v`) the block is immediately followed by the parent
of `w`. -/
lemma tourAux_decomp {n : ℕ} {v : V} (hf : Fuel (T := T) r n v) {w : V} (hw : Btw T r v w) :
    ∃ A B m, tourAux (T := T) r n v = A ++ tourAux (T := T) r m w ++ B ∧
      Fuel (T := T) r m w ∧ (∀ z ∈ A, ¬ Btw T r w z) ∧ (∀ z ∈ B, ¬ Btw T r w z) ∧
      (w ≠ v → ∃ z B', B = z :: B' ∧ T.Adj z w ∧ T.dist r w = T.dist r z + 1) := by
  induction n generalizing v with
  | zero =>
    obtain rfl := fuel_zero hT hf hw
    exact ⟨[], [], 0, by simp, hf, by simp, by simp, fun h => absurd rfl h⟩
  | succ n ih =>
    by_cases hwv : w = v
    · subst hwv
      exact ⟨[], [], n + 1, by simp, hf, by simp, by simp, fun h => absurd rfl h⟩
    obtain ⟨c, hc, hcw⟩ := exists_child hT hw hwv
    obtain ⟨cs₁, cs₂, hcs⟩ := List.append_of_mem hc
    have hnd := children_nodup (T := T) r v
    rw [hcs, List.nodup_middle, List.nodup_cons] at hnd
    have hc₁ : ∀ c' ∈ cs₁, c' ∈ children (T := T) r v ∧ c' ≠ c := fun c' h =>
      ⟨hcs ▸ List.mem_append_left _ h, fun e => hnd.1 (e ▸ List.mem_append_left _ h)⟩
    have hc₂ : ∀ c' ∈ cs₂, c' ∈ children (T := T) r v ∧ c' ≠ c := fun c' h =>
      ⟨hcs ▸ List.mem_append_right _ (List.mem_cons_of_mem _ h),
        fun e => hnd.1 (e ▸ List.mem_append_right _ h)⟩
    have hdc := (mem_children.1 hc).2
    have hdw := dist_le_of_btw hT.connected hcw
    -- the other children's traversals and `v` avoid the subtree of `w`
    have havoid : ∀ cs : List V, (∀ c' ∈ cs, c' ∈ children (T := T) r v ∧ c' ≠ c) →
        ∀ z ∈ cs.flatMap (fun c => tourAux (T := T) r n c ++ [v]), ¬ Btw T r w z := by
      intro cs hcs' z hz hwz
      simp only [List.mem_flatMap, List.mem_append, List.mem_singleton] at hz
      obtain ⟨c', hc', hz | rfl⟩ := hz
      · have h1 := (mem_tourAux hT (fuel_child hT hf (hcs' c' hc').1)).1 hz
        exact (hcs' c' hc').2
          (child_unique hT (hcs' c' hc').1 hc h1 (hwz.trans hT.connected hcw))
      · have := dist_le_of_btw hT.connected hwz
        omega
    have hv : ¬ Btw T r w v := by
      intro h; have := dist_le_of_btw hT.connected h; omega
    have htour : tourAux (T := T) r (n + 1) v =
        (v :: cs₁.flatMap fun c => tourAux (T := T) r n c ++ [v]) ++ tourAux (T := T) r n c ++
          (v :: cs₂.flatMap fun c => tourAux (T := T) r n c ++ [v]) := by
      rw [tourAux_succ, hcs]; simp
    by_cases hwc : w = c
    · subst hwc
      refine ⟨_, _, n, htour, fuel_child hT hf hc, ?_, ?_, fun _ => ⟨v, _, rfl, ?_, hdc⟩⟩
      · simp only [List.mem_cons]
        rintro z (rfl | hz)
        · exact hv
        · exact havoid cs₁ hc₁ z hz
      · simp only [List.mem_cons]
        rintro z (rfl | hz)
        · exact hv
        · exact havoid cs₂ hc₂ z hz
      · exact (mem_children.1 hc).1
    · obtain ⟨A, B, m, hAB, hfm, hA, hB, hpar⟩ := ih (fuel_child hT hf hc) hcw
      refine ⟨(v :: cs₁.flatMap fun c => tourAux (T := T) r n c ++ [v]) ++ A,
        B ++ (v :: cs₂.flatMap fun c => tourAux (T := T) r n c ++ [v]), m, ?_, hfm, ?_, ?_, ?_⟩
      · rw [htour, hAB]; simp
      · simp only [List.mem_append, List.mem_cons]
        rintro z ((rfl | hz) | hz)
        · exact hv
        · exact havoid cs₁ hc₁ z hz
        · exact hA z hz
      · simp only [List.mem_append, List.mem_cons]
        rintro z (hz | rfl | hz)
        · exact hB z hz
        · exact hv
        · exact havoid cs₂ hc₂ z hz
      · intro _
        obtain ⟨z, B', rfl, hz⟩ := hpar hwc
        exact ⟨z, _, rfl, hz⟩

end Tour

/-! #### Index bookkeeping for `A ++ M ++ B` -/

lemma getElem_append₃_cases {α : Type*} {L A M B : List α} (h : L = A ++ M ++ B) {k : ℕ}
    (hk : k < L.length) :
    (k < A.length ∧ L[k] ∈ A) ∨ (A.length ≤ k ∧ k < A.length + M.length ∧ L[k] ∈ M) ∨
      (A.length + M.length ≤ k ∧ L[k] ∈ B) := by
  subst h
  simp only [List.length_append] at hk
  by_cases h1 : k < A.length
  · left
    refine ⟨h1, ?_⟩
    rw [List.getElem_append_left (by simp; omega), List.getElem_append_left h1]
    exact List.getElem_mem _
  by_cases h2 : k < A.length + M.length
  · right; left
    refine ⟨by omega, h2, ?_⟩
    rw [List.getElem_append_left (by simp; omega), List.getElem_append_right (by omega)]
    exact List.getElem_mem _
  · right; right
    refine ⟨by omega, ?_⟩
    rw [List.getElem_append_right (by simp; omega)]
    exact List.getElem_mem _

lemma getElem_append₃_mid {α : Type*} {L A M B : List α} (h : L = A ++ M ++ B) {k : ℕ}
    (hk : k < M.length) :
    L[A.length + k]'(by subst h; simp; omega) = M[k] := by
  subst h
  rw [List.getElem_append_left (by simp; omega), List.getElem_append_right (by omega)]
  simp

lemma getElem_append₃_succ {α : Type*} {L A M B : List α} {z : α} (h : L = A ++ M ++ z :: B) :
    L[A.length + M.length]'(by subst h; simp) = z := by
  subst h
  rw [List.getElem_append_right (by simp)]
  simp

/-! #### Lemma 3 and Lemma 4 -/

include hT in
lemma listConstruction_decomp (r w : V) :
    ∃ A B m, listConstruction (T := T) r = A ++ tourAux (T := T) r m w ++ B ∧
      Fuel (T := T) r m w ∧ (∀ z ∈ A, ¬ Btw T r w z) ∧ (∀ z ∈ B, ¬ Btw T r w z) ∧
      (w ≠ r → ∃ z B', B = z :: B' ∧ T.Adj z w ∧ T.dist r w = T.dist r z + 1) :=
  tourAux_decomp hT (fuel_root hT r) (btw_left r w)

include hT in
/-- Subtrees occupy intervals of the list: an entry between two entries of the subtree of `z`
belongs to the subtree of `z`. -/
lemma btw_listConstruction_of_le {r z : V} {a i b : ℕ} (hai : a ≤ i) (hib : i ≤ b)
    (hb : b < (listConstruction (T := T) r).length)
    (ha' : Btw T r z ((listConstruction (T := T) r)[a]'(by omega)))
    (hb' : Btw T r z (listConstruction (T := T) r)[b]) :
    Btw T r z ((listConstruction (T := T) r)[i]'(by omega)) := by
  obtain ⟨A, B, m, hL, hf, hA, hB, -⟩ := listConstruction_decomp hT r z
  have ha1 : A.length ≤ a := by
    rcases getElem_append₃_cases hL (k := a) (by omega) with ⟨-, h⟩ | ⟨h1, -, -⟩ | ⟨h1, -⟩
    · exact absurd ha' (hA _ h)
    · exact h1
    · omega
  have hb2 : b < A.length + (tourAux (T := T) r m z).length := by
    rcases getElem_append₃_cases hL hb with ⟨h1, -⟩ | ⟨-, h1, -⟩ | ⟨-, h⟩
    · omega
    · exact h1
    · exact absurd hb' (hB _ h)
  rcases getElem_append₃_cases hL (k := i) (by omega) with ⟨h1, -⟩ | ⟨-, -, h⟩ | ⟨h1, -⟩
  · omega
  · exact (mem_tourAux hT hf).1 h
  · omega

include hT in
/-- Every occurrence of a vertex of the subtree of `w` lies between two occurrences of `w`. -/
lemma exists_occ_around {r w : V} {k : ℕ} (hk : k < (listConstruction (T := T) r).length)
    (h : Btw T r w (listConstruction (T := T) r)[k]) :
    (∃ a, ∃ ha : a < (listConstruction (T := T) r).length, a ≤ k ∧
        (listConstruction (T := T) r)[a] = w) ∧
      (∃ b, ∃ hb : b < (listConstruction (T := T) r).length, k ≤ b ∧
        (listConstruction (T := T) r)[b] = w) := by
  obtain ⟨A, B, m, hL, hf, hA, hB, -⟩ := listConstruction_decomp hT r w
  have hpos := tourAux_length_pos (T := T) (r := r) m w
  have hlen : (listConstruction (T := T) r).length =
      A.length + (tourAux (T := T) r m w).length + B.length := by
    rw [hL]; simp only [List.length_append]
  rcases getElem_append₃_cases hL hk with ⟨-, h'⟩ | ⟨h1, h2, -⟩ | ⟨-, h'⟩
  · exact absurd h (hA _ h')
  · refine ⟨⟨A.length + 0, by omega, by omega, ?_⟩,
      ⟨A.length + ((tourAux (T := T) r m w).length - 1), by omega, by omega, ?_⟩⟩
    · rw [getElem_append₃_mid hL hpos]; exact tourAux_getElem_zero m w
    · rw [getElem_append₃_mid hL (by omega)]; exact tourAux_getElem_last m w
  · exact absurd h (hB _ h')

include hT in
/-- If the entry `i` is in the subtree of `c` and a later entry `i'` is not, then the parent of
`c` occurs between them. -/
lemma exists_parent_between {r c : V} {i i' : ℕ} (hii' : i ≤ i')
    (hi' : i' < (listConstruction (T := T) r).length)
    (hc : Btw T r c ((listConstruction (T := T) r)[i]'(by omega)))
    (hc' : ¬ Btw T r c (listConstruction (T := T) r)[i']) :
    ∃ k, ∃ hk : k < (listConstruction (T := T) r).length, i ≤ k ∧ k ≤ i' ∧
      T.Adj (listConstruction (T := T) r)[k] c ∧
      T.dist r c = T.dist r (listConstruction (T := T) r)[k] + 1 := by
  have hcr : c ≠ r := by rintro rfl; exact hc' (btw_left c _)
  obtain ⟨A, B, m, hL, hf, hA, hB, hpar⟩ := listConstruction_decomp hT r c
  obtain ⟨z, B', rfl, hz⟩ := hpar hcr
  have hi2 : i < A.length + (tourAux (T := T) r m c).length := by
    rcases getElem_append₃_cases hL (k := i) (by omega) with ⟨h1, -⟩ | ⟨-, h1, -⟩ | ⟨-, h⟩
    · omega
    · exact h1
    · exact absurd hc (hB _ h)
  have hi'2 : A.length + (tourAux (T := T) r m c).length ≤ i' := by
    rcases getElem_append₃_cases hL hi' with ⟨h1, -⟩ | ⟨-, -, h⟩ | ⟨h1, -⟩
    · rcases getElem_append₃_cases hL (k := i) (by omega) with ⟨-, h⟩ | ⟨h2, -, -⟩ | ⟨h2, -⟩
      · exact absurd hc (hA _ h)
      · omega
      · omega
    · exact absurd ((mem_tourAux hT hf).1 h) hc'
    · exact h1
  refine ⟨A.length + (tourAux (T := T) r m c).length, ?_, by omega, hi'2, ?_⟩
  · rw [hL]; simp only [List.length_append, List.length_cons]; omega
  · rw [getElem_append₃_succ hL]; exact hz

omit [Fintype V] [LinearOrder V] in
lemma eq_of_btw_meet (hG : T.Connected) {r m c x y : V} (h1 : Btw T r m c) (h2 : Btw T r c x)
    (h3 : Btw T r c y) (h4 : Btw T x m y) : m = c := by
  unfold Btw at *
  have t1 := hG.dist_triangle (u := r) (v := m) (w := x)
  have t2 := hG.dist_triangle (u := r) (v := m) (w := y)
  have t3 := hG.dist_triangle (u := x) (v := c) (w := y)
  have s1 := SimpleGraph.dist_comm (G := T) (u := x) (v := m)
  have s2 := SimpleGraph.dist_comm (G := T) (u := x) (v := c)
  exact hG.dist_eq_zero_iff.1 (by omega)

include hT in
/-- The "lowest common ancestor" of `x` and `y`: a vertex on the paths `r – x`, `r – y` and
`x – y` (the vertex of the path `x – y` closest to the root). -/
lemma exists_meet (r x y : V) : ∃ m, Btw T r m x ∧ Btw T r m y ∧ Btw T x m y := by
  classical
  obtain ⟨m, hm, hmin⟩ := (Finset.univ.filter fun w => Btw T x w y).exists_min_image
    (fun w => T.dist r w) ⟨x, by simp [btw_left]⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hm hmin
  have hconv := convex_btw hT x y
  exact ⟨m, btw_of_isMin hT hconv hm hmin (btw_left x y),
    btw_of_isMin hT hconv hm hmin (btw_right x y), hm⟩

include hT in
lemma exists_median_between_of_le (r : V) {i i' : ℕ} (hii' : i ≤ i')
    (hi' : i' < (listConstruction (T := T) r).length) :
    ∃ k, ∃ hk : k < (listConstruction (T := T) r).length, i ≤ k ∧ k ≤ i' ∧
      Btw T r (listConstruction (T := T) r)[k] ((listConstruction (T := T) r)[i]'(by omega)) ∧
      Btw T r (listConstruction (T := T) r)[k] (listConstruction (T := T) r)[i'] ∧
      Btw T ((listConstruction (T := T) r)[i]'(by omega)) (listConstruction (T := T) r)[k]
        (listConstruction (T := T) r)[i'] := by
  have hi : i < (listConstruction (T := T) r).length := by omega
  obtain ⟨m, hmx, hmy, hxmy⟩ :=
    exists_meet hT r (listConstruction (T := T) r)[i] (listConstruction (T := T) r)[i']
  by_cases hxm : (listConstruction (T := T) r)[i] = m
  · exact ⟨i, hi, le_rfl, hii', btw_right r _, hxm ▸ hmy, btw_left _ _⟩
  obtain ⟨c, hc, hcx⟩ := exists_child hT hmx hxm
  have hcy : ¬ Btw T r c (listConstruction (T := T) r)[i'] := by
    intro hcy
    have e := eq_of_btw_meet hT.connected (btw_of_mem_children hc) hcx hcy hxmy
    have h2 := (mem_children.1 hc).2
    rw [e] at h2; omega
  obtain ⟨k, hk, hik, hki', hadj, hd⟩ := exists_parent_between hT hii' hi' hcx hcy
  have hkm : (listConstruction (T := T) r)[k] = m := by
    refine eq_of_btw_of_dist_eq_dist hT (u := c) ?_ (btw_of_mem_children hc) ?_
    · unfold Btw; rw [dist_eq_one_iff_adj.2 hadj, hd]
    · have := (mem_children.1 hc).2; omega
  exact ⟨k, hk, hik, hki', hkm ▸ hmx, hkm ▸ hmy, hkm ▸ hxmy⟩

-- The hypothesis `1 < |V(T)|` of the paper is not needed (for `|V(T)| = 1` the claim is vacuous).
set_option linter.unusedVariables false in
/-- **Lemma 3.1**: consecutive entries of the list are adjacent (if `|V(T)| > 1`). -/
theorem listConstruction_adj (r : V) (h1 : 1 < Fintype.card V) {i : ℕ}
    (hi : i + 1 < (listConstruction (T := T) r).length) :
    T.Adj (listConstruction (T := T) r)[i] (listConstruction (T := T) r)[i + 1] :=
  (List.isChain_iff_getElem.1 (isChain_tourAux (T := T) (r := r) _ r) i hi).1

lemma listConstruction_isChain (r : V) : (listConstruction (T := T) r).IsChain T.Adj :=
  (isChain_tourAux (T := T) (r := r) _ r).imp fun _ _ h => h.1

include hT in
/-- **Lemma 3.2** (length): the list has at most `2|V(T)|` entries. -/
theorem length_listConstruction_le (r : V) :
    (listConstruction (T := T) r).length ≤ 2 * Fintype.card V := by
  have h1 := length_tourAux hT (fuel_root hT r)
  have h2 := Finset.card_le_univ (subtree (T := T) r r)
  unfold listConstruction
  omega

include hT in
/-- **Lemma 3.2** (coverage): every vertex occurs in the list. -/
theorem mem_listConstruction (r v : V) : v ∈ listConstruction (T := T) r :=
  (mem_tourAux hT (fuel_root hT r)).2 (btw_left r v)

include hT in
/-- **Lemma 3.3**: `u` is in the subtree rooted at `v` (i.e. `v` is on the path from the root
to `u`) iff every occurrence of `u` lies between two occurrences of `v` (equivalently, between
the first and the last occurrence of `v`). -/
theorem subtree_iff_indices (r u v : V) :
    Btw T r v u ↔ ∀ k, ∀ hk : k < (listConstruction (T := T) r).length,
      (listConstruction (T := T) r)[k] = u →
      (∃ a, ∃ ha : a < (listConstruction (T := T) r).length, a ≤ k ∧
        (listConstruction (T := T) r)[a] = v) ∧
      (∃ b, ∃ hb : b < (listConstruction (T := T) r).length, k ≤ b ∧
        (listConstruction (T := T) r)[b] = v) := by
  constructor
  · intro h k hk hku
    exact exists_occ_around hT hk (by rw [hku]; exact h)
  · intro h
    obtain ⟨k, hk, hku⟩ := List.getElem_of_mem (mem_listConstruction hT r u)
    obtain ⟨⟨a, ha, hak, hav⟩, ⟨b, hb, hkb, hbv⟩⟩ := h k hk hku
    have := btw_listConstruction_of_le hT hak hkb hb (by rw [hav]; exact btw_right r v)
      (by rw [hbv]; exact btw_right r v)
    rwa [hku] at this

include hT in
/-- **Lemma 3.4**: between any occurrence of `v` and any occurrence of `v'` there is an
occurrence of their lowest common ancestor (the vertex on the paths `r–v`, `r–v'` and `v–v'`). -/
theorem exists_median_between (r : V) {i i' : ℕ}
    (hi : i < (listConstruction (T := T) r).length)
    (hi' : i' < (listConstruction (T := T) r).length) :
    ∃ k, ∃ hk : k < (listConstruction (T := T) r).length, min i i' ≤ k ∧ k ≤ max i i' ∧
      Btw T r (listConstruction (T := T) r)[k] (listConstruction (T := T) r)[i] ∧
      Btw T r (listConstruction (T := T) r)[k] (listConstruction (T := T) r)[i'] ∧
      Btw T (listConstruction (T := T) r)[i] (listConstruction (T := T) r)[k]
        (listConstruction (T := T) r)[i'] := by
  rcases le_total i i' with h | h
  · obtain ⟨k, hk, h1, h2, h3, h4, h5⟩ := exists_median_between_of_le hT r h hi'
    exact ⟨k, hk, by omega, by omega, h3, h4, h5⟩
  · obtain ⟨k, hk, h1, h2, h3, h4, h5⟩ := exists_median_between_of_le hT r h hi
    exact ⟨k, hk, by omega, by omega, h4, h3, h5.symm⟩

/-- **Lemma 4**: if `i` lies between two indices of vertices of `S`, the root path of the `i`-th
entry meets the hull of `S`. -/
theorem rpath_listConstruction_meets_hull [DecidableEq V] (r : V) {S : Set V} {a b i : ℕ}
    (hb : b < (listConstruction (T := T) r).length) (hai : a ≤ i) (hib : i ≤ b)
    (ha : (listConstruction (T := T) r)[a]'(by omega) ∈ S)
    (hb' : (listConstruction (T := T) r)[b] ∈ S) :
    ∃ w ∈ rpath hT r ((listConstruction (T := T) r)[i]'(by omega)), w ∈ hull T S := by
  obtain ⟨k, hk, -, -, h1, h2, h3⟩ := exists_median_between_of_le hT r (le_trans hai hib) hb
  exact ⟨_, (mem_rpath hT).2 (btw_listConstruction_of_le hT hai hib hb h1 h2),
    _, ha, _, hb', h3⟩

/-! ### The protocol `TreeAA₀` -/

section Protocol

variable {P : Type} [Fintype P] [DecidableEq P] {V : Type} [Fintype V] [LinearOrder V]
  {T : SimpleGraph V} (hT : T.IsTree) (r : V) {M₁ S₁ M₂ S₂ : Type}

/-- **`PathsFinder₀`**: join `RealAA(1)` with the first index of the own input in the list `L`;
output the path from the root to `L_[j]`. -/
noncomputable def pathsFinder0 (realAA₁ : Protocol P ℝ M₁ ℝ) : Protocol P V M₁ (List V) :=
  realAA₁.wrap (fun _ v => ((listConstruction (T := T) r).idxOf v : ℝ))
    (fun _ v j => rpath hT r ((listConstruction (T := T) r).getD (rnd j).toNat v))

/-- Line 6 of `TreeAA₀`: output `v_[j]` on the own path `(v_0, …, v_{k-1})`, or its last vertex if
`[j]` is beyond it. -/
noncomputable def treeAA0Out (Pth : List V) (v : V) (j : ℝ) : V :=
  if Pth.length ≤ (rnd j).toNat then Pth.getLast?.getD v else Pth.getD (rnd j).toNat v

/-- Lines 5–6 of `TreeAA₀`: join `RealAA(1)` with the index of `proj_P(v_in)` on the own path. -/
noncomputable def fromPath0 (realAA₂ : Protocol P ℝ M₂ ℝ) : Protocol P (V × List V) M₂ V :=
  realAA₂.wrap (fun _ i => (projIdx T i.2 i.1 : ℝ)) (fun _ i j => treeAA0Out i.2 i.1 j)

/-- **`TreeAA₀`** (Section 4.3.2): `PathsFinder₀` for `R₁` rounds, then lines 5–6. -/
noncomputable def treeAA0 (R₁ : ℕ) (realAA₁ : Protocol P ℝ M₁ ℝ) (realAA₂ : Protocol P ℝ M₂ ℝ) :
    Protocol P V (M₁ ⊕ M₂) V :=
  (pathsFinder0 hT r realAA₁).seq R₁ (fun _ x o => (x, o.getD [x])) (fromPath0 (T := T) realAA₂)

omit [Fintype P] [DecidableEq P] in
/-- The rounded RealAA outputs of honest parties are pairwise 1-close and lie in the range of
the honest (natural-number) RealAA inputs. -/
lemma rnd_toNat_spec {H : Set P} (i : P → ℕ) (j : P → ℝ)
    (hval : ∀ p ∈ H, ∃ a ∈ H, ∃ b ∈ H, (i a : ℝ) ≤ j p ∧ j p ≤ i b)
    (hagr : ∀ p ∈ H, ∀ q ∈ H, |j p - j q| ≤ 1) :
    (∀ p ∈ H, ∃ a ∈ H, ∃ b ∈ H, i a ≤ (rnd (j p)).toNat ∧ (rnd (j p)).toNat ≤ i b) ∧
      (∀ p ∈ H, ∀ q ∈ H, (rnd (j p)).toNat ≤ (rnd (j q)).toNat + 1) := by
  have hpos : ∀ p ∈ H, 0 ≤ rnd (j p) := by
    intro p hp
    obtain ⟨a, ha, b, hb, h1, h2⟩ := hval p hp
    have := (rnd_mem_Icc h1 h2).1; omega
  refine ⟨fun p hp => ?_, fun p hp q hq => ?_⟩
  · obtain ⟨a, ha, b, hb, h1, h2⟩ := hval p hp
    obtain ⟨h1', h2'⟩ := rnd_mem_Icc h1 h2
    exact ⟨a, ha, b, hb, by omega, by omega⟩
  · have hc := rnd_close (hagr p hp q hq)
    rw [abs_le] at hc
    have := hpos p hp; have := hpos q hq
    omega

omit [Fintype P] [DecidableEq P] in
/-- **Lemma 5** (`PathsFinder₀`, spec level). Let the honest parties `H` join RealAA with the
first indices `min L(x p)` of their inputs in `L = ListConstruction(T, r)`, and let the honest
RealAA outputs `j` lie in the range of the honest RealAA inputs and be pairwise 1-close. Then
there are vertices `v, v'` with `v = v'` or `v` the parent of `v'` such that every honest output
path `P(r, L_[j])` is `P(r, v)` or `P(r, v')` (property 2), and each of them meets the hull of
the honest inputs (property 1). -/
theorem pathsFinder0_spec {H : Set P} (x : P → V) (j : P → ℝ)
    (hval : ∀ p ∈ H, ∃ a ∈ H, ∃ b ∈ H, ((listConstruction (T := T) r).idxOf (x a) : ℝ) ≤ j p ∧
      j p ≤ (listConstruction (T := T) r).idxOf (x b))
    (hagr : ∀ p ∈ H, ∀ q ∈ H, |j p - j q| ≤ 1) :
    ∃ v v', (v = v' ∨ T.Adj v v' ∧ Btw T r v v') ∧ ∀ p ∈ H,
      (rpath hT r ((listConstruction (T := T) r).getD (rnd (j p)).toNat (x p)) = rpath hT r v ∨
        rpath hT r ((listConstruction (T := T) r).getD (rnd (j p)).toNat (x p)) =
          rpath hT r v') ∧
      ∃ w ∈ rpath hT r ((listConstruction (T := T) r).getD (rnd (j p)).toNat (x p)),
        w ∈ hull T (x '' H) := by
  set L := listConstruction (T := T) r with hL
  have hidx : ∀ p, L.idxOf (x p) < L.length := fun p =>
    List.idxOf_lt_length_of_mem (mem_listConstruction hT r (x p))
  have hidxget : ∀ p, L[L.idxOf (x p)]'(hidx p) = x p := fun p => List.getElem_idxOf (hidx p)
  obtain ⟨hk, hclose⟩ := rnd_toNat_spec (fun p => L.idxOf (x p)) j hval hagr
  have hkL : ∀ p ∈ H, (rnd (j p)).toNat < L.length := by
    intro p hp
    obtain ⟨a, ha, b, hb, -, h2⟩ := hk p hp
    exact lt_of_le_of_lt h2 (hidx b)
  have hget : ∀ p (hp : p ∈ H),
      L.getD (rnd (j p)).toNat (x p) = L[(rnd (j p)).toNat]'(hkL p hp) := fun p hp =>
    List.getD_eq_getElem _ _ _
  have hmeet : ∀ p ∈ H, ∃ w ∈ rpath hT r (L.getD (rnd (j p)).toNat (x p)), w ∈ hull T (x '' H) := by
    intro p hp
    obtain ⟨a, ha, b, hb, h1, h2⟩ := hk p hp
    rw [hget p hp]
    exact rpath_listConstruction_meets_hull hT r (hidx b) h1 h2
      (by rw [hidxget]; exact ⟨a, ha, rfl⟩) (by rw [hidxget]; exact ⟨b, hb, rfl⟩)
  rcases H.eq_empty_or_nonempty with rfl | ⟨p₀, hp₀⟩
  · exact ⟨r, r, Or.inl rfl, by simp⟩
  -- all honest rounded outputs are `m` or `m + 1`
  obtain ⟨m, hm, hmL⟩ : ∃ m, (∀ p ∈ H, (rnd (j p)).toNat = m ∨ (rnd (j p)).toNat = m + 1) ∧
      m < L.length := by
    by_cases hex : ∃ q ∈ H, (rnd (j q)).toNat + 1 = (rnd (j p₀)).toNat
    · obtain ⟨q, hq, hq'⟩ := hex
      refine ⟨(rnd (j q)).toNat, fun p hp => ?_, hkL q hq⟩
      have := hclose p hp q hq; have := hclose q hq p hp
      have := hclose p hp p₀ hp₀; have := hclose p₀ hp₀ p hp
      omega
    · push Not at hex
      refine ⟨(rnd (j p₀)).toNat, fun p hp => ?_, hkL p₀ hp₀⟩
      have := hclose p hp p₀ hp₀; have := hclose p₀ hp₀ p hp; have := hex p hp
      omega
  have hcongr : ∀ k (hk : k < L.length) k', k = k' → ∀ hk' : k' < L.length, L[k] = L[k'] := by
    rintro k hk k' rfl hk'; rfl
  by_cases hm1 : m + 1 < L.length
  · have hstep : TourStep (T := T) r L[m] L[m + 1] :=
      List.isChain_iff_getElem.1 (isChain_tourAux (T := T) (r := r) _ r) m hm1
    have hcase : ∀ p (hp : p ∈ H), L.getD (rnd (j p)).toNat (x p) = L[m] ∨
        L.getD (rnd (j p)).toNat (x p) = L[m + 1] := by
      intro p hp
      rw [hget p hp]
      rcases hm p hp with e | e
      · exact Or.inl (hcongr _ _ _ e hmL)
      · exact Or.inr (hcongr _ _ _ e hm1)
    obtain ⟨hadj, hd | hd⟩ := hstep
    · refine ⟨L[m], L[m + 1], Or.inr ⟨hadj, ?_⟩, fun p hp => ⟨?_, hmeet p hp⟩⟩
      · unfold Btw; rw [dist_eq_one_iff_adj.2 hadj, hd]
      · rcases hcase p hp with e | e <;> rw [e] <;> simp
    · refine ⟨L[m + 1], L[m], Or.inr ⟨hadj.symm, ?_⟩, fun p hp => ⟨?_, hmeet p hp⟩⟩
      · unfold Btw; rw [dist_eq_one_iff_adj.2 hadj.symm, hd]
      · rcases hcase p hp with e | e <;> rw [e] <;> simp
  · refine ⟨L[m], L[m], Or.inl rfl, fun p hp => ⟨Or.inl ?_, hmeet p hp⟩⟩
    rw [hget p hp]
    have := hkL p hp
    rcases hm p hp with e | e
    · rw [hcongr _ _ _ e hmL]
    · omega

omit [Fintype P] [DecidableEq P] [Fintype V] in
/-- **Theorem 3**, correctness argument (spec level; Section 4.3.2). Assume the honest paths are
`P(r, v)` or `P(r, v')` with `v = v'` or `v` the parent of `v'`, each meeting the hull of the
honest inputs (Lemma 5), and the honest RealAA outputs `j` lie in the range of the honest
projection indices and are pairwise 1-close. Then the outputs of line 6 of `TreeAA₀` are in the
hull of the honest inputs and pairwise at distance at most one. -/
theorem treeAA0_spec {H : Set P} (x : P → V) (Pp : P → List V) (j : P → ℝ) (v v' : V)
    (hvv' : v = v' ∨ T.Adj v v' ∧ Btw T r v v')
    (hP : ∀ p ∈ H, (Pp p = rpath hT r v ∨ Pp p = rpath hT r v') ∧
      ∃ w ∈ Pp p, w ∈ hull T (x '' H))
    (hval : ∀ p ∈ H, ∃ a ∈ H, ∃ b ∈ H,
      (projIdx T (Pp a) (x a) : ℝ) ≤ j p ∧ j p ≤ projIdx T (Pp b) (x b))
    (hagr : ∀ p ∈ H, ∀ q ∈ H, |j p - j q| ≤ 1) :
    (∀ p ∈ H, treeAA0Out (Pp p) (x p) (j p) ∈ hull T (x '' H)) ∧
    (∀ p ∈ H, ∀ q ∈ H,
      T.dist (treeAA0Out (Pp p) (x p) (j p)) (treeAA0Out (Pp q) (x q) (j q)) ≤ 1) := by
  -- the longer path `K = P(r, v')`
  set K := rpath hT r v' with hK
  have hrp : ∀ p ∈ H, ∃ u, Pp p = rpath hT r u := fun p hp => by
    rcases (hP p hp).1 with e | e
    · exact ⟨v, e⟩
    · exact ⟨v', e⟩
  have hpre : ∀ p ∈ H, Pp p <+: K := by
    intro p hp
    rcases (hP p hp).1 with e | e
    · rw [e]
      rcases hvv' with rfl | ⟨-, hb⟩
      · exact List.prefix_refl _
      · exact rpath_prefix hT ((mem_rpath hT).2 hb)
    · rw [e]
  have hlen : ∀ p ∈ H, K.length ≤ (Pp p).length + 1 := by
    intro p hp
    rcases (hP p hp).1 with e | e <;> rw [e]
    · rcases hvv' with rfl | ⟨hadj, hb⟩
      · rw [hK]; omega
      · rw [hK, length_rpath, length_rpath]
        unfold Btw at hb
        rw [dist_eq_one_iff_adj.2 hadj] at hb
        omega
    · omega
  have hne : ∀ p ∈ H, Pp p ≠ [] := fun p hp => by
    obtain ⟨u, hu⟩ := hrp p hp; rw [hu]; exact rpath_ne_nil hT r u
  -- projection indices and their vertices (Lemma 2)
  have hidx : ∀ q ∈ H, projIdx T (Pp q) (x q) < (Pp q).length := fun q hq =>
    projIdx_lt (hne q hq) (x q)
  have hidxK : ∀ q ∈ H, projIdx T (Pp q) (x q) < K.length := fun q hq =>
    lt_of_lt_of_le (hidx q hq) (hpre q hq).length_le
  have hproj : ∀ q (hq : q ∈ H), K[projIdx T (Pp q) (x q)]'(hidxK q hq) ∈ hull T (x '' H) := by
    intro q hq
    obtain ⟨u, hu⟩ := hrp q hq
    have := proj_mem_hull hT (S := x '' H) ⟨q, hq, rfl⟩ (r := r) (u := u) (hu ▸ (hP q hq).2)
    rw [← hu, List.getD_eq_getElem _ _ (hidx q hq)] at this
    rwa [← (hpre q hq).getElem (hidx q hq)]
  -- the rounded outputs
  obtain ⟨hk, hclose⟩ := rnd_toNat_spec (fun p => projIdx T (Pp p) (x p)) j hval hagr
  have hkK : ∀ p ∈ H, (rnd (j p)).toNat < K.length := by
    intro p hp
    obtain ⟨a, ha, b, hb, -, h2⟩ := hk p hp
    exact lt_of_le_of_lt h2 (hidxK b hb)
  -- the output of `p` is the entry `min [j] (k - 1)` of `K` (`k` = length of `p`'s path)
  have heK : ∀ p ∈ H, min (rnd (j p)).toNat ((Pp p).length - 1) < K.length := fun p hp => by
    have := hkK p hp; omega
  have hout : ∀ p (hp : p ∈ H), treeAA0Out (Pp p) (x p) (j p) =
      K[min (rnd (j p)).toNat ((Pp p).length - 1)]'(heK p hp) := by
    intro p hp
    have hl := List.length_pos_iff.2 (hne p hp)
    have hcongr : ∀ k (hk : k < K.length) k', k = k' → ∀ hk' : k' < K.length, K[k] = K[k'] := by
      rintro k hk k' rfl hk'; rfl
    unfold treeAA0Out
    split_ifs with h
    · rw [List.getLast?_eq_some_getLast (hne p hp), Option.getD_some, List.getLast_eq_getElem,
        (hpre p hp).getElem]
      exact hcongr _ _ _ (by omega) _
    · rw [List.getD_eq_getElem _ _ (by omega), (hpre p hp).getElem]
      exact hcongr _ _ _ (by omega) _
  refine ⟨fun p hp => ?_, fun p hp q hq => ?_⟩
  · -- validity: the effective index lies between two honest projection indices
    rw [hout p hp]
    obtain ⟨a, ha, b, hb, h1, h2⟩ := hk p hp
    have hlo : ∃ c ∈ H, projIdx T (Pp c) (x c) ≤ min (rnd (j p)).toNat ((Pp p).length - 1) := by
      by_cases h : (rnd (j p)).toNat < (Pp p).length
      · exact ⟨a, ha, by omega⟩
      · exact ⟨p, hp, by have := hidx p hp; omega⟩
    obtain ⟨c, hc, hc'⟩ := hlo
    have hbtw := btw_rpath_getElem hT r v' hc' (le_trans (min_le_left _ _) h2) (hidxK b hb)
    exact hull_convex hT (hproj c hc) (hproj b hb) hbtw
  · -- 1-agreement
    rw [hout p hp, hout q hq]
    have h1 := hclose p hp q hq
    have h2 := hclose q hq p hp
    have h3 := hkK p hp
    have h4 := hkK q hq
    have h5 := hlen p hp
    have h6 := hlen q hq
    exact dist_getElem_le' hT.connected (rpath_isChain hT r v') _ _ (by omega) (by omega)

set_option linter.unusedSectionVars false in
/-- **Theorem 3.** Given RealAA protocols achieving AA on `ℝ` with `ε = 1` within `R₁` rounds for
`2|V(T)|`-close inputs and within `R₂` rounds for `D(T)`-close inputs (against an adversary
structure `Z`), `TreeAA₀` achieves AA on the tree `T` within `R₁ + R₂` rounds. -/
theorem treeAA0_solves {Z : AdvStructure P} {R₁ R₂ : ℕ} (A₁ : Auth P M₁ S₁)
    (realAA₁ : Protocol P ℝ M₁ ℝ) (hU₁ : realAA₁.Unforging A₁)
    (h₁ : SolvesAuthWithin ⊤ realAA₁ A₁ Z (Close (2 * Fintype.card V : ℝ)) (RealAA 1) R₁)
    (A₂ : Auth P M₂ S₂) (realAA₂ : Protocol P ℝ M₂ ℝ) (hU₂ : realAA₂.Unforging A₂)
    (h₂ : SolvesAuthWithin ⊤ realAA₂ A₂ Z (Close (T.diam : ℝ)) (RealAA 1) R₂) :
    (treeAA0 hT r R₁ realAA₁ realAA₂).Unforging (Auth.seq A₁ A₂) ∧
      SolvesAuthWithin ⊤ (treeAA0 hT r R₁ realAA₁ realAA₂) (Auth.seq A₁ A₂) Z noPre (GraphAA T)
        (R₁ + R₂) := by
  classical
  refine ⟨Protocol.Unforging.seq (Protocol.Unforging.wrap _ _ _ hU₁)
    (Protocol.Unforging.wrap _ _ _ hU₂), ?_⟩
  intro s hZ hrel hV _
  set L := listConstruction (T := T) r with hL
  set f : P → V → Option (List V) → V × List V := fun _ x o => (x, o.getD [x]) with hf
  -- phase 1: `PathsFinder₀` = RealAA₁ on the first indices in `L`
  have hV1 := Scenario.AuthValid.seqFst ⊤ (pathsFinder0 hT r realAA₁) R₁ f
    (fromPath0 (T := T) realAA₂) hV
  set s₁ := (s.seqFst R₁).wrapIn (fun _ v => (L.idxOf v : ℝ)) with hs₁
  have hV1' : s₁.AuthValid ⊤ realAA₁ A₁ := (Scenario.authValid_wrap _ _ _ _ _ _).1 hV1
  have hpre₁ : Close (2 * Fintype.card V : ℝ) s₁.input s₁.honest := by
    have hb : ∀ p, (L.idxOf (s.input p) : ℝ) ≤ 2 * Fintype.card V := by
      intro p
      have h1 : L.idxOf (s.input p) < L.length :=
        List.idxOf_lt_length_of_mem (mem_listConstruction hT r (s.input p))
      have h2 : L.length ≤ 2 * Fintype.card V := length_listConstruction_le hT r
      exact_mod_cast (by omega : L.idxOf (s.input p) ≤ 2 * Fintype.card V)
    intro p _ q _
    simp only [s₁, Scenario.wrapIn_input, Scenario.seqFst_input]
    have := hb p; have := hb q
    have : (0 : ℝ) ≤ L.idxOf (s.input p) := Nat.cast_nonneg _
    have : (0 : ℝ) ≤ L.idxOf (s.input q) := Nat.cast_nonneg _
    rw [abs_le]; constructor <;> linarith
  obtain ⟨⟨hrT₁, hrV₁, hrA₁⟩, hrTerm₁⟩ := h₁ s₁ hZ ((hrel.seqFst R₁).wrapIn _) hV1' hpre₁
  have hex₁ : ∀ p, ∃ j : ℝ, p ∈ s.honest → Decides ⊤ realAA₁ s₁ p j := by
    intro p
    by_cases hp : p ∈ s.honest
    · obtain ⟨j, hj⟩ := hrT₁ p hp; exact ⟨j, fun _ => hj⟩
    · exact ⟨0, fun h => absurd h hp⟩
  choose j₁ hj₁ using hex₁
  -- the paths obtained by `PathsFinder₀`
  set Pth : P → List V := fun p => rpath hT r (L.getD (rnd (j₁ p)).toNat (s.input p)) with hPth
  have hdec₁ : ∀ p ∈ s.honest, Decides ⊤ (pathsFinder0 hT r realAA₁) (s.seqFst R₁) p (Pth p) :=
    fun p hp => (decides_wrap_iff _ _ _ _ _ _ _).2 ⟨j₁ p, hj₁ p hp, rfl⟩
  have hterm₁ : TerminatesBy ⊤ (pathsFinder0 hT r realAA₁) (s.seqFst R₁) R₁ :=
    terminatesBy_wrap _ _ _ _ _ _ hrTerm₁
  set x₂ := seqInputs ⊤ (pathsFinder0 hT r realAA₁) R₁ f s with hx₂def
  have hx₂ : ∀ p ∈ s.honest, x₂ p = (s.input p, Pth p) := fun p hp =>
    seqInputs_eq ⊤ _ R₁ f s p (Pth p) (hdec₁ p hp) (hterm₁ p hp)
  -- Lemma 5
  have hval₁ : ∀ p ∈ s.honest, ∃ a ∈ s.honest, ∃ b ∈ s.honest,
      (L.idxOf (s.input a) : ℝ) ≤ j₁ p ∧ j₁ p ≤ L.idxOf (s.input b) := by
    intro p hp
    obtain ⟨a, ha, b, hb, h1, h2⟩ := hrV₁ p hp (j₁ p) (hj₁ p hp)
    exact ⟨a, ha, b, hb, h1, h2⟩
  have hagr₁ : ∀ p ∈ s.honest, ∀ q ∈ s.honest, |j₁ p - j₁ q| ≤ 1 := fun p hp q hq =>
    hrA₁ p hp q hq _ _ (hj₁ p hp) (hj₁ q hq)
  obtain ⟨v, v', hvv', hPF⟩ := pathsFinder0_spec hT r s.input j₁ hval₁ hagr₁
  -- phase 2: lines 5–6 (RealAA₂ on the projection indices)
  set s₂ := (s.seqSnd R₁ x₂).wrapIn (fun _ (i : V × List V) => (projIdx T i.2 i.1 : ℝ)) with hs₂
  have hV2 : s₂.AuthValid ⊤ realAA₂ A₂ :=
    (Scenario.authValid_wrap _ _ _ _ _ _).1
      (Scenario.AuthValid.seqSnd ⊤ (pathsFinder0 hT r realAA₁) R₁ f
        (fromPath0 (T := T) realAA₂) hV)
  have hin₂ : ∀ p ∈ s.honest, s₂.input p = (projIdx T (Pth p) (s.input p) : ℝ) := by
    intro p hp
    simp only [s₂, Scenario.wrapIn_input, Scenario.seqSnd_input]
    rw [hx₂ p hp]
  have hpre₂ : Close (T.diam : ℝ) s₂.input s₂.honest := by
    have := close_projIdx hT r (H := s.honest) s.input Pth
      (fun p _ => ⟨rpath_ne_nil hT r _, _, rfl⟩)
    intro p hp q hq
    rw [hin₂ p hp, hin₂ q hq]
    exact this p hp q hq
  obtain ⟨⟨hrT₂, hrV₂, hrA₂⟩, hrTerm₂⟩ :=
    h₂ s₂ hZ ((hrel.seqSnd R₁ x₂).wrapIn _) hV2 hpre₂
  have hex₂ : ∀ p, ∃ j : ℝ, p ∈ s.honest → Decides ⊤ realAA₂ s₂ p j := by
    intro p
    by_cases hp : p ∈ s.honest
    · obtain ⟨j, hj⟩ := hrT₂ p hp; exact ⟨j, fun _ => hj⟩
    · exact ⟨0, fun h => absurd h hp⟩
  choose j₂ hj₂ using hex₂
  -- decisions of `TreeAA₀`
  have hdecT : ∀ p ∈ s.honest, ∀ o, Decides ⊤ (treeAA0 hT r R₁ realAA₁ realAA₂) s p o ↔
      o = treeAA0Out (Pth p) (s.input p) (j₂ p) := by
    intro p hp o
    rw [treeAA0, decides_seq_iff, fromPath0, decides_wrap_iff]
    simp only [Scenario.seqSnd_input]
    rw [← hx₂def, hx₂ p hp]
    constructor
    · rintro ⟨j', hj', rfl⟩
      rw [Decides.unique _ _ hj' (hj₂ p hp)]
    · rintro rfl
      exact ⟨j₂ p, hj₂ p hp, rfl⟩
  -- Theorem 3, spec level
  have hval₂ : ∀ p ∈ s.honest, ∃ a ∈ s.honest, ∃ b ∈ s.honest,
      (projIdx T (Pth a) (s.input a) : ℝ) ≤ j₂ p ∧ j₂ p ≤ projIdx T (Pth b) (s.input b) := by
    intro p hp
    obtain ⟨a, ha, b, hb, h1, h2⟩ := hrV₂ p hp (j₂ p) (hj₂ p hp)
    exact ⟨a, ha, b, hb, by rw [← hin₂ a ha]; exact h1, by rw [← hin₂ b hb]; exact h2⟩
  have hagr₂ : ∀ p ∈ s.honest, ∀ q ∈ s.honest, |j₂ p - j₂ q| ≤ 1 := fun p hp q hq =>
    hrA₂ p hp q hq _ _ (hj₂ p hp) (hj₂ q hq)
  obtain ⟨hvalid, hagree⟩ := treeAA0_spec hT r s.input Pth j₂ v v' hvv' hPF hval₂ hagr₂
  refine ⟨⟨fun p hp => ⟨_, (hdecT p hp _).2 rfl⟩, fun p hp o ho => ?_,
    fun p hp q hq o o' ho ho' => ?_⟩, ?_⟩
  · rw [(hdecT p hp o).1 ho]; exact hvalid p hp
  · rw [(hdecT p hp o).1 ho, (hdecT q hq o').1 ho']; exact hagree p hp q hq
  · exact terminatesBy_seq _ _ _ _ _ s R₂ (terminatesBy_wrap _ _ _ _ _ _ hrTerm₂)

end Protocol

end TreeAA
