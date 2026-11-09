import Papers.PODC2017.FenceInsertionChain.MultiCut

/-!
# Algorithm 1: the greedy chain multi-cut

Vertices of the chain are `v_0, …, v_{n-1}`; the edge `{v_k, v_{k+1}}` is represented by its index
`k`. Algorithm 1 of the paper:

```
T'  ← {(v_i, v_j) | (v_i, v_j) ∈ T ∧ i < j  ∨  (v_j, v_i) ∈ T ∧ j < i}     -- `orient`
T'' ← sort T' by j                                                         -- `sortByRight`
E'  ← ∅
for (v_i, v_j) ∈ T'' do
  if ∄ {v_i', v_j'} ∈ E' : i ≤ i' ∧ j' ≤ j then E' ← E' ∪ {{v_{j-1}, v_j}}  -- `step`
return E'
```

* `chainMultiCut T` — Algorithm 1, literally (the test of line 11 scans `E'`).
* `chainMultiCutFast T` — the same loop with an `O(1)` test against the last cut;
  `chainMultiCut_eq_fast`: both compute the same set. So the loop costs `O(|T|)` after sorting.

## Optimality, following the paper's proof

* `card_le_of_pairwiseDisjoint` — *first fact*: a cut of pairwise edge-disjoint terminal paths
  has at least as many edges as there are paths.
* `foldl_step_inv` — *second fact* (and feasibility): the pairs that trigger the addition of an edge
  have pairwise disjoint paths, there are `|E'|` of them, and `E'` cuts every processed pair.
* `chainMultiCut_cuts`, `chainMultiCut_card_le` — the output cuts every terminal pair `(s, t)`,
  `s ≠ t`, and is no larger than any other such cut.
* `algorithm_1_optimal` — **main theorem**: for terminal pairs without loops `(v, v)`, the edges
  `{v_k, v_{k+1}}`, `k ∈ chainMultiCut T`, form a minimum multi-cut of the chain.
* `fenceIns_greedy_optimal` — combined with Lemma 2.4: the greedy gives a minimum fence insertion.
-/

namespace Podc.FenceInsertionChain

open Finset SimpleGraph

/-- Lines 5–6: orient every terminal pair so that the smaller vertex comes first; pairs `(v, v)`
satisfy neither `i < j` nor `j < i` and are dropped. -/
def orient (T : List (ℕ × ℕ)) : List (ℕ × ℕ) :=
  T.filterMap fun p => if p.1 < p.2 then some p else if p.2 < p.1 then some (p.2, p.1) else none

/-- Line 7: sort the pairs by their right end. -/
def sortByRight (T : List (ℕ × ℕ)) : List (ℕ × ℕ) :=
  T.mergeSort fun a b => decide (a.2 ≤ b.2)

/-- Lines 11–12: add the edge `{v_{j-1}, v_j}` (index `j - 1`) unless an edge `{v_{i'}, v_{j'}}`
(index `k = i'`, `j' = k + 1`) of the current cut set lies on the path `v_i … v_j`. -/
def step (E : Finset ℕ) (p : ℕ × ℕ) : Finset ℕ :=
  if ¬ ∃ k ∈ E, p.1 ≤ k ∧ k + 1 ≤ p.2 then insert (p.2 - 1) E else E

/-- **Algorithm 1** (`ChainMultiCut`): the indices `k` of the cut edges `{v_k, v_{k+1}}`. -/
def chainMultiCut (T : List (ℕ × ℕ)) : Finset ℕ :=
  (sortByRight (orient T)).foldl step ∅

/-- The loop with a constant-time test: remember the right end `j` of the last pair that added an
edge (`0` before the first one); the pair `(i, j)` adds an edge iff `last ≤ i`. -/
def stepFast (s : Finset ℕ × ℕ) (p : ℕ × ℕ) : Finset ℕ × ℕ :=
  if s.2 ≤ p.1 then (insert (p.2 - 1) s.1, p.2) else s

/-- Algorithm 1 with the constant-time test of `stepFast`. -/
def chainMultiCutFast (T : List (ℕ × ℕ)) : Finset ℕ :=
  ((sortByRight (orient T)).foldl stepFast (∅, 0)).1

/-! ### Basic facts about orienting and sorting -/

theorem mem_orient {T : List (ℕ × ℕ)} {p : ℕ × ℕ} :
    p ∈ orient T ↔ p.1 < p.2 ∧ (p ∈ T ∨ (p.2, p.1) ∈ T) := by
  simp only [orient, List.mem_filterMap]
  constructor
  · rintro ⟨q, hq, h⟩
    split_ifs at h with h1 h2
    · cases h; exact ⟨h1, Or.inl hq⟩
    · cases h; exact ⟨h2, Or.inr hq⟩
  · rintro ⟨hlt, hp | hp⟩
    · exact ⟨p, hp, by simp [hlt]⟩
    · exact ⟨(p.2, p.1), hp, by simp [hlt, not_lt.2 hlt.le]⟩

theorem mem_sortByRight {T : List (ℕ × ℕ)} {p : ℕ × ℕ} : p ∈ sortByRight T ↔ p ∈ T :=
  (List.mergeSort_perm _ _).mem_iff

theorem pairwise_sortByRight (T : List (ℕ × ℕ)) :
    (sortByRight T).Pairwise fun a b => a.2 ≤ b.2 := by
  have := List.pairwise_mergeSort (le := fun a b : ℕ × ℕ => decide (a.2 ≤ b.2))
    (fun a b c hab hbc => by simp at *; omega) (fun a b => by simp; omega) T
  unfold sortByRight
  simpa using this

/-! ### The paper's two facts -/

/-- Paths `[a.1, a.2)` and `[b.1, b.2)` of the chain are edge-disjoint. -/
def PathsDisjoint (W : Finset (ℕ × ℕ)) : Prop :=
  ∀ a ∈ W, ∀ b ∈ W, a ≠ b → a.2 ≤ b.1 ∨ b.2 ≤ a.1

/-- `C` cuts the path of every pair in `P` (pairs `(i, j)` with `i < j`; edge `k` lies on the path
iff `i ≤ k < j`). -/
def Cuts (C : Finset ℕ) (P : ℕ × ℕ → Prop) : Prop :=
  ∀ p, P p → ∃ k ∈ C, p.1 ≤ k ∧ k < p.2

-- CSLib candidate
/-- **First fact** of the optimality proof: a cut of pairwise edge-disjoint terminal paths has at
least as many edges as there are paths. -/
theorem card_le_of_pairwiseDisjoint {W : Finset (ℕ × ℕ)} (hW : PathsDisjoint W) {C : Finset ℕ}
    (hC : Cuts C (· ∈ W)) : W.card ≤ C.card := by
  choose! c hc h1 h2 using hC
  refine card_le_card_of_injOn c (fun w hw => hc w hw) fun a ha b hb hab => ?_
  by_contra hne
  have := h1 a ha; have := h2 a ha; have := h1 b hb; have := h2 b hb
  rcases hW a ha b hb hne with h | h <;> omega

/-- The invariant of the loop of Algorithm 1 over a list `L` of increasing pairs sorted by right
end. (1) The cut set `E` cuts every processed pair; (2) every cut edge is the last edge
`{v_{j-1}, v_j}` of a processed pair; (3) **second fact**: the pairs `W` that triggered the
addition of an edge have pairwise disjoint paths, and there are `|E|` of them. -/
theorem foldl_step_inv (L : List (ℕ × ℕ)) (hlt : ∀ p ∈ L, p.1 < p.2)
    (hs : L.Pairwise fun a b => a.2 ≤ b.2) :
    Cuts (L.foldl step ∅) (· ∈ L) ∧ (∀ k ∈ L.foldl step ∅, ∃ q ∈ L, k + 1 = q.2) ∧
      ∃ W : Finset (ℕ × ℕ), (∀ w ∈ W, w ∈ L) ∧ W.card = (L.foldl step ∅).card ∧
        (∀ w ∈ W, w.2 - 1 ∈ L.foldl step ∅) ∧ PathsDisjoint W := by
  induction L using List.reverseRecOn with
  | nil => exact ⟨fun p hp => by simp at hp, fun k hk => by simp at hk, ∅, by simp, by simp,
      by simp, by simp [PathsDisjoint]⟩
  | append_singleton L p ih =>
    have hltL : ∀ q ∈ L, q.1 < q.2 := fun q hq => hlt q (by simp [hq])
    have hp : p.1 < p.2 := hlt p (by simp)
    have hsL : L.Pairwise fun a b => a.2 ≤ b.2 := (List.pairwise_append.1 hs).1
    have hle : ∀ q ∈ L, q.2 ≤ p.2 := fun q hq => (List.pairwise_append.1 hs).2.2 q hq p (by simp)
    obtain ⟨hcut, hlast, W, hWL, hWc, hWE, hWd⟩ := ih hltL hsL
    set E := L.foldl step ∅
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    by_cases htr : ∃ k ∈ E, p.1 ≤ k ∧ k + 1 ≤ p.2
    · -- no edge added
      have hE : step E p = E := by rw [step, ite_eq_right (not_not.2 htr)]
      rw [hE]
      refine ⟨fun q hq => ?_, fun k hk => ?_, W, fun w hw => by simp [hWL w hw], hWc, hWE, hWd⟩
      · rcases List.mem_append.1 hq with hq | hq
        · exact hcut q hq
        · obtain rfl := List.mem_singleton.1 hq
          obtain ⟨k, hk, h1, h2⟩ := htr
          exact ⟨k, hk, h1, by omega⟩
      · obtain ⟨q, hq, h⟩ := hlast k hk
        exact ⟨q, by simp [hq], h⟩
    · -- the edge `{v_{j-1}, v_j}` is added
      have hE : step E p = insert (p.2 - 1) E := by rw [step, ite_eq_left htr]
      rw [hE]
      -- every earlier cut edge lies before `v_i`
      have hbefore : ∀ k ∈ E, k < p.1 := by
        intro k hk
        obtain ⟨q, hq, hkq⟩ := hlast k hk
        have := hle q hq
        by_contra h
        exact htr ⟨k, hk, by omega, by omega⟩
      have hnot : p.2 - 1 ∉ E := fun h => by have := hbefore _ h; omega
      have hpW : p ∉ W := fun h => hnot (hWE p h)
      refine ⟨fun q hq => ?_, fun k hk => ?_, insert p W, fun w hw => ?_, ?_, fun w hw => ?_,
        fun a ha b hb hab => ?_⟩
      · rcases List.mem_append.1 hq with hq | hq
        · obtain ⟨k, hk, h1, h2⟩ := hcut q hq
          exact ⟨k, mem_insert_of_mem hk, h1, h2⟩
        · obtain rfl := List.mem_singleton.1 hq
          exact ⟨q.2 - 1, mem_insert_self _ _, by omega, by omega⟩
      · rcases mem_insert.1 hk with rfl | hk
        · exact ⟨p, by simp, by omega⟩
        · obtain ⟨q, hq, h⟩ := hlast k hk
          exact ⟨q, by simp [hq], h⟩
      · rcases mem_insert.1 hw with rfl | hw
        · simp
        · simp [hWL w hw]
      · rw [card_insert_of_notMem hpW, card_insert_of_notMem hnot, hWc]
      · rcases mem_insert.1 hw with rfl | hw
        · exact mem_insert_self _ _
        · exact mem_insert_of_mem (hWE w hw)
      · -- the paper: "the first edge of p₂ is after the last edge of p₁"
        have key : ∀ w ∈ W, w.2 ≤ p.1 := fun w hw => by
          have := hbefore _ (hWE w hw); have := hltL w (hWL w hw); omega
        rcases mem_insert.1 ha with ha' | ha' <;> rcases mem_insert.1 hb with hb' | hb'
        · exact absurd (ha'.trans hb'.symm) hab
        · rw [ha']; exact Or.inr (key b hb')
        · rw [hb']; exact Or.inl (key a ha')
        · exact hWd a ha' b hb' hab

-- CSLib candidate
/-- On sorted increasing pairs, the loop's output is a minimum cut. -/
theorem foldl_step_optimal (L : List (ℕ × ℕ)) (hlt : ∀ p ∈ L, p.1 < p.2)
    (hs : L.Pairwise fun a b => a.2 ≤ b.2) :
    Cuts (L.foldl step ∅) (· ∈ L) ∧ ∀ C, Cuts C (· ∈ L) → (L.foldl step ∅).card ≤ C.card := by
  obtain ⟨hcut, -, W, hWL, hWc, -, hWd⟩ := foldl_step_inv L hlt hs
  exact ⟨hcut, fun C hC => hWc ▸ card_le_of_pairwiseDisjoint hWd fun w hw => hC w (hWL w hw)⟩

/-! ### Correctness and optimality of Algorithm 1 -/

/-- The terminal pairs, as paths `[min, max)` of the chain. -/
def TermPair (T : List (ℕ × ℕ)) (p : ℕ × ℕ) : Prop :=
  p.1 < p.2 ∧ (p ∈ T ∨ (p.2, p.1) ∈ T)

theorem mem_sortByRight_orient {T : List (ℕ × ℕ)} {p : ℕ × ℕ} :
    p ∈ sortByRight (orient T) ↔ TermPair T p := by
  rw [mem_sortByRight, mem_orient]; rfl

/-- Algorithm 1 cuts the path between every terminal pair `(s, t)` with `s ≠ t`. -/
theorem chainMultiCut_cuts (T : List (ℕ × ℕ)) : Cuts (chainMultiCut T) (TermPair T) := by
  have h := (foldl_step_optimal (sortByRight (orient T))
    (fun p hp => (mem_sortByRight_orient.1 hp).1) (pairwise_sortByRight _)).1
  exact fun p hp => h p (mem_sortByRight_orient.2 hp)

/-- Algorithm 1 outputs a minimum cut: no cut of all terminal paths is smaller. -/
theorem chainMultiCut_card_le (T : List (ℕ × ℕ)) {C : Finset ℕ} (hC : Cuts C (TermPair T)) :
    (chainMultiCut T).card ≤ C.card :=
  (foldl_step_optimal (sortByRight (orient T))
    (fun _ hp => (mem_sortByRight_orient.1 hp).1) (pairwise_sortByRight _)).2 C
    fun p hp => hC p (mem_sortByRight_orient.1 hp)

/-- Every cut edge of Algorithm 1 is the last edge `{v_{j-1}, v_j}` of a terminal pair. -/
theorem chainMultiCut_edge (T : List (ℕ × ℕ)) {k : ℕ} (hk : k ∈ chainMultiCut T) :
    ∃ p, TermPair T p ∧ k + 1 = p.2 := by
  obtain ⟨-, h, -⟩ := foldl_step_inv (sortByRight (orient T))
    (fun p hp => (mem_sortByRight_orient.1 hp).1) (pairwise_sortByRight _)
  obtain ⟨q, hq, h⟩ := h k hk
  exact ⟨q, mem_sortByRight_orient.1 hq, h⟩

/-! ### The constant-time test -/

/-- With the cut set `E` of the literal loop and `last` the right end of the last triggering pair,
the literal test of line 11 agrees with `last ≤ i`. -/
theorem foldl_stepFast (L : List (ℕ × ℕ)) (hlt : ∀ p ∈ L, p.1 < p.2)
    (hs : L.Pairwise fun a b => a.2 ≤ b.2) :
    (L.foldl stepFast (∅, 0)).1 = L.foldl step ∅ ∧
      (∀ k ∈ L.foldl step ∅, k + 1 ≤ (L.foldl stepFast (∅, 0)).2) ∧
      ((L.foldl stepFast (∅, 0)).2 = 0 ∨ (L.foldl stepFast (∅, 0)).2 - 1 ∈ L.foldl step ∅) := by
  induction L using List.reverseRecOn with
  | nil => simp
  | append_singleton L p ih =>
    have hltL : ∀ q ∈ L, q.1 < q.2 := fun q hq => hlt q (by simp [hq])
    have hp : p.1 < p.2 := hlt p (by simp)
    have hsL : L.Pairwise fun a b => a.2 ≤ b.2 := (List.pairwise_append.1 hs).1
    have hle : ∀ q ∈ L, q.2 ≤ p.2 := fun q hq => (List.pairwise_append.1 hs).2.2 q hq p (by simp)
    obtain ⟨h1, h2, h3⟩ := ih hltL hsL
    obtain ⟨-, hlast, -⟩ := foldl_step_inv L hltL hsL
    simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]
    set E := L.foldl step ∅
    set s := L.foldl stepFast (∅, 0)
    have hkp : ∀ k ∈ E, k + 1 ≤ p.2 := fun k hk => by
      obtain ⟨q, hq, h⟩ := hlast k hk; have := hle q hq; omega
    have hiff : (∃ k ∈ E, p.1 ≤ k ∧ k + 1 ≤ p.2) ↔ ¬ s.2 ≤ p.1 := by
      constructor
      · rintro ⟨k, hk, hk1, -⟩; have := h2 k hk; omega
      · intro h
        rcases h3 with h3 | h3
        · omega
        · exact ⟨_, h3, by omega, by have := hkp _ h3; omega⟩
    by_cases ht : s.2 ≤ p.1
    · have hE : step E p = insert (p.2 - 1) E := by
        rw [step, ite_eq_left fun h => hiff.1 h ht]
      have hS : stepFast s p = (insert (p.2 - 1) s.1, p.2) := by simp [stepFast, ht]
      rw [hE, hS, h1]
      refine ⟨rfl, fun k hk => ?_, Or.inr (mem_insert_self _ _)⟩
      rcases mem_insert.1 hk with rfl | hk
      · simp only; omega
      · exact hkp k hk
    · have hE : step E p = E := by rw [step, ite_eq_right (not_not.2 (hiff.2 ht))]
      have hS : stepFast s p = s := by simp [stepFast, ht]
      rw [hE, hS]
      exact ⟨h1, h2, h3⟩

/-- Algorithm 1 with the constant-time test computes the same cut: after sorting, the loop does
`O(1)` work per terminal pair. -/
theorem chainMultiCut_eq_fast (T : List (ℕ × ℕ)) : chainMultiCutFast T = chainMultiCut T :=
  (foldl_stepFast _ (fun _ hp => (mem_sortByRight_orient.1 hp).1) (pairwise_sortByRight _)).1

/-! ### Algorithm 1 on the chain graph -/

variable {n : ℕ}

/-- The input of Algorithm 1 for terminal pairs of the chain `v_0 - … - v_{n-1}`. -/
def toNat (T : List (Fin n × Fin n)) : List (ℕ × ℕ) := T.map fun p => (p.1.val, p.2.val)

/-- The edges `{v_k, v_{k+1}}`, `k ∈ chainMultiCut T`, returned by Algorithm 1. -/
def chainMultiCutEdges (T : List (Fin n × Fin n)) : Finset (Sym2 (Fin n)) :=
  edgesOf (univ.filter fun k : Fin n => k.val ∈ chainMultiCut (toNat T))

theorem termPair_toNat {T : List (Fin n × Fin n)} {p : Fin n × Fin n} (hp : p ∈ T)
    (hne : p.1 ≠ p.2) : TermPair (toNat T) ((min p.1 p.2).val, (max p.1 p.2).val) := by
  rcases lt_or_gt_of_ne hne with h | h
  · refine ⟨by simpa [min_eq_left h.le, max_eq_right h.le] using h, Or.inl ?_⟩
    simp only [min_eq_left h.le, max_eq_right h.le, toNat, List.mem_map]
    exact ⟨p, hp, rfl⟩
  · refine ⟨by simpa [min_eq_right h.le, max_eq_left h.le] using h, Or.inr ?_⟩
    simp only [min_eq_right h.le, max_eq_left h.le, toNat, List.mem_map]
    exact ⟨p, hp, rfl⟩

/-- **Algorithm 1 is optimal** (Section 3): for terminal pairs `T` of the chain
`v_0 - v_1 - … - v_{n-1}` without loops `(v, v)`, the edges `{v_k, v_{k+1}}` chosen by the greedy
algorithm form a minimum multi-cut. -/
theorem algorithm_1_optimal (T : List (Fin n × Fin n)) (hT : ∀ p ∈ T, p.1 ≠ p.2) :
    IsMinMultiCut (pathGraph n) T.toFinset (chainMultiCutEdges T) := by
  set E := chainMultiCut (toNat T)
  set F := univ.filter fun k : Fin n => k.val ∈ E
  refine ⟨⟨fun e he => ?_, fun p hp => ?_⟩, fun C hC => ?_⟩
  · obtain ⟨k, hk, rfl⟩ := mem_image.1 (mem_coe.1 he)
    exact chainEdge_mem_edgeSet (mem_filter.1 hk).2
  · have hp := List.mem_toFinset.1 hp
    obtain ⟨k, hkE, h1, h2⟩ := chainMultiCut_cuts (toNat T) _ (termPair_toNat hp (hT p hp))
    have hkn : k < n := by have := (max p.1 p.2).isLt; omega
    rw [not_reachable_iff]
    refine ⟨⟨k, hkn⟩, Fin.le_def.2 h1, Fin.lt_def.2 h2, mem_coe.2 (mem_image_of_mem _ ?_)⟩
    refine mem_filter.2 ⟨mem_filter.2 ⟨mem_univ _, hkE⟩, ?_⟩
    have := (max p.1 p.2).isLt; simp only at h2 ⊢; omega
  · have hcut : Cuts ((cutIdx C).image Fin.val) (TermPair (toNat T)) := by
      rintro ⟨i, j⟩ ⟨hij, hq⟩
      have hq' : ∃ p ∈ T, p.1.val = i ∧ p.2.val = j ∨ p.1.val = j ∧ p.2.val = i := by
        rcases hq with hq | hq <;> obtain ⟨p, hp, he⟩ := List.mem_map.1 hq <;>
          simp only [Prod.mk.injEq] at he
        · exact ⟨p, hp, Or.inl he⟩
        · exact ⟨p, hp, Or.inr he⟩
      obtain ⟨p, hp, hpe⟩ := hq'
      obtain ⟨k, h1, h2, h3⟩ := (not_reachable_iff _ _ _).1 (hC.2 p (List.mem_toFinset.2 hp))
      have hkC : k ∈ cutIdx C := by
        refine mem_filter.2 ⟨mem_univ _, ?_, h3⟩
        have := (max p.1 p.2).isLt; have := Fin.lt_def.1 h2; omega
      refine ⟨k.val, mem_image_of_mem _ hkC, ?_, ?_⟩ <;>
        rcases hpe with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
        simp only [Fin.le_def, Fin.lt_def, Fin.val_min, Fin.val_max] at h1 h2 <;> omega
    calc (chainMultiCutEdges T).card ≤ F.card := card_edgesOf_le F
      _ ≤ E.card := card_le_card_of_injOn Fin.val (fun k hk => (mem_filter.1 hk).2)
          Fin.val_injective.injOn
      _ ≤ ((cutIdx C).image Fin.val).card := chainMultiCut_card_le _ hcut
      _ ≤ (cutIdx C).card := card_image_le
      _ = C.card := card_cutIdx hC.1

/-! ### Fence insertion via Algorithm 1 -/

/-- The algorithmic core of the title *"Fence insertion for straight-line programs is in P"*:
running Algorithm 1 on the required orders `→` (Lemma 2.4: `T = →`) and placing a fence after
operation `k` for every cut edge `{v_k, v_{k+1}}` gives a minimum single-type fence insertion
(Definition 2.2). Only optimality is proved here; the polynomial running time is not formalized
in a cost model (see `chainMultiCut_eq_fast` for the `O(1)` loop test). -/
theorem fenceIns_greedy_optimal (ord : Finset (Fin n × Fin n)) (hlt : ∀ x ∈ ord, x.1 < x.2) :
    IsOptIns1 ord (univ.filter fun k : Fin n => k.val ∈ chainMultiCut (toNat ord.toList)) := by
  set E := chainMultiCut (toNat ord.toList)
  refine ⟨fun x hx => ?_, fun G hG => ?_⟩
  · have hx' : x ∈ ord.toList := mem_toList.2 hx
    have h := termPair_toNat hx' (hlt x hx).ne
    rw [min_eq_left (hlt x hx).le, max_eq_right (hlt x hx).le] at h
    obtain ⟨k, hkE, h1, h2⟩ := chainMultiCut_cuts _ _ h
    have hkn : k < n := by have := x.2.isLt; simp only at h2; omega
    exact ⟨⟨k, hkn⟩, mem_filter.2 ⟨mem_univ _, hkE⟩, Fin.le_def.2 h1, Fin.lt_def.2 h2⟩
  · have hcut : Cuts (G.image Fin.val) (TermPair (toNat ord.toList)) := by
      rintro ⟨i, j⟩ ⟨hij, hq⟩
      rcases hq with hq | hq <;> obtain ⟨x, hx, he⟩ := List.mem_map.1 hq <;>
        simp only [Prod.mk.injEq] at he <;> have hx' := mem_toList.1 hx <;>
        have := Fin.lt_def.1 (hlt x hx')
      · obtain ⟨k, hk, h1, h2⟩ := hG x hx'
        refine ⟨k.val, mem_image_of_mem _ hk, ?_, ?_⟩ <;>
          simp only [Fin.le_def, Fin.lt_def] at h1 h2 <;> omega
      · simp only at hij; omega
    calc (univ.filter fun k : Fin n => k.val ∈ E).card ≤ E.card :=
          card_le_card_of_injOn Fin.val (fun k hk => (mem_filter.1 hk).2) Fin.val_injective.injOn
      _ ≤ (G.image Fin.val).card := chainMultiCut_card_le _ hcut
      _ ≤ G.card := card_image_le

/-! ### Examples -/

/-- Figure 2: the required orders `1 → 3`, `2 → 4` are cut by one edge, after operation `2`
(index `1` here). -/
example : chainMultiCut [(0, 2), (1, 3)] = {1} := by
  simp [chainMultiCut, sortByRight, orient, step]

/-- Ties and a pair starting at an earlier cut: `(0,2)` cuts edge `1`, `(1,2)` is already cut,
`(2,3)` is not (edge `1` is not on the path `v_2 v_3`) and cuts edge `2`. -/
example : chainMultiCut [(2, 3), (1, 2), (0, 2)] = {1, 2} := by
  simp [chainMultiCut, sortByRight, orient, List.mergeSort, List.MergeSort.Internal.splitInTwo,
    step]
  decide

/-- Pairs are oriented (line 5). -/
example : chainMultiCut [(3, 1), (2, 0)] = {1} := by
  simp [chainMultiCut, sortByRight, orient, step]

/-- A loop `(v, v)` is silently dropped by line 5, although no multi-cut separates `v` from
itself (`not_isMultiCut_of_diag`). -/
example : chainMultiCut [(1, 1)] = ∅ := by
  simp [chainMultiCut, sortByRight, orient]

end Podc.FenceInsertionChain
