import Papers.PODC2016.ShortcutsNoEmbedding.CoreSlow

/-!
# Theorem 1 of [HIZ16], deterministic version (`FindShortcut` with `CoreSlow`)

`FindShortcut` repeats: run the core subroutine on the parts that are not yet good, run
`Verification` (Corollary 6) to find the parts whose computed shortcut has at most `3b` block
components, fix their shortcut edges and discard the rest.

* `restrictParts P R`: the parts outside `R` are replaced by `∅` (they do not take part in the
  iteration; empty parts are seen by no tree edge).
* `coreOn R`: the shortcut computed by `CoreSlow` on the parts in `R`.
* `goodOn R`: the parts of `R` whose computed shortcut has `≤ 3b` block components (the output of
  `Verification` with `b₀ = 3b`, see `corollary_6` in `Supergraph.lean`).
* `remaining k`: the parts that are not good after `k` iterations; `findShortcut i` is the shortcut
  computed for part `i` in the iteration in which it became good.

## Main results

* `card_remaining_succ`: each iteration at least halves the number of remaining parts (Lemma 5).
* `remaining_numIter`: after `⌊log₂ N⌋ + 1` iterations no part remains.
* `theorem_1_deterministic`: the result is a `T`-restricted shortcut with congestion
  `≤ 2c (⌊log₂ N⌋ + 1)` and block parameter `≤ 3b` (each block containing a vertex of its part).
  The paper's randomized Theorem 1 has congestion `O(c log N)` via `CoreFast`
  (`lemma_4_combinatorial` covers the deterministic part of its analysis).
-/

set_option linter.unusedSectionVars false

namespace ShortcutsNoEmbedding

open SimpleGraph Finset RootedTree

variable {V ι : Type*} [Fintype V] [DecidableEq V] [Fintype ι] [DecidableEq ι]
  {G : SimpleGraph V} (T : G.RootedTree) (P : ι → Finset V) (c b : ℕ)

/-- The parts of `R`; the others are replaced by the empty set. -/
def restrictParts (R : Finset ι) (i : ι) : Finset V := if i ∈ R then P i else ∅

/-- The shortcut computed by `CoreSlow` on the parts in `R`. -/
noncomputable def coreOn (R : Finset ι) : ι → Finset (Sym2 V) :=
  coreSlow T (restrictParts P R) c

/-- The parts of `R` whose computed shortcut has at most `3b` block components: the output of the
`Verification` subroutine with `b₀ = 3b` (Corollary 6). -/
noncomputable def goodOn (R : Finset ι) : Finset ι :=
  R.filter fun i => blockParam (P i) (coreOn T P c R i) ≤ 3 * b

/-- The parts that are not yet good after `k` iterations of `FindShortcut`. -/
noncomputable def remaining : ℕ → Finset ι
  | 0 => univ
  | k + 1 => remaining k \ goodOn T P c b (remaining k)

/-- The number of iterations: `⌊log₂ N⌋ + 1` for `N` parts. -/
def numIter (N : ℕ) : ℕ := Nat.log 2 N + 1

variable {T P c b}

variable {H : ι → Finset (Sym2 V)} (hHr : ∀ i, T.Restricts (H i))
  (hHc : G.CongestionLE univ H c) (hHb : ∀ i, blockParam (P i) (H i) ≤ b)
include hHr hHc hHb

/-- **Proof of Theorem 1, one iteration.** Each iteration at least halves the number of remaining
parts: by Lemma 5 (applied to the remaining parts, with the canonical shortcut restricted to them),
at least half of them are good. -/
theorem card_remaining_succ (k : ℕ) :
    2 * (remaining T P c b (k + 1)).card ≤ (remaining T P c b k).card := by
  classical
  set R := remaining T P c b k
  let HR : ι → Finset (Sym2 V) := fun i => if i ∈ R then H i else ∅
  have hHRr : ∀ i, T.Restricts (HR i) := fun i => by
    by_cases hi : i ∈ R
    · simpa [HR, hi] using hHr i
    · intro e he; simp [HR, hi] at he
  have hHRc : G.CongestionLE univ HR c := by
    intro e he
    refine le_trans ?_ (hHc e he)
    exact_mod_cast card_le_card fun i hi => by
      simp only [mem_filter, mem_univ, true_and] at hi ⊢
      by_cases hr : i ∈ R <;> simp_all [HR]
  have hHRb : ∀ i, blockParam (restrictParts P R i) (HR i) ≤ b := fun i => by
    by_cases hi : i ∈ R
    · simpa [HR, restrictParts, hi] using hHb i
    · simp [HR, restrictParts, hi, blockParam]
  obtain ⟨J, hJR, hcard, hJ⟩ := many_good_of_cut_on (restrictParts P R)
    (U := coreSlowCut T (restrictParts P R) c) (fun t ht => by
      have := (coreSlowCut_spec _ c t).1 ht; exact ⟨this.1, this.2.le⟩)
    hHRr hHRc hHRb R (fun i hi => by simp [restrictParts, HR, hi])
  have hJgood : J ⊆ goodOn T P c b R := by
    intro i hi
    have := hJ i hi
    simp only [restrictParts, hJR hi, ite_true] at this
    exact mem_filter.2 ⟨hJR hi, this⟩
  have hsub : goodOn T P c b R ⊆ R := filter_subset _ _
  change 2 * (R \ goodOn T P c b R).card ≤ R.card
  rw [card_sdiff_of_subset hsub]
  have := card_le_card hJgood
  have := card_le_card hsub
  omega

theorem card_remaining_mul_pow (k : ℕ) :
    (remaining T P c b k).card * 2 ^ k ≤ Fintype.card ι := by
  induction k with
  | zero => simp [remaining]
  | succ k ih =>
    have h1 := Nat.mul_le_mul_right (2 ^ k) (card_remaining_succ hHr hHc hHb k)
    rw [pow_succ]
    nlinarith

/-- After `⌊log₂ N⌋ + 1` iterations, all parts are good. -/
theorem remaining_numIter : remaining T P c b (numIter (Fintype.card ι)) = ∅ := by
  have h := card_remaining_mul_pow hHr hHc hHb (numIter (Fintype.card ι))
  have hlt : Fintype.card ι < 2 ^ numIter (Fintype.card ι) := Nat.lt_pow_succ_log_self
    (by norm_num) _
  rw [← card_eq_zero]
  by_contra hne
  have : 2 ^ numIter (Fintype.card ι) ≤ (remaining T P c b _).card * 2 ^ _ :=
    Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero hne)
  omega

theorem exists_good (i : ι) : ∃ k < numIter (Fintype.card ι),
    i ∈ goodOn T P c b (remaining T P c b k) := by
  have : ∀ k, i ∈ remaining T P c b k ∨ ∃ j < k, i ∈ goodOn T P c b (remaining T P c b j) := by
    intro k
    induction k with
    | zero => left; simp [remaining]
    | succ k ih =>
      rcases ih with h | ⟨j, hj, h⟩
      · by_cases hg : i ∈ goodOn T P c b (remaining T P c b k)
        · exact Or.inr ⟨k, by omega, hg⟩
        · exact Or.inl (mem_sdiff.2 ⟨h, hg⟩)
      · exact Or.inr ⟨j, by omega, h⟩
  rcases this (numIter (Fintype.card ι)) with h | h
  · rw [remaining_numIter hHr hHc hHb] at h; simp at h
  · exact h

omit hHr hHc hHb in
variable (T P c b) in
open Classical in
/-- The iteration in which part `i` becomes good (`0` if never). -/
noncomputable def iterOf (i : ι) : ℕ :=
  if h : ∃ k, i ∈ goodOn T P c b (remaining T P c b k) then Nat.find h else 0

omit hHr hHc hHb in
variable (T P c b) in
/-- The shortcut produced by `FindShortcut`: the edges computed for part `i` in the iteration in
which it became good. -/
noncomputable def findShortcut (i : ι) : Finset (Sym2 V) :=
  coreOn T P c (remaining T P c b (iterOf T P c b i)) i

theorem iterOf_spec (i : ι) :
    i ∈ goodOn T P c b (remaining T P c b (iterOf T P c b i)) ∧
      iterOf T P c b i < numIter (Fintype.card ι) := by
  classical
  obtain ⟨k, hk, hg⟩ := exists_good hHr hHc hHb i
  have hex : ∃ k, i ∈ goodOn T P c b (remaining T P c b k) := ⟨k, hg⟩
  unfold iterOf
  rw [dite_eq_left hex]
  exact ⟨Nat.find_spec hex, lt_of_le_of_lt (Nat.find_min' hex hg) hk⟩

/-- **Theorem 1 of [HIZ16], deterministic version.** Let `T` be a rooted spanning tree and `P` a
family of `N` parts for which some `T`-restricted shortcut has congestion `≤ c` and block
parameter `≤ b`. `FindShortcut` (with `CoreSlow` as the core subroutine) terminates after
`⌊log₂ N⌋ + 1` iterations and returns a `T`-restricted shortcut with congestion
`≤ 2c (⌊log₂ N⌋ + 1)` in which every part has at most `3b` block components, each containing a
vertex of the part. -/
theorem theorem_1_deterministic :
    remaining T P c b (numIter (Fintype.card ι)) = ∅ ∧
      (∀ i, T.Restricts (findShortcut T P c b i)) ∧
      G.CongestionLE univ (findShortcut T P c b) (2 * c * numIter (Fintype.card ι) : ℕ) ∧
      ∀ i, blockParam (P i) (findShortcut T P c b i) ≤ 3 * b ∧
        BlocksMeetPart (P i) (findShortcut T P c b i) := by
  classical
  refine ⟨remaining_numIter hHr hHc hHb, fun i => restricts_cutShortcut _ _ i, ?_, fun i => ?_⟩
  · intro e _
    set K := numIter (Fintype.card ι)
    have hsub : univ.filter (fun i => e ∈ findShortcut T P c b i) ⊆
        (range K).biUnion fun k =>
          univ.filter fun i => e ∈ coreOn T P c (remaining T P c b k) i := by
      intro i hi
      simp only [mem_filter, mem_univ, true_and] at hi
      simp only [mem_biUnion, mem_range, mem_filter, mem_univ, true_and]
      exact ⟨_, (iterOf_spec hHr hHc hHb i).2, hi⟩
    have hk : ∀ k ∈ range K,
        (univ.filter fun i => e ∈ coreOn T P c (remaining T P c b k) i).card ≤ 2 * c :=
      fun k _ => card_filter_mem_cutShortcut_le univ
        (fun v hv hU => card_coreSlow_list_le _ c hv hU) e
    have := (card_le_card hsub).trans (card_biUnion_le.trans (sum_le_sum hk))
    simp only [sum_const, card_range, smul_eq_mul] at this
    exact_mod_cast this.trans (by rw [mul_comm])
  · obtain ⟨hg, -⟩ := iterOf_spec hHr hHc hHb i
    have hR := (mem_filter.1 hg).1
    refine ⟨(mem_filter.1 hg).2, ?_⟩
    have := blocksMeetPart_cutShortcut (T := T) (restrictParts P
      (remaining T P c b (iterOf T P c b i)))
      (coreSlowCut T (restrictParts P (remaining T P c b (iterOf T P c b i))) c) i
    simpa [findShortcut, coreOn, coreSlow, restrictParts, hR] using this

omit [DecidableEq ι] hHr hHc hHb in
/-- Non-vacuity: the hypotheses of `theorem_1_deterministic` are always satisfiable, e.g. by the
empty shortcut (congestion `0`, block parameter `≤ n`). -/
theorem empty_shortcut_canonical (T : G.RootedTree) (P : ι → Finset V) :
    (∀ i, T.Restricts ((fun _ => ∅ : ι → Finset (Sym2 V)) i)) ∧
      G.CongestionLE (univ : Finset ι) (fun _ => (∅ : Finset (Sym2 V))) (0 : ℕ) ∧
      ∀ i, blockParam (P i) ∅ ≤ Fintype.card V := by
  refine ⟨fun i e he => by simp at he, fun e _ => by simp, fun i => ?_⟩
  unfold blockParam
  calc _ ≤ (P i : Set V).ncard := Set.ncard_image_le (Set.toFinite _)
    _ ≤ (Set.univ : Set V).ncard := Set.ncard_le_ncard (Set.subset_univ _)
    _ = Fintype.card V := by rw [Set.ncard_univ, Nat.card_eq_fintype_card]

end ShortcutsNoEmbedding
