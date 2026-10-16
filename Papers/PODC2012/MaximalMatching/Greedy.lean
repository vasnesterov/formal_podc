import Papers.PODC2012.MaximalMatching.LowerBound

/-!
# The greedy algorithm: Lemma 1 and the tight bound of Theorem 2

Greedy maximal matching on a `k`-edge-coloured tree: in step `i = 0, 1, …, k-1` (colour `i`; the
paper numbers colours `1, …, k`), every edge of colour `i` whose endpoints are both unmatched joins
the matching. Whether `v` is matched within the first `n` steps only depends on the radius-`n`
view of `v`, so the output is a function of the radius-`k` view: running time `k - 1`.
-/

namespace Papers.PODC2012.MaximalMatching

open Cslib.ColourSystem FreeCox Pointwise

variable {k : ℕ}

/-- `greedyMatched V n v`: `v` is matched during the first `n` steps (colours `< n`). -/
def greedyMatched (V : Set (FreeCox k)) : ℕ → FreeCox k → Prop
  | 0, _ => False
  | n + 1, v => greedyMatched V n v ∨
      ∃ hn : n < k, v * gen ⟨n, hn⟩ ∈ V ∧ ¬ greedyMatched V n v ∧
        ¬ greedyMatched V n (v * gen ⟨n, hn⟩)

/-- Colour `c` is the greedy matching edge at `v`. -/
def GreedyEdge (V : Set (FreeCox k)) (v : FreeCox k) (c : Fin k) : Prop :=
  v * gen c ∈ V ∧ ¬ greedyMatched V c v ∧ ¬ greedyMatched V c (v * gen c)

open Classical in
/-- The greedy algorithm. -/
noncomputable def greedy : Algorithm k := fun V v =>
  if h : ∃ c, GreedyEdge V v c then some h.choose else none

theorem greedyMatched_iff (V : Set (FreeCox k)) (n : ℕ) (v : FreeCox k) :
    greedyMatched V n v ↔ ∃ c : Fin k, (c : ℕ) < n ∧ GreedyEdge V v c := by
  induction n generalizing v with
  | zero => simp [greedyMatched]
  | succ n ih =>
    have key : ∀ hn : n < k, GreedyEdge V v ⟨n, hn⟩ ↔ (v * gen ⟨n, hn⟩ ∈ V ∧
        ¬ greedyMatched V n v ∧ ¬ greedyMatched V n (v * gen ⟨n, hn⟩)) := fun hn => Iff.rfl
    simp only [greedyMatched]
    constructor
    · rintro (h | ⟨hn, hg⟩)
      · obtain ⟨c, hc, hg⟩ := (ih v).1 h; exact ⟨c, by omega, hg⟩
      · exact ⟨⟨n, hn⟩, by simp, (key hn).2 hg⟩
    · rintro ⟨c, hc, hg⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hc with hc | hc
      · exact Or.inl ((ih v).2 ⟨c, hc, hg⟩)
      · right
        obtain ⟨c, hcl⟩ := c
        simp only at hc
        subst hc
        exact ⟨hcl, (key hcl).1 hg⟩

/-- At most one greedy edge per node. -/
theorem greedyEdge_unique {V : Set (FreeCox k)} {v : FreeCox k} {c c' : Fin k}
    (h : GreedyEdge V v c) (h' : GreedyEdge V v c') : c = c' := by
  by_contra hne
  rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hlt | hlt
  · exact h'.2.1 ((greedyMatched_iff V c' v).2 ⟨c, hlt, h⟩)
  · exact h.2.1 ((greedyMatched_iff V c v).2 ⟨c', hlt, h'⟩)

theorem greedy_eq_some {V : Set (FreeCox k)} {v : FreeCox k} {c : Fin k} :
    greedy V v = some c ↔ GreedyEdge V v c := by
  unfold greedy
  split_ifs with h
  · simp only [Option.some.injEq]
    exact ⟨fun e => e ▸ h.choose_spec, fun hc => greedyEdge_unique h.choose_spec hc⟩
  · simp only [false_iff]
    exact fun hc => h ⟨c, hc⟩

theorem greedy_eq_none {V : Set (FreeCox k)} {v : FreeCox k} :
    greedy V v = none ↔ ∀ c, ¬ GreedyEdge V v c := by
  unfold greedy
  split_ifs with h
  · simp only [false_iff, not_forall, not_not]; exact h
  · simp only [true_iff]; push Not at h; exact h

theorem greedyEdge_symm {V : Set (FreeCox k)} {v : FreeCox k}
    (hv : v ∈ V) {c : Fin k} (h : GreedyEdge V v c) : GreedyEdge V (v * gen c) c := by
  refine ⟨by rw [mul_gen_mul_gen]; exact hv, h.2.2, by rw [mul_gen_mul_gen]; exact h.2.1⟩

/-- The greedy algorithm finds a maximal matching in every `k`-colour system. -/
theorem greedy_findsMaximalMatching {V : Set (FreeCox k)} (_hV : IsColourSystem V) :
    FindsMaximalMatching greedy V := by
  intro v hv
  refine ⟨fun c hc => mem_colours.2 (greedy_eq_some.1 hc).1, fun c hc => ?_, fun hn c hc => ?_⟩
  · exact greedy_eq_some.2 (greedyEdge_symm hv (greedy_eq_some.1 hc))
  · intro hn'
    rw [greedy_eq_none] at hn hn'
    have hnot : ∀ (w : FreeCox k) (n : ℕ), (∀ c, ¬ GreedyEdge V w c) → ¬ greedyMatched V n w :=
      fun w n hw hm => by
        obtain ⟨c', -, hc'⟩ := (greedyMatched_iff V n w).1 hm
        exact hw c' hc'
    exact hn c ⟨mem_colours.1 hc, hnot v c hn, hnot _ c hn'⟩

/-- Locality of `greedyMatched`: it only depends on the radius-`n` view. -/
theorem greedyMatched_congr {U W : Set (FreeCox k)} (n : ℕ) :
    ∀ x y : FreeCox k, (∀ z, len z ≤ n → (x * z ∈ U ↔ y * z ∈ W)) →
      (greedyMatched U n x ↔ greedyMatched W n y) := by
  induction n with
  | zero => intros; simp [greedyMatched]
  | succ n ih =>
    intro x y hxy
    have h0 : greedyMatched U n x ↔ greedyMatched W n y :=
      ih x y (fun z hz => hxy z (by omega))
    simp only [greedyMatched, h0]
    refine or_congr Iff.rfl (exists_congr fun hn => and_congr ?_ (and_congr Iff.rfl ?_))
    · exact hxy _ (by simp)
    · apply not_congr
      apply ih
      intro z hz
      rw [mul_assoc, mul_assoc]
      exact hxy _ (by have := len_mul_le (gen ⟨n, hn⟩) z; simp at this; omega)

/-- **Lemma 1**: the greedy algorithm finds a maximal matching in every anonymous `k`-edge-coloured
tree and has running time `k - 1`. -/
theorem lemma1 :
    HasRunningTime (greedy : Algorithm k) (k - 1) ∧
      ∀ V : Set (FreeCox k), IsColourSystem V → FindsMaximalMatching greedy V := by
  refine ⟨fun U V u v hU hV hu hv e => ?_, fun V hV => greedy_findsMaximalMatching hV⟩
  have hxy : ∀ z, len z ≤ k → (u * z ∈ U ↔ v * z ∈ V) := by
    intro z hz
    have := Set.ext_iff.1 e z
    simp only [mem_ball, mem_inv_smul] at this
    exact ⟨fun h => (this.1 ⟨h, by omega⟩).1, fun h => (this.2 ⟨h, by omega⟩).1⟩
  have hedge : ∀ c : Fin k, GreedyEdge U u c ↔ GreedyEdge V v c := by
    intro c
    unfold GreedyEdge
    refine and_congr (by simpa using hxy (gen c) (by simp; have := c.2; omega)) (and_congr ?_ ?_)
    · exact not_congr (greedyMatched_congr _ u v (fun z hz => hxy z (by omega)))
    · apply not_congr
      apply greedyMatched_congr
      intro z hz
      rw [mul_assoc, mul_assoc]
      exact hxy _ (by have := len_mul_le (gen c) z; simp at this; omega)
  cases h : greedy V v with
  | none =>
    rw [greedy_eq_none] at h ⊢
    exact fun c hc => h c ((hedge c).1 hc)
  | some c =>
    rw [greedy_eq_some] at h ⊢
    exact (hedge c).2 h

/-- Non-vacuity of Theorem 6: the greedy algorithm satisfies its hypotheses (with `r = k - 1`). -/
theorem good_greedy : Good (greedy : Algorithm k) (k - 1) :=
  ⟨lemma1.1, fun V hV _ => lemma1.2 V hV⟩

/-- **Theorem 2** (tight bound): `k - 1` is exactly the optimal running time for maximal matching
in anonymous `k`-edge-coloured trees, `k ≥ 1`. -/
theorem theorem2 :
    (∃ A : Algorithm k, HasRunningTime A (k - 1) ∧
        ∀ V : Set (FreeCox k), IsColourSystem V → FindsMaximalMatching A V) ∧
      ∀ (A : Algorithm k) (r : ℕ), HasRunningTime A r →
        (∀ V : Set (FreeCox k), IsColourSystem V → FindsMaximalMatching A V) → k - 1 ≤ r :=
  ⟨⟨greedy, lemma1⟩, fun A r hA hMM => theorem2_lower A r hA hMM⟩

end Papers.PODC2012.MaximalMatching
