import Papers.PODC2010.HindsightLinearizability.Trace

/-!
# Lemma 5.4 (Backbone Lemma) as stated is false

The paper states: for a temporal backbone `ζ` going through `τ(i₀), …, τ(i_k)` of a shape-legal
trace, *there exists a sequence `i₀ = j₀ < j₁ < … < j_k = i_k`* such that `ζ(m)` is a backbone
link in `τ(j_m)` and `i₀ ≤ j_m ≤ i_m`.

Both the strict inequalities and `j_k = i_k` are wrong: the last link of a temporal backbone
need not be a backbone link when it is crossed (this is the whole point of hindsight), and
consecutive links may be backbone links only at the same past state. The Hindsight Lemma only
gives `j_{m-1} ≤ j_m ≤ i_m`, which is what the paper's own proof ("follows directly from Lemma
5.2") yields and all that is used later (`backbone_lemma` in `Heap.lean`).

Counterexample, in an actual execution of the set algorithm (`cexExec`): thread 0 runs
`add(5)` (heap `H → a → T` with `a = 2`), then thread 1 runs `remove(5)`. Let `i₀ = 10` be the
state just before the atomic section of `remove` and `i₁ = 11` the state right after it. Then
`ζ = ⟨H, a⟩, ⟨a, T⟩` is a temporal backbone through `τ(10), τ(11)`: `H.n ↦ a` is a backbone
link at `10` and `a.n ↦ T` is a link at `11` (the removed node keeps its successor). But
`a.n ↦ T` is a backbone link at `10` only: either requirement `j₁ = i₁` or `j₀ < j₁ ≤ i₁` forces
`j₁ = 11`, where `a` is marked and unreachable.

The trace is shape-legal by Theorem 4.1 (`shapeLegal_trace`), so the counterexample satisfies
the paper's hypotheses.
-/

namespace Podc.HindsightLinearizability

open Cslib.SharedMemory HeapState

/-- The conclusion of Lemma 5.4 as stated in the paper (with `j₀ = i₀ < j₁ < … < j_k = i_k`). -/
def BackboneConclusionAsStated (τ : ℕ → HeapState ℕ Key) (ζ : ℕ → ℕ × ℕ) (idx : ℕ → ℕ)
    (k : ℕ) : Prop :=
  ∃ j : ℕ → ℕ, j 0 = idx 0 ∧ (∀ m < k, j m < j (m + 1)) ∧ j k = idx k ∧
    ∀ m ≤ k, idx 0 ≤ j m ∧ j m ≤ idx m ∧ (τ (j m)).BackboneLink (ζ m).1 (ζ m).2

/-- Lemma 5.4 as stated, but without the strict inequalities (only `j_k = i_k`). -/
def BackboneConclusionLastEq (τ : ℕ → HeapState ℕ Key) (ζ : ℕ → ℕ × ℕ) (idx : ℕ → ℕ)
    (k : ℕ) : Prop :=
  ∃ j : ℕ → ℕ, j 0 = idx 0 ∧ j k = idx k ∧
    ∀ m ≤ k, idx 0 ≤ j m ∧ j m ≤ idx m ∧ (τ (j m)).BackboneLink (ζ m).1 (ζ m).2

/-- Lemma 5.4 as stated, but without `j_k = i_k` (only the strict inequalities). -/
def BackboneConclusionStrict (τ : ℕ → HeapState ℕ Key) (ζ : ℕ → ℕ × ℕ) (idx : ℕ → ℕ)
    (k : ℕ) : Prop :=
  ∃ j : ℕ → ℕ, j 0 = idx 0 ∧ (∀ m < k, j m < j (m + 1)) ∧
    ∀ m ≤ k, idx 0 ≤ j m ∧ j m ≤ idx m ∧ (τ (j m)).BackboneLink (ζ m).1 (ζ m).2

instance (p : ℕ) (o : setSpec.Op) : Decidable ((impl ℕ).allowed p o) := isTrue trivial

instance : DecidableEq setSpec.Resp := inferInstanceAs (DecidableEq Bool)

/-- `add(5)` by thread 0, then `remove(5)` by thread 1. -/
def cexExec : List (Label ℕ setSpec) :=
  [.inv 0 (.add 5), .tau 0, .tau 0, .tau 0, .tau 0, .ret 0 true,
   .inv 1 (.remove 5), .tau 1, .tau 1, .tau 1, .tau 1]

lemma cexExec_valid : (impl ℕ).Valid cexExec :=
  (impl ℕ).valid_of_crun (by decide)

lemma memAt_cex (j : ℕ) :
    memAt cexExec j = (((impl ℕ).crun (cexExec.take j)).getD (impl ℕ).initCfg).mem () := by
  unfold memAt cfgAt; rw [Impl.run_eq_crun]

lemma cex_next_10 : (memAt cexExec 10).next 1 = some 2 := by rw [memAt_cex]; decide
lemma cex_H_10 : (memAt cexExec 10).H = 1 := by rw [memAt_cex]; decide
lemma cex_next_11 : (memAt cexExec 11).next 2 = some 0 := by rw [memAt_cex]; decide
lemma cex_mark_11 : (memAt cexExec 11).mark 2 = true := by rw [memAt_cex]; decide
lemma cex_cnt_11 : 2 < (memAt cexExec 11).cnt := by rw [memAt_cex]; decide

/-- The temporal backbone `⟨H, a⟩, ⟨a, T⟩` through `τ(10), τ(11)`. -/
def cexζ : ℕ → ℕ × ℕ := fun m => if m = 0 then (1, 2) else (2, 0)
/-- The subsequence `10, 11`. -/
def cexIdx : ℕ → ℕ := fun m => 10 + m

lemma cex_temporalBackbone : TemporalBackbone (trace cexExec) cexζ cexIdx 1 where
  path m hm := by obtain rfl : m = 0 := by omega
                  rfl
  idx_lt m _ := by simp [cexIdx]
  first := by
    refine ⟨?_, ?_⟩
    · show Relation.ReflTransGen _ (memAt cexExec 10).H 1
      rw [cex_H_10]
    · exact cex_next_10
  link m h0 h1 := by
    obtain rfl : m = 1 := by omega
    exact cex_next_11

lemma cex_not_backbone : ¬ (trace cexExec 11).Backbone 2 := by
  intro h
  have := ((memInv_memAt cexExec_valid 11).unmarked_iff_backbone cex_cnt_11).2 h
  rw [cex_mark_11] at this; cases this

/-- The trace of `cexExec` is shape-legal (Theorem 4.1), `cexζ` is a temporal backbone in it, and
the conclusion of Lemma 5.4 as stated fails, whether one keeps `j_k = i_k` or the strict
inequalities. -/
theorem lemma_5_4_as_stated_false :
    ShapeLegal (trace cexExec) (cexExec.length + 1) ∧
      TemporalBackbone (trace cexExec) cexζ cexIdx 1 ∧ cexIdx 1 < cexExec.length + 1 ∧
      ¬ BackboneConclusionLastEq (trace cexExec) cexζ cexIdx 1 ∧
      ¬ BackboneConclusionStrict (trace cexExec) cexζ cexIdx 1 ∧
      ¬ BackboneConclusionAsStated (trace cexExec) cexζ cexIdx 1 := by
  refine ⟨shapeLegal_trace cexExec_valid, cex_temporalBackbone, by decide, ?_, ?_, ?_⟩
  · rintro ⟨j, -, h1, h⟩
    have := (h 1 le_rfl).2.2.1
    rw [h1] at this
    exact cex_not_backbone this
  · rintro ⟨j, h0, hlt, h⟩
    have h2 := (h 1 le_rfl)
    have h3 := hlt 0 one_pos
    simp only [zero_add] at h3
    have : j 1 = 11 := by simp only [cexIdx] at h0 h2; omega
    have := h2.2.2.1
    rw [‹j 1 = 11›] at this
    exact cex_not_backbone this
  · rintro ⟨j, -, -, h1, h⟩
    have := (h 1 le_rfl).2.2.1
    rw [h1] at this
    exact cex_not_backbone this

/-- **Lemma 5.4 as stated is false**: there is a shape-legal trace (of the set algorithm) and a
temporal backbone in it for which no sequence `i₀ = j₀ < j₁ < … < j_k = i_k` as claimed
exists. -/
theorem lemma_5_4_false :
    ¬ ∀ (τ : ℕ → HeapState ℕ Key) (n : ℕ), ShapeLegal τ n → ∀ ζ idx k,
      TemporalBackbone τ ζ idx k → idx k < n → BackboneConclusionAsStated τ ζ idx k := by
  intro h
  obtain ⟨h1, h2, h3, -, -, h6⟩ := lemma_5_4_as_stated_false
  exact h6 (h _ _ h1 _ _ _ h2 h3)

end Podc.HindsightLinearizability
