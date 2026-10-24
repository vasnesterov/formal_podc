import Papers.PODC2021.PPStateComplexity.Leaderless
import Papers.PODC2021.PPStateComplexity.Examples

/-!
# Busy beaver functions and counterexamples

* Definition 1: `BB n` (leaderless busy beaver function). Theorem 5.9 gives `BB n ≤ 2^((2n+2)!)`
  (`BB_le`), i.e. `STATE(η) ∈ Ω(log log η)`; Example 2.1 gives `2^k ≤ BB (k+1)` (`le_BB`).
* `BB_L` (protocols *with leaders*) is **under-specified**: with unboundedly many leaders,
  four states decide `x ≥ η` for every `η` (`not_bddAbove_BBLSet`). So the paper's claims
  "an upper bound on the busy beaver function `BB_L(n)`" (Section 4) and "the state complexity of
  `x ≥ η` with leaders is the inverse of a non-elementary function" (abstract, conclusion) need
  the evidently intended fixed number `ℓ` of leaders; Theorem 4.5 itself correctly depends on `ℓ`.
* With configurations read as arbitrary multisets (the paper requires `≥ 2` agents, which forces
  `b ≥ 2`), Lemmas 4.1 and 5.2 fail for `b = 0` (`lemma_4_1_b_zero_false`,
  `lemma_5_2_b_zero_false`).
-/

namespace Podc.PPStateComplexity

open Cslib Cslib.PopulationProtocol

/-- The set of thresholds `η` such that `x ≥ η` is computed by a leaderless protocol with at most
`n` states. -/
def BBSet (n : ℕ) : Set ℕ :=
  {η | ∃ (Q : Type) (_ : Fintype Q) (_ : DecidableEq Q) (P : Protocol Q),
    Fintype.card Q ≤ n ∧ P.Leaderless ∧ P.ComputesGe η}

/-- The same set for protocols possibly with leaders (any number of them). -/
def BBLSet (n : ℕ) : Set ℕ :=
  {η | ∃ (Q : Type) (_ : Fintype Q) (_ : DecidableEq Q) (P : Protocol Q),
    Fintype.card Q ≤ n ∧ P.ComputesGe η}

/-- **Definition 1.** The busy beaver function: the largest `η` such that `x ≥ η` is computed by a
leaderless protocol with at most `n` states. -/
noncomputable def BB (n : ℕ) : ℕ := sSup (BBSet n)

/-- Every element of `BBSet n` is at most `2^((2n+2)!)` (Theorem 5.9). -/
theorem mem_BBSet_le {n η : ℕ} (h : η ∈ BBSet n) : η ≤ 2 ^ (2 * n + 2).factorial := by
  obtain ⟨Q, _, _, P, hcard, hL, hP⟩ := h
  exact (Protocol.theorem_5_9 hP hL).trans
    (Nat.pow_le_pow_right (by omega) (Nat.factorial_le (by omega)))

/-- **Theorem 5.9, busy beaver form:** `BB(n) ≤ 2^((2n+2)!)`. -/
theorem BB_le (n : ℕ) : BB n ≤ 2 ^ (2 * n + 2).factorial := by
  rcases (BBSet n).eq_empty_or_nonempty with h | h
  · simp [BB, h]
  · exact csSup_le h fun _ hη => mem_BBSet_le hη

theorem bddAbove_BBSet (n : ℕ) : BddAbove (BBSet n) := ⟨_, fun _ hη => mem_BBSet_le hη⟩

/-- `BB` is attained: `x ≥ BB(n)` is computed by some leaderless protocol with `≤ n` states
(when some protocol exists). -/
theorem BB_mem {n : ℕ} (h : (BBSet n).Nonempty) : BB n ∈ BBSet n :=
  Nat.sSup_mem h (bddAbove_BBSet n)

/-- Example 2.1 as a lower bound: `2^k ≤ BB(k + 2)`. -/
theorem le_BB (k : ℕ) : 2 ^ k ≤ BB (k + 2) :=
  le_csSup (bddAbove_BBSet _)
    ⟨_, inferInstance, inferInstance, exampleP' k, by simp, exampleP'_leaderless k,
      exampleP'_computesGe k⟩

/-- **`BB_L` needs a bound on the number of leaders.** For every `η`, the threshold `x ≥ η` is
computed by a protocol with 4 states and `η` leaders, so the thresholds computable with `≤ 4`
states (and leaders) are unbounded. -/
theorem not_bddAbove_BBLSet : ¬ BddAbove (BBLSet 4) := by
  rintro ⟨M, hM⟩
  have := hM ⟨St4, inferInstance, inferInstance, majority4 (M + 1), by decide,
    majority4_computesGe (M + 1)⟩
  omega

namespace Protocol

variable {Q : Type*} [DecidableEq Q] [Fintype Q] {P : Protocol Q} {η : ℕ}

/-- For a protocol computing `x ≥ η` with `η > 2`, the hypotheses of Lemma 4.1 hold with `b = 0`
while its conclusion `η ≤ a` fails. -/
theorem exists_lemma_4_1_b_zero (h : P.ComputesGe η) (hη : 2 < η) :
    ∃ (a b : ℕ) (B Da Db : Multiset Q) (S : Finset Q), IsBasisElem P.SC B S ∧
      (∀ q ∈ Da, q ∈ S) ∧ (∀ q ∈ Db, q ∈ S) ∧ 2 ≤ a ∧ b = 0 ∧
      P.Reach (P.IC a) (B + Da) ∧ P.Reach (Multiset.replicate b P.x) Db ∧ ¬ η ≤ a := by
  obtain ⟨C, hC, hst⟩ := computesGe_iff.1 h 2 le_rfl _ .refl
  refine ⟨2, 0, C, 0, 0, ∅, fun D hD => ?_, by simp, by simp, le_rfl, rfl, by simpa using hC,
    by simpa using (Relation.ReflTransGen.refl : P.Reach 0 0), by omega⟩
  have : D = 0 := Multiset.eq_zero_of_forall_notMem fun q hq => by simpa using hD q hq
  subst this
  rw [add_zero]
  cases hd : decide (η ≤ 2)
  · exact .inl (hd ▸ hst)
  · exact .inr (hd ▸ hst)

/-- For a leaderless protocol computing `x ≥ η` with `η > 2`, the hypotheses of Lemma 5.2 hold
with `b = 0` (and `π = 0`) while its conclusion `η ≤ a` fails. -/
theorem exists_lemma_5_2_b_zero (h : P.ComputesGe η) (hL : P.Leaderless) (hη : 2 < η) :
    ∃ (a b : ℕ) (B Da Db D : Multiset Q) (S : Finset Q) (π : Transition Q → ℕ),
      IsBasisElem P.SC B S ∧ (∀ q ∈ Da, q ∈ S) ∧ (∀ q ∈ Db, q ∈ S) ∧ 2 ≤ a ∧ b = 0 ∧
      P.Reach (P.IC a) D ∧ P.Reach D (B + Da) ∧ FlowEq (P.IC b) Db π ∧
      (∀ t, π t ≠ 0 → t ∈ P.T) ∧ (∀ t, π t ≠ 0 → ∀ q ∈ t.pre, 2 * ∑ t, π t ≤ D.count q) ∧
      ¬ η ≤ a := by
  obtain ⟨a, b, B, Da, Db, S, hB, hDa, hDb, ha, hb, h1, -, hlt⟩ := exists_lemma_4_1_b_zero h hη
  refine ⟨a, 0, B, Da, 0, B + Da, S, 0, hB, hDa, by simp, ha, rfl, h1, .refl,
    fun q => by simp [IC_leaderless hL], by simp, by simp, hlt⟩

end Protocol

/-- **Lemma 4.1 (configurations read as arbitrary multisets) is false for `b = 0`**: with the
4-state protocol deciding `x ≥ 3` (three leaders) all hypotheses hold for `a = 2`, `b = 0`, but
`η = 3 > a`. -/
theorem lemma_4_1_b_zero_false :
    ∃ (a b : ℕ) (B Da Db : Multiset St4) (S : Finset St4),
      IsBasisElem (majority4 3).SC B S ∧ (∀ q ∈ Da, q ∈ S) ∧ (∀ q ∈ Db, q ∈ S) ∧ 2 ≤ a ∧
      b = 0 ∧ (majority4 3).Reach ((majority4 3).IC a) (B + Da) ∧
      (majority4 3).Reach (Multiset.replicate b (majority4 3).x) Db ∧ ¬ 3 ≤ a :=
  Protocol.exists_lemma_4_1_b_zero (majority4_computesGe 3) (by norm_num)

/-- **Lemma 5.2 (configurations read as arbitrary multisets) is false for `b = 0`**:
Example 2.1 with `k = 2` (leaderless, `x ≥ 4`). -/
theorem lemma_5_2_b_zero_false :
    ∃ (a b : ℕ) (B Da Db D : Multiset (Option (Fin 3))) (S : Finset (Option (Fin 3)))
      (π : Transition (Option (Fin 3)) → ℕ),
      IsBasisElem (exampleP' 2).SC B S ∧ (∀ q ∈ Da, q ∈ S) ∧ (∀ q ∈ Db, q ∈ S) ∧ 2 ≤ a ∧
      b = 0 ∧ (exampleP' 2).Reach ((exampleP' 2).IC a) D ∧ (exampleP' 2).Reach D (B + Da) ∧
      FlowEq ((exampleP' 2).IC b) Db π ∧ (∀ t, π t ≠ 0 → t ∈ (exampleP' 2).T) ∧
      (∀ t, π t ≠ 0 → ∀ q ∈ t.pre, 2 * ∑ t, π t ≤ D.count q) ∧ ¬ 2 ^ 2 ≤ a :=
  Protocol.exists_lemma_5_2_b_zero (exampleP'_computesGe 2) (exampleP'_leaderless 2)
    (by norm_num)

end Podc.PPStateComplexity
