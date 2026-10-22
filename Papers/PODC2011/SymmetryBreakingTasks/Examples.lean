import Papers.PODC2011.SymmetryBreakingTasks.Structure

/-!
# The examples of Section 4: anchoring of `⟨20, 4, -, -⟩` tasks and Table 1

* `anchoring_examples` — the four `⟨20, 4, -, -⟩` examples of Section 4.2;
* `table_1` — every entry of Table 1 (kernel sets of the `⟨6, 3, ℓ, u⟩` tasks, `u ≤ 6`, and the
  "canonical" column) is correct;
* `table_1_missing_row` — but the table is not complete: the feasible task `⟨6, 3, 2, 6⟩` is
  missing (it is a synonym of `⟨6, 3, 2, 2⟩`);
* `synonyms_6_3` — the synonym classes listed in the text;
* `incomparable_6_3` — `⟨6, 3, 1, 4⟩` and `⟨6, 3, 0, 3⟩` are incomparable;
* `canonical_not_unique` — Definition of the canonical representative (Section 4.2): when
  `u > n`, two different synonymous tasks are both `(ℓ, u)`-anchored, hence both "their own
  representative"; Theorem 7's `f` picks `⟨4, 2, 0, 4⟩`.
-/

namespace Podc.SymmetryBreakingTasks

/-- Section 4.2: `⟨20,4,4,8⟩` is `ℓ`-anchored, `⟨20,4,2,6⟩` is `u`-anchored, `⟨20,4,5,5⟩` is
`(ℓ,u)`-anchored and `⟨20,4,4,6⟩` is neither. -/
theorem anchoring_examples :
    LAnchored 20 4 4 8 ∧ UAnchored 20 4 2 6 ∧ (LAnchored 20 4 5 5 ∧ UAnchored 20 4 5 5) ∧
      ¬ LAnchored 20 4 4 6 ∧ ¬ UAnchored 20 4 4 6 := by
  refine ⟨(theorem_3 ⟨by norm_num, by norm_num⟩).2 (by norm_num),
    (theorem_4 (by norm_num) ⟨by norm_num, by norm_num⟩).2 (by norm_num),
    ⟨(theorem_3 ⟨by norm_num, by norm_num⟩).2 (by norm_num),
      (theorem_4 (by norm_num) ⟨by norm_num, by norm_num⟩).2 (by norm_num)⟩, ?_, ?_⟩
  · rw [theorem_3 ⟨by norm_num, by norm_num⟩]; norm_num
  · rw [theorem_4 (by norm_num) ⟨by norm_num, by norm_num⟩]; norm_num

/-- The seven columns of Table 1: all non-increasing vectors of 3 naturals adding up to 6. -/
def kernels63 : Fin 7 → Fin 3 → ℕ :=
  ![![6, 0, 0], ![5, 1, 0], ![4, 2, 0], ![4, 1, 1], ![3, 3, 0], ![3, 2, 1], ![2, 2, 2]]

lemma kernels63_complete :
    ∀ a b c : Fin 7, (a : ℕ) + b + c = 6 → c ≤ b → b ≤ a →
      ∃ j, kernels63 j = ![(a : ℕ), b, c] := by
  decide +kernel

lemma kernels63_sound : ∀ j, ∑ v, kernels63 j v = 6 ∧ ∀ v w : Fin 3, v ≤ w →
    kernels63 j w ≤ kernels63 j v := by
  decide +kernel

/-- The kernel sets of all `⟨6, 3, ℓ, u⟩`-GSB tasks: the columns of Table 1 within the bounds. -/
theorem kernelSet_6_3 (ℓ u : ℕ) :
    kernelSet 6 3 ℓ u = {K | K ∈ Set.range kernels63 ∧ ∀ v, ℓ ≤ K v ∧ K v ≤ u} := by
  ext K
  rw [mem_kernelSet]
  constructor
  · rintro ⟨⟨hs, hb⟩, ha⟩
    refine ⟨?_, hb⟩
    rw [Fin.sum_univ_three] at hs
    have h01 := ha (show (0 : Fin 3) ≤ 1 by decide)
    have h12 := ha (show (1 : Fin 3) ≤ 2 by decide)
    obtain ⟨j, hj⟩ := kernels63_complete ⟨K 0, by omega⟩ ⟨K 1, by omega⟩ ⟨K 2, by omega⟩
      (by simpa using hs) (by simpa using h12) (by simpa using h01)
    refine ⟨j, ?_⟩
    rw [hj]; ext v; fin_cases v <;> rfl
  · rintro ⟨⟨j, rfl⟩, hb⟩
    exact ⟨⟨(kernels63_sound j).1, hb⟩, fun v w h => (kernels63_sound j).2 v w h⟩

/-- Table 1 as printed: rows `(ℓ, u, canonical?, membership of the seven kernel vectors)`. -/
def table1 : List (ℕ × ℕ × Bool × List Bool) :=
  [ (0, 6, true,  [true,  true,  true,  true,  true,  true,  true ]),
    (1, 6, false, [false, false, false, true,  false, true,  true ]),
    (0, 5, true,  [false, true,  true,  true,  true,  true,  true ]),
    (1, 5, false, [false, false, false, true,  false, true,  true ]),
    (2, 5, false, [false, false, false, false, false, false, true ]),
    (0, 4, true,  [false, false, true,  true,  true,  true,  true ]),
    (1, 4, true,  [false, false, false, true,  false, true,  true ]),
    (2, 4, false, [false, false, false, false, false, false, true ]),
    (0, 3, true,  [false, false, false, false, true,  true,  true ]),
    (1, 3, true,  [false, false, false, false, false, true,  true ]),
    (2, 3, false, [false, false, false, false, false, false, true ]),
    (0, 2, false, [false, false, false, false, false, false, true ]),
    (1, 2, false, [false, false, false, false, false, false, true ]),
    (2, 2, true,  [false, false, false, false, false, false, true ]) ]

/-- Table 1 is correct: each row lists exactly the kernel vectors of its task, and the rows marked
"canonical" are exactly the fixed points of Theorem 7's `f`. -/
theorem table_1 : ∀ r ∈ table1,
    Feasible 6 3 r.1 r.2.1 ∧ (canon 6 3 r.1 r.2.1 = (r.1, r.2.1) ↔ r.2.2.1 = true) ∧
    ∀ j : Fin 7, (kernels63 j ∈ kernelSet 6 3 r.1 r.2.1 ↔ r.2.2.2.getD j false = true) := by
  simp only [kernelSet_6_3, Set.mem_ofPred_eq, Set.mem_range_self, true_and, Feasible]
  decide +kernel

/-- Table 1 claims to list all feasible `⟨6, 3, ℓ, u⟩` tasks with `u ≤ 6`, but `⟨6, 3, 2, 6⟩` is
missing (a synonym of `⟨6, 3, 2, 2⟩`, kernel set `{[2, 2, 2]}`). -/
theorem table_1_missing_row :
    Feasible 6 3 2 6 ∧ (∀ r ∈ table1, (r.1, r.2.1) ≠ (2, 6)) ∧ sgsb 6 3 2 6 = sgsb 6 3 2 2 ∧
      (∀ ℓ u, Feasible 6 3 ℓ u → u ≤ 6 →
        (ℓ, u) = (2, 6) ∨ ∃ r ∈ table1, (r.1, r.2.1) = (ℓ, u)) := by
  refine ⟨⟨by norm_num, by norm_num⟩, by decide, ?_, ?_⟩
  · exact (theorem_7_iff (by norm_num) ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩).2
      (by decide)
  · rintro ℓ u ⟨h1, h2⟩ hu
    have : ℓ ≤ 2 := by omega
    interval_cases ℓ <;> interval_cases u <;> simp_all [table1]

/-- The synonym classes stated in Section 4.1. -/
theorem synonyms_6_3 :
    (sgsb 6 3 2 5 = sgsb 6 3 2 2 ∧ sgsb 6 3 2 4 = sgsb 6 3 2 2 ∧ sgsb 6 3 2 3 = sgsb 6 3 2 2 ∧
      sgsb 6 3 0 2 = sgsb 6 3 2 2 ∧ sgsb 6 3 1 2 = sgsb 6 3 2 2) ∧
    (sgsb 6 3 1 6 = sgsb 6 3 1 4 ∧ sgsb 6 3 1 5 = sgsb 6 3 1 4) := by
  have F : ∀ ℓ u, 3 * ℓ ≤ 6 → 6 ≤ 3 * u → Feasible 6 3 ℓ u := fun _ _ h1 h2 => ⟨h1, h2⟩
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩ <;>
    exact (theorem_7_iff (by norm_num) (F _ _ (by norm_num) (by norm_num))
      (F _ _ (by norm_num) (by norm_num))).2 (by decide)

/-- Section 4.1: `⟨6, 3, 1, 4⟩` and `⟨6, 3, 0, 3⟩` are not included one in the other. -/
theorem incomparable_6_3 :
    ¬ sgsb 6 3 1 4 ⊆ sgsb 6 3 0 3 ∧ ¬ sgsb 6 3 0 3 ⊆ sgsb 6 3 1 4 := by
  constructor
  · intro h
    have := h (show ![0, 0, 0, 0, 1, 2] ∈ sgsb 6 3 1 4 by rw [mem_sgsb]; decide)
    rw [mem_sgsb] at this; revert this; decide
  · intro h
    have := h (show ![0, 0, 0, 1, 1, 1] ∈ sgsb 6 3 0 3 by rw [mem_sgsb]; decide)
    rw [mem_sgsb] at this; revert this; decide

/-- The paper's definition of the canonical representative ("an `(ℓ, u)`-anchored task is its own
representative") does not pick a unique representative when `u > n`: `⟨4, 2, 0, 5⟩` and
`⟨4, 2, 0, 4⟩` are synonyms and both `(ℓ, u)`-anchored. Theorem 7's `f` picks `⟨4, 2, 0, 4⟩`. -/
theorem canonical_not_unique :
    sgsb 4 2 0 5 = sgsb 4 2 0 4 ∧ (LAnchored 4 2 0 5 ∧ UAnchored 4 2 0 5) ∧
      (LAnchored 4 2 0 4 ∧ UAnchored 4 2 0 4) ∧ canon 4 2 0 5 = (0, 4) := by
  refine ⟨(theorem_7_iff (by norm_num) ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩).2
    (by decide), ⟨(theorem_3 ⟨by norm_num, by norm_num⟩).2 (by norm_num), rfl⟩,
    ⟨(theorem_3 ⟨by norm_num, by norm_num⟩).2 (by norm_num), rfl⟩, by decide⟩

end Podc.SymmetryBreakingTasks
