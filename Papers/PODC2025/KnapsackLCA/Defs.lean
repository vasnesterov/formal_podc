import Mathlib
import Podc.Computability.QueryComplexity.QueryTree

/-!
# Knapsack instances and Local Computation Algorithms (Section 2)

Canonne, Li, Umboh. *Local Computation Algorithms for Knapsack: impossibility results, and how
to avoid them.* PODC 2025 (arXiv 2504.01543v1).

* `Instance n`: a Knapsack instance on `n` items with real profits, natural-number weights
  (Definition 2.2 requires integer weights) and a weight limit `cap`.
* `Instance.Feasible`, `IsOptimal`, `IsApprox α` (Definition 2.1 with `β = 0`),
  `IsMaximalFeasible`.
* `Instance.WellFormed` (non-negative profits, every weight at most `cap`) and
  `Instance.Normalized` (additionally total profit `1`), the standing assumptions of
  Definition 2.2.
* `LCA n Ω`: a randomized LCA: a distribution `seed` on random seeds and, for every weight limit
  `K`, seed `r` and query `i`, an adaptive query tree over the item oracle `Fin n → ℝ × ℕ` that
  outputs the yes/no answer. Statelessness, parallelizability and query-order obliviousness
  (Definitions 2.2–2.4) hold by construction: the answer is a function of `(I, r, i)` only.
* `LCA.QueryBound A q`: every answer is computed with at most `q` queries to the instance (the
  paper's `t(n)`, measured as query complexity, footnote 1).
* `LCA.Correct A 𝓘 Valid δ`: the *per-query* reading of Definition 2.2: for every instance of
  the class `𝓘` there is a seed-dependent solution `C r` such that, for every query `i`, with
  probability `≥ 1 - δ` the solution is valid and the answer to `i` agrees with it.
  `LCA.CorrectStrong`: the *global* reading: with probability `≥ 1 - δ` the set of items
  answered "yes" is valid. The global reading implies the per-query one
  (`LCA.CorrectStrong.correct`), so lower bounds against `Correct` are the strongest.
-/

namespace Podc.KnapsackLCA

open Cslib Cslib.Probability.PMF

/-- A Knapsack instance on `n` items: item `i` has profit `(item i).1` and integer weight
`(item i).2`; `cap` is the weight limit `K`. -/
structure Instance (n : ℕ) where
  /-- Profit and weight of every item (the oracle an LCA queries). -/
  item : Fin n → ℝ × ℕ
  /-- The weight limit `K`. -/
  cap : ℕ

namespace Instance

variable {n : ℕ} (I : Instance n)

/-- Profit of item `i`. -/
def profit (i : Fin n) : ℝ := (I.item i).1

/-- Weight of item `i`. -/
def weight (i : Fin n) : ℕ := (I.item i).2

/-- Total profit of a set of items. -/
def value (C : Finset (Fin n)) : ℝ := ∑ i ∈ C, I.profit i

/-- Total weight of a set of items. -/
def load (C : Finset (Fin n)) : ℕ := ∑ i ∈ C, I.weight i

/-- `C` respects the weight limit. -/
def Feasible (C : Finset (Fin n)) : Prop := I.load C ≤ I.cap

/-- `C` is an optimal solution. -/
def IsOptimal (C : Finset (Fin n)) : Prop :=
  I.Feasible C ∧ ∀ C', I.Feasible C' → I.value C' ≤ I.value C

/-- `C` is an `α`-approximate solution (Definition 2.1 with additive error `0`). -/
def IsApprox (α : ℝ) (C : Finset (Fin n)) : Prop :=
  I.Feasible C ∧ ∀ C', I.Feasible C' → α * I.value C' ≤ I.value C

/-- `C` is a maximal feasible solution: feasible, and no further item can be added. -/
def IsMaximalFeasible (C : Finset (Fin n)) : Prop :=
  I.Feasible C ∧ ∀ i ∉ C, ¬ I.Feasible (insert i C)

/-- Standing assumptions of Definition 2.2 without the normalisation of the profits:
non-negative profits and every weight at most the weight limit. -/
def WellFormed : Prop := (∀ i, 0 ≤ I.profit i) ∧ ∀ i, I.weight i ≤ I.cap

/-- All assumptions of Definition 2.2: well-formed, and the total profit is normalised to `1`. -/
def Normalized : Prop := I.WellFormed ∧ ∑ i, I.profit i = 1

theorem IsOptimal.isApprox_one {C : Finset (Fin n)} (h : I.IsOptimal C) : I.IsApprox 1 C :=
  ⟨h.1, fun C' hC' => by simpa using h.2 C' hC'⟩

end Instance

/-- A randomized Local Computation Algorithm for Knapsack on `n` items with seeds in `Ω`. -/
structure LCA (n : ℕ) (Ω : Type*) where
  /-- Distribution of the read-only random seed `r`. -/
  seed : PMF Ω
  /-- For weight limit `K`, seed `r` and query `i`: the query tree computing the answer. -/
  run : ℕ → Ω → Fin n → QueryTree (Fin n) (ℝ × ℕ) Bool

namespace LCA

variable {n : ℕ} {Ω : Type*} (A : LCA n Ω)

/-- The answer of `A` on instance `I`, seed `r`, query `i`: is item `i` in the solution? -/
def answer (I : Instance n) (r : Ω) (i : Fin n) : Bool := (A.run I.cap r i).eval I.item

/-- The solution `A` gives access to on instance `I` with seed `r`. -/
def solution (I : Instance n) (r : Ω) : Finset (Fin n) :=
  Finset.univ.filter fun i => A.answer I r i = true

/-- Every answer is computed with at most `q` queries to the instance. -/
def QueryBound (q : ℕ) : Prop := ∀ K r i f, (A.run K r i).cost f ≤ q

/-- Per-query correctness with failure probability `δ` on the instance class `𝓘`
(Definition 2.2): a seed-dependent solution `C r` exists such that every single query is
answered consistently with `C r`, and `C r` is valid, with probability `≥ 1 - δ`. -/
def Correct (𝓘 : Set (Instance n)) (Valid : Instance n → Finset (Fin n) → Prop) (δ : ℝ) :
    Prop :=
  ∀ I ∈ 𝓘, ∃ C : Ω → Finset (Fin n), ∀ i,
    1 - δ ≤ probReal A.seed {r | Valid I (C r) ∧ (A.answer I r i = true ↔ i ∈ C r)}

/-- Global correctness: with probability `≥ 1 - δ` the whole answered solution is valid. -/
def CorrectStrong (𝓘 : Set (Instance n)) (Valid : Instance n → Finset (Fin n) → Prop)
    (δ : ℝ) : Prop :=
  ∀ I ∈ 𝓘, 1 - δ ≤ probReal A.seed {r | Valid I (A.solution I r)}

theorem CorrectStrong.correct {𝓘 : Set (Instance n)} {Valid : Instance n → Finset (Fin n) → Prop}
    {δ : ℝ} (h : A.CorrectStrong 𝓘 Valid δ) : A.Correct 𝓘 Valid δ := by
  intro I hI
  refine ⟨A.solution I, fun i => (h I hI).trans (probReal_mono _ fun r hr => ⟨hr, ?_⟩)⟩
  simp [solution]

end LCA

/-! ### Non-vacuity: the read-everything LCA -/

namespace LCA

/-- The deterministic LCA that reads all `n` items and answers according to a fixed valid
solution (chosen by `sol`). -/
noncomputable def readAll {n : ℕ} (sol : Instance n → Finset (Fin n)) : LCA n Unit where
  seed := PMF.pure ()
  run K _ i := QueryTree.ofFun (List.finRange n) fun f => decide (i ∈ sol ⟨f, K⟩)

theorem readAll_queryBound {n : ℕ} (sol : Instance n → Finset (Fin n)) :
    (readAll sol).QueryBound n := fun K r i f => by
  simp [readAll, QueryTree.cost_ofFun_finRange]

/-- If `sol I` is always valid, the read-everything LCA is correct with failure probability
`0` on all instances (globally, hence also per query). So the hypotheses of the lower bounds
are satisfiable with `q = n`, and the lower bounds are tight up to constants. -/
theorem readAll_correctStrong {n : ℕ} (Valid : Instance n → Finset (Fin n) → Prop)
    (sol : Instance n → Finset (Fin n)) (hsol : ∀ I, Valid I (sol I)) (𝓘 : Set (Instance n)) :
    (readAll sol).CorrectStrong 𝓘 Valid 0 := by
  intro I _
  have hsolI : (readAll sol).solution I () = sol I := by
    ext i
    simp [solution, answer, readAll, QueryTree.eval_ofFun_finRange]
  have : {r : Unit | Valid I ((readAll sol).solution I r)} = Set.univ := by
    ext r; cases r; simp [hsolI, hsol I]
  rw [this]
  simp [probReal, readAll]

end LCA

namespace Instance

variable {n : ℕ} (I : Instance n)

theorem exists_isOptimal : ∃ C, I.IsOptimal C := by
  classical
  obtain ⟨C, hC, hmax⟩ := Finset.exists_max_image (Finset.univ.filter I.Feasible) I.value
    ⟨∅, by simp [Instance.Feasible, Instance.load]⟩
  exact ⟨C, (Finset.mem_filter.1 hC).2, fun C' hC' =>
    hmax C' (Finset.mem_filter.2 ⟨Finset.mem_univ _, hC'⟩)⟩

theorem exists_isMaximalFeasible : ∃ C, I.IsMaximalFeasible C := by
  classical
  obtain ⟨C, hC, hmax⟩ := Finset.exists_max_image (Finset.univ.filter I.Feasible) Finset.card
    ⟨∅, by simp [Instance.Feasible, Instance.load]⟩
  refine ⟨C, (Finset.mem_filter.1 hC).2, fun i hi hfeas => ?_⟩
  have := hmax _ (Finset.mem_filter.2 ⟨Finset.mem_univ _, hfeas⟩)
  rw [Finset.card_insert_of_notMem hi] at this
  omega

end Instance

/-- Non-vacuity of Theorems 3.2–3.4: an LCA with `n` queries giving access to an optimal
solution with failure probability `0` exists. -/
theorem exists_lca_optimal (n : ℕ) :
    ∃ A : LCA n Unit, A.QueryBound n ∧
      A.CorrectStrong Set.univ (fun I C => I.IsOptimal C) 0 :=
  ⟨_, LCA.readAll_queryBound _, LCA.readAll_correctStrong _ _
    (fun I => I.exists_isOptimal.choose_spec) _⟩

/-- Non-vacuity of Theorem 3.4: an LCA with `n` queries giving access to a maximal feasible
solution with failure probability `0` exists. -/
theorem exists_lca_maximalFeasible (n : ℕ) :
    ∃ A : LCA n Unit, A.QueryBound n ∧
      A.CorrectStrong Set.univ (fun I C => I.IsMaximalFeasible C) 0 :=
  ⟨_, LCA.readAll_queryBound _, LCA.readAll_correctStrong _ _
    (fun I => I.exists_isMaximalFeasible.choose_spec) _⟩

end Podc.KnapsackLCA
