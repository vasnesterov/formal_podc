import Papers.PODC2013.ByzantineVectorConsensus.Spec
import Cslib.Computability.Distributed.Byzantine.PartialSync.Map

/-!
# Theorem 3: exact BVC in synchrony for `n ≥ max(3t + 1, (d + 1) t + 1)`

The paper's algorithm: (1) every process Byzantine-broadcasts its input, so that all correct
processes obtain the same multiset `S` of `n` vectors, containing the true input of every correct
process; (2) every process decides a deterministically chosen point of `Γ(S)`.

Step (1) is *interactive consistency* (IC), which CSLib provides for `n > 3t` in the synchronous
model (`icSolvableSync_of_three_t_lt`, Pease–Shostak–Lamport; implemented there by an exchange
round followed by vector consensus rather than by `n` parallel Byzantine broadcasts — the
specification is the same). `withGamma A` post-processes the decided vector `S` with `gammaPt`
(the decision post-processing `Algorithm.mapDecide` of `Cslib.Computability.Distributed.Byzantine.PartialSync.Map`).
-/

open Cslib.Byzantine.PartialSync Finset Module

namespace ByzantineVectorConsensus

set_option linter.unusedSectionVars false

variable {P M S VI : Type*} [Fintype P] [DecidableEq P] {d t δ : ℕ}

/-- Step 2 of the exact BVC algorithm on top of an interactive-consistency algorithm `A`: decide
the chosen point `gammaPt t univ S` of `Γ(S)` when `A` decides the vector `S`. -/
noncomputable abbrev withGamma (t : ℕ) (A : Algorithm P M S VI (P → Vec d)) :
    Algorithm P M S VI (Vec d) :=
  A.mapDecide (gammaPt t univ)

/-- Correctness of the exact BVC algorithm (proof of **Theorem 3**): an interactive-consistency
algorithm followed by the choice of a point of `Γ` solves exact BVC in synchrony when
`n ≥ (d + 1) t + 1`. -/
theorem withGamma_solves {A : Algorithm P M S (Vec d) (P → Vec d)}
    (hA : SolvesConsensusSync t δ A (icValidity P (Vec d)))
    (hn : (d + 1) * t < Fintype.card P) :
    SolvesConsensusSync t δ (withGamma t A) (bvcValidity P d) := by
  refine hA.mapDecide fun c hc V hV => ?_
  -- the entries of the processes of `π(c)` are their inputs
  set T := c.procs
  have hT : Fintype.card P - t ≤ T.card := hc
  have hmem : gammaPt t univ V ∈ GammaOn t univ V :=
    gammaPt_mem V (by rw [finrank_fin_fun, card_univ]; exact hn)
  have := GammaOn_subset_convexHull (subset_univ T) (by rwa [card_univ]) hmem
  refine convexHull_mono ?_ this
  rintro _ ⟨q, hq, rfl⟩
  have hq' : c q ≠ none := Config.mem_procs_iff_ne_none.mp hq
  exact ⟨q, hV q hq'⟩

/-- **Theorem 3** of the paper: exact BVC is solvable in a synchronous system (without
signatures) if `n ≥ max(3t + 1, (d + 1) t + 1)`. -/
theorem theorem_3 {P : Type} [Fintype P] [DecidableEq P] (h3 : 3 * t < Fintype.card P)
    (hn : (d + 1) * t < Fintype.card P) : (bvcValidity P d).SolvableSync t δ := by
  obtain ⟨M, S, A, hA⟩ := icSolvableSync_of_three_t_lt (P := P) (VI := Vec d) (δ := δ) h3
  exact ⟨M, S, withGamma t A, withGamma_solves hA hn⟩

end ByzantineVectorConsensus
