import Papers.PODC2011.KCoreDecomposition.Run
import Papers.PODC2011.KCoreDecomposition.WorstCase

/-!
# Execution times of the paper's examples

Combines `execTime_eq` (`execTime = stab + 1`, `Run.lean`) with the trajectory computations of
`WorstCase.lean`:

* `worstGraph_execTime` — the "worst-case" family of Fig. 3 needs exactly `N − 2` rounds for every
  `N ≥ 5`, **not** `N − 1` as claimed in §4.2;
* `pathGraph_execTime` — a chain of `N ≥ 1` nodes needs `⌈N/2⌉` rounds (as claimed in §4.2);
* `fig2_execTime` — the example of §3.1.1 (Fig. 2) needs 3 rounds (as claimed);
* `isOrder_toList` — admissible message-processing orders exist (non-vacuity of `IsOrder`).
-/

open Finset SimpleGraph

namespace KCoreDecomposition

/-- Admissible processing orders exist: e.g. the neighbours in `Finset.toList` order. -/
theorem isOrder_toList {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] : IsOrder G fun _ u => (G.neighborFinset u).toList := by
  intro n u v; simp

/-- **§4.2, Fig. 3: the claimed execution time `N − 1` is wrong; it is `N − 2`** (for every
admissible message-processing order). -/
theorem worstGraph_execTime {N : ℕ} (hN : 5 ≤ N) {order : ℕ → Fin N → List (Fin N)}
    (ho : IsOrder (worstGraph N) order) : execTime (worstGraph N) order = N - 2 := by
  have : Nonempty (Fin N) := ⟨⟨0, by omega⟩⟩
  rw [execTime_eq ho, stab_worstGraph hN]; omega

/-- The paper's claim, refuted for every `N ≥ 5`. -/
theorem worstGraph_execTime_ne {N : ℕ} (hN : 5 ≤ N) {order : ℕ → Fin N → List (Fin N)}
    (ho : IsOrder (worstGraph N) order) : execTime (worstGraph N) order ≠ N - 1 := by
  rw [worstGraph_execTime hN ho]; omega

/-- **§4.2: a linear chain of `N` nodes requires `⌈N/2⌉` rounds.** -/
theorem pathGraph_execTime {N : ℕ} (hN : 1 ≤ N) {order : ℕ → Fin N → List (Fin N)}
    (ho : IsOrder (pathGraph N) order) : execTime (pathGraph N) order = (N + 1) / 2 := by
  have : Nonempty (Fin N) := ⟨⟨0, by omega⟩⟩
  rw [execTime_eq ho, stab_pathGraph]; omega

/-- **§3.1.1, Fig. 2: the example run takes 3 rounds.** -/
theorem fig2_execTime {order : ℕ → Fin 6 → List (Fin 6)} (ho : IsOrder fig2Graph order) :
    execTime fig2Graph order = 3 := by
  rw [execTime_eq ho, stab_fig2]

end KCoreDecomposition
