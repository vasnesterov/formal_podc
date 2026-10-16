import Papers.PODC2015.CrashConsensusDigraph.MVC
import Papers.PODC2015.CrashConsensusDigraph.IterativeCounterexample
import Papers.PODC2015.CrashConsensusDigraph.Async
import Papers.PODC2015.CrashConsensusDigraph.WALive

/-!
# Tseng–Vaidya, *Fault-Tolerant Consensus in Directed Graphs* (PODC 2015): summary

Synchronous systems (Section 2), crash faults, static digraph `G`, at most `f` crashes:

* `theorem1` — consensus solvable ⇒ `f` CT node connectivity (`CTConn G f`, Definition 2);
* `theorem3`, `theorem2` — Algorithm Min-Max solves binary consensus under `CTConn G f`;
* `theorem4` — Algorithm MVC solves consensus for inputs in `{0, …, K}` under `CTConn G f`;
* `binary_consensus_iff`, `consensus_iff` — the tight characterizations;
* `ctConn_iff_oneReach` — `CTConn` is the 1-reach condition.

Iterative algorithms (Section 3): `theorem5` (no fixed iterative algorithm on the graph of
Appendix B, eventual-output reading) and `notMax_solvesAt` (with fixed-iteration outputs the
graph of Appendix B is *not* a counterexample for `f = 1`).

Asynchronous systems (Section 4): `theorem6` / `theorem6_gen` (necessity of the partition
condition CCA, i.e. 2-reach), `lemma1`, `theorem7` (Algorithm WA, with the reset bug of the
pseudocode fixed) and the tight characterization `async_consensus_iff`.

Non-vacuity: the graph of Appendix B satisfies `f` CT node connectivity for every `f`, so the
algorithms of Theorems 2–4 run on it (`consensus_on_pGraph`); a graph violating the condition has
no consensus algorithm (`no_consensus_disconnected`).
-/

namespace CrashConsensusDigraph

open AsyncApproxBCDirected

/-- Non-vacuity of Theorems 2–4: consensus is solvable on the graph of Appendix B. -/
theorem consensus_on_pGraph (f K : ℕ) :
    SolvesOn (pGraph f) f {x | x ≤ K} (mvc f (ftDiam (pGraph f) f) K) ∧
      Solves (pGraph f) f (minMax (V := PNode f) f (ftDiam (pGraph f) f)) :=
  ⟨theorem4 (pGraph_ctConn f) (ftDiamLE_ftDiam f), theorem3 (pGraph_ctConn f) (ftDiamLE_ftDiam f)⟩

/-- Two nodes without links. -/
def twoIsolated : Digraph (Fin 2) where
  Adj _ _ := False

/-- Non-vacuity of Theorem 1: on two isolated nodes even failure-free binary consensus is
impossible. -/
theorem no_consensus_disconnected :
    ¬ ∃ (M S : Type) (alg : Algorithm (Fin 2) Bool M S Bool), Solves twoIsolated 0 alg := by
  rw [binary_consensus_iff]
  intro h
  obtain ⟨s, -, hs⟩ := h ∅ (by simp) ⟨0, by simp⟩
  have key : ∀ v, Reaches twoIsolated ∅ s v → v = s := by
    rintro v ⟨-, hr⟩
    induction hr with
    | refl => rfl
    | tail _ e _ => exact e.1.elim
  have h0 := key 0 (hs 0 (by simp))
  have h1 := key 1 (hs 1 (by simp))
  exact absurd (h0.trans h1.symm) (by decide)

end CrashConsensusDigraph
