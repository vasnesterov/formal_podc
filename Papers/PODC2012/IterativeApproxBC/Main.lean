import Papers.PODC2012.IterativeApproxBC.Necessity
import Papers.PODC2012.IterativeApproxBC.Convergence
import Papers.PODC2012.IterativeApproxBC.Applications

/-!
# Main results of [VTL12]

N. H. Vaidya, L. Tseng, G. Liang. *Iterative Approximate Byzantine Consensus in Arbitrary
Directed Graphs.* PODC 2012 (arXiv:1201.4183).

* `alg1_run_correct` — every run of Algorithm 1, with arbitrary (even adversarial,
  time-dependent) tie-breaking, satisfies validity (1) and convergence, and all fault-free states
  converge to a common limit, if `G` satisfies the condition (Theorems 2, 3).
* `alg1_correct` — for every deterministic tie-breaking rule, Algorithm 1 is a correct iterative
  algorithm (`IterAlg.Correct`); such rules exist.
* `exists_correct_iff` — **the characterization**: an iterative approximate Byzantine consensus
  algorithm exists on `G` iff `Condition G f` (Theorems 1–3), for every finite node set.
* `alg1_complete` — non-vacuity: on the complete graph with `n > 3f` (and e.g. on `Fin 4`,
  `f = 1`), Algorithm 1 is correct.
-/

open Finset Cslib.ApproxConsensus Filter Topology

namespace IterativeApproxBC

variable {V : Type*} [Fintype V] [DecidableEq V] {G : Digraph V} {f : ℕ}

/-- **Theorems 2 and 3** of [VTL12], for Algorithm 1 with arbitrary tie-breaking: if `G`
satisfies the condition and `n ≥ 2`, every run with at most `f` Byzantine nodes satisfies
validity (1) and convergence, and the fault-free states converge to a common limit. -/
theorem alg1_run_correct (hG : Condition G f) (hn : 2 ≤ Fintype.card V) {S : Scenario V}
    (hF : #S.F ≤ f) {x : ℕ → V → ℝ} (hx : IsRun G (alg1Step G f) S x) :
    ValidStep S.F x ∧ Converges S.F x ∧
      ∃ c, ∀ i ∉ S.F, Tendsto (fun t => x t i) atTop (𝓝 c) := by
  have : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  have hv := alg1_validStep hx hF
  have hc := alg1_converges hx hF (fun hf i => hG.inDegree hn hf i) hG
  exact ⟨hv, hc, hv.exists_tendsto hc⟩

/-- Algorithm 1 with any deterministic tie-breaking rule is a correct iterative algorithm
(validity in the convex-hull form and in the per-iteration form (1), and convergence). -/
theorem alg1_correct (hG : Condition G f) (hn : 2 ≤ Fintype.card V) (tb : TieBreak G f) :
    tb.alg.Correct G f ∧ tb.alg.CorrectStep G f := by
  have h : tb.alg.CorrectStep G f := fun S hF =>
    let h := alg1_run_correct hG hn hF (tb.isRun S)
    ⟨h.1, h.2.1⟩
  exact ⟨(IterAlg.correct_iff_correctStep G f _).mpr h, h⟩

/-- Under the condition (`n ≥ 2`) Algorithm 1 is well defined: tie-breaking rules exist. -/
theorem tieBreak_nonempty (hG : Condition G f) (hn : 2 ≤ Fintype.card V) :
    Nonempty (TieBreak G f) :=
  TieBreak.nonempty fun i => hG.two_mul_le_inDegree hn i

/-- With at most one node, the identity algorithm is trivially correct (the paper assumes
`n ≥ 2`). -/
theorem id_correct (hn : Fintype.card V ≤ 1) : (⟨fun _ _ v => v⟩ : IterAlg V).Correct G f := by
  intro S _
  have hsub : ∀ i j : V, i = j := fun i j => Fintype.card_le_one_iff.mp hn i j
  have hconst : ∀ t, (⟨fun _ _ v => v⟩ : IterAlg V).run G S t = S.input := by
    intro t; induction t with
    | zero => rfl
    | succ t ih => funext i; rw [IterAlg.run_succ, ih]
  refine ⟨fun t i hi => ⟨⟨i, hi, by rw [hconst, hconst]⟩, ⟨i, hi, by rw [hconst, hconst]⟩⟩,
    fun ε hε => ⟨0, fun t _ i _ j _ => ?_⟩⟩
  rw [hsub i j, sub_self, abs_zero]; exact hε.le

/-- **The characterization of [VTL12]** (Theorems 1, 2, 3): an iterative approximate Byzantine
consensus algorithm (state = output, no sense of time, validity and convergence against up to
`f` Byzantine nodes) exists on the digraph `G` iff for every partition `F, L, C, R` of the nodes
with `|F| ≤ f` and `L, R ≠ ∅`, `C ∪ R ⇒ L` or `L ∪ C ⇒ R`. -/
theorem exists_correct_iff : (∃ A : IterAlg V, A.Correct G f) ↔ Condition G f := by
  constructor
  · rintro ⟨A, hA⟩; exact condition_of_correct A hA
  · intro hG
    by_cases hn : 2 ≤ Fintype.card V
    · obtain ⟨tb⟩ := tieBreak_nonempty hG hn
      exact ⟨tb.alg, (alg1_correct hG hn tb).1⟩
    · exact ⟨_, id_correct (by omega)⟩

/-- Same characterization with validity in the per-iteration form (1). -/
theorem exists_correctStep_iff : (∃ A : IterAlg V, A.CorrectStep G f) ↔ Condition G f := by
  simp only [← IterAlg.correct_iff_correctStep]; exact exists_correct_iff

/-- **Non-vacuity**: on the complete graph with `n > 3f`, Algorithm 1 (any tie-breaking) is a
correct iterative algorithm, and tie-breaking rules exist. -/
theorem alg1_complete (h : 3 * f < Fintype.card V) (hn : 2 ≤ Fintype.card V) :
    Nonempty (TieBreak (⊤ : Digraph V) f) ∧ ∀ tb : TieBreak (⊤ : Digraph V) f, tb.alg.Correct ⊤ f :=
  ⟨tieBreak_nonempty (condition_complete h) hn, fun tb => (alg1_correct (condition_complete h) hn tb).1⟩

/-- Concrete instance: 4 nodes, complete graph, one Byzantine fault. -/
example : ∀ tb : TieBreak (⊤ : Digraph (Fin 4)) 1, tb.alg.Correct ⊤ 1 :=
  (alg1_complete (by simp) (by simp)).2

/-- Concrete instance where the condition fails: on the complete graph with `n = 3f`, no iterative
algorithm exists (e.g. 3 nodes, 1 fault). -/
example : ¬ ∃ A : IterAlg (Fin 3), A.Correct (⊤ : Digraph (Fin 3)) 1 := by
  rw [exists_correct_iff, condition_complete_iff (by simp)]; simp

end IterativeApproxBC
