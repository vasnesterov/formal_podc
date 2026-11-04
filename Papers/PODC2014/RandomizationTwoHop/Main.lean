import Papers.PODC2014.RandomizationTwoHop.Theorem1
import Papers.PODC2014.RandomizationTwoHop.Measure

/-!
# Anonymous Networks: Randomization = 2-Hop Coloring (PODC 2014) — main results

Emek, Pfister, Seidel, Wattenhofer. *Anonymous Networks: Randomization = 2-Hop Coloring.*
PODC 2014.

The main theorems with the paper's probabilistic definition of Las Vegas solvability
(`GRAN_AS`), derived from the versions for the combinatorial definition (`theorem_1`,
`theorem_2`), plus a non-vacuity check (a problem in GRAN).

Graph-theoretic results: `lemma_2`, `lemma_3`, `lemma_4` (`ViewGraph.lean`), `theorem_3`,
`corollary_1`, `corollary_2` (`Norris.lean`). Analysis of `A*`: `outPhase_eq` (Lemma 9),
`terminates` (Lemma 8), `mem_Fam` (Lemma 6), `eq_of_mem_Fam` (Lemma 7), `card_S`
(Observation 1).
-/

namespace Podc.RandomizationTwoHop

variable {In Out C : Type} [LinearOrder C]

/-- **Theorem 1** (paper's definitions): if `Π ∈ GRAN`, then `Πᶜ` is solvable by a deterministic
anonymous algorithm. -/
theorem theorem_1_AS (Pb : Problem In Out) (hP : GRAN_AS Pb) :
    ∃ A : RAlg (In × C) Out, A.IsDeterministic ∧ SolvesAS A (colored C Pb) := by
  obtain ⟨A, hdet, hA⟩ := theorem_1 (C := C) Pb hP.gran
  refine ⟨A, hdet, fun X hX P hPs hPG => ⟨?_, fun o ho => ?_⟩⟩
  · -- a deterministic algorithm terminates for all bits
    obtain ⟨β, -, t, ht⟩ := (hA X hX P hPs hPG).1 (fun _ _ => false) 0
    refine Filter.Eventually.of_forall fun β' => ⟨t, fun v => ?_⟩
    rw [RAlg.decided_det hdet (β := Function.curry β') β]; exact ht v
  · obtain ⟨β, t, h, rfl⟩ := MeasureTheory.nonempty_of_measure_ne_zero ho
    exact (hA X hX P hPs hPG).2 _ t h

/-- **Theorem 2** (paper's definitions): if `Π ∈ GRAN`, then `Πᶜ` is solvable in the infinity
model. -/
theorem theorem_2_AS [Nonempty Out] (Pb : Problem In Out) (hP : GRAN_AS Pb) :
    ∃ Ainf : Set (List (In × C)) → Out, ∀ X : LGraph (In × C), (colored C Pb).inst X →
      (colored C Pb).valid X (fun v => Ainf (⟪X⟫ v)) :=
  theorem_2 Pb hP.gran

/-! ### Non-vacuity: a problem in GRAN -/

/-- The trivial problem: every labelled graph is an instance, every output is valid. -/
def trivialProblem (In : Type) : Problem In Unit := ⟨fun _ => True, fun _ _ => True⟩

/-- An algorithm that outputs a constant in round 0. -/
def constAlg (In O : Type) (o : O) : RAlg In O :=
  ⟨Unit, Unit, fun _ _ => (), fun _ _ => (), fun _ _ _ => (), fun _ => some o⟩

theorem gran_trivialProblem (In : Type) : GRAN_AS (trivialProblem In) := by
  refine ⟨⟨constAlg In Unit (), fun X _ P _ _ => ⟨?_, fun _ _ => trivial⟩⟩,
    ⟨constAlg In Bool true, fun X _ P _ _ => ⟨?_, fun o ho => ?_⟩⟩⟩
  · exact Filter.Eventually.of_forall fun _ => ⟨0, fun _ => rfl⟩
  · exact Filter.Eventually.of_forall fun _ => ⟨0, fun _ => rfl⟩
  · obtain ⟨β, t, h, rfl⟩ := MeasureTheory.nonempty_of_measure_ne_zero ho
    refine ⟨fun _ v => ?_, fun hn => absurd trivial hn⟩
    have : ∀ t, (constAlg In Bool true).decided P X.lab (Function.curry β) t v = some true := by
      intro t; induction t with
      | zero => rfl
      | succ t ih => simp only [RAlg.decided, ih]; rfl
    simp [this]

end Podc.RandomizationTwoHop
