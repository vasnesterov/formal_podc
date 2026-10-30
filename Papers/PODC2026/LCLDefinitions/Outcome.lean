import Papers.PODC2026.LCLDefinitions.REFormalism

/-!
# Outcomes and the transfer of success probability (Lemmas 4.4, 4.5, 5.6, 5.7, 6.5, 6.6)

Formalization support for *"It does not matter how you define locally checkable labelings"*
(Cruciani, Das, Raevskaya, Suomela; PODC 2026, arXiv 2602.18188).

An *outcome* on a fixed instance is a probability distribution over output labellings
(`{(σ^{out,i}, p_i)}_{i ∈ I}` in the paper); we model it as a `PMF` on the type of labellings
(the pushforward of the paper's indexed family). It *solves* a problem with probability at least
`q` if the probability of the set of legal labellings is at least `q`.

Lemmas 4.4, 4.5, 5.6, 5.7, 6.5 and 6.6 of the paper all have the same proof: if a map (the
"lift") sends legal labellings for one problem to legal labellings for the other, then the
pushforward of an outcome solving the first problem with probability `≥ q` solves the second with
probability `≥ q`. This is `SolvesWithProb.map`. We instantiate it for Lemmas 6.5 and 6.6 with the
lifts of Lemmas 6.3 and 6.4. The locality (non-signaling / dependency radius) of the outcomes is
not modelled here.
-/

namespace Podc.LCLDefinitions

-- CSLib candidate (PN-views / outcome transfer are reusable beyond this paper)

open scoped ENNReal

universe u w

/-- An outcome `O` (a probability distribution over labellings) solves the problem whose legal
labellings are `legal` with probability at least `q`. -/
def SolvesWithProb {α : Type*} (O : PMF α) (legal : Set α) (q : ℝ≥0∞) : Prop :=
  q ≤ O.toOuterMeasure legal

/-- **Probability transfer** (the common argument of Lemmas 4.4, 4.5, 5.6, 5.7, 6.5, 6.6): if the
lift `f` maps legal labellings for `A` to legal labellings for `B` ("the lift is sound"), and the
outcome `O` solves `A` with probability at least `q`, then the outcome obtained by sampling from
`O` and applying the lift solves `B` with probability at least `q`. -/
theorem SolvesWithProb.map {α β : Type*} {O : PMF α} {A : Set α} {B : Set β} {q : ℝ≥0∞}
    (hO : SolvesWithProb O A q) (f : α → β) (hf : ∀ x ∈ A, f x ∈ B) :
    SolvesWithProb (O.map f) B q := by
  unfold SolvesWithProb at *
  rw [PMF.toOuterMeasure_map_apply]
  exact hO.trans (O.toOuterMeasure.mono fun x hx => hf x hx)

section Section6

variable {V : Type w} [DecidableEq V] {G : SimpleGraph V} [G.LocallyFinite]
  {Sig : Type u} {r : ℕ} {C : Set (View Sig (r + 1))}

/-- **Lemma 6.5.** If an outcome `O_E` solves the RE problem `E` (Definition 6.1) on `G` with
probability at least `q`, then sampling from `O_E` and applying the lift `E → D` of Lemma 6.3
gives an outcome that solves the PN-checkable problem `D` on `G` with probability at least `q`. -/
theorem lemma_6_5 {O : PMF (V → V → View Sig (r + 1) × Fin 3)} {q : ℝ≥0∞}
    (hO : SolvesWithProb O {lam | (problemE C).Valid G lam} q) :
    SolvesWithProb (O.map (liftED G)) {σ | PNValid G C σ} q :=
  hO.map _ fun _ h => liftED_valid h

/-- **Lemma 6.6.** On a 3-regular graph `G`, if an outcome `O_D` solves the PN-checkable problem
`D` with probability at least `q`, then sampling from `O_D` and applying the lift `D → E` of
Lemma 6.4 gives an outcome that solves the RE problem `E` with probability at least `q`. -/
theorem lemma_6_6 (hG : ∀ v, G.degree v = 3) {O : PMF (V → Sig)} {q : ℝ≥0∞}
    (hO : SolvesWithProb O {σ | PNValid G C σ} q) :
    SolvesWithProb (O.map fun σ => liftDE G σ r) {lam | (problemE C).Valid G lam} q :=
  hO.map _ fun _ h => liftDE_valid hG h

end Section6

end Podc.LCLDefinitions
