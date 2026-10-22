import Podc.Computability.Distributed.PopulationProtocols.Multiset.PotentialReach

/-!
# WS³: LayeredTermination and StrongConsensus (Blondin, Esparza, Jaax, Meyer, PODC 2017, §4)

The population-protocol model (multiset configurations, transition relation `T`, edge fairness,
`WellSpecified`, `Silent`, `Termination`, `Consensus`, `WS2`) and potential reachability (flow
equations, traps, siphons) are in
`Podc/Computability/Distributed/PopulationProtocols/Multiset/`. Here:

* `IsOrderedPartition T L`: `L = [T₁, …, Tₙ]` is an ordered partition of `T`.
* `LayeredTerminationWith P L` (Definition 4), `LayeredTermination P`.
* `StrongConsensus P` (Definition 14).
* `WS3 P`.
-/

namespace Podc.PPVerification

open Cslib.PopulationProtocol Cslib.TransitionSystem

variable {Q Λ : Type*} [DecidableEq Q] [Fintype Q]

/-- `[T₁, …, Tₙ]` is an *ordered partition* of `T`: nonempty, pairwise disjoint parts covering
`T`. -/
structure IsOrderedPartition (T : Set (Transition Q)) (L : List (Set (Transition Q))) : Prop where
  nonempty : ∀ S ∈ L, S.Nonempty
  disjoint : L.Pairwise Disjoint
  cover : {t | ∃ S ∈ L, t ∈ S} = T

/-- `T₁ ∪ ⋯ ∪ Tᵢ`, the transitions of the first `i` layers. -/
def layersBelow (L : List (Set (Transition Q))) (i : ℕ) : Set (Transition Q) :=
  {t | ∃ S ∈ L.take i, t ∈ S}

/-- **Definition 4 (LayeredTermination)** for a given ordered partition `L = [T₁, …, Tₙ]`:
for every layer `Tᵢ`,
(a) every (fair or unfair) execution of `P[Tᵢ]` is silent, and
(b) if `C →*_{Tᵢ} C'` and `C` is terminal in `P[T₁ ∪ ⋯ ∪ Tᵢ₋₁]`, then so is `C'`. -/
def LayeredTerminationWith (P : MProtocol Q Λ) (L : List (Set (Transition Q))) : Prop :=
  IsOrderedPartition P.T L ∧ ∀ i (hi : i < L.length),
    (∀ E : Run (P.restrict L[i]).Step, E.Silent) ∧
    ∀ C C', MReach (P.restrict L[i]).T C C' → Terminal (P.restrict (layersBelow L i)).T C →
      Terminal (P.restrict (layersBelow L i)).T C'

/-- **Definition 4.** `P` satisfies LayeredTermination if some ordered partition of its
transitions satisfies (a) and (b). -/
def LayeredTermination (P : MProtocol Q Λ) : Prop := ∃ L, LayeredTerminationWith P L

/-- **Definition 14 (StrongConsensus).** For every initial configuration `C` there is `b` such
that every terminal configuration potentially reachable from `C` is a consensus configuration
with output `b`. -/
def StrongConsensus (P : MProtocol Q Λ) : Prop :=
  ∀ C, P.IsInitial C → ∃ b, ∀ C', PotReach P.T C C' → Terminal P.T C' → IsConsensus P.O C' b

/-- `WS³`: protocols satisfying LayeredTermination and StrongConsensus (§4.3). -/
def WS3 (P : MProtocol Q Λ) : Prop := LayeredTermination P ∧ StrongConsensus P

end Podc.PPVerification
