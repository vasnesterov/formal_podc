import Papers.PODC2025.BAWithPredictions.Classification
import Papers.PODC2025.BAWithPredictions.Plurality
import Cslib.Computability.Distributed.Byzantine.PartialSync.Rounds

/-!
# Synchronous round executions (for the upper bounds)

The algorithms of Sections 6–8 are verified as CSLib round algorithms
(`Cslib.Byzantine.PartialSync.RoundAlgorithm`) against abstract round executions
(`RoundRun RA F inp`) that are synchronous from round `0` (`SyncFrom 0`): every message between
honest processes is delivered in its round, messages from honest senders are genuine, and the
Byzantine processes of `F` send arbitrary messages. Every synchronous run of the compiled
algorithm induces such a round execution (`Run.toRoundRun_syncFrom`), so the results transfer to
the time-based synchronous model.

* Synchronous executions are `E : RoundRun RA F inp` with `E.SyncFrom 0`.
* `roundMsgs E N`: the number of messages sent by honest processes to *other* processes in rounds
  `< N` (the paper's message complexity).
-/

namespace BAWithPredictions

open Finset Cslib.Byzantine.PartialSync

variable {P Msg S VI VO : Type*} [Fintype P] [DecidableEq P]

/-- Number of messages sent by honest processes to other processes in rounds `< N`. -/
def roundMsgs {RA : RoundAlgorithm P Msg S VI VO} {F : Finset P} {inp : P → VI}
    (E : RoundRun RA F inp) (N : ℕ) : ℕ :=
  ∑ r ∈ range N, ∑ p ∈ univ.filter (· ∉ F),
    (univ.filter fun q => q ≠ p ∧ RA.send r p (E.s r p) q ≠ none).card

end BAWithPredictions
