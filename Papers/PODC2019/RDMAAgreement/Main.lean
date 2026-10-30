import Papers.PODC2019.RDMAAgreement.LowerBound.Theorem61
import Papers.PODC2019.RDMAAgreement.LowerBound.NonVacuity
import Papers.PODC2019.RDMAAgreement.PMP.Safety
import Papers.PODC2019.RDMAAgreement.PMP.Counterexample
import Papers.PODC2019.RDMAAgreement.PMP.FirstBallot
import Papers.PODC2019.RDMAAgreement.RB.Main

/-!
# The Impact of RDMA on Agreement (Aguilera, Ben-David, Guerraoui, Marathe, Zablotchi, PODC 2019)

Entry point. Main results:
* Theorem 6.1: `Podc.RDMAAgreement.LowerBound.theorem_6_1`, `not_twoDeciding`
  (non-vacuity of its hypotheses: `LowerBound.NonVacuity.hypotheses_satisfiable`);
* Algorithm 7 (Protected Memory Paxos): `PMP.theorem_D2_false` (agreement fails as written),
  `PMP.first_ballot_not_minimal_false`, and for the repaired algorithm `PMP.theorem_D1`,
  `PMP.theorem_D2`, `PMP.lemma_D4`;
* Lemma 4.1 (reliable broadcast from SWMR regular registers): `RB.lemma_4_1`,
  `RB.lemma_4_1_nonvacuous`.
-/
