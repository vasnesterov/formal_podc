import Papers.PODC2019.HardnessOptimization.MDSConnected
import Papers.PODC2019.HardnessOptimization.MDSCounterexample
import Papers.PODC2019.HardnessOptimization.MDSRandomized
import Papers.PODC2019.HardnessOptimization.Steiner
import Papers.PODC2019.HardnessOptimization.MaxCutTheorem
import Papers.PODC2019.HardnessOptimization.HamPathTheorem
import Papers.PODC2019.HardnessOptimization.HamPathCycle

/-! Axiom check of the main results (only `propext`, `Classical.choice`, `Quot.sound`). -/

#print axioms Cslib.CommunicationComplexity.Protocol.disj_lowerBound
#print axioms Cslib.Congest.LBFamily.simulation
#print axioms Cslib.Congest.LBFamily.rand_lowerBound
#print axioms Cslib.Congest.gather_accepts
#print axioms HardnessOptimization.lemma_2_1
#print axioms HardnessOptimization.theorem_2_1_n
#print axioms HardnessOptimization.theorem_2_1_connected
#print axioms HardnessOptimization.theorem_2_1_hyp_satisfiable
#print axioms HardnessOptimization.theorem_2_1_randomized
#print axioms HardnessOptimization.paper_intermediate_claim_false
#print axioms HardnessOptimization.claim_2_8
#print axioms HardnessOptimization.theorem_2_7
#print axioms HardnessOptimization.MaxCut.lemma_2_4
#print axioms HardnessOptimization.MaxCut.theorem_2_8
#print axioms HardnessOptimization.HamPath.hamPath_iff
#print axioms HardnessOptimization.HamPath.theorem_2_2
#print axioms HardnessOptimization.HamPath.theorem_2_2_n
#print axioms HardnessOptimization.HamPath.paperArc_not_hamPath
#print axioms HardnessOptimization.HamPath.theorem_2_3
#print axioms HardnessOptimization.MaxCut.claim_2_9
