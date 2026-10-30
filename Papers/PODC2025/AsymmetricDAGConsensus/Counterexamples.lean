import Papers.PODC2025.AsymmetricDAGConsensus.RoundGather

/-!
# Lemma 3.2 (Algorithm 2 has no common core) and the "`log n − 1` rounds" claim

* `lemma_3_2`: the 30-process fail-prone system of Figure 1 / Listing 1 satisfies `B³`, its
  canonical quorums form an asymmetric quorum system, and Algorithm 2 has a fault-free execution
  in which all 30 processes (the maximal guild) ag-deliver and no common core exists.
  This confirms the paper's Lemma 3.2.
* `log_rounds_claim_false`: Appendix A claims that "the common core property can be obtained in
  `log n − 1` rounds of the type of communication used here". For `n = 8` this is
  `log₂ 8 − 1 = 2` rounds, but the 2-round version of the protocol has a fault-free execution
  on an 8-process `B³` system without common core (`ex8`). The same system has a common core
  after 3 rounds (`ex8_three_rounds_core`), so the bound fails by exactly the rounds the claim
  is about. `ex5` (5 processes) refutes the extrapolation "`r` rounds suffice below `2^(r+1)`
  processes" of the Section 3.2 remark ("3 rounds suffice below 16 processes") at `r = 2`.

Processes are `Fin n`; process `i` of the paper is `i - 1` here.
-/

namespace Podc.AsymmetricDAGConsensus

open Cslib.Byzantine.AsyncBroadcast Cslib.AsymmetricQuorum RoundGather

/-- The quorums of Figure 1 / Listing 1 (process `i + 1` of the paper is `i`). Each process has
a single fail-prone set, the complement of its quorum. -/
def fig1 : Fin 30 → Finset (Fin 30) := ![
  {0, 1, 2, 3, 4, 15}, {0, 5, 6, 7, 8, 16}, {0, 1, 2, 3, 4, 17}, {0, 5, 6, 7, 8, 18},
  {1, 5, 9, 10, 11, 19}, {3, 7, 10, 12, 14, 20}, {3, 7, 10, 12, 14, 21}, {4, 8, 11, 13, 14, 22},
  {4, 8, 11, 13, 14, 23}, {3, 7, 10, 12, 14, 24}, {0, 5, 6, 7, 8, 25}, {1, 5, 9, 10, 11, 26},
  {2, 6, 9, 12, 13, 27}, {2, 6, 9, 12, 13, 28}, {4, 8, 11, 13, 14, 29}, {0, 1, 2, 3, 4, 15},
  {0, 1, 2, 3, 4, 15}, {0, 1, 2, 3, 4, 15}, {0, 1, 2, 3, 4, 15}, {0, 5, 6, 7, 8, 26},
  {0, 5, 6, 7, 8, 26}, {0, 5, 6, 7, 8, 19}, {1, 5, 9, 10, 11, 29}, {1, 5, 9, 10, 11, 29},
  {0, 5, 6, 7, 8, 21}, {0, 1, 2, 3, 4, 15}, {0, 5, 6, 7, 8, 26}, {0, 1, 2, 3, 4, 15},
  {0, 1, 2, 3, 4, 28}, {1, 5, 9, 10, 11, 29}]

set_option maxRecDepth 100000 in
theorem fig1_inter : ∀ i j, (fig1 i ∩ fig1 j).Nonempty := by decide +kernel

set_option maxRecDepth 100000 in
theorem fig1_no_core : ∀ i, ∃ k, ¬ fig1 i ⊆ R fig1 (3 - 1) k := by
  simp only [R]; decide +kernel

/-- **Lemma 3.2.** Algorithm 2 does not satisfy the common-core property: for the fail-prone
system of Figure 1 (which satisfies `B³`, with its canonical asymmetric quorum system), there
is a fault-free execution of Algorithm 2 in which every process ag-delivers, all processes form
the maximal guild, and no common core exists. -/
theorem lemma_3_2 {V : Type*} (x : Fin 30 → V) :
    B3 (canonicalFailProne fig1) ∧
    IsQuorumSystem (canonicalFailProne fig1) (canonicalQuorums fig1) ∧
    maxGuild (canonicalFailProne fig1) (canonicalQuorums fig1) ∅ = Set.univ ∧
    ∃ σ, Reachable (protocol (canonicalQuorums fig1) 3) x .byzantine 0 σ ∧ σ.bad = ∅ ∧
      (∀ p, σ.dec p ≠ none) ∧
      ¬ CommonCore (canonicalQuorums fig1)
        (maxGuild (canonicalFailProne fig1) (canonicalQuorums fig1) ∅) σ.dec := by
  refine ⟨b3_canonical fig1_inter, isQuorumSystem_canonical fig1_inter,
    maxGuild_canonical_empty fig1, fin fig1 x 3,
    reachable_run (Qs := canonicalQuorums fig1) (r := 3) fig1 x (fun _ => rfl) (by norm_num) _ _, rfl, fun p => by simp [fin], ?_⟩
  rw [maxGuild_canonical_empty]
  exact not_commonCore_of_run fig1 x Set.univ fun i =>
    (fig1_no_core i).imp fun k hk => ⟨Set.mem_univ k, hk⟩

/-! ### Fewer rounds: the `log n − 1` claim -/

/-- A 5-process single-quorum system without common core after 2 rounds (found by SAT search;
2 rounds have a common core for every system with at most 4 processes). -/
def ex5 : Fin 5 → Finset (Fin 5) := ![{0, 1, 3}, {2, 3, 4}, {0, 3, 4}, {0, 4}, {0, 2, 3}]

/-- `ex5` padded to 8 processes: processes 5, 6, 7 copy the quorum of process 0. -/
def ex8 : Fin 8 → Finset (Fin 8) :=
  ![{0, 1, 3}, {2, 3, 4}, {0, 3, 4}, {0, 4}, {0, 2, 3}, {0, 1, 3}, {0, 1, 3}, {0, 1, 3}]

theorem ex5_inter : ∀ i j, (ex5 i ∩ ex5 j).Nonempty := by decide
theorem ex8_inter : ∀ i j, (ex8 i ∩ ex8 j).Nonempty := by decide
theorem ex5_no_core : ∀ i, ∃ k, ¬ ex5 i ⊆ R ex5 (2 - 1) k := by simp only [R]; decide
theorem ex8_no_core : ∀ i, ∃ k, ¬ ex8 i ⊆ R ex8 (2 - 1) k := by simp only [R]; decide
/-- With 3 rounds, `ex8` does have a common core in the canonical run. -/
theorem ex8_three_rounds_core : ∃ i, ∀ k, ex8 i ⊆ R ex8 (3 - 1) k := by simp only [R]; decide

/-- The 2-round version of the protocol has a fault-free execution without common core on any
single-quorum `B³` system `q` for which no quorum lies in every 2-round neighbourhood. -/
theorem two_rounds_no_core {n : ℕ} {V : Type*} (q : Fin n → Finset (Fin n))
    (hi : ∀ i j, (q i ∩ q j).Nonempty) (hc : ∀ i, ∃ k, ¬ q i ⊆ R q (2 - 1) k) (x : Fin n → V) :
    B3 (canonicalFailProne q) ∧ IsQuorumSystem (canonicalFailProne q) (canonicalQuorums q) ∧
    ∃ σ, Reachable (protocol (canonicalQuorums q) 2) x .byzantine 0 σ ∧ σ.bad = ∅ ∧
      (∀ p, σ.dec p ≠ none) ∧
      ¬ CommonCore (canonicalQuorums q) (maxGuild (canonicalFailProne q) (canonicalQuorums q) ∅)
        σ.dec := by
  refine ⟨b3_canonical hi, isQuorumSystem_canonical hi, fin q x 2,
    reachable_run (Qs := canonicalQuorums q) (r := 2) q x (fun _ => rfl) (by norm_num) _ _, rfl, fun p => by simp [fin], ?_⟩
  rw [maxGuild_canonical_empty]
  exact not_commonCore_of_run q x Set.univ fun i =>
    (hc i).imp fun k hk => ⟨Set.mem_univ k, hk⟩

/-- **The claim of Appendix A ("the common core property can be obtained in `log n − 1`
rounds") is false.** For `n = 8` processes, `log₂ n − 1 = 2`, but the 2-round quorum-replacement
gather has a fault-free execution on an 8-process `B³` system in which every process
ag-delivers and there is no common core. -/
theorem log_rounds_claim_false {V : Type*} (x : Fin 8 → V) :
    Nat.log 2 8 - 1 = 2 ∧ B3 (canonicalFailProne ex8) ∧
    IsQuorumSystem (canonicalFailProne ex8) (canonicalQuorums ex8) ∧
    ∃ σ, Reachable (protocol (canonicalQuorums ex8) 2) x .byzantine 0 σ ∧ σ.bad = ∅ ∧
      (∀ p, σ.dec p ≠ none) ∧
      ¬ CommonCore (canonicalQuorums ex8)
        (maxGuild (canonicalFailProne ex8) (canonicalQuorums ex8) ∅) σ.dec :=
  ⟨by decide, two_rounds_no_core ex8 ex8_inter ex8_no_core x⟩

/-- The extrapolation of the Section 3.2 remark ("with 3 rounds every system with fewer than
16 processes has a common core") to `r = 2` rounds and fewer than `2³ = 8` processes fails:
`ex5` has 5 processes. -/
theorem two_rounds_five_processes {V : Type*} (x : Fin 5 → V) :
    5 < 2 ^ (2 + 1) ∧ B3 (canonicalFailProne ex5) ∧
    IsQuorumSystem (canonicalFailProne ex5) (canonicalQuorums ex5) ∧
    ∃ σ, Reachable (protocol (canonicalQuorums ex5) 2) x .byzantine 0 σ ∧ σ.bad = ∅ ∧
      (∀ p, σ.dec p ≠ none) ∧
      ¬ CommonCore (canonicalQuorums ex5)
        (maxGuild (canonicalFailProne ex5) (canonicalQuorums ex5) ∅) σ.dec :=
  ⟨by norm_num, two_rounds_no_core ex5 ex5_inter ex5_no_core x⟩

end Podc.AsymmetricDAGConsensus
