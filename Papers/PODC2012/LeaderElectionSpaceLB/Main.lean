import Papers.PODC2012.LeaderElectionSpaceLB.Lemma54
import Papers.PODC2012.LeaderElectionSpaceLB.NonVacuity

/-!
# Theorem 5.1: leader election needs `Ω(log n)` registers

Any leader election algorithm for `n` processes from read/write registers that satisfies
nondeterministic solo-termination needs at least `⌊log₂ n⌋ - 1` registers. In fact, some
reachable configuration has at least `⌊log₂ n⌋ - 1` distinct registers that are covered
(about to be written).

For `n` not a power of two we run the paper's construction on `2^⌊log₂ n⌋` processes (the others
never take a step), as the paper's "w.l.o.g. `n` is a power of two" suggests.
-/

namespace Podc.LeaderElectionSpaceLB

set_option linter.unusedSectionVars false

open Classical

variable {P Reg V L : Type*} [DecidableEq P] [DecidableEq Reg] [Fintype P] [Fintype Reg]

namespace Alg

variable (A : Alg P Reg V L)

/-- **Theorem 5.1** (covering form). For a leader election algorithm with nondeterministic
solo-termination for `n` processes, some reachable configuration has at least `⌊log₂ n⌋ - 1`
distinct covered registers. -/
theorem theorem_5_1_covered (hLE : A.IsLeaderElection) (hST : A.SoloTerminating) :
    ∃ C, A.Reachable C ∧ ∃ T : Finset Reg, Nat.log 2 (Fintype.card P) - 1 ≤ T.card ∧
      ∀ r ∈ T, ∃ p, A.Covers C p r := by
  set n := Fintype.card P
  set t := Nat.log 2 n
  by_cases ht : t < 2
  · choose l hl using A.init_nonempty
    let C₀ : Config P Reg V L := ⟨l, A.v₀, fun _ => none⟩
    exact ⟨C₀, A.isInit_reachable ⟨hl, fun _ => rfl, fun _ => rfl⟩, ∅, by simp; omega,
      by simp⟩
  push Not at ht
  have hn : n ≠ 0 := by
    intro h; simp [t, h] at ht
  set N := 2 ^ t
  have hNn : N ≤ n := Nat.pow_log_le_self 2 hn
  have hN4 : 4 ≤ N := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ t := Nat.pow_le_pow_right (by norm_num) ht
  obtain ⟨Act, -, hAct⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset P))
    (n := N) (by simpa using hNn)
  obtain ⟨S⟩ := A.lemma_5_4 hLE hST Act N hAct (by omega) (N - 4) (by omega)
  set C := A.run S.C₀ S.es
  refine ⟨C, ⟨S.C₀, S.es, S.init, S.valid, rfl⟩,
    Finset.univ.filter (fun r => ∃ q ∈ S.reps, A.Covers C q r), ?_, ?_⟩
  · have h1 : S.reps.card ≤ 4 * (Finset.univ.filter (fun r => ∃ q ∈ S.reps, A.Covers C q r)).card := by
      apply A.card_le_mul C S.reps _ 4
      · intro q hq
        obtain ⟨r, hr⟩ := S.cover q hq
        exact ⟨r, by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨q, hq, hr⟩, hr⟩
      · intro r
        have := S.cnt_le r
        rwa [show N - (N - 4) = 4 by omega] at this
    have h2 : f N (N - 4) ≤ S.reps.card := S.card
    rw [f_pow_sub_four t ht] at h2
    omega
  · intro r hr
    obtain ⟨q, -, hq⟩ := (Finset.mem_filter.1 hr).2
    exact ⟨q, hq⟩

/-- **Theorem 5.1.** Any leader election algorithm for `n` processes from read/write registers
that satisfies nondeterministic solo-termination uses at least `⌊log₂ n⌋ - 1 = Ω(log n)`
registers. -/
theorem theorem_5_1 (hLE : A.IsLeaderElection) (hST : A.SoloTerminating) :
    Nat.log 2 (Fintype.card P) - 1 ≤ Fintype.card Reg := by
  obtain ⟨-, -, T, hT, -⟩ := A.theorem_5_1_covered hLE hST
  exact hT.trans (Finset.card_le_univ T)

/-- Non-vacuity of Theorem 5.1: for every number of processes there is an algorithm satisfying
its hypotheses (the racing-counters algorithm of `NonVacuity.lean`, with `n` registers). -/
example (Q : Type*) [Fintype Q] [DecidableEq Q] :
    Nat.log 2 (Fintype.card Q) - 1 ≤ Fintype.card Q :=
  (Racing.racing Q).theorem_5_1 Racing.racing_isLeaderElection Racing.racing_soloTerminating

end Alg

end Podc.LeaderElectionSpaceLB
