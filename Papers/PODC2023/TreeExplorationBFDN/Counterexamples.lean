import Papers.PODC2023.TreeExplorationBFDN.Examples
import Papers.PODC2023.TreeExplorationBFDN.Main

/-!
# Counterexamples to statements of the paper
-/

set_option linter.unusedSectionVars false

namespace Podc.TreeExplorationBFDN

open Finset SimpleGraph

section Claim1

/-- Re-anchoring choices of the Claim 1 execution (robots `0, 1, 2`). -/
def c1Na : ℕ → Fin 3 → Fin 7
  | 0 => ![0, 0, 0] | 1 => ![0, 0, 1] | 2 => ![0, 0, 1]
  | 3 => ![0, 0, 5] | 4 => ![0, 0, 5] | 5 => ![0, 0, 5] | 6 => ![0, 0, 5] | 7 => ![0, 0, 5]
  | 8 => ![0, 0, 5] | _ => ![0, 0, 0]

/-- Moves of the Claim 1 execution. -/
def c1Tgt : ℕ → Fin 3 → Fin 7
  | 0 => ![1, 2, 0] | 1 => ![3, 4, 1] | 2 => ![5, 2, 0] | 3 => ![6, 0, 1] | 4 => ![5, 0, 3]
  | 5 => ![3, 0, 5] | 6 => ![1, 0, 3] | 7 => ![0, 0, 1] | _ => ![0, 0, 0]

/-- The Claim 1 execution with `k = 3` robots on `claim1Tree`. -/
def c1Exec : ℕ → Config (Fin 7) 3
  | 0 => init claim1Tree 3
  | t + 1 => after claim1Tree univ (c1Exec t) (c1Na t) (c1Tgt t)

theorem c1Na_ge {t : ℕ} (ht : 9 ≤ t) : c1Na t = ![0, 0, 0] := by
  unfold c1Na; split <;> first | rfl | omega

theorem c1Tgt_ge {t : ℕ} (ht : 8 ≤ t) : c1Tgt t = ![0, 0, 0] := by
  unfold c1Tgt; split <;> first | rfl | omega

theorem c1Exec_ge {t : ℕ} (ht : 10 ≤ t) : c1Exec t = c1Exec 10 := by
  induction t, ht using Nat.le_induction with
  | base => rfl
  | succ t ht ih =>
    show after claim1Tree univ (c1Exec t) (c1Na t) (c1Tgt t) = c1Exec 10
    rw [ih, c1Na_ge (by omega), c1Tgt_ge (by omega)]
    apply Config.ext <;> decide

theorem c1_isSyncExec : IsSyncExec claim1Tree c1Exec := by
  refine ⟨rfl, fun t => ?_⟩
  by_cases ht : t < 10
  · interval_cases t <;> exact ⟨_, _, by decide, by decide, rfl⟩
  · rw [c1Exec_ge (t := t + 1) (by omega), c1Exec_ge (t := t) (by omega)]
    show Round claim1Tree univ (c1Exec 10) (c1Exec 10)
    refine ⟨c1Na 10, c1Tgt 10, by decide, by decide, ?_⟩
    apply Config.ext <;> decide

/-- **Claim 1 of the full version is false** ("the total number of rounds when some robot does
not move is at most `D + 1`"): on a tree of depth `D = 4` with `k = 3` robots, BFDN (with
lowest-index tie-breaking) terminates after 9 rounds, and 6 of them contain an idle robot.
In round 3 robot 2 is sent to anchor `5` (depth 3) while robot 0, standing at `5`, takes the last
dangling edge; the tree is explored, but robot 2 still walks down to `5` and back, while the
other robots wait at the root for `2·3 − 1` rounds. The correct bound is `2D`
(`card_idleRounds_le`), which still suffices for Theorem 2.1. -/
theorem claim_1_false :
    IsSyncExec claim1Tree c1Exec ∧ maxDepth claim1Tree = 4 ∧
      (∀ t < 9, ¬ Terminal claim1Tree (c1Exec t)) ∧ Terminal claim1Tree (c1Exec 9) ∧
      ((range 9).filter fun t => ∃ i, (c1Exec (t + 1)).pos i = (c1Exec t).pos i).card = 6 ∧
      maxDepth claim1Tree + 1 < 6 := by
  refine ⟨c1_isSyncExec, by decide, ?_, by decide, by decide, by decide⟩
  intro t ht
  interval_cases t <;> decide

end Claim1

end Podc.TreeExplorationBFDN

namespace Podc.TreeExplorationBFDN

open Finset SimpleGraph

section Star

/-- All possible first two rounds of BFDN with one robot on the star with two leaves. -/
theorem star3_two_rounds : ∀ a b a' b' : Fin 3,
    (∀ i, ReanchorOK star3 univ (init star3 1) (fun _ => a) i) →
    (∀ i, MoveOK star3 univ (init star3 1) (fun _ => a) (fun _ => b) i) →
    (∀ i, ReanchorOK star3 univ (after star3 univ (init star3 1) (fun _ => a) (fun _ => b))
      (fun _ => a') i) →
    (∀ i, MoveOK star3 univ (after star3 univ (init star3 1) (fun _ => a) (fun _ => b))
      (fun _ => a') (fun _ => b') i) →
    b ≠ 0 ∧ b' = 0 ∧
      (after star3 univ (after star3 univ (init star3 1) (fun _ => a) (fun _ => b))
        (fun _ => a') (fun _ => b')).vis ≠ univ := by
  intro a b a' b'
  fin_cases a <;> fin_cases b <;> fin_cases a' <;> fin_cases b' <;> decide

theorem fun_fin_one {α : Type*} (f : Fin 1 → α) : f = fun _ => f 0 := by
  funext i; rw [Subsingleton.elim i 0]

theorem star3_exec {e : ℕ → Config (Fin 3) 1} (he : IsSyncExec star3 e) :
    (e 1).pos 0 ≠ 0 ∧ (e 2).pos 0 = 0 ∧ (e 2).vis ≠ univ := by
  obtain ⟨na, tgt, hR, hM, h1⟩ := he.2 0
  obtain ⟨na', tgt', hR', hM', h2⟩ := he.2 1
  rw [he.1] at hR hM h1
  rw [h1] at hR' hM' h2
  obtain ⟨a, rfl⟩ : ∃ a, na = fun _ => a := ⟨na 0, fun_fin_one na⟩
  obtain ⟨b, rfl⟩ : ∃ b, tgt = fun _ => b := ⟨tgt 0, fun_fin_one tgt⟩
  obtain ⟨a', rfl⟩ : ∃ a, na' = fun _ => a := ⟨na' 0, fun_fin_one na'⟩
  obtain ⟨b', rfl⟩ : ∃ b, tgt' = fun _ => b := ⟨tgt' 0, fun_fin_one tgt'⟩
  obtain ⟨hb, hb', hv⟩ := star3_two_rounds _ _ _ _ hR hM hR' hM'
  refine ⟨by rw [h1]; exact hb, by rw [h2]; exact hb', by rw [h2]; exact hv⟩

/-- **The loop condition of Algorithm 1 in the brief announcement is wrong.** Line 14 reads
"while not all robots are at the root"; with one robot on the star with two leaves, every
execution of BFDN has the robot at a leaf after round 0 and back at the root after round 1, so the
loop stops after two rounds with a leaf never visited. (The full version uses the correct
condition "while some robot changes position", which we formalize via `Terminal`.) -/
theorem algorithm_1_loop_stops_early {e : ℕ → Config (Fin 3) 1} (he : IsSyncExec star3 e) :
    (∃ i, (e 1).pos i ≠ star3.root) ∧ (∀ i, (e 2).pos i = star3.root) ∧ (e 2).vis ≠ univ := by
  obtain ⟨h1, h2, h3⟩ := star3_exec he
  refine ⟨⟨0, h1⟩, fun i => ?_, h3⟩
  rw [Subsingleton.elim i 0]; exact h2

/-- Number of calls to procedure `Reanchor` in rounds `0, …, t₁ - 1` of a synchronous execution
(every robot at the root calls it). -/
def reanchorCalls {V : Type*} [DecidableEq V] {G : SimpleGraph V} (T : G.RootedTree) {k : ℕ}
    (e : ℕ → Config V k) (t₁ : ℕ) : ℕ :=
  ∑ t ∈ range t₁, (univ.filter fun i => (e t).pos i = T.root).card

/-- **Corollary 3.2 (as stated in the brief announcement) is false.** It claims that the number of
calls to `Reanchor` is at most `D (k min(log k, log Δ) + k)`. With one robot on the star with two
leaves (`D = 1`) this bound is `1`, but `Reanchor` is called in rounds 0 and 2, both before the
end of the exploration. (In general, robots at the root call `Reanchor` in every round; what the
analysis needs and what we prove is Lemma 2 of the full version, `lemma_2`, which bounds the
assignments to anchors of a fixed depth `d ≥ 1`.) -/
theorem corollary_3_2_false {e : ℕ → Config (Fin 3) 1} (he : IsSyncExec star3 e) :
    (∀ t < 3, ¬ Terminal star3 (e t)) ∧
      ((maxDepth star3 : ℝ) * (1 * min (Real.log 1) (Real.log (tableGraph ![(0 : Fin 3), 0, 0]).maxDegree)
        + 1) = 1) ∧ 2 ≤ reanchorCalls star3 e 3 := by
  obtain ⟨h1, h2, h3⟩ := star3_exec he
  have hD : maxDepth star3 = 1 := by decide
  refine ⟨?_, ?_, ?_⟩
  · intro t ht
    interval_cases t
    · rw [he.1]; decide
    · exact fun h => h1 (h.2 0)
    · exact fun h => h3 h.1
  · rw [hD, Real.log_one, min_eq_left (Real.log_natCast_nonneg _)]; norm_num
  · unfold reanchorCalls
    rw [sum_range_succ, sum_range_succ, sum_range_succ]
    have e0 : (univ.filter fun i => (e 0).pos i = star3.root).card = 1 := by rw [he.1]; decide
    have e2 : (univ.filter fun i => (e 2).pos i = star3.root).card = 1 := by
      rw [filter_true_of_mem (fun i _ => by rw [Subsingleton.elim i 0]; exact h2)]; rfl
    omega

end Star

end Podc.TreeExplorationBFDN
