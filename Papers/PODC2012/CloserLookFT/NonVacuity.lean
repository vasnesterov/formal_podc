import Papers.PODC2012.CloserLookFT.ElectionSafety

/-!
# Non-vacuity and tightness of Theorem 2.4

* `elected_example`: with two processes and one level a process gets elected (the safety
  theorem is not vacuous);
* `two_leaders_three_procs_one_level`: with three processes and only one level (`3 > 2^1`) two
  processes are elected, so the hypothesis `n ≤ 2^L` (i.e. `L ≥ ⌈log₂ n⌉` levels) of
  `EReach.elected_unique` cannot be dropped. (Exhaustive search also finds two leaders for
  `n = 5`, `L = 2`.)
-/

namespace Podc.CloserLookFT

/-- An action of the transition system. -/
inductive Act (P : Type) where
  | inv (p : P)
  | step (p : P)

variable {P : Type} [DecidableEq P]

/-- Run a list of actions from the initial state. -/
def runActs (L : ℕ) (as : List (Act P)) : ESys P :=
  as.foldl (fun s a => match a with | .inv p => s.invoke p | .step p => s.step L p) (ESys.init P)

lemma runActs_reach (L : ℕ) (as : List (Act P)) : EReach L (runActs L as) := by
  unfold runActs
  induction as using List.reverseRecOn with
  | nil => exact EReach.init
  | append_singleton as a ih =>
    rw [List.foldl_append]
    cases a with
    | inv p => exact ih.invoke p
    | step p => exact ih.step p

/-- Process `0` alone gets elected (two processes, one level). -/
theorem elected_example :
    let s := runActs (P := Fin 2) 1 [.inv 0, .step 0, .step 0, .step 0, .step 0, .step 0, .step 0,
      .step 0]
    EReach 1 s ∧ (s.loc 0).Elected := by
  refine ⟨runActs_reach _ _, ?_⟩
  have : (runActs (P := Fin 2) 1 [.inv 0, .step 0, .step 0, .step 0, .step 0, .step 0, .step 0,
      .step 0]).loc 0 = .out true 1 1 0 := by decide
  rw [this]; trivial

/-- The schedule found by exhaustive search for three processes and one level. -/
def twoLeaders : List (Act (Fin 3)) :=
  [.inv 0, .step 0, .step 0, .step 0, .step 0, .inv 1, .step 1, .step 1, .step 1, .step 1,
   .step 0, .step 0, .step 0, .step 1, .step 0, .step 1, .inv 2, .step 2, .step 2, .step 2,
   .step 2, .step 2, .step 2]

/-- **Tightness**: three processes, one level: two processes are elected. -/
theorem two_leaders_three_procs_one_level :
    EReach 1 (runActs 1 twoLeaders) ∧ ((runActs 1 twoLeaders).loc 1).Elected ∧
      ((runActs 1 twoLeaders).loc 2).Elected := by
  refine ⟨runActs_reach _ _, ?_, ?_⟩
  · have : (runActs 1 twoLeaders).loc 1 = .wdone := by decide
    rw [this]; trivial
  · have : (runActs 1 twoLeaders).loc 2 = .wdone := by decide
    rw [this]; trivial

end Podc.CloserLookFT
