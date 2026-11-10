import Papers.PODC2012.OrderPreservingByzRenaming.Alg5

/-!
# Algorithm 5 fails for `n = 7`, `t = 2` (Theorem 39 and Lemma 33 are false)

Correct processes `0, …, 4` with ids `3, …, 7`; Byzantine processes `5, 6`; the Byzantine processes
use the "fake" ids `x = 2` and `y = 1`.

* Round 1: process `5` sends `x` to `0, 1, 2` and `y` to `3, 4`; process `6` sends `y` to `2`.
* Round 2: both echo `x` to `0, 1, 2` and `y` to `2`. So `0, 1, 2` see 5 echoes of `x`, process `2`
  sees 5 echoes of `y`.
* Round 3: both send Ready for `x` to `0` only and Ready for `y` to `2, 3, 4` only. Result:
  `timely₀ = {2, …, 7}`, `timely_i = {3, …, 7}` for `i ≥ 1`; `accepted₀ = accepted₁ = {2, …, 7}`,
  `accepted_i = {1, …, 7}` for `i ≥ 2`. Hence processes `0, 1` rank `x, 3` as `δ, 2δ`, processes
  `2, 3, 4` as `2δ, 3δ`.
* Round 4: both send process `1` the vote `x ↦ 3δ, k ↦ (k - 1)δ (k = 3, …, 7)`. It is valid at `1`
  (`x ∉ timely₁`), and process `1` computes `ranks[x] = 2δ` and `ranks[3] ∈ {2δ, 2.5δ}` (both
  choices of `select_t`): the spacing `δ` between `x` and `3` is lost.
* Round 5: process `0` (with `x ∈ timely₀`) rejects the vote of the correct process `1`
  (**Lemma 33 fails**); the Byzantine processes send nothing to `0`. So `0` has only 4 < n - t valid
  votes and drops every id from `accepted`, including its own: it never decides.
-/

namespace Podc.OrderPreservingByzRenaming.Alg5

open Cslib.Byzantine.LockStep

namespace Cex7

/-- Byzantine processes. -/
def F : Finset (Fin 7) := {5, 6}

/-- Ids: process `j` has id `j + 3`. -/
def x (j : Fin 7) : ℕ := j.val + 3

/-- The Byzantine vote sent to process `1` in Round 4 (in units of `δ`). -/
def voteVal (k : ℕ) : ℚ := (if k = 2 then 3 else (k : ℚ) - 1) * δ 7 2

/-- The adversary. -/
def adv (r : ℕ) (b p : Fin 7) : Option Msg :=
  match r with
  | 0 => if b.val = 5 then (if p.val ≤ 2 then some (.ident 2) else some (.ident 1))
         else if p.val = 2 then some (.ident 1) else none
  | 1 => if p.val ≤ 1 then some (.echo {2}) else if p.val = 2 then some (.echo {1, 2}) else none
  | 2 => if p.val = 0 then some (.ready {2}) else if 2 ≤ p.val then some (.ready {1}) else none
  | 3 => if p.val = 1 then some (.aa {2, 3, 4, 5, 6, 7} voteVal) else none
  | _ => none

/-- The scenario. -/
def scen : Scenario (Fin 7) ℕ Msg where
  byz := ↑F
  input := x
  adv := adv

lemma hF : ∀ j, j ∈ scen.byz ↔ j ∈ F := fun _ => Iff.rfl

lemma timely0 : (run 7 2 selPaper F x adv 3 0).timely = {2, 3, 4, 5, 6, 7} := by
  decide +kernel

lemma timely1 : (run 7 2 selPaper F x adv 3 1).timely = {3, 4, 5, 6, 7} := by
  decide +kernel

lemma acc3_0 : (run 7 2 selPaper F x adv 3 0).acc = {2, 3, 4, 5, 6, 7} := by decide +kernel

lemma acc3_2 : (run 7 2 selPaper F x adv 3 2).acc = {1, 2, 3, 4, 5, 6, 7} := by decide +kernel

/-- After Round 4, process `1` has lost the spacing between `x = 2` and the correct id `3`. -/
lemma ranks4_paper : (run 7 2 selPaper F x adv 4 1).val 2 = 2 * δ 7 2 ∧
    (run 7 2 selPaper F x adv 4 1).val 3 = 2 * δ 7 2 := by decide +kernel

lemma ranks4_dlpsw : (run 7 2 selDLPSW F x adv 4 1).val 2 = 2 * δ 7 2 ∧
    (run 7 2 selDLPSW F x adv 4 1).val 3 = 5 / 2 * δ 7 2 := by decide +kernel

/-- **Lemma 33 fails** (with the paper's `select_t`): in Round 5, the vote of the correct process
`1` is not valid at the correct process `0`. -/
lemma lemma_33_false_paper :
    ¬ IsValid 7 2 (run 7 2 selPaper F x adv 4 0).timely (run 7 2 selPaper F x adv 4 1).acc
      (run 7 2 selPaper F x adv 4 1).val := by
  decide +kernel

/-- **Lemma 33 fails** (with the `select_t` of Dolev et al.). -/
lemma lemma_33_false_dlpsw :
    ¬ IsValid 7 2 (run 7 2 selDLPSW F x adv 4 0).timely (run 7 2 selDLPSW F x adv 4 1).acc
      (run 7 2 selDLPSW F x adv 4 1).val := by
  decide +kernel

lemma acc5_paper : (run 7 2 selPaper F x adv 5 0).acc = ∅ := by decide +kernel

lemma acc5_dlpsw : (run 7 2 selDLPSW F x adv 5 0).acc = ∅ := by decide +kernel

/-- The failure spreads: after Round 7 no correct process has any id left in `accepted`. -/
lemma acc7_paper : ∀ p : Fin 7, p ∉ F → (run 7 2 selPaper F x adv 7 p).acc = ∅ := by decide +kernel

end Cex7

/-- If a correct process has an empty `accepted` set after Round 5 of some run, Algorithm 5 with any
number `L ≥ 5` of rounds fails termination in that run. -/
lemma not_solves_of_acc_empty {n t : ℕ} {sel : ℕ → List ℚ → List ℚ} {s : Scenario (Fin n) ℕ Msg}
    (hs : s.Reliable) {F : Finset (Fin n)} (hF : ∀ j, j ∈ s.byz ↔ j ∈ F) (hbyz : s.byz ∈ (atMost t : AdvStructure (Fin n)))
    (hinj : Set.InjOn s.input s.honest) {p : Fin n} (hp : p ∉ s.byz)
    (h5 : (run n t sel F s.input s.adv 5 p).acc = ∅) {L : ℕ} (hL : 5 ≤ L) (M : ℕ) :
    ¬ Solves (⊤ : SimpleGraph (Fin n)) (alg n t sel L) (atMost t) (OPRenaming M) := by
  intro h
  obtain ⟨hterm, -⟩ := h s hbyz hs ⟨hinj, fun _ _ => trivial⟩
  obtain ⟨o, ho⟩ := hterm p hp
  refine not_decides_of_not_mem hs hF hp ?_ o ho
  intro hmem
  have := run_acc_mono F s.input s.adv (by norm_num) hL p hmem
  rw [h5] at this
  simp at this

/-- **Theorem 39 is false.** For `n = 7 > 3t`, `t = 2`, Algorithm 5 (with either choice of
`select_t`, and any number `L ≥ 5` of rounds, in particular the paper's `L = 2⌈log t⌉ + 8 = 10`)
does not solve order-preserving renaming, whatever the target namespace: in the execution `Cex7.scen`
the correct process `0` never decides. -/
theorem theorem_39_false :
    7 > 3 * 2 ∧ ∀ L ≥ 5, ∀ M,
      ¬ Solves (⊤ : SimpleGraph (Fin 7)) (alg 7 2 selPaper L) (atMost 2) (OPRenaming M) ∧
      ¬ Solves (⊤ : SimpleGraph (Fin 7)) (alg 7 2 selDLPSW L) (atMost 2) (OPRenaming M) := by
  have hbyz : Cex7.scen.byz ∈ (atMost 2 : AdvStructure (Fin 7)) := by
    simp [Cex7.scen, Set.ncard_coe_finset, Cex7.F]
  have hinj : Set.InjOn Cex7.scen.input Cex7.scen.honest := fun p _ q _ h => by
    simpa [Cex7.scen, Cex7.x, Fin.ext_iff] using h
  have hp : (0 : Fin 7) ∉ Cex7.scen.byz := by simp [Cex7.scen, Cex7.F]
  refine ⟨by norm_num, fun L hL M => ⟨?_, ?_⟩⟩
  · exact not_solves_of_acc_empty (fun _ _ _ h => h) Cex7.hF hbyz hinj hp Cex7.acc5_paper hL M
  · exact not_solves_of_acc_empty (fun _ _ _ h => h) Cex7.hF hbyz hinj hp Cex7.acc5_dlpsw hL M

namespace Cex9

/-- Byzantine processes. -/
def F : Finset (Fin 9) := {7, 8}

/-- Ids: process `j` has id `j + 3`. -/
def x (j : Fin 9) : ℕ := j.val + 3

/-- The Byzantine vote sent to process `1` in Round 4. -/
def voteVal (k : ℕ) : ℚ := (if k = 2 then 3 else (k : ℚ) - 1) * δ 9 2

/-- The adversary (same pattern as `Cex7.adv`). -/
def adv (r : ℕ) (b p : Fin 9) : Option Msg :=
  match r with
  | 0 => if b.val = 7 then (if p.val ≤ 4 then some (.ident 2) else some (.ident 1))
         else if p.val ≤ 2 then some (.ident 1) else none
  | 1 => if p.val = 2 then some (.echo {1, 2}) else if p.val ≤ 4 then some (.echo {2})
         else some (.echo {1})
  | 2 => if p.val = 0 then some (.ready {2}) else if 2 ≤ p.val then some (.ready {1}) else none
  | 3 => if p.val = 1 then some (.aa {2, 3, 4, 5, 6, 7, 8, 9} voteVal) else none
  | _ => none

/-- The scenario. -/
def scen : Scenario (Fin 9) ℕ Msg where
  byz := ↑F
  input := x
  adv := adv

lemma hF : ∀ j, j ∈ scen.byz ↔ j ∈ F := fun _ => Iff.rfl

lemma timely0 : (run 9 2 selPaper F x adv 3 0).timely = {2, 3, 4, 5, 6, 7, 8, 9} := by
  decide +kernel

lemma acc3_1 : (run 9 2 selPaper F x adv 3 1).acc = {2, 3, 4, 5, 6, 7, 8, 9} := by decide +kernel

lemma acc3_2 : (run 9 2 selPaper F x adv 3 2).acc = {1, 2, 3, 4, 5, 6, 7, 8, 9} := by
  decide +kernel

lemma acc5_paper : (run 9 2 selPaper F x adv 5 0).acc = ∅ := by decide +kernel

lemma acc5_dlpsw : (run 9 2 selDLPSW F x adv 5 0).acc = ∅ := by decide +kernel

end Cex9

/-- **Theorem 42 is false.** For `n = 9 > t² + 2t = 8`, `t = 2`, the modified Algorithm 5 with
`L = 7` rounds (4 approximation rounds), and in fact with any `L ≥ 5`, does not solve
order-preserving renaming (tight or not): in `Cex9.scen` the correct process `0` never decides. -/
theorem theorem_42_false :
    9 > 2 ^ 2 + 2 * 2 ∧ ∀ L ≥ 5, ∀ M,
      ¬ Solves (⊤ : SimpleGraph (Fin 9)) (alg 9 2 selPaper L) (atMost 2) (OPRenaming M) ∧
      ¬ Solves (⊤ : SimpleGraph (Fin 9)) (alg 9 2 selDLPSW L) (atMost 2) (OPRenaming M) := by
  have hbyz : Cex9.scen.byz ∈ (atMost 2 : AdvStructure (Fin 9)) := by
    simp [Cex9.scen, Set.ncard_coe_finset, Cex9.F]
  have hinj : Set.InjOn Cex9.scen.input Cex9.scen.honest := fun p _ q _ h => by
    simpa [Cex9.scen, Cex9.x, Fin.ext_iff] using h
  have hp : (0 : Fin 9) ∉ Cex9.scen.byz := by simp [Cex9.scen, Cex9.F]
  refine ⟨by norm_num, fun L hL M => ⟨?_, ?_⟩⟩
  · exact not_solves_of_acc_empty (fun _ _ _ h => h) Cex9.hF hbyz hinj hp Cex9.acc5_paper hL M
  · exact not_solves_of_acc_empty (fun _ _ _ h => h) Cex9.hF hbyz hinj hp Cex9.acc5_dlpsw hL M

end Podc.OrderPreservingByzRenaming.Alg5
