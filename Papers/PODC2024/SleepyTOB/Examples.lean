import Papers.PODC2024.SleepyTOB.ExtendedGA

/-!
# Small examples: the literal integrity property, and why graded consistency alone does not lock

D'Amato, Losa, Zanolini, PODC 2024.

* `integrity_literal_false`: Definition 4 states integrity as "if a well-behaved process outputs
  a log with any grade, then there exists a well-behaved process that *inputs the log*". Taken
  literally this fails for every graded agreement with validity: a single honest process with input
  `[1]` outputs `[]` with grade 1. The intended property (as in [MMR] and in the proof of Lemma 1) is
  that some honest input *extends* the log; that is what `lemma_1` proves.
* `graded_consistency_insufficient`: the proof of Lemma 3 derives the base case "all processes in
  `H_r` vote for an extension of the decided `Λ`" from graded consistency alone. Graded consistency
  only gives the other honest processes `Λ` with grade `≥ 0`, and bounded divergence allows them a
  second, conflicting and *longer* grade-0 output, which becomes their `L_{v-1}`. Below: 7 honest
  processes (5 voting `[1]`, 2 voting `[2,5]`) and 2 Byzantine processes that vote `[1]` towards `p`
  and `[2,5]` towards `q`; `p` outputs `[1]` with grade 1 while `q`'s longest output is `[2,5]`. The
  repair (`Exec.Follows.decision_lock`) uses integrity of `GA_{v-1,2}` and uniqueness of
  `GA_{v-1,1}`, as in [MMR]'s safety proof.
-/

namespace Podc.SleepyTOB

open Finset

noncomputable section
open Classical

/-- A one-process instance of the extended graded agreement (synchronous, quorum holds). -/
def oneProcGA : ExtGA (Fin 1) ℕ where
  H := univ
  B := ∅
  Hnext := univ
  P0 := ∅
  input _ := [1]
  M0 _ _ := none
  R _ _ := {[1]}
  disjoint_H_B := disjoint_empty_right _
  disjoint_Hnext_B := disjoint_empty_right _
  M0_mem _ _ h := absurd rfl h
  R_asleep _ q h := (h (by convert Finset.mem_union_left (∅ : Finset (Fin 1)) (mem_univ q))).elim
  R_honest _ _ _ := subset_refl _

/-- Integrity as literally stated in Definition 4 ("some well-behaved process inputs the log")
fails for the extended graded agreement (already for the plain one, `M0 = ∅`). -/
theorem integrity_literal_false :
    oneProcGA.Quorum ∧ oneProcGA.Sync ∧
    ¬ (∀ p ∈ oneProcGA.Hnext, ∀ Λ, Outputs (oneProcGA.M p) Λ →
        ∃ q ∈ oneProcGA.H, oneProcGA.input q = Λ) := by
  have hq : oneProcGA.Quorum := by
    unfold ExtGA.Quorum ExtGA.O; simp [oneProcGA]
  have hs : oneProcGA.Sync := fun _ _ _ _ => rfl
  refine ⟨hq, hs, fun h => ?_⟩
  have hg := (lemma_1 oneProcGA hq hs).validity [] (fun _ _ => List.nil_prefix) 0 (mem_univ 0)
  obtain ⟨q, -, hq'⟩ := h 0 (mem_univ 0) [] hg.outputs
  simp [oneProcGA] at hq'

/-- True votes of the 9-process example: `0–4` vote `[1]`, the others `[2,5]`. -/
def gcHonestVote (q : Fin 9) : List ℕ := if q.val < 5 then [1] else [2, 5]

/-- Honest processes `0–6`. -/
def gcHonest : Finset (Fin 9) := {0, 1, 2, 3, 4, 5, 6}

/-- What `p` counts: Byzantine `7, 8` vote `[1]`. -/
def gcTallyP : Votes (Fin 9) ℕ := fun q => if q.val < 7 then some (gcHonestVote q) else some [1]

/-- What `q` counts: Byzantine `7, 8` vote `[2,5]`. -/
def gcTallyQ : Votes (Fin 9) ℕ := fun q => if q.val < 7 then some (gcHonestVote q) else some [2, 5]

theorem gc_faithful_P : Faithful gcTallyP univ gcHonest gcHonestVote :=
  ⟨subset_univ _, fun q hq => by
    fin_cases q <;> simp_all [gcHonest, gcTallyP]⟩

theorem gc_faithful_Q : Faithful gcTallyQ univ gcHonest gcHonestVote :=
  ⟨subset_univ _, fun q hq => by
    fin_cases q <;> simp_all [gcHonest, gcTallyQ]⟩

/-- Graded consistency does not by itself give the other honest processes a longest output
extending a grade-1 log: two faithful tallies of the same honest votes (`|H| = 7 > 2·9/3`), `p`
outputs `[1]` with grade 1, `q` outputs `[1]` (with grade 0, as graded consistency demands) but its
longest output is the conflicting `[2,5]`. -/
theorem graded_consistency_insufficient :
    Faithful gcTallyP univ gcHonest gcHonestVote ∧ Faithful gcTallyQ univ gcHonest gcHonestVote ∧
    2 * #(univ : Finset (Fin 9)) < 3 * #gcHonest ∧
    Grade1 gcTallyP [1] ∧ Outputs gcTallyQ [1] ∧ IsLongest (Outputs gcTallyQ) [2, 5] ∧
    Conflict [2, 5] [1] := by
  have hH : 2 * #(univ : Finset (Fin 9)) < 3 * #gcHonest := by decide
  have hg : Grade1 gcTallyP [1] := by
    refine grade1_of_subset_votesFor (U := univ) (H' := {0, 1, 2, 3, 4, 7, 8}) (subset_univ _)
      ?_ (by decide)
    intro q hq
    simp only [votesFor, mem_filter, mem_univ, true_and]
    fin_cases q <;> simp_all [gcTallyP, gcHonestVote]
  have hvoters : ∀ M : Votes (Fin 9) ℕ, #(voters M) ≤ 9 := fun M =>
    (card_le_card (subset_univ _)).trans (by simp)
  have hout : ∀ Λ (H' : Finset (Fin 9)), 3 < #H' → H' ⊆ votesFor gcTallyQ Λ →
      Outputs gcTallyQ Λ := fun Λ H' hc hs => by
    have := card_le_card hs; have := hvoters gcTallyQ; unfold Outputs; omega
  refine ⟨gc_faithful_P, gc_faithful_Q, hH, hg, ?_, ⟨?_, ?_⟩, ?_⟩
  · refine hout _ {0, 1, 2, 3, 4} (by decide) ?_
    intro q hq
    simp only [votesFor, mem_filter, mem_univ, true_and]
    fin_cases q <;> simp_all [gcTallyQ, gcHonestVote]
  · refine hout _ {5, 6, 7, 8} (by decide) ?_
    intro q hq
    simp only [votesFor, mem_filter, mem_univ, true_and]
    fin_cases q <;> simp_all [gcTallyQ, gcHonestVote]
  · intro L hL
    have hne : (votesFor gcTallyQ L).Nonempty := by
      rw [← card_pos]; unfold Outputs at hL; omega
    obtain ⟨q, hq⟩ := hne
    simp only [votesFor, mem_filter, mem_univ, true_and] at hq
    obtain ⟨l, hl, hL'⟩ := hq
    refine hL'.length_le.trans ?_
    fin_cases q <;> simp [gcTallyQ, gcHonestVote] at hl <;> subst hl <;> simp
  · simp [Conflict, Compatible]

end

end Podc.SleepyTOB
