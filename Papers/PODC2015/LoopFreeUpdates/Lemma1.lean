import Papers.PODC2015.LoopFreeUpdates.Rounds

/-!
# Lemma 1 for `FF` nodes, read literally, is false

Lemma 1 of the paper: "If there exists a 3-round update schedule S which updates any nodes
`V′ ⊆ V` of type FB, then there is also a 3-round update schedule which updates all nodes of `V′` in
the first round. The same holds true for nodes of type FF."

Every schedule updates every node, so taken literally (with `V′` = all `FF` nodes) the `FF` part says
that all `FF` nodes can go to round 1. That is false (it would also make the 3-round problem trivial:
see the paper's own Fig. 4). The proof only moves nodes *from round 2* to round 1, which is correct
(`Instance.lemma_1`). Here is a 7-node instance with a 3-round schedule but none with both `FF` nodes in
round 1.
-/

set_option linter.unusedSectionVars false

namespace Podc.LoopFreeUpdates

open Relation

namespace Instance

variable {V : Type*} [DecidableEq V] (I : Instance V)

/-- A decision procedure for strongly loop-free schedules on concrete instances: check all walks. -/
theorem isSLF_of_check (rounds : List (Finset V)) (N : ℕ) (hs : I.IsSchedule rounds)
    (h : ∀ t (ht : t < rounds.length), ∀ X ∈ rounds[t].powerset, ∀ v ∈ I.old,
      I.iterFrom (done rounds t ∪ X) v N = none) : I.IsSLF rounds :=
  ⟨hs, fun t ht X hX => I.loopFree_of_iterFrom N (h t ht X (Finset.mem_powerset.2 hX))⟩

end Instance

/-- The instance: old route `0, 1, …, 6`, new route `0, 5, 4, 1, 3, 2, 6`. -/
def lemma1Instance : Instance ℕ where
  old := List.range 7
  new := [0, 5, 4, 1, 3, 2, 6]
  nodup := List.nodup_range
  perm := by decide
  ne_nil := by decide
  head_eq := by decide
  getLast_eq := by decide

/-- Its `FF` nodes are `0` and `1` (node `2` is `FB`, `3` and `4` are `BB`, `5` is `BF`). -/
theorem lemma1Instance_FF : lemma1Instance.ofType lemma1Instance.IsFF = {0, 1} := by decide

theorem lemma1Instance_hasSLF : lemma1Instance.HasSLF 3 :=
  ⟨[{2}, {3, 4}, {0, 1, 5}], rfl,
    lemma1Instance.isSLF_of_check _ 7 (by unfold Instance.IsSchedule; decide) (by decide)⟩

/-- **Lemma 1 (`FF` part, literal reading) is false**: the instance has a 3-round schedule, but no
3-round schedule updates all its `FF` nodes in the first round. -/
theorem lemma_1_FF_literal_false :
    lemma1Instance.HasSLF 3 ∧
      ¬ ∃ rounds : List (Finset ℕ), ∃ h : rounds.length = 3, lemma1Instance.IsSLF rounds ∧
        lemma1Instance.ofType lemma1Instance.IsFF ⊆ rounds[0] := by
  refine ⟨lemma1Instance_hasSLF, ?_⟩
  rintro ⟨rounds, hlen, h, hFF⟩
  rw [lemma1Instance_FF] at hFF
  have h1 : 1 ∈ rounds[0] := hFF (by simp)
  have hBB : ∀ v, lemma1Instance.IsBB v → v ∈ rounds[1] := by
    intro v hv
    obtain ⟨i, hi, hvi⟩ := lemma1Instance.exists_round h.1 hv.1
    have : i = 0 ∨ i = 1 ∨ i = 2 := by omega
    rcases this with rfl | rfl | rfl
    · exact absurd (lemma1Instance.dashedFwd_of_mem_first h hi hvi hv.1) hv.2.1
    · exact hvi
    · exact absurd (lemma1Instance.solidFwd_of_mem_last h (t := 2) (by omega) hvi hv.1) hv.2.2
  have h3 : 3 ∉ rounds[0] := fun h3 =>
    Finset.disjoint_left.1 (lemma1Instance.disjoint_rounds h.1 (i := 0) (j := 1) (by omega)
      (by omega) (by omega)) h3 (hBB 3 (by decide))
  have h4 : 4 ∈ rounds[1] := hBB 4 (by decide)
  have hlf := h.2 1 (by omega) {4} (Finset.singleton_subset_iff.2 h4)
  have hd : Instance.done rounds 1 = rounds[0] := by
    ext v; simp only [Instance.mem_done]
    constructor
    · rintro ⟨i, hi, hi1, hv⟩
      obtain rfl : i = 0 := by omega
      exact hv
    · intro hv; exact ⟨0, by omega, by omega, hv⟩
  rw [hd] at hlf
  -- the loop 1 ⇢ 3 → 4 ⇢ 1
  apply hlf 1
  have s1 : lemma1Instance.Step (rounds[0] ∪ {4}) 1 3 := by
    unfold Instance.Step
    rw [lemma1Instance.fwd_of_mem (Finset.mem_union_left _ h1)]; decide
  have s3 : lemma1Instance.Step (rounds[0] ∪ {4}) 3 4 := by
    unfold Instance.Step
    rw [lemma1Instance.fwd_of_not_mem (by simp [h3])]; decide
  have s4 : lemma1Instance.Step (rounds[0] ∪ {4}) 4 1 := by
    unfold Instance.Step
    rw [lemma1Instance.fwd_of_mem (by simp)]; decide
  exact TransGen.head s1 (TransGen.head s3 (TransGen.single s4))

end Podc.LoopFreeUpdates
