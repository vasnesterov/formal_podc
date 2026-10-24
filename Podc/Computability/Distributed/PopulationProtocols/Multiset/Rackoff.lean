/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
-- CSLib candidate: Cslib/Computability/Distributed/PopulationProtocols/Multiset/Rackoff.lean
import Podc.Computability.PetriNets.Rackoff
import Podc.Computability.Distributed.PopulationProtocols.Multiset.PotentialReach

/-!
# Short covering sequences in population protocols

Rackoff's bound (`Cslib.PetriNet.exists_short_cover`) specialised to multiset population
protocols: a population protocol is a Petri net whose places are the states and whose
transitions consume and produce two agents each.

## Main definitions

* `Transition.petriNet`: the Petri net of the transitions over `Q`.
* `countVec C`: the vector of state counts of a configuration `C`.

## Main statements

* `FiresSeq.valid_run`, `exists_firesSeq_of_valid`: firing sequences are exactly the
  sequences valid for all places of the Petri net.
* `MReach.exists_short_cover_le`: if `C` reaches a configuration `≥ D`, then it does so by
  a firing sequence of length at most `rackoffBound 2 R |Q|`, where `R` bounds the counts of `D`.
* `MReach.exists_short_cover`: if `C` reaches a configuration containing `q`, then it does so by
  a firing sequence of length at most `2 ^ (2 * (2 |Q| + 1)!)`.
-/

namespace Cslib.PopulationProtocol

open Cslib.PetriNet

variable {Q : Type*} [DecidableEq Q]

/-- The Petri net of population-protocol transitions: places are states, and a transition
consumes its pre-multiset and produces its post-multiset. -/
def Transition.petriNet : PetriNet Q (Transition Q) where
  pre t q := t.pre.count q
  post t q := t.post.count q

/-- The vector of state counts of a configuration. -/
def countVec (C : Multiset Q) : Q → ℤ := fun q => C.count q

theorem Transition.petriNet_pre_le (t : Transition Q) (q : Q) :
    (Transition.petriNet (Q := Q)).pre t q ≤ 2 := by
  simpa [Transition.petriNet] using Multiset.count_le_card q t.pre

theorem Transition.Fires.fire_countVec {t : Transition Q} {C C' : Multiset Q}
    (h : t.Fires C C') : Transition.petriNet.fire t (countVec C) = countVec C' := by
  funext q
  simp only [PetriNet.fire, countVec, Transition.petriNet, h.count_eq q, Transition.delta]
  ring

/-- A firing sequence is valid for all places, and its run computes the final counts. -/
theorem FiresSeq.valid_run [Fintype Q] {w : List (Transition Q)} {C C' : Multiset Q}
    (h : FiresSeq w C C') :
    Transition.petriNet.Valid Finset.univ w (countVec C) ∧
      Transition.petriNet.run w (countVec C) = countVec C' := by
  induction w generalizing C with
  | nil => simp only [firesSeq_nil] at h; subst h; exact ⟨trivial, rfl⟩
  | cons t w ih =>
    obtain ⟨C₁, h₁, hw⟩ := h
    refine ⟨⟨fun q _ => ?_, ?_⟩, ?_⟩
    · simp only [Transition.petriNet, countVec]
      exact_mod_cast Multiset.count_le_of_le q h₁.1
    · rw [h₁.fire_countVec]; exact (ih hw).1
    · rw [PetriNet.run_cons, h₁.fire_countVec]; exact (ih hw).2

/-- A sequence valid for all places is a firing sequence. -/
theorem exists_firesSeq_of_valid [Fintype Q] {w : List (Transition Q)} {C : Multiset Q}
    (h : Transition.petriNet.Valid Finset.univ w (countVec C)) :
    ∃ C', FiresSeq w C C' ∧ Transition.petriNet.run w (countVec C) = countVec C' := by
  induction w generalizing C with
  | nil => exact ⟨C, rfl, rfl⟩
  | cons t w ih =>
    obtain ⟨hpre, hw⟩ := h
    have hle : t.pre ≤ C := Multiset.le_iff_count.2 fun q => by
      have := hpre q (Finset.mem_univ q)
      simp only [Transition.petriNet, countVec] at this
      exact_mod_cast this
    have hf : t.Fires C (C - t.pre + t.post) := ⟨hle, rfl⟩
    rw [hf.fire_countVec] at hw
    obtain ⟨C', hC', hrun⟩ := ih hw
    exact ⟨C', ⟨_, hf, hC'⟩, by rw [PetriNet.run_cons, hf.fire_countVec, hrun]⟩

/-- **Short covering sequences (Rackoff).** If `C` reaches some configuration `C' ≥ D` through
`T`, and every count of `D` is at most `R`, then `C` reaches some configuration `C'' ≥ D` through
`T` by a firing sequence of length at most `rackoffBound 2 R |Q|`. -/
theorem MReach.exists_short_cover_le [Fintype Q] {T : Set (Transition Q)} {C C' D : Multiset Q}
    {R : ℕ} (h : MReach T C C') (hD : D ≤ C') (hR : ∀ q, D.count q ≤ R) :
    ∃ w C'', (∀ t ∈ w, t ∈ T) ∧ FiresSeq w C C'' ∧ D ≤ C'' ∧
      w.length ≤ rackoffBound 2 R (Fintype.card Q) := by
  obtain ⟨w, hwT, hw⟩ := h.exists_firesSeq
  obtain ⟨hv, hrun⟩ := hw.valid_run
  have hc : Transition.petriNet.Covers Finset.univ w (countVec C) (fun q => D.count q) := by
    intro q _
    rw [hrun]
    simp only [countVec]
    exact_mod_cast Multiset.count_le_of_le q hD
  obtain ⟨w', hsub, hv', hc', hlen⟩ :=
    PetriNet.exists_short_cover (Transition.petriNet_pre_le) hR hv hc
  obtain ⟨C'', hC'', hrun'⟩ := exists_firesSeq_of_valid hv'
  refine ⟨w', C'', fun t ht => hwT t (hsub.subset ht), hC'', ?_, ?_⟩
  · refine Multiset.le_iff_count.2 fun q => ?_
    have := hc' q (Finset.mem_univ q)
    rw [hrun'] at this
    simp only [countVec] at this
    exact_mod_cast this
  · simpa using hlen

/-- **Short covering sequences (Rackoff).** If `C` reaches through `T` a configuration
containing the state `q`, then it reaches through `T` a configuration containing `q` by a firing
sequence of length at most `2 ^ (2 * (2 |Q| + 1)!)`. -/
theorem MReach.exists_short_cover [Fintype Q] {T : Set (Transition Q)} {C C' : Multiset Q} {q : Q}
    (h : MReach T C C') (hq : q ∈ C') :
    ∃ w C'', (∀ t ∈ w, t ∈ T) ∧ FiresSeq w C C'' ∧ q ∈ C'' ∧
      w.length ≤ 2 ^ (2 * (2 * Fintype.card Q + 1).factorial) := by
  have hD : ({q} : Multiset Q) ≤ C' := Multiset.singleton_le.2 hq
  obtain ⟨w, C'', hwT, hw, hle, hlen⟩ := h.exists_short_cover_le hD (R := 2) fun p => by
    rw [Multiset.count_singleton]; split_ifs <;> omega
  exact ⟨w, C'', hwT, hw, Multiset.singleton_le.1 hle,
    hlen.trans (rackoffBound_two_two_le _)⟩

end Cslib.PopulationProtocol
