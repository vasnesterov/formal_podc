import Papers.PODC2019.RDMAAgreement.PMP.Steps
import Papers.PODC2019.RDMAAgreement.PMP.Counterexample

/-!
# Safety of the repaired Protected Memory Paxos: Theorems D.1, D.2, Lemma D.4

For the repaired algorithm (line 21 writes `(propNr, a, w)` with `(a, w)` the last phase-2 pair
the process issued, instead of `(propNr, ⊥, ⊥)`), every reachable state satisfies validity
(Theorem D.1) and agreement (Theorem D.2), for any number of processes and memories and any
schedule (asynchrony, zombie operations, arbitrary leader changes, processes that keep starting
attempts after deciding).

The proof is an inductive invariant (`Inv`, see `Invariant.lean`, preserved by every step in
`Steps.lean`): a Paxos `SafeAt` invariant whose "promises" are justified by the permission
mechanism (Lemma D.3).
-/

namespace Podc.RDMAAgreement.PMP

set_option linter.unusedSectionVars false

open Function

variable {P M V : Type*} [DecidableEq P] [DecidableEq M] [Fintype M]
variable {p1 : P} {inp : P → V}

theorem inv_step {s s' : State P M V} (h : Inv p1 inp s) (hs : Step p1 inp .repaired s s') :
    Inv p1 inp s' := by
  cases hs with
  | startFirst q hq hs _ hb hlt => exact inv_startFirst h q hq hs hb hlt
  | startNext q b _ hact hb hlt h2 => exact inv_startNext h q b hact hb hlt h2
  | invPerm q m hpc hl => exact inv_invPerm h q m hpc hl
  | effPerm q m hl => exact inv_effPerm h q m hl
  | effW1 q m sl hl hp => exact inv_effW1 h q m sl hl hp
  | effW1nak q m sl hl _ => exact inv_effW1nak h q m sl hl
  | effW2 q m b v hl hp => exact inv_effW2 h q m b v hl hp
  | effW2nak q m b v hl _ => exact inv_effW2nak h q m b v hl
  | effRd q m hl => exact inv_effRd h q m hl
  | dlvPerm q m hpc hl => exact inv_dlvPerm h q m hpc hl
  | dlvW1 q m hpc hl => exact inv_dlvW1 h q m hpc hl
  | dlvW1nak q m _ _ => exact inv_kill h q m
  | dlvRdAbort q m _ _ _ _ => exact inv_kill h q m
  | dlvRdNone q m f hpc hl hmp hn => exact inv_dlvRdNone h q m f hpc hl hmp hn
  | dlvRdKeep q m f r a y hpc hl hmp _ hmax hle =>
    exact inv_dlvRdKeep h q m f r a y hpc hl hmp hmax hle
  | dlvRdAdopt q m f r a y hpc hl hmp hr hmax hgt hp2 =>
    exact inv_dlvRdAdopt h q m f r a y hpc hl hmp hr hmax hgt hp2
  | dlvRdLate q m _ _ _ _ _ _ _ _ _ _ _ => exact inv_kill h q m
  | passFirst q m hpc hl hmaj hp2 => exact inv_passFirst h q m hpc hl hmaj hp2
  | passLate q m hpc hl _ hp2 => exact inv_passLate h q m hpc hl hp2
  | issueFirst q m hpc hl => exact inv_issueFirst h q m hpc hl
  | dlvW2 q m hpc hl _ => exact inv_dlvW2 h q m hpc hl
  | dlvW2Decide q m hpc hl hmaj => exact inv_dlvW2Decide h q m hpc hl hmaj
  | dlvW2nak q m _ _ => exact inv_kill h q m
  | discard q m r hpc hl => exact inv_discard h q m r hpc hl

theorem inv_init : Inv p1 inp (initState (M := M) p1 inp) where
  p2zero := rfl
  p2used _ _ h := by cases h
  p2inp _ _ h := by cases h
  safe _ _ h := by cases h
  voteP2 _ _ _ _ h := by cases h
  accMono _ _ _ _ h := by cases h
  slotP2 _ _ _ _ h := by cases h
  dec _ h := by cases h
  fresh _ _ _ _ := rfl
  inj _ _ _ h := by cases h
  loc p :=
    { unst := fun _ => rfl
      balUsed := fun h => by cases h
      balPos := fun h => by cases h
      p2cur := fun h => by cases h
      p2none := fun h => by cases h
      curInp := ⟨p, rfl⟩
      curMax := fun h => by cases h
      lastIss := fun _ _ h => by cases h
      done := fun h => by cases h
      slotMp := fun _ => le_rfl
      accLI := fun _ => AccLe.none_left _
      r2 := fun h => by cases h
      thr := fun _ => TInv.offIdle rfl }

theorem Reachable.inv {s : State P M V} (hs : Reachable p1 inp .repaired s) : Inv p1 inp s := by
  induction hs with
  | refl => exact inv_init
  | tail _ hst ih => exact inv_step ih hst

theorem Maj.inter {Q W : Finset M} (hQ : Maj Q) (hW : Maj W) : ∃ m, m ∈ Q ∧ m ∈ W := by
  by_contra hne
  push Not at hne
  have hdis : Disjoint Q W := Finset.disjoint_left.mpr hne
  have h1 := Finset.card_union_of_disjoint hdis
  have h2 := Finset.card_le_univ (Q ∪ W)
  unfold Maj at hQ hW
  omega

theorem Maj.nonempty {W : Finset M} (hW : Maj W) : ∃ m, m ∈ W := by
  obtain ⟨m, hm, -⟩ := hW.inter hW
  exact ⟨m, hm⟩

/-- **Theorem D.1 (validity)** for the repaired Protected Memory Paxos: every decided value is
the input of some process. -/
theorem theorem_D1 {s : State P M V} (hs : Reachable p1 inp .repaired s) :
    ∀ v ∈ s.decs, ∃ q, inp q = v := by
  intro v hv
  have h := hs.inv
  obtain ⟨p, b, W, hW, hWm⟩ := h.dec v hv
  obtain ⟨m, hm⟩ := hW.nonempty
  exact h.p2inp b v (h.voteP2 _ _ _ _ (hWm m hm))

/-- **Lemma D.4** for the repaired Protected Memory Paxos: two successful line-35 writes with the
same proposal number carry the same value. -/
theorem lemma_D4 {s : State P M V} (hs : Reachable p1 inp .repaired s) {m m' : M} {r r' : P}
    {b : ℕ} {x x' : V} (hv : (m, r, b, x) ∈ s.votes) (hv' : (m', r', b, x') ∈ s.votes) :
    x = x' := by
  have h := hs.inv
  have h1 := h.voteP2 _ _ _ _ hv
  rw [h.voteP2 _ _ _ _ hv'] at h1
  exact (Option.some.inj h1).symm

theorem agree_aux {s : State P M V} (h : Inv p1 inp s) {p p' : P} {b b' : ℕ} {W W' : Finset M}
    {v w : V} (hW : Maj W) (hWm : ∀ m ∈ W, (m, p, b, v) ∈ s.votes) (hW' : Maj W')
    (hWm' : ∀ m ∈ W', (m, p', b', w) ∈ s.votes) (hbb : b ≤ b') : v = w := by
  obtain ⟨m, hm⟩ := hW.nonempty
  obtain ⟨m', hm'⟩ := hW'.nonempty
  have hv := h.voteP2 _ _ _ _ (hWm m hm)
  have hw := h.voteP2 _ _ _ _ (hWm' m' hm')
  rcases hbb.lt_or_eq with hlt | rfl
  · have hb0 : 0 < b := by
      rcases Nat.eq_zero_or_pos b with rfl | hpos
      · rw [h.p2zero] at hv; cases hv
      · exact hpos
    obtain ⟨Q, hQ, hQm⟩ := h.safe b' w hw b hb0 hlt
    obtain ⟨m1, hm1Q, hm1W⟩ := hQ.inter hW
    rcases hQm m1 hm1Q with ⟨r, hr⟩ | ⟨hno, -⟩
    · have := h.voteP2 _ _ _ _ hr
      rw [hv] at this
      exact Option.some.inj this
    · exact absurd (hWm m1 hm1W) (hno p v)
  · rw [hv] at hw; exact Option.some.inj hw

/-- **Theorem D.2 (agreement)** for the repaired Protected Memory Paxos: any two decisions (by
the same or by different processes, at any times) are equal. -/
theorem theorem_D2 {s : State P M V} (hs : Reachable p1 inp .repaired s) :
    ∀ v ∈ s.decs, ∀ w ∈ s.decs, v = w := by
  intro v hv w hw
  have h := hs.inv
  obtain ⟨p, b, W, hW, hWm⟩ := h.dec v hv
  obtain ⟨p', b', W', hW', hWm'⟩ := h.dec w hw
  rcases le_total b b' with hbb | hbb
  · exact agree_aux h hW hWm hW' hWm' hbb
  · exact (agree_aux h hW' hWm' hW hWm hbb).symm

namespace Counterexample

/-- `p2` decides `true` (first 13 actions of `schedule`). -/
def scheduleDecide : List (Act (Fin 2) (Fin 1)) := schedule.take 13

theorem decide_repaired :
    (run (0 : Fin 2) Counterexample.inp .repaired scheduleDecide (initState 0 Counterexample.inp)).map State.decs =
      some [true] := by
  decide +kernel

end Counterexample

open Counterexample in
/-- Non-vacuity: the repaired algorithm has executions in which a process decides. -/
theorem repaired_nonvacuous :
    ∃ s : State (Fin 2) (Fin 1) Bool, Reachable (0 : Fin 2) Counterexample.inp .repaired s ∧ s.decs = [true] := by
  have h := decide_repaired
  simp only [Option.map_eq_some_iff] at h
  obtain ⟨s, hs, hd⟩ := h
  exact ⟨s, run_sound _ _ _ _ _ _ hs, hd⟩

end Podc.RDMAAgreement.PMP
