import Papers.PODC2015.KAtomicityVerification.Characterization

/-!
# Algorithm GPO ("greedy plus obligations"), Section 4

The algorithm constructs a `k`-atomic value order *from right to left*. It keeps the suffix `T`
built so far, the set `U` of values not yet placed and obligation sets `B[1] ⊆ … ⊆ B[k-1]`
(`B[i]` = values that must be placed within the next `i` positions). In each iteration:

* if some `B[i]` is full (`|B[i]| = i`), pick from the smallest full `B[ℓ]` the value whose write
  has the largest finish time, otherwise pick such a value from `U` (lines 5–10);
* prepend it to `T`, remove it from `U` (line 11);
* `W` := unplaced values having a read that `w(v)` happens before (line 12), `W'` := unplaced values
  whose write some `w(v')`, `v' ∈ W`, happens before (line 13);
* shift `B[j] := B[j+1] \ {v}`, `B[k-1] := (B[k-1] ∪ W ∪ W') \ {v}` (lines 14–17);
* return NO if some `B[i]` is overfull (`|B[i]| > i`, lines 18–19).

The loop `while U ≠ ∅` is modelled by `|V|` iterations of `step`, which is the identity once
`U = ∅`. Ties between equal finish times (impossible in the paper's model with distinct event
times) are broken by a linear order on `V`; the correctness proof does not depend on the
tie-break.
-/

set_option linter.unusedSectionVars false

namespace Podc.KAtomicityVerification

open Finset

variable {V R : Type*} [Fintype V] [LinearOrder V] [Fintype R]

/-- The state of GPO: the constructed suffix `T`, the unplaced values `U`, the obligation sets
`B i` (only `1 ≤ i ≤ k - 1` are used). -/
structure GState (V : Type*) where
  T : List V
  U : Finset V
  B : ℕ → Finset V

/-- Lines 1–3: the initial state. -/
def GState.init : GState V := ⟨[], univ, fun _ => ∅⟩

namespace History

variable (H : History V R)

instance : DecidableRel H.hb := fun a b => inferInstanceAs (Decidable (H.f a < H.s b))
instance : DecidableRel H.EW := fun _ _ => inferInstanceAs (Decidable (H.hb _ _))

/-- Finish time of the write of a value. -/
def wf (v : V) : ℕ := H.f (.inl v)

/-- A value of `S` whose write has the largest finish time. -/
def pickMax (S : Finset V) (h : S.Nonempty) : V :=
  (S.filter (fun v => ∀ u ∈ S, H.wf u ≤ H.wf v)).min' (by
    obtain ⟨v, hv, hmax⟩ := S.exists_max_image H.wf h
    exact ⟨v, by simp only [mem_filter]; exact ⟨hv, hmax⟩⟩)

lemma pickMax_spec (S : Finset V) (h : S.Nonempty) :
    H.pickMax S h ∈ S ∧ ∀ u ∈ S, H.wf u ≤ H.wf (H.pickMax S h) := by
  have := min'_mem (S.filter (fun v => ∀ u ∈ S, H.wf u ≤ H.wf v)) (by
    obtain ⟨v, hv, hmax⟩ := S.exists_max_image H.wf h
    exact ⟨v, by simp only [mem_filter]; exact ⟨hv, hmax⟩⟩)
  simp only [mem_filter] at this
  exact this

/-- Indices `1 ≤ i ≤ k - 1` of the full obligation sets (line 5). -/
def fullIdx (k : ℕ) (st : GState V) : Finset ℕ :=
  (Icc 1 (k - 1)).filter (fun i => (st.B i).card = i)

lemma mem_fullIdx {k : ℕ} {st : GState V} {i : ℕ} :
    i ∈ fullIdx k st ↔ 1 ≤ i ∧ i ≤ k - 1 ∧ (st.B i).card = i := by
  simp [fullIdx, and_assoc]

/-- Lines 5–10: the value chosen in the next iteration. -/
def choice (k : ℕ) (st : GState V) (hU : st.U.Nonempty) : V :=
  if hF : (fullIdx k st).Nonempty then
    H.pickMax (st.B ((fullIdx k st).min' hF)) (by
      have := min'_mem _ hF
      rw [mem_fullIdx] at this
      exact card_pos.1 (by omega))
  else H.pickMax st.U hU

/-- The set `W` of line 12 (computed after `v` has been removed from `U`). -/
def setW (U : Finset V) (v : V) : Finset V :=
  U.filter (fun v' => ∃ r : R, H.val r = v' ∧ H.hb (.inl v) (.inr r))

/-- The set `W'` of line 13. -/
def setW' (U W : Finset V) : Finset V :=
  U.filter (fun v'' => ∃ v' ∈ W, H.EW v' v'')

/-- Lines 11–17: the state after placing the chosen value (before the overfull test). -/
def next (k : ℕ) (st : GState V) (hU : st.U.Nonempty) : GState V :=
  let v := H.choice k st hU
  let U' := st.U.erase v
  let W := H.setW U' v
  let W' := H.setW' U' W
  { T := v :: st.T, U := U',
    B := fun j => if j = 0 then ∅ else if j < k - 1 then st.B (j + 1) \ {v}
      else if j = k - 1 then (st.B (k - 1) ∪ W ∪ W') \ {v} else ∅ }

/-- Line 18: some obligation set is overfull. -/
def Overfull (k : ℕ) (st : GState V) : Prop := ∃ i ∈ Icc 1 (k - 1), i < (st.B i).card

instance (k : ℕ) (st : GState V) : Decidable (Overfull k st) := by
  unfold Overfull; infer_instance

/-- One iteration of the outer loop; `none` means that GPO returned NO. -/
def step (k : ℕ) (st : GState V) : Option (GState V) :=
  if hU : st.U.Nonempty then
    if Overfull k (H.next k st hU) then none else some (H.next k st hU)
  else some st

/-- `n` iterations of the outer loop. -/
def run (k : ℕ) : ℕ → GState V → Option (GState V)
  | 0, st => some st
  | n + 1, st => (H.step k st).bind (run k n)


/-- **Algorithm 2 (GPO).** `true` = YES. The loop runs while `U ≠ ∅`, i.e. `|V|` times. -/
def gpo (k : ℕ) : Bool := (H.run k (Fintype.card V) GState.init).isSome

end History

end Podc.KAtomicityVerification
