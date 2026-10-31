import Mathlib
import Cslib.Computability.Distributed.SharedMemory.LinPoints

-- CSLib candidate: Cslib/Computability/Distributed/SharedMemory/LinPoints.lean

/-!
# Retracting a speculative linearization point

`IsLinearization.erase`: a pending (not completed) entry can be removed from the middle of a
linearization if its removal does not change the legality of the rest. Two instances:

* `IsLinearization.erase_ro`: the entry is read-only at its position (a read, a failed
  compare&swap);
* `IsLinearization.erase_absorbed`: the next entry absorbs it (`δ (δ s o).1 o' = δ s o'`, e.g. a
  write immediately followed by another write).

Together with `IsLinearization.push` this supports *speculative* linearization points: linearize
an operation when it may have taken effect, and retract the entry when it turns out that it has
not (a crash before the response of a read, a write that is about to be re-executed...).
-/

namespace Cslib.SharedMemory

open List

variable {P : Type} {A : ObjSpec} [DecidableEq P]

/-- Remove a pending entry whose removal keeps the rest legal. -/
lemma IsLinearization.erase {α : List (Label P A)} {L₁ L₂ : List (OpId P × A.Op)}
    {x : OpId P} {o : A.Op} (hL : IsLinearization α (L₁ ++ (x, o) :: L₂))
    (hxc : ¬ Completed α x)
    (hseq : SeqOK α (A.δ (A.runOps A.init (L₁.map Prod.snd)) o).1 L₂ →
      SeqOK α (A.runOps A.init (L₁.map Prod.snd)) L₂) :
    IsLinearization α (L₁ ++ L₂) where
  nodup := by
    have := hL.nodup
    simp only [map_append, map_cons] at this ⊢
    exact (nodup_middle.1 this |> nodup_cons.1).2
  op_eq y hy := hL.op_eq y (by
    simp only [mem_append, mem_cons] at hy ⊢; tauto)
  complete a ha := by
    have := hL.complete a ha
    simp only [map_append, map_cons, mem_append, mem_cons] at this ⊢
    rcases this with h | h | h
    · exact Or.inl h
    · subst h; exact absurd ha hxc
    · exact Or.inr h
  realtime a b hab hb := by
    have hsub : (L₁ ++ L₂).map Prod.fst <+ (L₁ ++ (x, o) :: L₂).map Prod.fst := by
      simp only [map_append, map_cons]
      exact Sublist.append_left (sublist_cons_self _ _) _
    have hb' : b ∈ (L₁ ++ (x, o) :: L₂).map Prod.fst := hsub.subset hb
    have h := hL.realtime a b hab hb'
    have hax : a ≠ x := fun h => hxc (h ▸ hab.completed)
    have hbx : b ≠ x := by
      rintro rfl
      have := hL.nodup
      simp only [map_append, map_cons] at this hb
      rw [nodup_middle, nodup_cons] at this
      exact this.1 hb
    have hx1 : x ∉ L₁.map Prod.fst := by
      have := hL.nodup
      simp only [map_append, map_cons] at this
      rw [nodup_middle, nodup_cons] at this
      exact fun h => this.1 (mem_append_left _ h)
    have h' := h.erase x
    rw [List.erase_of_not_mem (by simp [Ne.symm hax, Ne.symm hbx])] at h'
    simpa [map_append, map_cons, List.erase_append_right _ hx1] using h'
  seq := by
    have hs := hL.seq
    rw [seqOK_append] at hs ⊢
    exact ⟨hs.1, hseq hs.2.2⟩

/-- Remove a pending entry that is read-only at its position. -/
lemma IsLinearization.erase_ro {α : List (Label P A)} {L₁ L₂ : List (OpId P × A.Op)}
    {x : OpId P} {o : A.Op} (hL : IsLinearization α (L₁ ++ (x, o) :: L₂))
    (hxc : ¬ Completed α x)
    (hro : (A.δ (A.runOps A.init (L₁.map Prod.snd)) o).1 = A.runOps A.init (L₁.map Prod.snd)) :
    IsLinearization α (L₁ ++ L₂) :=
  hL.erase hxc (fun h => by rwa [hro] at h)

/-- Remove a pending entry that the next entry absorbs. -/
lemma IsLinearization.erase_absorbed {α : List (Label P A)} {L₁ L₂ : List (OpId P × A.Op)}
    {x y : OpId P} {o o' : A.Op} (hL : IsLinearization α (L₁ ++ (x, o) :: (y, o') :: L₂))
    (hxc : ¬ Completed α x)
    (habs : A.δ (A.δ (A.runOps A.init (L₁.map Prod.snd)) o).1 o' =
      A.δ (A.runOps A.init (L₁.map Prod.snd)) o') :
    IsLinearization α (L₁ ++ (y, o') :: L₂) :=
  hL.erase hxc (fun h => by
    simp only [SeqOK] at h ⊢
    rw [habs] at h; exact h)

end Cslib.SharedMemory
