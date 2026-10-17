import Cslib.Computability.Distributed.SharedMemory.LinPoints
import Cslib.Computability.Distributed.SharedMemory.Linearization

/-!
# Retroactive linearization points

Generic tools (CSLib candidates), moved here from
`Papers/PODC2021/ScannableBinaryObjects/Impl1Lin.lean` (same names and namespace):

* `IsLinearization.insert`: a pending operation that does not change the state at the chosen
  position can be inserted into the middle of a linearization, provided no operation after
  the insertion point precedes it in real time (retroactive linearization points of read-only
  operations);
* `split_insert`, `split_cons_insert`: how a split `L = L₁ ++ L₂` survives such an insertion.

Used by `Papers/PODC2021/ScannableBinaryObjects` and `Papers/PODC2016/ConcurrentDSU`.
-/

set_option linter.unusedSectionVars false

-- CSLib candidate (whole file)
namespace Cslib.SharedMemory

open List

section Generic

variable {P : Type} {A : ObjSpec} [DecidableEq P]

-- CSLib candidate
/-- Retroactive linearization point: insert a pending operation `x` (which does not change the
state reached after `L₁`) between `L₁` and `L₂`, if nothing in `L₂` precedes `x`. -/
lemma IsLinearization.insert {α : List (Label P A)} {L₁ L₂ : List (OpId P × A.Op)}
    (hL : IsLinearization α (L₁ ++ L₂)) {x : OpId P} {o : A.Op} (hx : opOf α x = some o)
    (hxL : x ∉ (L₁ ++ L₂).map Prod.fst) (hxc : ¬ Completed α x)
    (hro : (A.δ (A.runOps A.init (L₁.map Prod.snd)) o).1 = A.runOps A.init (L₁.map Prod.snd))
    (h2 : ∀ y ∈ L₂, ¬ Precedes α y.1 x) : IsLinearization α (L₁ ++ (x, o) :: L₂) where
  nodup := by
    have := hL.nodup
    simp only [map_append, map_cons] at this hxL ⊢
    rw [nodup_middle, nodup_cons]
    exact ⟨hxL, this⟩
  op_eq y hy := by
    simp only [mem_append, mem_cons] at hy
    rcases hy with hy | rfl | hy
    · exact hL.op_eq y (mem_append_left _ hy)
    · exact hx
    · exact hL.op_eq y (mem_append_right _ hy)
  complete a ha := by
    have := hL.complete a ha
    simp only [map_append, map_cons, mem_append, mem_cons] at this ⊢
    tauto
  realtime a b hab hb := by
    have hsub : (L₁ ++ L₂).map Prod.fst <+ (L₁ ++ (x, o) :: L₂).map Prod.fst := by
      simp only [map_append, map_cons]
      exact Sublist.append_left (sublist_cons_self _ _) _
    by_cases hbx : b = x
    · subst hbx
      have ha := hL.complete a hab.completed
      have ha1 : a ∈ L₁.map Prod.fst := by
        simp only [map_append, mem_append] at ha
        rcases ha with ha | ha
        · exact ha
        · obtain ⟨y, hy, rfl⟩ := mem_map.1 ha
          exact absurd hab (h2 y hy)
      rw [sublist_pair_iff]
      exact ⟨L₁.map Prod.fst, (L₂.map Prod.fst).cons b, by simp, ha1, by simp⟩
    · have hb' : b ∈ (L₁ ++ L₂).map Prod.fst := by
        simp only [map_append, map_cons, mem_append, mem_cons] at hb ⊢
        rcases hb with hb | hb | hb
        · exact Or.inl hb
        · exact absurd hb hbx
        · exact Or.inr hb
      exact (hL.realtime a b hab hb').trans hsub
  seq := by
    have hs := hL.seq
    rw [seqOK_append] at hs ⊢
    refine ⟨hs.1, ?_, ?_⟩
    · intro r hr
      exact absurd (completed_iff_respOf.2 (by rw [hr]; rfl)) hxc
    · rw [hro]; exact hs.2

-- CSLib candidate
/-- A split `L = S₁ ++ S₂` survives the insertion of `z` at another split `L = W₁ ++ W₂`:
`z` lands either in the left part or in the right part. -/
lemma split_insert {X : Type} {S₁ S₂ W₁ W₂ : List X} (h : S₁ ++ S₂ = W₁ ++ W₂) (z : X) :
    ∃ S₁' S₂', W₁ ++ z :: W₂ = S₁' ++ S₂' ∧ (∀ y ∈ S₂', y ∈ S₂ ∨ y = z) ∧
      (∀ y ∈ S₂, y ∈ S₂') ∧ (S₁' = S₁ ∨ ∃ A B, S₁ = A ++ B ∧ S₁' = A ++ z :: B) := by
  rcases append_eq_append_iff.1 h with ⟨a', rfl, rfl⟩ | ⟨c', rfl, rfl⟩
  · -- `W₁ = S₁ ++ a'`, `S₂ = a' ++ W₂`
    refine ⟨S₁, a' ++ z :: W₂, by simp, ?_, ?_, Or.inl rfl⟩
    · intro y hy; simp only [mem_append, mem_cons] at hy ⊢; tauto
    · intro y hy; simp only [mem_append, mem_cons] at hy ⊢; tauto
  · -- `S₁ = W₁ ++ c'`, `W₂ = c' ++ S₂`
    refine ⟨W₁ ++ z :: c', S₂, by simp, fun y hy => Or.inl hy, fun y hy => hy,
      Or.inr ⟨W₁, c', rfl, rfl⟩⟩

-- CSLib candidate
/-- A split around an element, `L = L₁ ++ y :: L₂`, survives the insertion of `z` at another
split `L = W₁ ++ W₂`. -/
lemma split_cons_insert {X : Type} {L₁ L₂ W₁ W₂ : List X} {y : X}
    (h : L₁ ++ y :: L₂ = W₁ ++ W₂) (z : X) :
    ∃ L₁' L₂', W₁ ++ z :: W₂ = L₁' ++ y :: L₂' ∧
      (L₁' = L₁ ∨ ∃ A B, L₁ = A ++ B ∧ L₁' = A ++ z :: B) := by
  rcases append_eq_append_iff.1 h with ⟨a', rfl, h2⟩ | ⟨c', rfl, rfl⟩
  · rcases a' with _ | ⟨y', a'⟩
    · simp only [nil_append] at h2; subst h2
      exact ⟨L₁ ++ [z], L₂, by simp, Or.inr ⟨L₁, [], by simp, rfl⟩⟩
    · simp only [cons_append, cons.injEq] at h2
      obtain ⟨rfl, rfl⟩ := h2
      exact ⟨L₁, a' ++ z :: W₂, by simp, Or.inl rfl⟩
  · exact ⟨W₁ ++ z :: c', L₂, by simp, Or.inr ⟨W₁, c', rfl, rfl⟩⟩

end Generic

end Cslib.SharedMemory
