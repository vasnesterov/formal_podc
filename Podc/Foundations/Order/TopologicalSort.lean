/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Order.Extension.Linear
import Mathlib.Data.Finset.Sort
import Mathlib.Logic.Relation

/-! # Topological sorting of a finite acyclic relation

-- CSLib candidate: `Cslib/Foundations/Order/TopologicalSort.lean`

A relation `r` whose restriction to a finite set `s` has no cycle admits a *topological sort*:
a duplicate-free list enumerating exactly `s` in which every `r`-edge between members of `s` goes
forward. We obtain it from Szpilrajn's linear extension theorem (`extend_partialOrder`) and
`Finset.sort`.

## Main statements

* `Finset.exists_topologicalSort`: the list exists, with edges going forward in `List.idxOf`.
-/

namespace Finset

variable {α : Type*}

/-- The restriction of `r` to `s`. -/
def restrictRel (s : Finset α) (r : α → α → Prop) (a b : α) : Prop := a ∈ s ∧ b ∈ s ∧ r a b

/-- **Topological sort.** If `r` restricted to the finite set `s` has no cycle, then there is a
duplicate-free enumeration of `s` along which every `r`-edge between members of `s` goes forward. -/
theorem exists_topologicalSort [DecidableEq α] (s : Finset α) (r : α → α → Prop)
    (hacyc : ∀ a, ¬ Relation.TransGen (s.restrictRel r) a a) :
    ∃ l : List α, l.Nodup ∧ (∀ a, a ∈ l ↔ a ∈ s) ∧
      ∀ a b, a ∈ s → b ∈ s → r a b → l.idxOf a < l.idxOf b := by
  classical
  set p := Relation.ReflTransGen (s.restrictRel r) with hp
  have : IsPartialOrder α p :=
    { refl := fun _ => Relation.ReflTransGen.refl
      trans := fun _ _ _ h₁ h₂ => h₁.trans h₂
      antisymm := by
        intro a b h₁ h₂
        rcases Relation.reflTransGen_iff_eq_or_transGen.1 h₂ with h | h
        · exact h
        · exact absurd (h.trans_left h₁) (hacyc b) }
  obtain ⟨q, hq, hpq⟩ := extend_partialOrder p
  refine ⟨s.sort q, s.sort_nodup q, fun a => s.mem_sort q, ?_⟩
  intro a b ha hb hab
  have hne : a ≠ b := by
    rintro rfl
    exact hacyc a (Relation.TransGen.single ⟨ha, ha, hab⟩)
  have hqab : q a b := hpq a b (Relation.ReflTransGen.single ⟨ha, hb, hab⟩)
  set l := s.sort q
  have hal : a ∈ l := (s.mem_sort q).2 ha
  have hbl : b ∈ l := (s.mem_sort q).2 hb
  have hia := List.idxOf_lt_length_of_mem hal
  have hib := List.idxOf_lt_length_of_mem hbl
  rcases lt_trichotomy (l.idxOf a) (l.idxOf b) with h | h | h
  · exact h
  · exact absurd (by rw [← List.getElem_idxOf hia, ← List.getElem_idxOf hib]; simp [h]) hne
  · have hpw := List.pairwise_iff_getElem.1 (s.pairwise_sort q) _ _ hib hia h
    rw [List.getElem_idxOf, List.getElem_idxOf] at hpw
    exact absurd (Std.Antisymm.antisymm _ _ hqab hpw) hne

end Finset
