import Papers.PODC2026.ConflictFreedom.Domain
import Podc.Foundations.Data.Mazurkiewicz.NTrace

/-!
# Traces of duplicate-free schedules form a GCA domain

Kuznetsov, Sutra and Toyos-Marfurt, *Conflict-Freedom as a Progress Condition*, PODC 2026,
Section 4.1: the prefix order on (Mazurkiewicz) traces is a meet-semilattice in which compatible
finite sets have least upper bounds; it is moreover coherent. We restrict to traces of
duplicate-free schedules, which is all Algorithms 1–2 ever manipulate (commands are unique).
-/

namespace Podc.ConflictFreedom

open Cslib.Mazurkiewicz

variable {α : Type*} {D : α → α → Prop} [Std.Symm D]

noncomputable instance : GCADomain (NTrace D) where
  lub := NTrace.lub
  isLUB_lub S h := NTrace.isLUB_lub h
  compat_of_pairwise S h := NTrace.compat_of_pairwise fun x hx y hy => by
    obtain ⟨z, hz⟩ := h x hx y hy
    exact ⟨z, hz x (by simp), hz y (by simp)⟩

lemma lub_eq (S : Finset (NTrace D)) : GCADomain.lub S = NTrace.lub S := rfl

lemma compat_iff (S : Set (NTrace D)) : Compat S ↔ ∃ z, ∀ x ∈ S, x ≤ z := Iff.rfl

end Podc.ConflictFreedom
