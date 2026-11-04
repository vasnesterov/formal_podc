import Mathlib.Data.List.Nodup
import Mathlib.Order.WithBot

/-!
# Auxiliary list lemmas

Small facts about sublists, filters of sorted lists and `flatMap`, used to assemble the
linearization in the proof of Lemma 4.5.
-/

-- CSLib candidate: Mathlib-style list lemmas (`Mathlib/Data/List/...`)

namespace Podc.WritableObjects

open List

variable {X Y : Type}

/-- In a list without duplicates, two elements cannot occur in both orders. -/
lemma not_sublist_pair_both {l : List X} (hl : l.Nodup) {a b : X} (h1 : [a, b] <+ l)
    (h2 : [b, a] <+ l) : False := by
  induction l with
  | nil => simp at h1
  | cons c l ih =>
    rw [List.nodup_cons] at hl
    rcases List.sublist_cons_iff.1 h1 with k1 | ⟨r, hr, h1'⟩ <;>
      rcases List.sublist_cons_iff.1 h2 with k2 | ⟨r', hr', h2'⟩
    · exact ih hl.2 k1 k2
    · simp only [List.cons.injEq] at hr'
      obtain ⟨rfl, rfl⟩ := hr'
      exact hl.1 (k1.subset (show b ∈ [a, b] by simp))
    · simp only [List.cons.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      exact hl.1 (k2.subset (show a ∈ [b, a] by simp))
    · simp only [List.cons.injEq] at hr hr'
      obtain ⟨rfl, rfl⟩ := hr
      obtain ⟨hb, rfl⟩ := hr'
      subst hb
      exact hl.1 (h1'.subset (by simp))

/-- A sublist of the first components lifts to the list of pairs. -/
lemma sublist_pair_of_fst {L : List (X × Y)} (hL : (L.map Prod.fst).Nodup) {a b : X × Y}
    (ha : a ∈ L) (hb : b ∈ L) (h : [a.1, b.1] <+ L.map Prod.fst) : [a, b] <+ L := by
  induction L with
  | nil => simp at ha
  | cons c L ih =>
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hL
    simp only [List.map_cons] at h
    rcases List.sublist_cons_iff.1 h with h | ⟨r, hr, h'⟩
    · have hx1 : a.1 ∈ L.map Prod.fst := h.subset (show a.1 ∈ [a.1, b.1] by simp)
      have hx2 : b.1 ∈ L.map Prod.fst := h.subset (show b.1 ∈ [a.1, b.1] by simp)
      have ha' : a ∈ L := by
        rcases List.mem_cons.1 ha with rfl | ha
        · exact absurd (List.mem_map.1 hx1) hL.1
        · exact ha
      have hb' : b ∈ L := by
        rcases List.mem_cons.1 hb with rfl | hb
        · exact absurd (List.mem_map.1 hx2) hL.1
        · exact hb
      exact (ih hL.2 ha' hb' h).cons c
    · simp only [List.cons.injEq] at hr
      obtain ⟨hac, rfl⟩ := hr
      have hb1 : b.1 ∈ L.map Prod.fst := h'.subset (by simp)
      have ha' : a = c := by
        rcases List.mem_cons.1 ha with rfl | ha
        · rfl
        · exact absurd ⟨a, ha, hac⟩ hL.1
      subst ha'
      have hb' : b ∈ L := by
        rcases List.mem_cons.1 hb with rfl | hb
        · obtain ⟨z, hz, hz'⟩ := List.mem_map.1 hb1
          exact absurd ⟨z, hz, hz'⟩ hL.1
        · exact hb
      exact List.Sublist.cons_cons a (List.singleton_sublist.2 hb')

/-- The elements with a given key form a contiguous block of a list sorted by keys. -/
lemma exists_filter_infix [LinearOrder Y] (g : X → Y) (c : Y) {l : List X}
    (hl : l.Pairwise (fun x y => g x ≤ g y)) :
    ∃ A B, l = A ++ l.filter (fun x => decide (g x = c)) ++ B ∧ (∀ x ∈ A, g x < c) ∧
      (∀ x ∈ B, c < g x) := by
  induction l with
  | nil => exact ⟨[], [], by simp, by simp, by simp⟩
  | cons a l ih =>
    rw [List.pairwise_cons] at hl
    obtain ⟨A, B, h1, h2, h3⟩ := ih hl.2
    rcases lt_trichotomy (g a) c with hlt | heq | hgt
    · refine ⟨a :: A, B, ?_, ?_, h3⟩
      · rw [List.filter_cons_of_neg (by simp [hlt.ne])]
        simp only [List.cons_append]
        exact congrArg _ h1
      · intro x hx
        rcases List.mem_cons.1 hx with rfl | hx
        · exact hlt
        · exact h2 x hx
    · have hA : A = [] := by
        rcases A with _ | ⟨x, A⟩
        · rfl
        · exfalso
          have hx : x ∈ l := by rw [h1]; simp
          have := hl.1 x hx
          have := h2 x (by simp)
          rw [← heq] at this
          exact absurd (lt_of_le_of_lt ‹g a ≤ g x› this) (lt_irrefl _)
      subst hA
      refine ⟨[], B, ?_, by simp, h3⟩
      rw [List.filter_cons_of_pos (by simp [heq])]
      simp only [List.nil_append, List.cons_append]
      exact congrArg _ (by simpa using h1)
    · refine ⟨[], a :: l, ?_, by simp, ?_⟩
      · have : (a :: l).filter (fun x => decide (g x = c)) = [] := by
          rw [List.filter_eq_nil_iff]
          intro x hx
          rcases List.mem_cons.1 hx with rfl | hx
          · simp [hgt.ne']
          · have := hl.1 x hx; simp [(lt_of_lt_of_le hgt this).ne']
        rw [this]; simp
      · intro x hx
        rcases List.mem_cons.1 hx with rfl | hx
        · exact hgt
        · exact lt_of_lt_of_le hgt (hl.1 x hx)

/-- An element that comes before all others is the head. -/
lemma eq_cons_of_first {l : List X} (hl : l.Nodup) {h : X} (hh : h ∈ l)
    (hfirst : ∀ z ∈ l, z ≠ h → [h, z] <+ l) : ∃ rest, l = h :: rest := by
  rcases l with _ | ⟨c, l⟩
  · simp at hh
  · by_cases hc : c = h
    · exact ⟨l, by rw [hc]⟩
    · exfalso
      have := hfirst c (by simp) hc
      rw [List.nodup_cons] at hl
      rcases List.sublist_cons_iff.1 this with h1 | ⟨r, hr, h1⟩
      · exact hl.1 (h1.subset (by simp))
      · simp only [List.cons.injEq] at hr
        exact hc hr.1.symm

/-- Elements of earlier blocks come before elements of later blocks of a `flatMap` over a
strictly increasing list. -/
lemma sublist_flatMap_of_lt {l : List ℕ} (hl : l.Pairwise (· < ·)) (f : ℕ → List X)
    {m n : ℕ} (hm : m ∈ l) (hn : n ∈ l) (hmn : m < n) {a b : X} (ha : a ∈ f m) (hb : b ∈ f n) :
    [a, b] <+ l.flatMap f := by
  induction l with
  | nil => simp at hm
  | cons c l ih =>
    rw [List.pairwise_cons] at hl
    rw [List.flatMap_cons]
    rcases List.mem_cons.1 hm with rfl | hm'
    · have hn' : n ∈ l := by
        rcases List.mem_cons.1 hn with rfl | hn'
        · exact absurd hmn (lt_irrefl _)
        · exact hn'
      have : [a, b] = [a] ++ [b] := rfl
      rw [this]
      exact List.Sublist.append (List.singleton_sublist.2 ha)
        (List.singleton_sublist.2 (List.mem_flatMap.2 ⟨n, hn', hb⟩))
    · have hn' : n ∈ l := by
        rcases List.mem_cons.1 hn with rfl | hn'
        · exact absurd (hl.1 m hm') (by omega)
        · exact hn'
      exact (ih hl.2 hm' hn').trans (List.sublist_append_right _ _)

lemma sublist_flatMap_of_mem {l : List ℕ} (f : ℕ → List X) {m : ℕ} (hm : m ∈ l) :
    f m <+ l.flatMap f := by
  induction l with
  | nil => simp at hm
  | cons c l ih =>
    rw [List.flatMap_cons]
    rcases List.mem_cons.1 hm with rfl | hm'
    · exact List.sublist_append_left _ _
    · exact (ih hm').trans (List.sublist_append_right _ _)

/-- Order of pairs in a list without duplicates is transitive. -/
lemma sublist_pair_trans {l : List X} (hl : l.Nodup) {a b c : X} (h1 : [a, b] <+ l)
    (h2 : [b, c] <+ l) : [a, c] <+ l := by
  induction l with
  | nil => simp at h1
  | cons d l ih =>
    rw [List.nodup_cons] at hl
    rcases List.sublist_cons_iff.1 h1 with k1 | ⟨r, hr, k1⟩ <;>
      rcases List.sublist_cons_iff.1 h2 with k2 | ⟨r', hr', k2⟩
    · exact (ih hl.2 k1 k2).cons d
    · simp only [List.cons.injEq] at hr'
      obtain ⟨rfl, rfl⟩ := hr'
      exact absurd (k1.subset (show b ∈ [a, b] by simp)) hl.1
    · simp only [List.cons.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      exact List.Sublist.cons_cons a (List.singleton_sublist.2 (k2.subset (by simp)))
    · simp only [List.cons.injEq] at hr hr'
      obtain ⟨rfl, rfl⟩ := hr
      obtain ⟨rfl, rfl⟩ := hr'
      exact absurd (k1.subset (by simp)) hl.1

/-- If `a` comes before `b` and `l = A ++ b :: B` has no duplicates, then `a ∈ A`. -/
lemma mem_of_sublist_pair {A B : List X} {b : X} (hl : (A ++ b :: B).Nodup) {a : X}
    (h : [a, b] <+ A ++ b :: B) : a ∈ A := by
  induction A with
  | nil =>
    simp only [List.nil_append, List.nodup_cons] at hl
    rcases List.sublist_cons_iff.1 h with k | ⟨r, hr, k⟩
    · exact absurd (k.subset (show b ∈ [a, b] by simp)) hl.1
    · simp only [List.cons.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      exact absurd (k.subset (by simp)) hl.1
  | cons c A ih =>
    simp only [List.cons_append, List.nodup_cons] at hl h
    rcases List.sublist_cons_iff.1 h with k | ⟨r, hr, k⟩
    · exact List.mem_cons_of_mem _ (ih hl.2 k)
    · simp only [List.cons.injEq] at hr
      rw [hr.1]; exact List.mem_cons_self

end Podc.WritableObjects
