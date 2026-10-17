import Mathlib

-- CSLib candidate (general, not specific to this paper)

/-!
# Distributing a finite set according to prescribed counts

Local computations used by the routing algorithm: a node splits the messages it holds into
parts, class by class, according to prescribed capacities (`assign`), and picks the unique
element of a set of size at most one (`pick`).
-/

namespace CongestedCliqueRouting

open Finset

section Assign

variable {α κ ι : Type*} [DecidableEq α] [DecidableEq κ] [Fintype ι] [DecidableEq ι]

omit [DecidableEq α] in
lemma card_filter_eq_sum_fiber (S : Finset α) (cls : α → κ) (f : α → ι) (k : κ) :
    (S.filter (fun a => cls a = k)).card =
      ∑ p, (S.filter (fun a => cls a = k ∧ f a = p)).card := by
  rw [card_eq_sum_card_fiberwise (f := f) (t := univ) (fun _ _ => mem_coe.2 (mem_univ _))]
  refine sum_congr rfl fun p _ => ?_
  rw [filter_filter]

theorem exists_assign [Nonempty ι] (S : Finset α) (cls : α → κ) (cap : κ → ι → ℕ)
    (h : ∀ k, (S.filter (fun a => cls a = k)).card ≤ ∑ p, cap k p) :
    ∃ f : α → ι, ∀ k p, (S.filter (fun a => cls a = k ∧ f a = p)).card ≤ cap k p := by
  induction S using Finset.induction_on with
  | empty => exact ⟨fun _ => Classical.arbitrary ι, fun _ _ => by simp⟩
  | insert a S ha ih =>
    obtain ⟨f, hf⟩ := ih fun k =>
      le_trans (card_le_card (filter_subset_filter _ (subset_insert a S))) (h k)
    set k0 := cls a
    have hlt : (S.filter (fun x => cls x = k0)).card < ∑ p, cap k0 p := by
      have h1 := h k0
      rw [filter_insert, if_pos rfl, card_insert_of_notMem (by simp [ha])] at h1
      omega
    obtain ⟨p0, hp0⟩ : ∃ p0, (S.filter (fun x => cls x = k0 ∧ f x = p0)).card < cap k0 p0 := by
      by_contra hcon
      push Not at hcon
      rw [card_filter_eq_sum_fiber S cls f k0] at hlt
      exact absurd (sum_le_sum fun p _ => hcon p) (not_le.2 hlt)
    refine ⟨Function.update f a p0, fun k p => ?_⟩
    have hS : S.filter (fun x => cls x = k ∧ Function.update f a p0 x = p) =
        S.filter (fun x => cls x = k ∧ f x = p) := by
      refine filter_congr fun x hx => ?_
      have : x ≠ a := fun hxa => ha (hxa ▸ hx)
      simp [Function.update_of_ne this]
    rw [filter_insert, hS]
    by_cases hk : cls a = k ∧ p0 = p
    · obtain ⟨hk, rfl⟩ := hk
      rw [if_pos ⟨hk, by simp⟩, card_insert_of_notMem (by simp [ha])]
      subst hk
      exact hp0
    · rw [if_neg (by
        rintro ⟨h1, h2⟩
        exact hk ⟨h1, by simpa using h2⟩)]
      exact hf k p

open Classical in
/-- A deterministic assignment of the elements of `S` to parts `p : ι` such that at most
`cap k p` elements of class `k` go to part `p` (when this is possible). -/
noncomputable def assign [Nonempty ι] (S : Finset α) (cls : α → κ) (cap : κ → ι → ℕ) : α → ι :=
  if h : ∀ k, (S.filter (fun a => cls a = k)).card ≤ ∑ p, cap k p then
    Classical.choose (exists_assign S cls cap h)
  else fun _ => Classical.arbitrary ι

lemma assign_le [Nonempty ι] {S : Finset α} {cls : α → κ} {cap : κ → ι → ℕ}
    (h : ∀ k, (S.filter (fun a => cls a = k)).card ≤ ∑ p, cap k p) (k : κ) (p : ι) :
    (S.filter (fun a => cls a = k ∧ assign S cls cap a = p)).card ≤ cap k p := by
  unfold assign
  rw [dif_pos h]
  exact Classical.choose_spec (exists_assign S cls cap h) k p

omit [DecidableEq α] [DecidableEq κ] [DecidableEq ι] in
lemma eq_of_sum_eq_of_le {f g : ι → ℕ} (hle : ∀ p, f p ≤ g p) (hsum : ∑ p, f p = ∑ p, g p)
    (p : ι) : f p = g p :=
  ((sum_eq_sum_iff_of_le fun p _ => hle p).1 hsum) p (mem_univ p)

lemma assign_eq [Nonempty ι] {S : Finset α} {cls : α → κ} {cap : κ → ι → ℕ}
    (h : ∀ k, (S.filter (fun a => cls a = k)).card = ∑ p, cap k p) (k : κ) (p : ι) :
    (S.filter (fun a => cls a = k ∧ assign S cls cap a = p)).card = cap k p := by
  have hle := assign_le (fun k => (h k).le) k
  refine eq_of_sum_eq_of_le hle ?_ p
  rw [← card_filter_eq_sum_fiber, h k]

end Assign

section Pick

variable {α : Type*}

/-- Some element of `S`, if any (deterministic in `S`). -/
noncomputable def pick (S : Finset α) : Option α := S.toList.head?

lemma pick_mem {S : Finset α} {a : α} (h : pick S = some a) : a ∈ S := by
  unfold pick at h
  exact mem_toList.1 (List.mem_of_head? h)

lemma pick_singleton (a : α) : pick ({a} : Finset α) = some a := by
  simp [pick]

lemma pick_empty : pick (∅ : Finset α) = none := by
  simp [pick]

lemma pick_eq_none_iff {S : Finset α} : pick S = none ↔ S = ∅ := by
  simp [pick]

/-- If `S` has at most one element, `pick` returns it. -/
lemma pick_eq_some_of_card_le_one {S : Finset α} (h : S.card ≤ 1) {a : α} (ha : a ∈ S) :
    pick S = some a := by
  obtain ⟨b, rfl⟩ : ∃ b, S = {b} := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 h with h0 | h1
    · simp_all
    · exact card_eq_one.1 h1
  rw [mem_singleton.1 ha, pick_singleton]

end Pick

end CongestedCliqueRouting
