import Mathlib.Data.Finset.Max
import Podc.Foundations.Quorum

-- CSLib candidate: Cslib/Foundations/Data/Finset/Quorum.lean (with `Podc.Foundations.Quorum`)

/-!
# Counting votes: `countEq`, thresholds, majority and plurality

Voting steps of fault-tolerant protocols count how many members of a set `s` (the processes heard
from, the received messages, …) report a value `b`, and select a value reported often enough.
This file provides one counting function and the three selectors used by such protocols.

## Main definitions

* `Finset.countEq s f b`: the number of `a ∈ s` with `f a = b`.
* `Finset.threshold? s f k`: some value `b` reported (as `some b`) by at least `k` members of `s`,
  or `none` if there is none. Votes are `Option`-valued: `none` is "no vote".
* `Finset.majority? s f`: the value reported by a strict majority of `s`, if any
  (`= threshold? s f (#s / 2 + 1)`).
* `Finset.plurality s f d`: a most frequent value of `f` on `s` (`d` if `s = ∅`).

## Main statements

* `Finset.countEq_add_countEq_le`, `Finset.eq_of_card_lt_countEq_add_countEq`: two distinct
  values are reported by at most `#s` members together; two "heavy" values coincide.
* `Finset.exists_mem_notMem_of_card_lt_countEq`: a value reported more than `#F` times is reported
  by a member outside `F`.
* `Finset.majority?_eq_of_notMem`: if the members outside `F` are a strict majority of `s` and
  all report `o`, the majority value is `o`.
* `Finset.plurality_eq_of_card_lt_two_mul_countEq`: a strict-majority value is the plurality.
* `Finset.find?_map_eq_threshold?`, `Finset.find?_map_eq_majority?`: the computable "first
  candidate above the threshold" scan of a protocol computes `threshold?` / `majority?`.
-/

namespace Finset

variable {α β : Type*} [DecidableEq β] {s t F : Finset α} {f : α → β} {b c : β} {k : ℕ}

/-! ### Counting -/

/-- `s.countEq f b`: the number of members `a` of `s` with `f a = b`. -/
def countEq (s : Finset α) (f : α → β) (b : β) : ℕ := #{a ∈ s | f a = b}

theorem countEq_def : s.countEq f b = #{a ∈ s | f a = b} := rfl

@[simp] theorem countEq_empty : (∅ : Finset α).countEq f b = 0 := rfl

theorem countEq_le_card : s.countEq f b ≤ #s := card_filter_le _ _

@[gcongr]
theorem countEq_mono (h : s ⊆ t) : s.countEq f b ≤ t.countEq f b :=
  card_le_card (filter_subset_filter _ h)

theorem exists_mem_of_countEq_pos (h : 0 < s.countEq f b) : ∃ a ∈ s, f a = b := by
  obtain ⟨a, ha⟩ := card_pos.1 h
  exact ⟨a, (mem_filter.1 ha).1, (mem_filter.1 ha).2⟩

/-- Two distinct values are reported by at most `#s` members of `s` together. -/
theorem countEq_add_countEq_le (h : b ≠ c) : s.countEq f b + s.countEq f c ≤ #s := by
  classical
  rw [countEq, countEq, ← card_union_of_disjoint]
  · exact card_le_card (union_subset (filter_subset _ _) (filter_subset _ _))
  · exact disjoint_filter.2 fun a _ hb hc => h (hb.symm.trans hc)

/-- Two values reported by more than `#s` members of `s` together coincide. -/
theorem eq_of_card_lt_countEq_add_countEq (h : #s < s.countEq f b + s.countEq f c) : b = c := by
  by_contra hbc
  have := countEq_add_countEq_le (s := s) (f := f) hbc
  omega

/-- A value reported by more than `#F` members of `s` is reported by a member outside `F`. -/
theorem exists_mem_notMem_of_card_lt_countEq (h : #F < s.countEq f b) :
    ∃ a ∈ s, a ∉ F ∧ f a = b := by
  obtain ⟨a, ha, haF⟩ := exists_mem_notMem_of_card_lt_card h
  exact ⟨a, (mem_filter.1 ha).1, haF, (mem_filter.1 ha).2⟩

section DecidableEq

variable [DecidableEq α]

/-- Shrinking `s` to `t` loses at most `#(s \ t)` votes for `b`. -/
theorem countEq_le_countEq_add_card_sdiff (s t : Finset α) :
    s.countEq f b ≤ t.countEq f b + #(s \ t) := by
  refine (card_le_card fun a ha => ?_).trans (card_union_le _ _)
  rw [mem_filter] at ha
  by_cases hat : a ∈ t
  · exact mem_union_left _ (mem_filter.2 ⟨hat, ha.2⟩)
  · exact mem_union_right _ (mem_sdiff.2 ⟨ha.1, hat⟩)

/-- If every member of `s` outside `F` reports `b`, then `b` is reported at least
`#(s \ F)` times. -/
theorem card_sdiff_le_countEq (h : ∀ a ∈ s, a ∉ F → f a = b) : #(s \ F) ≤ s.countEq f b :=
  card_le_card fun a ha => by
    rw [mem_sdiff] at ha
    exact mem_filter.2 ⟨ha.1, h a ha.1 ha.2⟩

end DecidableEq

/-! ### Threshold selection -/

section Selectors

variable {f : α → Option β}

open Classical in
/-- `s.threshold? f k`: some value `b` such that `some b` is reported by at least `k` members of
`s` (chosen arbitrarily), or `none` if there is no such value. -/
noncomputable def threshold? (s : Finset α) (f : α → Option β) (k : ℕ) : Option β :=
  if h : ∃ b, k ≤ s.countEq f (some b) then some h.choose else none

theorem le_countEq_of_threshold?_eq_some (h : s.threshold? f k = some b) :
    k ≤ s.countEq f (some b) := by
  unfold threshold? at h
  split_ifs at h with h'
  cases h
  exact h'.choose_spec

theorem threshold?_eq_none_iff : s.threshold? f k = none ↔ ∀ b, s.countEq f (some b) < k := by
  unfold threshold?
  split_ifs with h
  · simp only [false_iff, not_forall, not_lt]
    exact h
  · push Not at h
    simpa using h

/-- If `b` reaches the threshold and no other value does, the selected value is `b`. -/
theorem threshold?_eq_some_of_forall (hb : k ≤ s.countEq f (some b))
    (hu : ∀ c, c ≠ b → s.countEq f (some c) < k) : s.threshold? f k = some b := by
  cases h : s.threshold? f k with
  | none => exact absurd hb (not_le.2 (threshold?_eq_none_iff.1 h b))
  | some c =>
    by_contra hcb
    exact absurd (le_countEq_of_threshold?_eq_some h)
      (not_le.2 (hu c fun e => hcb (congrArg some e)))

/-- With a threshold above `#s / 2` the selected value is unique. -/
theorem threshold?_eq_some (hk : #s < 2 * k) (hb : k ≤ s.countEq f (some b)) :
    s.threshold? f k = some b :=
  threshold?_eq_some_of_forall hb fun c hc => by
    have := countEq_add_countEq_le (s := s) (f := f) (Option.some_injective _ |>.ne hc)
    omega

/-- A selected value (for a positive threshold) is reported by some member of `s`. -/
theorem exists_mem_of_threshold?_eq_some (hk : 0 < k) (h : s.threshold? f k = some b) :
    ∃ a ∈ s, f a = some b :=
  exists_mem_of_countEq_pos ((le_countEq_of_threshold?_eq_some h).trans_lt' hk)

/-! ### Strict majority -/

/-- `s.majority? f`: the value reported (as `some b`) by a strict majority of `s`, if any. -/
noncomputable def majority? (s : Finset α) (f : α → Option β) : Option β :=
  s.threshold? f (#s / 2 + 1)

theorem majority?_eq_some_iff : s.majority? f = some b ↔ #s < 2 * s.countEq f (some b) := by
  constructor
  · intro h
    have := le_countEq_of_threshold?_eq_some h
    omega
  · intro h
    exact threshold?_eq_some (by omega) (by omega)

theorem majority?_eq_none_iff : s.majority? f = none ↔ ∀ b, 2 * s.countEq f (some b) ≤ #s := by
  rw [majority?, threshold?_eq_none_iff]
  exact forall_congr' fun _ => by omega

/-- If the members of `s` outside `F` form a strict majority of `s` and all report `o`, then the
majority value is `o`. -/
theorem majority?_eq_of_notMem [DecidableEq α] {o : Option β} (hF : #s < 2 * #(s \ F))
    (h : ∀ a ∈ s, a ∉ F → f a = o) : s.majority? f = o := by
  have hc := card_sdiff_le_countEq h
  cases o with
  | some b => exact majority?_eq_some_iff.2 (by omega)
  | none =>
    refine majority?_eq_none_iff.2 fun b => ?_
    have := countEq_add_countEq_le (s := s) (f := f) (b := some b) (c := none) (by simp)
    omega

theorem exists_mem_of_majority?_eq_some (h : s.majority? f = some b) : ∃ a ∈ s, f a = some b :=
  exists_mem_of_threshold?_eq_some (by omega) h

/-! ### Computable selectors -/

/-- Votes `some (g a)` for `some b` are the votes `g a` for `b`. -/
@[simp] theorem countEq_some (g : α → β) (b : β) :
    s.countEq (fun a => some (g a)) (some b) = s.countEq g b := by
  simp [countEq]

/-- **Scanning for a heavy value.** Protocols compute a threshold value by scanning a list `L`
covering `s` for the first `a ∈ s` whose value `g a` is reported at least `k` times. When
`#s < 2 * k` (at most one value reaches the threshold), this is `s.threshold? (some ∘ g) k`. -/
theorem find?_map_eq_threshold? {g : α → β} {L : List α} (hL : ∀ a ∈ s, a ∈ L) {p : α → Bool}
    (hp : ∀ a, p a = true ↔ a ∈ s ∧ k ≤ s.countEq g (g a)) (hk : #s < 2 * k) :
    (L.find? p).map g = s.threshold? (fun a => some (g a)) k := by
  cases h : L.find? p with
  | some a =>
    have := (hp a).1 (List.find?_some h)
    exact (threshold?_eq_some hk (by rw [countEq_some]; exact this.2)).symm
  | none =>
    refine (threshold?_eq_none_iff.2 fun b => ?_).symm
    rw [countEq_some]
    by_contra hb
    push Not at hb
    obtain ⟨a, ha, rfl⟩ := exists_mem_of_countEq_pos (show 0 < s.countEq g b by omega)
    exact List.find?_eq_none.1 h a (hL a ha) ((hp a).2 ⟨ha, hb⟩)

/-- **Scanning for a strict majority.** The first `a ∈ s` in a list covering `s` whose value
`g a` is reported by a strict majority of `s` gives `s.majority? (some ∘ g)`. -/
theorem find?_map_eq_majority? {g : α → β} {L : List α} (hL : ∀ a ∈ s, a ∈ L) {p : α → Bool}
    (hp : ∀ a, p a = true ↔ a ∈ s ∧ #s < 2 * s.countEq g (g a)) :
    (L.find? p).map g = s.majority? (fun a => some (g a)) :=
  find?_map_eq_threshold? hL
    (fun a => (hp a).trans (and_congr_right fun _ => ⟨fun h => by omega, fun h => by omega⟩))
    (by omega)

end Selectors

/-! ### Plurality -/

/-- `s.plurality f d`: a most frequent value of `f` on `s` (ties broken arbitrarily), or `d` if
`s` is empty. -/
noncomputable def plurality (s : Finset α) (f : α → β) (d : β) : β :=
  if h : s.Nonempty then f (s.exists_max_image (fun a => s.countEq f (f a)) h).choose else d

/-- The plurality value is reported at least as often as any other value. -/
theorem countEq_le_countEq_plurality (hs : s.Nonempty) (d b : β) :
    s.countEq f b ≤ s.countEq f (s.plurality f d) := by
  rcases Nat.eq_zero_or_pos (s.countEq f b) with h | h
  · omega
  obtain ⟨a, ha, rfl⟩ := exists_mem_of_countEq_pos h
  simp only [plurality, hs, ↓reduceDIte]
  exact (s.exists_max_image (fun a => s.countEq f (f a)) hs).choose_spec.2 a ha

/-- A value reported by a strict majority of `s` is the plurality. -/
theorem plurality_eq_of_card_lt_two_mul_countEq {d : β} (h : #s < 2 * s.countEq f b) :
    s.plurality f d = b := by
  have hs : s.Nonempty := by
    rw [← card_pos]; have := countEq_le_card (s := s) (f := f) (b := b); omega
  by_contra hne
  have h₁ := countEq_le_countEq_plurality (f := f) hs d b
  have h₂ := countEq_add_countEq_le (s := s) (f := f) hne
  omega

end Finset
