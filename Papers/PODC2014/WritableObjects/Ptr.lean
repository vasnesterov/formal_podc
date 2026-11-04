import Papers.PODC2014.WritableObjects.Control

/-!
# The register `Ptr` along a transcript

`nptr α t` counts the writes to `Ptr` among the first `t` events (the paper's timestamp
`TS_Ptr(t)`, (4.2)); `ptrAt α t` (the value of `Ptr` at point `t`) depends only on `nptr α t`.
-/

namespace Podc.WritableObjects

open Cslib.SharedMemory

variable {P ι : Type} {T : ObjSpec}

/-- The number of writes to `Ptr` among the first `t` events (`TS_Ptr(t)` in the paper). -/
def nptr (α : List (Ev P ι T)) (t : ℕ) : ℕ := ((α.take t).filterMap Ev.ptrVal).length

variable {α : List (Ev P ι T)}

lemma ptrVal_eq_some {ev : Ev P ι T} {i : ι} : ev.ptrVal = some i ↔ ∃ p, ev = .ptr p i := by
  cases ev <;> simp [Ev.ptrVal]

lemma filterMap_take_succ' {β : Type} (g : Ev P ι T → Option β) {t : ℕ} (ht : t < α.length) :
    (α.take (t + 1)).filterMap g = (α.take t).filterMap g ++ (g α[t]).toList := by
  rw [List.take_add_one, List.filterMap_append, List.getElem?_eq_getElem ht]
  cases h : g α[t] <;> simp [h]

lemma ptrAt_eq (α : List (Ev P ι T)) (t : ℕ) :
    ptrAt α t = ((α.filterMap Ev.ptrVal).take (nptr α t)).getLast? := by
  have hpre : (α.take t).filterMap Ev.ptrVal <+: α.filterMap Ev.ptrVal := by
    refine ⟨(α.drop t).filterMap Ev.ptrVal, ?_⟩
    rw [← List.filterMap_append, List.take_append_drop]
  rw [ptrAt, nptr]
  conv_lhs => rw [List.prefix_iff_eq_take.1 hpre]

lemma ptrAt_congr {s t : ℕ} (h : nptr α s = nptr α t) : ptrAt α s = ptrAt α t := by
  rw [ptrAt_eq, ptrAt_eq, h]

lemma nptr_mono {s t : ℕ} (hst : s ≤ t) : nptr α s ≤ nptr α t := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hst
  simp only [nptr, List.take_add, List.filterMap_append, List.length_append]
  omega

lemma nptr_succ_of_ptr {w : ℕ} {p : P} {i : ι} (hw : α[w]? = some (.ptr p i)) :
    nptr α (w + 1) = nptr α w + 1 ∧ ptrAt α (w + 1) = some i := by
  obtain ⟨hw', hev⟩ := getElem_of_getElem? hw
  simp only [nptr, ptrAt, filterMap_take_succ' _ hw', hev, Ev.ptrVal]
  simp

lemma nptr_succ_of_not_ptr {k : ℕ} (hk : k < α.length) (h : ∀ p i, α[k] ≠ .ptr p i) :
    nptr α (k + 1) = nptr α k ∧ ptrAt α (k + 1) = ptrAt α k := by
  have : α[k].ptrVal = none := by
    cases hc : α[k] <;> simp_all [Ev.ptrVal]
  simp only [nptr, ptrAt, filterMap_take_succ' _ hk, this]
  simp

/-- A point where `Ptr ≠ i` followed by one where `Ptr = i`: `i` is written in between. -/
lemma exists_ptr_of_ne {s t : ℕ} {i : ι} (hst : s ≤ t) (hs : ptrAt α s ≠ some i)
    (ht : ptrAt α t = some i) : ∃ w p, s ≤ w ∧ w < t ∧ α[w]? = some (.ptr p i) := by
  induction t, hst using Nat.le_induction with
  | base => exact absurd ht hs
  | succ t hst ih =>
    by_cases htl : t < α.length
    swap
    · have h1 : α.take (t + 1) = α.take t := by
        rw [List.take_of_length_le (by omega), List.take_of_length_le (by omega)]
      obtain ⟨w, p, h1, h2, h3⟩ := ih (by simpa [ptrAt, h1] using ht)
      exact ⟨w, p, h1, by omega, h3⟩
    by_cases hp : ∃ p j, α[t] = .ptr p j
    · obtain ⟨p, j, hj⟩ := hp
      have := (nptr_succ_of_ptr (α := α) (w := t) (by rw [List.getElem?_eq_getElem htl, hj])).2
      rw [this] at ht
      cases ht
      exact ⟨t, p, hst, by omega, by rw [List.getElem?_eq_getElem htl, hj]⟩
    · simp only [not_exists] at hp
      rw [(nptr_succ_of_not_ptr htl hp).2] at ht
      obtain ⟨w, p, h1, h2, h3⟩ := ih ht
      exact ⟨w, p, h1, by omega, h3⟩

/-- Different writes to `Ptr` have different timestamps. -/
lemma eq_of_nptr_eq {w w' : ℕ} {p p' : P} {i i' : ι} (hw : α[w]? = some (.ptr p i))
    (hw' : α[w']? = some (.ptr p' i')) (h : nptr α (w + 1) = nptr α (w' + 1)) : w = w' := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have h1 := nptr_mono (α := α) (show w + 1 ≤ w' by omega)
    have h2 := (nptr_succ_of_ptr hw').1
    omega
  · have h1 := nptr_mono (α := α) (show w' + 1 ≤ w by omega)
    have h2 := (nptr_succ_of_ptr hw).1
    omega

/-- The timestamp of a point at which `Ptr ≠ ⊥` is positive and `Ptr` holds the corresponding
written index. -/
lemma ptrAt_eq_some {t : ℕ} {i : ι} (h : ptrAt α t = some i) :
    1 ≤ nptr α t ∧ (α.filterMap Ev.ptrVal)[nptr α t - 1]? = some i := by
  rw [ptrAt_eq] at h
  have hpos : 1 ≤ nptr α t := by
    by_contra hc
    simp only [not_le, Nat.lt_one_iff] at hc
    simp [hc] at h
  refine ⟨hpos, ?_⟩
  rw [List.getLast?_eq_getElem?, List.getElem?_take] at h
  rw [← h]
  have : nptr α t ≤ (α.filterMap Ev.ptrVal).length := by
    unfold nptr
    have hpre : (α.take t).filterMap Ev.ptrVal <+: α.filterMap Ev.ptrVal := by
      refine ⟨(α.drop t).filterMap Ev.ptrVal, ?_⟩
      rw [← List.filterMap_append, List.take_append_drop]
    exact hpre.length_le
  simp only [List.length_take, Nat.min_eq_left this]
  split_ifs <;> first | rfl | omega

/-- The last write to `Ptr` before a point where `Ptr = i`: it writes `i` and has the same
timestamp. -/
lemma exists_last_ptr {t : ℕ} {i : ι} (h : ptrAt α t = some i) :
    ∃ w p, w < t ∧ α[w]? = some (.ptr p i) ∧ nptr α (w + 1) = nptr α t := by
  induction t with
  | zero => simp [ptrAt] at h
  | succ t ih =>
    by_cases htl : t < α.length
    swap
    · have h1 : α.take (t + 1) = α.take t := by
        rw [List.take_of_length_le (by omega), List.take_of_length_le (by omega)]
      obtain ⟨w, p, h2, h3, h4⟩ := ih (by simpa [ptrAt, h1] using h)
      exact ⟨w, p, by omega, h3, by rw [h4]; simp [nptr, h1]⟩
    by_cases hp : ∃ p j, α[t] = .ptr p j
    · obtain ⟨p, j, hj⟩ := hp
      have hj' : α[t]? = some (.ptr p j) := by rw [List.getElem?_eq_getElem htl, hj]
      have := nptr_succ_of_ptr hj'
      rw [this.2] at h
      cases h
      exact ⟨t, p, by omega, hj', rfl⟩
    · simp only [not_exists] at hp
      have := nptr_succ_of_not_ptr htl hp
      rw [this.2] at h
      obtain ⟨w, p, h2, h3, h4⟩ := ih h
      exact ⟨w, p, by omega, h3, by rw [h4, this.1]⟩

end Podc.WritableObjects
