import Papers.PODC2011.SymmetryBreakingTasks.Basic

/-!
# From the `(n-1)`-slot task to `(n+1)`-renaming (Section 6, Figure 2, Theorem 12)

The algorithm of Figure 2 (code for `p_i`):
1. `my_slot ← KS.slot_request()` (an object solving the `(n-1)`-slot task `⟨n, n-1, 1, n⟩`);
2. `STATE[i] ← ⟨my_slot, id_i⟩`; `snapshot` of `STATE`;
3. if no other process with the same slot is in the snapshot, return `my_slot`;
4. otherwise, with `p_j` such a process, return `n` if `id_i < id_j` and `n + 1` otherwise.

**Execution model.** Since the snapshot object is atomic and `STATE[i]` is written once, an
execution is determined, as far as the decisions are concerned, by
* the slots `s : Fin n → Fin (n - 1)` returned by the `KS` object (in an execution where every
  process decides, `s` is an output vector of the `(n-1)`-slot task);
* the linearization times `w i` of the write of `p_i` and `r i` of its snapshot, with `w i < r i`
  and all write/snapshot times distinct; the snapshot of `p_i` contains `STATE[j]` iff
  `w j < r i`.
Names are `0, …, n` (the paper's `1, …, n+1`): slots are `0, …, n-2`, and the paper's names `n` and
`n + 1` are `n - 1` and `n`. Validity (Definition 1) only constrains executions in which every
process decides, and decisions are write-once, so it suffices to check those executions;
wait-freedom is obvious (straight-line code).
-/

namespace Podc.SymmetryBreakingTasks.SlotRenaming

open Finset

variable {n : ℕ}

/-- The name returned by `p_i` in Figure 2 (`0`-indexed). -/
noncomputable def newName (id : Fin n → ℕ) (s : Fin n → Fin (n - 1)) (w r : Fin n → ℕ) (i : Fin n) :
    Fin (n + 1) :=
  open Classical in
  if h : ∃ j, j ≠ i ∧ w j < r i ∧ s j = s i then
    if id i < id h.choose then ⟨n - 1, by omega⟩ else ⟨n, by omega⟩
  else ⟨s i, by have := (s i).isLt; omega⟩

/-- In an output vector of the `(n-1)`-slot task, at most two processes share a slot. -/
lemma unique_partner {s : Fin n → Fin (n - 1)} (hs : s ∈ kSlot n (n - 1)) {i j k : Fin n}
    (hj : j ≠ i) (hk : k ≠ i) (hsj : s j = s i) (hsk : s k = s i) : j = k := by
  by_contra hjk
  have h2 : cnt s (s i) ≤ 2 := by
    have := cnt_le_sub (ℓ := 1) (fun w => (mem_sgsb.1 hs w).1) (s i)
    omega
  have : ({i, j, k} : Finset (Fin n)) ⊆ ({a | s a = s i} : Finset (Fin n)) := by
    intro a ha; simp only [mem_insert, mem_singleton] at ha
    rcases ha with rfl | rfl | rfl <;> simp [hsj, hsk]
  have := (card_le_card this).trans h2
  rw [card_insert_of_notMem (by simp [hj.symm, hk.symm]), card_pair hjk] at this
  omega

/-- In an output vector of the `(n-1)`-slot task, at most one slot is shared. -/
lemma unique_dup {s : Fin n → Fin (n - 1)} (hs : s ∈ kSlot n (n - 1)) {a b : Fin (n - 1)}
    (ha : 2 ≤ cnt s a) (hb : 2 ≤ cnt s b) : a = b := by
  by_contra hab
  have hle : ∑ v, (1 + (if v = a then 1 else 0) + (if v = b then 1 else 0)) ≤ ∑ v, cnt s v :=
    sum_le_sum fun v _ => by
      have := (mem_sgsb.1 hs v).1
      by_cases hva : v = a
      · subst hva; simp [hab]; omega
      · by_cases hvb : v = b
        · subst hvb; simp [hva]; omega
        · simp [hva, hvb]; omega
  rw [sum_cnt, sum_add_distrib, sum_add_distrib, sum_ite_eq', sum_ite_eq'] at hle
  simp at hle
  omega

/-- Theorem 12: the algorithm of Figure 2 solves `(n+1)`-renaming from any solution to the
`(n-1)`-slot task: in every execution in which all processes decide, the names are distinct
(and they are in `0..n` by construction). -/
theorem theorem_12 (id : Fin n → ℕ) (hid : Function.Injective id) (s : Fin n → Fin (n - 1))
    (hs : s ∈ kSlot n (n - 1)) (w r : Fin n → ℕ) (hwr : ∀ i, w i < r i)
    (hdist : ∀ i j, w i ≠ r j) : Function.Injective (newName id s w r) := by
  classical
  -- of two processes, at least one sees the other
  have see : ∀ x y, w x < r y ∨ w y < r x := fun x y => by
    have := hwr x; have := hwr y; have := hdist x y; have := hdist y x; omega
  have hc : ∀ x (hx : ∃ j, j ≠ x ∧ w j < r x ∧ s j = s x), 2 ≤ cnt s (s x) := fun x hx => by
    have : ({x, hx.choose} : Finset (Fin n)) ⊆ ({a | s a = s x} : Finset (Fin n)) := by
      intro a ha; simp only [mem_insert, mem_singleton] at ha
      rcases ha with rfl | rfl <;> simp [hx.choose_spec.2.2]
    have := card_le_card this
    rwa [card_pair (Ne.symm hx.choose_spec.1)] at this
  intro i j hij
  by_contra hne
  have hn := i.isLt
  by_cases hi : ∃ k, k ≠ i ∧ w k < r i ∧ s k = s i <;>
    by_cases hj : ∃ k, k ≠ j ∧ w k < r j ∧ s k = s j
  · -- both see a conflict: then `i` and `j` share the duplicated slot and compare identities
    have h1 := hi.choose_spec; have h2 := hj.choose_spec
    have hsij : s i = s j := unique_dup hs (hc i hi) (hc j hj)
    have ci : hi.choose = j := unique_partner hs h1.1 (Ne.symm hne) h1.2.2 hsij.symm
    have cj : hj.choose = i := unique_partner hs h2.1 hne h2.2.2 hsij
    simp only [newName, dite_eq_left_of_eq_true (eq_true hi),
      dite_eq_left_of_eq_true (eq_true hj), ci, cj] at hij
    have := hid.ne hne
    split_ifs at hij <;> simp only [Fin.mk.injEq] at hij <;> omega
  · simp only [newName, dite_eq_left_of_eq_true (eq_true hi),
      dite_eq_right_of_eq_false (eq_false hj)] at hij
    have := (s j).isLt
    split_ifs at hij <;> simp only [Fin.mk.injEq] at hij <;> omega
  · simp only [newName, dite_eq_right_of_eq_false (eq_false hi),
      dite_eq_left_of_eq_true (eq_true hj)] at hij
    have := (s i).isLt
    split_ifs at hij <;> simp only [Fin.mk.injEq] at hij <;> omega
  · -- neither sees a conflict, so they have the same slot; but one of them sees the other
    simp only [newName, dite_eq_right_of_eq_false (eq_false hi),
      dite_eq_right_of_eq_false (eq_false hj), Fin.mk.injEq] at hij
    have hsij : s i = s j := Fin.ext hij
    rcases see i j with h | h
    · exact hj ⟨i, hne, h, hsij⟩
    · exact hi ⟨j, Ne.symm hne, h, hsij.symm⟩

/-- Non-vacuity: the hypotheses of Theorem 12 are satisfiable (`n = 3`, slots `[0, 0, 1]`,
sequential execution). -/
theorem theorem_12_hyps_satisfiable :
    ∃ (id : Fin 3 → ℕ) (s : Fin 3 → Fin 2) (w r : Fin 3 → ℕ), Function.Injective id ∧
      s ∈ kSlot 3 2 ∧ (∀ i, w i < r i) ∧ ∀ i j, w i ≠ r j :=
  ⟨![5, 7, 9], ![0, 0, 1], ![0, 2, 4], ![1, 3, 5], by decide, by rw [kSlot, mem_sgsb]; decide,
    by decide, by decide⟩

end Podc.SymmetryBreakingTasks.SlotRenaming
