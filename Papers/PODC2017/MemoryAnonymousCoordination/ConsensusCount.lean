import Papers.PODC2017.MemoryAnonymousCoordination.ConsensusDefs

/-!
# Figure 2: counting lemmas for views and the adoption rule (line 4)

`cnt view v` (entries with `val = v`), `nonW view w` (entries with `val ≠ w`) and the adoption
rule `adopt n view x`. With `m + 1 = 2n` registers a value occurring `≥ n` times is unique
(`adopt_eq`), a view with fewer than `n` non-`w` entries adopts `w` (`adopt_of_nonW_lt`), and a
preference is stable after writing it once (`adopt_stable`).
-/

namespace Podc.MemoryAnonymousCoordination.Consensus

variable {P V : Type} {m : ℕ} [DecidableEq V]

lemma cnt_add_nonW (f : Fin m → Option (P × V)) (w : V) : cnt f w + nonW f w = m := by
  unfold cnt nonW
  rw [Finset.card_filter_add_card_filter_not]; simp

lemma cnt_le_nonW (f : Fin m → Option (P × V)) {u w : V} (h : u ≠ w) : cnt f u ≤ nonW f w := by
  unfold cnt nonW
  apply Finset.card_le_card
  intro j; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  intro hj; rw [hj]; simpa using h

lemma nonW_le {f g : Fin m → Option (P × V)} {w : V}
    (h : ∀ j, g j = f j ∨ val (g j) = some w) : nonW g w ≤ nonW f w := by
  unfold nonW
  apply Finset.card_le_card
  intro j; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  intro hj; rcases h j with h | h
  · rwa [← h]
  · exact absurd h hj

lemma nonW_le_succ {f g : Fin m → Option (P × V)} {w : V} (j₀ : Fin m)
    (h : ∀ j, j ≠ j₀ → g j = f j) : nonW g w ≤ nonW f w + 1 := by
  unfold nonW
  calc _ ≤ (insert j₀ (Finset.univ.filter fun j => val (f j) ≠ some w)).card := by
        apply Finset.card_le_card
        intro j; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
        intro hj; by_cases hj0 : j = j₀
        · exact Or.inl hj0
        · right; rwa [← h j hj0]
    _ ≤ _ := Finset.card_insert_le _ _

lemma nonW_comp (f : Fin m → Option (P × V)) (σ : Equiv.Perm (Fin m)) (w : V) :
    nonW (fun j => f (σ j)) w = nonW f w := by
  unfold nonW
  exact Finset.card_equiv σ (by simp)

lemma nonW_eq_zero {f : Fin m → Option (P × V)} {w : V} (h : ∀ j, val (f j) = some w) :
    nonW f w = 0 := by
  unfold nonW
  simp [h]

/-- Two values each occurring in all but fewer than `n` of `2n − 1` entries are equal. -/
lemma eq_of_nonW_lt {f : Fin m → Option (P × V)} {n : ℕ} (hm : m + 1 = 2 * n) {w w' : V}
    (h : nonW f w < n) (h' : nonW f w' < n) : w = w' := by
  by_contra hne
  have h1 := cnt_le_nonW f hne
  have h2 := cnt_add_nonW f w
  omega

lemma adopt_spec {n : ℕ} {f : Fin m → Option (P × V)} (x : V) (h : ∃ u, n ≤ cnt f u) :
    n ≤ cnt f (adopt n f x) := by
  unfold adopt; rw [dite_eq_left_of_eq_true (eq_true h)]; exact h.choose_spec

lemma adopt_of_not {n : ℕ} {f : Fin m → Option (P × V)} (x : V) (h : ¬ ∃ u, n ≤ cnt f u) :
    adopt n f x = x := by
  unfold adopt; rw [dite_eq_right_of_eq_false (eq_false h)]

/-- With `m < 2n` entries, a value occurring at least `n` times is the one adopted. -/
lemma adopt_eq {n : ℕ} (hm : m + 1 = 2 * n) {f : Fin m → Option (P × V)} (x : V) {w : V}
    (h : n ≤ cnt f w) : adopt n f x = w := by
  have h1 := adopt_spec x ⟨w, h⟩
  by_contra hne
  have h2 := cnt_le_nonW f hne
  have h3 := cnt_add_nonW f w
  omega

/-- A view with fewer than `n` entries whose val is not `w` adopts `w`. -/
lemma adopt_of_nonW_lt {n : ℕ} (hm : m + 1 = 2 * n) {f : Fin m → Option (P × V)} (x : V)
    {w : V} (h : nonW f w < n) : adopt n f x = w := by
  apply adopt_eq hm
  have := cnt_add_nonW f w
  omega

/-- The adopted value is the preference or occurs in the view. -/
lemma adopt_mem {n : ℕ} (hn : 1 ≤ n) (f : Fin m → Option (P × V)) (x : V) :
    adopt n f x = x ∨ ∃ j q, f j = some (q, adopt n f x) := by
  by_cases h : ∃ u, n ≤ cnt f u
  · right
    have h1 := adopt_spec x h
    have : (Finset.univ.filter fun j => val (f j) = some (adopt n f x)).Nonempty := by
      rw [← Finset.card_pos]; unfold cnt at h1; omega
    obtain ⟨j, hj⟩ := this
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    refine ⟨j, ?_⟩
    cases hfj : f j with
    | none => simp [hfj] at hj
    | some e => obtain ⟨q, v⟩ := e; simp only [hfj, val_some, Option.some.injEq] at hj; exact ⟨q, by rw [hj]⟩
  · left; exact adopt_of_not x h

lemma cnt_update_self (f : Fin m → Option (P × V)) (j : Fin m) (p : P) (u : V) :
    cnt f u ≤ cnt (Function.update f j (some (p, u))) u := by
  unfold cnt
  apply Finset.card_le_card
  intro i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Function.update_apply]
  intro hi; split_ifs <;> simp [hi]

lemma cnt_update_other (f : Fin m → Option (P × V)) (j : Fin m) (p : P) {u u' : V}
    (h : u' ≠ u) : cnt (Function.update f j (some (p, u))) u' ≤ cnt f u' := by
  unfold cnt
  apply Finset.card_le_card
  intro i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Function.update_apply]
  intro hi; split_ifs at hi with hij
  · simp only [val_some, Option.some.injEq] at hi; exact absurd hi.symm h
  · exact hi

/-- After writing the adopted value once, it is adopted again (the preference is stable in solo
runs). -/
lemma adopt_stable {n : ℕ} (hm : m + 1 = 2 * n) (f : Fin m → Option (P × V)) (x : V) (j : Fin m)
    (p : P) :
    adopt n (Function.update f j (some (p, adopt n f x))) (adopt n f x) = adopt n f x := by
  set x' := adopt n f x with hx'
  by_cases h : ∃ u, n ≤ cnt f u
  · apply adopt_eq hm
    exact (adopt_spec x h).trans (cnt_update_self f j p x')
  · by_cases h' : ∃ u, n ≤ cnt (Function.update f j (some (p, x'))) u
    · obtain ⟨u, hu⟩ := h'
      by_cases hux : u = x'
      · subst hux; exact adopt_eq hm _ hu
      · exact absurd ⟨u, hu.trans (cnt_update_other f j p hux)⟩ h
    · exact adopt_of_not _ h'

end Podc.MemoryAnonymousCoordination.Consensus
