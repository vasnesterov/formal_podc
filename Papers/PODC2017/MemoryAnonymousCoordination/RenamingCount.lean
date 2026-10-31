import Papers.PODC2017.MemoryAnonymousCoordination.RenamingDefs

/-!
# Figure 3: counting lemmas for views, catching up (lines 7–12) and adoption (lines 13–14)
-/

set_option linter.unusedSectionVars false

namespace Podc.MemoryAnonymousCoordination.Renaming

variable {P : Type} {m : ℕ} [DecidableEq P]

/-! ### Maximal round -/

lemma le_maxRd (V : Fin m → Option (P × St P)) (j : Fin m) : rdOf (V j) ≤ maxRd V :=
  Finset.le_sup (f := fun j => rdOf (V j)) (Finset.mem_univ j)

lemma maxRd_le {V : Fin m → Option (P × St P)} {r : ℕ} (h : ∀ j, rdOf (V j) ≤ r) :
    maxRd V ≤ r :=
  Finset.sup_le fun j _ => h j

lemma exists_maxRd {V : Fin m → Option (P × St P)} (h : 0 < maxRd V) :
    ∃ j, rdOf (V j) = maxRd V := by
  obtain ⟨j, -, hj⟩ := Finset.exists_mem_eq_sup (s := Finset.univ) (f := fun j => rdOf (V j))
    (by
      rcases Finset.univ.eq_empty_or_nonempty (α := Fin m) with h' | h'
      · exfalso; unfold maxRd at h; rw [h'] at h; simp at h
      · exact h')
  exact ⟨j, hj.symm⟩

/-! ### Catching up -/

lemma catchUp_of_le {S : Sel P m} {p : P} {s : St P} {V : Fin m → Option (P × St P)}
    (h : maxRd V ≤ s.rd) : catchUp S p s V = s := by
  simp [catchUp, Nat.not_lt.2 h]

/-- Catching up copies an entry of the view (or keeps the local variables). -/
lemma catchUp_mem (S : Sel P m) (p : P) (s : St P) (V : Fin m → Option (P × St P)) :
    catchUp S p s V = s ∨ ∃ j q, V j = some (q, catchUp S p s V) := by
  unfold catchUp
  split_ifs with h
  · split
    · rename_i q e he; exact Or.inr ⟨_, q, he⟩
    · exact Or.inl rfl
  · exact Or.inl rfl

/-- With an admissible line 9, after catching up the round is the maximum of the own round and
the rounds in the view. -/
lemma catchUp_rd {S : Sel P m} (hS : S.OK) (p : P) (s : St P) (V : Fin m → Option (P × St P)) :
    (catchUp S p s V).rd = max s.rd (maxRd V) := by
  unfold catchUp
  split_ifs with h
  · have hup := hS.up p s V h
    split
    · rename_i q e he; rw [he] at hup; simp at hup; omega
    · rename_i he; rw [he] at hup; simp at hup; omega
  · omega

/-! ### Counting entries -/

lemma cnt_add_le (V : Fin m → Option (P × St P)) (t : ℕ) {u w : P} (h : u ≠ w) :
    cnt V t u + cnt V t w ≤ m := by
  unfold cnt
  rw [← Finset.card_union_of_disjoint]
  · exact (Finset.card_le_univ _).trans (by simp)
  · rw [Finset.disjoint_filter]
    intro j _ h1 h2; rw [h1] at h2; simp at h2; exact h h2

lemma cnt_update_self (V : Fin m → Option (P × St P)) (j : Fin m) (p : P) (s : St P) :
    cnt V s.rd s.val ≤ cnt (Function.update V j (some (p, s))) s.rd s.val := by
  unfold cnt
  apply Finset.card_le_card
  intro i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Function.update_apply]
  intro hi; split_ifs <;> simp_all

lemma cnt_update_other (V : Fin m → Option (P × St P)) (j : Fin m) (p : P) (s : St P) {u : P}
    (h : u ≠ s.val) : cnt (Function.update V j (some (p, s))) s.rd u ≤ cnt V s.rd u := by
  unfold cnt
  apply Finset.card_le_card
  intro i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Function.update_apply]
  intro hi; split_ifs at hi with hij
  · simp only [rvOf_some, Option.some.injEq, Prod.mk.injEq] at hi; exact absurd hi.1.symm h
  · exact hi

/-! ### Adoption -/

@[simp] lemma adopt_rd (n : ℕ) (V : Fin m → Option (P × St P)) (s : St P) :
    (adopt n V s).rd = s.rd := by
  unfold adopt; split_ifs <;> rfl

@[simp] lemma adopt_hist (n : ℕ) (V : Fin m → Option (P × St P)) (s : St P) :
    (adopt n V s).hist = s.hist := by
  unfold adopt; split_ifs <;> rfl

lemma adopt_spec {n : ℕ} {V : Fin m → Option (P × St P)} (s : St P) (h : ∃ u, n ≤ cnt V s.rd u) :
    n ≤ cnt V s.rd (adopt n V s).val := by
  unfold adopt; rw [dite_eq_left_of_eq_true (eq_true h)]; exact h.choose_spec

lemma adopt_of_not {n : ℕ} {V : Fin m → Option (P × St P)} (s : St P)
    (h : ¬ ∃ u, n ≤ cnt V s.rd u) : adopt n V s = s := by
  unfold adopt; rw [dite_eq_right_of_eq_false (eq_false h)]

/-- With `m < 2n` entries, a value occurring at least `n` times in the current round is the one
adopted. -/
lemma adopt_eq {n : ℕ} (hm : m + 1 = 2 * n) {V : Fin m → Option (P × St P)} (s : St P) {w : P}
    (h : n ≤ cnt V s.rd w) : (adopt n V s).val = w := by
  have h1 := adopt_spec s ⟨w, h⟩
  by_contra hne
  have := cnt_add_le V s.rd hne
  omega

/-- The adopted value is the preference, or it is the val of an entry of the current round. -/
lemma adopt_mem {n : ℕ} (hn : 1 ≤ n) (V : Fin m → Option (P × St P)) (s : St P) :
    adopt n V s = s ∨ ∃ j q e, V j = some (q, e) ∧ e.val = (adopt n V s).val ∧ e.rd = s.rd := by
  by_cases h : ∃ u, n ≤ cnt V s.rd u
  · right
    have h1 := adopt_spec s h
    have : (Finset.univ.filter fun j => rvOf (V j) = some ((adopt n V s).val, s.rd)).Nonempty := by
      rw [← Finset.card_pos]; unfold cnt at h1; omega
    obtain ⟨j, hj⟩ := this
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    cases hV : V j with
    | none => simp [hV] at hj
    | some e =>
      obtain ⟨q, e⟩ := e
      simp only [hV, rvOf_some, Option.some.injEq, Prod.mk.injEq] at hj
      exact ⟨j, q, e, hV, hj.1, hj.2⟩
  · left; exact adopt_of_not s h

lemma adopt_val_eq_of {n : ℕ} {V : Fin m → Option (P × St P)} {s : St P}
    (h : (adopt n V s).val = s.val) : adopt n V s = s := by
  cases s; unfold adopt at h ⊢; split_ifs at h ⊢ with h' <;> simp_all

/-- After writing the adopted record once, it is adopted again. -/
lemma adopt_stable {n : ℕ} (hm : m + 1 = 2 * n) (V : Fin m → Option (P × St P)) (s : St P)
    (j : Fin m) (p : P) :
    adopt n (Function.update V j (some (p, adopt n V s))) (adopt n V s) = adopt n V s := by
  set s' := adopt n V s with hs'
  apply adopt_val_eq_of
  by_cases h : ∃ u, n ≤ cnt V s.rd u
  · apply adopt_eq hm
    have h1 := adopt_spec s h
    rw [← hs'] at h1
    have : s'.rd = s.rd := adopt_rd _ _ _
    rw [← this] at h1
    exact h1.trans (cnt_update_self V j p s')
  · by_cases h' : ∃ u, n ≤ cnt (Function.update V j (some (p, s'))) s'.rd u
    · obtain ⟨u, hu⟩ := h'
      by_cases hux : u = s'.val
      · subst hux; exact adopt_eq hm _ hu
      · exfalso; apply h
        refine ⟨u, ?_⟩
        have := hu.trans (cnt_update_other V j p s' hux)
        rwa [show s'.rd = s.rd from adopt_rd _ _ _] at this
    · rw [adopt_of_not _ h']

end Podc.MemoryAnonymousCoordination.Renaming
