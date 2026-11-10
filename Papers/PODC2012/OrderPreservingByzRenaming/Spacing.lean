import Papers.PODC2012.OrderPreservingByzRenaming.Alg5

/-!
# Spacing in the approximation phase (Lemmas 31 and 32)

* **Lemma 31** (`lemma_31`): if the multisets `U`, `W` are built from pairs `(a, pair(a))` with
  `a + δ ≤ pair(a)`, then after sorting `uᵢ + δ ≤ wᵢ` for every `i`. Proved by induction on insertion
  sort (`orderedInsert` preserves the pointwise relation of sorted lists).
* **Lemma 32** (`lemma_32`): the spacing `ranks[id] + δ ≤ ranks[id']` of two ids that are both in
  the *own* `timely` set of a correct process is preserved by one approximation round (all valid
  votes contain both ids with that spacing). True.

Lemma 33 needs the spacing for pairs in `timely` of *other* correct processes, which `isValid` of
the updating process does not check; this is where the paper's proof breaks
(`Counterexample5.lean`).
-/

namespace Podc.OrderPreservingByzRenaming.Alg5

/-- The relation "spaced by at least `d`". -/
def Spaced (d : ℚ) (a b : ℚ) : Prop := a + d ≤ b

section Sorting

variable {d : ℚ}

lemma orderedInsert_eq_cons {a : ℚ} {s : List ℚ} (h : ∀ y ∈ s, a ≤ y) :
    s.orderedInsert (· ≤ ·) a = a :: s := by
  cases s with
  | nil => rfl
  | cons y s => simp [List.orderedInsert, h y (by simp)]

/-- Inserting spaced elements into pointwise spaced sorted lists keeps them pointwise spaced. -/
lemma forall₂_orderedInsert {s₁ s₂ : List ℚ} (h : List.Forall₂ (Spaced d) s₁ s₂)
    (hs₁ : s₁.Pairwise (· ≤ ·)) (hs₂ : s₂.Pairwise (· ≤ ·)) {a b : ℚ} (hab : Spaced d a b) :
    List.Forall₂ (Spaced d) (s₁.orderedInsert (· ≤ ·) a) (s₂.orderedInsert (· ≤ ·) b) := by
  induction h generalizing a b with
  | nil => simpa using hab
  | @cons x y s₁ s₂ hxy h ih =>
    simp only [List.pairwise_cons] at hs₁ hs₂
    simp only [List.orderedInsert]
    unfold Spaced at hxy hab
    split_ifs with h1 h2 h2
    · exact .cons hab (.cons hxy h)
    · -- `a ≤ x`, `b > y`
      refine .cons (by unfold Spaced; linarith) ?_
      rw [← orderedInsert_eq_cons hs₁.1]
      exact ih hs₁.2 hs₂.2 (by unfold Spaced; linarith)
    · -- `a > x`, `b ≤ y`
      refine .cons (by unfold Spaced; linarith) ?_
      rw [← orderedInsert_eq_cons hs₂.1]
      exact ih hs₁.2 hs₂.2 (by unfold Spaced; linarith)
    · exact .cons hxy (ih hs₁.2 hs₂.2 hab)

/-- **Lemma 31.** Pointwise spaced lists stay pointwise spaced after sorting. -/
theorem lemma_31 {l₁ l₂ : List ℚ} (h : List.Forall₂ (Spaced d) l₁ l₂) :
    List.Forall₂ (Spaced d) (l₁.insertionSort (· ≤ ·)) (l₂.insertionSort (· ≤ ·)) := by
  induction h with
  | nil => exact .nil
  | cons hab h ih =>
    simp only [List.insertionSort]
    exact forall₂_orderedInsert ih (List.pairwise_insertionSort _ _) (List.pairwise_insertionSort _ _) hab

end Sorting

section Avg

variable {d : ℚ}

lemma sum_add_le {l₁ l₂ : List ℚ} (h : List.Forall₂ (Spaced d) l₁ l₂) :
    l₁.sum + l₁.length * d ≤ l₂.sum := by
  induction h with
  | nil => simp
  | cons hab _ ih => simp only [List.sum_cons, List.length_cons]; unfold Spaced at hab; push_cast; linarith

lemma avg_add_le {l₁ l₂ : List ℚ} (h : List.Forall₂ (Spaced d) l₁ l₂) (hne : l₁ ≠ []) :
    avg l₁ + d ≤ avg l₂ := by
  have hlen := h.length_eq
  have hpos : (0 : ℚ) < l₁.length := by exact_mod_cast List.length_pos_iff.2 hne
  unfold avg
  rw [← hlen, div_add' _ _ _ hpos.ne', div_le_div_iff_of_pos_right hpos]
  have := sum_add_le h
  linarith

lemma forall₂_filterMap_getElem? {l₁ l₂ : List ℚ} (h : List.Forall₂ (Spaced d) l₁ l₂)
    (g : ℕ → Option ℕ) (idx : List ℕ) :
    List.Forall₂ (Spaced d) (idx.filterMap fun i => (g i).bind (l₁[·]?))
      (idx.filterMap fun i => (g i).bind (l₂[·]?)) := by
  induction idx with
  | nil => exact .nil
  | cons i idx ih =>
    simp only [List.filterMap_cons]
    cases g i with
    | none => simpa using ih
    | some j =>
      simp only [Option.bind_some]
      have hlen := h.length_eq
      by_cases hj : j < l₁.length
      · have hj2 : j < l₂.length := hlen ▸ hj
        simp only [List.getElem?_eq_getElem hj, List.getElem?_eq_getElem hj2]
        exact .cons ((List.forall₂_iff_get.1 h).2 j hj hj2) ih
      · have hj2 : ¬ j < l₂.length := hlen ▸ hj
        simp only [List.getElem?_eq_none (Nat.le_of_not_lt hj),
          List.getElem?_eq_none (Nat.le_of_not_lt hj2)]
        exact ih

lemma selPaper_eq (t : ℕ) (l : List ℚ) :
    selPaper t l = (List.range (l.length / t)).filterMap fun i => (some (i * t)).bind (l[·]?) := rfl

lemma selDLPSW_eq (t : ℕ) (l : List ℚ) :
    selDLPSW t l = (List.range l.length).filterMap fun i =>
      (if i % t = 0 then some i else none).bind (l[·]?) := by
  unfold selDLPSW
  congr 1; funext i; split_ifs <;> rfl

lemma forall₂_selPaper (t : ℕ) {l₁ l₂ : List ℚ} (h : List.Forall₂ (Spaced d) l₁ l₂) :
    List.Forall₂ (Spaced d) (selPaper t l₁) (selPaper t l₂) := by
  rw [selPaper_eq, selPaper_eq, ← h.length_eq]
  exact forall₂_filterMap_getElem? h _ _

lemma forall₂_selDLPSW (t : ℕ) {l₁ l₂ : List ℚ} (h : List.Forall₂ (Spaced d) l₁ l₂) :
    List.Forall₂ (Spaced d) (selDLPSW t l₁) (selDLPSW t l₂) := by
  rw [selDLPSW_eq, selDLPSW_eq, ← h.length_eq]
  exact forall₂_filterMap_getElem? h _ _

lemma selPaper_ne_nil {t : ℕ} (ht : 1 ≤ t) {l : List ℚ} (hl : t ≤ l.length) : selPaper t l ≠ [] := by
  have h0 : 0 < l.length / t := Nat.div_pos hl (by omega)
  have : (0 : ℕ) ∈ List.range (l.length / t) := List.mem_range.2 h0
  intro hnil
  rw [selPaper, List.filterMap_eq_nil_iff] at hnil
  have := hnil 0 this
  simp only [zero_mul] at this
  rw [List.getElem?_eq_none_iff] at this
  omega

lemma selDLPSW_ne_nil (t : ℕ) {l : List ℚ} (hl : 0 < l.length) : selDLPSW t l ≠ [] := by
  intro hnil
  rw [selDLPSW, List.filterMap_eq_nil_iff] at hnil
  have := hnil 0 (List.mem_range.2 hl)
  simp only [Nat.zero_mod, if_true] at this
  rw [List.getElem?_eq_none_iff] at this
  omega

end Avg

/-- A choice function `select_t` that picks positions depending only on the length (so pointwise
spaced lists give pointwise spaced selections) and selects something from a reduced multiset of
size `n - 2t`. Both `selPaper` (for `t ≥ 1`) and `selDLPSW` qualify. -/
structure GoodSel (n t : ℕ) (sel : ℕ → List ℚ → List ℚ) : Prop where
  forall₂ : ∀ {d : ℚ} {l₁ l₂ : List ℚ}, List.Forall₂ (Spaced d) l₁ l₂ →
    List.Forall₂ (Spaced d) (sel t l₁) (sel t l₂)
  ne_nil : ∀ l : List ℚ, l.length = n - 2 * t → sel t l ≠ []

lemma goodSel_paper {n t : ℕ} (ht : 1 ≤ t) (hn : 3 * t < n) : GoodSel n t selPaper :=
  ⟨forall₂_selPaper t, fun _ hl => selPaper_ne_nil ht (by omega)⟩

lemma goodSel_dlpsw {n t : ℕ} (hn : 3 * t < n) : GoodSel n t selDLPSW :=
  ⟨forall₂_selDLPSW t, fun _ hl => selDLPSW_ne_nil t (by omega)⟩

/-- One approximation step preserves spacing (core of Lemma 32). -/
lemma newVal_spaced {n t : ℕ} {sel : ℕ → List ℚ → List ℚ} (hsel : GoodSel n t sel)
    (hn : 2 * t < n) {d m₁ m₂ : ℚ} {v₁ v₂ : List ℚ} (hm : Spaced d m₁ m₂)
    (hv : List.Forall₂ (Spaced d) v₁ v₂) (hlen : v₁.length ≤ n) :
    Spaced d (newVal n t sel m₁ v₁) (newVal n t sel m₂ v₂) := by
  have hl := hv.length_eq
  have hfill : List.Forall₂ (Spaced d) (v₁ ++ List.replicate (n - v₁.length) m₁)
      (v₂ ++ List.replicate (n - v₂.length) m₂) := by
    rw [← hl]
    refine List.rel_append hv ?_
    induction (n - v₁.length) with
    | zero => exact .nil
    | succ k ih => exact .cons hm ih
  have hsort := lemma_31 hfill
  have htrim := List.forall₂_take (n - 2 * t) (List.forall₂_drop t hsort)
  have hlen₁ : (((v₁ ++ List.replicate (n - v₁.length) m₁).insertionSort (· ≤ ·)).drop t |>.take
      (n - 2 * t)).length = n - 2 * t := by
    simp [List.length_insertionSort]; omega
  unfold newVal Spaced
  exact avg_add_le (hsel.forall₂ htrim) (hsel.ne_nil _ hlen₁)

lemma length_votesFor_le {n : ℕ} (V : List (Finset ℕ × (ℕ → ℚ))) (hV : V.length ≤ n) (a : ℕ) :
    (votesFor V a).length ≤ n :=
  (List.length_filterMap_le _ _).trans hV

lemma length_validVotes_le (n t : ℕ) (timely : Finset ℕ) (ib : Fin n → Option Msg) :
    (validVotes n t timely ib).length ≤ n :=
  (List.length_filterMap_le _ _).trans (by simp)

lemma forall₂_votesFor {n t : ℕ} {timely : Finset ℕ} {a b : ℕ} (ha : a ∈ timely) (hb : b ∈ timely)
    (hab : a < b) (V : List (Finset ℕ × (ℕ → ℚ))) (hV : ∀ R ∈ V, IsValid n t timely R.1 R.2) :
    List.Forall₂ (Spaced (δ n t)) (votesFor V a) (votesFor V b) := by
  induction V with
  | nil => exact .nil
  | cons R V ih =>
    have hR := hV R (by simp) a ha b hb hab
    simp only [votesFor, List.filterMap_cons, hR.1, hR.2.1, if_true]
    refine .cons (by unfold Spaced; linarith [hR.2.2]) (ih fun R' h => hV R' (by simp [h]))

lemma mem_validVotes {n t : ℕ} {timely : Finset ℕ} {ib : Fin n → Option Msg} {R : Finset ℕ × (ℕ → ℚ)}
    (h : R ∈ validVotes n t timely ib) : IsValid n t timely R.1 R.2 := by
  simp only [validVotes, List.mem_filterMap, List.mem_finRange, true_and] at h
  obtain ⟨j, hj⟩ := h
  split at hj
  · split_ifs at hj with hv
    · cases hj; exact hv
  · cases hj

/-- **Lemma 32.** If two ids `a < b` are in the `timely` set of a correct process `q` and spaced
by `δ` in its `ranks` at the beginning of an approximation round, they are still spaced by `δ`
at its end (if both stay accepted; the new values are computed in any case). -/
theorem lemma_32 {n t : ℕ} {sel : ℕ → List ℚ → List ℚ} (hsel : GoodSel n t sel) (hn : 2 * t < n)
    (F : Finset (Fin n)) (x : Fin n → ℕ) (adv : ℕ → Fin n → Fin n → Option Msg) {r : ℕ} (hr : 3 ≤ r)
    (q : Fin n) {a b : ℕ} (ha : a ∈ (run n t sel F x adv r q).timely)
    (hb : b ∈ (run n t sel F x adv r q).timely) (hab : a < b)
    (hsp : (run n t sel F x adv r q).val a + δ n t ≤ (run n t sel F x adv r q).val b) :
    (run n t sel F x adv (r + 1) q).val a + δ n t ≤ (run n t sel F x adv (r + 1) q).val b := by
  obtain ⟨k, rfl⟩ : ∃ k, r = k + 3 := ⟨r - 3, by omega⟩
  simp only [run, step]
  exact newVal_spaced hsel hn hsp
    (forall₂_votesFor ha hb hab _ fun R hR => mem_validVotes hR)
    (length_votesFor_le _ (length_validVotes_le _ _ _ _) _)

end Podc.OrderPreservingByzRenaming.Alg5
