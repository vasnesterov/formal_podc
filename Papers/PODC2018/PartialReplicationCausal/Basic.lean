import Papers.PODC2018.PartialReplicationCausal.Model

/-!
# Basic lemmas: counting updates per edge, stability of the log and of `↪`
-/

namespace Podc.PartialReplicationCausal

open Classical

variable {ι Reg : Type*} (X : ι → Set Reg)

/-- `cnt X s j k a`: the number of updates among `0, …, a - 1` issued by `j` on a register of
`X k`, i.e. on the edge `e_jk`. For an update `c` on `e_jk`, `cnt X s j k (c + 1)` is its position
among the updates on `e_jk` (starting at `1`). -/
noncomputable def cnt (s : State ι Reg) (j k : ι) (a : ℕ) : ℕ :=
  ((Finset.range a).filter fun c => (s.log c).src = j ∧ (s.log c).reg ∈ X k).card

variable {X}

lemma cnt_mono (s : State ι Reg) (j k : ι) {a b : ℕ} (h : a ≤ b) : cnt X s j k a ≤ cnt X s j k b :=
  Finset.card_le_card (Finset.filter_subset_filter _ (Finset.range_subset_range.2 h))

lemma cnt_succ (s : State ι Reg) (j k : ι) (a : ℕ) :
    cnt X s j k (a + 1) =
      cnt X s j k a + if (s.log a).src = j ∧ (s.log a).reg ∈ X k then 1 else 0 := by
  unfold cnt
  rw [Finset.range_add_one, Finset.filter_insert]
  split_ifs with h
  · rw [Finset.card_insert_of_notMem (by simp)]
  · rfl

lemma cnt_pos (s : State ι Reg) {j k : ι} {c : ℕ} (hc : (s.log c).src = j ∧ (s.log c).reg ∈ X k) :
    0 < cnt X s j k (c + 1) := by
  rw [cnt_succ, ite_eq_left hc]; omega

lemma cnt_lt_of_lt (s : State ι Reg) {j k : ι} {c c' : ℕ} (hcc : c < c')
    (hc' : (s.log c').src = j ∧ (s.log c').reg ∈ X k) :
    cnt X s j k (c + 1) < cnt X s j k (c' + 1) := by
  have := cnt_mono (X := X) s j k (show c + 1 ≤ c' by omega)
  rw [cnt_succ s j k c', ite_eq_left hc']; omega

lemma eq_of_cnt_eq (s : State ι Reg) {j k : ι} {c c' : ℕ}
    (hc : (s.log c).src = j ∧ (s.log c).reg ∈ X k) (hc' : (s.log c').src = j ∧ (s.log c').reg ∈ X k)
    (h : cnt X s j k (c + 1) = cnt X s j k (c' + 1)) : c = c' := by
  rcases lt_trichotomy c c' with hlt | heq | hgt
  · exact absurd h (cnt_lt_of_lt s hlt hc').ne
  · exact heq
  · exact absurd h (cnt_lt_of_lt s hgt hc).ne'

/-- Every position `1, …, cnt (c+1)` on edge `e_jk` is taken by an update `≤ c`. -/
lemma exists_cnt_eq (s : State ι Reg) (j k : ι) :
    ∀ (a m : ℕ), 0 < m → m ≤ cnt X s j k a →
      ∃ c < a, (s.log c).src = j ∧ (s.log c).reg ∈ X k ∧ cnt X s j k (c + 1) = m := by
  intro a
  induction a with
  | zero => intro m hm h; simp [cnt] at h; omega
  | succ a ih =>
    intro m hm h
    rw [cnt_succ] at h
    by_cases hc : (s.log a).src = j ∧ (s.log a).reg ∈ X k
    · rw [ite_eq_left hc] at h
      rcases Nat.lt_or_ge m (cnt X s j k a + 1) with hlt | hge
      · obtain ⟨c, hc1, hc2⟩ := ih m hm (by omega)
        exact ⟨c, by omega, hc2⟩
      · refine ⟨a, by omega, hc.1, hc.2, ?_⟩
        rw [cnt_succ, ite_eq_left hc]; omega
    · rw [ite_eq_right hc] at h
      obtain ⟨c, hc1, hc2⟩ := ih m hm (by omega)
      exact ⟨c, by omega, hc2⟩

lemma cnt_congr {s s' : State ι Reg} {a : ℕ} (h : ∀ c < a, s'.log c = s.log c) (j k : ι) :
    cnt X s' j k a = cnt X s j k a := by
  unfold cnt
  congr 1
  apply Finset.filter_congr
  intro c hc
  rw [h c (Finset.mem_range.1 hc)]

/-! ### `↪` -/

lemma hb_mono {s s' : State ι Reg} (hn : s.n ≤ s'.n) (h : ∀ c < s.n, s'.log c = s.log c)
    {a b : ℕ} (hab : HB s a b) : HB s' a b := by
  unfold HB at *
  refine Relation.TransGen.mono ?_ _ _ hab
  rintro x y ⟨hy, hx⟩
  exact ⟨by omega, by rwa [h y hy]⟩

lemma hb_lt_n {s : State ι Reg} {a b : ℕ} (hab : HB s a b) : b < s.n := by
  induction hab with
  | single h => exact h.1
  | tail _ h _ => exact h.1

lemma hb_back {s s' : State ι Reg} (h : ∀ c < s.n, s'.log c = s.log c)
    (hpre : ∀ c < s.n, ∀ d ∈ (s.log c).pre, d < s.n)
    {a b : ℕ} (hab : HB s' a b) (hb : b < s.n) : HB s a b := by
  induction hab with
  | single h' =>
    refine .single ⟨hb, ?_⟩
    rw [← h _ hb]; exact h'.2
  | @tail y z _ h' ih =>
    have hc : y ∈ (s.log z).pre := by rw [← h _ hb]; exact h'.2
    exact .tail (ih (hpre _ hb _ hc)) ⟨hb, hc⟩

end Podc.PartialReplicationCausal
