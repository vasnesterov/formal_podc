import Papers.PODC2015.AlmostStableMatchings.Counting

/-!
# Bounding the remaining lists of the bad men (Lemma 4.4)

`sum_bad_card_le`: at the end of `ASM`, `ℓ · ∑_{m bad} |Q^m| ≤ 8 k |E|`.

**The proof differs from the paper's.** The paper argues that the bad men at the end are the men
that were bad when they left the active set (`B_i`), and that "the number of bad men cannot
increase after a call to `QuantileMatch`". This overlooks *inactive* men: a man who is matched
when he becomes inactive (in iteration `j`, `|Q^m| < 2^j`) can later be rejected by his partner
when an active man proposes to her; he then stays unmatched with a nonempty list forever, i.e. he
becomes bad without being active. We account for such men with the per-man potential
`F(m) = 2^j` (matched) / `|Q^m|` (unmatched) of an inactive man, which never increases during
iteration `j` (`reach_Fpot`), together with `matched_inactive_le`: the number of inactive
men displaced in iteration `j` is at most the number of bad active men at the start of iteration
`j`. Summing over the iterations gives the paper's bound `∑_{m bad} |Q^m| ≤ ∑_i 2^{i+1} b_i`,
where `b_i` is the number of bad active men at the end of iteration `i`, and Lemma 4.5 bounds
`ℓ b_i ≤ 2k |act_i|`; finally `∑_i 2^i |act_i| ≤ 2 |E|`.
-/

set_option linter.unusedSectionVars false

namespace Papers.PODC2015.AlmostStableMatchings

open Finset

variable {M W : Type*} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]

namespace Prefs

variable {P : Prefs M W} {k : ℕ} {mm : MMOracle M W} {act : Finset M} {j : ℕ}

/-! ## Inactive men within one iteration -/

/-- Potential of an inactive man in iteration `j`. -/
def Fpot (j : ℕ) (s : St M W) (m : M) : ℕ := if s.pm m = none then #(s.Q m) else 2 ^ j

lemma istep_Fpot {s s' : St M W} (hI : P.IInv k j act s) (h : P.IStep k mm act s s') {m : M}
    (hm : m ∉ act) : Fpot j s' m ≤ Fpot j s m := by
  have hQ := Finset.card_le_card (istep_Q h m)
  unfold Fpot
  by_cases h0 : s.pm m = none
  · rw [ite_eq_left (istep_inactive_pm hI h hm h0), ite_eq_left h0]; exact hQ
  · rw [ite_eq_right h0]
    split_ifs
    · exact (hQ.trans_lt (hI.Q_inact m hm)).le
    · exact le_rfl

lemma reach_Fpot {s s' : St M W} (hI : P.IInv k j act s)
    (h : Relation.ReflTransGen (P.IStep k mm act) s s') {m : M} (hm : m ∉ act) :
    Fpot j s' m ≤ Fpot j s m := by
  induction h with
  | refl => exact le_rfl
  | tail hr hst ih => exact (istep_Fpot (hI.reach hr) hst hm).trans ih

/-- Unmatched-list mass of the men outside `act`. -/
def Vmass (act : Finset M) (s : St M W) : ℕ :=
  ∑ m, if m ∉ act ∧ s.pm m = none then #(s.Q m) else 0

/-- Number of matched men outside `act`. -/
def MI (act : Finset M) (s : St M W) : ℕ :=
  ∑ m, if m ∉ act ∧ s.pm m ≠ none then 1 else 0

lemma MI_eq (act : Finset M) (s : St M W) : MI act s = #(actᶜ.filter fun m => s.pm m ≠ none) := by
  rw [MI, ← Finset.card_filter]
  congr 1; ext m; simp

lemma card_filter_mem_badSet (X : Finset M) (s : St M W) :
    #(X.filter fun m => m ∈ badSet s) = ∑ m, if m ∈ X ∧ m ∈ badSet s then 1 else 0 := by
  rw [← Finset.card_filter]; congr 1; ext m; simp

lemma sum_Fpot (act : Finset M) (s : St M W) :
    ∑ m, (if m ∉ act then Fpot j s m else 0) = Vmass act s + 2 ^ j * MI act s := by
  rw [Vmass, MI, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  unfold Fpot
  by_cases h1 : m ∈ act <;> by_cases h2 : s.pm m = none <;> simp [h1, h2]

/-- Within one iteration, the potential of the inactive men never increases. -/
lemma inactive_mass {s s' : St M W} (hI : P.IInv k j act s)
    (h : Relation.ReflTransGen (P.IStep k mm act) s s') :
    Vmass act s' + 2 ^ j * MI act s' ≤ Vmass act s + 2 ^ j * MI act s := by
  rw [← sum_Fpot, ← sum_Fpot]
  refine Finset.sum_le_sum fun m _ => ?_
  split_ifs with hm
  · exact le_rfl
  · exact reach_Fpot hI h hm

/-- Within one iteration, the inactive men that lose their partner are at most the bad active
men at its start. -/
lemma inactive_displaced (hk : 1 ≤ k) {s s' : St M W} (hI : P.IInv k j act s)
    (h : Relation.ReflTransGen (P.IStep k mm act) s s') :
    MI act s ≤ MI act s' + #(act.filter fun m => m ∈ badSet s) := by
  rw [MI_eq, MI_eq]
  exact matched_inactive_le hI.inv (hI.reach h).inv (reach_pw hk hI h)
    (fun m hm => reach_inactive_pm hI h hm) (reach_Q h)

/-- Moving from iteration `j` (active set `A`) to iteration `j + 1` (active set `B ⊆ A`), in the
same state. -/
lemma transition {s : St M W} {A B : Finset M} (hBA : B ⊆ A)
    (hQ : ∀ m ∈ A, m ∉ B → #(s.Q m) < 2 ^ (j + 1)) :
    Vmass B s + 2 ^ (j + 1) * #(B.filter fun m => m ∈ badSet s) ≤
      Vmass A s + 2 ^ (j + 1) * #(A.filter fun m => m ∈ badSet s) := by
  rw [card_filter_mem_badSet, card_filter_mem_badSet, Vmass, Vmass, Finset.mul_sum,
    Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun m _ => ?_
  by_cases hB : m ∈ B
  · have hA := hBA hB
    simp [hA, hB]
  · by_cases hA : m ∈ A
    · have := hQ m hA hB
      simp only [hB, not_false_eq_true, true_and, hA, not_true_eq_false, false_and,
        ↓reduceIte, mul_zero, add_zero, zero_add, mem_badSet]
      split_ifs with h1 h2 <;> simp_all [Finset.not_nonempty_iff_eq_empty]
      exact (hQ m hA hB).le
    · simp [hA, hB]

/-! ## The whole run -/

variable (P k mm) in
/-- Start state of iteration `i`. -/
abbrev st (ℓ i : ℕ) : St M W := P.stage k mm ℓ i

variable (P k mm) in
/-- Active men of iteration `i`. -/
abbrev ac (ℓ i : ℕ) : Finset M := P.active i (st P k mm ℓ i)

lemma qmIter_A_empty (hk : 1 ≤ k) {s : St M W} (hI : P.Inv k s) (hA : ∀ m, s.A m = ∅)
    (ℓ : ℕ) (m : M) : ((P.quantileMatch k mm act)^[ℓ] s).A m = ∅ := by
  cases ℓ with
  | zero => exact hA m
  | succ ℓ =>
    rw [Function.iterate_succ_apply']
    exact quantileMatch_A hk (by
      clear hA
      induction ℓ generalizing s with
      | zero => exact hI
      | succ t ih => rw [Function.iterate_succ_apply]; exact ih hI.quantileMatch) m

lemma stage_A_empty (hk : 1 ≤ k) (ℓ : ℕ) : ∀ i m, (st P k mm ℓ i).A m = ∅
  | 0, m => rfl
  | i + 1, m => qmIter_A_empty hk (inv_stage mm ℓ i) (stage_A_empty hk ℓ i) ℓ m

lemma stage_IInv (hk : 1 ≤ k) (ℓ i : ℕ) : P.IInv k i (ac P k mm ℓ i) (st P k mm ℓ i) where
  inv := inv_stage mm ℓ i
  A_inact m _ := stage_A_empty hk ℓ i m
  Q_inact m hm := by simpa [active] using hm

lemma reach_stage (ℓ i : ℕ) : Relation.ReflTransGen (P.IStep k mm (ac P k mm ℓ i))
    (st P k mm ℓ i) (st P k mm ℓ (i + 1)) := reach_qmIter ℓ

lemma card_Q_le (ℓ i : ℕ) (m : M) : #((st P k mm ℓ i).Q m) ≤ P.degM m := by
  rw [← P.card_NM]; exact Finset.card_le_card ((inv_stage (k := k) mm ℓ i).Q_sub m)

lemma Q_stage_succ (ℓ i : ℕ) (m : M) : (st P k mm ℓ (i + 1)).Q m ⊆ (st P k mm ℓ i).Q m :=
  reach_Q (reach_stage ℓ i) m

/-- Bad active men at the end of iteration `i`. -/
abbrev bcount (P : Prefs M W) (k : ℕ) (mm : MMOracle M W) (ℓ i : ℕ) : ℕ :=
  #((ac P k mm ℓ i).filter fun m => m ∈ badSet (st P k mm ℓ (i + 1)))

/-- The main accounting: `V_j(s_j) + 2^j min(c_j, MI_j(s_j)) ≤ ∑_{i < j} 2^{i+1} b_i`. -/
lemma accounting (hk : 1 ≤ k) (ℓ : ℕ) : ∀ j,
    Vmass (ac P k mm ℓ j) (st P k mm ℓ j) +
      2 ^ j * min #((ac P k mm ℓ j).filter fun m => m ∈ badSet (st P k mm ℓ j))
        (MI (ac P k mm ℓ j) (st P k mm ℓ j)) ≤
      ∑ i ∈ Finset.range j, 2 ^ (i + 1) * bcount P k mm ℓ i
  | 0 => by
    have h1 : Vmass (ac P k mm ℓ 0) (st P k mm ℓ 0) = 0 := by
      refine Finset.sum_eq_zero fun m _ => ?_
      split_ifs with h
      · have := h.1; simp only [active, pow_zero, Finset.mem_filter, Finset.mem_univ, true_and,
          not_le, Nat.lt_one_iff] at this
        exact this
      · rfl
    have h2 : MI (ac P k mm ℓ 0) (st P k mm ℓ 0) = 0 := by
      refine Finset.sum_eq_zero fun m _ => ?_
      simp [st, stage, init]
    simp [h1, h2]
  | j + 1 => by
    have ih := accounting hk ℓ j
    have hI := stage_IInv (mm := mm) (P := P) hk ℓ j
    have h1 := inactive_mass hI (reach_stage ℓ j)
    have h2 := inactive_displaced hk hI (reach_stage ℓ j)
    have h3 := transition (s := st P k mm ℓ (j + 1)) (j := j)
      (A := ac P k mm ℓ j) (B := ac P k mm ℓ (j + 1))
      (fun m hm => by
        simp only [active, Finset.mem_filter, Finset.mem_univ, true_and] at hm ⊢
        have := Finset.card_le_card (Q_stage_succ (P := P) (k := k) (mm := mm) ℓ j m)
        rw [pow_succ] at hm; omega)
      (fun m _ hm => by simpa [active] using hm)
    rw [Finset.sum_range_succ]
    have h4 : min #((ac P k mm ℓ (j + 1)).filter fun m => m ∈ badSet (st P k mm ℓ (j + 1)))
        (MI (ac P k mm ℓ (j + 1)) (st P k mm ℓ (j + 1))) ≤
        #((ac P k mm ℓ (j + 1)).filter fun m => m ∈ badSet (st P k mm ℓ (j + 1))) :=
      min_le_left _ _
    have h5 := Nat.mul_le_mul_left (2 ^ (j + 1)) h4
    -- `V_j(s_{j+1}) ≤ V_j(s_j) + 2^j min(c_j, MI_j(s_j))`
    have h6 : Vmass (ac P k mm ℓ j) (st P k mm ℓ (j + 1)) ≤ Vmass (ac P k mm ℓ j) (st P k mm ℓ j) +
        2 ^ j * min #((ac P k mm ℓ j).filter fun m => m ∈ badSet (st P k mm ℓ j))
          (MI (ac P k mm ℓ j) (st P k mm ℓ j)) := by
      rcases min_choice #((ac P k mm ℓ j).filter fun m => m ∈ badSet (st P k mm ℓ j))
          (MI (ac P k mm ℓ j) (st P k mm ℓ j)) with e | e <;> rw [e]
      · have := Nat.mul_le_mul_left (2 ^ j) h2
        rw [Nat.mul_add] at this; omega
      · omega
    unfold bcount at *
    omega

lemma sum_geom_le (n d : ℕ) : ∑ i ∈ Finset.range n, (if 2 ^ i ≤ d then 2 ^ i else 0) ≤ 2 * d := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · refine (Finset.sum_eq_zero fun i _ => ?_).le
    have := Nat.one_le_two_pow (n := i); rw [ite_eq_right (by omega)]
  have hgeom : ∀ t, ∑ i ∈ Finset.range t, 2 ^ i + 1 = 2 ^ t := by
    intro t; induction t with
    | zero => simp
    | succ t ih => rw [Finset.sum_range_succ, pow_succ]; omega
  have hsub : ∑ i ∈ Finset.range n, (if 2 ^ i ≤ d then 2 ^ i else 0) ≤
      ∑ i ∈ Finset.range (Nat.log 2 d + 1), 2 ^ i := by
    rw [← Finset.sum_filter]
    refine Finset.sum_le_sum_of_subset fun i hi => ?_
    simp only [Finset.mem_filter, Finset.mem_range] at hi ⊢
    have := Nat.le_log_of_pow_le (by norm_num) hi.2
    omega
  have h1 := hgeom (Nat.log 2 d + 1)
  have h2 := Nat.pow_log_le_self 2 (by omega : d ≠ 0)
  rw [pow_succ] at h1
  omega

/-- `∑_i 2^i |act_i| ≤ 2 |E|`. -/
lemma sum_pow_card_ac_le (ℓ L : ℕ) :
    ∑ i ∈ Finset.range L, 2 ^ i * #(ac P k mm ℓ i) ≤ 2 * P.E.card := by
  rw [P.card_E_eq_sum_degM, Finset.mul_sum]
  have : ∀ i, 2 ^ i * #(ac P k mm ℓ i) = ∑ m, if m ∈ ac P k mm ℓ i then 2 ^ i else 0 := by
    intro i
    rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, smul_eq_mul, Nat.mul_comm]
  simp_rw [this]
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum fun m _ => le_trans (Finset.sum_le_sum fun i _ => ?_)
    (sum_geom_le L (P.degM m))
  split_ifs with h1 h2
  · exact le_rfl
  · exfalso; apply h2
    simp only [active, Finset.mem_filter, Finset.mem_univ, true_and] at h1
    exact h1.trans (card_Q_le ℓ i m)
  · exact Nat.zero_le _
  · exact le_rfl

/-- **Lemma 4.4 (the core estimate).** At the end of `ASM`, provided every degree is
`< 2^{L+1}`, the remaining lists of the bad men have total size at most `8k|E|/ℓ`. -/
theorem sum_bad_card_le (hk : 1 ≤ k) (ℓ L : ℕ) (hL : ∀ m, P.degM m < 2 ^ (L + 1)) :
    ℓ * ∑ m ∈ badSet (P.asm k mm ℓ L), #((P.asm k mm ℓ L).Q m) ≤ 8 * k * P.E.card := by
  have hacc := accounting (P := P) (mm := mm) hk ℓ (L + 1)
  have hempty : ac P k mm ℓ (L + 1) = ∅ := by
    refine Finset.eq_empty_of_forall_notMem fun m hm => ?_
    simp only [active, Finset.mem_filter, Finset.mem_univ, true_and] at hm
    have := card_Q_le (P := P) (k := k) (mm := mm) ℓ (L + 1) m
    have := hL m; omega
  have hV : Vmass (ac P k mm ℓ (L + 1)) (st P k mm ℓ (L + 1)) =
      ∑ m ∈ badSet (P.asm k mm ℓ L), #((P.asm k mm ℓ L).Q m) := by
    rw [hempty, Vmass, badSet, Finset.sum_filter]
    refine Finset.sum_congr rfl fun m _ => ?_
    simp only [Finset.notMem_empty, not_false_eq_true, true_and]
    by_cases h1 : (st P k mm ℓ (L + 1)).pm m = none
    · by_cases h2 : ((st P k mm ℓ (L + 1)).Q m).Nonempty
      · simp [h1, h2, asm]
      · simp [h1, asm, Finset.not_nonempty_iff_eq_empty.1 h2]
    · simp [h1, asm]
  have hb : ∀ i, ℓ * bcount P k mm ℓ i ≤ 2 * k * #(ac P k mm ℓ i) := fun i =>
    lemma_4_5 hk (stage_IInv (mm := mm) hk ℓ i) ℓ
  have hsum := sum_pow_card_ac_le (P := P) (k := k) (mm := mm) ℓ (L + 1)
  calc ℓ * ∑ m ∈ badSet (P.asm k mm ℓ L), #((P.asm k mm ℓ L).Q m)
      ≤ ℓ * ∑ i ∈ Finset.range (L + 1), 2 ^ (i + 1) * bcount P k mm ℓ i := by
        rw [← hV]; exact Nat.mul_le_mul_left ℓ (le_trans (Nat.le_add_right _ _) hacc)
    _ = ∑ i ∈ Finset.range (L + 1), 2 ^ (i + 1) * (ℓ * bcount P k mm ℓ i) := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => by ring
    _ ≤ ∑ i ∈ Finset.range (L + 1), 2 ^ (i + 1) * (2 * k * #(ac P k mm ℓ i)) :=
        Finset.sum_le_sum fun i _ => Nat.mul_le_mul_left _ (hb i)
    _ = 4 * k * ∑ i ∈ Finset.range (L + 1), 2 ^ i * #(ac P k mm ℓ i) := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => by ring
    _ ≤ 4 * k * (2 * P.E.card) := Nat.mul_le_mul_left _ hsum
    _ = 8 * k * P.E.card := by ring

end Prefs

end Papers.PODC2015.AlmostStableMatchings
