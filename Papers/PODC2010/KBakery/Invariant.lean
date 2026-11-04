import Papers.PODC2010.KBakery.Defs

/-!
# The inductive invariant of the k-Bakery
-/

set_option linter.unusedSectionVars false

namespace Podc.KBakery

open Finset

variable {P : Type} [LinearOrder P] [Fintype P]
variable {fife : Bool} {k : ℕ} {s : Cfg P} {p i q r : P} {v : ℕ}

lemma ticket_mono (hI : Inv k s) (ha : Admissible s p i) (j : P) :
    s.ticket j ≤ (stepAt fife k s p i).ticket j := by
  by_cases hj : j = p
  · subst hj
    rcases hpc : s.pc j with _ | rem | ⟨acc, rem⟩ | rem | ⟨pred, cap⟩ | ⟨pred, rem⟩ |
      ⟨pred, rem, cap⟩ | rem | _ | rem <;>
      simp only [stepAt_ticket, core, hpc] <;> (try split_ifs) <;> try simp
    -- line 15, writing the ticket
    rename_i hi
    have h0 : rem = ∅ := by
      have := admissible_of_not_mem ha (by simpa [hpc, PC.rem] using hi)
      simpa [hpc, PC.rem] using this
    subst h0
    have := hI.g1 j acc ∅ hpc (by simp)
    omega
  · simp [core_ticket_ne hj]

lemma safe_step (hI : Inv k s) (ha : Admissible s p i) (hv : v ≤ s.ticket r)
    (h : Safe s q v r) : Safe (stepAt fife k s p i) q v r := by
  by_cases hq : q = p
  · subst hq
    rcases hpc : s.pc q with _ | rem | ⟨acc, rem⟩ | rem | ⟨pred, cap⟩ | ⟨pred, rem⟩ |
      ⟨pred, rem, cap⟩ | rem | _ | rem <;>
      simp only [Safe, hpc] at h <;>
      simp only [Safe, stepAt_pc, stepAt_ticket, core, hpc] <;> (try split_ifs) <;>
      (try simp) <;> first
        | exact h
        | exact Or.inr ⟨r, hv⟩
        | (rename_i hi
           rcases h with h | ⟨j, hj, hj'⟩
           · exact Or.inl (Or.inl h)
           · by_cases hji : j = i
             · subst hji; exact Or.inl (Or.inr hj')
             · exact Or.inr ⟨j, ⟨hji, hj⟩, hj'⟩)
        | (rename_i hi
           have h0 := admissible_of_not_mem ha (by simpa [hpc, PC.rem] using hi)
           simp only [hpc, PC.rem] at h0
           subst h0
           simp only [Finset.notMem_empty, false_and, exists_false, or_false] at h
           exact Or.inl (by omega))
  · have hpc := core_pc_ne (fife := fife) (k := k) (s := s) (i := i) hq
    have ht := core_ticket_ne (fife := fife) (k := k) (s := s) (i := i) hq
    unfold Safe at h ⊢
    simp only [stepAt_pc, stepAt_ticket, hpc, ht]
    rcases hq' : s.pc q with _ | rem | ⟨acc, rem⟩ | rem | ⟨pred, cap⟩ | ⟨pred, rem⟩ |
      ⟨pred, rem, cap⟩ | rem | _ | rem <;> simp only [hq'] at h ⊢ <;> try exact h
    rcases h with h | ⟨j, hj, hj'⟩
    · exact Or.inl h
    · exact Or.inr ⟨j, hj, hj'.trans (ticket_mono hI ha j)⟩

lemma U_step (hI : Inv k s) (ha : Admissible s p i) (hv : v ≤ s.ticket r) :
    U (stepAt fife k s p i) v r ⊆ U s v r := by
  intro q hq
  rw [mem_U] at hq ⊢
  exact ⟨hq.1, fun h => hq.2 (safe_step hI ha hv h)⟩

lemma card_U_step (hI : Inv k s) (ha : Admissible s p i) (hv : v ≤ s.ticket r) :
    (U (stepAt fife k s p i) v r).card ≤ (U s v r).card :=
  card_le_card (U_step hI ha hv)

/-- Safety for a larger pair implies safety for a smaller ticket. -/
lemma safe_anti {s : Cfg P} {q r p' : P} {v w : ℕ} (hw : w < v) (h : Safe s q v r) :
    Safe s q w p' := by
  unfold Safe at h ⊢
  rcases hq' : s.pc q with _ | rem | ⟨acc, rem⟩ | rem | ⟨pred, cap⟩ | ⟨pred, rem⟩ |
      ⟨pred, rem, cap⟩ | rem | _ | rem <;> simp only [hq'] at h ⊢ <;>
    first
    | trivial
    | (rcases h with h | ⟨j, hj, hj'⟩
       · exact Or.inl (by omega)
       · exact Or.inr ⟨j, hj, by omega⟩)
    | (left; rcases h with h | ⟨h, -⟩ <;> omega)

omit [Fintype P] in
lemma wantGood_coe {v w : ℕ} {r q : P} : wantGood v r (w : WithTop ℕ) q ↔ lexLt v r w q := by
  simp [wantGood, lexLt]

omit [Fintype P] in
lemma le_of_wantGood {v : ℕ} {r q : P} {w : WithTop ℕ} (h : wantGood v r w q) :
    (v : WithTop ℕ) ≤ w := by
  rcases h with h | ⟨h, -⟩
  · exact h.le
  · exact h.le

omit [Fintype P] in
lemma lt_of_wantGood_of_lt {v t : ℕ} {r q : P} {w : WithTop ℕ} (h : wantGood v r w q)
    (ht : w < t) : v < t := by
  have := (le_of_wantGood h).trans_lt ht
  exact_mod_cast this

lemma safe_of_wantGood (hI : Inv k s) (hqp : q ≠ p)
    (hg : wantGood (s.ticket p) p (s.want q p) q) : Safe s q (s.ticket p) p := by
  have hw := hI.wantC q p hqp
  unfold WantSpec at hw
  unfold Safe
  rcases hq' : s.pc q with _ | rem | ⟨acc, rem⟩ | rem | ⟨pred, cap⟩ | ⟨pred, rem⟩ |
      ⟨pred, rem, cap⟩ | rem | _ | rem <;> simp only [hq'] at hw ⊢ <;> try trivial
  · -- line 15
    rw [hw] at hg
    have h1 : s.ticket p ≤ s.ticket q := by exact_mod_cast le_of_wantGood hg
    by_cases hqr : q ∈ rem
    · exact Or.inr ⟨q, hqr, h1⟩
    · exact Or.inl (h1.trans (hI.g1 q acc rem hq' hqr))
  · -- line 16
    split_ifs at hw with hpr
    · exact Or.inl (lt_of_wantGood_of_lt hg hw)
    · rwa [hw, wantGood_coe] at hg
  all_goals rwa [hw, wantGood_coe] at hg

/-! ### Preservation of the invariant, field by field -/

lemma g1_step (hI : Inv k s) (ha : Admissible s p i) :
    ∀ q acc rem, (stepAt fife k s p i).pc q = .d15 acc rem → q ∉ rem →
      (stepAt fife k s p i).ticket q ≤ acc := by
  intro q acc rem h hq
  by_cases hqp : q = p
  · subst hqp
    rcases hpc : s.pc q with _ | rem' | ⟨acc', rem'⟩ | rem' | ⟨pred, cap⟩ | ⟨pred, rem'⟩ |
      ⟨pred, rem', cap⟩ | rem' | _ | rem' <;>
      simp only [stepAt_pc, stepAt_ticket, core, hpc] at h ⊢ <;> (try split_ifs at h ⊢) <;>
      simp at h
    · obtain ⟨-, rfl⟩ := h; simp at hq
    · obtain ⟨rfl, rfl⟩ := h
      rename_i hi
      simp only [Finset.mem_erase, not_and] at hq
      by_cases hqi : q = i
      · subst hqi; simp
      · exact (hI.g1 q acc' rem' hpc fun h' => hq hqi h').trans (le_max_left _ _)
  · rw [stepAt_pc, core_pc_ne hqp] at h
    rw [stepAt_ticket, core_ticket_ne hqp]
    exact hI.g1 q acc rem h hq

lemma wantC_step (hI : Inv k s) (ha : Admissible s p i) :
    ∀ q p', q ≠ p' → WantSpec (stepAt fife k s p i) q p' := by
  intro q p' hqp'
  have hw := hI.wantC q p' hqp'
  by_cases hqp : q = p
  · subst hqp
    unfold WantSpec at hw ⊢
    rcases hpc : s.pc q with _ | rem' | ⟨acc', rem'⟩ | rem' | ⟨pred, cap⟩ | ⟨pred, rem'⟩ |
      ⟨pred, rem', cap⟩ | rem' | _ | rem' <;>
      simp only [hpc] at hw <;>
      simp only [stepAt_pc, stepAt_ticket, stepAt_want, core, hpc] <;> (try split_ifs) <;>
      simp [Function.update_apply, hqp'.symm] at hw ⊢ <;> first
      | exact hw
      | (rename_i hi
         have h0 := admissible_of_not_mem ha (by simpa [hpc, PC.rem] using hi)
         simp only [hpc, PC.rem] at h0
         subst h0
         try simp at hw
         first
         | exact hw
         | (have := hI.g1 q acc' ∅ hpc (by simp)
            rw [hw]
            exact_mod_cast (by omega : s.ticket q < acc' + 1)))
      | (by_cases h' : p' = i <;> by_cases h'' : p' ∈ rem' <;> simp_all)
  · rw [WantSpec, stepAt_pc, core_pc_ne hqp, stepAt_want, core_want_ne hqp, stepAt_ticket,
      core_ticket_ne hqp]
    exact hw

lemma capture_step_of_ne (h : r ≠ p) (x : P) :
    (stepAt fife k s p i).capture r x = s.capture r x := by
  simp [core_capture_ne h]

lemma capLe_step (hI : Inv k s) (ha : Admissible s p i) :
    ∀ r x, (stepAt fife k s p i).capture r x ≤ (stepAt fife k s p i).ticket r := by
  intro r x
  by_cases hr : r = p
  · subst hr
    by_cases hc : ∀ rem, s.pc r ≠ .cap23 rem
    · rw [stepAt_capture, core_capture_self_of_ne_cap23 hc]
      exact (hI.capLe r x).trans (ticket_mono hI ha r)
    · push Not at hc
      obtain ⟨rem, hpc⟩ := hc
      simp only [stepAt_capture, stepAt_ticket, core, hpc]
      split_ifs
      · by_cases hx : x = i <;> simp [hx, hI.capLe r x]
      · exact hI.capLe r x
  · rw [capture_step_of_ne hr]
    exact (hI.capLe r x).trans (ticket_mono hI ha r)

lemma capLt_step (hI : Inv k s) (ha : Admissible s p i) :
    ∀ q, ((stepAt fife k s p i).pc q).PreCap →
      ∀ x, (stepAt fife k s p i).capture q x < (stepAt fife k s p i).ticket q := by
  intro q hq x
  by_cases hqp : q = p
  · subst hqp
    rcases hpc : s.pc q with _ | rem' | ⟨acc', rem'⟩ | rem' | ⟨pred, cap⟩ | ⟨pred, rem'⟩ |
      ⟨pred, rem', cap⟩ | rem' | _ | rem' <;>
      simp only [stepAt_pc, stepAt_capture, stepAt_ticket, core, hpc] at hq ⊢ <;>
      (try split_ifs at hq ⊢) <;> simp [PC.PreCap] at hq <;>
      simp only [setPc_capture, setPc_ticket, Function.update_self] <;>
      first
      | exact hI.capLt q (by simp [hpc, PC.PreCap]) x
      | (have := hI.capLe q x
         rename_i hi
         have h0 := admissible_of_not_mem ha (by simpa [hpc, PC.rem] using hi)
         simp only [hpc, PC.rem] at h0
         subst h0
         have := hI.g1 q acc' ∅ hpc (by simp)
         omega)
  · rw [stepAt_pc, core_pc_ne hqp] at hq
    rw [capture_step_of_ne hqp, stepAt_ticket, core_ticket_ne hqp]
    exact hI.capLt q hq x

lemma predNot_step (hI : Inv k s) : ∀ q, q ∉ ((stepAt fife k s p i).pc q).pred := by
  intro q
  by_cases hqp : q = p
  · subst hqp
    have h1 := hI.predNot q
    rcases hpc : s.pc q with _ | rem' | ⟨acc', rem'⟩ | rem' | ⟨pred, cap⟩ | ⟨pred, rem'⟩ |
      ⟨pred, rem', cap⟩ | rem' | _ | rem' <;>
      simp only [hpc] at h1 <;>
      simp only [stepAt_pc, core, hpc] <;> (try split_ifs) <;>
      simp_all [PC.pred]
  · rw [stepAt_pc, core_pc_ne hqp]; exact hI.predNot q

lemma scanNot_step (hI : Inv k s) :
    ∀ q pred rem, (stepAt fife k s p i).pc q = .scan pred rem → q ∉ rem := by
  intro q pred rem h
  by_cases hqp : q = p
  · subst hqp
    have h1 := hI.predNot q
    rcases hpc : s.pc q with _ | rem' | ⟨acc', rem'⟩ | rem' | ⟨pred', cap⟩ | ⟨pred', rem'⟩ |
      ⟨pred', rem', cap⟩ | rem' | _ | rem' <;>
      simp only [hpc] at h1 <;>
      simp only [stepAt_pc, core, hpc] at h <;> (try split_ifs at h) <;>
      simp at h <;> (try simp_all [PC.pred]) <;>
      first
      | (obtain ⟨-, rfl⟩ := h; simp [hI.scanNot q _ _ hpc])
      | (obtain ⟨h2, h3⟩ := h; rw [← h3, h2]; exact h1)
  · rw [stepAt_pc, core_pc_ne hqp] at h; exact hI.scanNot q pred rem h

lemma s1_step (hI : Inv k s) (ha : Admissible s p i) :
    ∀ p', ((stepAt fife k s p i).pc p').InLoop → ∀ q, q ≠ p' →
      q ∉ ((stepAt fife k s p i).pc p').pred →
      Safe (stepAt fife k s p i) q ((stepAt fife k s p i).ticket p') p' := by
  intro p' hl q hqp hq
  by_cases hpp : p' = p
  · subst hpp
    by_cases h15 : ∃ acc rem, s.pc p' = .d15 acc rem
    · obtain ⟨acc, rem, hpc⟩ := h15
      simp only [stepAt_pc, core, hpc] at hl
      split_ifs at hl <;> simp [PC.InLoop] at hl
    push Not at h15
    rw [stepAt_ticket, core_ticket_self_of_ne_d15 h15]
    apply safe_step hI ha le_rfl
    have hs1 := hI.s1 p'
    rcases hpc : s.pc p' with _ | rem' | ⟨acc', rem'⟩ | rem' | ⟨pred, cap⟩ | ⟨pred, rem'⟩ |
      ⟨pred, rem', cap⟩ | rem' | _ | rem' <;>
      simp only [hpc, PC.InLoop, PC.pred] at hs1 <;>
      simp only [stepAt_pc, core, hpc] at hl hq <;> (try split_ifs at hl hq) <;>
      (try cases fife) <;> simp [PC.InLoop, PC.pred] at hl hq <;>
      first
      | exact hs1 trivial q hqp hq
      | exact absurd hq hqp
      | (rename_i hi hg
         by_cases hqi : q = i
         · subst hqi; exact safe_of_wantGood hI hqp hg
         · exact hs1 trivial q hqp (fun h => hq hqi h))
  · rw [stepAt_pc, core_pc_ne hpp] at hl hq
    rw [stepAt_ticket, core_ticket_ne hpp]
    exact safe_step hI ha le_rfl (hI.s1 p' hl q hqp hq)

lemma witness_step (hI : Inv k s) (ha : Admissible s p i) {t : ℕ}
    (h : ∃ v r, r ≠ q ∧ t < v ∧ v ≤ s.ticket r ∧ (U s v r).card < k) :
    ∃ v r, r ≠ q ∧ t < v ∧ v ≤ (stepAt fife k s p i).ticket r ∧
      (U (stepAt fife k s p i) v r).card < k := by
  obtain ⟨v, r, h1, h2, h3, h4⟩ := h
  exact ⟨v, r, h1, h2, h3.trans (ticket_mono hI ha r),
    (card_U_step hI ha h3).trans_lt h4⟩

lemma s3_step (hI : Inv k s) (ha : Admissible s p i) :
    ∀ p', ((stepAt fife k s p i).pc p').Captured →
      ∃ v r, r ≠ p' ∧ (stepAt fife k s p i).ticket p' < v ∧
        v ≤ (stepAt fife k s p i).ticket r ∧ (U (stepAt fife k s p i) v r).card < k := by
  intro p' hc
  by_cases hpp : p' = p
  · subst hpp
    by_cases h15 : ∃ acc rem, s.pc p' = .d15 acc rem
    · obtain ⟨acc, rem, hpc⟩ := h15
      simp only [stepAt_pc, core, hpc] at hc
      split_ifs at hc <;> simp [PC.Captured] at hc
    push Not at h15
    rw [stepAt_ticket, core_ticket_self_of_ne_d15 h15]
    apply witness_step hI ha
    have hs3 := hI.s3 p'
    rcases hpc : s.pc p' with _ | rem' | ⟨acc', rem'⟩ | rem' | ⟨pred, cap⟩ | ⟨pred, rem'⟩ |
      ⟨pred, rem', cap⟩ | rem' | _ | rem' <;>
      simp only [hpc, PC.Captured] at hs3 <;>
      simp only [stepAt_pc, core, hpc] at hc <;> (try split_ifs at hc) <;>
      (try cases fife) <;> (try cases cap) <;> simp [PC.Captured] at hc <;>
      (try exact hs3 trivial)
    -- a new capture detected at line 22
    all_goals
      by_cases hlt : s.ticket p' < s.capture i p'
      swap
      · simp [hlt] at hc
      clear hc
      have hip : i ≠ p' := by
        rintro rfl
        have := hI.capLt i (by simp [hpc, PC.PreCap]) i
        omega
      exact ⟨s.capture i p', i, hip, hlt, hI.capLe i p', hI.s5 i p' (by omega)⟩
  · rw [stepAt_pc, core_pc_ne hpp] at hc
    rw [stepAt_ticket, core_ticket_ne hpp]
    exact witness_step hI ha (hI.s3 p' hc)

/-- The capture case of the loop exit: a process `p` captured with a pair `(v, r)`, `v > Ticket[p]`,
has at most as many unsafe processes as `(v, r)` has (it is itself unsafe for `(v, r)`, and only `r`
may be unsafe for `p` but not for `(v, r)`). -/
lemma card_U_le_of_capture {s : Cfg P} (hpost : (s.pc p).Post15) (hrp : r ≠ p)
    (hv : s.ticket p < v) : (U s (s.ticket p) p).card ≤ (U s v r).card := by
  classical
  have hpU : p ∈ U s v r := by
    rw [mem_U]
    refine ⟨hrp.symm, fun h => ?_⟩
    unfold Safe at h
    rcases hpc : s.pc p with _ | rem' | ⟨acc', rem'⟩ | rem' | ⟨pred, cap⟩ | ⟨pred, rem'⟩ |
      ⟨pred, rem', cap⟩ | rem' | _ | rem' <;> simp only [hpc, PC.Post15] at hpost h <;>
      (rcases h with h | ⟨h, -⟩ <;> omega)
  have hsub : (U s (s.ticket p) p).erase r ⊆ (U s v r).erase p := by
    intro q hq
    simp only [mem_erase, mem_U] at hq ⊢
    obtain ⟨hqr, hqp, hns⟩ := hq
    exact ⟨hqp, hqr, fun h => hns (safe_anti hv h)⟩
  have h1 := card_le_card hsub
  have h2 := card_erase_add_one hpU
  have h3 := pred_card_le_card_erase (s := U s (s.ticket p) p) (a := r)
  omega

lemma s4_step (hI : Inv k s) (ha : Admissible s p i) :
    ∀ p', ((stepAt fife k s p i).pc p').Qual →
      (U (stepAt fife k s p i) ((stepAt fife k s p i).ticket p') p').card < k := by
  intro p' hc
  by_cases hpp : p' = p
  · subst hpp
    by_cases h15 : ∃ acc rem, s.pc p' = .d15 acc rem
    · obtain ⟨acc, rem, hpc⟩ := h15
      simp only [stepAt_pc, core, hpc] at hc
      split_ifs at hc <;> simp [PC.Qual] at hc
    push Not at h15
    rw [stepAt_ticket, core_ticket_self_of_ne_d15 h15]
    refine lt_of_le_of_lt (card_U_step hI ha le_rfl) ?_
    have hs4 := hI.s4 p'
    rcases hpc : s.pc p' with _ | rem' | ⟨acc', rem'⟩ | rem' | ⟨pred, cap⟩ | ⟨pred, rem'⟩ |
      ⟨pred, rem', cap⟩ | rem' | _ | rem' <;>
      simp only [hpc, PC.Qual] at hs4 <;>
      simp only [stepAt_pc, core, hpc] at hc <;> (try split_ifs at hc) <;>
      (try cases fife) <;> simp [PC.Qual] at hc <;>
      (try exact hs4 trivial)
    -- leaving the loop at line 19
    all_goals
      rename_i hexit _
      by_cases hcap : cap = true
      · subst hcap
        obtain ⟨v, r, hrp, hv, -, hU⟩ := hI.s3 p' (by simp [hpc, PC.Captured])
        exact (card_U_le_of_capture (by simp [hpc, PC.Post15]) hrp hv).trans_lt hU
      · have hk : pred.card < k := by
          simp only [Bool.not_eq_true] at hcap
          simp only [hcap, and_true, not_le] at hexit
          exact hexit
        refine lt_of_le_of_lt (card_le_card ?_) hk
        intro q hq
        rw [mem_U] at hq
        by_contra hqn
        exact hq.2 (hI.s1 p' (by simp [hpc, PC.InLoop]) q hq.1 (by simpa [hpc, PC.pred] using hqn))
  · rw [stepAt_pc, core_pc_ne hpp] at hc
    rw [stepAt_ticket, core_ticket_ne hpp]
    exact (card_U_step hI ha le_rfl).trans_lt (hI.s4 p' hc)

lemma s5_step (hI : Inv k s) (ha : Admissible s p i) :
    ∀ r x, 0 < (stepAt fife k s p i).capture r x →
      (U (stepAt fife k s p i) ((stepAt fife k s p i).capture r x) r).card < k := by
  intro r x hx
  by_cases hrp : r = p
  · subst hrp
    by_cases hc : ∃ rem, s.pc r = .cap23 rem ∧ x ∈ rem ∧ i = x
    · obtain ⟨rem, hpc, hxr, rfl⟩ := hc
      have hval : (stepAt fife k s r i).capture r i = s.ticket r := by
        simp [core, hpc, hxr]
      have ht : (stepAt fife k s r i).ticket r = s.ticket r := by
        simp [core, hpc, hxr]
      rw [hval]
      exact (card_U_step hI ha le_rfl).trans_lt (hI.s4 r (by simp [hpc, PC.Qual]))
    · have hval : (stepAt fife k s r i).capture r x = s.capture r x := by
        by_cases hc' : ∃ rem, s.pc r = .cap23 rem
        · obtain ⟨rem, hpc⟩ := hc'
          simp only [stepAt_capture, core, hpc]
          split_ifs with hi
          · have : x ≠ i := fun h => hc ⟨rem, hpc, h ▸ hi, h.symm⟩
            simp [Function.update_of_ne this]
          · rfl
        · push Not at hc'
          rw [stepAt_capture, core_capture_self_of_ne_cap23 hc']
      rw [hval] at hx ⊢
      exact (card_U_step hI ha (hI.capLe r x)).trans_lt (hI.s5 r x hx)
  · rw [capture_step_of_ne hrp] at hx ⊢
    exact (card_U_step hI ha (hI.capLe r x)).trans_lt (hI.s5 r x hx)

theorem inv_step (hI : Inv k s) (ha : Admissible s p i) : Inv k (stepAt fife k s p i) where
  g1 := g1_step hI ha
  wantC := wantC_step hI ha
  capLe := capLe_step hI ha
  capLt := capLt_step hI ha
  predNot := predNot_step hI
  scanNot := scanNot_step hI
  s1 := s1_step hI ha
  s3 := s3_step hI ha
  s4 := s4_step hI ha
  s5 := s5_step hI ha

theorem inv_init : Inv k (Cfg.init : Cfg P) where
  g1 := by intro q acc rem h; simp [Cfg.init] at h
  wantC := by intro q p _; simp [WantSpec, Cfg.init]
  capLe := by intro r x; simp [Cfg.init]
  capLt := by intro p h; simp [Cfg.init, PC.PreCap] at h
  predNot := by intro p; simp [Cfg.init, PC.pred]
  scanNot := by intro p pred rem h; simp [Cfg.init] at h
  s1 := by intro p h; simp [Cfg.init, PC.InLoop] at h
  s3 := by intro p h; simp [Cfg.init, PC.Captured] at h
  s4 := by intro p h; simp [Cfg.init, PC.Qual] at h
  s5 := by intro r x h; simp [Cfg.init] at h

theorem Reachable.inv {s : Cfg P} (h : Reachable fife k s) : Inv k s := by
  induction h with
  | init => exact inv_init
  | step _ ha ih => exact inv_step ih ha

theorem Run.inv (r : Run fife k P) (t : ℕ) : Inv k (r.s t) := by
  induction t with
  | zero => rw [r.init]; exact inv_init
  | succ t ih => rw [r.step t]; exact inv_step ih (r.adm t)

end Podc.KBakery
