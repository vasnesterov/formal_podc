import Papers.PODC2019.RMESubLogBoth.InvRepairLemmas

/-!
# The scan (lines 31–38) preserves the repairer's invariant
-/

namespace Podc.RMESubLogBoth

variable {k : ℕ}

open Relation

section
variable {c : Cfg k} {own : ℕ → ℕ}

/-- Line 31: the invariant of the scan holds with `EA` = the allocated nodes not at line 13. -/
lemma scanInv_init (hG : Glob c own) (hL : ∀ j, LI c own j) {q : Fin k} {x : ℕ}
    (hn : c.node q = some x) (hpc : c.pc q = .l31 x) :
    ScanInv c own q x c.tail ∅ ∅ 0 {a | a < c.nxt ∧ ∀ j, c.pc j ≠ .l13 a} := by
  have l13facts : ∀ j a, c.pc j = .l13 a → c.node j = some a ∧ c.pred a = .nil ∧
      (∀ w, ¬ c.Bh w a) ∧ c.tail ≠ a := by
    intro j a hj
    have := hL j; unfold LI at this; rw [hj] at this
    exact ⟨this.1, this.2.1, this.2.2.2.2.1, this.2.2.2.2.2⟩
  refine
    { tlEA := ⟨hG.tailLt, fun j hj => (l13facts j _ hj).2.2.2 rfl⟩
      xEA := ⟨(hG.nodeLt q x hn).2, fun j hj => by
        have := hG.node_inj hn (l13facts j x hj).1; subst this; rw [hpc] at hj; cases hj⟩
      EAlt := fun a ha => ha.1
      tail := .inl rfl
      bhLate := by
        intro a b hab hna
        exfalso; apply hna
        refine ⟨(hG.pos_of_bh hab).2, fun j hj => ?_⟩
        obtain ⟨hn', hp', -, -⟩ := l13facts j a hj
        obtain ⟨j', hj', hv⟩ := hab
        have := hG.node_inj hn' hj'; subst this
        rw [Cfg.vp_of_ovr_none (by simp [hj, PC.ovr]) hn', hp'] at hv; cases hv
      bhEarly := fun a b hab _ => ⟨hG.bhLt a b hab, fun j hj => (l13facts j b hj).2.2.1 a hab⟩
      lateIO := by
        intro a ha h
        exfalso; apply ha
        refine ⟨?_, fun j hj => ?_⟩
        · by_contra hlt
          have := (hG.fresh a (not_lt.mp hlt)).1
          rcases h with h | h <;> rw [h] at this <;> cases this
        · have := (l13facts j a hj).2.1
          rcases h with h | h <;> rw [h] at this <;> cases this
      l13Late := fun j a hj ha => ha.2 j hj
      Vlt := by simp
      Vl13 := by simp
      Esrc := by simp
      Etgt := by simp
      E1 := by simp
      E2 := by simp
      Etail := by simp
      El13 := by simp
      Ein := by simp
      Eown := by simp
      Eout := by simp
      EEA := by simp
      Eacyc := by
        intro u h
        rcases TransGen.head'_iff.mp h with ⟨b, hb, -⟩
        simp [EdgeR] at hb
      scanned := by intro j hj; omega }

lemma ScanInv.succ_none {q : Fin k} {x tl : ℕ} {V : Finset ℕ} {E : Finset (ℕ × ℕ)} {i : ℕ}
    {EA : Set ℕ} (h : ScanInv c own q x tl V E i EA) (hi : i < k)
    (hn : c.node ⟨i, hi⟩ = none) : ScanInv c own q x tl V E (i + 1) EA :=
  { h with
    Eown := fun u v e => Nat.lt_succ_of_lt (h.Eown u v e)
    scanned := by
      intro j hj a ha
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | hj
      · exact h.scanned j hj a ha
      · have : j = ⟨i, hi⟩ := Fin.ext hj
        rw [this, hn] at ha; cases ha }

lemma not_transGen_insert {E : Finset (ℕ × ℕ)} {a b : ℕ}
    (hac : ∀ u, ¬ TransGen (EdgeR E) u u) (hba : ¬ ReflTransGen (EdgeR E) b a) :
    ∀ u, ¬ TransGen (EdgeR (insert (a, b) E)) u u := by
  -- every path in the new graph either avoids the new edge or uses it
  have key : ∀ u v, TransGen (EdgeR (insert (a, b) E)) u v →
      TransGen (EdgeR E) u v ∨ (ReflTransGen (EdgeR E) u a ∧ ReflTransGen (EdgeR E) b v) := by
    intro u v h
    induction h with
    | single e =>
      rcases Finset.mem_insert.mp e with e | e
      · cases e; exact .inr ⟨.refl, .refl⟩
      · exact .inl (.single e)
    | tail _ e ih =>
      rcases Finset.mem_insert.mp e with e | e
      · cases e
        rcases ih with ih | ⟨h1, -⟩
        · exact .inr ⟨ih.to_reflTransGen, .refl⟩
        · exact .inr ⟨h1, .refl⟩
      · rcases ih with ih | ⟨h1, h2⟩
        · exact .inl (.tail ih e)
        · exact .inr ⟨h1, .tail h2 e⟩
  intro u h
  rcases key u u h with h1 | ⟨h1, h2⟩
  · exact hac u h1
  · exact hba (h2.trans h1)

/-- Lines 36–38 extend the scanned graph. -/
lemma ScanInv.add (hG : Glob c own) (hL : ∀ j, LI c own j) {q : Fin k} {x tl : ℕ}
    {V : Finset ℕ} {E : Finset (ℕ × ℕ)} {i a : ℕ} {EA : Set ℕ}
    (h : ScanInv c own q x tl V E i EA) (hi : i < k) (hown : own a = i) (ha : a < c.nxt)
    (hnn : c.nn a = true) (hb : ∀ b, (h : i < k) → c.node ⟨i, h⟩ = some b → b ∈ EA → b = a)
    (hq : c.pc q = .l36 x tl V E i a) :
    ScanInv c own q x tl (addV V a (c.pred a)) (addE E a (c.pred a)) (i + 1) EA := by
  have ha13 : ∀ j, c.pc j ≠ .l13 a := by
    intro j hj
    have := hL j; unfold LI at this; rw [hj] at this
    rw [this.2.2.1] at hnn; cases hnn
  -- the new vertex is not the source of an old edge
  have hnoout : ∀ v, (a, v) ∉ E := fun v e => by
    have := h.Eown a v e; omega
  -- vertices of `V` stay, edges of `E` stay
  have hVsub : V ⊆ addV V a (c.pred a) := by
    intro v hv; unfold addV; split <;> simp [hv]
  have hEsub : E ⊆ addE E a (c.pred a) := by
    intro e he; unfold addE; split <;> simp [he]
  have haV : a ∈ addV V a (c.pred a) := by unfold addV; split <;> simp
  -- characterization of the new edges
  have hnewE : ∀ u v, (u, v) ∈ addE E a (c.pred a) →
      (u, v) ∈ E ∨ (u = a ∧ c.pred a = .node v) := by
    intro u v e
    unfold addE at e
    split at e
    · rename_i d hd
      rcases Finset.mem_insert.mp e with e | e
      · cases e; exact .inr ⟨rfl, hd⟩
      · exact .inl e
    · exact .inl e
  have hnewV : ∀ v, v ∈ addV V a (c.pred a) → v ∈ V ∨ v = a ∨ c.pred a = .node v := by
    intro v hv
    unfold addV at hv
    split at hv
    · rename_i d hd
      simp at hv; rcases hv with rfl | rfl | hv
      · exact .inr (.inl rfl)
      · exact .inr (.inr hd)
      · exact .inl hv
    · simp at hv; rcases hv with rfl | hv
      · exact .inr (.inl rfl)
      · exact .inl hv
  have hbh : ∀ d, c.pred a = .node d → c.Bh a d := fun d hd => bh_of_pred hG hL hd
  refine
    { tlEA := h.tlEA, xEA := h.xEA, EAlt := h.EAlt, tail := h.tail, bhLate := h.bhLate,
      bhEarly := h.bhEarly, lateIO := h.lateIO, l13Late := h.l13Late
      Vlt := by
        intro v hv
        rcases hnewV v hv with hv | rfl | hd
        · exact h.Vlt v hv
        · exact ha
        · exact hG.bhLt _ _ (hbh _ hd)
      Vl13 := by
        intro v hv j
        rcases hnewV v hv with hv | rfl | hd
        · exact h.Vl13 v hv j
        · exact ha13 j
        · intro hj
          have := hL j; unfold LI at this; rw [hj] at this
          exact this.2.2.2.2.1 a (hbh _ hd)
      Esrc := by
        intro u v e
        rcases hnewE u v e with e | ⟨rfl, -⟩
        · exact hVsub (h.Esrc u v e)
        · exact haV
      Etgt := by
        intro u v e
        rcases hnewE u v e with e | ⟨rfl, hd⟩
        · exact hVsub (h.Etgt u v e)
        · unfold addV; rw [hd]; simp
      E1 := by
        intro u v e
        rcases hnewE u v e with e | ⟨rfl, hd⟩
        · exact h.E1 u v e
        · exact .inl hd
      E2 := by
        intro u v w e hw
        rcases hnewE u v e with e | ⟨rfl, hd⟩
        · exact h.E2 u v w e hw
        · exact hG.bhInj w u v hw (hbh _ hd)
      Etail := by
        intro u v e
        rcases hnewE u v e with e | ⟨rfl, hd⟩
        · exact h.Etail u v e
        · intro ht; exact hG.noBhTail u (ht ▸ hbh _ hd)
      El13 := by
        intro u v j e
        rcases hnewE u v e with e | ⟨rfl, hd⟩
        · exact h.El13 u v j e
        · intro hj
          have := hL j; unfold LI at this; rw [hj] at this
          exact this.2.2.2.2.1 u (hbh _ hd)
      Ein := by
        intro u u' v e e'
        rcases hnewE u v e with e1 | ⟨hu, hd⟩ <;> rcases hnewE u' v e' with e2 | ⟨hu', hd'⟩
        · exact h.Ein u u' v e1 e2
        · subst hu'; exact (h.E2 u v _ e1 (hbh _ hd')).symm
        · subst hu; exact h.E2 u' v _ e2 (hbh _ hd)
        · rw [hu, hu']
      Eown := by
        intro u v e
        rcases hnewE u v e with e | ⟨rfl, -⟩
        · exact Nat.lt_succ_of_lt (h.Eown u v e)
        · omega
      Eout := by
        intro u v v' e e'
        rcases hnewE u v e with e1 | ⟨hu, hd⟩ <;> rcases hnewE u v' e' with e2 | ⟨hu', hd'⟩
        · exact h.Eout u v v' e1 e2
        · subst hu'; exact absurd e1 (hnoout v)
        · subst hu; exact absurd e2 (hnoout v')
        · rw [hd] at hd'; cases hd'; rfl
      EEA := by
        intro u v e hu
        rcases hnewE u v e with e | ⟨rfl, hd⟩
        · exact h.EEA u v e hu
        · exact h.bhEarly _ _ (hbh _ hd) hu
      Eacyc := by
        rcases (show (∃ d, c.pred a = .node d) ∨ addE E a (c.pred a) = E by
            cases c.pred a <;> simp [addE]) with ⟨d, hd⟩ | hE'
        · have hE' : addE E a (c.pred a) = insert (a, d) E := by simp [addE, hd]
          rw [hE']
          refine not_transGen_insert h.Eacyc ?_
          intro hr
          -- a `Pred`-cycle through `a`
          have hPL := (h.rtg_E_PL hr (by rw [hd]; simp)).1
          have hcyc : TransGen c.Bh a a := TransGen.head' (hbh _ hd) (rtg_PL_bh hG hL hPL)
          exact wf_not_transGen hG.wf a hcyc
        · rw [hE']; exact h.Eacyc
      scanned := by
        intro j hj b hjb
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | hj
        · rcases h.scanned j hj b hjb with h1 | ⟨h1, h2, h3⟩
          · exact .inl h1
          · exact .inr ⟨hVsub h1, h2, fun v hv => hEsub (h3 v hv)⟩
        · by_cases hbEA : b ∈ EA
          · right
            have hji : j = ⟨i, hi⟩ := Fin.ext hj
            subst hji
            have := hb b hi hjb hbEA; subst this
            refine ⟨haV, hnn, fun v hv => ?_⟩
            rcases vp_cases hL _ hjb with h1 | ⟨m, h2, -, -⟩ | ⟨m, h2, -, -⟩
            · rw [h1] at hv; unfold addE; rw [hv]; simp
            · have := hL ⟨i, hi⟩; unfold LI at this; rw [h2] at this
              rw [this.2.2.1] at hnn; cases hnn
            · -- a port at line 49 is the repairer, which is at line 36
              have h49 := hG.holder _ (by rw [h2]; trivial)
              have h36 := hG.holder q (by rw [hq]; trivial)
              rw [h36] at h49; cases h49
              rw [hq] at h2; cases h2
          · exact .inl hbEA }

end

end Podc.RMESubLogBoth
