import Papers.PODC2011.AtMostOnceEffectiveness.Safety

/-!
# Lemma 4.2: no process terminates while fewer than `n − (β + m − 2)` jobs are done

Additional invariants (`Inv2`): `DONE_p` only contains recorded jobs, `|TRY_p| ≤ m − 1`, and a
terminated process saw `|FREE_p \ TRY_p| < β`. Hence a terminated process implies
`n − Do − (m − 1) < β` (`do_ge_of_halted`), which is Lemma 4.2.
-/

set_option linter.unusedSectionVars false

namespace Podc.AtMostOnceEffectiveness

open Function

variable {m n β : ℕ} {C C' : Config m Reg ℕ LState} {p q : Fin m}

/-- All jobs recorded in the `done` matrix. -/
def recorded (C : Config m Reg ℕ LState) : Finset ℕ :=
  Finset.univ.biUnion (fun q : Fin m => (line C q).toFinset)

/-- The secondary invariant. -/
structure Inv2 (m n β : ℕ) (C : Config m Reg ℕ LState) : Prop where
  doneRec : ∀ p, (C.loc p).doneS ⊆ recorded C
  trySet : ∀ p, (C.loc p).status = .setNext → (C.loc p).tryS = ∅
  tryCard : ∀ p : Fin m, (C.loc p).status = .gatherTry →
    (C.loc p).tryS.card + (if p.val < (C.loc p).q then 1 else 0) ≤ (C.loc p).q
  tryCard' : ∀ p : Fin m, (C.loc p).status ≠ .gatherTry → (C.loc p).tryS.card ≤ m - 1
  fin : ∀ p, (C.loc p).status = .finished → (free n (C.loc p) \ (C.loc p).tryS).card < β

lemma recorded_mono (hI : Inv m n C) (hs : KStep m n β C p C') : recorded C ⊆ recorded C' := by
  intro x hx
  simp only [recorded, Finset.mem_biUnion, Finset.mem_univ, true_and, List.mem_toFinset] at hx ⊢
  obtain ⟨r, hr⟩ := hx
  refine ⟨r, ?_⟩
  by_cases hrp : r = p
  · subst hrp; rw [hs.line_self (hI.posOwn r)]; exact List.mem_append_left _ hr
  · rw [hs.line_ne hrp]; exact hr

lemma tryS_card_le (hI2 : Inv2 m n β C) (hI : Inv m n C) (p : Fin m) :
    (C.loc p).tryS.card ≤ m - 1 := by
  by_cases h : (C.loc p).status = .gatherTry
  · have h1 := hI2.tryCard p h
    have h2 := hI.qlt p (Or.inl h)
    have := p.isLt
    split_ifs at h1 <;> omega
  · exact hI2.tryCard' p h

theorem Inv2.step (hI : Inv m n C) (hI2 : Inv2 m n β C) (hs : KStep m n β C p C') :
    Inv2 m n β C' where
  doneRec := by
    intro r
    have hmono := recorded_mono hI hs
    by_cases hrp : r = p
    · subst hrp
      have hline := hs.line_self (hI.posOwn r)
      cases hs with
      | doneRead h hq hp hv =>
        simp only [update_self]
        refine Finset.insert_subset (hmono ?_) ((hI2.doneRec r).trans hmono)
        have hqm := hI.qlt r (Or.inr h)
        set a : Fin m := ⟨(C.loc r).q, hqm⟩
        have hlt : (C.loc r).pos a < (C.loc a).pos a := by
          by_contra hc; push Not at hc
          have := hI.lineZero a _ hc; simp [a] at this hv; omega
        have hpos : 1 ≤ (C.loc r).pos a :=
          (hI.reader r a (fun e => hq (by have := congrArg Fin.val e; simpa [a] using this))).1
        have hlen := hI.line_length (n := n) a
        simp only [recorded, Finset.mem_biUnion, Finset.mem_univ, true_and, List.mem_toFinset]
        refine ⟨a, ?_⟩
        have hmem := List.getElem_mem (l := line C a) (n := (C.loc r).pos a - 1) (by omega)
        rwa [hI.line_getElem a _ (by omega), show (C.loc r).pos ↑a - 1 + 1 = (C.loc r).pos a by
          omega] at hmem
      | writeDone h =>
        simp only [update_self]
        refine Finset.insert_subset ?_ ((hI2.doneRec r).trans hmono)
        simp only [recorded, Finset.mem_biUnion, Finset.mem_univ, true_and, List.mem_toFinset]
        exact ⟨r, by rw [hline]; simp [pend, h]⟩
      | _ => simpa using (hI2.doneRec r).trans hmono
    · rw [hs.loc_ne hrp]; exact (hI2.doneRec r).trans hmono
  trySet := by
    intro r hr
    by_cases hrp : r = p
    · subst hrp
      cases hs with
      | tryRead h hq => simp [adv_status] at hr; split_ifs at hr <;> simp_all
      | trySkip h hq => simp [adv_status] at hr; split_ifs at hr <;> simp_all
      | doneAdv h hq => simp [adv_status] at hr; split_ifs at hr <;> simp_all
      | _ => simp_all
    · rw [hs.loc_ne hrp] at hr ⊢; exact hI2.trySet r hr
  tryCard := by
    intro r hr
    by_cases hrp : r = p
    · subst hrp
      cases hs with
      | setNext h => simp [hI.qSet r h, hI2.trySet r h]
      | tryRead h hq =>
        simp only [update_self, adv_status, adv_q, adv_tryS] at hr ⊢
        have h1 := hI2.tryCard r h
        have hc : (addTry (C.mem (.next (C.loc r).q)) (C.loc r).tryS).card ≤
            (C.loc r).tryS.card + 1 := by
          unfold addTry; split_ifs
          · exact Finset.card_insert_le _ _
          · omega
        have hrq : r.val ≠ (C.loc r).q := fun e => hq e.symm
        split_ifs at hr ⊢ with h2 h3 h3 <;> simp_all <;> split_ifs at h1 <;> omega
      | trySkip h hq =>
        simp only [update_self, adv_status, adv_q, adv_tryS] at hr ⊢
        have h1 := hI2.tryCard r h
        split_ifs at hr ⊢ with h2 h3 h3 <;> simp_all <;> split_ifs at h1 <;> omega
      | doneAdv h hq => simp [adv_status] at hr; split_ifs at hr <;> simp_all
      | _ => simp_all
    · rw [hs.loc_ne hrp] at hr ⊢; exact hI2.tryCard r hr
  tryCard' := by
    intro r hr
    by_cases hrp : r = p
    · subst hrp
      have h0 := tryS_card_le hI2 hI r
      cases hs with
      | compNext h hb => simp
      | tryRead h hq =>
        simp only [update_self, adv_status, adv_q, adv_tryS] at hr ⊢
        have h1 := hI2.tryCard r h
        have hqm := hI.qlt r (Or.inl h)
        have := r.isLt
        have hc : (addTry (C.mem (.next (C.loc r).q)) (C.loc r).tryS).card ≤
            (C.loc r).tryS.card + 1 := by
          unfold addTry; split_ifs
          · exact Finset.card_insert_le _ _
          · omega
        split_ifs at hr with h2
        · simp_all
        · split_ifs at h1 <;> omega
      | trySkip h hq =>
        simp only [update_self, adv_status, adv_q, adv_tryS] at hr ⊢
        have h1 := hI2.tryCard r h
        have hqm := hI.qlt r (Or.inl h)
        split_ifs at hr with h2
        · simp_all
        · split_ifs at h1 <;> omega
      | _ => simp_all
    · rw [hs.loc_ne hrp] at hr ⊢; exact hI2.tryCard' r hr
  fin := by
    intro r hr
    by_cases hrp : r = p
    · subst hrp
      cases hs with
      | finish h hb => simpa [free] using hb
      | tryRead h hq => simp [adv_status] at hr; split_ifs at hr <;> simp_all
      | trySkip h hq => simp [adv_status] at hr; split_ifs at hr <;> simp_all
      | doneAdv h hq => simp [adv_status] at hr; split_ifs at hr <;> simp_all
      | _ => simp_all
    · rw [hs.loc_ne hrp] at hr ⊢; exact hI2.fin r hr

theorem Inv2.init : Inv2 m n β (kk m n β).init where
  doneRec := by intro p; simp [Alg.init, kk, LState.init]
  trySet := by intro p h; simp [Alg.init, kk, LState.init] at h
  tryCard := by intro p h; simp [Alg.init, kk, LState.init] at h
  tryCard' := by intro p _; simp [Alg.init, kk, LState.init]
  fin := by intro p h; simp [Alg.init, kk, LState.init] at h

/-- Both invariants hold in every reachable configuration (for `β ≥ 1`). -/
theorem inv_of_reachable (hβ : 1 ≤ β) {C : Config m Reg ℕ LState}
    (h : (kk m n β).Reachable C) : Inv m n C ∧ Inv2 m n β C := by
  induction h with
  | init => exact ⟨Inv.init, Inv2.init⟩
  | step _ hs ih => exact ⟨ih.1.step hβ hs, ih.2.step ih.1 (step_inv hs)⟩

lemma halted_iff : (kk m n β).Halted C p ↔ (C.loc p).status = .finished := by
  unfold Alg.Halted
  simp only [kk, kkNext]
  cases h : (C.loc p).status <;> simp [h] <;> split_ifs <;> simp

lemma recorded_subset_jobs (hI : Inv m n C) : recorded C ⊆ Alg.jobs n C := by
  intro x hx
  simp only [recorded, Finset.mem_biUnion, Finset.mem_univ, true_and, List.mem_toFinset] at hx
  obtain ⟨r, hr⟩ := hx
  simp only [Alg.jobs, Finset.mem_filter]
  refine ⟨hI.lineJ r x hr, ?_⟩
  have : x ∈ plog C r := by rw [hI.plogEq r]; exact List.mem_append_left _ hr
  unfold plog at this
  exact (List.map_subset _ (List.filter_subset' _)) this

lemma card_free_ge (hI : Inv m n C) (hI2 : Inv2 m n β C) (p : Fin m) :
    n - Alg.Do n C ≤ (free n (C.loc p)).card := by
  have h1 : Finset.Icc 1 n \ Alg.jobs n C ⊆ free n (C.loc p) := by
    apply Finset.sdiff_subset_sdiff (le_refl _)
    exact (hI2.doneRec p).trans (recorded_subset_jobs hI)
  have h2 := Finset.card_le_card h1
  have hsub : Alg.jobs n C ⊆ Finset.Icc 1 n := Finset.filter_subset _ _
  rw [Finset.card_sdiff_of_subset hsub] at h2
  simpa [Alg.Do] using h2

/-- A terminated process implies that at least `n − (β + m − 2)` jobs were performed: in the
enabling state of its last `compNext`, `|FREE_p \ TRY_p| < β`, `|FREE_p| ≥ n − Do` and
`|TRY_p| ≤ m − 1`. -/
theorem do_ge_of_halted (hI : Inv m n C) (hI2 : Inv2 m n β C) (h : (kk m n β).Halted C p) :
    n < Alg.Do n C + β + (m - 1) := by
  rw [halted_iff] at h
  have h1 := hI2.fin p h
  have h2 := card_free_ge hI hI2 p
  have h3 := tryS_card_le hI2 hI p
  have h4 : (free n (C.loc p)).card ≤ (free n (C.loc p) \ (C.loc p).tryS).card +
      (C.loc p).tryS.card := by
    have := Finset.card_sdiff_add_card_inter (free n (C.loc p)) (C.loc p).tryS
    have := Finset.card_le_card (Finset.inter_subset_right (s₁ := free n (C.loc p))
      (s₂ := (C.loc p).tryS))
    omega
  omega

/-- **Lemma 4.2** of [Kentros–Kiayias]: if fewer than `n − (β + m − 2)` jobs have been performed
(`Do(α) ≤ n − (β + m − 1)`), no process has terminated. -/
theorem lemma_4_2 (hβ : 1 ≤ β) {C : Config m Reg ℕ LState} (hC : (kk m n β).Reachable C)
    (hDo : Alg.Do n C + (β + m - 1) ≤ n) (p : Fin m) : ¬ (kk m n β).Halted C p := by
  intro h
  obtain ⟨hI, hI2⟩ := inv_of_reachable hβ hC
  have := do_ge_of_halted hI hI2 h
  have hm : 0 < m := p.pos
  omega

/-- **Lemma 4.2**, the paper's form: a finite execution with at most `f ≤ m − 1` crashed processes
(`F`) and `Do(α) ≤ n − (β + m − 1)` can be extended by a step of a non-crashed process. -/
theorem lemma_4_2_extend (hβ : 1 ≤ β) {C : Config m Reg ℕ LState} (hC : (kk m n β).Reachable C)
    (hDo : Alg.Do n C + (β + m - 1) ≤ n) (F : Finset (Fin m)) (hF : F.card < m) :
    ∃ p ∉ F, ∃ C', (kk m n β).step C p = some C' := by
  obtain ⟨p, hp⟩ : ∃ p, p ∉ F := by
    by_contra h; push Not at h
    have : F = Finset.univ := Finset.eq_univ_iff_forall.mpr h
    rw [this, Finset.card_univ, Fintype.card_fin] at hF; omega
  exact ⟨p, hp, Alg.step_isSome_of_not_halted (lemma_4_2 hβ hC hDo p)⟩

end Podc.AtMostOnceEffectiveness
