import Papers.PODC2016.RWLockRMRTradeoff.Construction
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# The execution `E₂` of the proof of Theorem 5

From `C₁` (all readers in the CS, writers in the remainder section), all readers execute their exit
sections. The schedule is built in rounds (the paper's `σ_j = σ'_j σ''_j`):
* *drain*: while some reader in its exit section is poised on a non-expanding step (or on its
  response), let it take that step;
* *round*: when every reader still in its exit section is poised on an expanding step, schedule
  these steps in the order given by Lemma 2.
Invariant after `j` rounds: all awareness sets have at most `3^j` elements and every reader still in
its exit section has performed at least `j` expanding steps. Bounded Exit makes the construction
terminate.
-/

namespace Podc.RWLockRMRTradeoff

open Cslib.SharedMemory

variable {n m : ℕ} {ι V L : Type} [DecidableEq ι] [DecidableEq V] {v₀ : V}
variable {I : RWAlg n m ι V v₀ L} {cm : CacheModel (Proc n m) ι}

lemma xcount_eq_zero {A : ObjSpec} {P : Type} [DecidableEq P] {J : Impl A (Regs ι V v₀) P L}
    {cm' : CacheModel P ι} (f : Ext J cm' → Label P A → Prop) (X : Ext J cm')
    (β : List (Label P A)) (h : ∀ ℓ ∈ β, ∀ Y, ¬ f Y ℓ) : xcount f X β = 0 := by
  induction β generalizing X with
  | nil => rfl
  | cons ℓ β ih =>
    simp only [xcount]
    split
    · rfl
    · rename_i Y _
      rw [if_neg (h ℓ List.mem_cons_self X), ih Y (fun ℓ' h' => h ℓ' (List.mem_cons_of_mem _ h'))]

lemma not_expBy_of_not_tau {A : ObjSpec} {P : Type} [DecidableEq P] {J : Impl A (Regs ι V v₀) P L}
    {cm' : CacheModel P ι} {ℓ : Label P A} (h : ∀ q, ℓ ≠ .tau q) (p : P) (Y : Ext J cm') :
    ¬ ExpBy p Y ℓ := fun ⟨_, he⟩ => by
  obtain ⟨q, -, -, -, rfl, -⟩ := expanding_iff.1 he; exact h q rfl

/-- The readers invoke `unlock` one after the other. -/
lemma xrun_invs (s : List (Fin n)) (hnd : s.Nodup) (X : Ext I cm)
    (hall : ∀ p o, I.allowed p o) (hidle : ∀ i ∈ s, X.cfg.pend (.inl i) = none) :
    ∃ Y, xrun X (s.map fun i => .inv (.inl i) .unlock) = some Y ∧ Y.kn = X.kn ∧
      (∀ i ∈ s, Y.cfg.pend (.inl i) = some .unlock) ∧
      (∀ q, (∀ i ∈ s, q ≠ .inl i) → Y.cfg.pend q = X.cfg.pend q) := by
  induction s generalizing X with
  | nil => exact ⟨X, rfl, rfl, by simp, fun _ _ => rfl⟩
  | cons i s ih =>
    obtain ⟨his, hnd'⟩ := List.nodup_cons.1 hnd
    have hs := Impl.step_inv_eq_some (I := I) (o := MutexOp.unlock)
      (hidle i List.mem_cons_self) (hall _ _)
    set X₁ : Ext I cm := ⟨_, kstep I X.cfg X.kn (.inv (.inl i) .unlock),
      cacheStep I cm X.cfg X.cache (.inv (.inl i) .unlock)⟩
    have hxs : xstep X (.inv (.inl i) .unlock) = some X₁ := xstep_eq_some.2 ⟨hs, rfl, rfl⟩
    obtain ⟨Y, hY, hk, h1, h2⟩ := ih hnd' X₁ (fun i' hi' => by
      have : i' ≠ i := fun h => his (h ▸ hi')
      simp [X₁, Function.update_of_ne (show (Sum.inl i' : Proc n m) ≠ .inl i by simpa),
        hidle i' (List.mem_cons_of_mem _ hi')])
    refine ⟨Y, by rw [List.map_cons, xrun_cons, hxs]; exact hY, by rw [hk]; rfl,
      fun i' hi' => ?_, fun q hq => ?_⟩
    · rcases List.mem_cons.1 hi' with rfl | hi'
      · rw [h2 _ (fun i'' hi'' h => his (by cases h; exact hi''))]; simp [X₁]
      · exact h1 i' hi'
    · rw [h2 q (fun i' hi' => hq i' (List.mem_cons_of_mem _ hi'))]
      simp [X₁, Function.update_of_ne (hq i List.mem_cons_self)]

/-- Regions after the invocations of `unlock`. -/
lemma regFold_invs (s : List (Fin n)) (hnd : s.Nodup) (r : Option Region) (q : Proc n m) :
    regFold r (s.map fun i => (.inv (.inl i) .unlock : Label (Proc n m) mutexObj)) q =
      if ∃ i ∈ s, q = .inl i then r.bind (fun r => r.next (.inv q .unlock)) else r := by
  induction s generalizing r with
  | nil => simp
  | cons i s ih =>
    obtain ⟨his, hnd'⟩ := List.nodup_cons.1 hnd
    rw [List.map_cons, regFold_cons, ih hnd']
    by_cases hq : q = .inl i
    · subst hq
      have : ¬ ∃ i' ∈ s, (Sum.inl i : Proc n m) = .inl i' := by
        rintro ⟨i', hi', h⟩; cases h; exact his hi'
      simp only [Label.proc, ite_true, this, if_false]
      simp
    · simp only [Label.proc, Ne.symm hq, if_false]
      congr 1
      apply propext
      constructor
      · rintro ⟨i', hi', rfl⟩; exact ⟨i', List.mem_cons_of_mem _ hi', rfl⟩
      · rintro ⟨i', hi', rfl⟩
        rcases List.mem_cons.1 hi' with rfl | hi'
        · exact absurd rfl hq
        · exact ⟨i', hi', rfl⟩

/-- The invariant of the construction of `E₂` after the labels `γ` (run from `X₀`, the
configuration after all readers invoked `unlock`) and `j` rounds. -/
structure E2Inv (X₀ : Ext I cm) (γ : List (Label (Proc n m) mutexObj)) (Z : Ext I cm) (j : ℕ) :
    Prop where
  run : xrun X₀ γ = some Z
  lbl : ∀ ℓ ∈ γ, ℓ.proc.isLeft ∧ ∀ q o, ℓ ≠ .inv q o
  reg : ∀ i, regFold (some .exiting) γ (.inl i) =
    some (if Z.cfg.pend (.inl i) = none then .rem else .exiting)
  wr : ∀ j', Z.cfg.pend (.inr j') = none
  aw : ∀ q, (Z.kn.aw q).card ≤ 3 ^ j
  exp : ∀ i, Z.cfg.pend (.inl i) ≠ none → j ≤ xcount (ExpBy (.inl i)) X₀ γ
  some : j = 0 ∨ ∃ i, j ≤ xcount (ExpBy (.inl i)) X₀ γ

/-- The termination measure: remaining exit steps of readers still in their exit section. -/
noncomputable def e2Measure (Bm : ℕ) (γ : List (Label (Proc n m) mutexObj)) (Z : Ext I cm) : ℕ :=
  ∑ i : Fin n, if Z.cfg.pend (.inl i) = none then 0 else Bm + 1 - tauCount (.inl i) γ

lemma nextLabel_cases (C : Config mutexObj (Regs ι V v₀) (Proc n m) L) (p : Proc n m) :
    (∃ i o k, I.act p (C.loc p) = .access i o k ∧ I.nextLabel C p = .tau p) ∨
      (∃ r l, I.act p (C.loc p) = .ret r l ∧ I.nextLabel C p = .ret p r) := by
  unfold Impl.nextLabel
  split
  · rename_i i o k h; exact Or.inl ⟨i, o, k, h, rfl⟩
  · rename_i r l h; exact Or.inr ⟨r, l, h, rfl⟩

/-- **The construction of `E₂`.** -/
theorem e2_construct (X₀ : Ext I cm) (hX₀ : X₀.kn = Know.init) (Bm : ℕ)
    (hBm : ∀ γ (Z : Ext I cm), xrun X₀ γ = some Z → (∀ ℓ ∈ γ, ∀ q o, ℓ ≠ .inv q o) →
      ∀ i, ¬ Returns (.inl i) γ → tauCount (.inl i) γ ≤ Bm) :
    ∀ N γ Z j, E2Inv X₀ γ Z j → e2Measure Bm γ Z ≤ N →
      ∃ γ' Z' r, E2Inv X₀ (γ ++ γ') Z' r ∧ ∀ i, Z'.cfg.pend (.inl i) = none := by
  classical
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro γ Z j hI hμ
  have hK : KInv Z.kn := xrun_kinv hI.run (hX₀ ▸ KInv.init)
  -- pending readers have taken at most `Bm` steps
  have htc : ∀ i, Z.cfg.pend (.inl i) ≠ none → tauCount (.inl i) γ ≤ Bm := by
    intro i hi
    apply hBm γ Z hI.run (fun ℓ h => (hI.lbl ℓ h).2) i
    apply not_returns_of_exiting γ _ (fun ℓ h => (hI.lbl ℓ h).2)
    rw [hI.reg i, if_neg hi]
  by_cases hdone : ∀ i, Z.cfg.pend (.inl i) = none
  · exact ⟨[], Z, j, by simpa using hI, hdone⟩
  push Not at hdone
  by_cases hdrain : ∃ i, Z.cfg.pend (.inl i) ≠ none ∧ ¬ Expanding Z (I.nextLabel Z.cfg (.inl i))
  · -- drain step
    obtain ⟨i, hi, hne⟩ := hdrain
    set ℓ := I.nextLabel Z.cfg (.inl i) with hℓ
    obtain ⟨C', hC'⟩ := Option.isSome_iff_exists.1 (I.step_nextLabel_isSome Z.cfg (.inl i) hi)
    set Z' : Ext I cm := ⟨C', kstep I Z.cfg Z.kn ℓ, cacheStep I cm Z.cfg Z.cache ℓ⟩
    have hxs : xstep Z ℓ = some Z' := xstep_eq_some.2 ⟨hC', rfl, rfl⟩
    have hrun' : xrun X₀ (γ ++ [ℓ]) = some Z' := by
      rw [xrun_append_of_eq hI.run, xrun_cons, hxs]; rfl
    have hproc : ℓ.proc = .inl i := I.nextLabel_proc _ _
    have hoth : ∀ q, q ≠ .inl i → C'.pend q = Z.cfg.pend q := fun q hq =>
      (Impl.step_other hC' (by rw [hproc]; exact Ne.symm hq)).2
    have hcnt : ∀ p, xcount (ExpBy p) X₀ (γ ++ [ℓ]) ≥ xcount (ExpBy p) X₀ γ := fun p => by
      rw [xcount_append _ hI.run]; omega
    -- pending readers after the step were pending before
    have hpend' : ∀ i', C'.pend (.inl i') ≠ none → Z.cfg.pend (.inl i') ≠ none := by
      intro i' h'
      by_cases hii : i' = i
      · subst hii; exact hi
      · rwa [← hoth _ (by simpa using hii)]
    rcases nextLabel_cases (I := I) Z.cfg (.inl i) with ⟨i₀, o, k, hact, htau⟩ | ⟨r, l, hact, hret⟩
    · -- an internal step
      rw [← hℓ] at htau
      have hC'' : I.step Z.cfg (.tau (.inl i)) = some C' := by rw [← htau, hℓ]; exact hC'
      have hpi : C'.pend = Z.cfg.pend := (Impl.step_tau hC'').2.1
      have hI' : E2Inv X₀ (γ ++ [ℓ]) Z' j := by
        refine ⟨hrun', fun ℓ' h' => ?_, fun i' => ?_, fun j' => ?_, fun q => ?_,
          fun i' h' => ?_, ?_⟩
        · rcases List.mem_append.1 h' with h' | h'
          · exact hI.lbl ℓ' h'
          · simp only [List.mem_singleton] at h'; subst h'; rw [htau]
            exact ⟨rfl, fun q o h => by cases h⟩
        · rw [regFold_append, hI.reg i', htau]
          simp only [Z', hpi]
          split_ifs <;> simp [regFold_cons, Label.proc, Region.next]
        · simp only [Z', hpi]; exact hI.wr j'
        · have : ¬ (Z.kn.aw q).card < ((kstep I Z.cfg Z.kn ℓ).aw q).card := fun h => hne ⟨q, h⟩
          simp only [Z']; have := hI.aw q; omega
        · exact (hI.exp i' (hpend' i' h')).trans (hcnt _)
        · exact hI.some.imp_right fun ⟨i', h'⟩ => ⟨i', h'.trans (hcnt _)⟩
      have hμ' : e2Measure Bm (γ ++ [ℓ]) Z' < e2Measure Bm γ Z := by
        unfold e2Measure
        apply Finset.sum_lt_sum
        · intro i' _
          simp only [Z', hpi, tauCount_append]
          split_ifs <;> omega
        · refine ⟨i, Finset.mem_univ _, ?_⟩
          have : tauCount (.inl i) [ℓ] = 1 := by rw [htau]; simp [tauCount, isTauOf]
          simp only [Z', hpi, tauCount_append, this, if_neg hi]
          have := htc i hi; omega
      obtain ⟨γ', Z'', r', h1, h2⟩ := ih _ (by omega) _ _ _ hI' le_rfl
      exact ⟨ℓ :: γ', Z'', r', by simpa using h1, h2⟩
    · -- the response
      rw [← hℓ] at hret
      have hC'' : I.step Z.cfg (.ret (.inl i) r) = some C' := by rw [← hret, hℓ]; exact hC'
      have hpi : C'.pend (.inl i) = none := by simp [(Impl.step_ret hC'').2.1]
      have hI' : E2Inv X₀ (γ ++ [ℓ]) Z' j := by
        refine ⟨hrun', fun ℓ' h' => ?_, fun i' => ?_, fun j' => ?_, fun q => ?_,
          fun i' h' => ?_, ?_⟩
        · rcases List.mem_append.1 h' with h' | h'
          · exact hI.lbl ℓ' h'
          · simp only [List.mem_singleton] at h'; subst h'; rw [hret]
            exact ⟨rfl, fun q o h => by cases h⟩
        · rw [regFold_append, hI.reg i', hret]
          by_cases hii : i' = i
          · subst hii
            simp only [Z', hpi, if_neg hi]
            simp [regFold_cons, Label.proc, Region.next]
          · have hq : (Sum.inl i' : Proc n m) ≠ .inl i := by simpa using hii
            simp only [Z', hoth _ hq]
            rw [regFold_cons, if_neg (by simpa [Label.proc] using Ne.symm hq)]; rfl
        · simp only [Z', hoth (.inr j') (by simp)]; exact hI.wr j'
        · have : ¬ (Z.kn.aw q).card < ((kstep I Z.cfg Z.kn ℓ).aw q).card := fun h => hne ⟨q, h⟩
          simp only [Z']; have := hI.aw q; omega
        · exact (hI.exp i' (hpend' i' h')).trans (hcnt _)
        · exact hI.some.imp_right fun ⟨i', h'⟩ => ⟨i', h'.trans (hcnt _)⟩
      have hμ' : e2Measure Bm (γ ++ [ℓ]) Z' < e2Measure Bm γ Z := by
        unfold e2Measure
        apply Finset.sum_lt_sum
        · intro i' _
          by_cases hii : i' = i
          · subst hii; simp [Z', hpi]
          · have hq : (Sum.inl i' : Proc n m) ≠ .inl i := by simpa using hii
            have h0 : tauCount (.inl i') [ℓ] = 0 := by rw [hret]; simp [tauCount, isTauOf]
            simp only [Z', hoth _ hq, tauCount_append, h0, add_zero, le_refl]
        · refine ⟨i, Finset.mem_univ _, ?_⟩
          simp only [Z', hpi, if_true, if_neg hi]
          have := htc i hi; omega
      obtain ⟨γ', Z'', r', h1, h2⟩ := ih _ (by omega) _ _ _ hI' le_rfl
      exact ⟨ℓ :: γ', Z'', r', by simpa using h1, h2⟩
  · -- a round: every pending reader is poised on an expanding step
    push Not at hdrain
    set T : Finset (Proc n m) :=
      (Finset.univ.filter fun i : Fin n => Z.cfg.pend (.inl i) ≠ none).image Sum.inl with hTdef
    have hmemT : ∀ p, p ∈ T ↔ ∃ i, p = .inl i ∧ Z.cfg.pend (.inl i) ≠ none := by
      intro p; simp only [hTdef, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨i, h, rfl⟩; exact ⟨i, rfl, h⟩
      · rintro ⟨i, rfl, h⟩; exact ⟨i, h, rfl⟩
    -- the poised steps are reading steps
    have hpoised : ∀ p ∈ T, Z.cfg.pend p ≠ none ∧ Expanding Z (.tau p) ∧
        ∃ i o k, I.act p (Z.cfg.loc p) = .access i o k ∧
          (o = (CASOp.read : CASOp V) ∨ ∃ a b, o = (CASOp.cas a b : CASOp V)) := by
      intro p hp
      obtain ⟨i, rfl, hi⟩ := (hmemT p).1 hp
      have he := hdrain i hi
      obtain ⟨q, i₀, o, k, hq, hact, ho, -⟩ := expanding_iff.1 he
      have hq' : q = .inl i := by
        have := I.nextLabel_proc Z.cfg (.inl i); rw [hq] at this; exact this
      subst hq'
      exact ⟨hi, hq ▸ he, i₀, o, k, hact, ho⟩
    obtain ⟨l, hnd, hlT, Y, hY, hYaw⟩ := lemma2 hK T
      (fun p hp => by
        obtain ⟨h1, -, i, o, k, h2, -⟩ := hpoised p hp
        exact ⟨h1, i, o, k, h2⟩) hI.aw
    have hmeml : ∀ p, p ∈ l ↔ p ∈ T := fun p => by rw [← hlT, List.mem_toFinset]
    have hexp1 := round_expanding (X := Z) l hnd (fun p hp => by
      obtain ⟨-, -, i, o, k, h1, h2⟩ := hpoised p ((hmeml p).1 hp)
      exact ⟨i, o, k, h1, h2⟩) hY
    have htaus : ∀ ℓ ∈ (l.map Label.tau : List (Label (Proc n m) mutexObj)), ∃ q, ℓ = .tau q := by
      intro ℓ h; obtain ⟨q, -, rfl⟩ := List.mem_map.1 h; exact ⟨q, rfl⟩
    have hpY : Y.cfg.pend = Z.cfg.pend := xrun_pend_of_tau hY htaus
    have hrun' : xrun X₀ (γ ++ l.map .tau) = some Y := by rw [xrun_append_of_eq hI.run, hY]
    have hcnt : ∀ p, xcount (ExpBy p) X₀ (γ ++ l.map .tau) =
        xcount (ExpBy p) X₀ γ + xcount (ExpBy p) Z (l.map .tau) := fun p =>
      xcount_append _ hI.run _
    have htc1 : ∀ i, Z.cfg.pend (.inl i) ≠ none →
        tauCount (.inl i) (l.map .tau : List (Label (Proc n m) mutexObj)) = 1 := by
      intro i hi
      have hm : (Sum.inl i : Proc n m) ∈ l := (hmeml _).2 ((hmemT _).2 ⟨i, rfl, hi⟩)
      unfold tauCount
      rw [List.countP_map]
      rw [← List.count_eq_one_of_mem hnd hm, List.count]
      apply List.countP_congr
      intro q _
      simp [isTauOf]
    have hI' : E2Inv X₀ (γ ++ l.map .tau) Y (j + 1) := by
      refine ⟨hrun', fun ℓ' h' => ?_, fun i' => ?_, fun j' => ?_, fun q => ?_,
        fun i' h' => ?_, ?_⟩
      · rcases List.mem_append.1 h' with h' | h'
        · exact hI.lbl ℓ' h'
        · obtain ⟨q, hq, rfl⟩ := List.mem_map.1 h'
          obtain ⟨i, rfl, -⟩ := (hmemT q).1 ((hmeml q).1 hq)
          exact ⟨rfl, fun q o h => by cases h⟩
      · rw [regFold_append, hI.reg i', regFold_taus _ _ _ (fun ℓ h _ => htaus ℓ h), hpY]
      · rw [hpY]; exact hI.wr j'
      · have := hYaw q; rw [pow_succ]; omega
      · rw [hpY] at h'
        rw [hcnt]
        have := hI.exp i' h'
        have := hexp1 (.inl i') ((hmeml _).2 ((hmemT _).2 ⟨i', rfl, h'⟩)) (hpoised _
          ((hmemT _).2 ⟨i', rfl, h'⟩)).2.1
        omega
      · right
        obtain ⟨i, hi⟩ := hdone
        refine ⟨i, ?_⟩
        rw [hcnt]
        have := hI.exp i hi
        have := hexp1 (.inl i) ((hmeml _).2 ((hmemT _).2 ⟨i, rfl, hi⟩)) (hpoised _
          ((hmemT _).2 ⟨i, rfl, hi⟩)).2.1
        omega
    have hμ' : e2Measure Bm (γ ++ l.map .tau) Y < e2Measure Bm γ Z := by
      unfold e2Measure
      apply Finset.sum_lt_sum
      · intro i' _
        simp only [hpY, tauCount_append]
        split_ifs with h
        · exact le_rfl
        · omega
      · obtain ⟨i, hi⟩ := hdone
        refine ⟨i, Finset.mem_univ _, ?_⟩
        simp only [hpY, tauCount_append, htc1 i hi, if_neg hi]
        have := htc i hi; omega
    obtain ⟨γ', Z'', r', h1, h2⟩ := ih _ (by omega) _ _ _ hI' le_rfl
    exact ⟨l.map .tau ++ γ', Z'', r', by simpa using h1, h2⟩

end Podc.RWLockRMRTradeoff
