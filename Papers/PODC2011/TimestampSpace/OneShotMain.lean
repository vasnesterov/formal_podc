import Papers.PODC2011.TimestampSpace.OneShotStep

/-!
# Theorem 1.2 of the paper (one-shot lower bound)

`step`: one round of the construction of Section 4; `theorem_1_2`: the bound
`⌊√(2n)⌋ ≤ #objects + ⌈log₂ n⌉ + 2` for `n ≥ 3` processes.
-/

set_option linter.unusedSectionVars false

namespace Cslib.SharedMemory.Timestamp

open Cslib.SharedMemory Impl

variable {P : Type} [DecidableEq P] {T : Type} {ι : Type} [DecidableEq ι] {B : ι → ObjSpec}
  {L : Type} {I : Impl (tsObj T) B P L} [Fintype P] [Fintype ι]

/-- One round of the construction: from a configuration satisfying the invariant in which
`ℓ - |R| ≥ 3`, Lemma 4.1 and the choice of the first move after which a new set of objects
reaches the diagonal give a configuration satisfying the invariant with a strictly larger `R`. -/
theorem step (hI : IsTS I true) (hB : RWLike B) (hn : 3 ≤ Fintype.card P)
    (hι : Fintype.card ι ≤ Nat.sqrt (2 * Fintype.card P))
    {α : List (Label P (tsObj T))} {C : Config (tsObj T) B P L} {R : Finset ι} {ℓ : ℕ}
    (hInv : Inv I (Nat.sqrt (2 * Fintype.card P)) (Fintype.card P) α C R ℓ)
    (hℓ : R.card + 3 ≤ ℓ) :
    ∃ α' C' R' ℓ', Inv I (Nat.sqrt (2 * Fintype.card P)) (Fintype.card P) α' C' R' ℓ' ∧
      R.card < R'.card := by
  classical
  set n := Fintype.card P with hn_def
  set m := Nat.sqrt (2 * n) with hm_def
  set j := R.card with hj
  have hlm := hInv.lem
  -- three disjoint block writes covering `R`, and the idle processes
  obtain ⟨b₀, b₁, b₂, hT, hs₀, hs₁⟩ := exists_triple_ge (I := I) C R
    (fun r hr => by have := hInv.full r hr; omega)
  have S : CovSetup I α C (↑R) b₀ b₁ b₂ :=
    ⟨hInv.run, hInv.adm, hT.nodup, hT.covers, hT.mem₀, hT.mem₁, hT.mem₂⟩
  set U := (idleSet α).toList with hU
  have hUmem : ∀ p, p ∈ U ↔ opsOf α p = [] := fun p => by simp [hU, mem_idleSet]
  have hUlen : U.length = (idleSet α).card := Finset.length_toList _
  have hidle2 := idle_ge_two hInv hn hι
  -- Lemma 4.1
  obtain ⟨c₀, c₁, M₀, M₁, hc, hndM, hMU, hlen, hhalf, hownM, hcntM, hruns, hcov₀, hcov₁⟩ :=
    lemma_4_1 hI hB S U (Finset.nodup_toList _) (by omega) (fun u hu => (hUmem u).1 hu)
  have hbR : ∀ (b : List (P × ι)), (∀ i, i ∈ (↑R : Set ι) ↔ i ∈ b.map Prod.snd) →
      ∀ x ∈ b, x.2 ∈ R := fun b hb x hx => by
    have := (hb x.2).2 (List.mem_map_of_mem hx); simpa using this
  have D : SD I α C R U c₀ c₁ M₀ M₁ := by
    refine ⟨hInv.run, hInv.adm, hUmem, Finset.nodup_toList _, ?_, ?_, ?_, ?_, hndM, hMU, hlen,
      hhalf, hownM, hcntM, hruns, hcov₀, hcov₁⟩
    · intro x hx
      rcases hc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rcases List.mem_append.1 hx with h | h
        · exact ⟨hT.covers x (by simp [h]), hbR _ hT.mem₀ x h⟩
        · exact ⟨hT.covers x (by simp [h]), hbR _ hT.mem₁ x h⟩
      · rcases List.mem_append.1 hx with h | h
        · exact ⟨hT.covers x (by simp [h]), hbR _ hT.mem₁ x h⟩
        · exact ⟨hT.covers x (by simp [h]), hbR _ hT.mem₀ x h⟩
    · have h01 : (b₀.map Prod.fst ++ b₁.map Prod.fst).Nodup :=
        hT.nodup.sublist (List.sublist_append_left _ _)
      rcases hc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact h01
      · exact (List.perm_append_comm.nodup_iff).1 h01
    · rcases hc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> assumption
    · rcases hc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> assumption
  -- the configurations along the schedule
  -- at the end of the schedule some new set of objects reaches the diagonal
  have hΦN : HasFull I (cfgAt I C D.ms D.ms.length) R ℓ := by
    by_contra hno
    have hsp : ∀ S ⊆ Rᶜ, S.Nonempty → ∃ r ∈ S, sig I (cfgAt I C D.ms D.ms.length) r + S.card ≤ ℓ - j - 1 := by
      intro S hS hne
      by_contra hc'
      push Not at hc'
      exact hno ⟨S, hne, Finset.disjoint_of_subset_left hS disjoint_compl_left,
        fun r hr => by have := hc' r hr; omega⟩
    have h1 := sum_le_stair Rᶜ _ _ hsp Rᶜ le_rfl
    rw [← card_outCov] at h1
    have h2 := D.outCov_end
    have h3 := card_partition hInv.run R
    have h4 := hInv.nbound
    rw [← hj] at h4
    have hUc : M₀.length + M₁.length + 1 = (idleSet α).card := by rw [← hUlen]; exact hlen
    have hRc : (Rᶜ).card = Fintype.card ι - j := Finset.card_compl R
    have hRle : j ≤ Fintype.card ι := Finset.card_le_univ R
    have h5 : stair (ℓ - j - 1) (Rᶜ).card ≤ stair (m - j) (m - j) :=
      (stair_mono_left (by omega) _).trans (stair_mono_right _ (by omega))
    have h6 := stair_add m j (m - j)
    rw [show j + (m - j) = m by omega] at h6
    have h7 : stair m m + 2 ≤ n := stair_sqrt_le n hn
    omega
  -- the first move after which this happens
  have hex : ∃ t, t ≤ D.ms.length ∧ HasFull I (cfgAt I C D.ms t) R ℓ := ⟨D.ms.length, le_rfl, hΦN⟩
  set ts := Nat.find hex with hts
  obtain ⟨htsN, hfull⟩ := Nat.find_spec hex
  have hmin : ∀ t < ts, ¬ HasFull I (cfgAt I C D.ms t) R ℓ := fun t ht hf =>
    Nat.find_min hex ht ⟨by omega, hf⟩
  obtain ⟨Q, hQne, hQR, hQ⟩ := hfull
  set X := cfgAt I C D.ms ts with hX
  have hQpos : 1 ≤ Q.card := Finset.card_pos.2 hQne
  have hcardR' : (R ∪ Q).card = j + Q.card := by
    rw [Finset.card_union_of_disjoint hQR.symm]
  -- the previous configuration
  have hprev : ts = 0 ∨ ∃ Y r₀, r₀ ∈ Q ∧ ¬ HasFull I Y R ℓ ∧
      (∀ r, r ≠ r₀ → sig I X r ≤ sig I Y r) ∧ sig I X r₀ ≤ sig I Y r₀ + 1 := by
    rcases Nat.eq_zero_or_pos ts with h0 | hpos
    · exact Or.inl h0
    right
    obtain ⟨XX, hXX⟩ := D.run_ms
    set p := (D.ms[ts - 1]'(by omega)).1
    have hag : ∀ q, q ≠ p → X.loc q = (cfgAt I C D.ms (ts - 1)).loc q ∧
        X.pend q = (cfgAt I C D.ms (ts - 1)).pend q := by
      intro q hq
      have := cfgAt_step_other D.owned hXX (t := ts - 1) (by omega) hq
      rw [show ts - 1 + 1 = ts by omega] at this
      exact this
    have hle := fun r => sig_le_of_agree_except (I := I) p hag r
    have hnf := hmin (ts - 1) (by omega)
    have hmov : ∃ r₀ ∈ Q, I.Covers X p r₀ := by
      by_contra hno
      push Not at hno
      exact hnf ⟨Q, hQne, hQR, fun r hr => by
        have := hle r; rw [ite_eq_right (hno r hr)] at this; have := hQ r hr; omega⟩
    obtain ⟨r₀, hr₀, hcov⟩ := hmov
    refine ⟨_, r₀, hr₀, hnf, fun r hr => ?_, ?_⟩
    · have := hle r
      rwa [ite_eq_right (fun h => hr (covers_unique h hcov)), Nat.add_zero] at this
    · have := hle r₀
      split_ifs at this <;> omega
  -- the new state
  set two := c₀.length + M₀.length < ts ∧ Q.card = 1 with htwo
  set ℓ' := if two then ℓ - 1 else ℓ with hℓ'
  refine ⟨α ++ flat (D.ms.take ts), X, R ∪ Q, ℓ', ⟨D.run_t ts, D.adm_t ts, ?_, ?_, ?_, ?_, ?_,
    ?_⟩, by omega⟩
  · -- full
    intro r hr
    rw [hcardR']
    rcases Finset.mem_union.1 hr with hr | hr
    · have h1 := hInv.full r hr
      have h2 := D.R_loss (t := ts) r
      rw [← hX] at h2
      by_cases h : two
      · rw [hℓ', ite_eq_left h]; split_ifs at h2 <;> omega
      · rw [hℓ', ite_eq_right h]
        simp only [htwo, not_and] at h
        split_ifs at h2 with h3
        · omega
        · have := h (by omega); omega
    · have := hQ r hr
      rw [hℓ']; split_ifs <;> omega
  · -- sparse
    intro S hS hne
    rw [hcardR']
    rw [Finset.disjoint_union_right] at hS
    by_contra hcon
    push Not at hcon
    have hS' : Disjoint (Q ∪ S) R := Finset.disjoint_union_left.2 ⟨hQR, hS.1⟩
    have hne' : (Q ∪ S).Nonempty := hQne.mono Finset.subset_union_left
    have hcard' : (Q ∪ S).card = Q.card + S.card :=
      Finset.card_union_of_disjoint hS.2.symm
    have hSpos : 1 ≤ S.card := Finset.card_pos.2 hne
    rcases hprev with h0 | ⟨Y, r₀, hr₀, hnf, hXY, hXY₀⟩
    · have hXC : X = C := by rw [hX, h0, cfgAt_zero]
      have hnot : ¬ two := fun h => by simp only [htwo] at h; omega
      obtain ⟨r, hr, hle⟩ := hInv.sparse _ hS' hne'
      rw [hcard'] at hle
      rcases Finset.mem_union.1 hr with hr | hr
      · have := hQ r hr; rw [hXC] at this; omega
      · have := hcon r hr; rw [hℓ', ite_eq_right hnot, hXC] at this; omega
    · have : ¬ ∀ r ∈ Q ∪ S, ℓ ≤ sig I Y r + (Q ∪ S).card + j := fun h =>
        hnf ⟨Q ∪ S, hne', hS', h⟩
      push Not at this
      obtain ⟨r, hr, hlt⟩ := this
      rw [hcard'] at hlt
      rcases Finset.mem_union.1 hr with hr | hr
      · have h1 := hQ r hr
        by_cases hrr : r = r₀
        · subst hrr; omega
        · have := hXY r hrr; omega
      · have hrr : r ≠ r₀ := fun h => Finset.disjoint_left.1 hS.2 hr (h ▸ hr₀)
        have h1 := hXY r hrr
        have h2 := hcon r hr
        by_cases h : two
        · rw [hℓ', ite_eq_left h] at h2; simp only [htwo] at h; omega
        · rw [hℓ', ite_eq_right h] at h2; omega
  · -- nbound
    rw [hcardR']
    have hsub : NSet I (α ++ flat (D.ms.take ts)) X (R ∪ Q) ⊆
        NSet I α C R ∪ Finset.univ.filter (fun q => ∃ r ∈ Q, I.Covers X q r) := by
      intro q hq
      rw [mem_NSet] at hq
      obtain ⟨hops, hncov⟩ := hq
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, mem_NSet]
      by_cases hm : q ∈ (D.ms.take ts).map Prod.fst
      · by_cases hqU : q ∈ U
        · obtain ⟨r, hr, hcov⟩ := D.moved_U htsN hm hqU
          by_cases hrQ : r ∈ Q
          · exact Or.inr ⟨r, hrQ, hcov⟩
          · exact absurd ⟨r, by simp [hrQ]; simpa using hr, hcov⟩ hncov
        · have hc' := D.moved_notU hm hqU
          rw [← List.map_append] at hc'
          obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hc'
          refine Or.inl ⟨fun h => hqU ((hUmem _).2 h), fun ⟨r, hr, hcov⟩ => hr ?_⟩
          rw [← covers_unique (D.ccov x hx).1 hcov]; exact (D.ccov x hx).2
      · have hst := D.unmoved hm
        by_cases hcC : ∃ r ∉ R, I.Covers C q r
        · obtain ⟨r, hr, hcov⟩ := hcC
          have hcovX : I.Covers X q r := covers_congr hst.1.symm hst.2.symm hcov
          by_cases hrQ : r ∈ Q
          · exact Or.inr ⟨r, hrQ, hcovX⟩
          · exact absurd ⟨r, by simp [hr, hrQ], hcovX⟩ hncov
        · refine Or.inl ⟨fun h => hops ?_, hcC⟩
          rw [opsOf_append, h, D.opsOf_unmoved hm]; rfl
    have h1 := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    rw [← sum_sig] at h1
    have h2 : ∑ r ∈ Q, sig I X r ≤ stair (m - j) Q.card := by
      rcases hprev with h0 | ⟨Y, r₀, hr₀, hnf, hXY, hXY₀⟩
      · have hXC : X = C := by rw [hX, h0, cfgAt_zero]
        rw [hXC]
        exact (sum_sig_compl_le hInv Q hQR).trans (stair_mono_left (by omega) _)
      · have hsp : ∀ S ⊆ Q, S.Nonempty → ∃ r ∈ S, sig I Y r + S.card ≤ ℓ - j - 1 := by
          intro S hS hne
          by_contra hc'
          push Not at hc'
          exact hnf ⟨S, hne, Finset.disjoint_of_subset_left hS hQR,
            fun r hr => by have := hc' r hr; omega⟩
        have hY := sum_le_stair Q _ _ hsp Q le_rfl
        have hXYs : ∑ r ∈ Q, sig I X r ≤ ∑ r ∈ Q, (sig I Y r + if r = r₀ then 1 else 0) := by
          apply Finset.sum_le_sum
          intro r _
          by_cases hrr : r = r₀
          · subst hrr; simp; omega
          · simp [hrr, hXY r hrr]
        rw [Finset.sum_add_distrib, Finset.sum_ite_eq' Q r₀, ite_eq_left hr₀] at hXYs
        have h3 := stair_pred_add_one (T := ℓ - j) (s := Q.card) (by omega) hQpos
        have h4 := stair_mono_left (show ℓ - j ≤ m - j by omega) Q.card
        omega
    have h3 := stair_add m j Q.card
    have h4 := hInv.nbound
    rw [← hj] at h4
    omega
  · -- idleb
    have hidle_sub : idleSet (α ++ flat (D.ms.take ts)) ⊆ idleSet α := by
      intro q hq; exact ((D.idle_iff htsN).1 hq).1
    have hy := hInv.idleb
    by_cases h : two
    · rw [hℓ', ite_eq_left h]
      simp only [htwo] at h
      have hsub2 : idleSet (α ++ flat (D.ms.take ts)) ⊆ idleSet α \ (M₀.map Prod.fst).toFinset := by
        intro q hq
        obtain ⟨h1, h2⟩ := (D.idle_iff htsN).1 hq
        refine Finset.mem_sdiff.2 ⟨h1, fun h3 => h2 (D.M₀_moved h.1 ?_)⟩
        simpa using h3
      have hM₀sub : (M₀.map Prod.fst).toFinset ⊆ idleSet α := by
        intro q hq
        rw [mem_idleSet, ← hUmem]
        exact D.M_U (by simp at hq ⊢; obtain ⟨b, hb⟩ := hq; exact Or.inl ⟨b, hb⟩)
      have hM₀nd : (M₀.map Prod.fst).Nodup := by
        have := D.Mnd; rw [List.map_append] at this
        exact this.sublist (List.sublist_append_left _ _)
      have hx := Finset.card_le_card hsub2
      rw [Finset.card_sdiff_of_subset hM₀sub, List.toFinset_card_of_nodup hM₀nd,
        List.length_map] at hx
      have hd : m - (ℓ - 1) = (m - ℓ) + 1 := by omega
      rw [hd, pow_succ]
      set x := (idleSet (α ++ flat (D.ms.take ts))).card
      set y := (idleSet α).card
      have h2x : 2 * (x - 1) ≤ y - 1 := by omega
      calc (x - 1) * (2 ^ (m - ℓ) * 2) = (2 * (x - 1)) * 2 ^ (m - ℓ) := by ring
        _ ≤ (y - 1) * 2 ^ (m - ℓ) := Nat.mul_le_mul_right _ h2x
        _ < n := hy
    · rw [hℓ', ite_eq_right h]
      have hx := Finset.card_le_card hidle_sub
      exact lt_of_le_of_lt (Nat.mul_le_mul_right _ (by omega)) hy
  · -- lem
    rw [hℓ']; split_ifs <;> omega
  · -- dclog
    by_cases h : two
    · rw [hℓ', ite_eq_left h]
      have hy := hInv.idleb
      have h1 : 2 ^ (m - ℓ) < n := lt_of_le_of_lt (Nat.le_mul_of_pos_left _ (by omega)) hy
      have h2 := (Nat.lt_clog_iff_pow_lt (by norm_num : 1 < 2)).2 h1
      omega
    · rw [hℓ', ite_eq_right h]; exact hInv.dclog

/-- **Theorem 1.2**: any one-shot timestamp implementation for `n ≥ 3` processes from
read/write-like base objects (e.g. registers) satisfying (non-deterministic) solo termination
uses at least `⌊√(2n)⌋ - ⌈log₂ n⌉ - 2` base objects. -/
theorem theorem_1_2 (hB : RWLike B) (hI : IsTS I true) (hn : 3 ≤ Fintype.card P) :
    Nat.sqrt (2 * Fintype.card P) ≤ Fintype.card ι + Nat.clog 2 (Fintype.card P) + 2 := by
  set n := Fintype.card P
  set m := Nat.sqrt (2 * n)
  by_cases hι : Fintype.card ι ≤ m
  swap; · omega
  have key : ∀ k (α : List (Label P (tsObj T))) (C : Config (tsObj T) B P L) (R : Finset ι) (ℓ : ℕ),
      Inv I m n α C R ℓ → Fintype.card ι - R.card ≤ k →
      ∃ (α' : List (Label P (tsObj T))) (C' : Config (tsObj T) B P L) (R' : Finset ι) (ℓ' : ℕ),
        Inv I m n α' C' R' ℓ' ∧ ℓ' < R'.card + 3 := by
    intro k
    induction k with
    | zero =>
      intro α C R ℓ h hk
      by_cases hl : ℓ < R.card + 3
      · exact ⟨α, C, R, ℓ, h, hl⟩
      · obtain ⟨_, _, R', _, -, hlt⟩ := step hI hB hn hι h (by omega)
        have := Finset.card_le_univ R'
        omega
    | succ k ih =>
      intro α C R ℓ h hk
      by_cases hl : ℓ < R.card + 3
      · exact ⟨α, C, R, ℓ, h, hl⟩
      · obtain ⟨α', C', R', ℓ', h', hlt⟩ := step hI hB hn hι h (by omega)
        exact ih α' C' R' ℓ' h' (by omega)
  obtain ⟨_, _, R', ℓ', hInv', hlt⟩ :=
    key _ [] I.initCfg ∅ m (inv_init (by omega) hι) le_rfl
  have := hInv'.dclog
  have := hInv'.lem
  have := Finset.card_le_univ R'
  omega

/-- **Theorem 1.2** in the paper's form `√(2n) - log n - O(1)`: the number of base objects is
larger than `√(2n) - log₂ n - 4`. -/
theorem theorem_1_2_real (hB : RWLike B) (hI : IsTS I true) (hn : 3 ≤ Fintype.card P) :
    Real.sqrt (2 * Fintype.card P) - Real.logb 2 (Fintype.card P) - 4 < Fintype.card ι := by
  have h := theorem_1_2 hB hI hn
  set n := Fintype.card P
  have h1 : Real.sqrt ((2 * n : ℕ) : ℝ) < Nat.sqrt (2 * n) + 1 := Real.real_sqrt_lt_nat_sqrt_succ
  have hc : 1 ≤ Nat.clog 2 n := Nat.clog_pos (by norm_num) (by omega)
  have h2 : ((Nat.clog 2 n : ℕ) : ℝ) - 1 < Real.logb 2 n := by
    have hp := Nat.pow_pred_clog_lt_self (b := 2) (by norm_num) (show 1 < n by omega)
    rw [Real.lt_logb_iff_rpow_lt (by norm_num) (by positivity)]
    have : ((Nat.clog 2 n : ℝ) - 1) = ((Nat.clog 2 n - 1 : ℕ) : ℝ) := by
      rw [Nat.cast_sub hc]; simp
    rw [this, Real.rpow_natCast]; exact_mod_cast hp
  have h3 : ((Nat.sqrt (2 * n) : ℕ) : ℝ) ≤ Fintype.card ι + Nat.clog 2 n + 2 := by exact_mod_cast h
  push_cast at h1
  linarith

end Cslib.SharedMemory.Timestamp
