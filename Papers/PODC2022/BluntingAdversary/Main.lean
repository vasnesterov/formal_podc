import Papers.PODC2022.BluntingAdversary.Removal
import Papers.PODC2022.BluntingAdversary.TSLSim

/-!
# Quantifying the blunting power (Section 4.2)

* `prob_iter_le_prob_impl`: `Prob[O^k] ≤ Prob[O]` (the transformed objects never help the
  adversary).
* `optBX_le_prob_atom`: for every adversary against `P(O^k)`, `Pr[B ∧ X] ≤ Prob[O^a]` — the
  correct form of Lemma 4.3 (the paper's conditional version is false, see
  `Counterexample.lean`).
* `theorem_4_2_r1`: Theorem 4.2 exactly as stated, for programs with at most one random step.
* `theorem_4_2_weak` (in `Theorem42.lean`): the bound `Prob[O^k] ≤ Prob[O^a] + (1 − q)` for any
  number `r` of random steps, `q = (max{0,k−r}/k)^{n−1}`.
-/

set_option linter.unusedSectionVars false

namespace Podc.BluntingAdversary

open Cslib.SharedMemory Removal
open scoped Classical

variable {P : Type} [Fintype P] [Nonempty P] [DecidableEq P] {A : ObjSpec} {C L : Type}
  {ι : Type} [DecidableEq ι] {Bs : ι → ObjSpec}
  {Pr : Program P A C} {I : Impl A Bs P L} {Pi : P → L → Prop} {k : ℕ}

/-- The transformed objects never help the adversary: `Prob[P(O^k) → B] ≤ Prob[P(O) → B]`. -/
theorem prob_iter_le_prob_impl (hEF : EffectFree I Pi) (hWF : PreambleWF I Pi) (hk : 1 ≤ k)
    (B : (P → C) → Prop) :
    prob Pr (iterSem I Pi k) B ≤ prob Pr (implSem I Pi) B := by
  have := opt_le_avg (Pr := Pr) hEF hWF hk (payK := payB B) (payO := payB B) (payB_nonneg B)
    (payB_le_one B) (fun J sk so _ hrel _ => by simp [payB, hrel.cl]) invK_init
    (fam := fun _ => initCfg Pr (implSem I Pi)) (fun J => rel_init J)
  rwa [avgJ_const] at this

/-- **Correct form of Lemma 4.3.** For every adversary against `P(O^k)`, the probability of
reaching `B` *and* `X` (all object random steps choose randomization-free iterations) is at most
`Prob[P(O^a) → B]`. -/
theorem optBX_le_prob_atom (hall : ∀ p o, I.allowed p o) (hTSL : TailStronglyLinearizable I Pi)
    (hEF : EffectFree I Pi) (hWF : PreambleWF I Pi) (hk : 1 ≤ k) (B : (P → C) → Prop) :
    (sys Pr (iterSem I Pi k)).opt (payBX B) (initCfg Pr (iterSem I Pi k)) ≤
      prob Pr (atomSem A) B := by
  refine le_trans ?_ (optSafe_le_prob_atom Pr I Pi hall hTSL B)
  have := opt_le_avg (Pr := Pr) hEF hWF hk (payK := payBX B) (payO := paySafe B)
    (paySafe_nonneg B) (paySafe_le_one B) ?_ invK_init
    (fam := fun _ => initCfg Pr (implSem I Pi)) (fun J => rel_init J)
  · rwa [avgJ_const] at this
  · intro J sk so hinv hrel ht
    unfold payBX paySafe
    split_ifs with h1 h2 <;> try norm_num
    exfalso; apply h2
    refine ⟨by rw [hrel.cl]; exact h1.1, ?_⟩
    by_contra hb
    rcases hrel.bad (by simpa using hb) with ⟨q, hq⟩ | ⟨q, hq⟩
    · simp [h1.2 q] at hq
    · have hinv' : ∀ q, sk.busy q = true → ∃ o κ, Pr.next q (sk.cl q) = .call o κ :=
        fun q hq => by obtain ⟨o, κ, h, -⟩ := (hinv q).call hq; exact ⟨o, κ, h⟩
      rw [terminal_iff Pr _ hinv'] at ht
      exact absurd hq.1 (by simp [(ht q).1])

/-! ## Theorem 4.2 for programs with at most one random step -/

section R1

/-- Deterministic moves of `P(O)` keep the ghost fields. -/
lemma det_ghost {s s' : Cfg P C L (Mem Bs)} {q : P}
    (h : (sys Pr (implSem I Pi)).move s q = .det s') :
    s'.badCoin = s.badCoin ∧ s'.coins = s.coins := by
  obtain ⟨ℓs, hs⟩ := TSLSim.oStep_of_move h
  exact hs.badCoin

lemma detReach_ghost {s s' : Cfg P C L (Mem Bs)} (h : (sys Pr (implSem I Pi)).DetReach s s') :
    s'.badCoin = s.badCoin ∧ s'.coins = s.coins := by
  induction h with
  | refl => exact ⟨rfl, rfl⟩
  | step q hm _ ih => obtain ⟨h1, h2⟩ := det_ghost hm; exact ⟨ih.1.trans h1, ih.2.trans h2⟩

/-- Once the last possible random step has happened, only `B` matters. -/
lemma opt_payB_le_paySafe_of_last {r : ℕ} (hr : AtMostRandom Pr (implSem I Pi) r)
    (B : (P → C) → Prop) {s : Cfg P C L (Mem Bs)}
    (hs : (sys Pr (implSem I Pi)).Reach (initCfg Pr (implSem I Pi)) s) (hc : s.coins = r)
    (hb : s.badCoin = false) :
    (sys Pr (implSem I Pi)).opt (payB B) s ≤ (sys Pr (implSem I Pi)).opt (paySafe B) s := by
  refine MDP.opt_le_of_super (fun s x => (sys Pr (implSem I Pi)).Reach (initCfg Pr (implSem I Pi)) s ∧
    s.coins = r ∧ s.badCoin = false ∧ x = (sys Pr (implSem I Pi)).opt (paySafe B) s) ?_ ?_ ?_ ?_
    ⟨hs, hc, hb, rfl⟩
  · rintro s x ⟨-, -, -, rfl⟩; exact MDP.opt_nonneg (paySafe_nonneg B) s
  · rintro s x ⟨-, -, hb, rfl⟩ ht
    rw [MDP.opt_of_terminal ht]; simp [payB, paySafe, hb]
  · rintro s x q s' ⟨hs, hc, hb, rfl⟩ hm
    obtain ⟨h1, h2⟩ := det_ghost hm
    exact ⟨_, MDP.opt_det (paySafe_nonneg B) (paySafe_le_one B) hm,
      hs.trans (.det q hm (.refl _)), h2.trans hc, h1.trans hb, rfl⟩
  · rintro s x q m g ⟨hs, hc, -, rfl⟩ hm
    exfalso
    obtain ⟨-, g', -, rfl⟩ := TSLSim.oRand_of_move hm
    have := hr _ (hs.trans (.rand q m _ 0 hm (.refl _)))
    simp at this; omega

/-- Among the choices `J`, those avoiding one forbidden value on a set `D` of at most `n - 1`
processes have probability at least `((k-1)/k)^(n-1)`. -/
lemma card_avoid_ge (hk : 1 ≤ k) (D : Finset P) (hD : D.card ≤ Fintype.card P - 1)
    (ℓ : P → Ch k) :
    (((k - 1 : ℕ) : ℝ) / k) ^ (Fintype.card P - 1) * Fintype.card (P → Ch k) ≤
      ((Fintype.piFinset fun q => if q ∈ D then Finset.univ.erase (ℓ q) else Finset.univ).card : ℝ) := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have hck : Fintype.card (Ch k) = k := by simp; omega
  rw [Fintype.card_piFinset, Fintype.card_fun, hck]
  have hprod : (∏ q : P, ((if q ∈ D then Finset.univ.erase (ℓ q) else Finset.univ) :
      Finset (Ch k)).card : ℝ) = ∏ q : P, (if q ∈ D then ((k - 1 : ℕ) : ℝ) else k) := by
    push_cast
    refine Finset.prod_congr rfl fun q _ => ?_
    split_ifs
    · rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, hck]
    · rw [Finset.card_univ, hck]
  push_cast
  rw [hprod, Finset.prod_ite, Finset.prod_const, Finset.prod_const]
  simp only [Finset.filter_mem_eq_inter, Finset.univ_inter]
  have hcomp : (Finset.univ.filter fun q => q ∉ D).card = Fintype.card P - D.card := by
    rw [Finset.filter_not, Finset.filter_mem_eq_inter, Finset.univ_inter,
      Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ]
  rw [hcomp]
  have hDle : D.card ≤ Fintype.card P := le_trans hD (Nat.sub_le _ _)
  have hbase0 : (0 : ℝ) ≤ ((k - 1 : ℕ) : ℝ) / k := by positivity
  have hbase1 : ((k - 1 : ℕ) : ℝ) / k ≤ 1 := by
    rw [div_le_one hkpos]; exact_mod_cast Nat.sub_le _ _
  calc (((k - 1 : ℕ) : ℝ) / k) ^ (Fintype.card P - 1) * (k : ℝ) ^ Fintype.card P
      ≤ (((k - 1 : ℕ) : ℝ) / k) ^ D.card * (k : ℝ) ^ Fintype.card P := by
        exact mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one hbase0 hbase1 hD) (by positivity)
    _ = ((k - 1 : ℕ) : ℝ) ^ D.card * (k : ℝ) ^ (Fintype.card P - D.card) := by
        rw [div_pow, ← Nat.sub_add_cancel hDle, pow_add]
        field_simp
        simp [Nat.add_sub_cancel]

/-- Mixing bound: if `F ≤ S` on a set of choices of probability at least `q` and `F ≤ T`
everywhere, with `S ≤ T`, then `avg F ≤ q S + (1 - q) T`. -/
lemma avgJ_le_mix {F : (P → Ch k) → ℝ} {S T q : ℝ} (hST : S ≤ T) (hq : 0 ≤ q)
    (G : Finset (P → Ch k)) (hG : ∀ J ∈ G, F J ≤ S) (hT : ∀ J, F J ≤ T)
    (hcard : q * Fintype.card (P → Ch k) ≤ G.card) :
    avgJ k F ≤ q * S + (1 - q) * T := by
  have hN := card_pos (P := P) k
  unfold avgJ
  rw [div_le_iff₀ hN]
  have h1 : ∑ J, F J ≤ ∑ J, (if J ∈ G then S else T) :=
    Finset.sum_le_sum fun J _ => by split_ifs with h; exact hG J h; exact hT J
  have h2 : ∑ J, (if J ∈ G then S else T) = G.card * S + (Fintype.card (P → Ch k) - G.card) * T := by
    rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul]
    simp only [Finset.filter_mem_eq_inter, Finset.univ_inter]
    rw [Finset.filter_not, Finset.filter_mem_eq_inter, Finset.univ_inter,
      Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ]
    push_cast [Finset.card_le_univ G]; ring
  nlinarith

/-- The key estimate behind Theorem 4.2 for `r = 1`. -/
theorem opt_iter_le_mix_r1 (hEF : EffectFree I Pi) (hWF : PreambleWF I Pi) (hk : 1 ≤ k)
    (hr : AtMostRandom Pr (implSem I Pi) 1) (B : (P → C) → Prop) :
    (sys Pr (iterSem I Pi k)).opt (payB B) (initCfg Pr (iterSem I Pi k)) ≤
      (((k - 1 : ℕ) : ℝ) / k) ^ (Fintype.card P - 1) *
          (sys Pr (implSem I Pi)).opt (paySafe B) (initCfg Pr (implSem I Pi)) +
        (1 - (((k - 1 : ℕ) : ℝ) / k) ^ (Fintype.card P - 1)) * prob Pr (implSem I Pi) B := by
  set KS := sys Pr (iterSem I Pi k)
  set OS := sys Pr (implSem I Pi)
  set q : ℝ := (((k - 1 : ℕ) : ℝ) / k) ^ (Fintype.card P - 1) with hq
  set S := OS.opt (paySafe B) (initCfg Pr (implSem I Pi))
  set PO := prob Pr (implSem I Pi) B
  set T := q * S + (1 - q) * PO with hT
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q ≤ 1 := pow_le_one₀ (by positivity) (by rw [div_le_one hkpos]; exact_mod_cast Nat.sub_le _ _)
  have hS0 : 0 ≤ S := MDP.opt_nonneg (paySafe_nonneg B) _
  have hSP : S ≤ PO := MDP.opt_mono (payB_nonneg B) (payB_le_one B) (paySafe_le_payB B) _
  have hT0 : 0 ≤ T := by nlinarith
  have hmix : ∀ y, y ≤ S → y ≤ PO → y ≤ T := fun y h1 h2 => by nlinarith
  have hpS := paySafe_nonneg (L := L) (M := Mem Bs) B
  have hpS1 := paySafe_le_one (L := L) (M := Mem Bs) B
  have hpB := payB_nonneg (L := L) (M := Mem Bs) B
  have hpB1 := payB_le_one (L := L) (M := Mem Bs) B
  refine MDP.opt_le_of_super (fun sk x => (KS.Reach (initCfg Pr (iterSem I Pi k)) sk ∧ sk.coins = 0 ∧
      x = T ∧ ∀ J, ∃ so, Rel Pi k J sk so ∧ OS.DetReach (initCfg Pr (implSem I Pi)) so) ∨
      x = KS.opt (payB B) sk) ?_ ?_ ?_ ?_ (Or.inl ⟨.refl _, rfl, rfl, fun J => ⟨_, rel_init J, .refl _⟩⟩)
  · rintro s x (⟨-, -, rfl, -⟩ | rfl)
    · exact hT0
    · exact MDP.opt_nonneg (payB_nonneg B) _
  · rintro s x (⟨hs, -, rfl, hJ⟩ | rfl) ht
    · obtain ⟨so, hrel, hdr⟩ := hJ (fun _ => ⟨0, by omega⟩)
      have hinv := (reach_rel hEF hWF hk hs).1
      have hto := terminal_of_rel hinv hrel ht
      have hbad : so.badCoin = false := by rw [(detReach_ghost hdr).1]; rfl
      have h1 : payB B s = payB B so := by simp [payB, hrel.cl]
      apply hmix
      · rw [h1]
        calc payB B so = paySafe B so := by simp [payB, paySafe, hbad]
          _ = OS.opt (paySafe B) so := (MDP.opt_of_terminal hto).symm
          _ ≤ S := MDP.opt_detReach hpS hpS1 hdr
      · rw [h1]
        calc payB B so = OS.opt (payB B) so := (MDP.opt_of_terminal hto).symm
          _ ≤ PO := MDP.opt_detReach hpB hpB1 hdr
    · rw [MDP.opt_of_terminal ht]
  · rintro s x p s' (⟨hs, hc, rfl, hJ⟩ | rfl) hm
    · have hinv := (reach_rel hEF hWF hk hs).1
      have hst : ∀ J, ∃ so', Rel Pi k J s' so' ∧ OS.DetReach (initCfg Pr (implSem I Pi)) so' := by
        intro J
        obtain ⟨so, hrel, hdr⟩ := hJ J
        have h : InvK Pr I Pi k s' ∧ ∃ so', Rel Pi k J s' so' ∧ (so' = so ∨ OS.move so p = .det so') := by
          cases hb : s.busy p
          · exact step_det_idle hk hinv hrel hb hm
          · exact step_det_busy hEF hWF hinv hrel hb hm
        obtain ⟨-, so', hrel', hmv⟩ := h
        refine ⟨so', hrel', ?_⟩
        rcases hmv with rfl | hmv
        · exact hdr
        · exact hdr.snoc p hmv
      refine ⟨T, le_rfl, Or.inl ⟨hs.trans (.det p hm (.refl _)), ?_, rfl, hst⟩⟩
      obtain ⟨so, hrel, hdr⟩ := hJ (fun _ => ⟨0, by omega⟩)
      obtain ⟨so', hrel', hdr'⟩ := hst (fun _ => ⟨0, by omega⟩)
      have h1 := (detReach_ghost hdr').2
      rw [← hrel'.coins, h1]; rfl
    · exact ⟨_, MDP.opt_det (payB_nonneg B) (payB_le_one B) hm, Or.inr rfl⟩
  · rintro s x p m g (⟨hs, hc, rfl, hJ⟩ | rfl) hm
    · have hinv := (reach_rel hEF hWF hk hs).1
      choose fam hrel hdr using hJ
      cases hb : s.busy p
      · -- the (only) program random step
        have hstep := fun J => step_rand_client hk hinv (hrel J) hb hm
        choose g' hmv hg' using hstep
        refine ⟨fun i => KS.opt (payB B) (g i), ?_, fun i => Or.inr rfl⟩
        have hle : ∀ i, KS.opt (payB B) (g i) ≤ avgJ k fun J => OS.opt (payB B) (g' J i) := fun i =>
          opt_le_avg hEF hWF hk hpB hpB1 (fun J sk so _ hrel _ => by simp [payB, hrel.cl])
            (hg' (fun _ => ⟨0, by omega⟩) i).1 fun J => (hg' J i).2
        calc (∑ i, KS.opt (payB B) (g i)) / (m + 1)
            ≤ (∑ i, avgJ k fun J => OS.opt (payB B) (g' J i)) / (m + 1) :=
              div_le_div_of_nonneg_right (Finset.sum_le_sum fun i _ => hle i) (by positivity)
          _ = avgJ k fun J => (∑ i, OS.opt (payB B) (g' J i)) / (m + 1) := by
              simp only [avgJ, ← Finset.sum_div]; rw [Finset.sum_comm]; ring
          _ ≤ T := by
            -- processes inside their preamble at the random step
            set D : Finset P := Finset.univ.filter fun q => s.busy q = true ∧
              (s.lo q).ph = .pre ∧ Pi q (s.lo q).cur
            set ℓ : P → Ch k := fun q => if h : (s.lo q).res.length < k - 1 + 1 then ⟨_, h⟩ else 0
            have hpD : p ∉ D := by simp [D, hb]
            have hDc : D.card ≤ Fintype.card P - 1 := by
              have : D ⊆ Finset.univ.erase p := fun q hq => by
                simp only [Finset.mem_erase, Finset.mem_univ, and_true]; rintro rfl; exact hpD hq
              calc D.card ≤ (Finset.univ.erase p).card := Finset.card_le_card this
                _ = Fintype.card P - 1 := by rw [Finset.card_erase_of_mem (Finset.mem_univ _)]; rfl
            refine avgJ_le_mix hSP hq0 _ (fun J hJ => ?_) (fun J => ?_) (card_avoid_ge hk D hDc ℓ)
            · -- a clean choice: the random step happens at a complete prefix
              have hclean : ¬ (fam J).inPreamble (implSem I Pi) := by
                rintro ⟨r, hrb, hrpi⟩
                have hvr := (hrel J).view r
                have hir := hinv r
                rw [Fintype.mem_piFinset] at hJ
                cases hbr : s.busy r
                · simp [oview, hbr] at hvr; rw [hvr.1] at hrb; cases hrb
                · cases hph : (s.lo r).ph with
                  | pre =>
                    simp only [oview, hbr, hph, ite_true] at hvr
                    by_cases hl : (J r : ℕ) < (s.lo r).res.length
                    · simp only [hl, ite_true, Prod.mk.injEq] at hvr
                      rw [hvr.2] at hrpi
                      exact hir.res_post hbr _ (resAt_mem hl) hrpi
                    · by_cases he : (J r : ℕ) = (s.lo r).res.length
                      · simp only [hl, he, lt_irrefl, ite_false, ite_true, Prod.mk.injEq] at hvr
                        rw [hvr.2] at hrpi
                        have hrD : r ∈ D := by
                          simp only [D, Finset.mem_filter, Finset.mem_univ, true_and]
                          exact ⟨hbr, hph, hrpi⟩
                        have := hJ r
                        simp only [hrD, ite_true, Finset.mem_erase, Finset.mem_univ, and_true] at this
                        apply this
                        have hlen := hir.pre_len hbr hph
                        rw [Fin.ext_iff]; simp only [ℓ]; rw [dif_pos (by omega)]; exact he
                      · simp only [hl, he, ite_false, Prod.mk.injEq] at hvr
                        rw [hvr.1] at hrb; cases hrb
                  | choose =>
                    simp only [oview, hbr, hph, ite_true, Prod.mk.injEq] at hvr
                    rw [hvr.2] at hrpi
                    have hlt : (J r : ℕ) < (s.lo r).res.length := by
                      rw [hir.choose_len hbr hph]; have := (J r).isLt; omega
                    exact hir.res_post hbr _ (resAt_mem hlt) hrpi
                  | tail =>
                    simp only [oview, hbr, hph, ite_true, Prod.mk.injEq] at hvr
                    rw [hvr.2] at hrpi
                    exact hir.tail_post hbr hph hrpi
              obtain ⟨-, g0, -, hg0⟩ := TSLSim.oRand_of_move (hmv J)
              have hbad0 : (fam J).badCoin = false := by rw [(detReach_ghost (hdr J)).1]; rfl
              have hc0 : (fam J).coins = 0 := by rw [(detReach_ghost (hdr J)).2]; rfl
              have hsafe : ∀ i, OS.opt (payB B) (g' J i) ≤ OS.opt (paySafe B) (g' J i) := by
                intro i
                refine opt_payB_le_paySafe_of_last hr B
                  ((hdr J).reach.trans (.rand p m _ i (hmv J) (.refl _))) ?_ ?_
                · rw [hg0]; simp [hc0]
                · rw [hg0]; simp [hbad0, hclean]
              calc (∑ i, OS.opt (payB B) (g' J i)) / (m + 1)
                  ≤ (∑ i, OS.opt (paySafe B) (g' J i)) / (m + 1) :=
                    div_le_div_of_nonneg_right (Finset.sum_le_sum fun i _ => hsafe i) (by positivity)
                _ ≤ OS.opt (paySafe B) (fam J) := MDP.opt_rand hpS hpS1 (hmv J)
                _ ≤ S := MDP.opt_detReach hpS hpS1 (hdr J)
            · calc (∑ i, OS.opt (payB B) (g' J i)) / (m + 1) ≤ OS.opt (payB B) (fam J) :=
                    MDP.opt_rand hpB hpB1 (hmv J)
                _ ≤ PO := MDP.opt_detReach hpB hpB1 (hdr J)
      · -- an object random step before the program random step
        obtain ⟨rfl, -, hg, hrelg⟩ := step_rand_obj hk hinv hb hm
        refine ⟨fun _ => T, le_of_eq (by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul, Nat.cast_add, Nat.cast_one, mul_div_cancel_left₀ _ (by positivity)]),
          fun j => Or.inl ⟨hs.trans (.rand p _ g j hm (.refl _)), ?_, rfl, fun J => ?_⟩⟩
        · have h1 := hrelg _ _ j (hrel (Function.update (fun _ => ⟨0, by omega⟩) p j)) (by simp)
          rw [← h1.coins, (hrel _).coins, hc]
        · refine ⟨fam (Function.update J p j),
            rel_congr (hrelg _ _ j (hrel _) (by simp)) fun r hr => ?_, hdr _⟩
          by_cases hrq : r = p
          · subst hrq; exact Or.inr (hg j).2.2.1
          · exact absurd (by simp [Function.update_of_ne hrq]) hr
    · exact ⟨fun i => KS.opt (payB B) (g i), MDP.opt_rand (payB_nonneg B) (payB_le_one B) hm,
        fun i => Or.inr rfl⟩

/-- **Theorem 4.2 of the paper, for programs with at most one random step** (`r = 1`, the case
used in Appendix A.3.1): with `q = ((k-1)/k)^(n-1)`,
`Prob[O^k] ≤ Prob[O^a] + (1 - q) (Prob[O] - Prob[O^a])`. -/
theorem theorem_4_2_r1 (hall : ∀ p o, I.allowed p o) (hTSL : TailStronglyLinearizable I Pi)
    (hEF : EffectFree I Pi) (hWF : PreambleWF I Pi) (hk : 1 ≤ k)
    (hr : AtMostRandom Pr (implSem I Pi) 1) (B : (P → C) → Prop) :
    prob Pr (iterSem I Pi k) B ≤ prob Pr (atomSem A) B +
      (1 - (((k - 1 : ℕ) : ℝ) / k) ^ (Fintype.card P - 1)) *
        (prob Pr (implSem I Pi) B - prob Pr (atomSem A) B) := by
  have h1 := opt_iter_le_mix_r1 hEF hWF hk hr B
  have h2 := optSafe_le_prob_atom Pr I Pi hall hTSL B
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have hq0 : 0 ≤ (((k - 1 : ℕ) : ℝ) / k) ^ (Fintype.card P - 1) := by positivity
  unfold prob at h1 h2 ⊢
  nlinarith

end R1

/-! ## Strongly linearizable objects (one direction of Theorem 2.3, [GHW11]) -/

/-- With the trivial preamble mapping `Π₀` (nothing is inside a preamble) no program random step
is ever flagged. -/
lemma opt_payB_le_paySafe_trivial (B : (P → C) → Prop) :
    (sys Pr (implSem I fun _ _ => False)).opt (payB B) (initCfg Pr (implSem I fun _ _ => False)) ≤
      (sys Pr (implSem I fun _ _ => False)).opt (paySafe B)
        (initCfg Pr (implSem I fun _ _ => False)) := by
  set OS := sys Pr (implSem I fun _ _ => False)
  refine MDP.opt_le_of_super (fun s x => s.badCoin = false ∧ x = OS.opt (paySafe B) s) ?_ ?_ ?_ ?_
    ⟨rfl, rfl⟩
  · rintro s x ⟨-, rfl⟩; exact MDP.opt_nonneg (paySafe_nonneg B) s
  · rintro s x ⟨hb, rfl⟩ ht; rw [MDP.opt_of_terminal ht]; simp [payB, paySafe, hb]
  · rintro s x q s' ⟨hb, rfl⟩ hm
    exact ⟨_, MDP.opt_det (paySafe_nonneg B) (paySafe_le_one B) hm, (det_ghost hm).1.trans hb, rfl⟩
  · rintro s x q m g ⟨hb, rfl⟩ hm
    obtain ⟨-, g', -, rfl⟩ := TSLSim.oRand_of_move hm
    refine ⟨_, MDP.opt_rand (paySafe_nonneg B) (paySafe_le_one B) hm, fun i => ⟨?_, rfl⟩⟩
    simp [hb, Cfg.inPreamble, implSem]

/-- **Theorem 2.3 (one direction).** For a strongly linearizable implementation, the adversary
cannot do better than against the atomic object: `Prob[P(O) → B] ≤ Prob[P(O^a) → B]`. -/
theorem prob_impl_le_atom_of_stronglyLinearizable (hall : ∀ p o, I.allowed p o)
    (hSL : I.StronglyLinearizable) (B : (P → C) → Prop) :
    prob Pr (implSem I fun _ _ => False) B ≤ prob Pr (atomSem A) B := by
  refine (opt_payB_le_paySafe_trivial B).trans (optSafe_le_prob_atom Pr I _ hall ?_ B)
  obtain ⟨f, hf, hpre⟩ := hSL
  exact ⟨⟨f, hf⟩, f, fun α C h _ => hf α ⟨C, h⟩,
    fun α β C C' _ h' _ _ hαβ => hpre α β ⟨C', h'⟩ hαβ⟩

end Podc.BluntingAdversary
