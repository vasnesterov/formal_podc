import Papers.PODC2017.NoisyRadioBroadcast.StarBlocks

/-!
# Lemma 15, impossibility part: adaptive routing on the star needs `Ω(k log n)` rounds

On the star with `n` leaves and receiver faults, a leaf misses a transmission with probability `p`
independently. If an adaptive routing schedule uses `R < ⌈k/2⌉ · T` rounds, then at least
`⌊k/2⌋ + 1` messages are transmitted fewer than `T` times; via the per-message coupling, all `n`
leaves receive each such message only if each has a clean coin among the first `T` coins of the
message's columns, which happens with probability `(1 - p^T)^n`, independently across messages.
-/

namespace Podc.NoisyRadioBroadcast

open Finset Cslib.Probability

variable {n k : ℕ}

open Classical in
/-- The core bound: if `R < (k - m + 1) T` then every adaptive routing schedule on the star
delivers all `k` messages within `R` rounds with probability at most
`C(k, m) ((1 - p^T)^n)^m`. -/
theorem star_prob_delivered_le {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (sch : AdaptiveSchedule (Option (Fin n)) k) {R T m : ℕ} (hm : m ≤ k)
    (hR : R < (k - m + 1) * T) :
    prob p R (fun ω => Delivered (starRun sch ω R)) ≤ (k.choose m) * ((1 - p ^ T) ^ n) ^ m := by
  set M := R + T + 1 with hMdef
  have hM : 0 < M := by omega
  have hRM : R ≤ M := by omega
  have hTM : T ≤ M := by omega
  rw [prob_eq_sum_couple (sel_causal sch M hM) (sel_fresh sch M hM hRM) p
    (determinedUpTo_delivered _ _ _ _ _)]
  -- the good event for a set `S` of messages
  let Good : Finset (Fin k) → (Option (Fin k) × Fin M → Option (Fin n) → Bool) → Prop :=
    fun S z => ∀ i ∈ S, ∀ v : Fin n, ∃ j : Fin M, j.val < T ∧ z (some i, j) (some v) = true
  have hpt : ∀ z : Option (Fin k) × Fin M → Option (Fin n) → Bool,
      (if Delivered (starRun sch (couple (sel sch M hM) (fun _ => true) z) R) then (1 : ℝ) else 0)
        ≤ ∑ S ∈ powersetCard m univ, if Good S z then 1 else 0 := by
    intro z
    split_ifs with hD
    · -- find the set `S`
      set A := (univ : Finset (Fin k)).filter fun i => T ≤ cnt sch (cpl sch M hM z) i R
      have hA : #A * T ≤ R := by
        calc #A * T = ∑ i ∈ A, T := by rw [sum_const, smul_eq_mul]
          _ ≤ ∑ i ∈ A, cnt sch (cpl sch M hM z) i R := sum_le_sum fun i hi => (mem_filter.1 hi).2
          _ ≤ ∑ i, cnt sch (cpl sch M hM z) i R := sum_le_sum_of_subset (subset_univ _)
          _ ≤ R := sum_cnt_le sch _ R
      have hAk : #A + m ≤ k := by
        by_contra hc
        have : (k - m + 1) * T ≤ #A * T := Nat.mul_le_mul_right _ (by omega)
        omega
      have hcomp : m ≤ #Aᶜ := by rw [card_compl, Fintype.card_fin]; omega
      obtain ⟨S, hSA, hS⟩ := exists_subset_card_eq hcomp
      have hgood : Good S z := by
        intro i hi v
        have hiA : i ∉ A := by have := hSA hi; simpa using this
        have hlt : cnt sch (cpl sch M hM z) i R < T := by
          by_contra hc; exact hiA (mem_filter.2 ⟨mem_univ _, by omega⟩)
        have hknow : i ∈ starRun sch (cpl sch M hM z) R (some v) := by
          have := hD (some v); simp only [starRun] at this ⊢; rw [this]; exact mem_univ _
        obtain ⟨j, hj, hz⟩ := know_leaf_imp sch M hM z R hRM v i hknow
        exact ⟨j, hj.trans hlt, hz⟩
      refine (single_le_sum (f := fun S => if Good S z then (1 : ℝ) else 0)
        (fun S _ => by split_ifs <;> norm_num) (mem_powersetCard.2 ⟨subset_univ _, hS⟩)).trans_eq'
        ?_
      simp [hgood]
    · exact sum_nonneg fun S _ => by split_ifs <;> norm_num
  have hW : ∀ z : Option (Fin k) × Fin M → Option (Fin n) → Bool,
      0 ≤ ∏ i, coinProb (1 - p) (z i) :=
    fun z => prod_nonneg fun i _ => coinProb_nonneg (by linarith) (by linarith) _
  calc _ ≤ ∑ z : Option (Fin k) × Fin M → Option (Fin n) → Bool, (∏ i, coinProb (1 - p) (z i)) *
          ∑ S ∈ powersetCard m univ, (if Good S z then (1 : ℝ) else 0) :=
        sum_le_sum fun z _ => mul_le_mul_of_nonneg_left (hpt z) (hW z)
    _ = ∑ S ∈ powersetCard m univ, ∑ z : Option (Fin k) × Fin M → Option (Fin n) → Bool,
          (∏ i, coinProb (1 - p) (z i)) * (if Good S z then (1 : ℝ) else 0) := by
        simp_rw [mul_sum]; exact sum_comm
    _ = ∑ S ∈ powersetCard m univ, ((1 - p ^ T) ^ n) ^ m := by
        refine sum_congr rfl fun S hS => ?_
        rw [sum_regroup]
        -- the indicator as a product over blocks and columns
        set h : Option (Fin k) → Option (Fin n) → (Fin M → Bool) → ℝ := fun a c b =>
          if a ∈ S.image some ∧ c ∈ (univ : Finset (Fin n)).image some then
            (if ∃ j : Fin M, j.val < T ∧ b j = true then 1 else 0) else 1 with hh
        have hind : ∀ z' : Option (Fin k) → Option (Fin n) → Fin M → Bool,
            (if Good S (fun x c => z' x.1 c x.2) then (1 : ℝ) else 0) =
              ∏ a, ∏ c, h a c (z' a c) := by
          intro z'
          have hprod : ∀ a c, h a c (z' a c) = if (a ∈ S.image some ∧
              c ∈ (univ : Finset (Fin n)).image some) →
                ∃ j : Fin M, j.val < T ∧ z' a c j = true then 1 else 0 := by
            intro a c
            simp only [hh]
            by_cases h1 : a ∈ S.image some ∧ c ∈ (univ : Finset (Fin n)).image some
            · by_cases h2 : ∃ j : Fin M, j.val < T ∧ z' a c j = true
              · rw [ite_eq_left h1, ite_eq_left h2, ite_eq_left fun _ => h2]
              · rw [ite_eq_left h1, ite_eq_right h2, ite_eq_right fun h3 => h2 (h3 h1)]
            · rw [ite_eq_right h1, ite_eq_left fun h3 => absurd h3 h1]
          by_cases hG : Good S (fun x c => z' x.1 c x.2)
          · rw [ite_eq_left hG]; symm
            refine prod_eq_one fun a _ => prod_eq_one fun c _ => ?_
            rw [hprod, ite_eq_left]
            rintro ⟨ha, hc⟩
            obtain ⟨i, hi, rfl⟩ := mem_image.1 ha
            obtain ⟨v, -, rfl⟩ := mem_image.1 hc
            exact hG i hi v
          · rw [ite_eq_right hG]; symm
            simp only [Good, not_forall] at hG
            obtain ⟨i, hi, v, hv⟩ := hG
            refine prod_eq_zero (mem_univ (some i)) (prod_eq_zero (mem_univ (some v)) ?_)
            rw [hprod, ite_eq_right]
            intro h; exact hv (h ⟨mem_image_of_mem _ hi, mem_image_of_mem _ (mem_univ v)⟩)
        simp_rw [hind]
        rw [sum_prod_blocks (1 - p) (fun a u => ∏ c, h a c (u c))]
        simp_rw [sum_prod_cols (1 - p) (h _)]
        have hcol : ∀ a c, ∑ b : Fin M → Bool, coinProb (1 - p) b * h a c b =
            if a ∈ S.image some ∧ c ∈ (univ : Finset (Fin n)).image some then 1 - p ^ T
            else 1 := by
          intro a c
          simp only [hh]
          split_ifs
          · rw [sum_coinProb_exists_lt_true _ T hTM]; ring
          · simp [sum_coinProb]
        simp_rw [hcol]
        have hS' : #S = m := (mem_powersetCard.1 hS).2
        simp_rw [ite_and]
        have hin : ∀ a : Option (Fin k), (∏ c : Option (Fin n), if a ∈ S.image some then
            (if c ∈ (univ : Finset (Fin n)).image some then 1 - p ^ T else 1) else 1) =
            if a ∈ S.image some then (1 - p ^ T) ^ n else 1 := by
          intro a
          split_ifs
          · rw [prod_ite_mem, univ_inter, prod_image (fun _ _ _ _ h => Option.some.inj h),
              prod_const, card_univ, Fintype.card_fin]
          · simp
        simp_rw [hin]
        rw [prod_ite_mem, univ_inter, prod_image (fun _ _ _ _ h => Option.some.inj h), prod_const,
          hS']
    _ = (k.choose m) * ((1 - p ^ T) ^ n) ^ m := by
        rw [sum_const, card_powersetCard, card_univ, Fintype.card_fin, nsmul_eq_mul]

end Podc.NoisyRadioBroadcast
