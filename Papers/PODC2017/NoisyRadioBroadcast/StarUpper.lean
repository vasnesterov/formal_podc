import Papers.PODC2017.NoisyRadioBroadcast.StarBlocks
import Mathlib.Algebra.Order.Field.GeomSum

/-!
# Lemma 15, possibility part: `k (log n + O(1))` rounds suffice on the star

The adaptive schedule `greedy` lets the source broadcast some message that a leaf does not know
yet (leaves stay silent). Via the per-message coupling, every round of an unsuccessful run is
charged to a pair `(i, t)` such that the first `t` coins of the columns of `mᵢ` do not yet cover
all leaves (`not_delivered_le_sum`); for `t ≥ a` with `n p^a ≤ 1` the probability of this is at
most `p^{t-a}`, and an exponential-moment (Chernoff) bound for the independent messages finishes
the proof (`star_greedy_succeeds`).
-/

namespace Podc.NoisyRadioBroadcast

open Finset Cslib.Probability

variable {n k : ℕ}

theorem run_mono_succ {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (s : V)
    (f : FaultModel) (sch : AdaptiveSchedule V k) (ω : ℕ → V → Bool) (r : ℕ) (u : V) :
    run G s f sch ω r u ⊆ run G s f sch ω (r + 1) u := by
  simp only [run, stepKnow]
  split
  · exact subset_insert _ _
  · exact Subset.rfl

theorem run_mono {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (s : V)
    (f : FaultModel) (sch : AdaptiveSchedule V k) (ω : ℕ → V → Bool) {r r' : ℕ} (h : r ≤ r')
    (u : V) : run G s f sch ω r u ⊆ run G s f sch ω r' u := by
  induction h with
  | refl => exact Subset.rfl
  | step _ ih => exact ih.trans (run_mono_succ G s f sch ω _ u)

open Classical in
/-- The greedy adaptive schedule on the star: the source broadcasts some message that some leaf
does not know yet; the leaves stay silent. -/
noncomputable def greedy : AdaptiveSchedule (Option (Fin n)) k := fun _ K u =>
  if u = none then
    (if h : ∃ i : Fin k, ∃ v : Fin n, i ∉ K (some v) then some (Classical.choose h) else none)
  else none

theorem greedy_leaf (r : ℕ) (K : Know (Option (Fin n)) k) (v : Fin n) :
    greedy r K (some v) = none := by
  simp [greedy]

/-- The first `t` coins of the columns `u (some v)` cover all leaves. -/
def covB {M : ℕ} (u : Option (Fin n) → Fin M → Bool) (t : ℕ) : Prop :=
  ∀ v : Fin n, ∃ j : Fin M, j.val < t ∧ u (some v) j = true

instance {M : ℕ} (u : Option (Fin n) → Fin M → Bool) (t : ℕ) : Decidable (covB u t) := by
  unfold covB; infer_instance

theorem covB_mono {M : ℕ} {u : Option (Fin n) → Fin M → Bool} {t t' : ℕ} (h : t ≤ t')
    (hc : covB u t) : covB u t' := fun v => by
  obtain ⟨j, hj, hu⟩ := hc v; exact ⟨j, hj.trans_le h, hu⟩

/-- The column block of message `i`. -/
def block {M : ℕ} (z : Option (Fin k) × Fin M → Option (Fin n) → Bool) (i : Fin k) :
    Option (Fin n) → Fin M → Bool := fun c j => z (some i, j) c

open Classical in
/-- **Charging.** If the greedy run fails within `R ≤ M` rounds, then `R` is at most the number
of pairs `(i, t)`, `t < M`, such that the first `t` columns of `mᵢ` do not cover all leaves. -/
theorem not_delivered_le_sum (M : ℕ) (hM : 0 < M) (z : Option (Fin k) × Fin M → Option (Fin n) → Bool)
    {R : ℕ} (hRM : R ≤ M)
    (hD : ¬ Delivered (starRun (greedy (n := n) (k := k)) (cpl greedy M hM z) R)) :
    R ≤ ∑ i, #((range M).filter fun t => ¬ covB (block z i) t) := by
  set g : AdaptiveSchedule (Option (Fin n)) k := greedy with hg
  set ω := cpl g M hM z with hω
  -- at every round `r < R` some leaf misses some message
  have hmiss : ∀ r < R, ∃ i : Fin k, ∃ v : Fin n, i ∉ starRun g ω r (some v) := by
    intro r hr
    by_contra hc
    push Not at hc
    apply hD
    intro u
    cases u with
    | none => exact source_know _ _ _
    | some v =>
      exact eq_univ_of_forall fun i => run_mono (star n) none .receiver g ω hr.le _ (hc i v)
  -- the message broadcast in round `r`
  have hact : ∀ r : Fin R, ∃ i, srcAct g ω r = some i ∧
      ∃ v : Fin n, i ∉ starRun g ω r (some v) := by
    intro r
    have h := hmiss r r.2
    rw [srcAct_eq]
    simp only [hg, greedy, ite_true]
    exact ⟨_, dite_eq_left h, Classical.choose_spec h⟩
  choose ι hι hιv using hact
  -- charge round `r` to `(ι r, cnt (ι r) r)`
  have hmem : ∀ r ∈ (univ : Finset (Fin R)), (⟨ι r, cnt g ω (ι r) r⟩ : Σ _ : Fin k, ℕ) ∈
      univ.sigma fun i => (range M).filter fun t => ¬ covB (block z i) t := by
    intro r _
    simp only [mem_sigma, mem_univ, true_and, mem_filter, mem_range]
    refine ⟨(cnt_le _ _ _ _).trans_lt (r.2.trans_le hRM), fun hcov => ?_⟩
    obtain ⟨v, hv⟩ := hιv r
    apply hv
    rw [hω, know_leaf_iff g M hM z greedy_leaf r (r.2.le.trans hRM)]
    exact hcov v
  have hinj : Set.InjOn (fun r : Fin R => (⟨ι r, cnt g ω (ι r) r⟩ : Σ _ : Fin k, ℕ))
      (univ : Finset (Fin R)) := by
    intro r _ r' _ h
    simp only [Sigma.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    have h2' : cnt g ω (ι r) r = cnt g ω (ι r) r' := by
      rw [h1] at h2 ⊢; exact eq_of_heq h2
    by_contra hne
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hlt | hlt
    · exact (cnt_lt_of_lt g hlt (hι r)).ne h2'
    · have := cnt_lt_of_lt g hlt (hι r')
      rw [← h1] at this
      exact this.ne h2'.symm
  have := card_le_card_of_injOn _ hmem hinj
  rwa [card_univ, Fintype.card_fin, card_sigma] at this

/-- The excess of message `i` beyond the first `a` transmissions. -/
noncomputable def excess {M : ℕ} (a : ℕ) (u : Option (Fin n) → Fin M → Bool) : ℕ :=
  #((range (M - a)).filter fun s => ¬ covB u (a + s))

theorem card_not_covB_le {M : ℕ} (a : ℕ) (u : Option (Fin n) → Fin M → Bool) :
    #((range M).filter fun t => ¬ covB u t) ≤ a + excess a u := by
  classical
  have hsub : (range M).filter (fun t => ¬ covB u t) ⊆
      range a ∪ ((range (M - a)).filter fun s => ¬ covB u (a + s)).image (a + ·) := by
    intro t ht
    simp only [mem_filter, mem_range] at ht
    rw [mem_union, mem_range, mem_image]
    by_cases hta : t < a
    · exact Or.inl hta
    · refine Or.inr ⟨t - a, ?_, by omega⟩
      simp only [mem_filter, mem_range]
      exact ⟨by omega, by rw [Nat.add_sub_cancel' (by omega)]; exact ht.2⟩
  calc _ ≤ #(range a ∪ ((range (M - a)).filter fun s => ¬ covB u (a + s)).image (a + ·)) :=
        card_le_card hsub
    _ ≤ #(range a) + #(((range (M - a)).filter fun s => ¬ covB u (a + s)).image (a + ·)) :=
        card_union_le _ _
    _ ≤ a + excess a u := by
        rw [card_range, excess]; exact Nat.add_le_add_left card_image_le _

theorem lt_excess_imp {M : ℕ} {a : ℕ} {u : Option (Fin n) → Fin M → Bool} {d : ℕ}
    (hd : d < excess a u) : ¬ covB u (a + d) := by
  intro hc
  have : excess a u ≤ d := by
    unfold excess
    calc _ ≤ #(range d) := card_le_card fun s hs => by
            simp only [mem_filter, mem_range] at hs ⊢
            by_contra hsd
            exact hs.2 (covB_mono (by omega) hc)
      _ = d := card_range d
  omega

theorem excess_le {M : ℕ} (a : ℕ) (u : Option (Fin n) → Fin M → Bool) : excess a u ≤ M - a := by
  unfold excess; exact (card_filter_le _ _).trans (card_range _).le

open Classical in
/-- `P(the first t columns do not cover all leaves) ≤ n p^t`. -/
theorem sum_not_covB_le {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {M t : ℕ} (ht : t ≤ M) :
    ∑ u : Option (Fin n) → Fin M → Bool, (∏ c, coinProb (1 - p) (u c)) *
      (if ¬ covB u t then 1 else 0) ≤ n * p ^ t := by
  have hw : ∀ u : Option (Fin n) → Fin M → Bool, 0 ≤ ∏ c, coinProb (1 - p) (u c) :=
    fun u => prod_nonneg fun c _ => coinProb_nonneg (by linarith) (by linarith) _
  have hpt : ∀ u : Option (Fin n) → Fin M → Bool, (if ¬ covB u t then (1 : ℝ) else 0) ≤
      ∑ v : Fin n, ∏ c, (if c = some v then
        (if ∀ j : Fin M, j.val < t → u c j = false then 1 else 0) else 1) := by
    intro u
    by_cases hc : covB u t
    · rw [ite_eq_right (not_not.2 hc)]
      exact sum_nonneg fun v _ => prod_nonneg fun c _ => by split_ifs <;> norm_num
    · rw [ite_eq_left hc]
      simp only [covB, not_forall, not_exists, not_and] at hc
      obtain ⟨v, hv⟩ := hc
      refine le_trans ?_ (single_le_sum (f := fun v => ∏ c, (if c = some v then
        (if ∀ j : Fin M, j.val < t → u c j = false then (1 : ℝ) else 0) else 1))
        (fun v _ => prod_nonneg fun c _ => by split_ifs <;> norm_num) (mem_univ v))
      rw [prod_ite_eq' univ (some v)]
      simp only [mem_univ, ite_true]
      rw [ite_eq_left fun j hj => by simpa using hv j hj]
  calc _ ≤ ∑ u : Option (Fin n) → Fin M → Bool, (∏ c, coinProb (1 - p) (u c)) *
          ∑ v : Fin n, ∏ c, (if c = some v then
            (if ∀ j : Fin M, j.val < t → u c j = false then 1 else 0) else 1) :=
        sum_le_sum fun u _ => mul_le_mul_of_nonneg_left (hpt u) (hw u)
    _ = ∑ v : Fin n, ∑ u : Option (Fin n) → Fin M → Bool, (∏ c, coinProb (1 - p) (u c)) *
          ∏ c, (if c = some v then
            (if ∀ j : Fin M, j.val < t → u c j = false then 1 else 0) else 1) := by
        simp_rw [mul_sum]; exact sum_comm
    _ = ∑ v : Fin n, p ^ t := by
        refine sum_congr rfl fun v _ => ?_
        rw [sum_prod_cols (1 - p) (fun c b => if c = some v then
          (if ∀ j : Fin M, j.val < t → b j = false then 1 else 0) else 1)]
        have : ∀ c : Option (Fin n), ∑ b : Fin M → Bool, coinProb (1 - p) b *
            (if c = some v then (if ∀ j : Fin M, j.val < t → b j = false then 1 else 0)
              else 1) = if c = some v then p ^ t else 1 := by
          intro c
          split_ifs
          · rw [sum_coinProb_forall_lt_false _ t ht]; ring
          · simp [sum_coinProb]
        simp_rw [this]
        rw [prod_ite_eq' univ (some v)]
        simp
    _ = n * p ^ t := by rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- **Exponential moment of the excess.** With `λ = 2/(1+p)` and `n p^a ≤ 1`,
`E[λ^{excess}] ≤ 2`. -/
theorem sum_pow_excess_le {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p < 1) {M a : ℕ}
    (ha : (n : ℝ) * p ^ a ≤ 1) :
    ∑ u : Option (Fin n) → Fin M → Bool, (∏ c, coinProb (1 - p) (u c)) *
      (2 / (1 + p)) ^ excess a u ≤ 2 := by
  classical
  set l : ℝ := 2 / (1 + p) with hl
  have hl1 : 1 ≤ l := by rw [hl, le_div_iff₀ (by linarith)]; linarith
  have hlp : l * p < 1 := by
    rw [hl, div_mul_eq_mul_div, div_lt_one (by linarith)]; linarith
  have hw : ∀ u : Option (Fin n) → Fin M → Bool, 0 ≤ ∏ c, coinProb (1 - p) (u c) :=
    fun u => prod_nonneg fun c _ => coinProb_nonneg (by linarith) (by linarith) _
  have hsumw : ∑ u : Option (Fin n) → Fin M → Bool, ∏ c, coinProb (1 - p) (u c) = 1 := by
    rw [← Fintype.prod_sum (fun (_ : Option (Fin n)) b => coinProb (1 - p) b)]
    simp [sum_coinProb]
  -- pointwise telescoping bound
  have hpt : ∀ u : Option (Fin n) → Fin M → Bool, l ^ excess a u ≤
      1 + ∑ d ∈ range (M - a), (l ^ (d + 1) - l ^ d) * (if ¬ covB u (a + d) then 1 else 0) := by
    intro u
    have htel : l ^ excess a u = 1 + ∑ d ∈ range (excess a u), (l ^ (d + 1) - l ^ d) := by
      rw [sum_range_sub (fun d => l ^ d)]; ring
    rw [htel]
    gcongr 1 + ?_
    calc ∑ d ∈ range (excess a u), (l ^ (d + 1) - l ^ d)
        = ∑ d ∈ range (excess a u), (l ^ (d + 1) - l ^ d) *
            (if ¬ covB u (a + d) then 1 else 0) := by
          refine sum_congr rfl fun d hd => ?_
          rw [ite_eq_left (lt_excess_imp (mem_range.1 hd)), mul_one]
      _ ≤ _ := by
          refine sum_le_sum_of_subset_of_nonneg (range_subset_range.2 (excess_le a u))
            fun d _ _ => mul_nonneg ?_ (by split_ifs <;> norm_num)
          rw [pow_succ]; nlinarith [pow_nonneg (zero_le_one.trans hl1) d]
  calc _ ≤ ∑ u : Option (Fin n) → Fin M → Bool, (∏ c, coinProb (1 - p) (u c)) *
          (1 + ∑ d ∈ range (M - a), (l ^ (d + 1) - l ^ d) *
            (if ¬ covB u (a + d) then 1 else 0)) :=
        sum_le_sum fun u _ => mul_le_mul_of_nonneg_left (hpt u) (hw u)
    _ = 1 + ∑ d ∈ range (M - a), (l ^ (d + 1) - l ^ d) *
          ∑ u : Option (Fin n) → Fin M → Bool, (∏ c, coinProb (1 - p) (u c)) *
            (if ¬ covB u (a + d) then 1 else 0) := by
        simp_rw [mul_add, mul_one, sum_add_distrib, hsumw, mul_sum]
        congr 1
        rw [sum_comm]
        refine sum_congr rfl fun d _ => sum_congr rfl fun u _ => by ring
    _ ≤ 1 + ∑ d ∈ range (M - a), (l ^ (d + 1) - l ^ d) * (n * p ^ (a + d)) := by
        gcongr with d hd
        · rw [pow_succ]; nlinarith [pow_nonneg (zero_le_one.trans hl1) d]
        · exact sum_not_covB_le hp0 hp1.le (by have := mem_range.1 hd; omega)
    _ ≤ 1 + ∑ d ∈ range (M - a), (l - 1) * (l * p) ^ d := by
        refine (add_le_add_iff_left 1).2 (sum_le_sum fun d _ => ?_)
        rw [pow_succ, mul_pow, pow_add]
        have h1 : 0 ≤ l ^ d * (l - 1) := mul_nonneg (pow_nonneg (by linarith) _) (by linarith)
        calc (l ^ d * l - l ^ d) * (n * (p ^ a * p ^ d))
            = (l ^ d * (l - 1)) * p ^ d * (n * p ^ a) := by ring
          _ ≤ (l ^ d * (l - 1)) * p ^ d * 1 :=
              mul_le_mul_of_nonneg_left ha (mul_nonneg h1 (pow_nonneg hp0 _))
          _ = (l - 1) * (l ^ d * p ^ d) := by ring
    _ ≤ 1 + (l - 1) * (1 / (1 - l * p)) := by
        rw [← mul_sum]
        refine (add_le_add_iff_left 1).2 (mul_le_mul_of_nonneg_left ?_ (by linarith))
        have := geom_sum_Ico_le_of_lt_one (m := 0) (n := M - a)
          (mul_nonneg (by linarith) hp0) hlp
        rwa [Nat.Ico_zero_eq_range, pow_zero] at this
    _ = 2 := by
        have hlp' : 1 - l * p = l - 1 := by
          rw [hl]; field_simp; ring
        have hpos : 0 < l - 1 := by
          rw [hl, sub_pos, lt_div_iff₀ (by linarith : (0 : ℝ) < 1 + p)]; linarith
        rw [hlp', mul_one_div_cancel hpos.ne']
        norm_num

open Classical in
/-- **Lemma 15, possibility part (round bound).** With receiver faults of probability `p < 1`,
if `n p^a ≤ 1` and `(2/(1+p))^b ≥ 4`, the greedy adaptive schedule delivers `k ≥ 1` messages to
all `n` leaves of the star within `k (a + b)` rounds with probability at least
`1 - 2^{-k} ≥ 1 - 1/k`. -/
theorem star_greedy_succeeds {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p < 1) {a b : ℕ}
    (ha : (n : ℝ) * p ^ a ≤ 1) (hb : 4 ≤ (2 / (1 + p)) ^ b) (hk : 1 ≤ k) :
    RoutingSucceeds (star n) none .receiver p k greedy (k * (a + b)) := by
  set R := k * (a + b) with hR
  set M := R + 1 with hMdef
  have hM : 0 < M := by omega
  have hRM : R ≤ M := by omega
  set l : ℝ := 2 / (1 + p) with hl
  have hl1 : 1 ≤ l := by rw [hl, le_div_iff₀ (by linarith)]; linarith
  have hl0 : 0 < l := by linarith
  set g : AdaptiveSchedule (Option (Fin n)) k := greedy with hg
  have hdet : DeterminedUpTo R (fun ω => ¬ Delivered (run (star n) none .receiver g ω R)) :=
    fun ω ω' h => not_congr (determinedUpTo_delivered (star n) none .receiver g R ω ω' h)
  have hw : ∀ z : Option (Fin k) × Fin M → Option (Fin n) → Bool,
      0 ≤ ∏ i, coinProb (1 - p) (z i) :=
    fun z => prod_nonneg fun i _ => coinProb_nonneg (by linarith) (by linarith) _
  -- pointwise Markov bound
  have hpt : ∀ z : Option (Fin k) × Fin M → Option (Fin n) → Bool,
      (if ¬ Delivered (run (star n) none .receiver g (couple (sel g M hM) (fun _ => true) z) R)
        then (1 : ℝ) else 0) ≤ (l ^ (k * b))⁻¹ * ∏ i, l ^ excess a (block z i) := by
    intro z
    have hnn : 0 ≤ (l ^ (k * b))⁻¹ * ∏ i, l ^ excess a (block z i) :=
      mul_nonneg (inv_nonneg.2 (pow_nonneg hl0.le _)) (prod_nonneg fun i _ => pow_nonneg hl0.le _)
    by_cases hD : Delivered (run (star n) none .receiver g (couple (sel g M hM) (fun _ => true) z) R)
    · rw [ite_eq_right (not_not.2 hD)]; exact hnn
    · rw [ite_eq_left hD]
      have h1 := not_delivered_le_sum M hM z hRM hD
      have h2 : R ≤ k * a + ∑ i, excess a (block z i) := by
        refine h1.trans ?_
        calc ∑ i, #((range M).filter fun t => ¬ covB (block z i) t)
            ≤ ∑ i : Fin k, (a + excess a (block z i)) :=
              sum_le_sum fun i _ => card_not_covB_le a _
          _ = k * a + ∑ i, excess a (block z i) := by
              rw [sum_add_distrib, sum_const, card_univ, Fintype.card_fin, smul_eq_mul]
      have h3 : k * b ≤ ∑ i, excess a (block z i) := by rw [hR] at h2; nlinarith
      rw [prod_pow_eq_pow_sum, ← div_eq_inv_mul, le_div_iff₀ (pow_pos hl0 _), one_mul]
      exact pow_le_pow_right₀ hl1 h3
  have hmain : prob p R (fun ω => ¬ Delivered (run (star n) none .receiver g ω R)) ≤
      (1 / 2) ^ k := by
    rw [prob_eq_sum_couple (sel_causal g M hM) (sel_fresh g M hM hRM) p hdet]
    set G : Option (Fin k) → (Option (Fin n) → Fin M → Bool) → ℝ :=
      fun x u => Option.elim x 1 fun _ => l ^ excess a u with hG
    have hGprod : ∀ z' : Option (Fin k) → Option (Fin n) → Fin M → Bool,
        ∏ i : Fin k, l ^ excess a (block (fun x c => z' x.1 c x.2) i) = ∏ x, G x (z' x) := by
      intro z'
      rw [Fintype.prod_option]
      simp only [hG, Option.elim, one_mul]
      rfl
    refine (sum_le_sum fun z _ => mul_le_mul_of_nonneg_left (by convert hpt z) (hw z)).trans ?_
    calc ∑ z : Option (Fin k) × Fin M → Option (Fin n) → Bool,
            (∏ i, coinProb (1 - p) (z i)) *
              ((l ^ (k * b))⁻¹ * ∏ i, l ^ excess a (block z i))
          = (l ^ (k * b))⁻¹ * ∑ z' : Option (Fin k) → Option (Fin n) → Fin M → Bool,
            (∏ x, ∏ c, coinProb (1 - p) (z' x c)) * ∏ x, G x (z' x) := by
          rw [sum_regroup, mul_sum]
          refine sum_congr rfl fun z' _ => ?_
          rw [hGprod]
          ring
      _ = (l ^ (k * b))⁻¹ * ∏ x : Option (Fin k), ∑ u : Option (Fin n) → Fin M → Bool,
            (∏ c, coinProb (1 - p) (u c)) * G x u := by
          rw [sum_prod_blocks (1 - p) G]
      _ ≤ (l ^ (k * b))⁻¹ * 2 ^ k := by
          refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 (pow_nonneg hl0.le _))
          rw [Fintype.prod_option]
          simp only [hG, Option.elim, mul_one]
          rw [← Fintype.prod_sum (fun (_ : Option (Fin n)) b => coinProb (1 - p) b)]
          simp only [sum_coinProb, prod_const_one, one_mul]
          calc ∏ i : Fin k, ∑ u : Option (Fin n) → Fin M → Bool,
                (∏ c, coinProb (1 - p) (u c)) * l ^ excess a u
              ≤ ∏ _i : Fin k, (2 : ℝ) :=
                Finset.prod_le_prod₀ (fun i _ => sum_nonneg fun u _ => mul_nonneg
                  (prod_nonneg fun c _ => coinProb_nonneg (by linarith) (by linarith) _)
                  (pow_nonneg hl0.le _)) (fun i _ => sum_pow_excess_le hp0 hp1 ha)
            _ = 2 ^ k := by rw [prod_const, card_univ, Fintype.card_fin]
      _ ≤ (4 ^ k)⁻¹ * 2 ^ k := by
          gcongr
          rw [mul_comm k b, pow_mul]
          exact pow_le_pow_left₀ (by norm_num) hb k
      _ = (1 / 2) ^ k := by
          rw [show (4 : ℝ) ^ k = 2 ^ k * 2 ^ k by rw [← mul_pow]; norm_num, mul_inv, one_div_pow]
          field_simp
  unfold RoutingSucceeds
  have hnot := prob_not (V := Option (Fin n)) p R
    (fun ω => Delivered (run (star n) none .receiver g ω R))
  have hk' : (1 / 2 : ℝ) ^ k ≤ 1 / k := by
    rw [one_div_pow, one_div_le_one_div (by positivity) (by exact_mod_cast hk)]
    exact_mod_cast (Nat.lt_two_pow_self).le
  change 1 - 1 / (k : ℝ) ≤ prob p R (fun ω => Delivered (run (star n) none .receiver g ω R))
  linarith

end Podc.NoisyRadioBroadcast
