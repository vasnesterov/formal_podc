import Papers.PODC2021.WakeUpMatching.Chain
import Papers.PODC2021.WakeUpMatching.Schedule
import Papers.PODC2021.WakeUpMatching.BadRound
import Papers.PODC2021.WakeUpMatching.Lemma56
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Lemma 5.4: Algorithm 1 outputs a maximal matching with high probability

Dani, Gupta, Hayes, Pettie, PODC 2021 (arXiv:2104.09096v2), Lemma 5.4 (and the maximality part of
Theorem 1.1).

**The random process.** Algorithm 1 runs `T` rounds; in round `t` every unmatched node recruits
with probability `r(t)/2`, accepts with probability `r(t)/2` and sleeps otherwise, independently,
with `r(t) = 1/(2 + 3(1 − (t−1)/T)Δ)` (`rate`). An execution is a path `ω : Fin T → V → Role`
(round `i + 1` uses `ω i`) with product weight `pathWeight (roundLaw T Δ) ω`
(`Chain.lean`); `runState ω t` are the partner variables after `t` rounds (`= partnerAfter`,
`runState_eq_partnerAfter`).

**Lemma 5.4** (`lemma_5_4`): if `Δ ≥ 1` bounds the maximum degree, then
`P(M(T) is maximal) ≥ 1 − T |V| exp(−((T/(3Δ)) ln(3/2) − 1/2)/(6e))`.
With `T ≥ 1000 Δ ln n`, `n ≥ |V|`, this is `≥ 1 − 2T|V|/n⁶` (`lemma_5_4_whp`), i.e. `1 − o(1/n²)`
for `T = ⌈1000 Δ ln n⌉`, as claimed.

The proof is the paper's: if round `T + 1` is bad (`Δ(T) ≥ 1`, i.e. `M(T)` not maximal), take
the first bad round `t` and a witness `v` (`exists_first_bad`); then `Z(v, t') = 1` on
`I = {t' < t : 3 r(t') > 2 r(t)}`. By the chain rule (`pathProb_forall_le`) and Lemma 5.6 this
has probability `≤ ∏_{t'∈I} (1 − r(t')/(6e)) ≤ exp(−∑_I r/(6e))`, and
`∑_I r ≥ (T/(3Δ)) ln(3/2) − 1/2` (`sum_rate_ge`, a telescoping replacement of the paper's
integral). A union bound over `(t, v)` finishes.
-/

set_option linter.unusedSectionVars false

namespace Podc.WakeUpMatching

open Finset

instance : Inhabited Role := ⟨.sleep⟩

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The participation rate `r(t)` as a function of the round number. -/
noncomputable def rr (T Δ : ℕ) (t : ℕ) : ℝ := rate T Δ t

/-- The law of the role vector of round `i + 1` (path index `i`); after round `T` (irrelevant)
the rate is frozen at `r(T)` so that all laws are probability laws. -/
noncomputable def roundLaw (T Δ : ℕ) (i : ℕ) (x : V → Role) : ℝ :=
  ∏ u, roleLaw (rr T Δ (min (i + 1) T)) (x u)

/-- The partner variables after `t` rounds of the execution `ω`. -/
noncomputable def runState {T : ℕ} (ω : Fin T → V → Role) : ℕ → V → Option V :=
  pathState (fun _ s x => round G s x) (fun _ => none) ω

/-- `runState` is Algorithm 1 run with the role choices of `ω` (`partnerAfter`, `Radio.lean`). -/
theorem runState_eq_partnerAfter {T : ℕ} (ω : Fin T → V → Role) (t : ℕ) :
    runState G ω t = partnerAfter G (fun t => pathExt ω (t - 1)) t := by
  induction t with
  | zero => rfl
  | succ t ih => simp only [runState, pathState, partnerAfter] at ih ⊢; rw [ih]; rfl

/-- The partner variables encode a *maximal* matching: every edge has a matched endpoint. -/
def IsMaximalState (s : V → Option V) : Prop := ∀ x y, G.Adj x y → (s x).isSome ∨ (s y).isSome

variable {G}

section Rates

variable {T Δ : ℕ} (hT : 0 < T) (hΔ : 1 ≤ Δ)
include hT hΔ

theorem rr_pos {t : ℕ} (ht : t ≤ T + 1) : 0 < rr T Δ t :=
  rate_pos (by exact_mod_cast hT) (by exact_mod_cast hΔ) (by exact_mod_cast ht)

theorem rr_le_half {t : ℕ} (ht : t ≤ T + 1) : rr T Δ t ≤ 1 / 2 :=
  rate_le_half (by exact_mod_cast hT) (by exact_mod_cast hΔ) (by exact_mod_cast ht)

theorem rr_mono {s t : ℕ} (hst : s ≤ t) (ht : t ≤ T + 1) : rr T Δ s ≤ rr T Δ t :=
  rate_mono (by exact_mod_cast hT) (by exact_mod_cast hΔ) (by exact_mod_cast hst)
    (by exact_mod_cast ht)

theorem roundLaw_nonneg (i : ℕ) (x : V → Role) : 0 ≤ roundLaw (V := V) T Δ i x :=
  prod_nonneg fun _ _ => roleLaw_nonneg (rr_pos hT hΔ (by omega)).le
    ((rr_le_half hT hΔ (by omega)).trans (by norm_num)) _

omit hT hΔ in
theorem roundLaw_sum (i : ℕ) : ∑ x, roundLaw (V := V) T Δ i x = 1 := by
  have := prob_true (V := V) (rr T Δ (min (i + 1) T))
  unfold prob at this
  simpa [roundLaw] using this

/-- The lower bound on `∑_{t' ∈ I} r(t')` (the paper's integral computation). -/
theorem sum_lostSet_ge {t : ℕ} (ht1 : 1 ≤ t) (ht : t ≤ T + 1) (hbad : 1 / 2 ≤ Δ * rr T Δ t) :
    (T : ℝ) / (3 * Δ) * Real.log (3 / 2) - 1 / 2 ≤ ∑ t' ∈ lostSet (rr T Δ) t, rr T Δ t' := by
  have hTr : (0 : ℝ) < T := by exact_mod_cast hT
  have hΔr : (1 : ℝ) ≤ Δ := by exact_mod_cast hΔ
  set r := rr T Δ
  set P : ℕ → Prop := fun t' => 3 * r t' ≤ 2 * r t
  set a := Nat.findGreatest P (t - 1)
  have hP0 : P 0 := by
    have h1 : r 0 ≤ r 1 := rr_mono hT hΔ (Nat.zero_le 1) (by omega)
    have h2 : r 1 < 1 / (3 * Δ) := by
      have := rate_one_lt (T := (T : ℝ)) hΔr; simpa [r, rr] using this
    have h3 : 1 / (Δ : ℝ) ≤ 2 * r t := by
      rw [div_le_iff₀ (by linarith)]; linarith
    have h4 : 3 * (1 / (3 * (Δ : ℝ))) = 1 / Δ := by field_simp
    show 3 * r 0 ≤ 2 * r t
    linarith
  have haP : P a := Nat.findGreatest_spec (P := P) (Nat.zero_le _) hP0
  have hale : a ≤ t - 1 := Nat.findGreatest_le _
  have hlost : lostSet r t = Ioc a (t - 1) := by
    ext t'
    simp only [lostSet, mem_filter, mem_Icc, mem_Ioc]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      refine ⟨?_, h2⟩
      by_contra hle
      have : r t' ≤ r a := rr_mono hT hΔ (by omega) (by omega)
      have : 3 * r a ≤ 2 * r t := haP
      linarith
    · rintro ⟨h1, h2⟩
      refine ⟨⟨by omega, h2⟩, ?_⟩
      have := Nat.findGreatest_is_greatest (P := P) h1 h2
      simp only [P, not_le] at this
      exact this
  have hsum := sum_rate_ge hTr hΔr a t (by omega) (by exact_mod_cast ht)
  have hsplit : ∑ t' ∈ Ioc a t, rate T Δ t' = ∑ t' ∈ Ioc a (t - 1), r t' + r t := by
    have := Finset.sum_Ioc_succ_top (f := r) hale
    rw [Nat.sub_add_cancel ht1] at this
    exact this
  have hra : 0 < r a := rr_pos hT hΔ (by omega)
  have hrt : r t ≤ 1 / 2 := rr_le_half hT hΔ ht
  have hratio : Real.log (3 / 2) ≤ Real.log (r t / r a) := by
    apply Real.log_le_log (by norm_num)
    rw [le_div_iff₀ hra]; linarith [haP]
  have hcoef : 0 ≤ (T : ℝ) / (3 * Δ) := by positivity
  rw [hlost]
  have := mul_le_mul_of_nonneg_left hratio hcoef
  simp only [r, rr] at hsplit hsum this hrt ⊢
  linarith

end Rates

/-- If round `T + 1` is good (`Δ(T) · 1/2 < 1/2`), the final matching is maximal. -/
theorem isMaximalState_of_good {T Δ : ℕ} (hT : 0 < T) {s : ℕ → V → Option V}
    (h : Good G (rr T Δ) s (T + 1)) : IsMaximalState G (s T) := by
  unfold Good at h
  rw [show T + 1 - 1 = T by omega,
    show rr T Δ (T + 1) = 1 / 2 by
      simpa [rr] using rate_T_add_one (Δ := (Δ : ℝ)) (by exact_mod_cast hT : (0 : ℝ) < T)] at h
  have h0 : maxRes G (s T) = 0 := by
    have : (maxRes G (s T) : ℝ) < 1 := by linarith
    exact_mod_cast Nat.lt_one_iff.1 (by exact_mod_cast this)
  intro x y hxy
  by_contra hc
  simp only [not_or, Bool.not_eq_true, Option.isSome_eq_false_iff, Option.isNone_iff_eq_none] at hc
  have hy : y ∈ resN G (s T) x := by simp [resN, hxy, hc.2]
  have : #(resN G (s T) x) ≤ maxRes G (s T) :=
    le_sup (f := fun u => #(resN G (s T) u)) (by simp [hc.1])
  have := card_pos.2 ⟨y, hy⟩
  omega

/-! ### The probability bound -/

/-- The per-round event behind `Z(v, i + 1)`: state `s` before round `i + 1`, roles `x`. -/
def stepZ (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ → ℝ) (v : V) (i : ℕ)
    (s : V → Option V) (x : V → Role) : Prop :=
  (maxRes G s : ℝ) * r (i + 1) < 1 / 2 ∧ round G s x v = none ∧
    1 ≤ 3 * r (i + 1) * (#(resN G (round G s x) v) : ℝ)

/-- The event `∏_{t' ∈ I(t)} Z(v, t') = 1` of the paper (`E_{v,t}`). -/
def lostEvent (G : SimpleGraph V) [DecidableRel G.Adj] (T Δ t : ℕ) (v : V)
    (ω : Fin T → V → Role) : Prop :=
  ∀ t' ∈ lostSet (rr T Δ) t, LostOpp G (rr T Δ) (runState G ω) v t'

/-- The bound `exp(−((T/(3Δ)) ln(3/2) − 1/2)/(6e))` on `P(E_{v,t})`. -/
noncomputable def lostBound (T Δ : ℕ) : ℝ :=
  Real.exp (-(((T : ℝ) / (3 * Δ) * Real.log (3 / 2) - 1 / 2) / (6 * Real.exp 1)))

section Prob

variable {T Δ : ℕ} (hT : 0 < T) (hΔ : 1 ≤ Δ)
include hT hΔ

/-- Lemma 5.6 in the path space: `E(Z(v, i+1) | M(i)) ≤ 1 − r(i+1)/(6e)`. -/
theorem pathStepProb_stepZ_le {i : ℕ} (hi : i < T) (v : V) (s : V → Option V) :
    pathStepProb (roundLaw (V := V) T Δ) i (stepZ G (rr T Δ) v i s) ≤
      1 - rr T Δ (i + 1) / (6 * Real.exp 1) := by
  have hmin : min (i + 1) T = i + 1 := by omega
  have heq : ∀ (E : (V → Role) → Prop) [DecidablePred E],
      pathStepProb (roundLaw (V := V) T Δ) i E = prob (rr T Δ (i + 1)) E := by
    intro E _
    rw [pathStepProb_eq_sum_ite]; unfold prob; rw [sum_filter]
    simp only [roundLaw, hmin]
  have hr0 := rr_pos hT hΔ (t := i + 1) (by omega)
  have hr1 := rr_le_half hT hΔ (t := i + 1) (by omega)
  classical
  by_cases hg : (maxRes G s : ℝ) * rr T Δ (i + 1) < 1 / 2
  · have hZ : stepZ G (rr T Δ) v i s = fun x => round G s x v = none ∧
        1 ≤ 3 * rr T Δ (i + 1) * (#(resN G (round G s x) v) : ℝ) := by
      funext x; exact propext ⟨fun h => h.2, fun h => ⟨hg, h⟩⟩
    rw [hZ, heq]
    exact lemma_5_6 s hr0 hr1 (Δ := maxRes G s)
      (fun u hu => le_sup (f := fun u => #(resN G s u)) (by simp [hu])) hg v
  · rw [heq, prob_false (fun x h => hg h.1)]
    have : rr T Δ (i + 1) / (6 * Real.exp 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      have := Real.add_one_le_exp 1; linarith
    linarith

/-- `P(E_{v,t}) ≤ exp(−((T/(3Δ)) ln(3/2) − 1/2)/(6e))` for every round `t ∈ [1, T + 1]` with
`Δ r(t) ≥ 1/2`. -/
theorem pathProb_lostEvent_le {t : ℕ} (ht1 : 1 ≤ t) (ht : t ≤ T + 1)
    (hbad : 1 / 2 ≤ Δ * rr T Δ t) (v : V) :
    pathProb (roundLaw (V := V) T Δ) T (lostEvent G T Δ t v) ≤ lostBound T Δ := by
  have hp := roundLaw_nonneg (V := V) hT hΔ
  have hp1 := roundLaw_sum (V := V) (T := T) (Δ := Δ)
  set r := rr T Δ
  set I := (lostSet r t).image (· - 1)
  have hmemL : ∀ t' ∈ lostSet r t, 1 ≤ t' ∧ t' ≤ t - 1 := fun t' h => by
    simp only [lostSet, mem_filter, mem_Icc] at h; exact h.1
  have hI : ∀ i ∈ I, i < T := by
    intro i hi
    obtain ⟨t', ht', rfl⟩ := mem_image.1 hi
    have := hmemL t' ht'; omega
  -- step 1: the event is contained in the chain event
  have h1 : pathProb (roundLaw (V := V) T Δ) T (lostEvent G T Δ t v) ≤
      pathProb (roundLaw (V := V) T Δ) T (fun ω => ∀ i ∈ I,
        stepZ G r v i (pathState (fun _ s x => round G s x) (fun _ => none) ω i)
          (pathExt ω i)) := by
    refine pathProb_mono hp fun ω h i hi => ?_
    obtain ⟨t', ht', rfl⟩ := mem_image.1 hi
    have hL := hmemL t' ht'
    obtain ⟨j, rfl⟩ : ∃ j, t' = j + 1 := ⟨t' - 1, by omega⟩
    obtain ⟨hgood, hnone, hd⟩ := h (j + 1) ht'
    exact ⟨hgood, hnone, hd⟩
  -- step 2: chain rule with Lemma 5.6
  have h2 := pathProb_forall_le hp hp1 (fun _ s x => round G s x) (fun _ => none) I hI
    (fun i => stepZ G r v i) (fun i => 1 - r (i + 1) / (6 * Real.exp 1))
    (fun i hi s => pathStepProb_stepZ_le hT hΔ (hI i hi) v s)
  -- step 3: back to the rounds of `I(t)`
  have h3 : ∏ i ∈ I, (1 - r (i + 1) / (6 * Real.exp 1)) =
      ∏ t' ∈ lostSet r t, (1 - r t' / (6 * Real.exp 1)) := by
    rw [prod_image]
    · refine prod_congr rfl fun t' ht' => ?_
      have := (hmemL t' ht').1
      rw [Nat.sub_add_cancel this]
    · intro a ha b hb hab
      have := (hmemL a ha).1; have := (hmemL b hb).1
      simp only at hab; omega
  -- step 4: `∏ (1 − x) ≤ exp(−∑ x)` and the sum bound
  have h4 := prod_one_sub_le_exp (lostSet r t) (fun t' => r t' / (6 * Real.exp 1)) (by
    intro t' ht'
    have hL := hmemL t' ht'
    have hpos := rr_pos hT hΔ (t := t') (by omega)
    have hle := rr_le_half hT hΔ (t := t') (by omega)
    refine ⟨by positivity, ?_⟩
    rw [div_le_one (by positivity)]
    have := Real.add_one_le_exp 1; linarith)
  have h5 := sum_lostSet_ge hT hΔ ht1 ht hbad
  have h6 : -∑ t' ∈ lostSet r t, r t' / (6 * Real.exp 1) ≤
      -(((T : ℝ) / (3 * Δ) * Real.log (3 / 2) - 1 / 2) / (6 * Real.exp 1)) := by
    have hs : ∑ t' ∈ lostSet r t, r t' / (6 * Real.exp 1) =
        (∑ t' ∈ lostSet r t, r t') / (6 * Real.exp 1) := by
      simp only [div_eq_mul_inv, Finset.sum_mul]
    rw [hs, neg_le_neg_iff]
    exact div_le_div_of_nonneg_right h5 (by positivity)
  calc _ ≤ _ := h1
    _ ≤ _ := h2
    _ = _ := h3
    _ ≤ _ := h4
    _ ≤ lostBound T Δ := Real.exp_le_exp.2 h6

/-- **Lemma 5.4.** If `Δ ≥ 1` bounds the maximum degree of `G` and Algorithm 1 runs `T ≥ 1`
rounds, then `M(T)` is a maximal matching with probability at least
`1 − T |V| exp(−((T/(3Δ)) ln(3/2) − 1/2)/(6e))`. -/
theorem lemma_5_4 (hdeg : ∀ v, G.degree v ≤ Δ) :
    1 - T * Fintype.card V * lostBound T Δ ≤
      pathProb (roundLaw (V := V) T Δ) T (fun ω => IsMaximalState G (runState G ω T)) := by
  have hp := roundLaw_nonneg (V := V) hT hΔ
  have hp1 := roundLaw_sum (V := V) (T := T) (Δ := Δ)
  set r := rr T Δ
  set S := ((Icc 1 (T + 1)).filter fun t => 1 / 2 ≤ Δ * r t) ×ˢ (univ : Finset V)
  -- the failure event is covered by the events `E_{v,t}`
  have hcover : ∀ ω, ¬ IsMaximalState G (runState G ω T) →
      ∃ q ∈ S, lostEvent G T Δ q.1 q.2 ω := by
    intro ω hω
    have hbad : ¬ Good G r (runState G ω) (T + 1) := fun h => hω (isMaximalState_of_good hT h)
    have hs : IsRoundSeq (G := G) (runState G ω) := fun t => ⟨pathExt ω t, rfl⟩
    obtain ⟨t₁, h1, ht₁, -, -, v, hv, hlost⟩ :=
      exists_first_bad r hs (fun t' ht' => rr_pos hT hΔ ht') (by omega) hbad
    have hdv : (#(resN G (runState G ω (t₁ - 1)) v) : ℝ) ≤ Δ := by
      have : #(resN G (runState G ω (t₁ - 1)) v) ≤ G.degree v := by
        rw [← SimpleGraph.card_neighborFinset_eq_degree]
        exact card_le_card fun u hu => by
          simp only [resN, mem_filter, mem_univ, true_and] at hu; simpa using hu.1
      exact_mod_cast this.trans (hdeg v)
    have hrpos := rr_pos hT hΔ ht₁
    refine ⟨(t₁, v), ?_, hlost⟩
    simp only [S, mem_product, mem_filter, mem_Icc, mem_univ, and_true]
    exact ⟨⟨h1, ht₁⟩, by nlinarith⟩
  -- `|S| ≤ T |V|`: round `1` is never bad
  have hS : (#S : ℝ) ≤ T * Fintype.card V := by
    have hsub : ((Icc 1 (T + 1)).filter fun t => 1 / 2 ≤ Δ * r t) ⊆ Icc 2 (T + 1) := by
      intro t ht
      simp only [mem_filter, mem_Icc] at ht ⊢
      refine ⟨?_, ht.1.2⟩
      by_contra h
      have : t = 1 := by omega
      subst this
      have hΔr : (1 : ℝ) ≤ Δ := by exact_mod_cast hΔ
      have h1 : r 1 < 1 / (3 * Δ) := by
        have := rate_one_lt (T := (T : ℝ)) hΔr; simpa [r, rr] using this
      have : (Δ : ℝ) * r 1 < 1 / 3 := by
        rw [lt_div_iff₀ (by positivity)] at h1
        nlinarith
      linarith [ht.2]
    have := card_le_card hsub
    simp only [Nat.card_Icc] at this
    have : #S ≤ T * Fintype.card V := by
      simp only [S, card_product, card_univ]
      exact Nat.mul_le_mul_right _ (by omega)
    exact_mod_cast this
  have hfail : pathProb (roundLaw (V := V) T Δ) T
      (fun ω => ¬ IsMaximalState G (runState G ω T)) ≤ T * Fintype.card V * lostBound T Δ := by
    calc _ ≤ pathProb (roundLaw (V := V) T Δ) T
          (fun ω => ∃ q ∈ S, lostEvent G T Δ q.1 q.2 ω) := pathProb_mono hp hcover
      _ ≤ ∑ q ∈ S, pathProb (roundLaw (V := V) T Δ) T (lostEvent G T Δ q.1 q.2) :=
          pathProb_exists_le hp S _
      _ ≤ ∑ _q ∈ S, lostBound T Δ := by
          refine sum_le_sum fun q hq => ?_
          simp only [S, mem_product, mem_filter, mem_Icc] at hq
          exact pathProb_lostEvent_le hT hΔ hq.1.1.1 hq.1.1.2 hq.1.2 q.2
      _ = #S * lostBound T Δ := by rw [sum_const, nsmul_eq_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right hS (Real.exp_pos _).le
  have := pathProb_not (T := T) hp1 (fun ω => IsMaximalState G (runState G ω T))
  linarith

/-- **Lemma 5.4, high-probability form.** With `T ≥ 1000 Δ ln n` rounds (`C = 1000` as in the
paper) and `n ≥ 1`, the matching is maximal with probability `≥ 1 − 2 T |V| / n⁶`; for
`n ≥ |V|` and `T = ⌈1000 Δ ln n⌉` this is `1 − o(1/n²)`. -/
theorem lemma_5_4_whp (hdeg : ∀ v, G.degree v ≤ Δ) {n : ℕ} (hn : 1 ≤ n)
    (hTn : 1000 * (Δ : ℝ) * Real.log n ≤ T) :
    1 - 2 * T * Fintype.card V / (n : ℝ) ^ 6 ≤
      pathProb (roundLaw (V := V) T Δ) T (fun ω => IsMaximalState G (runState G ω T)) := by
  refine le_trans ?_ (lemma_5_4 hT hΔ hdeg)
  have hΔr : (1 : ℝ) ≤ Δ := by exact_mod_cast hΔ
  have hnr : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hL : 0 ≤ Real.log n := Real.log_nonneg hnr
  have hl15 : 1 / 3 ≤ Real.log (3 / 2) := by
    have := Real.one_sub_inv_le_log_of_pos (x := 3 / 2) (by norm_num); norm_num at this ⊢
    linarith
  have he1 := Real.exp_one_lt_d9
  have he0 := Real.exp_one_gt_d9
  have hl2 := Real.log_two_gt_d9
  have hT3 : 1000 / 3 * Real.log n ≤ (T : ℝ) / (3 * Δ) := by
    rw [le_div_iff₀ (by positivity)]; nlinarith
  -- the exponent is at least `6 ln n − ln 2`
  have hX : 6 * Real.log n - Real.log 2 ≤
      ((T : ℝ) / (3 * Δ) * Real.log (3 / 2) - 1 / 2) / (6 * Real.exp 1) := by
    rw [le_div_iff₀ (by positivity)]
    have : 1000 / 3 * Real.log n * (1 / 3) ≤ (T : ℝ) / (3 * Δ) * Real.log (3 / 2) :=
      mul_le_mul hT3 hl15 (by norm_num) (by positivity)
    nlinarith
  have hB : lostBound T Δ ≤ 2 / (n : ℝ) ^ 6 := by
    unfold lostBound
    calc _ ≤ Real.exp (Real.log 2 - 6 * Real.log n) := Real.exp_le_exp.2 (by linarith)
      _ = 2 / (n : ℝ) ^ 6 := by
          rw [Real.exp_sub, Real.exp_log (by norm_num),
            show (6 : ℝ) * Real.log n = Real.log ((n : ℝ) ^ 6) by rw [Real.log_pow]; norm_num,
            Real.exp_log (by positivity)]
  have : (T : ℝ) * Fintype.card V * lostBound T Δ ≤ T * Fintype.card V * (2 / (n : ℝ) ^ 6) :=
    mul_le_mul_of_nonneg_left hB (by positivity)
  have : (T : ℝ) * Fintype.card V * (2 / (n : ℝ) ^ 6) = 2 * T * Fintype.card V / (n : ℝ) ^ 6 := by
    ring
  linarith

end Prob

end Podc.WakeUpMatching
