import Papers.PODC2017.NoisyRadioBroadcast.Prob
import Mathlib.LinearAlgebra.Lagrange

/-!
# Lemma 16: the coding throughput of the star with receiver faults is `Θ(1)`
-/

namespace Podc.NoisyRadioBroadcast

open Finset Filter
open scoped ENNReal

section ReedSolomon

variable {A : Type*} [Field A]

/-- The Reed–Solomon polynomial `∑ i, m i X^i` with coefficients `m`. -/
noncomputable def starCoding_poly {k : ℕ} (m : Fin k → A) : Polynomial A :=
  ∑ i : Fin k, Polynomial.C (m i) * Polynomial.X ^ (i : ℕ)

theorem starCoding_poly_coeff {k : ℕ} (m : Fin k → A) (i : Fin k) :
    (starCoding_poly m).coeff i = m i := by
  simp [starCoding_poly, Fin.val_inj]

/-- Reed–Solomon decoding: from the received evaluations `e j` (at the points `α j`; `none` =
erasure), interpolate the polynomial through the received points and read off its coefficients. -/
noncomputable def starCoding_decode {L k : ℕ} (α : Fin L → A) (e : Fin L → Option A) :
    Fin k → A := fun i =>
  (Lagrange.interpolate (univ.filter fun j => (e j).isSome) α (fun j => (e j).getD 0)).coeff i

/-- **Reed–Solomon erasure decoding**: if every received value is the evaluation of the polynomial
of `m` at distinct points and at least `k` values are received, decoding returns `m`. -/
theorem starCoding_decode_eq {L k : ℕ} {α : Fin L → A} (hα : Function.Injective α)
    (m : Fin k → A) {e : Fin L → Option A}
    (he : ∀ j x, e j = some x → x = (starCoding_poly m).eval (α j))
    (hk : k ≤ #(univ.filter fun j => (e j).isSome)) : starCoding_decode α e = m := by
  funext i
  unfold starCoding_decode
  rw [← Lagrange.eq_interpolate_of_eval_eq _ hα.injOn]
  · exact starCoding_poly_coeff m i
  · exact (Polynomial.degree_sum_fin_lt m).trans_le (by exact_mod_cast hk)
  · intro j hj
    simp only [mem_filter, mem_univ, true_and] at hj
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 hj
    rw [hx, ← he j x hx]
    rfl

end ReedSolomon

section Star

variable {X : Type*} {n : ℕ}

/-- On the star, if only the source broadcasts (`b`), a leaf receives `b` iff its coin is clean. -/
theorem starCoding_heard_leaf (b : Option X) (c : Option (Fin n) → Bool) (u : Fin n) :
    heard (star n) .receiver (fun v => if v = none then b else none) c (some u) =
      if c (some u) then b else none := by
  have hH : ∀ x, b = some x → Hears (star n) (fun v => if v = none then b else none) (some u) none :=
    fun x hx => ⟨by simp, by simp [star], by simp [hx], fun w' hw' _ => by
      simp [star] at hw'; exact hw'⟩
  rcases hb : heard (star n) .receiver (fun v => if v = none then b else none) c (some u)
    with _ | x
  · cases hc : c (some u)
    · rfl
    · cases b with
      | none => rfl
      | some x =>
        have := (heard_eq_some_iff (star n) (f := .receiver) (c := c) (x := x)).2
          ⟨none, hH x rfl, by simp [faultCoin, hc], by simp⟩
        rw [hb] at this
        cases this
  · obtain ⟨w, hw, hc, hx⟩ := (heard_eq_some_iff (star n)).1 hb
    have hw0 : w = none := by
      have := hw.2.1
      simp [star] at this
      exact this
    subst hw0
    simp only [faultCoin] at hc
    simp only [ite_true] at hx
    simp [hc, hx]

variable {A : Type*} [Field A]

/-- The Reed–Solomon schedule on the star: in round `r < L` the source broadcasts the evaluation
of the polynomial of the messages at `α r`; the leaves stay silent and decode by interpolation. -/
noncomputable def starCoding_sched (n : ℕ) {L k : ℕ} (α : Fin L → A) :
    CodingSchedule (Option (Fin n)) A k where
  act r _ inp _ := if h : r < L then inp.map fun m => (starCoding_poly m).eval (α ⟨r, h⟩) else none
  dec _ h := starCoding_decode α fun j => h[(j : ℕ)]?.join

theorem starCoding_hist {L k : ℕ} (α : Fin L → A) (m : Fin k → A)
    (ω : ℕ → Option (Fin n) → Bool) (r : ℕ) (u : Fin n) :
    codingHist (star n) none .receiver (starCoding_sched n α) m ω r (some u) =
      (List.range r).map fun j => if ω j (some u) then
        (if h : j < L then some ((starCoding_poly m).eval (α ⟨j, h⟩)) else none) else none := by
  induction r with
  | zero => rfl
  | succ r ih =>
    simp only [codingHist]
    rw [ih, List.range_succ, List.map_append]
    congr 1
    simp only [List.map_cons, List.map_nil]
    rw [← starCoding_heard_leaf]
    congr 1
    refine congrArg (fun a => heard (star n) .receiver a (ω r) (some u)) (funext fun v => ?_)
    cases v <;> simp [starCoding_sched]

end Star

section Numeric

theorem starCoding_numeric {q : ℝ} (hq1 : q ≤ 1) {n k L : ℕ} (hk : 1 ≤ k)
    (hL : 4 * (k : ℝ) + 2 * n ≤ q * L) :
    (n : ℝ) * (((1 / 2 : ℝ) ^ (k - 1))⁻¹ * (1 - (1 - 1 / 2) * q) ^ L) ≤ 1 / k := by
  have h1 : (1 - (1 - 1 / 2) * q) ^ L ≤ Real.exp (-(q * L) / 2) := by
    calc (1 - (1 - 1 / 2) * q) ^ L ≤ Real.exp (-q / 2) ^ L :=
          pow_le_pow_left₀ (by linarith) (by have := Real.add_one_le_exp (-q / 2); linarith) L
      _ = Real.exp (-(q * L) / 2) := by rw [← Real.exp_nat_mul]; ring_nf
  have h2 : Real.exp (-(q * L) / 2) ≤ Real.exp (-(2 * k + n)) := Real.exp_le_exp.2 (by linarith)
  have h3 : ((1 / 2 : ℝ) ^ (k - 1))⁻¹ ≤ Real.exp k := by
    rw [one_div, inv_pow, inv_inv]
    calc (2 : ℝ) ^ (k - 1) ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) (Nat.sub_le _ _)
      _ ≤ Real.exp 1 ^ k :=
          pow_le_pow_left₀ (by norm_num) (by have := Real.add_one_le_exp 1; linarith) k
      _ = Real.exp k := by rw [← Real.exp_nat_mul, mul_one]
  have hn : (n : ℝ) ≤ Real.exp n := by have := Real.add_one_le_exp (n : ℝ); linarith
  have hk' : (k : ℝ) ≤ Real.exp k := by have := Real.add_one_le_exp (k : ℝ); linarith
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  calc (n : ℝ) * (((1 / 2 : ℝ) ^ (k - 1))⁻¹ * (1 - (1 - 1 / 2) * q) ^ L)
      ≤ Real.exp n * (Real.exp k * Real.exp (-(2 * k + n))) :=
        mul_le_mul hn (mul_le_mul h3 (h1.trans h2) (pow_nonneg (by linarith) _)
          (Real.exp_pos _).le)
          (mul_nonneg (by positivity) (pow_nonneg (by linarith) _)) (Real.exp_pos _).le
    _ = 1 / Real.exp k := by
        rw [← Real.exp_add, ← Real.exp_add, one_div, ← Real.exp_neg]; ring_nf
    _ ≤ 1 / k := one_div_le_one_div_of_le hk0 hk'

end Numeric

/-- The Reed–Solomon schedule with `L ≥ (4k + 2n)/(1 - p)` rounds succeeds on the star with
receiver faults. -/
theorem starCoding_succeeds {A : Type*} [Field A] {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p < 1)
    {n k L : ℕ} (hk : 1 ≤ k) {α : Fin L → A} (hα : Function.Injective α)
    (hL : 4 * (k : ℝ) + 2 * n ≤ (1 - p) * L) :
    CodingSucceeds (star n) none .receiver p k (starCoding_sched n α) L := by
  classical
  intro m
  set T : Fin n → Finset (Fin L × Option (Fin n)) := fun u => univ ×ˢ {some u} with hT
  have hcard : ∀ (ω : ℕ → Option (Fin n) → Bool) u,
      #((T u).filter fun x => ω x.1 x.2 = true) =
        #(univ.filter fun j : Fin L => ω j (some u) = true) := by
    intro ω u
    refine card_nbij' (fun x => x.1) (fun j => (j, some u)) ?_ ?_ ?_ ?_
    · rintro ⟨a, b⟩ hx
      simp only [hT, coe_filter, mem_product, mem_univ, mem_singleton, true_and,
        Set.mem_ofPred_eq] at hx ⊢
      rw [← hx.1]; exact hx.2
    · intro j hj
      simp_all
    · rintro ⟨a, b⟩ hx
      simp only [hT, coe_filter, mem_product, mem_univ, mem_singleton, true_and,
        Set.mem_ofPred_eq] at hx ⊢
      rw [hx.1]
    · intro j hj
      simp
  have hgood : ∀ ω : ℕ → Option (Fin n) → Bool,
      (¬ ∃ u ∈ univ, #((T u).filter fun x => ω x.1 x.2 = true) ≤ k - 1) →
        CodingDecodes (star n) none .receiver (starCoding_sched n α) m ω L := by
    intro ω hω v hv
    obtain ⟨u, rfl⟩ := Option.ne_none_iff_exists'.1 hv
    push Not at hω
    have hu := hω u (mem_univ _)
    rw [hcard] at hu
    show starCoding_decode α (fun j : Fin L => (codingHist (star n) none .receiver
      (starCoding_sched n α) m ω L (some u))[(j : ℕ)]?.join) = m
    rw [starCoding_hist]
    apply starCoding_decode_eq hα m
    · intro j x hx
      simp [j.isLt] at hx
      exact hx.2.symm
    · refine (by omega : k ≤ #(univ.filter fun j : Fin L => ω j (some u) = true)).trans_eq ?_
      congr 1
      ext j
      simp
  have hbad : ∀ u, prob p L (fun ω => #((T u).filter fun x => ω x.1 x.2 = true) ≤ k - 1) ≤
      ((1 / 2 : ℝ) ^ (k - 1))⁻¹ * (1 - (1 - 1 / 2) * (1 - p)) ^ L := by
    intro u
    have := prob_card_le_le hp0 hp1.le (T u) (k - 1) (l := 1 / 2) (by norm_num) (by norm_num)
    have hT' : #(T u) = L := by simp [hT]
    rwa [hT'] at this
  have hnum := starCoding_numeric (q := 1 - p) (by linarith) hk hL
  calc 1 - 1 / (k : ℝ)
      ≤ 1 - n * (((1 / 2 : ℝ) ^ (k - 1))⁻¹ * (1 - (1 - 1 / 2) * (1 - p)) ^ L) := by linarith
    _ = 1 - ∑ _u : Fin n, ((1 / 2 : ℝ) ^ (k - 1))⁻¹ * (1 - (1 - 1 / 2) * (1 - p)) ^ L := by
        simp
    _ ≤ 1 - ∑ u : Fin n, prob p L (fun ω => #((T u).filter fun x => ω x.1 x.2 = true) ≤ k - 1) :=
        sub_le_sub_left (sum_le_sum fun u _ => hbad u) _
    _ ≤ 1 - prob p L (fun ω => ∃ u ∈ univ, #((T u).filter fun x => ω x.1 x.2 = true) ≤ k - 1) :=
        sub_le_sub_left (prob_exists_le hp0 hp1.le _ _) _
    _ = prob p L (fun ω => ¬ ∃ u ∈ univ, #((T u).filter fun x => ω x.1 x.2 = true) ≤ k - 1) :=
        (prob_not _ _ _).symm
    _ ≤ _ := prob_mono hp0 hp1.le hgood

section Lower

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (s : V) (f : FaultModel)
  {A : Type*} {k : ℕ}

theorem starCoding_hist_length (sch : CodingSchedule V A k) (m : Fin k → A)
    (ω : ℕ → V → Bool) (r : ℕ) (u : V) : (codingHist G s f sch m ω r u).length = r := by
  induction r generalizing u with
  | zero => rfl
  | succ r ih => simp [codingHist, ih]

/-- Information-theoretic bound: for a fixed coin outcome, a node decodes correctly at most
`(|A| + 1)^R` message vectors (its history is a list of `R` entries in `Option A`). -/
theorem starCoding_card_decoded_le [Fintype A] [DecidableEq A] (sch : CodingSchedule V A k)
    (ω : ℕ → V → Bool) (R : ℕ) (u : V) :
    #(univ.filter fun m : Fin k → A => sch.dec u (codingHist G s f sch m ω R u) = m) ≤
      (Fintype.card A + 1) ^ R := by
  have := card_le_card_of_injOn
    (s := univ.filter fun m : Fin k → A => sch.dec u (codingHist G s f sch m ω R u) = m)
    (t := (univ : Finset (List.Vector (Option A) R)))
    (fun m => ⟨codingHist G s f sch m ω R u, starCoding_hist_length G s f sch m ω R u⟩)
    (fun _ _ => mem_coe.2 (mem_univ _)) ?_
  · simpa [card_vector] using this
  · intro m₁ h₁ m₂ h₂ h
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at h₁ h₂
    have h' : codingHist G s f sch m₁ ω R u = codingHist G s f sch m₂ ω R u :=
      congrArg Subtype.val h
    rw [← h₁, ← h₂, h']

/-- A coding schedule over an alphabet with at least `4` letters that succeeds within `R` rounds
for `k ≥ 2` messages (in any network with a node other than the source) needs `2R ≥ k`. -/
theorem starCoding_rounds_ge [Fintype A] [DecidableEq A] {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hA : 4 ≤ Fintype.card A) (hk : 2 ≤ k) {u : V} (hu : u ≠ s) {sch : CodingSchedule V A k}
    {R : ℕ} (h : CodingSucceeds G s f p k sch R) : k ≤ 2 * R := by
  classical
  set c := Fintype.card A with hc
  have key : (c : ℝ) ^ k * (1 - 1 / k) ≤ ((c : ℝ) + 1) ^ R := by
    calc (c : ℝ) ^ k * (1 - 1 / k) = ∑ _m : Fin k → A, (1 - 1 / (k : ℝ)) := by
          simp [hc]; ring
      _ ≤ ∑ m : Fin k → A, prob p R (fun ω => sch.dec u (codingHist G s f sch m ω R u) = m) :=
        sum_le_sum fun m _ => (h m).trans (prob_mono hp0 hp1 fun ω hω => hω u hu)
      _ = ∑ y : Fin R → V → Bool, (∏ r, Cslib.Probability.coinProb (1 - p) (y r)) *
            (#(univ.filter fun m : Fin k → A =>
              sch.dec u (codingHist G s f sch m (extendCoins y) R u) = m) : ℝ) := by
        unfold prob
        rw [sum_comm]
        refine sum_congr rfl fun y _ => ?_
        rw [← mul_sum]
        congr 1
        convert (natCast_card_filter (R := ℝ) _ _).symm
      _ ≤ ∑ y : Fin R → V → Bool, (∏ r, Cslib.Probability.coinProb (1 - p) (y r)) *
            ((c : ℝ) + 1) ^ R := by
        refine sum_le_sum fun y _ => mul_le_mul_of_nonneg_left ?_ (weight_nonneg hp0 hp1 y)
        exact_mod_cast starCoding_card_decoded_le G s f sch _ R u
      _ = ((c : ℝ) + 1) ^ R := by rw [← sum_mul, sum_weight, one_mul]
  have hc4 : (4 : ℝ) ≤ c := by exact_mod_cast hA
  have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have h1 : (c : ℝ) ^ (k - 1) < (c : ℝ) ^ (2 * R) := by
    calc (c : ℝ) ^ (k - 1) < (c : ℝ) ^ (k - 1) * (c * (1 - 1 / k)) := by
          refine lt_mul_of_one_lt_right (by positivity) ?_
          have : (1 : ℝ) / k ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hk2
          nlinarith
      _ = (c : ℝ) ^ k * (1 - 1 / k) := by
          rw [← mul_assoc, ← pow_succ, Nat.sub_add_cancel (by omega)]
      _ ≤ ((c : ℝ) + 1) ^ R := key
      _ ≤ ((c : ℝ) ^ 2) ^ R := pow_le_pow_left₀ (by positivity) (by nlinarith) R
      _ = (c : ℝ) ^ (2 * R) := by rw [← pow_mul]
  have := (pow_lt_pow_iff_right₀ (by linarith : (1 : ℝ) < c)).1 h1
  omega

end Lower

/-- **Lemma 16** of the paper (coding throughput of the star topology with receiver faults is
`Θ(1)`), for messages and packets drawn from finite fields `F k` with at least `k²` elements. -/
theorem lemma16 {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p < 1) {n : ℕ} (hn : 1 ≤ n)
    (F : ℕ → Type) [∀ k, Field (F k)] [∀ k, Fintype (F k)] [∀ k, DecidableEq (F k)]
    (hF : ∀ k, k ^ 2 ≤ Fintype.card (F k)) :
    ENNReal.ofReal ((1 - p) / 8) ≤ codingThroughput (star n) none .receiver p F ∧
      codingThroughput (star n) none .receiver p F ≤ 2 := by
  classical
  have hq0 : 0 < 1 - p := by linarith
  constructor
  · -- lower bound: the Reed–Solomon schedule with `⌈(4k + 2n)/(1-p)⌉` rounds
    refine le_limsup_of_frequently_le (Eventually.frequently ?_)
    rw [eventually_atTop]
    refine ⟨max n (⌈8 / (1 - p)⌉₊ + 1), fun k hk => ?_⟩
    have hkn : n ≤ k := le_of_max_le_left hk
    have hk' : ⌈8 / (1 - p)⌉₊ + 1 ≤ k := le_of_max_le_right hk
    have hk1 : 1 ≤ k := by omega
    have hk8 : 8 / (1 - p) ≤ k :=
      (Nat.le_ceil _).trans (by exact_mod_cast (Nat.le_succ _).trans hk')
    have hkq : 8 ≤ (k : ℝ) * (1 - p) := (div_le_iff₀ hq0).1 hk8
    have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk1
    have hnR : (n : ℝ) ≤ k := by exact_mod_cast hkn
    set L := ⌈(4 * (k : ℝ) + 2 * n) / (1 - p)⌉₊ with hLdef
    have hL1 : 4 * (k : ℝ) + 2 * n ≤ L * (1 - p) := (div_le_iff₀ hq0).1 (Nat.le_ceil _)
    have hL2 : (L : ℝ) * (1 - p) < 4 * k + 2 * n + (1 - p) := by
      have := mul_lt_mul_of_pos_right (Nat.ceil_lt_add_one (by positivity) :
        (L : ℝ) < (4 * (k : ℝ) + 2 * n) / (1 - p) + 1) hq0
      rwa [add_mul, div_mul_cancel₀ _ hq0.ne', one_mul] at this
    have hL3 : (L : ℝ) * (1 - p) ≤ 8 * k := by linarith
    have hLk : (L : ℝ) ≤ (k : ℝ) ^ 2 :=
      le_of_mul_le_mul_right (by nlinarith) hq0
    have hLc : L ≤ Fintype.card (F k) := (by exact_mod_cast hLk : L ≤ k ^ 2).trans (hF k)
    have hLpos : (0 : ℝ) < L := by
      by_contra h
      have : (L : ℝ) = 0 := le_antisymm (not_lt.1 h) (Nat.cast_nonneg _)
      rw [this] at hL1
      linarith
    let α : Fin L → F k := fun r => (Fintype.equivFin (F k)).symm (Fin.castLE hLc r)
    have hα : Function.Injective α :=
      (Fintype.equivFin (F k)).symm.injective.comp (Fin.castLE_injective hLc)
    have hsucc := starCoding_succeeds (n := n) hp0 hp1 hk1 hα (by linarith)
    have hR : codingRounds (star n) none .receiver p (F k) k ≤ (L : ℕ∞) :=
      iInf₂_le L ⟨_, hsucc⟩
    calc ENNReal.ofReal ((1 - p) / 8) ≤ (k : ℝ≥0∞) / (L : ℝ≥0∞) := by
          rw [show (k : ℝ≥0∞) = ENNReal.ofReal k by simp,
            show (L : ℝ≥0∞) = ENNReal.ofReal L by simp, ← ENNReal.ofReal_div_of_pos hLpos]
          exact ENNReal.ofReal_le_ofReal (by rw [le_div_iff₀ hLpos]; linarith)
      _ ≤ _ := by
          refine ENNReal.div_le_div_left ?_ _
          have := ENat.toENNReal_le.2 hR
          simpa using this
  · -- upper bound: information theoretic
    refine limsup_le_of_le (h := ?_)
    rw [eventually_atTop]
    refine ⟨2, fun k hk => ?_⟩
    have hA : 4 ≤ Fintype.card (F k) := (by nlinarith : 4 ≤ k ^ 2).trans (hF k)
    have hge : (((k + 1) / 2 : ℕ) : ℕ∞) ≤ codingRounds (star n) none .receiver p (F k) k := by
      refine le_iInf₂ fun R hR => ?_
      obtain ⟨sch, h⟩ := hR
      have := starCoding_rounds_ge (star n) none .receiver hp0 hp1.le hA hk
        (u := some ⟨0, hn⟩) (by simp) h
      exact_mod_cast (by omega : (k + 1) / 2 ≤ R)
    apply ENNReal.div_le_of_le_mul
    calc (k : ℝ≥0∞) ≤ 2 * (((k + 1) / 2 : ℕ) : ℝ≥0∞) := by
          exact_mod_cast (by omega : k ≤ 2 * ((k + 1) / 2))
      _ ≤ 2 * (codingRounds (star n) none .receiver p (F k) k : ℝ≥0∞) := by
          gcongr
          have := ENat.toENNReal_le.2 hge
          simpa using this

end Podc.NoisyRadioBroadcast
