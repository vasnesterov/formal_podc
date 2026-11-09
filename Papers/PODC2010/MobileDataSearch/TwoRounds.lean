import Papers.PODC2010.MobileDataSearch.Basic
import Papers.PODC2010.MobileDataSearch.Ineq

/-!
# Theorem 4: FRO is an `8/7`-approximation for two rounds

Bar-Noy, Cheilaris, Feng, Levin, *Finding mobile data under delay constraints with searching costs*,
PODC 2010, Section 5.1.

The paper reduces to `N = 3, 4` (Lemma 4, whose proof is flawed, see `Lemma4.lean`) and omits the
proofs for `N = 3, 4` (Lemmas 5, 6). We give a direct proof for every `N` (`bracket`): for the
first round `S` of any strategy let `k` be the largest index with `w(box 0..k-1) ≤ w(S)`; then
one of the two FRO candidates "first `k` boxes" and "first `k+1` boxes" is within `8/7` of `S`.
The real-variable core is `key_hom` (`Ineq.lean`).
-/

namespace Podc.MobileDataSearch

open Finset

variable {n : ℕ}

lemma sum_pref_zero (f : Fin n → ℝ) : ∑ i ∈ pref n 0, f i = 0 := by
  simp [pref]

lemma sum_pref_self (f : Fin n → ℝ) : ∑ i ∈ pref n n, f i = ∑ i, f i := by
  congr 1; ext i; simp [pref]

lemma pref_succ (k : ℕ) (hk : k < n) : pref n (k + 1) = insert ⟨k, hk⟩ (pref n k) := by
  ext i
  simp only [pref, mem_filter, mem_univ, true_and, mem_insert, Fin.ext_iff]
  omega

lemma sum_pref_succ (f : Fin n → ℝ) (k : ℕ) (hk : k < n) :
    ∑ i ∈ pref n (k + 1), f i = ∑ i ∈ pref n k, f i + f ⟨k, hk⟩ := by
  rw [pref_succ k hk, sum_insert (by simp [pref]), add_comm]

lemma sum_compl_eq (f : Fin n → ℝ) (S : Finset (Fin n)) :
    ∑ i ∈ Sᶜ, f i = ∑ i, f i - ∑ i ∈ S, f i := by
  rw [← sum_add_sum_compl S f]; ring

lemma gain_nonneg {p w : Fin n → ℝ} (hp : ∀ i, 0 ≤ p i) (hw : ∀ i, 0 ≤ w i)
    (S : Finset (Fin n)) : 0 ≤ gain p w S :=
  mul_nonneg (sum_nonneg fun i _ => hp i) (sum_nonneg fun i _ => hw i)

/-- The hypotheses of `key_hom`: the data of the prefix `Q` (cost `u`, probability `U`), the
critical box (cost `δ`, probability `Δ`) and the first round `S` (cost `b`, probability `a`). -/
def KeyHyp (P W u U δ Δ a b : ℝ) : Prop :=
  0 ≤ u ∧ 0 < δ ∧ u ≤ b ∧ b ≤ u + δ ∧ u + δ ≤ W ∧ 0 ≤ U ∧ 0 ≤ Δ ∧ U + Δ ≤ P ∧
    Δ * u ≤ U * δ ∧ (P - U - Δ) * δ ≤ Δ * (W - u - δ) ∧ a * δ ≤ U * δ + Δ * (b - u) ∧
    (a ≤ P - Δ ∨ δ ≤ b)

/-- **Bracketing lemma** (generic form). Let `S` be any first round and `k` the largest index with
`w(0..k-1) ≤ w(S)`. Any real inequality `α G(S) ≤ (α - β) P W + β max(G(Q_k), G(Q_{k+1}))`
valid under `KeyHyp` transfers to a prefix `Q` of the ratio order. -/
theorem bracket_gen {p w : Fin n → ℝ} (hp : ∀ i, 0 ≤ p i) (hw : ∀ i, 0 ≤ w i)
    (hs : RatioSorted p w) (S : Finset (Fin n)) (α β : ℝ) (hβ : 0 ≤ β) (hαβ : β ≤ α)
    (hkey : ∀ k (hk : k < n), 0 < ∑ i, p i → 0 < ∑ i, w i →
      KeyHyp (∑ i, p i) (∑ i, w i) (∑ i ∈ pref n k, w i) (∑ i ∈ pref n k, p i) (w ⟨k, hk⟩)
        (p ⟨k, hk⟩) (∑ i ∈ S, p i) (∑ i ∈ S, w i) →
      α * ((∑ i ∈ S, p i) * ((∑ i, w i) - ∑ i ∈ S, w i)) ≤
        (α - β) * ((∑ i, p i) * (∑ i, w i)) + β * max ((∑ i ∈ pref n k, p i) *
          ((∑ i, w i) - ∑ i ∈ pref n k, w i)) (((∑ i ∈ pref n k, p i) + p ⟨k, hk⟩) *
          ((∑ i, w i) - (∑ i ∈ pref n k, w i) - w ⟨k, hk⟩))) :
    ∃ k ≤ n, α * gain p w S ≤ (α - β) * ((∑ i, p i) * (∑ i, w i)) + β * gain p w (pref n k) := by
  set P := ∑ i, p i
  set W := ∑ i, w i
  set a := ∑ i ∈ S, p i
  set b := ∑ i ∈ S, w i
  have ha0 : 0 ≤ a := sum_nonneg fun i _ => hp i
  have haP : a ≤ P := sum_le_sum_of_subset_of_nonneg (subset_univ S) fun i _ _ => hp i
  have hbW : b ≤ W := sum_le_sum_of_subset_of_nonneg (subset_univ S) fun i _ _ => hw i
  have hgS : gain p w S = a * (W - b) := by rw [gain, sum_compl_eq]
  have hPW0 : 0 ≤ P * W :=
    mul_nonneg (sum_nonneg fun i _ => hp i) (sum_nonneg fun i _ => hw i)
  -- trivial case: the gain of `S` vanishes
  have triv : gain p w S ≤ 0 →
      ∃ k ≤ n, α * gain p w S ≤ (α - β) * (P * W) + β * gain p w (pref n k) := fun h => by
    have h0 : gain p w S = 0 := le_antisymm h (gain_nonneg hp hw S)
    refine ⟨0, Nat.zero_le _, ?_⟩
    rw [h0, mul_zero]
    exact add_nonneg (mul_nonneg (by linarith) hPW0) (mul_nonneg hβ (gain_nonneg hp hw _))
  rcases (sum_nonneg fun i _ => hp i : 0 ≤ P).eq_or_lt with hP0 | hP0
  · exact triv (by rw [hgS]; nlinarith)
  rcases (sum_nonneg fun i _ => hw i : 0 ≤ W).eq_or_lt with hW0 | hW0
  · have hW : W = 0 := hW0.symm
    have hb0 : 0 ≤ b := sum_nonneg fun i _ => hw i
    exact triv (by rw [hgS]; nlinarith)
  -- the bracketing index
  set Wk : ℕ → ℝ := fun k => ∑ i ∈ pref n k, w i
  set Pk : ℕ → ℝ := fun k => ∑ i ∈ pref n k, p i
  set k := Nat.findGreatest (fun k => Wk k ≤ b) n with hk_def
  have hk_le : k ≤ n := Nat.findGreatest_le n
  have hk_spec : Wk k ≤ b :=
    Nat.findGreatest_spec (P := fun k => Wk k ≤ b) (Nat.zero_le n)
      (by simp only [Wk, sum_pref_zero]; exact sum_nonneg fun i _ => hw i)
  rcases hk_le.eq_or_lt with hkn | hkn
  · -- `w(S) ≥ W`: the gain of `S` is `0`
    apply triv
    have : Wk k = W := by rw [hkn]; exact sum_pref_self w
    rw [hgS]; nlinarith
  have hk1 : ¬ Wk (k + 1) ≤ b := Nat.findGreatest_is_greatest (Nat.lt_succ_self k) hkn
  set j : Fin n := ⟨k, hkn⟩
  have hWk1 : Wk (k + 1) = Wk k + w j := sum_pref_succ w k hkn
  have hPk1 : Pk (k + 1) = Pk k + p j := sum_pref_succ p k hkn
  -- the "ratio defect" `t i = p i w_j - p_j w_i` is `≥ 0` before `j` and `≤ 0` after `j`
  set t : Fin n → ℝ := fun i => p i * w j - p j * w i
  have ht_before : ∀ i : Fin n, i.val ≤ k → 0 ≤ t i := fun i hi => by
    have := hs i j (Fin.le_def.2 hi); simp only [t]; linarith
  have ht_after : ∀ i : Fin n, k ≤ i.val → t i ≤ 0 := fun i hi => by
    have := hs j i (Fin.le_def.2 hi); simp only [t]; linarith
  have hsum_t : ∀ X : Finset (Fin n), ∑ i ∈ X, t i = (∑ i ∈ X, p i) * w j - p j * ∑ i ∈ X, w i :=
    fun X => by simp only [t, sum_sub_distrib, sum_mul, mul_sum]
  have hpre_t : 0 ≤ ∑ i ∈ pref n k, t i :=
    sum_nonneg fun i hi => ht_before i (by simp [pref] at hi; omega)
  have hrest_t : ∑ i ∈ (pref n (k + 1))ᶜ, t i ≤ 0 :=
    sum_nonpos fun i hi => ht_after i (by simp [pref] at hi; omega)
  have hS_t : ∑ i ∈ S, t i ≤ ∑ i ∈ pref n k, t i := by
    rw [← sum_filter_add_sum_filter_not S (fun i => i.val < k)]
    have h1 : ∑ i ∈ S.filter (fun i => ¬ i.val < k), t i ≤ 0 :=
      sum_nonpos fun i hi => ht_after i (by simp at hi; omega)
    have h2 : ∑ i ∈ S.filter (fun i => i.val < k), t i ≤ ∑ i ∈ pref n k, t i := by
      apply sum_le_sum_of_subset_of_nonneg
      · intro i hi; simp only [mem_filter] at hi; simp [pref, hi.2]
      · intro i hi _; exact ht_before i (by simp [pref] at hi; omega)
    linarith
  have hδ : 0 < w j := by
    have : b < Wk (k + 1) := lt_of_not_ge hk1
    linarith
  have hWk0 : 0 ≤ Wk k := sum_nonneg fun i _ => hw i
  have hPk0 : 0 ≤ Pk k := sum_nonneg fun i _ => hp i
  have hWk1W : Wk (k + 1) ≤ W :=
    sum_le_sum_of_subset_of_nonneg (subset_univ _) fun i _ _ => hw i
  have hPk1P : Pk (k + 1) ≤ P :=
    sum_le_sum_of_subset_of_nonneg (subset_univ _) fun i _ _ => hp i
  have hcompl_p : ∑ i ∈ (pref n (k + 1))ᶜ, p i = P - Pk (k + 1) := sum_compl_eq p _
  have hcompl_w : ∑ i ∈ (pref n (k + 1))ᶜ, w i = W - Wk (k + 1) := sum_compl_eq w _
  have key := hkey k hkn hP0 hW0 ⟨hWk0, hδ, hk_spec,
    (by have : b < Wk (k + 1) := lt_of_not_ge hk1; linarith), (by linarith), hPk0, hp j,
    (by linarith),
    (by have := hsum_t (pref n k); simp only [Wk, Pk] at *; linarith),
    (by
      have := hsum_t (pref n (k + 1))ᶜ
      rw [hcompl_p, hcompl_w] at this
      rw [hPk1] at this; rw [hWk1] at this
      nlinarith),
    (by
      have h1 := hsum_t S
      have h2 := hsum_t (pref n k)
      simp only [Wk, Pk] at *
      nlinarith),
    (by
      by_cases hjS : j ∈ S
      · right; exact single_le_sum (fun i _ => hw i) hjS
      · left
        have : a ≤ ∑ i ∈ univ.erase j, p i :=
          sum_le_sum_of_subset_of_nonneg (fun i hi => mem_erase.2 ⟨fun h => hjS (h ▸ hi),
            mem_univ _⟩) fun i _ _ => hp i
        rw [sum_erase_eq_sub (mem_univ j)] at this
        exact this)⟩
  have hg0 : gain p w (pref n k) = Pk k * (W - Wk k) := by rw [gain, sum_compl_eq]
  have hg1 : gain p w (pref n (k + 1)) = (Pk k + p j) * (W - Wk k - w j) := by
    rw [gain, sum_compl_eq]
    have e1 := hPk1; have e2 := hWk1
    simp only [Pk, Wk] at e1 e2
    rw [e1, e2]; ring
  rw [hgS]
  rcases le_total (Pk k * (W - Wk k)) ((Pk k + p j) * (W - Wk k - w j)) with hm | hm
  · refine ⟨k + 1, hkn, ?_⟩
    rw [hg1]; rw [max_eq_right hm] at key; exact key
  · refine ⟨k, hk_le, ?_⟩
    rw [hg0]; rw [max_eq_left hm] at key; exact key

/-- **Bracketing lemma** for Theorem 4: `7 · cost(Q) ≤ 8 · cost(S)` for some prefix `Q`. -/
theorem bracket {p w : Fin n → ℝ} (hp : ∀ i, 0 ≤ p i) (hw : ∀ i, 0 ≤ w i)
    (hs : RatioSorted p w) (S : Finset (Fin n)) :
    ∃ k ≤ n, 8 * gain p w S ≤ (8 - 7) * ((∑ i, p i) * (∑ i, w i)) + 7 * gain p w (pref n k) :=
  bracket_gen hp hw hs S 8 7 (by norm_num) (by norm_num) fun k _ hP hW h => by
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := h
    have := key_hom _ _ _ _ _ _ _ _ hP hW h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
    linarith

/-- **Theorem 4 of [paper]** (upper bound): for two rounds, Algorithm FRO is an
`8/7`-approximation. Boxes indexed in non-increasing order of `p i / w i` (any tie-breaking),
`p, w ≥ 0`; `A` any output of FRO, `B` any strategy. Holds for every number of boxes `N`. -/
theorem theorem4 {p w : Fin n → ℝ} (hp : ∀ i, 0 ≤ p i) (hw : ∀ i, 0 ≤ w i)
    (hs : RatioSorted p w) {A : Strategy n 2} (hA : IsFRO p w A) (B : Strategy n 2) :
    cost p w A ≤ 8 / 7 * cost p w B := by
  obtain ⟨k, -, hk⟩ := bracket hp hw hs (firstRound B)
  norm_num at hk
  have h1 := hA.2 (prefixStrategy k) (prefixStrategy_monotone k)
  rw [cost_two, cost_two, firstRound_prefixStrategy] at h1
  rw [cost_two p w B, cost_two p w A]
  linarith

/-! ### Typical tokens (Theorem 5) -/

private lemma typ_min (x1 b x2 : ℝ) (h1 : x1 ≤ b) (h2 : b ≤ x2) (h3 : x2 ≤ 1)
    (hc : x2 - x1 ≤ b) :
    b * (1 - b) ≤ max (x1 * (1 - x1)) (x2 * (1 - x2)) ∨
      (1 - b ^ 2) / 4 ≤ max (x1 * (1 - x1)) (x2 * (1 - x2)) := by
  rcases le_total (x1 + x2) 1 with hs | hs
  · rcases le_total (x2 + b) 1 with ht | ht
    · left; refine le_trans ?_ (le_max_right _ _)
      nlinarith [mul_nonneg (sub_nonneg.2 h2) (show 0 ≤ 1 - x2 - b by linarith)]
    · right; refine le_trans ?_ (le_max_right _ _)
      nlinarith [mul_nonneg (show 0 ≤ (1 + b) / 2 - x2 by linarith)
        (show 0 ≤ x2 + (1 + b) / 2 - 1 by linarith)]
  · right; refine le_trans ?_ (le_max_left _ _)
    nlinarith [mul_nonneg (show 0 ≤ x1 - (1 - b) / 2 by linarith)
      (show 0 ≤ 1 - x1 - (1 - b) / 2 by linarith)]

lemma two_le_sqrt_seven : 2 ≤ √7 := by
  rw [show (2 : ℝ) = √4 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
  exact Real.sqrt_le_sqrt (by norm_num)

private lemma typ_real2 (x1 b x2 : ℝ) (h1 : x1 ≤ b) (h2 : b ≤ x2) (h3 : x2 ≤ 1)
    (hc : x2 - x1 ≤ b) :
    (4 + √7) * (b * (1 - b)) ≤ (√7 - 2) + 6 * max (x1 * (1 - x1)) (x2 * (1 - x2)) := by
  have hs : √7 ^ 2 = 7 := Real.sq_sqrt (by norm_num)
  have hs2 := two_le_sqrt_seven
  rcases typ_min x1 b x2 h1 h2 h3 hc with hm | hm
  · nlinarith [sq_nonneg (2 * b - 1)]
  · nlinarith [mul_nonneg (show (0 : ℝ) ≤ 5 / 2 + √7 by linarith) (sq_nonneg (b - √7 + 2))]

/-- The real inequality behind Theorem 5 (typical token, normalised): the prefixes have
first-round probabilities `x₁ ≤ b ≤ x₂`, `b` the probability of `S`. -/
lemma typ_real (x1 b x2 : ℝ) (h0 : 0 ≤ x1) (h1 : x1 ≤ b) (h2 : b ≤ x2) (h3 : x2 ≤ 1)
    (hc : b + x2 - x1 ≤ 1 ∨ x2 - x1 ≤ b) :
    (4 + √7) * (b * (1 - b)) ≤ (√7 - 2) + 6 * max (x1 * (1 - x1)) (x2 * (1 - x2)) := by
  rcases hc with hc | hc
  · -- mirror `x ↦ 1 - x`
    have := typ_real2 (1 - x2) (1 - b) (1 - x1) (by linarith) (by linarith) (by linarith)
      (by linarith)
    rw [max_comm] at this
    have e1 : (1 - b) * (1 - (1 - b)) = b * (1 - b) := by ring
    have e2 : (1 - x1) * (1 - (1 - x1)) = x1 * (1 - x1) := by ring
    have e3 : (1 - x2) * (1 - (1 - x2)) = x2 * (1 - x2) := by ring
    rwa [e1, e2, e3] at this
  · exact typ_real2 x1 b x2 h1 h2 h3 hc

/-- Homogeneous form of `typ_real` in the notation of `KeyHyp` (`p = w`). -/
lemma typ_hom (W u δ b : ℝ) (hW : 0 < W) (h : KeyHyp W W u u δ δ b b) :
    (4 + √7) * (b * (W - b)) ≤ (4 + √7 - 6) * (W * W) +
      6 * max (u * (W - u)) ((u + δ) * (W - u - δ)) := by
  obtain ⟨h1, h2, h3, h4, h5, -, -, -, -, -, -, h12⟩ := h
  have key := typ_real (u / W) (b / W) ((u + δ) / W) (div_nonneg h1 hW.le)
    (div_le_div_of_nonneg_right h3 hW.le) (div_le_div_of_nonneg_right h4 hW.le)
    (by rw [div_le_one hW]; exact h5)
    (by
      rcases h12 with h | h
      · left; rw [← add_div, div_sub_div_same, div_le_one hW]; linarith
      · right; rw [div_sub_div_same]; exact div_le_div_of_nonneg_right (by linarith) hW.le)
  have hW2 : 0 < W * W := mul_pos hW hW
  have e1 : b / W * (1 - b / W) = b * (W - b) / (W * W) := by field_simp
  have e2 : u / W * (1 - u / W) = u * (W - u) / (W * W) := by field_simp
  have e3 : (u + δ) / W * (1 - (u + δ) / W) = (u + δ) * (W - u - δ) / (W * W) := by
    field_simp; ring
  rw [e1, e2, e3, max_div_div_right hW2.le] at key
  have h := mul_le_mul_of_nonneg_left key hW2.le
  have h8 : W * W * ((4 + √7) * (b * (W - b) / (W * W))) = (4 + √7) * (b * (W - b)) := by
    field_simp
  have h7 : W * W * (√7 - 2 + 6 * (max (u * (W - u)) ((u + δ) * (W - u - δ)) / (W * W))) =
      (√7 - 2) * (W * W) + 6 * max (u * (W - u)) ((u + δ) * (W - u - δ)) := by
    field_simp
  rw [h8, h7] at h
  linarith

/-- **Theorem 5 of [paper]** (upper bound): for a typical token (`p = w`), two rounds and *any*
order of the boxes (all orders are ratio orders), FRO is a `(4 + √7)/6`-approximation;
`(4 + √7)/6 = (7 - 2√7)/(28 - 10√7) ≈ 1.108`. -/
theorem theorem5 {p : Fin n → ℝ} (hp : ∀ i, 0 ≤ p i) {A : Strategy n 2} (hA : IsFRO p p A)
    (B : Strategy n 2) : cost p p A ≤ (4 + √7) / 6 * cost p p B := by
  have hs : RatioSorted p p := fun i j _ => by rw [mul_comm]
  obtain ⟨k, -, hk⟩ := bracket_gen hp hp hs (firstRound B) (4 + √7) 6 (by norm_num)
    (by linarith [two_le_sqrt_seven]) fun k _ _ hW h => typ_hom _ _ _ _ hW h
  have h1 := hA.2 (prefixStrategy k) (prefixStrategy_monotone k)
  rw [cost_two, cost_two, firstRound_prefixStrategy] at h1
  rw [cost_two p p B, cost_two p p A]
  nlinarith

end Podc.MobileDataSearch
