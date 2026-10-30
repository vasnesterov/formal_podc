import Papers.PODC2026.MultiKrumRobustness.Config

/-!
# Lower bounds on `κ⋆` (Proposition 1, Theorems 3 and 4, Proposition B.1)

All constructions are one-dimensional, `x i = c i • e` for a unit vector `e` of an arbitrary
nontrivial real inner product space `E` (the paper uses `ℝ^d` and `e = e₁`). The MultiKrum lower
bounds hold for *every* tie-breaking (`IsMultiKrum`), because in each construction the relevant
groups of indices have strictly separated scores, so every valid selection is determined
(`IsSelection.subset_of_score_lt`, `IsSelection.superset_of_score_lt`).

* `prop_1` — **Proposition 1**: for `2 ≤ n`, `2f ≤ n`, if `κ⋆(F) < ∞` then `2f < n` and
  `κ⋆(F) ≥ f/(n-2f)` (cases `kappaStar_eq_top_of_n_eq_two_mul`, `zero_le_kappaStar`,
  `prop_1_aux`).
* `theorem_3_even`, `theorem_3_odd` — **Theorem 3** (Krum), via `krum_lowerBound_aux`.
* `prop_B1_corrected` — **Proposition B.1** with the corrected bound
  `R'(n,f,m) = (n-f)²/(f(n-2f)) · (f/(n-f) + (m-a)/m)²`, `a = min(m, n-2f)`;
  `prop_B1` — the paper's (weaker, still true) bound `R(n,f,m)`; `boundB1_lt_corrected`,
  `prop_B1_paper_lt_theorem_4` — the paper's `R` is strictly smaller for `m > n - 2f`, so it does
  not recover Theorem 4.
* `theorem_4` — **Theorem 4**: `κ⋆_{n-f} ≥ 4f/(n-2f)` for `n > 3f`, `n ≥ 2`.
* `kappaStar_eq_bot_of_n_eq_one` — for `n = 1` (`f = 0`) Krum has `κ⋆ = -∞`, so Proposition 1,
  Theorem 3 (odd case) and Theorem 4 need `n ≥ 2`.
-/

open Finset Filter Topology

namespace Podc.MultiKrumRobustness

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}

/-! ### Two-valued configurations: `p` copies of `e`, then `n - p` copies of `0` -/

/-- Coefficients of the two-valued configuration: `1` on the first `p` indices, `0` after. -/
noncomputable def twoVal (p : ℕ) (i : Fin n) : ℝ := if i.val < p then 1 else 0

lemma sum_twoVal {p lo hi : ℕ} (h1 : lo ≤ p) (h2 : p ≤ hi) (h3 : hi ≤ n) (g : ℝ → ℝ) :
    ∑ i ∈ block n lo hi, g (twoVal p i) = ((p - lo : ℕ) : ℝ) * g 1 + ((hi - p : ℕ) : ℝ) * g 0 := by
  rw [sum_block_split h1 h2, sum_block_const (h2.trans h3) (v := g 1),
    sum_block_const h3 (v := g 0)]
  all_goals intro i ha hb; simp only [twoVal]; split_ifs <;> first | rfl | (exfalso; omega)

lemma sum_twoVal_id {p N : ℕ} (hpN : p ≤ N) (hN : N ≤ n) :
    ∑ i ∈ block n 0 N, twoVal p i = p := by
  have := sum_twoVal (Nat.zero_le p) hpN hN (fun t => t)
  simpa using this

lemma mean_twoVal {e : E} {p N : ℕ} (hpN : p ≤ N) (hN : N ≤ n) :
    mean (fun i => twoVal p i • e) (block n 0 N) = ((p : ℝ) / N) • e := by
  rw [mean_line, card_block hN, sum_twoVal_id hpN hN]
  simp [div_eq_inv_mul]

lemma variance_twoVal {e : E} (he : ‖e‖ = 1) {p N : ℕ} (hpN : p ≤ N) (hN : N ≤ n) (hN0 : 0 < N) :
    variance (fun i => twoVal p i • e) (block n 0 N) = p * (N - p) / N ^ 2 := by
  rw [variance_line he, card_block hN, Nat.sub_zero, sum_twoVal_id hpN hN,
    sum_twoVal (Nat.zero_le p) hpN hN (fun t => (t - (N : ℝ)⁻¹ * p) ^ 2)]
  have : (N : ℝ) ≠ 0 := by positivity
  push_cast [Nat.cast_sub hpN, Nat.sub_zero]
  field_simp
  ring

/-- The Krum construction of Theorem 3, for a general number `p` of copies of `e`: with `p`
copies of `e` followed by `n - p` copies of `0` (`f ≤ p`, `2p < n`), every Krum selection is a
zero vector, while the reference set `S = {1, …, n - f}` has mean `p/(n-f) e` and variance
`p (n - f - p)/(n - f)²`. Hence `κ⋆₁ ≥ p / (n - f - p)`. -/
theorem krum_lowerBound_aux [Nontrivial E] {f p : ℕ} (hp : 1 ≤ p) (hfp : f ≤ p) (h2p : 2 * p < n)
    {F : (Fin n → E) → E} (hF : IsMultiKrum f 1 F) :
    (((p : ℝ) / ((n : ℝ) - f - p) : ℝ) : EReal) ≤ kappaStar f F := by
  obtain ⟨e, he⟩ := exists_unit E
  set x : Fin n → E := fun i => twoVal p i • e with hx
  have hfn : f ≤ n := by omega
  have hN : ((n - f : ℕ) : ℝ) = n - f := by push_cast [Nat.cast_sub hfn]; ring
  have hNpos : (0 : ℝ) < n - f := by
    have : (f : ℝ) + 1 ≤ n := by exact_mod_cast (show f + 1 ≤ n by omega)
    linarith
  have hpn : (2 * p : ℝ) < n := by exact_mod_cast h2p
  have hfp' : (f : ℝ) ≤ p := by exact_mod_cast hfp
  -- the score of `0` is at most `(p - f)/(n - f)`
  have hs0 : score f x ((0 : ℝ) • e) ≤ ((n - f : ℕ) : ℝ)⁻¹ * (p - f) := by
    unfold score
    gcongr
    calc nearestSum x (n - f) ((0 : ℝ) • e)
        ≤ ∑ j ∈ block n f n, (0 - twoVal p j) ^ 2 :=
          nearestSum_line_le he _ _ (by rw [card_block le_rfl])
      _ = p - f := by
          rw [sum_twoVal hfp (by omega) le_rfl (fun t => (0 - t) ^ 2)]
          push_cast [Nat.cast_sub hfp]; ring
  -- the score of `e` is at least `(n - f - p)/(n - f)`
  have hs1 : ((n - f : ℕ) : ℝ)⁻¹ * (((n - f : ℕ) : ℝ) - p) ≤ score f x ((1 : ℝ) • e) := by
    unfold score
    gcongr
    have hsub : (univ.filter fun j => (1 - twoVal p j) ^ 2 < 1) ⊆ block n 0 p := by
      intro j hj
      rw [mem_filter_univ] at hj
      simp only [twoVal] at hj
      simp only [mem_block, Nat.zero_le, true_and]
      by_contra h
      simp [h] at hj
    have := le_nearestSum_line he (twoVal p) (k := n - f) (r := p) (Nat.sub_le n f) 1 zero_le_one
      ((card_le_card hsub).trans (by rw [card_block (by omega)]; simp))
    simpa using this
  have hlt : ∀ i ∈ block n p n, ∀ j ∉ block n p n, score f x (x i) < score f x (x j) := by
    intro i hi j hj
    simp only [mem_block, not_and, not_lt] at hi hj
    have hi' : ¬ i.val < p := not_lt.2 hi.1
    have hj' : j.val < p := by
      by_contra h
      have := hj (not_lt.1 h)
      omega
    have hxi : x i = (0 : ℝ) • e := by simp [hx, twoVal, hi']
    have hxj : x j = (1 : ℝ) • e := by simp [hx, twoVal, hj']
    rw [hxi, hxj]
    refine lt_of_le_of_lt hs0 (lt_of_lt_of_le ?_ hs1)
    rw [hN]
    exact mul_lt_mul_of_pos_left (by linarith) (inv_pos.2 hNpos)
  obtain ⟨S, hS, hFS⟩ := hF x
  have hsub := hS.subset_of_score_lt hlt (by rw [card_block le_rfl]; omega)
  obtain ⟨i, rfl⟩ := card_eq_one.1 hS.1
  have hi : i ∈ block n p n := hsub (mem_singleton_self i)
  have hFx : F x = 0 := by
    rw [hFS, mean_eq_of_const (singleton_nonempty i) (v := x i) (fun j hj => by
      rw [mem_singleton.1 hj])]
    simp only [mem_block] at hi
    simp [hx, twoVal, not_lt.2 hi.1]
  -- the reference set `S = {1, …, n - f}`
  have hcard : (block n 0 (n - f)).card = n - f := by rw [card_block (Nat.sub_le _ _)]; simp
  have hpN : p ≤ n - f := by omega
  have hmean : mean x (block n 0 (n - f)) = ((p : ℝ) / ((n - f : ℕ) : ℝ)) • e :=
    mean_twoVal hpN (Nat.sub_le _ _)
  have hvar : variance x (block n 0 (n - f)) = p * (((n - f : ℕ) : ℝ) - p) / ((n - f : ℕ) : ℝ) ^ 2 :=
    variance_twoVal he hpN (Nat.sub_le _ _) (by omega)
  have hvpos : 0 < variance x (block n 0 (n - f)) := by
    rw [hvar, hN]
    have : (1 : ℝ) ≤ p := by exact_mod_cast hp
    have : 0 < (n : ℝ) - f - p := by linarith
    positivity
  have key := div_le_kappaStar f F x _ hcard hvpos
  convert key using 2
  rw [hFx, hmean, hvar, zero_sub, norm_neg, norm_smul, he, mul_one, Real.norm_eq_abs, sq_abs, hN]
  have : 0 < (n : ℝ) - f - p := by linarith
  field_simp

/-- If `n - f ≥ 2`, every aggregation rule has `κ⋆ ≥ 0`: the configuration `e, 0, …, 0` with
`S = {1, …, n - f}` has positive variance. -/
theorem zero_le_kappaStar [Nontrivial E] {f : ℕ} (h : f + 2 ≤ n) (F : (Fin n → E) → E) :
    0 ≤ kappaStar f F := by
  obtain ⟨e, he⟩ := exists_unit E
  have hcard : (block n 0 (n - f)).card = n - f := by rw [card_block (Nat.sub_le _ _)]; simp
  have hvar := variance_twoVal (p := 1) he (show 1 ≤ n - f by omega) (Nat.sub_le n f) (by omega)
  have hN : (2 : ℝ) ≤ ((n - f : ℕ) : ℝ) := by exact_mod_cast (show 2 ≤ n - f by omega)
  have hvpos : 0 < variance (fun i => twoVal 1 i • e) (block n 0 (n - f)) := by
    rw [hvar]
    exact div_pos (by push_cast; linarith) (by positivity)
  refine le_trans ?_ (div_le_kappaStar f F _ _ hcard hvpos)
  exact_mod_cast div_nonneg (sq_nonneg _) hvpos.le

/-! ### Degenerate case `n = 1` -/

/-- For `n = 1` and `f = 0`, the only `1`-MultiKrum rule (= Krum = `(n-f)`-MultiKrum) is
`F x = x₀`, whose robustness coefficient is `-∞`, since every reference set has `Σ_S = 0` and
zero bias (convention `0/0 = -∞`). Hence Proposition 1, the odd case of Theorem 3 and Theorem 4
fail for `n = 1` (their bounds are all `0`). -/
theorem kappaStar_eq_bot_of_n_eq_one (F : (Fin 1 → E) → E) (hF : IsMultiKrum 0 1 F) :
    kappaStar 0 F = ⊥ := by
  have hT : ∀ (x : Fin 1 → E) (T : Finset (Fin 1)), T.card = 1 →
      mean x T = x 0 ∧ variance x T = 0 := by
    intro x T hT
    have hne : T.Nonempty := card_pos.1 (by omega)
    have hc : ∀ i ∈ T, x i = x 0 := fun i _ => by rw [Subsingleton.elim i 0]
    exact ⟨mean_eq_of_const hne hc, variance_eq_zero_of_const hne hc⟩
  unfold kappaStar
  simp only [iSup_eq_bot]
  intro x S hS
  obtain ⟨S', hS', hFS⟩ := hF x
  rw [(hT x S hS).1, (hT x S hS).2, hFS, (hT x S' hS'.1).1]
  simp [ratio]

/-- Non-vacuity of `kappaStar_eq_bot_of_n_eq_one`: Krum exists for `n = 1`. -/
theorem exists_isMultiKrum_kappaStar_eq_bot :
    ∃ F : (Fin 1 → E) → E, IsMultiKrum 0 1 F ∧ kappaStar 0 F = ⊥ := by
  obtain ⟨F, hF⟩ := exists_isMultiKrum (E := E) (n := 1) 0 le_rfl
  exact ⟨F, hF, kappaStar_eq_bot_of_n_eq_one F hF⟩

/-! ### Proposition 1 -/

lemma ratio_eq_top {a : ℝ} (ha : a ≠ 0) : ratio a 0 = ⊤ := by simp [ratio, ha]

/-- Proposition 1, case `n = 2f`: `f` copies of `e` and `f` copies of `0`; both halves are
reference sets with zero variance, and `F(x)` differs from one of their means, so `κ⋆ = +∞`. -/
theorem kappaStar_eq_top_of_n_eq_two_mul [Nontrivial E] {f : ℕ} (hf : 1 ≤ f) (hn : n = 2 * f)
    (F : (Fin n → E) → E) : kappaStar f F = ⊤ := by
  obtain ⟨e, he⟩ := exists_unit E
  set x : Fin n → E := fun i => twoVal f i • e with hx
  have hc1 : (block n 0 f).card = n - f := by rw [card_block (by omega)]; omega
  have hc2 : (block n f n).card = n - f := card_block le_rfl
  have hne1 : (block n 0 f).Nonempty := card_pos.1 (by omega)
  have hne2 : (block n f n).Nonempty := card_pos.1 (by omega)
  have hv1 : ∀ i ∈ block n 0 f, x i = e := fun i hi => by
    simp only [mem_block] at hi; simp [hx, twoVal, hi.2]
  have hv2 : ∀ i ∈ block n f n, x i = 0 := fun i hi => by
    simp only [mem_block] at hi; simp [hx, twoVal, not_lt.2 hi.1]
  refine top_le_iff.1 ?_
  by_cases hFx : F x = e
  · have := ratio_le_kappaStar f F x _ hc2
    rwa [mean_eq_of_const hne2 hv2, variance_eq_zero_of_const hne2 hv2, hFx, sub_zero, he,
      ratio_eq_top (by norm_num)] at this
  · have := ratio_le_kappaStar f F x _ hc1
    rwa [mean_eq_of_const hne1 hv1, variance_eq_zero_of_const hne1 hv1,
      ratio_eq_top (by simpa [sub_eq_zero] using hFx)] at this

/-! ### Theorem 3 -/

/-- **Theorem 3** (Krum's lower bound), `n` even: `κ⋆₁ ≥ (n - 2)/(n - 2f + 2)`, under the
standing assumption `f ≤ n/2` of Definition 2. For `n = 2f` the bound holds trivially
(`κ⋆ = +∞`, `kappaStar_eq_top_of_n_eq_two_mul`); for `n = 2` (where `f = 0` and the bound is `0`)
the paper's construction degenerates and we use `zero_le_kappaStar` instead. -/
theorem theorem_3_even [Nontrivial E] {f : ℕ} (hev : Even n) (hn : 2 ≤ n) (hf' : 2 * f ≤ n)
    {F : (Fin n → E) → E} (hF : IsMultiKrum f 1 F) :
    ((((n : ℝ) - 2) / ((n : ℝ) - 2 * f + 2) : ℝ) : EReal) ≤ kappaStar f F := by
  rcases hf'.lt_or_eq with hf | hf
  swap
  · rw [kappaStar_eq_top_of_n_eq_two_mul (by omega) hf.symm F]; exact le_top
  obtain ⟨h, rfl⟩ := hev
  rcases Nat.lt_or_ge h 2 with h2 | h2
  · obtain rfl : h = 1 := by omega
    obtain rfl : f = 0 := by omega
    norm_num
    exact zero_le_kappaStar (by norm_num) F
  · have key := krum_lowerBound_aux (p := h - 1) (by omega) (by omega) (by omega) hF
    convert key using 2
    push_cast [Nat.cast_sub (show 1 ≤ h by omega)]
    have : (f : ℝ) + 1 ≤ h := by exact_mod_cast (show f + 1 ≤ h by omega)
    rw [div_eq_div_iff (by linarith) (by linarith)]
    ring

/-- **Theorem 3** (Krum's lower bound), `n` odd: `κ⋆₁ ≥ (n - 1)/(n - 2f + 1)`, for `n ≥ 3`
(for `n = 1` the statement fails, see `kappaStar_eq_bot_of_n_eq_one`). -/
theorem theorem_3_odd [Nontrivial E] {f : ℕ} (hodd : Odd n) (hn : 3 ≤ n) (hf' : 2 * f ≤ n)
    {F : (Fin n → E) → E} (hF : IsMultiKrum f 1 F) :
    ((((n : ℝ) - 1) / ((n : ℝ) - 2 * f + 1) : ℝ) : EReal) ≤ kappaStar f F := by
  obtain ⟨h, rfl⟩ := hodd
  have hf : 2 * f < 2 * h + 1 := by omega
  have key := krum_lowerBound_aux (p := h) (by omega) (by omega) (by omega) hF
  convert key using 2
  push_cast
  have : (f : ℝ) ≤ h := by exact_mod_cast (show f ≤ h by omega)
  rw [div_eq_div_iff (by linarith) (by linarith)]
  ring

/-! ### Three-valued configurations: `f` copies of `-e`, `n - 2f` of `0`, `f` of `w e` -/

/-- Coefficients of the three-valued configuration: `-1` on the first `f` indices, `0` on the next
`n - 2f`, and `w` on the last `f`. -/
noncomputable def threeVal (f : ℕ) (w : ℝ) (i : Fin n) : ℝ :=
  if i.val < f then -1 else if i.val < n - f then 0 else w

lemma sum_threeVal_low {f : ℕ} (hf : 2 * f ≤ n) (w : ℝ) (g : ℝ → ℝ) :
    ∑ i ∈ block n 0 (n - f), g (threeVal f w i) = f * g (-1) + ((n - 2 * f : ℕ) : ℝ) * g 0 := by
  rw [sum_block_split (Nat.zero_le f) (by omega), sum_block_const (by omega) (v := g (-1)),
    sum_block_const (by omega) (v := g 0)]
  · rw [show n - f - f = n - 2 * f by omega, Nat.sub_zero]
  all_goals intro i ha hb; simp only [threeVal]; split_ifs <;> first | rfl | (exfalso; omega)

lemma sum_threeVal_high {f : ℕ} (hf : 2 * f ≤ n) (w : ℝ) (g : ℝ → ℝ) :
    ∑ i ∈ block n f n, g (threeVal f w i) = ((n - 2 * f : ℕ) : ℝ) * g 0 + f * g w := by
  rw [sum_block_split (show f ≤ n - f by omega) (Nat.sub_le n f), sum_block_const (by omega) (v := g 0),
    sum_block_const le_rfl (v := g w)]
  · rw [show n - f - f = n - 2 * f by omega, show n - (n - f) = f by omega]
  all_goals intro i ha hb; simp only [threeVal]; split_ifs <;> first | rfl | (exfalso; omega)

lemma cast_sub_two_mul {f : ℕ} (hf : 2 * f ≤ n) : ((n - 2 * f : ℕ) : ℝ) = n - 2 * f := by
  push_cast [Nat.cast_sub hf]; ring

lemma cast_sub' {f : ℕ} (hf : f ≤ n) : ((n - f : ℕ) : ℝ) = n - f := by
  push_cast [Nat.cast_sub hf]; ring

/-- The reference set `S = {1, …, n - f}` (the `-e`'s and the `0`'s) has mean `-f/(n-f) e`. -/
lemma mean_threeVal_low {e : E} {f : ℕ} (hf : 2 * f < n) (w : ℝ) :
    mean (fun i => threeVal f w i • e) (block n 0 (n - f)) = (-(f : ℝ) / (n - f)) • e := by
  rw [mean_line, card_block (Nat.sub_le _ _), Nat.sub_zero,
    sum_threeVal_low (g := fun t => t) hf.le w, cast_sub' (by omega)]
  congr 1
  ring

/-- The reference set `S = {1, …, n - f}` has variance `f (n - 2f)/(n - f)²`. -/
lemma variance_threeVal_low {e : E} (he : ‖e‖ = 1) {f : ℕ} (hf : 2 * f < n) (w : ℝ) :
    variance (fun i => threeVal f w i • e) (block n 0 (n - f)) =
      f * (n - 2 * f) / ((n : ℝ) - f) ^ 2 := by
  rw [variance_line he, card_block (Nat.sub_le _ _), Nat.sub_zero,
    sum_threeVal_low (g := fun t => t) hf.le w,
    sum_threeVal_low (g := fun t => (t - ((n - f : ℕ) : ℝ)⁻¹ * (f * -1 + ((n - 2 * f : ℕ) : ℝ) * 0)) ^ 2)
      hf.le w, cast_sub' (by omega), cast_sub_two_mul hf.le]
  have : (0 : ℝ) < n - f := by
    have : (f : ℝ) < n := by exact_mod_cast (show f < n by omega)
    linarith
  field_simp
  ring

/-- With `w = 1`, the set `{f + 1, …, n}` (the `0`'s and the `e`'s) has mean `f/(n-f) e`. -/
lemma mean_threeVal_high {e : E} {f : ℕ} (hf : 2 * f < n) :
    mean (fun i => threeVal f 1 i • e) (block n f n) = ((f : ℝ) / (n - f)) • e := by
  rw [mean_line, card_block le_rfl, sum_threeVal_high (g := fun t => t) hf.le 1, cast_sub' (by omega)]
  congr 1
  ring

/-- With `w = 1`, the set `{f + 1, …, n}` has variance `f (n - 2f)/(n - f)²`. -/
lemma variance_threeVal_high {e : E} (he : ‖e‖ = 1) {f : ℕ} (hf : 2 * f < n) :
    variance (fun i => threeVal f 1 i • e) (block n f n) =
      f * (n - 2 * f) / ((n : ℝ) - f) ^ 2 := by
  rw [variance_line he, card_block le_rfl,
    sum_threeVal_high (g := fun t => t) hf.le 1,
    sum_threeVal_high (g := fun t => (t - ((n - f : ℕ) : ℝ)⁻¹ * (((n - 2 * f : ℕ) : ℝ) * 0 + f * 1)) ^ 2)
      hf.le 1, cast_sub' (by omega), cast_sub_two_mul hf.le]
  have : (0 : ℝ) < n - f := by
    have : (f : ℝ) < n := by exact_mod_cast (show f < n by omega)
    linarith
  field_simp
  ring

/-- Proposition 1, main case `f ≥ 1`, `2f < n`: with `f` copies of `-e`, `n - 2f` of `0` and `f`
of `e`, the reference sets `{1, …, n-f}` and `{f+1, …, n}` have means `∓ f/(n-f) e` and equal
variances `f(n-2f)/(n-f)²`; `F(x)` is at distance `≥ f/(n-f)` from one of the two means. -/
theorem prop_1_aux [Nontrivial E] {f : ℕ} (hf : 1 ≤ f) (hn : 2 * f < n) (F : (Fin n → E) → E) :
    ((((f : ℝ) / ((n : ℝ) - 2 * f)) : ℝ) : EReal) ≤ kappaStar f F := by
  obtain ⟨e, he⟩ := exists_unit E
  set x : Fin n → E := fun i => threeVal f 1 i • e with hx
  have hf' : (1 : ℝ) ≤ f := by exact_mod_cast hf
  have hn' : (2 * f : ℝ) + 1 ≤ n := by exact_mod_cast (show 2 * f + 1 ≤ n by omega)
  have hc1 : (block n 0 (n - f)).card = n - f := by rw [card_block (Nat.sub_le _ _)]; simp
  have hc2 : (block n f n).card = n - f := card_block le_rfl
  have hV : (0 : ℝ) < f * (n - 2 * f) / ((n : ℝ) - f) ^ 2 := by
    apply div_pos (mul_pos (by linarith) (by linarith)) (by nlinarith)
  set V := f * ((n : ℝ) - 2 * f) / ((n : ℝ) - f) ^ 2 with hVdef
  have hv1 : variance x (block n 0 (n - f)) = V := variance_threeVal_low he hn 1
  have hv2 : variance x (block n f n) = V := variance_threeVal_high he hn
  have hm1 : mean x (block n 0 (n - f)) = (-(f : ℝ) / (n - f)) • e := mean_threeVal_low hn 1
  have hm2 : mean x (block n f n) = ((f : ℝ) / (n - f)) • e := mean_threeVal_high hn
  have k1 := div_le_kappaStar f F x _ hc1 (hv1 ▸ hV)
  have k2 := div_le_kappaStar f F x _ hc2 (hv2 ▸ hV)
  rw [hv1, hm1] at k1
  rw [hv2, hm2] at k2
  set q : ℝ := (f : ℝ) / (n - f) with hq
  have hq0 : 0 ≤ q := div_nonneg (by linarith) (by linarith)
  have hgoal : (f : ℝ) / (n - 2 * f) = q ^ 2 / V := by
    rw [hq, hVdef]
    have : (0 : ℝ) < n - f := by linarith
    have : (0 : ℝ) < n - 2 * f := by linarith
    field_simp
  -- `F(x)` is at distance at least `q` from one of the two means
  set y := F x
  have htri : ‖(-q) • e - q • e‖ ≤ ‖y - (-q) • e‖ + ‖y - q • e‖ := by
    have := norm_sub_le_norm_sub_add_norm_sub ((-q) • e) y (q • e)
    rwa [norm_sub_rev ((-q) • e) y] at this
  have hd : ‖(-q) • e - q • e‖ = 2 * q := by
    rw [← sub_smul, norm_smul, he, mul_one, Real.norm_eq_abs, abs_of_nonpos (by linarith)]
    ring
  rw [hd] at htri
  rw [hgoal]
  have hqdiv : -(f : ℝ) / (n - f) = -q := by rw [hq, neg_div]
  rw [hqdiv] at k1
  by_cases h1 : q ≤ ‖y - (-q) • e‖
  · refine le_trans ?_ k1
    exact_mod_cast div_le_div_of_nonneg_right (pow_le_pow_left₀ hq0 h1 2) hV.le
  · refine le_trans ?_ k2
    have h2 : q ≤ ‖y - q • e‖ := by linarith
    exact_mod_cast div_le_div_of_nonneg_right (pow_le_pow_left₀ hq0 h2 2) hV.le

/-- **Proposition 1** (universal lower bound). Let `2f ≤ n` (Definition 2 assumes `f ≤ n/2`) and
`n ≥ 2`. If an aggregation rule `F` is robust (`κ⋆(F) < ∞`), then `n - 2f > 0` and
`κ⋆(F) ≥ f/(n - 2f)`. (For `n = 1` the bound fails: `kappaStar_eq_bot_of_n_eq_one`.) -/
theorem prop_1 [Nontrivial E] {f : ℕ} (hn : 2 ≤ n) (hf : 2 * f ≤ n) (F : (Fin n → E) → E)
    (hF : kappaStar f F < ⊤) :
    2 * f < n ∧ ((((f : ℝ) / ((n : ℝ) - 2 * f)) : ℝ) : EReal) ≤ kappaStar f F := by
  have hlt : 2 * f < n := by
    refine lt_of_le_of_ne hf fun h => ?_
    rw [kappaStar_eq_top_of_n_eq_two_mul (by omega) h.symm F] at hF
    exact lt_irrefl _ hF
  refine ⟨hlt, ?_⟩
  rcases Nat.eq_zero_or_pos f with rfl | hf1
  · simpa using zero_le_kappaStar (by omega) F
  · exact prop_1_aux hf1 hlt F

/-! ### Proposition B.1 and Theorem 4 -/

/-- `a(n, f, m) = min(m, n - 2f)`, the number of zero vectors selected in Proposition B.1. -/
def aB1 (n f m : ℕ) : ℕ := min m (n - 2 * f)

/-- The bound `R(n, f, m) = (n-f)²/(f(n-2f)) · ((a·f/(n-f) + m - a)/m)²` as stated in
Proposition B.1 of the paper. -/
noncomputable def boundB1 (n f m : ℕ) : ℝ :=
  ((n : ℝ) - f) ^ 2 / (f * ((n : ℝ) - 2 * f)) *
    (((aB1 n f m : ℝ) * (f / ((n : ℝ) - f)) + m - aB1 n f m) / m) ^ 2

/-- The corrected bound `R'(n, f, m) = (n-f)²/(f(n-2f)) · (f/(n-f) + (m - a)/m)²` that the
construction of Proposition B.1 actually yields (the bias is `‖x̄_{S⋆} - x̄_S‖ =
(m-a)(1-ε)/m + f/(n-f)`, not `(a·f/(n-f) + (m-a)(1-ε))/m`). -/
noncomputable def boundB1Corrected (n f m : ℕ) : ℝ :=
  ((n : ℝ) - f) ^ 2 / (f * ((n : ℝ) - 2 * f)) *
    ((f : ℝ) / ((n : ℝ) - f) + ((m : ℝ) - aB1 n f m) / m) ^ 2

/-- The instance of Proposition B.1 for a fixed `ε ∈ (0, 1)`: `f` copies of `-e`, `n - 2f` of `0`,
`f` of `(1-ε) e`. Every valid selection consists of `a` zeros and `m - a` copies of `(1-ε) e`. -/
theorem prop_B1_instance [Nontrivial E] {f m : ℕ} (hf : 1 ≤ f) (hn : 3 * f < n) (hm0 : 0 < m)
    (hm : m ≤ n - f) {F : (Fin n → E) → E} (hF : IsMultiKrum f m F) {ε : ℝ} (hε0 : 0 < ε)
    (hε1 : ε < 1) :
    ((((n : ℝ) - f) ^ 2 / (f * ((n : ℝ) - 2 * f)) *
      ((f : ℝ) / ((n : ℝ) - f) + ((m : ℝ) - aB1 n f m) * (1 - ε) / m) ^ 2 : ℝ) : EReal) ≤
      kappaStar f F := by
  obtain ⟨e, he⟩ := exists_unit E
  set w : ℝ := 1 - ε with hw
  have hw0 : 0 < w := by linarith
  have hw1 : w < 1 := by linarith
  set x : Fin n → E := fun i => threeVal f w i • e with hx
  have hf' : (1 : ℝ) ≤ f := by exact_mod_cast hf
  have hn' : (3 * f : ℝ) + 1 ≤ n := by exact_mod_cast (show 3 * f + 1 ≤ n by omega)
  have hN : ((n - f : ℕ) : ℝ) = n - f := cast_sub' (by omega)
  have hNpos : (0 : ℝ) < n - f := by linarith
  have hx_low : ∀ j : Fin n, j.val < f → x j = (-1 : ℝ) • e := fun j hj => by
    simp [hx, threeVal, hj]
  have hx_mid : ∀ j : Fin n, f ≤ j.val → j.val < n - f → x j = (0 : ℝ) • e := fun j h1 h2 => by
    simp [hx, threeVal, not_lt.2 h1, h2]
  have hx_high : ∀ j : Fin n, n - f ≤ j.val → x j = w • e := fun j h => by
    simp [hx, threeVal, not_lt.2 h, show ¬ j.val < f by omega]
  -- scores
  have hT : (block n f n).card = n - f := card_block le_rfl
  have hs0 : score f x ((0 : ℝ) • e) ≤ ((n - f : ℕ) : ℝ)⁻¹ * (f * w ^ 2) := by
    unfold score
    gcongr
    calc nearestSum x (n - f) ((0 : ℝ) • e)
        ≤ ∑ j ∈ block n f n, (0 - threeVal f w j) ^ 2 := nearestSum_line_le he _ _ hT
      _ = f * w ^ 2 := by rw [sum_threeVal_high (by omega) w (fun t => (0 - t) ^ 2)]; ring
  have hsw : score f x (w • e) ≤ ((n - f : ℕ) : ℝ)⁻¹ * ((n - 2 * f : ℝ) * w ^ 2) := by
    unfold score
    gcongr
    calc nearestSum x (n - f) (w • e)
        ≤ ∑ j ∈ block n f n, (w - threeVal f w j) ^ 2 := nearestSum_line_le he _ _ hT
      _ = (n - 2 * f : ℝ) * w ^ 2 := by
          rw [sum_threeVal_high (by omega) w (fun t => (w - t) ^ 2), cast_sub_two_mul (by omega)]
          ring
  have hsw' : ((n - f : ℕ) : ℝ)⁻¹ * ((n - 2 * f : ℝ) * w ^ 2) ≤ score f x (w • e) := by
    unfold score
    gcongr
    have hsub : (univ.filter fun j => (w - threeVal f w j) ^ 2 < w ^ 2) ⊆ block n (n - f) n := by
      intro j hj
      rw [mem_filter_univ] at hj
      simp only [mem_block]
      simp only [threeVal] at hj
      split_ifs at hj with h1 h2
      · exfalso; nlinarith
      · exfalso; simp at hj
      · exact ⟨by omega, j.isLt⟩
    have := le_nearestSum_line he (threeVal f w) (k := n - f) (r := f) (Nat.sub_le n f) w
      (sq_nonneg w) ((card_le_card hsub).trans (by rw [card_block le_rfl]; omega))
    rw [hN] at this
    linarith
  have hsm : ((n - f : ℕ) : ℝ)⁻¹ * (n - 2 * f : ℝ) ≤ score f x ((-1 : ℝ) • e) := by
    unfold score
    gcongr
    have hsub : (univ.filter fun j => (-1 - threeVal f w j) ^ 2 < 1) ⊆ block n 0 f := by
      intro j hj
      rw [mem_filter_univ] at hj
      simp only [mem_block, Nat.zero_le, true_and]
      simp only [threeVal] at hj
      split_ifs at hj with h1 h2
      · exact h1
      · exfalso; norm_num at hj
      · exfalso; nlinarith
    have := le_nearestSum_line he (threeVal f w) (k := n - f) (r := f) (Nat.sub_le n f) (-1)
      zero_le_one ((card_le_card hsub).trans (by rw [card_block (by omega)]; omega))
    rw [hN] at this
    linarith
  have hNinv : (0 : ℝ) < ((n - f : ℕ) : ℝ)⁻¹ := by rw [hN]; exact inv_pos.2 hNpos
  have hAB : (f : ℝ) * w ^ 2 < (n - 2 * f : ℝ) * w ^ 2 := by
    have : (f : ℝ) < n - 2 * f := by linarith
    have : 0 < w ^ 2 := by positivity
    nlinarith
  have hBC : (n - 2 * f : ℝ) * w ^ 2 < (n - 2 * f : ℝ) := by
    have : 0 < (n : ℝ) - 2 * f := by linarith
    have : w ^ 2 < 1 := by nlinarith
    nlinarith
  have h0w : score f x ((0 : ℝ) • e) < score f x (w • e) :=
    hs0.trans_lt ((mul_lt_mul_of_pos_left hAB hNinv).trans_le hsw')
  have hwm : score f x (w • e) < score f x ((-1 : ℝ) • e) :=
    hsw.trans_lt ((mul_lt_mul_of_pos_left hBC hNinv).trans_le hsm)
  -- the two separated groups
  have hG1 : ∀ i ∈ block n f (n - f), ∀ j ∉ block n f (n - f),
      score f x (x i) < score f x (x j) := by
    intro i hi j hj
    simp only [mem_block, not_and, not_lt] at hi hj
    rw [hx_mid i hi.1 hi.2]
    rcases lt_or_ge j.val f with h | h
    · rw [hx_low j h]; exact h0w.trans hwm
    · rw [hx_high j (hj h)]; exact h0w
  have hG2 : ∀ i ∈ block n f n, ∀ j ∉ block n f n, score f x (x i) < score f x (x j) := by
    intro i hi j hj
    simp only [mem_block, not_and, not_lt] at hi hj
    have hj' : j.val < f := by
      by_contra h
      have := hj (not_lt.1 h)
      omega
    rw [hx_low j hj']
    rcases lt_or_ge i.val (n - f) with h | h
    · rw [hx_mid i hi.1 h]; exact h0w.trans hwm
    · rw [hx_high i h]; exact hwm
  -- the selection
  obtain ⟨S, hS, hFS⟩ := hF x
  have hsumS : ∑ i ∈ S, threeVal f w i = ((m : ℝ) - aB1 n f m) * w := by
    rcases le_or_gt m (n - 2 * f) with hle | hgt
    · have hsub := hS.subset_of_score_lt hG1 (by rw [card_block (by omega)]; omega)
      have ha : aB1 n f m = m := min_eq_left hle
      rw [ha, sub_self, zero_mul]
      refine sum_eq_zero fun i hi => ?_
      have := mem_block.1 (hsub hi)
      simp [threeVal, not_lt.2 this.1, this.2]
    · have hsup := hS.superset_of_score_lt hG1 (by rw [card_block (by omega)]; omega)
      have hsub := hS.subset_of_score_lt hG2 (by rw [card_block le_rfl]; omega)
      have ha : aB1 n f m = n - 2 * f := min_eq_right hgt.le
      rw [← sum_sdiff hsup, sum_eq_zero (s := block n f (n - f)) (fun i hi => by
        have := mem_block.1 hi
        simp [threeVal, not_lt.2 this.1, this.2]), add_zero,
        sum_congr rfl (g := fun _ => w) (fun i hi => by
          have h1 := mem_block.1 (hsub (mem_sdiff.1 hi).1)
          have h2 : ¬ (i ∈ block n f (n - f)) := (mem_sdiff.1 hi).2
          simp only [mem_block, not_and, not_lt] at h2
          have h3 := h2 h1.1
          simp [threeVal, not_lt.2 h3, show ¬ i.val < f by omega]),
        sum_const, nsmul_eq_mul, card_sdiff_of_subset hsup, hS.1, card_block (by omega), ha,
        show n - f - f = n - 2 * f by omega]
      push_cast [Nat.cast_sub (show n - 2 * f ≤ m by omega)]
      ring
  have hmeanS : F x = (((m : ℝ))⁻¹ * (((m : ℝ) - aB1 n f m) * w)) • e := by
    rw [hFS, mean_line, hS.1, hsumS]
  -- the reference set
  have hc1 : (block n 0 (n - f)).card = n - f := by rw [card_block (Nat.sub_le _ _)]; simp
  have hv1 : variance x (block n 0 (n - f)) = f * (n - 2 * f) / ((n : ℝ) - f) ^ 2 :=
    variance_threeVal_low he (by omega) w
  have hm1 : mean x (block n 0 (n - f)) = (-(f : ℝ) / (n - f)) • e :=
    mean_threeVal_low (by omega) w
  have hV : (0 : ℝ) < f * (n - 2 * f) / ((n : ℝ) - f) ^ 2 :=
    div_pos (mul_pos (by linarith) (by linarith)) (by positivity)
  have key := div_le_kappaStar f F x _ hc1 (hv1 ▸ hV)
  convert key using 2
  rw [hv1, hm1, hmeanS, ← sub_smul, norm_smul, he, mul_one, Real.norm_eq_abs, sq_abs]
  have : (0 : ℝ) < m := by exact_mod_cast hm0
  have : (0 : ℝ) < n - 2 * f := by linarith
  field_simp
  ring

/-- **Proposition B.1, corrected.** For `n > 3f`, `f ≥ 1` and `0 < m ≤ n - f`, every
`m`-MultiKrum rule (any tie-breaking) satisfies `κ⋆_m ≥ R'(n, f, m)
= (n-f)²/(f(n-2f)) · (f/(n-f) + (m-a)/m)²`, `a = min(m, n-2f)`. Obtained from
`prop_B1_instance` by letting `ε → 0⁺`. -/
theorem prop_B1_corrected [Nontrivial E] {f m : ℕ} (hf : 1 ≤ f) (hn : 3 * f < n) (hm0 : 0 < m)
    (hm : m ≤ n - f) {F : (Fin n → E) → E} (hF : IsMultiKrum f m F) :
    ((boundB1Corrected n f m : ℝ) : EReal) ≤ kappaStar f F := by
  set g : ℝ → ℝ := fun ε => ((n : ℝ) - f) ^ 2 / (f * ((n : ℝ) - 2 * f)) *
      ((f : ℝ) / ((n : ℝ) - f) + ((m : ℝ) - aB1 n f m) * (1 - ε) / m) ^ 2 with hg
  have hcont : Continuous g := by rw [hg]; fun_prop
  have hlim : Tendsto (fun ε => ((g ε : ℝ) : EReal)) (𝓝[>] 0) (𝓝 ((g 0 : ℝ) : EReal)) :=
    ((continuous_coe_real_ereal.comp hcont).tendsto 0).mono_left nhdsWithin_le_nhds
  have hg0 : g 0 = boundB1Corrected n f m := by simp [hg, boundB1Corrected]
  rw [← hg0]
  refine le_of_tendsto hlim ?_
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 from one_pos)] with ε hε
  exact prop_B1_instance hf hn hm0 hm hF hε.1 hε.2

lemma aB1_le (n f m : ℕ) : (aB1 n f m : ℝ) ≤ m := by exact_mod_cast min_le_left _ _

/-- The paper's bound is never larger than the corrected one. -/
lemma boundB1_le_corrected {f m : ℕ} (hn : 2 * f < n) (hm0 : 0 < m) :
    boundB1 n f m ≤ boundB1Corrected n f m := by
  unfold boundB1 boundB1Corrected
  have hn' : (2 * f : ℝ) + 1 ≤ n := by exact_mod_cast (show 2 * f + 1 ≤ n by omega)
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm0
  have hq : (0 : ℝ) ≤ f / ((n : ℝ) - f) := div_nonneg (Nat.cast_nonneg _) (by linarith)
  have ha := aB1_le n f m
  have ha0 : (0 : ℝ) ≤ aB1 n f m := Nat.cast_nonneg _
  refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ?_ ?_ 2) ?_
  · exact div_nonneg (by nlinarith) hm'.le
  · rw [div_le_iff₀ hm', add_mul, div_mul_cancel₀ _ hm'.ne']
    nlinarith
  · exact div_nonneg (sq_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (by linarith))

/-- The two bounds agree when `m ≤ n - 2f` (then `a = m` and only zeros are selected). -/
lemma boundB1_eq_corrected_of_le {f m : ℕ} (hm0 : 0 < m) (hm : m ≤ n - 2 * f) :
    boundB1 n f m = boundB1Corrected n f m := by
  have ha : aB1 n f m = m := min_eq_left hm
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm0.ne'
  unfold boundB1 boundB1Corrected
  rw [ha]
  congr 2
  field_simp
  ring

/-- The paper's bound is *strictly* smaller than the corrected one as soon as `m > n - 2f`
(then some copies of `(1-ε) e` are selected, and the paper's bias computation undercounts the
`f/(n-f)` offset of the reference mean). -/
lemma boundB1_lt_corrected {f m : ℕ} (hf : 1 ≤ f) (hn : 2 * f < n) (hgt : n - 2 * f < m) :
    boundB1 n f m < boundB1Corrected n f m := by
  have ha : aB1 n f m = n - 2 * f := min_eq_right hgt.le
  have hn' : (2 * f : ℝ) + 1 ≤ n := by exact_mod_cast (show 2 * f + 1 ≤ n by omega)
  have hf' : (1 : ℝ) ≤ f := by exact_mod_cast hf
  have hm' : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hlt : ((aB1 n f m : ℕ) : ℝ) < m := by exact_mod_cast (ha ▸ hgt)
  have hq : (0 : ℝ) < f / ((n : ℝ) - f) := div_pos (by linarith) (by linarith)
  have ha0 : (0 : ℝ) ≤ aB1 n f m := Nat.cast_nonneg _
  unfold boundB1 boundB1Corrected
  refine mul_lt_mul_of_pos_left (pow_lt_pow_left₀ ?_ ?_ two_ne_zero) ?_
  · rw [div_lt_iff₀ hm', add_mul, div_mul_cancel₀ _ hm'.ne']
    nlinarith
  · exact div_nonneg (by nlinarith) hm'.le
  · exact div_pos (by nlinarith) (mul_pos (by linarith) (by linarith))

/-- **Proposition B.1** as stated in the paper: `κ⋆_m ≥ R(n, f, m)`. True (it is weaker than the
corrected bound), although the paper's derivation of `R` contains a computational error. -/
theorem prop_B1 [Nontrivial E] {f m : ℕ} (hf : 1 ≤ f) (hn : 3 * f < n) (hm0 : 0 < m)
    (hm : m ≤ n - f) {F : (Fin n → E) → E} (hF : IsMultiKrum f m F) :
    ((boundB1 n f m : ℝ) : EReal) ≤ kappaStar f F :=
  le_trans (EReal.coe_le_coe_iff.2 (boundB1_le_corrected (by omega) hm0))
    (prop_B1_corrected hf hn hm0 hm hF)

/-- At `m = n - f` the corrected bound is exactly Theorem 4's `4f/(n-2f)`. -/
lemma boundB1Corrected_n_sub_f {f : ℕ} (hf : 1 ≤ f) (hn : 2 * f < n) :
    boundB1Corrected n f (n - f) = 4 * f / ((n : ℝ) - 2 * f) := by
  have ha : aB1 n f (n - f) = n - 2 * f := min_eq_right (by omega)
  have hn' : (2 * f : ℝ) + 1 ≤ n := by exact_mod_cast (show 2 * f + 1 ≤ n by omega)
  have hf' : (1 : ℝ) ≤ f := by exact_mod_cast hf
  unfold boundB1Corrected
  rw [ha, cast_sub' (by omega), cast_sub_two_mul hn.le]
  have : (0 : ℝ) < n - f := by linarith
  have : (0 : ℝ) < n - 2 * f := by linarith
  field_simp
  ring

/-- At `m = n - f` the paper's bound is `R = f (2n - 3f)² / ((n - 2f)(n - f)²)`. -/
lemma boundB1_n_sub_f {f : ℕ} (hf : 1 ≤ f) (hn : 2 * f < n) :
    boundB1 n f (n - f) = f * (2 * n - 3 * f) ^ 2 / (((n : ℝ) - 2 * f) * ((n : ℝ) - f) ^ 2) := by
  have ha : aB1 n f (n - f) = n - 2 * f := min_eq_right (by omega)
  have hn' : (2 * f : ℝ) + 1 ≤ n := by exact_mod_cast (show 2 * f + 1 ≤ n by omega)
  have hf' : (1 : ℝ) ≤ f := by exact_mod_cast hf
  unfold boundB1
  rw [ha, cast_sub_two_mul hn.le, cast_sub' (by omega)]
  have : (0 : ℝ) < n - f := by linarith
  have : (0 : ℝ) < n - 2 * f := by linarith
  field_simp
  ring

/-- The paper's Proposition B.1 does **not** recover Theorem 4: at `m = n - f` its bound
`f (2n-3f)²/((n-2f)(n-f)²)` is strictly smaller than `4f/(n-2f)`. -/
theorem prop_B1_paper_lt_theorem_4 {f : ℕ} (hf : 1 ≤ f) (hn : 2 * f < n) :
    boundB1 n f (n - f) < 4 * f / ((n : ℝ) - 2 * f) := by
  rw [← boundB1Corrected_n_sub_f hf hn]
  exact boundB1_lt_corrected hf hn (by omega)

/-- **Theorem 4** ((n−f)-MultiKrum's lower bound). For `n > 3f` (and `n ≥ 2`, excluding the
degenerate `n = 1`, see `kappaStar_eq_bot_of_n_eq_one`), every `(n-f)`-MultiKrum rule satisfies
`κ⋆_{n-f} ≥ 4f/(n-2f)`. Proved as the case `m = n - f` of `prop_B1_corrected`. -/
theorem theorem_4 [Nontrivial E] {f : ℕ} (hn : 3 * f < n) (hn2 : 2 ≤ n)
    {F : (Fin n → E) → E} (hF : IsMultiKrum f (n - f) F) :
    (((4 * f / ((n : ℝ) - 2 * f)) : ℝ) : EReal) ≤ kappaStar f F := by
  rcases Nat.eq_zero_or_pos f with rfl | hf
  · simpa using zero_le_kappaStar (by omega) F
  · rw [← boundB1Corrected_n_sub_f hf (by omega)]
    exact prop_B1_corrected hf hn (by omega) le_rfl hF

end Podc.MultiKrumRobustness
