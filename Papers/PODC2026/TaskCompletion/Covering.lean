import Papers.PODC2026.TaskCompletion.Basic

/-!
# Lemma 3.1: existence of load balancing covering families

Fischer, Gelles, *The Task Completion Problem and its Application to Crash-Resilient
Computation* (PODC 2026, arXiv:2605.17961), Section 3.

Probabilistic method on a finite uniform space: membership `j ∈ A_i` is the event `x j i < B` for
a uniformly random `x : Fin n → Fin (2m) → Fin k`, i.e. probability exactly `B/k`, independently
over all pairs `(i, j)`.
-/

open Finset

namespace Podc.TaskCompletion

/-! ### Generic counting lemmas -/

-- CSLib candidate (Cslib/Probability/Finite/Uniform.lean)
section Generic

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {Y : Type*} [Fintype Y]

/-- Splitting a sum over `(k+1)`-tuples into the first entry and the rest. -/
lemma sum_fun_succ_cons {M : Type*} [AddCommMonoid M] {k : ℕ} (F : (Fin (k + 1) → Y) → M) :
    ∑ g, F g = ∑ y, ∑ g : Fin k → Y, F (Fin.cons y g) := by
  rw [← (Fin.consEquiv fun _ => Y).sum_comp, Fintype.sum_prod_type]
  rfl

omit [LinearOrder K] [IsStrictOrderedRing K] in
/-- **Second moment of a sum of independent centred variables.** If each `h j` is centred on `Y`,
then `|Y| · ∑_g (∑_j h j (g j))² = |Y|^k ∑_j ∑_y (h j y)²` (the cross terms vanish). -/
theorem card_mul_sum_sq_sum_apply (k : ℕ) (h : Fin k → Y → K) (h0 : ∀ j, ∑ y, h j y = 0) :
    (Fintype.card Y : K) * ∑ g : Fin k → Y, (∑ j, h j (g j)) ^ 2 =
      (Fintype.card Y : K) ^ k * ∑ j, ∑ y, h j y ^ 2 := by
  induction k with
  | zero => simp
  | succ k ih =>
    have ih' := ih (fun j => h j.succ) (fun j => h0 j.succ)
    rw [sum_fun_succ_cons]
    simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
    have hy : ∀ y, ∑ g : Fin k → Y, (h 0 y + ∑ j : Fin k, h j.succ (g j)) ^ 2 =
        (Fintype.card Y : K) ^ k * h 0 y ^ 2 + h 0 y * (2 * ∑ g : Fin k → Y, ∑ j, h j.succ (g j)) +
          ∑ g : Fin k → Y, (∑ j, h j.succ (g j)) ^ 2 := by
      intro y
      simp only [add_sq, sum_add_distrib, ← mul_sum, sum_const, card_univ, Fintype.card_fun,
        Fintype.card_fin, nsmul_eq_mul]
      push_cast
      ring
    simp only [hy, sum_add_distrib, ← sum_mul, h0 0, zero_mul, add_zero, sum_const, card_univ,
      nsmul_eq_mul, ← mul_sum]
    rw [ih']
    ring

/-- **Chebyshev's inequality for a sum of independent centred variables (counting form).** -/
theorem card_le_abs_sum_apply_le (k : ℕ) (h : Fin k → Y → K) (h0 : ∀ j, ∑ y, h j y = 0)
    {δ : K} (hδ : 0 ≤ δ) :
    (#(univ.filter fun g : Fin k → Y => δ ≤ |∑ j, h j (g j)|) : K) * δ ^ 2 *
        Fintype.card Y ≤ (Fintype.card Y : K) ^ k * ∑ j, ∑ y, h j y ^ 2 := by
  rw [← card_mul_sum_sq_sum_apply k h h0, mul_comm _ (Fintype.card Y : K)]
  gcongr
  calc (#(univ.filter fun g : Fin k → Y => δ ≤ |∑ j, h j (g j)|) : K) * δ ^ 2
      = ∑ _g ∈ univ.filter fun g : Fin k → Y => δ ≤ |∑ j, h j (g j)|, δ ^ 2 := by simp
    _ ≤ ∑ g ∈ univ.filter fun g : Fin k → Y => δ ≤ |∑ j, h j (g j)|, (∑ j, h j (g j)) ^ 2 := by
        refine sum_le_sum fun g hg => ?_
        rw [mem_filter] at hg
        exact (pow_le_pow_left₀ hδ hg.2 2).trans (sq_abs _).le
    _ ≤ ∑ g : Fin k → Y, (∑ j, h j (g j)) ^ 2 :=
        sum_le_sum_of_subset_of_nonneg (subset_univ _) fun _ _ _ => sq_nonneg _

/-- **Many independent rare events (counting form, binomial version).** If each coordinate `i`
satisfies `P i` for at most an `a` fraction of its values, then at most `C(|ι|, t) a^t |∀ i, β i|`
points have at least `t` coordinates satisfying `P`. -/
theorem card_many_le_choose {ι : Type*} [Fintype ι] [DecidableEq ι] {β : ι → Type*}
    [∀ i, Fintype (β i)] (P : ∀ i, β i → Prop) [∀ i, DecidablePred (P i)] {a : K}
    (hP : ∀ i, (#(univ.filter (P i)) : K) ≤ a * Fintype.card (β i)) (t : ℕ) :
    (#(univ.filter fun x : ∀ i, β i => t ≤ #(univ.filter fun i => P i (x i))) : K) ≤
      (Fintype.card ι).choose t * a ^ t * Fintype.card (∀ i, β i) := by
  classical
  set N : K := (Fintype.card (∀ i, β i) : K)
  let box : Finset ι → Finset (∀ i, β i) := fun T =>
    Fintype.piFinset fun i => if i ∈ T then univ.filter (P i) else univ
  have hsub : (univ.filter fun x : ∀ i, β i => t ≤ #(univ.filter fun i => P i (x i))) ⊆
      (powersetCard t univ).biUnion box := by
    intro x hx
    rw [mem_filter] at hx
    obtain ⟨T, hT, hTc⟩ := exists_subset_card_eq hx.2
    rw [mem_biUnion]
    refine ⟨T, mem_powersetCard.2 ⟨subset_univ _, hTc⟩, ?_⟩
    rw [Fintype.mem_piFinset]
    intro i
    split_ifs with hi
    · simpa using hT hi
    · exact mem_univ _
  have hT : ∀ T : Finset ι, #T = t → (#(box T) : K) ≤ a ^ t * N := by
    intro T hT
    simp only [box, Fintype.card_piFinset, N, Fintype.card_pi]
    push_cast
    calc ∏ i, ((#(if i ∈ T then univ.filter (P i) else univ) : ℕ) : K)
        ≤ ∏ i, ((if i ∈ T then a else 1) * Fintype.card (β i)) := by
          refine prod_le_prod₀ (fun _ _ => by positivity) fun i _ => ?_
          split_ifs
          · exact hP i
          · simp
      _ = a ^ t * ∏ i, (Fintype.card (β i) : K) := by
          rw [prod_mul_distrib, prod_ite_mem, univ_inter, prod_const, hT]
  calc (#(univ.filter fun x : ∀ i, β i => t ≤ #(univ.filter fun i => P i (x i))) : K)
      ≤ (#((powersetCard t univ).biUnion box) : K) := by
        exact_mod_cast card_le_card hsub
    _ ≤ ∑ T ∈ powersetCard t (univ : Finset ι), (#(box T) : K) := by
        exact_mod_cast card_biUnion_le
    _ ≤ ∑ _T ∈ powersetCard t (univ : Finset ι), a ^ t * N :=
        sum_le_sum fun T hTm => hT T (mem_powersetCard.1 hTm).2
    _ = (Fintype.card ι).choose t * a ^ t * N := by
        rw [sum_const, card_powersetCard, card_univ, nsmul_eq_mul, mul_assoc]

end Generic

/-! ### The random construction -/

section Construction

variable {n N k : ℕ}

/-- The random set `A'_i = {j | x j i < B}` (each `j` is in it with probability `B/k`). -/
def rowSet (B : ℕ) (x : Fin n → Fin N → Fin k) (i : Fin N) : Finset (Fin n) :=
  univ.filter fun j => ((x j i : ℕ) < B)

/-- The load `|{i ∈ I | j ∈ A'_i}|` of an element `j`, as a function of its column
`g = x j : Fin N → Fin k`. -/
def colLoad (B : ℕ) (I : Finset (Fin N)) (g : Fin N → Fin k) : ℕ :=
  #(I.filter fun i => ((g i : ℕ) < B))

/-- The column `g` of an element is bad for `I`: its load is outside `[(1-ε)B, (1+ε)B]`. -/
def ColBad (ε : ℝ) (B : ℕ) (I : Finset (Fin N)) (g : Fin N → Fin k) : Prop :=
  ¬ ((1 - ε) * B ≤ (colLoad B I g : ℝ) ∧ (colLoad B I g : ℝ) ≤ (1 + ε) * B)

/-- The set `s` violates Definition 1(1). -/
def RowBad (n k B : ℕ) (s : Finset (Fin n)) : Prop :=
  ¬ ((n * B : ℝ) / (2 * k) ≤ #s ∧ (#s : ℝ) ≤ 2 * n * B / k)

/-- `#{g : Fin N → Fin k | g i < B} · k = B · k^N`. -/
lemma card_filter_apply_lt_mul {B : ℕ} (hBk : B ≤ k) (i : Fin N) :
    (#(univ.filter fun g : Fin N → Fin k => (g i : ℕ) < B) : ℝ) * k = B * (k : ℝ) ^ N := by
  have e : univ.filter (fun g : Fin N → Fin k => (g i : ℕ) < B) =
      Fintype.piFinset (fun i' => if i' = i then univ.filter (fun y : Fin k => (y : ℕ) < B)
        else univ) := by
    ext g
    simp only [mem_filter, mem_univ, true_and, Fintype.mem_piFinset]
    constructor
    · intro hg i'
      split_ifs with h
      · subst h; simpa using hg
      · exact mem_univ _
    · intro hg
      simpa using hg i
  rw [e, Fintype.card_piFinset, ← mul_prod_erase _ _ (mem_univ i)]
  simp only [ite_true, Fin.card_filter_val_lt, min_eq_right hBk]
  have : ∏ x ∈ univ.erase i, #(if x = i then univ.filter (fun y : Fin k => (y : ℕ) < B)
      else (univ : Finset (Fin k))) = ∏ x ∈ univ.erase i, k := by
    refine prod_congr rfl fun x hx => ?_
    simp [ne_of_mem_erase hx]
  rw [this]
  push_cast
  rw [mul_assoc, prod_erase_mul _ _ (mem_univ i)]
  simp

open Classical in
/-- Definition 1(1) fails for a fixed random set `A'_i` with probability `≤ 8k/(nB)`
(Chebyshev). -/
lemma row_bound {B : ℕ} (hB : 0 < B) (hBk : B ≤ k) (hn : 0 < n) (i : Fin N) :
    (#(univ.filter fun x : Fin n → Fin N → Fin k => RowBad n k B (rowSet B x i)) : ℝ) *
      (n * B) ≤ 8 * k * Fintype.card (Fin n → Fin N → Fin k) := by
  have hk : 0 < k := lt_of_lt_of_le hB hBk
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hBR : (0 : ℝ) < B := by exact_mod_cast hB
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  set q : ℝ := B / k with hq
  have hq0 : 0 < q := by positivity
  have hq1 : q ≤ 1 := by rw [hq, div_le_one hkR]; exact_mod_cast hBk
  set Yc : ℝ := ((Fintype.card (Fin N → Fin k) : ℕ) : ℝ) with hYc
  have hY : Yc = (k : ℝ) ^ N := by simp [hYc]
  have hYpos : 0 < Yc := by rw [hY]; positivity
  have hP : (#(univ.filter fun g : Fin N → Fin k => (g i : ℕ) < B) : ℝ) = q * Yc := by
    have := card_filter_apply_lt_mul (N := N) hBk i
    rw [hY, hq]
    field_simp
    linarith
  let h : Fin n → (Fin N → Fin k) → ℝ := fun _ g => (if (g i : ℕ) < B then 1 else 0) - q
  have h0 : ∀ j, ∑ g, h j g = 0 := by
    intro j
    simp only [h, sum_sub_distrib, sum_boole, sum_const, card_univ, nsmul_eq_mul]
    rw [hP, ← hYc]; ring
  have hsq : ∀ j, ∑ g, h j g ^ 2 ≤ 2 * q * Yc := by
    intro j
    calc ∑ g, h j g ^ 2 ≤ ∑ g : Fin N → Fin k, ((if (g i : ℕ) < B then 1 else 0) + q ^ 2) := by
          refine sum_le_sum fun g _ => ?_
          simp only [h]
          split_ifs <;> nlinarith
      _ = q * Yc + q ^ 2 * Yc := by
          rw [sum_add_distrib, sum_boole, hP, sum_const, card_univ, nsmul_eq_mul, ← hYc]; ring
      _ ≤ 2 * q * Yc := by nlinarith
  have hcheb := card_le_abs_sum_apply_le (K := ℝ) n h h0 (δ := n * q / 2) (by positivity)
  have hsub : (univ.filter fun x : Fin n → Fin N → Fin k => RowBad n k B (rowSet B x i)) ⊆
      univ.filter fun g : Fin n → Fin N → Fin k => n * q / 2 ≤ |∑ j, h j (g j)| := by
    intro x hx
    simp only [mem_filter, mem_univ, true_and] at hx ⊢
    have hs : ∑ j, h j (x j) = (#(rowSet B x i) : ℝ) - n * q := by
      simp [h, sum_sub_distrib, sum_boole, rowSet]
    rw [hs]
    unfold RowBad at hx
    have e1 : (n * B : ℝ) / (2 * k) = n * q / 2 := by rw [hq]; field_simp
    have e2 : (2 * n * B : ℝ) / k = 2 * (n * q) := by rw [hq]; field_simp
    rw [e1, e2] at hx
    rcases not_and_or.1 hx with h1 | h1
    · rw [abs_of_neg (by push Not at h1; nlinarith)]; push Not at h1; nlinarith
    · push Not at h1; rw [abs_of_pos (by nlinarith)]; nlinarith
  have hcard := card_le_card hsub
  have hsum : ∑ j : Fin n, ∑ g, h j g ^ 2 ≤ n * (2 * q * Yc) := by
    calc ∑ j : Fin n, ∑ g, h j g ^ 2 ≤ ∑ _j : Fin n, 2 * q * Yc := sum_le_sum fun j _ => hsq j
      _ = n * (2 * q * Yc) := by simp
  have hΩ : ((Fintype.card (Fin n → Fin N → Fin k) : ℕ) : ℝ) = Yc ^ n := by
    simp [hYc]
  rw [hΩ]
  set c : ℝ := (#(univ.filter fun x : Fin n → Fin N → Fin k => RowBad n k B (rowSet B x i)) : ℝ)
  set c' : ℝ := (#(univ.filter fun g : Fin n → Fin N → Fin k => n * q / 2 ≤ |∑ j, h j (g j)|) : ℝ)
  have hcc : c ≤ c' := Nat.cast_le.mpr hcard
  rw [← hYc] at hcheb
  have key : c * (n * q) * (n * q * Yc) ≤ (8 * Yc ^ n) * (n * q * Yc) := by
    have : c * (n * q / 2) ^ 2 * Yc ≤ Yc ^ n * (n * (2 * q * Yc)) := by
      calc c * (n * q / 2) ^ 2 * Yc ≤ c' * (n * q / 2) ^ 2 * Yc := by gcongr
        _ ≤ Yc ^ n * ∑ j : Fin n, ∑ g, h j g ^ 2 := hcheb
        _ ≤ _ := by gcongr
    nlinarith
  have key2 : c * (n * q) ≤ 8 * Yc ^ n := le_of_mul_le_mul_right key (by positivity)
  have : c * (n * B) = c * (n * q) * k := by rw [hq]; field_simp
  rw [this]
  nlinarith

open Classical in
/-- For a fixed `k`-set `I`, the column of an element is bad with probability `≤ 2/(ε²B)`
(Chebyshev). -/
lemma col_bound {ε : ℝ} (hε : 0 < ε) {B : ℕ} (hB : 0 < B) (hBk : B ≤ k) (I : Finset (Fin N))
    (hI : #I = k) :
    (#(univ.filter (ColBad (k := k) ε B I)) : ℝ) * (ε ^ 2 * B) ≤
      2 * Fintype.card (Fin N → Fin k) := by
  have hk : 0 < k := lt_of_lt_of_le hB hBk
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hBR : (0 : ℝ) < B := by exact_mod_cast hB
  set q : ℝ := B / k with hq
  have hqk : q * k = B := by rw [hq]; field_simp
  have hq0 : 0 < q := by positivity
  have hq1 : q ≤ 1 := by rw [hq, div_le_one hkR]; exact_mod_cast hBk
  have hcB : (#(univ.filter fun y : Fin k => (y : ℕ) < B) : ℝ) = B := by
    rw [Fin.card_filter_val_lt, min_eq_right hBk]
  let h : Fin N → Fin k → ℝ := fun i y =>
    if i ∈ I then (if (y : ℕ) < B then 1 else 0) - q else 0
  have h0 : ∀ i, ∑ y, h i y = 0 := by
    intro i
    by_cases hi : i ∈ I
    · simp only [h, hi, ite_true, sum_sub_distrib, sum_boole, sum_const, card_univ,
        Fintype.card_fin, nsmul_eq_mul]
      rw [hcB, ← hqk]; ring
    · simp [h, hi]
  have hsq : ∀ i, ∑ y, h i y ^ 2 ≤ if i ∈ I then (2 * B : ℝ) else 0 := by
    intro i
    by_cases hi : i ∈ I
    · simp only [h, hi, ite_true]
      calc ∑ y : Fin k, ((if (y : ℕ) < B then (1 : ℝ) else 0) - q) ^ 2
          ≤ ∑ y : Fin k, ((if (y : ℕ) < B then 1 else 0) + q ^ 2) := by
            refine sum_le_sum fun g _ => ?_
            split_ifs <;> nlinarith
        _ = B + q * B := by
            rw [sum_add_distrib, sum_boole, hcB, sum_const, card_univ, Fintype.card_fin,
              nsmul_eq_mul, ← hqk]; ring
        _ ≤ 2 * B := by nlinarith
    · simp [h, hi]
  have hcheb := card_le_abs_sum_apply_le (K := ℝ) N h h0 (δ := ε * B) (by positivity)
  have hsub : univ.filter (ColBad (k := k) ε B I) ⊆
      univ.filter fun g : Fin N → Fin k => ε * B ≤ |∑ i, h i (g i)| := by
    intro g hg
    simp only [mem_filter, mem_univ, true_and] at hg ⊢
    have hs : ∑ i, h i (g i) = (colLoad B I g : ℝ) - B := by
      simp only [h]
      rw [← sum_filter, filter_mem_eq_inter, univ_inter, sum_sub_distrib, sum_boole, sum_const,
        hI, nsmul_eq_mul, mul_comm, hqk, colLoad]
    rw [hs]
    unfold ColBad at hg
    rcases not_and_or.1 hg with h1 | h1
    · push Not at h1; rw [abs_of_neg (by nlinarith)]; nlinarith
    · push Not at h1; rw [abs_of_pos (by nlinarith)]; nlinarith
  have hsum : ∑ i : Fin N, ∑ y, h i y ^ 2 ≤ k * (2 * B) := by
    calc ∑ i : Fin N, ∑ y, h i y ^ 2 ≤ ∑ i : Fin N, (if i ∈ I then (2 * B : ℝ) else 0) :=
          sum_le_sum fun i _ => hsq i
      _ = k * (2 * B) := by rw [sum_ite_mem, univ_inter, sum_const, hI, nsmul_eq_mul]
  set c : ℝ := (#(univ.filter (ColBad (k := k) ε B I)) : ℝ)
  set c' : ℝ := (#(univ.filter fun g : Fin N → Fin k => ε * B ≤ |∑ i, h i (g i)|) : ℝ)
  have hcc : c ≤ c' := Nat.cast_le.mpr (card_le_card hsub)
  have hΩ : ((Fintype.card (Fin N → Fin k) : ℕ) : ℝ) = (k : ℝ) ^ N := by simp
  rw [hΩ]
  simp only [Fintype.card_fin] at hcheb
  have key : c * (ε ^ 2 * B) * (B * k) ≤ 2 * (k : ℝ) ^ N * (B * k) := by
    calc c * (ε ^ 2 * B) * (B * k) = c * (ε * B) ^ 2 * k := by ring
      _ ≤ c' * (ε * B) ^ 2 * k := by gcongr
      _ ≤ (k : ℝ) ^ N * (k * (2 * B)) := hcheb.trans (by gcongr)
      _ = 2 * (k : ℝ) ^ N * (B * k) := by ring
  exact le_of_mul_le_mul_right key (by positivity)

open Classical in
/-- Selecting `m` good sets out of `2m`: if at most `m` of the random sets violate
Definition 1(1) and every `k`-set of indices has at most `εn` bad elements, then `m` of the sets
form a `(k, B, ε)`-load balancing covering family. -/
lemma exists_lbcf_of_good {ε : ℝ} {n m k B : ℕ} (x : Fin n → Fin (2 * m) → Fin k)
    (h1 : #(univ.filter fun i => RowBad n k B (rowSet B x i)) ≤ m)
    (h2 : ∀ I : Finset (Fin (2 * m)), #I = k →
      (#(univ.filter fun j => ColBad ε B I (x j)) : ℝ) ≤ ε * n) :
    ∃ A : Fin m → Finset (Fin n), IsLBCF n m k B ε A := by
  set G := univ.filter fun i => ¬ RowBad n k B (rowSet B x i) with hG
  have hGc : m ≤ #G := by
    have := card_filter_add_card_filter_not (s := (univ : Finset (Fin (2 * m))))
      (fun i => RowBad n k B (rowSet B x i))
    rw [card_univ, Fintype.card_fin, ← hG] at this
    omega
  obtain ⟨G', hG'G, hG'c⟩ := exists_subset_card_eq hGc
  let e := G'.orderEmbOfFin hG'c
  have he : ∀ ℓ, ¬ RowBad n k B (rowSet B x (e ℓ)) := fun ℓ =>
    (mem_filter.1 (hG'G (G'.orderEmbOfFin_mem hG'c ℓ))).2
  refine ⟨fun ℓ => rowSet B x (e ℓ), ⟨fun ℓ => (not_not.1 (he ℓ)).1,
    fun ℓ => (not_not.1 (he ℓ)).2, fun I hI => ?_⟩⟩
  set I' := I.map e.toEmbedding with hI'def
  have hI' : #I' = k := by rw [hI'def, card_map, hI]
  refine ⟨univ.filter fun j => ¬ ColBad ε B I' (x j), ?_, fun j hj => ?_⟩
  · have hsplit := card_filter_add_card_filter_not (s := (univ : Finset (Fin n)))
      (fun j => ColBad ε B I' (x j))
    rw [card_univ, Fintype.card_fin] at hsplit
    have h2' := h2 I' hI'
    have : ((#(univ.filter fun j => ¬ ColBad ε B I' (x j)) : ℕ) : ℝ) =
        n - #(univ.filter fun j => ColBad ε B I' (x j)) := by
      rw [eq_sub_iff_add_eq, add_comm]; exact_mod_cast hsplit
    rw [this]; linarith
  · rw [mem_filter] at hj
    have hl : load (fun ℓ => rowSet B x (e ℓ)) I j = colLoad B I' (x j) := by
      simp only [load, colLoad, hI'def, filter_map, card_map, rowSet, mem_filter, mem_univ,
        true_and]
      rfl
    rw [hl]
    exact not_not.1 hj.2

end Construction

/-- **Lemma 3.1, for every `n`.** Let `ε ∈ (0,1)`, `c = ε³/8` and `B = ⌈72/c⌉`. For any `n`,
any integer `m ≤ cn` and any `B ≤ k ≤ m`, there exists a `(k, B, ε)`-load balancing covering
family `A₁, …, A_m ⊆ [n]`. -/
theorem lemma_3_1_all_n {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) (n m k : ℕ)
    (hm : (m : ℝ) ≤ ε ^ 3 / 8 * n) (hBk : ⌈72 / (ε ^ 3 / 8)⌉₊ ≤ k) (hkm : k ≤ m) :
    ∃ A : Fin m → Finset (Fin n), IsLBCF n m k ⌈72 / (ε ^ 3 / 8)⌉₊ ε A := by
  classical
  set B := ⌈72 / (ε ^ 3 / 8)⌉₊ with hBdef
  have hε3 : 0 < ε ^ 3 := by positivity
  have hε31 : ε ^ 3 ≤ ε := by
    calc ε ^ 3 ≤ ε ^ 1 := pow_le_pow_of_le_one hε0.le hε1.le (by norm_num)
      _ = ε := pow_one ε
  have hBε : (576 : ℝ) ≤ ε ^ 3 * B := by
    have h := Nat.le_ceil (72 / (ε ^ 3 / 8))
    rw [← hBdef] at h
    have e : 72 / (ε ^ 3 / 8) = 576 / ε ^ 3 := by field_simp; norm_num
    rw [e, div_le_iff₀ hε3] at h; linarith
  have hBR : (576 : ℝ) ≤ B := by
    have : (0 : ℝ) ≤ B := Nat.cast_nonneg _
    nlinarith
  have hB : 0 < B := by exact_mod_cast (by linarith : (0 : ℝ) < B)
  have hk : 0 < k := lt_of_lt_of_le hB hBk
  have hm0 : 0 < m := lt_of_lt_of_le hk hkm
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm0
  have hnR : (0 : ℝ) < n := by
    by_contra hc
    have : (n : ℝ) = 0 := le_antisymm (not_lt.1 hc) (Nat.cast_nonneg _)
    rw [this, mul_zero] at hm; linarith
  have hn : 0 < n := by exact_mod_cast hnR
  have hkR : (k : ℝ) ≤ m := by exact_mod_cast hkm
  set t := ⌊ε * n⌋₊ + 1 with ht
  have htε : ε * n < t := by rw [ht]; push_cast; exact Nat.lt_floor_add_one _
  have h2m : 2 * m ≤ t := by
    have : ((2 * m : ℕ) : ℝ) < t := by push_cast; nlinarith
    exact_mod_cast this.le
  have ht0 : t ≠ 0 := by rw [ht]; omega
  have : Nonempty (Fin n → Fin (2 * m) → Fin k) := ⟨fun _ _ => ⟨0, hk⟩⟩
  set Ωc : ℝ := (Fintype.card (Fin n → Fin (2 * m) → Fin k) : ℝ) with hΩc
  have hΩ : 0 < Ωc := by rw [hΩc]; exact_mod_cast Fintype.card_pos
  -- the two bad events
  let E1 : (Fin n → Fin (2 * m) → Fin k) → Prop := fun x =>
    m + 1 ≤ #(univ.filter fun i => RowBad n k B (rowSet B x i))
  let E2 : (Fin n → Fin (2 * m) → Fin k) → Prop := fun x =>
    ∃ I ∈ powersetCard k (univ : Finset (Fin (2 * m))),
      t ≤ #(univ.filter fun j => ColBad ε B I (x j))
  -- Definition 1(1) fails for more than `m` sets with probability `≤ 1/288` (Markov)
  have hE1 : (#(univ.filter E1) : ℝ) ≤ 1 / 288 * Ωc := by
    have hrow : ∀ i : Fin (2 * m), (#(univ.filter fun x : Fin n → Fin (2 * m) → Fin k =>
        RowBad n k B (rowSet B x i)) : ℝ) ≤ Ωc / 576 := by
      intro i
      have h := row_bound (N := 2 * m) hB hBk hn i
      set c : ℝ := (#(univ.filter fun x : Fin n → Fin (2 * m) → Fin k =>
        RowBad n k B (rowSet B x i)) : ℝ)
      have hc0 : 0 ≤ c := Nat.cast_nonneg _
      have h8 : (8 * k : ℝ) ≤ n := by nlinarith
      have h' : c * B * n ≤ Ωc * n := by
        calc c * B * n = c * (n * B) := by ring
          _ ≤ 8 * k * Ωc := h
          _ ≤ n * Ωc := by gcongr
          _ = Ωc * n := by ring
      have h'' : c * B ≤ Ωc := le_of_mul_le_mul_right h' hnR
      rw [le_div_iff₀ (by norm_num)]
      nlinarith
    have markov : (m + 1) * #(univ.filter E1) ≤ ∑ i : Fin (2 * m),
        #(univ.filter fun x : Fin n → Fin (2 * m) → Fin k => RowBad n k B (rowSet B x i)) := by
      calc (m + 1) * #(univ.filter E1) = ∑ _x ∈ univ.filter E1, (m + 1) := by
            rw [sum_const, smul_eq_mul, mul_comm]
        _ ≤ ∑ x ∈ univ.filter E1, #(univ.filter fun i => RowBad n k B (rowSet B x i)) :=
            sum_le_sum fun x hx => (mem_filter.1 hx).2
        _ ≤ ∑ x, #(univ.filter fun i => RowBad n k B (rowSet B x i)) :=
            sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _ => Nat.zero_le _)
        _ = _ := by simp only [card_eq_sum_ones, sum_filter]; exact sum_comm
    have markovR : ((m : ℝ) + 1) * #(univ.filter E1) ≤ 2 * m * (Ωc / 576) := by
      have := (Nat.cast_le (α := ℝ)).2 markov
      push_cast at this
      refine this.trans ?_
      calc (∑ i : Fin (2 * m), (#(univ.filter fun x : Fin n → Fin (2 * m) → Fin k =>
            RowBad n k B (rowSet B x i)) : ℝ)) ≤ ∑ _i : Fin (2 * m), Ωc / 576 :=
            sum_le_sum fun i _ => hrow i
        _ = 2 * m * (Ωc / 576) := by simp
    have : ((m : ℝ) + 1) * #(univ.filter E1) ≤ ((m : ℝ) + 1) * (1 / 288 * Ωc) := by
      nlinarith
    exact le_of_mul_le_mul_left this (by positivity)
  -- Definition 1(2) fails for some `k`-set with probability `≤ 1/50`
  have hE2 : (#(univ.filter E2) : ℝ) ≤ 1 / 50 * Ωc := by
    set a : ℝ := 2 / (ε ^ 2 * B) with ha
    have ha0 : 0 ≤ a := by positivity
    have hcol : ∀ I ∈ powersetCard k (univ : Finset (Fin (2 * m))),
        (#(univ.filter fun x : Fin n → Fin (2 * m) → Fin k =>
          t ≤ #(univ.filter fun j => ColBad ε B I (x j))) : ℝ) ≤ n.choose t * a ^ t * Ωc := by
      intro I hI
      have hIc := (mem_powersetCard.1 hI).2
      have := card_many_le_choose (K := ℝ) (ι := Fin n) (β := fun _ => Fin (2 * m) → Fin k)
        (fun _ => ColBad ε B I) (a := a) (fun _ => ?_) t
      · rw [hΩc]; simpa using this
      have hc := col_bound hε0 hB hBk I hIc
      rw [ha, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
      exact hc
    have hunion : univ.filter E2 = (powersetCard k (univ : Finset (Fin (2 * m)))).biUnion
        fun I => univ.filter fun x : Fin n → Fin (2 * m) → Fin k =>
          t ≤ #(univ.filter fun j => ColBad ε B I (x j)) := by
      ext x; simp [E2]
    have hchoose : (((2 * m).choose k : ℕ) : ℝ) ≤ 2 ^ t := by
      have := Nat.choose_le_two_pow (2 * m) k
      have h2 : 2 ^ (2 * m) ≤ 2 ^ t := Nat.pow_le_pow_right (by norm_num) h2m
      exact_mod_cast this.trans h2
    have hna : (n : ℝ) * a ≤ t / 288 := by
      rw [ha, mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
      have : ε * n * (ε ^ 2 * B) ≤ t * (ε ^ 2 * B) := by gcongr
      nlinarith
    have htpos : (0 : ℝ) < t := by positivity
    have hct : (n.choose t : ℝ) * a ^ t ≤ (Real.exp 1 / 288) ^ t := by
      have h1 := Nat.choose_le_pow_div (α := ℝ) t n
      calc (n.choose t : ℝ) * a ^ t ≤ (n : ℝ) ^ t / t.factorial * a ^ t := by gcongr
        _ = (n * a) ^ t / t.factorial := by rw [mul_pow]; ring
        _ ≤ (t / 288) ^ t / t.factorial := by gcongr
        _ = (1 / 288) ^ t * ((t : ℝ) ^ t / t.factorial) := by
            rw [div_pow, div_pow, one_pow]; ring
        _ ≤ (1 / 288) ^ t * Real.exp t := by
            gcongr; exact Real.pow_div_factorial_le_exp _ htpos.le _
        _ = (Real.exp 1 / 288) ^ t := by
            rw [← Real.exp_one_pow, div_pow, div_pow, one_pow]; ring
    have he1 := Real.exp_one_lt_d9
    have hbase : 2 * Real.exp 1 / 288 ≤ 1 := by linarith
    calc (#(univ.filter E2) : ℝ)
        ≤ ∑ I ∈ powersetCard k (univ : Finset (Fin (2 * m))),
            (#(univ.filter fun x : Fin n → Fin (2 * m) → Fin k =>
              t ≤ #(univ.filter fun j => ColBad ε B I (x j))) : ℝ) := by
          rw [hunion]; exact_mod_cast card_biUnion_le
      _ ≤ ∑ _I ∈ powersetCard k (univ : Finset (Fin (2 * m))), n.choose t * a ^ t * Ωc :=
          sum_le_sum hcol
      _ = (((2 * m).choose k : ℕ) : ℝ) * (n.choose t * a ^ t) * Ωc := by
          rw [sum_const, card_powersetCard, card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
      _ ≤ 2 ^ t * (Real.exp 1 / 288) ^ t * Ωc := by gcongr
      _ = (2 * Real.exp 1 / 288) ^ t * Ωc := by rw [← mul_pow]; ring
      _ ≤ (2 * Real.exp 1 / 288) * Ωc := by
          gcongr; exact pow_le_of_le_one (by positivity) hbase ht0
      _ ≤ 1 / 50 * Ωc := mul_le_mul_of_nonneg_right (by linarith) hΩ.le
  -- probabilistic method
  have hlt : #(univ.filter fun x => E1 x ∨ E2 x) < Fintype.card (Fin n → Fin (2 * m) → Fin k) := by
    have h := card_union_le (univ.filter E1) (univ.filter E2)
    rw [← filter_or] at h
    have : (#(univ.filter fun x => E1 x ∨ E2 x) : ℝ) < Ωc := by
      have : (#(univ.filter fun x => E1 x ∨ E2 x) : ℝ) ≤ #(univ.filter E1) + #(univ.filter E2) := by
        exact_mod_cast h
      linarith
    rw [hΩc] at this
    exact_mod_cast this
  obtain ⟨x, hx⟩ : ∃ x, ¬ (E1 x ∨ E2 x) := by
    by_contra hcon
    push Not at hcon
    have : univ.filter (fun x => E1 x ∨ E2 x) = univ := filter_true_of_mem fun x _ => hcon x
    rw [this, card_univ] at hlt
    exact lt_irrefl _ hlt
  rw [not_or] at hx
  refine exists_lbcf_of_good x (by have := hx.1; simp only [E1, not_le] at this; omega)
    fun I hI => ?_
  have h2 := hx.2
  simp only [E2, not_exists, not_and, not_le] at h2
  have hlt' := h2 I (mem_powersetCard.2 ⟨subset_univ _, hI⟩)
  have hle : #(univ.filter fun j => ColBad ε B I (x j)) ≤ ⌊ε * n⌋₊ := by omega
  calc (#(univ.filter fun j => ColBad ε B I (x j)) : ℝ) ≤ ⌊ε * n⌋₊ := by exact_mod_cast hle
    _ ≤ ε * n := Nat.floor_le (by positivity)

/-- **Lemma 3.1.** Let `ε ∈ (0,1)`, `c = ε³/8` and `B = ⌈72/c⌉`. For any sufficiently large `n`,
any integer `m ≤ cn` and any `B ≤ k ≤ m`, there exists a `(k, B, ε)`-load balancing covering
family `A₁, …, A_m ⊆ [n]`. -/
theorem lemma_3_1 {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ m k : ℕ, (m : ℝ) ≤ ε ^ 3 / 8 * n → ⌈72 / (ε ^ 3 / 8)⌉₊ ≤ k → k ≤ m →
      ∃ A : Fin m → Finset (Fin n), IsLBCF n m k ⌈72 / (ε ^ 3 / 8)⌉₊ ε A :=
  ⟨0, fun n _ m k hm hBk hkm => lemma_3_1_all_n hε0 hε1 n m k hm hBk hkm⟩

end Podc.TaskCompletion
