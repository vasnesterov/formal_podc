import Mathlib

-- CSLib candidate (general, not specific to this paper)

/-!
# Combinatorics of sample sort (Lemma 4.3 of Lenzen, PODC 2013)

This file contains the purely order-theoretic and arithmetic facts behind the sample-sort step
of Lenzen's sorting algorithm on the congested clique ("Optimal deterministic routing and
sorting on the congested clique", PODC 2013, Section 4):

* `rk H x` is the rank of `x` in a finite set `H` (number of elements of `H` below `x`); on `H`
  it is a strictly monotone bijection onto `range |H|` (`rk_lt_rk`, `image_rk`), which lets us
  transfer counting statements about `H` to statements about `Finset.range` (`card_filter_rk`).
* `samples H p` are the elements at positions `p-1, 2p-1, …` of the sorted `H`; there are
  `|H| / p` of them (`card_samples`).
* `delims U q k` are the elements of `U` at positions `q-1, 2q-1, …, (k-1)q-1`, and
  `bucketOf D x` is the number of delimiters below `x`. For `x ∈ U`, the bucket index is
  `min (rk U x / q) (k-1)` (`bucketOf_delims`); if `|U| ≤ q k`, every bucket receives at most
  `q` elements of `U` (`card_fiber_bucketOf_delims`).
* The segment lemma `card_filter_add_one_le`: the elements of `H` in a fibre of a monotone map
  form a contiguous block of positions, so a fibre with `m` elements of `H` contains at least
  `m / p` samples. Summed over disjoint sets this is Lemma 4.3 (`sum_bucket_le`).
-/

namespace CongestedCliqueRouting

open Finset

section Arith

/-- `n ≡ q - 1 (mod q)` iff `q ∣ n + 1`. -/
lemma mod_eq_pred_iff_dvd {q : ℕ} (hq : 0 < q) (n : ℕ) : n % q = q - 1 ↔ q ∣ n + 1 := by
  constructor
  · intro h
    refine ⟨n / q + 1, ?_⟩
    have := Nat.mod_add_div n q
    rw [mul_add]
    omega
  · rintro ⟨c, hc⟩
    cases c with
    | zero => simp at hc
    | succ d =>
      have : n = (q - 1) + q * d := by rw [mul_add] at hc; omega
      rw [this, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]

/-- Among `0, …, n-1` exactly `n / q` numbers are `≡ q - 1 (mod q)`. -/
lemma count_mod_eq_pred {q : ℕ} (hq : 0 < q) (n : ℕ) :
    Nat.count (fun r => r % q = q - 1) n = n / q := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.count_succ, ih, Nat.succ_div]
    simp only [mod_eq_pred_iff_dvd hq]

/-- Among `0, …, n-1` exactly `n / q` numbers are `≡ q - 1 (mod q)`. -/
lemma card_range_filter_mod {q : ℕ} (hq : 0 < q) (n : ℕ) :
    ((range n).filter fun r => r % q = q - 1).card = n / q := by
  rw [← Nat.count_eq_card_filter_range, count_mod_eq_pred hq]

/-- In the block `[a, a + m)` exactly `(a + m) / q - a / q` numbers are `≡ q - 1 (mod q)`. -/
lemma card_range_filter_shift_mod {q : ℕ} (hq : 0 < q) (a m : ℕ) :
    ((range m).filter fun r => (a + r) % q = q - 1).card = (a + m) / q - a / q := by
  rw [← Nat.count_eq_card_filter_range]
  have := Nat.count_add (fun r => r % q = q - 1) a m
  rw [count_mod_eq_pred hq, count_mod_eq_pred hq] at this
  omega

lemma div_le_add_div_sub_div (a m q : ℕ) : m / q ≤ (a + m) / q - a / q := by
  have := (Nat.div_add_div_le_add_div (x := a) (y := m) (z := q))
  omega

lemma add_div_sub_div_le {q : ℕ} (hq : 0 < q) (a m : ℕ) :
    (a + m) / q - a / q ≤ m / q + 1 := by
  rw [Nat.add_div hq]
  generalize a / q = A
  generalize m / q = B
  split_ifs <;> omega

end Arith

variable {M : Type*} [LinearOrder M]

/-- Rank of `x` in `H`: number of elements of `H` below `x`. -/
def rk (H : Finset M) (x : M) : ℕ := (H.filter (· < x)).card

/-- Samples of `H` with step `p`: the elements at positions `p-1, 2p-1, …` of the sorted `H`. -/
def samples (H : Finset M) (p : ℕ) : Finset M := H.filter fun x => rk H x % p = p - 1

/-- Delimiters: elements of `U` at positions `q-1, 2q-1, …, (k-1)q-1`. -/
def delims (U : Finset M) (q k : ℕ) : Finset M :=
  U.filter fun x => rk U x % q = q - 1 ∧ rk U x < (k - 1) * q

/-- Bucket index of `x` w.r.t. delimiters `D`: number of delimiters below `x`. -/
def bucketOf (D : Finset M) (x : M) : ℕ := (D.filter (· < x)).card

/-! ### Ranks -/

/-- The rank is monotone (on all of `M`). -/
theorem rk_mono (H : Finset M) {x y : M} (h : x ≤ y) : rk H x ≤ rk H y := by
  apply card_le_card
  intro z hz
  simp only [mem_filter] at hz ⊢
  exact ⟨hz.1, hz.2.trans_le h⟩

/-- The rank is strictly increasing from elements of `H`. -/
theorem rk_lt_rk_of_lt (H : Finset M) {x y : M} (hx : x ∈ H) (h : x < y) : rk H x < rk H y := by
  apply card_lt_card
  have hsub : H.filter (· < x) ⊆ H.filter (· < y) := by
    intro z hz
    simp only [mem_filter] at hz ⊢
    exact ⟨hz.1, hz.2.trans h⟩
  refine (ssubset_iff_of_subset hsub).2 ⟨x, mem_filter.2 ⟨hx, h⟩, ?_⟩
  simp

/-- Ranks of elements of `H` are `< |H|`. -/
theorem rk_lt_card {H : Finset M} {x : M} (hx : x ∈ H) : rk H x < H.card :=
  card_lt_card (filter_ssubset.2 ⟨x, hx, lt_irrefl x⟩)

/-- On `H`, the rank is order-reflecting and order-preserving. -/
theorem rk_lt_rk {H : Finset M} {x y : M} (hx : x ∈ H) (_hy : y ∈ H) :
    rk H x < rk H y ↔ x < y := by
  refine ⟨fun h => lt_of_not_ge fun h' => ?_, rk_lt_rk_of_lt H hx⟩
  have := rk_mono H h'
  omega

/-- The rank is injective on `H`. -/
theorem rk_injOn (H : Finset M) : Set.InjOn (rk H) H := by
  intro x hx y hy hxy
  rcases lt_trichotomy x y with h | h | h
  · exact absurd hxy (rk_lt_rk_of_lt H hx h).ne
  · exact h
  · exact absurd hxy (rk_lt_rk_of_lt H hy h).ne'

/-- The ranks of the elements of `H` are exactly `0, …, |H| - 1`. -/
theorem image_rk (H : Finset M) : H.image (rk H) = range H.card := by
  apply eq_of_subset_of_card_le
  · intro r hr
    obtain ⟨x, hx, rfl⟩ := mem_image.1 hr
    exact mem_range.2 (rk_lt_card hx)
  · rw [card_range, card_image_of_injOn (rk_injOn H)]

/-- Transfer of counting statements: counting the elements of `H` whose rank satisfies `P` is
the same as counting the numbers `< |H|` satisfying `P`. -/
theorem card_filter_rk (H : Finset M) (P : ℕ → Prop) [DecidablePred P] :
    (H.filter fun x => P (rk H x)).card = ((range H.card).filter P).card := by
  rw [← image_rk H, filter_image,
    card_image_of_injOn ((rk_injOn H).mono (coe_subset.2 (filter_subset _ _)))]

/-- Rank decomposition along a monotone map `f`: the rank of `x` in `H` is the number of
elements of `H` in lower fibres of `f` plus the rank of `x` inside its own fibre. -/
theorem rk_eq_add {H : Finset M} {f : M → ℕ} (hf : Monotone f) {x : M} (_hx : x ∈ H) :
    rk H x = (H.filter fun y => f y < f x).card + rk (H.filter fun y => f y = f x) x := by
  unfold rk
  rw [filter_filter, ← card_union_of_disjoint]
  · congr 1
    ext y
    simp only [mem_filter, mem_union]
    constructor
    · rintro ⟨hy, hyx⟩
      rcases (hf hyx.le).lt_or_eq with h | h
      · exact Or.inl ⟨hy, h⟩
      · exact Or.inr ⟨hy, h, hyx⟩
    · rintro (⟨hy, h⟩ | ⟨hy, _, hyx⟩)
      · refine ⟨hy, lt_of_not_ge fun h' => ?_⟩
        have := hf h'
        omega
      · exact ⟨hy, hyx⟩
  · rw [disjoint_filter]
    intro y _ h1 h2
    omega

/-- Spreading: in `K`, at most `⌈|K| / s⌉` elements have rank `≡ y (mod s)`. -/
theorem card_rk_mod_le (K : Finset M) {s : ℕ} (hs : 0 < s) (y : ℕ) :
    (K.filter fun x => rk K x % s = y).card ≤ (K.card + s - 1) / s := by
  rw [card_filter_rk K (fun r => r % s = y)]
  calc _ ≤ (range ((K.card + s - 1) / s)).card := by
        apply card_le_card_of_injOn (fun r => r / s)
        · intro r hr
          simp only [coe_filter, mem_range, Set.mem_ofPred_eq, coe_range, Set.mem_Iio] at hr ⊢
          rw [Nat.lt_iff_add_one_le, Nat.le_div_iff_mul_le hs, add_mul, one_mul]
          have := Nat.div_mul_le_self r s
          omega
        · intro r1 h1 r2 h2 he
          simp only [coe_filter, mem_range, Set.mem_ofPred_eq] at h1 h2 he
          have e1 := Nat.div_add_mod r1 s
          have e2 := Nat.div_add_mod r2 s
          rw [he] at e1
          omega
    _ = _ := card_range _

/-- The ranks of the elements of `H` in the fibre `f ⁻¹ {j}` of a monotone `f` form the block
`[a, a + m)`; counting those `≡ p - 1 (mod p)`. -/
lemma card_rk_mod_fiber (H : Finset M) {f : M → ℕ} (hf : Monotone f) (j : ℕ) {p : ℕ}
    (hp : 0 < p) :
    (H.filter fun x => rk H x % p = p - 1 ∧ f x = j).card =
      ((H.filter fun x => f x < j).card + (H.filter fun x => f x = j).card) / p
        - (H.filter fun x => f x < j).card / p := by
  have hr : ∀ x ∈ H, f x = j →
      rk H x = (H.filter fun y => f y < j).card + rk (H.filter fun y => f y = j) x := by
    intro x hx hxj
    rw [rk_eq_add hf hx, hxj]
  have : (H.filter fun x => rk H x % p = p - 1 ∧ f x = j) =
      (H.filter fun x => f x = j).filter fun x =>
        ((H.filter fun y => f y < j).card + rk (H.filter fun y => f y = j) x) % p = p - 1 := by
    ext x
    simp only [mem_filter]
    constructor
    · rintro ⟨hx, h1, h2⟩
      exact ⟨⟨hx, h2⟩, by rw [← hr x hx h2]; exact h1⟩
    · rintro ⟨⟨hx, h2⟩, h1⟩
      exact ⟨hx, by rw [hr x hx h2]; exact h1, h2⟩
  rw [this, card_filter_rk _ (fun r => ((H.filter fun y => f y < j).card + r) % p = p - 1),
    card_range_filter_shift_mod hp]

/-! ### Samples -/

/-- There are `⌊|H| / p⌋` samples. -/
theorem card_samples (H : Finset M) {p : ℕ} (hp : 0 < p) : (samples H p).card = H.card / p := by
  unfold samples
  rw [card_filter_rk H (fun r => r % p = p - 1), card_range_filter_mod hp]

/-- The rank of a sample among the samples is `< ⌊|H| / p⌋` (used to select the `i`-th
sample). -/
theorem rk_samples_lt {H : Finset M} {p : ℕ} (hp : 0 < p) {x : M} (hx : x ∈ samples H p) :
    rk (samples H p) x < H.card / p :=
  card_samples H hp ▸ rk_lt_card hx

/-- Segment lemma: a fibre of a monotone map containing `m` elements of `H` contains at least
`⌊m / p⌋` samples of `H`; in the form `m + 1 ≤ p (s + 1)`. -/
theorem card_filter_add_one_le {H : Finset M} {p : ℕ} (hp : 0 < p) {f : M → ℕ}
    (hf : Monotone f) (j : ℕ) :
    (H.filter fun x => f x = j).card + 1 ≤
      p * (((samples H p).filter fun x => f x = j).card + 1) := by
  have e : (samples H p).filter (fun x => f x = j) =
      H.filter fun x => rk H x % p = p - 1 ∧ f x = j := by
    unfold samples
    rw [filter_filter]
  rw [e, card_rk_mod_fiber H hf j hp]
  have h1 := div_le_add_div_sub_div (H.filter fun x => f x < j).card
    (H.filter fun x => f x = j).card p
  have h2 := Nat.lt_mul_div_succ (H.filter fun x => f x = j).card hp
  calc _ ≤ p * ((H.filter fun x => f x = j).card / p + 1) := h2
    _ ≤ _ := Nat.mul_le_mul_left _ (by omega)

/-- Lemma 4.3 of [Lenzen 2013] (summed form). Let `H i` be pairwise disjoint sets of keys (the
keys held by node `i`), each node choosing every `p`-th of its keys as a sample, and let `f` be a
monotone bucket map. If the fibre `f ⁻¹ {j}` contains `s` samples in total, it contains at most
`p (s + |ι|) - |ι|` keys. -/
theorem sum_bucket_le {ι : Type*} [Fintype ι] {H : ι → Finset M}
    (hH : ∀ i i', i ≠ i' → Disjoint (H i) (H i')) {p : ℕ} (hp : 0 < p) {f : M → ℕ}
    (hf : Monotone f) (j : ℕ) :
    ∑ i, ((H i).filter fun x => f x = j).card + Fintype.card ι ≤
      p * (((Finset.univ.biUnion fun i => samples (H i) p).filter fun x => f x = j).card +
        Fintype.card ι) := by
  rw [filter_biUnion, card_biUnion]
  · calc ∑ i, ((H i).filter fun x => f x = j).card + Fintype.card ι
          = ∑ i, (((H i).filter fun x => f x = j).card + 1) := by
            rw [sum_add_distrib, sum_const, card_univ, smul_eq_mul, mul_one]
        _ ≤ ∑ i, p * (((samples (H i) p).filter fun x => f x = j).card + 1) :=
            sum_le_sum fun i _ => card_filter_add_one_le hp hf j
        _ = _ := by
            rw [← mul_sum, sum_add_distrib, sum_const, card_univ, smul_eq_mul, mul_one]
  · intro i _ i' _ hii'
    exact Disjoint.mono ((filter_subset _ _).trans (filter_subset _ _))
      ((filter_subset _ _).trans (filter_subset _ _)) (hH i i' hii')

/-! ### Delimiters and buckets -/

/-- Bucket indices are monotone. -/
theorem bucketOf_mono (D : Finset M) {x y : M} (h : x ≤ y) : bucketOf D x ≤ bucketOf D y :=
  rk_mono D h

/-- There are at most `k - 1` delimiters. -/
theorem card_delims_le (U : Finset M) (q k : ℕ) : (delims U q k).card ≤ k - 1 := by
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · simp [delims]
  unfold delims
  rw [card_filter_rk U (fun r => r % q = q - 1 ∧ r < (k - 1) * q)]
  calc _ ≤ ((range ((k - 1) * q)).filter fun r => r % q = q - 1).card := by
        apply card_le_card
        intro r
        simp only [mem_filter, mem_range]
        tauto
    _ = k - 1 := by rw [card_range_filter_mod hq, Nat.mul_div_cancel _ hq]

/-- Bucket indices w.r.t. `delims U q k` are at most `k - 1`. -/
theorem bucketOf_delims_le {U : Finset M} {q k : ℕ} (x : M) :
    bucketOf (delims U q k) x ≤ k - 1 :=
  (card_le_card (filter_subset _ _)).trans (card_delims_le U q k)

/-- The bucket of an element `x ∈ U` w.r.t. `delims U q k` is `min (⌊rk U x / q⌋) (k - 1)`. -/
theorem bucketOf_delims {U : Finset M} {q k : ℕ} {x : M} (hq : 0 < q) (hx : x ∈ U) :
    bucketOf (delims U q k) x = min (rk U x / q) (k - 1) := by
  unfold bucketOf delims
  rw [filter_filter]
  have : (U.filter fun z => (rk U z % q = q - 1 ∧ rk U z < (k - 1) * q) ∧ z < x) =
      U.filter fun z => rk U z % q = q - 1 ∧ rk U z < min (rk U x) ((k - 1) * q) := by
    apply filter_congr
    intro z hz
    rw [← rk_lt_rk hz hx, lt_min_iff]
    tauto
  rw [this, card_filter_rk U (fun r => r % q = q - 1 ∧ r < min (rk U x) ((k - 1) * q))]
  have h2 : ((range U.card).filter fun r => r % q = q - 1 ∧ r < min (rk U x) ((k - 1) * q)) =
      (range (min (rk U x) ((k - 1) * q))).filter fun r => r % q = q - 1 := by
    ext r
    simp only [mem_filter, mem_range, lt_min_iff]
    have := rk_lt_card hx
    omega
  rw [h2, card_range_filter_mod hq]
  rcases le_total (rk U x) ((k - 1) * q) with h | h
  · rw [min_eq_left h, min_eq_left]
    exact Nat.div_le_of_le_mul (by rwa [mul_comm])
  · rw [min_eq_right h, min_eq_right, Nat.mul_div_cancel _ hq]
    exact (Nat.le_div_iff_mul_le hq).2 h

/-- If `|U| ≤ q k`, every bucket w.r.t. `delims U q k` contains at most `q` elements of `U`. -/
theorem card_fiber_bucketOf_delims {U : Finset M} {q k : ℕ} (hq : 0 < q) (hU : U.card ≤ q * k)
    (j : ℕ) : (U.filter fun x => bucketOf (delims U q k) x = j).card ≤ q := by
  have : (U.filter fun x => bucketOf (delims U q k) x = j) =
      U.filter fun x => min (rk U x / q) (k - 1) = j := by
    apply filter_congr
    intro x hx
    rw [bucketOf_delims hq hx]
  rw [this, card_filter_rk U (fun r => min (r / q) (k - 1) = j)]
  calc _ ≤ (Ico (j * q) (j * q + q)).card := by
        apply card_le_card
        intro r
        simp only [mem_filter, mem_range, mem_Ico]
        rintro ⟨hr, hj⟩
        have e1 := Nat.div_add_mod r q
        have e2 := Nat.mod_lt r hq
        rcases le_total (r / q) (k - 1) with h | h
        · rw [min_eq_left h] at hj
          subst hj
          rw [mul_comm]
          generalize r / q = d at *
          generalize r % q = e at *
          omega
        · rw [min_eq_right h] at hj
          subst hj
          obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by
            rcases Nat.eq_zero_or_pos k with rfl | hk
            · rw [mul_zero] at hU; omega
            · omega⟩
          simp only [Nat.add_sub_cancel] at h ⊢
          generalize r / q = d at *
          generalize r % q = e at *
          have : q * k' ≤ q * d := Nat.mul_le_mul_left q h
          rw [mul_add, mul_one] at hU
          rw [mul_comm]
          omega
    _ = q := by simp

/-- Delimiters in a block: a fibre of a monotone map containing `L` elements of `U` contains at
most `⌊L / q⌋ + 1` delimiters. -/
theorem card_delims_filter_le {U : Finset M} {q k : ℕ} (hq : 0 < q) {f : M → ℕ}
    (hf : Monotone f) (j : ℕ) :
    ((delims U q k).filter fun x => f x = j).card ≤ (U.filter fun x => f x = j).card / q + 1 := by
  calc _ ≤ (U.filter fun x => rk U x % q = q - 1 ∧ f x = j).card := by
        apply card_le_card
        intro x
        simp only [delims, mem_filter]
        tauto
    _ = _ := card_rk_mod_fiber U hf j hq
    _ ≤ _ := add_div_sub_div_le hq _ _

end CongestedCliqueRouting
