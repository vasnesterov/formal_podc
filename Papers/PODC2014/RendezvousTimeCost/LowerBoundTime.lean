import Papers.PODC2014.RendezvousTimeCost.Ring

/-!
# Theorem 3.2 of Miller–Pelc: fast rendezvous is expensive (repaired proof)

Theorem 3.2 of [Miller, Pelc, *Time versus cost tradeoffs for deterministic rendezvous in
networks*, PODC 2014]: in the oriented ring of size `n` (`E = n - 1`) with simultaneous start,
every deterministic rendezvous algorithm for `L` labels with time `O(E log L)` has cost
`Ω(E log L)`.

## The repair

The paper cuts the ring into 6 sectors of size `n/6` and time into blocks of `n/6` rounds, and
encodes each agent by the sequence of sectors visited at block boundaries (its "progress
vector"). Its Fact 3.11 claims that two agents with the same progress vector, started at
antipodal nodes, never meet. This is false: knowing the sector of an agent only at block
boundaries does not confine it mid-block (an agent at the end of `P_{j+1}` may enter `P_{j+2}`
mid-block and come back), so the two agents can meet.

We use a repaired argument with more slack, entirely in terms of displacements on `ℤ` (no
sector arithmetic mod 6; any `n ≥ 10` works):
* blocks and sectors have length `s = n / 10`; the *sector walk* of agent `x` is
  `σ_x(k) = ⌊d_x(k s) / s⌋`, where `d_x` is the trimmed displacement `tdisp` (it moves by at
  most one sector per block);
* the progress vector `J_x ∈ {-1, 0, 1}^K` records the jumps of a greedy anchor that follows
  `σ_x` with hysteresis 2 (`LBTime.anc`, `LBTime.jmp`); the anchor is `2 * Σ_{i<k} J_x(i)`,
  so equal progress vectors give `|σ_x(k) - σ_y(k)| ≤ 2` at all block boundaries;
* hence two agents with equal progress vectors stay within distance `< 5 s ≤ n / 2` of each
  other's (relative) start for the whole time `K s ≥ T`, so started at distance `n / 2` they do
  not meet: distinct labels have distinct progress vectors;
* every jump costs at least `s + 1` edge traversals (the displacement since the last jump
  changes by more than `s`);
* there are few vectors with fewer than `k` jumps
  (`#{J | #supp J < k} ≤ λ^{-k} (1 + 2λ)^K`), so some label makes at least `k` jumps.
-/

namespace Podc.RendezvousTimeCost

open Finset

namespace LBTime

/-! ### Greedy anchors and jumps of an integer walk -/

/-- Greedy anchor following the walk `σ` with hysteresis `2`. -/
def anc (σ : ℕ → ℤ) : ℕ → ℤ
  | 0 => 0
  | k + 1 => if 2 ≤ |σ (k + 1) - anc σ k| then σ (k + 1) else anc σ k

/-- The jump of the anchor between block boundaries `k` and `k + 1`. -/
def jmp (σ : ℕ → ℤ) (k : ℕ) : SignType :=
  if 2 ≤ |σ (k + 1) - anc σ k| then SignType.sign (σ (k + 1) - anc σ k) else 0

/-- Number of jumps among the first `k` blocks. -/
def cnt (σ : ℕ → ℤ) (k : ℕ) : ℕ := ∑ i ∈ range k, if jmp σ i = 0 then 0 else 1

lemma anc_inv (σ : ℕ → ℤ) (h0 : σ 0 = 0) (h1 : ∀ k, |σ (k + 1) - σ k| ≤ 1) :
    ∀ k, |σ k - anc σ k| ≤ 1
  | 0 => by simp [anc, h0]
  | k + 1 => by
    have ih := anc_inv σ h0 h1 k
    simp only [anc]
    split_ifs with h
    · simp
    · push Not at h
      rw [abs_lt] at h
      rw [abs_le]; omega

lemma jmp_ne_zero_iff (σ : ℕ → ℤ) (k : ℕ) :
    jmp σ k ≠ 0 ↔ 2 ≤ |σ (k + 1) - anc σ k| := by
  unfold jmp
  split_ifs with h
  · simp only [ne_eq, sign_eq_zero_iff, h, iff_true]
    intro h'; rw [h'] at h; simp at h
  · simp [h]

lemma anc_succ (σ : ℕ → ℤ) (h0 : σ 0 = 0) (h1 : ∀ k, |σ (k + 1) - σ k| ≤ 1) (k : ℕ) :
    anc σ (k + 1) = anc σ k + 2 * (jmp σ k : ℤ) := by
  have ih := anc_inv σ h0 h1 k
  have hk := h1 k
  simp only [anc, jmp]
  split_ifs with h
  · rw [abs_le] at ih hk
    rcases le_abs'.1 h with h' | h'
    · have : σ (k + 1) - anc σ k = -2 := by omega
      rw [this]; simp; omega
    · have : σ (k + 1) - anc σ k = 2 := by omega
      rw [this]; simp; omega
  · simp

lemma anc_eq_of_jmp {σ τ : ℕ → ℤ} (hσ0 : σ 0 = 0) (hσ1 : ∀ k, |σ (k + 1) - σ k| ≤ 1)
    (hτ0 : τ 0 = 0) (hτ1 : ∀ k, |τ (k + 1) - τ k| ≤ 1) :
    ∀ k, (∀ i < k, jmp σ i = jmp τ i) → anc σ k = anc τ k
  | 0, _ => rfl
  | k + 1, h => by
    rw [anc_succ σ hσ0 hσ1, anc_succ τ hτ0 hτ1,
      anc_eq_of_jmp hσ0 hσ1 hτ0 hτ1 k (fun i hi => h i (by omega)), h k (by omega)]

/-! ### Floor division -/

lemma ediv_gap {s a b : ℤ} (hs : 0 < s) (h : 2 ≤ |a / s - b / s|) : s + 1 ≤ |a - b| := by
  have ha := Int.mul_ediv_add_emod a s
  have hb := Int.mul_ediv_add_emod b s
  have ha1 := Int.emod_nonneg a hs.ne'
  have ha2 := Int.emod_lt_of_pos a hs
  have hb1 := Int.emod_nonneg b hs.ne'
  have hb2 := Int.emod_lt_of_pos b hs
  set q := a / s - b / s with hq
  have hab : a - b = s * q + (a % s - b % s) := by rw [hq, mul_sub]; linarith
  rcases le_abs'.1 h with h' | h'
  · have : s * q ≤ s * (-2) := mul_le_mul_of_nonneg_left h' hs.le
    rw [le_abs']; left; linarith
  · have : s * 2 ≤ s * q := mul_le_mul_of_nonneg_left h' hs.le
    rw [le_abs']; right; linarith

lemma ediv_step {s a b : ℤ} (hs : 0 < s) (h : |a - b| ≤ s) : |a / s - b / s| ≤ 1 := by
  by_contra h'
  push Not at h'
  have := ediv_gap hs (a := a) (b := b) (by omega)
  omega

lemma ediv_close {s a b : ℤ} (hs : 0 < s) (h : |a / s - b / s| ≤ 2) : |a - b| < 3 * s := by
  have ha := Int.mul_ediv_add_emod a s
  have hb := Int.mul_ediv_add_emod b s
  have ha1 := Int.emod_nonneg a hs.ne'
  have ha2 := Int.emod_lt_of_pos a hs
  have hb1 := Int.emod_nonneg b hs.ne'
  have hb2 := Int.emod_lt_of_pos b hs
  set q := a / s - b / s with hq
  have hab : a - b = s * q + (a % s - b % s) := by rw [hq, mul_sub]; linarith
  rw [abs_le] at h
  have h1 : s * (-2) ≤ s * q := mul_le_mul_of_nonneg_left h.1 hs.le
  have h2 : s * q ≤ s * 2 := mul_le_mul_of_nonneg_left h.2 hs.le
  rw [abs_lt]; constructor <;> linarith

/-! ### Every jump costs `s + 1` moves -/

lemma cost_inv {s : ℤ} (hs : 0 < s) (D M : ℕ → ℤ) (hD0 : D 0 = 0)
    (hstep : ∀ k, |D (k + 1) - D k| ≤ M (k + 1) - M k) (hblock : ∀ k, |D (k + 1) - D k| ≤ s) :
    ∀ k, ∃ r ≤ k, D r / s = anc (fun i => D i / s) k ∧
      (s + 1) * (cnt (fun i => D i / s) k : ℤ) + |D k - D r| ≤ M k - M 0
  | 0 => ⟨0, le_rfl, by simp [anc, hD0], by simp [cnt]⟩
  | k + 1 => by
    obtain ⟨r, hr, hra, hcost⟩ := cost_inv hs D M hD0 hstep hblock k
    have hk := hstep k
    have htri := abs_sub_le (D (k + 1)) (D k) (D r)
    have hcnt : (cnt (fun i => D i / s) (k + 1) : ℤ) = cnt (fun i => D i / s) k +
        (if jmp (fun i => D i / s) k = 0 then 0 else 1) := by
      simp only [cnt, sum_range_succ]; push_cast; split_ifs <;> simp
    by_cases hj : jmp (fun i => D i / s) k = 0
    · refine ⟨r, by omega, ?_, ?_⟩
      · have : ¬ 2 ≤ |D (k + 1) / s - anc (fun i => D i / s) k| := fun h =>
          (jmp_ne_zero_iff _ k).2 h hj
        exact hra.trans (by
          simp only [anc]; exact (ite_eq_right_iff.2 (fun h => absurd h this)).symm)
      · rw [hcnt]; simp only [hj, ↓reduceIte]; linarith
    · have hj' := (jmp_ne_zero_iff _ k).1 hj
      refine ⟨k + 1, le_rfl, ?_, ?_⟩
      · simp only [anc]; exact (ite_eq_left_iff.2 (fun h => absurd hj' h)).symm
      · rw [hcnt]; simp only [hj, ↓reduceIte]
        rw [← hra] at hj'
        have := ediv_gap hs hj'
        simp only [sub_self, abs_zero, add_zero]
        linarith

/-! ### Agents whose sector walks stay close do not meet -/

lemma close_of_sectors {s : ℕ} (hs : 0 < s) (K : ℕ) (dx dy : ℕ → ℤ)
    (hx : ∀ t t', t ≤ t' → |dx t' - dx t| ≤ (t' : ℤ) - t)
    (hy : ∀ t t', t ≤ t' → |dy t' - dy t| ≤ (t' : ℤ) - t)
    (hsec : ∀ k ≤ K, |dx (k * s) / (s : ℤ) - dy (k * s) / (s : ℤ)| ≤ 2) :
    ∀ t ≤ K * s, |dx t - dy t| < 5 * s := by
  intro t ht
  have hk : t / s ≤ K := Nat.div_le_of_le_mul (by rw [mul_comm]; exact ht)
  have h1 : t / s * s ≤ t := Nat.div_mul_le_self t s
  have h2 : t < t / s * s + s := by
    have := Nat.lt_div_mul_add (a := t) hs; omega
  have hc := ediv_close (Int.natCast_pos.2 hs) (hsec _ hk)
  have hxa := hx _ _ h1
  have hya := hy _ _ h1
  push_cast [h1] at hxa hya
  rw [abs_lt] at hc ⊢
  rw [abs_le] at hxa hya
  constructor <;> linarith

/-! ### Sector walks and progress vectors of agents -/

variable {n L : ℕ} [NeZero n]

/-- The sector walk `σ_x(k) = ⌊d_x(k s) / s⌋` (`s = n / 10`) of the trimmed displacement. -/
noncomputable def sec (n : ℕ) [NeZero n] {L : ℕ} (V : Behaviour L) (x : Fin L) (k : ℕ) : ℤ :=
  tdisp n V x (k * (n / 10)) / ((n / 10 : ℕ) : ℤ)

/-- The progress vector `J_x ∈ {-1, 0, 1}^K` of agent `x`: the jumps of the greedy anchor of its
sector walk during the first `K` blocks. -/
noncomputable def prog (n : ℕ) [NeZero n] {L : ℕ} (V : Behaviour L) (x : Fin L) (K : ℕ) :
    Fin K → SignType :=
  fun i => jmp (sec n V x) i

lemma tdisp_zero' (V : Behaviour L) (x : Fin L) : tdisp n V x 0 = 0 := by simp [tdisp]

lemma abs_tdisp_sub_le_moves (V : Behaviour L) (x : Fin L) {t t' : ℕ} (h : t ≤ t') :
    |tdisp n V x t' - tdisp n V x t| ≤
      (moves (V x) (min t' (mx n V x)) : ℤ) - moves (V x) (min t (mx n V x)) :=
  abs_disp_sub_le_moves _ (min_le_min_right _ h)

lemma abs_tdisp_sub_le (V : Behaviour L) (x : Fin L) {t t' : ℕ} (h : t ≤ t') :
    |tdisp n V x t' - tdisp n V x t| ≤ (t' : ℤ) - t := by
  refine (abs_disp_sub_le _ (min_le_min_right _ h)).trans ?_
  push_cast; omega

lemma sec_zero (V : Behaviour L) (x : Fin L) : sec n V x 0 = 0 := by
  simp [sec, tdisp_zero' (n := n)]

lemma sec_step (hn : 10 ≤ n) (V : Behaviour L) (x : Fin L) (k : ℕ) :
    |sec n V x (k + 1) - sec n V x k| ≤ 1 := by
  refine ediv_step (by have : 0 < n / 10 := by omega
                       exact_mod_cast this) ?_
  have := abs_tdisp_sub_le (n := n) V x (Nat.mul_le_mul_right (n / 10) (Nat.le_succ k))
  have e : (((k + 1) * (n / 10) : ℕ) : ℤ) - ((k * (n / 10) : ℕ) : ℤ) = ((n / 10 : ℕ) : ℤ) := by
    push_cast; ring
  linarith

/-! ### Few vectors have few jumps -/

/-- `#{J ∈ {-1, 0, 1}^K | #supp J < k} ≤ λ^{-k} (1 + 2 λ)^K` for `0 < λ ≤ 1`. -/
lemma card_few_jumps_le (K k : ℕ) {l : ℝ} (hl0 : 0 < l) (hl1 : l ≤ 1) :
    ((univ.filter (fun J : Fin K → SignType =>
        (univ.filter (fun i => J i ≠ 0)).card < k)).card : ℝ) ≤ (l ^ k)⁻¹ * (1 + 2 * l) ^ K := by
  have hw : ∀ J : Fin K → SignType, ∏ i, (if J i = 0 then (1 : ℝ) else l) =
      l ^ (univ.filter (fun i => J i ≠ 0)).card := by
    intro J; rw [Finset.prod_ite]; simp
  have hsum : ∑ J : Fin K → SignType, l ^ (univ.filter (fun i => J i ≠ 0)).card =
      (1 + 2 * l) ^ K := by
    simp_rw [← hw]
    rw [← Fintype.prod_sum (fun (_ : Fin K) (v : SignType) => if v = 0 then (1 : ℝ) else l)]
    rw [show (Finset.univ : Finset SignType) = {0, -1, 1} by decide]
    simp; ring
  rw [Finset.card_eq_sum_ones, Nat.cast_sum]
  calc ∑ J ∈ univ.filter (fun J : Fin K → SignType =>
          (univ.filter (fun i => J i ≠ 0)).card < k), ((1 : ℕ) : ℝ)
      ≤ ∑ J ∈ univ.filter (fun J : Fin K → SignType =>
          (univ.filter (fun i => J i ≠ 0)).card < k),
          (l ^ k)⁻¹ * l ^ (univ.filter (fun i => J i ≠ 0)).card := by
        refine sum_le_sum (fun J hJ => ?_)
        simp only [mem_filter, mem_univ, true_and] at hJ
        have : l ^ k ≤ l ^ (univ.filter (fun i => J i ≠ 0)).card :=
          pow_le_pow_of_le_one hl0.le hl1 hJ.le
        rw [inv_mul_eq_div, le_div_iff₀ (by positivity)]
        simpa using this
    _ ≤ ∑ J : Fin K → SignType, (l ^ k)⁻¹ * l ^ (univ.filter (fun i => J i ≠ 0)).card :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => by positivity)
    _ = _ := by rw [← mul_sum, hsum]

end LBTime

open LBTime

/-- Finite core of Theorem 3.2 of [Miller–Pelc] (repaired proof): if the time is at most
`T ≤ K s` (`s = n / 10`) and fewer than `L` progress vectors in `{-1, 0, 1}^K` have fewer than
`k` nonzero entries, then some execution costs at least `k (s + 1)`. -/
theorem thm_3_2_core {n L : ℕ} [NeZero n] (hn : 10 ≤ n) (hL : 2 ≤ L) (V : Behaviour L)
    (hV : IsRendezvous n V) {T K k : ℕ} (hT : TimeLE n V T) (hK : T ≤ K * (n / 10))
    (hcount : (Finset.univ.filter (fun J : Fin K → SignType =>
        (Finset.univ.filter (fun i => J i ≠ 0)).card < k)).card < L) :
    ∃ x y px py, x ≠ y ∧ px ≠ py ∧ k * (n / 10 + 1) ≤ execCost n V x px y py := by
  have hs : 0 < n / 10 := by omega
  have hsZ : (0 : ℤ) < ((n / 10 : ℕ) : ℤ) := by exact_mod_cast hs
  have hn2 : 2 ≤ n := by omega
  -- distinct labels have distinct progress vectors
  have hinj : Function.Injective (fun x => prog n V x K) := by
    intro x y hxy
    by_contra hne
    have hanc : ∀ j ≤ K, anc (sec n V x) j = anc (sec n V y) j := fun j hj =>
      anc_eq_of_jmp (sec_zero V x) (sec_step hn V x) (sec_zero V y) (sec_step hn V y) j
        (fun i hi => congrFun hxy ⟨i, by omega⟩)
    have hsec : ∀ j ≤ K, |tdisp n V x (j * (n / 10)) / ((n / 10 : ℕ) : ℤ) -
        tdisp n V y (j * (n / 10)) / ((n / 10 : ℕ) : ℤ)| ≤ 2 := by
      intro j hj
      have h1 := anc_inv _ (sec_zero V x) (sec_step hn V x) j
      have h2 := anc_inv _ (sec_zero V y) (sec_step hn V y) j
      rw [hanc j hj] at h1
      simp only [sec] at h1 h2
      rw [abs_le] at h1 h2 ⊢; constructor <;> linarith
    have hclose := close_of_sectors hs K _ _ (fun t t' h => abs_tdisp_sub_le V x h)
      (fun t t' h => abs_tdisp_sub_le V y h) hsec
    have hp : (0 : ZMod n) ≠ ((n / 2 : ℕ) : ZMod n) := by
      intro h
      have := (ZMod.natCast_eq_zero_iff (n / 2) n).1 h.symm
      have := Nat.le_of_dvd (by omega) this
      omega
    have hm := meets_meetTime (hV x y hne 0 _ hp)
    have htx := meetTime_le_mx V (Ne.symm hne) hp
    have hty : meetTime n V x 0 y ((n / 2 : ℕ) : ZMod n) ≤ mx n V y := by
      rw [meetTime_comm]; exact meetTime_le_mx V hne hp.symm
    have hc := hclose _ ((hT x y hne 0 _ hp).trans hK)
    rw [tdisp, tdisp, min_eq_left htx, min_eq_left hty] at hc
    generalize meetTime n V x 0 y ((n / 2 : ℕ) : ZMod n) = t at hm hc
    have hz : (((disp (V x) t - disp (V y) t - (n / 2 : ℕ) : ℤ)) : ZMod n) = 0 := by
      unfold Meets at hm
      simp only [Int.cast_sub, Int.cast_natCast]; linear_combination hm
    have hd := (ZMod.intCast_zmod_eq_zero_iff_dvd _ n).1 hz
    rw [abs_lt] at hc
    have := Int.eq_zero_of_abs_lt_dvd hd (by rw [abs_lt]; constructor <;> omega)
    omega
  -- some label makes at least `k` jumps
  obtain ⟨x, hx⟩ : ∃ x, k ≤ (univ.filter (fun i => prog n V x K i ≠ 0)).card := by
    by_contra h
    push Not at h
    have := Finset.card_le_card_of_injOn (fun x => prog n V x K) (s := univ)
      (t := univ.filter (fun J : Fin K → SignType => (univ.filter (fun i => J i ≠ 0)).card < k))
      (fun x _ => by simpa using h x) hinj.injOn
    simp only [card_univ, Fintype.card_fin] at this
    omega
  -- each jump costs `s + 1` moves
  obtain ⟨y, px, py, hyx, hp, hmt⟩ := exists_meetTime_eq_mx V x hn2 hL
  refine ⟨x, y, px, py, hyx.symm, hp, ?_⟩
  obtain ⟨r, -, -, hcost⟩ := cost_inv hsZ (fun j => tdisp n V x (j * (n / 10)))
    (fun j => (moves (V x) (min (j * (n / 10)) (mx n V x)) : ℤ)) (by simp [tdisp])
    (fun j => abs_tdisp_sub_le_moves V x (Nat.mul_le_mul_right _ (Nat.le_succ j)))
    (fun j => by
      have := abs_tdisp_sub_le (n := n) V x (Nat.mul_le_mul_right (n / 10) (Nat.le_succ j))
      have e : (((j + 1) * (n / 10) : ℕ) : ℤ) - ((j * (n / 10) : ℕ) : ℤ) =
          ((n / 10 : ℕ) : ℤ) := by
        push_cast; ring
      linarith) K
  have hcnt : cnt (sec n V x) K = (univ.filter (fun i => prog n V x K i ≠ 0)).card := by
    rw [Finset.card_filter, cnt, ← Fin.sum_univ_eq_sum_range]
    refine sum_congr rfl (fun i _ => ?_)
    simp only [prog]; split_ifs <;> simp_all
  have hM : moves (V x) (min (K * (n / 10)) (mx n V x)) ≤ moves (V x) (mx n V x) :=
    moves_mono _ (min_le_right _ _)
  have habs := abs_nonneg (tdisp n V x (K * (n / 10)) - tdisp n V x (r * (n / 10)))
  change (((n / 10 : ℕ) : ℤ) + 1) * (cnt (sec n V x) K : ℤ) + _ ≤ _ at hcost
  simp only [Nat.zero_mul, Nat.zero_min, moves_zero, CharP.cast_eq_zero, sub_zero] at hcost
  rw [hcnt] at hcost
  have h1 : k * (n / 10 + 1) ≤ moves (V x) (min (K * (n / 10)) (mx n V x)) := by
    have : ((k * (n / 10 + 1) : ℕ) : ℤ) ≤ moves (V x) (min (K * (n / 10)) (mx n V x)) := by
      simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one]
      have hk : (k : ℤ) ≤ (#{i | prog n V x K i ≠ 0} : ℕ) := by exact_mod_cast hx
      nlinarith
    exact_mod_cast this
  unfold execCost; rw [hmt]; omega

/-- Theorem 3.2 of [Miller–Pelc]: in the oriented ring of size `n ≥ 10` (`E = n - 1`) with
simultaneous start, any deterministic rendezvous algorithm for `L` labels with time at most
`c E log L` has cost at least `c' E log L`, for a constant `c' > 0` depending only on `c`
(and all `L ≥ L₀(c)`). Proved with the repaired argument of `thm_3_2_core`. -/
theorem thm_3_2 (c : ℝ) (hc : 0 < c) : ∃ c' > 0, ∃ L₀ : ℕ, ∀ (n L : ℕ) [NeZero n], 10 ≤ n →
    L₀ ≤ L → ∀ V : Behaviour L, IsRendezvous n V → ∀ T : ℕ, TimeLE n V T →
      (T : ℝ) ≤ c * ((n - 1 : ℕ) : ℝ) * Real.logb 2 L →
      ∃ x y px py, x ≠ y ∧ px ≠ py ∧
        c' * ((n - 1 : ℕ) : ℝ) * Real.logb 2 L ≤ execCost n V x px y py := by
  set B : ℝ := 1 + 288 * c with hB
  have hB1 : 1 < B := by linarith
  set A : ℝ := Real.log B with hA
  have hA0 : 0 < A := Real.log_pos hB1
  set l : ℝ := B⁻¹ with hl
  have hl0 : 0 < l := by positivity
  have hl1 : l ≤ 1 := inv_le_one_of_one_le₀ hB1.le
  have hcl : 36 * c * l ≤ 1 / 8 := by
    rw [hl, ← div_eq_mul_inv, div_le_iff₀ (by linarith)]; linarith
  set γ : ℝ := 1 / (8 * A) with hγ
  have hγ0 : 0 < γ := by positivity
  have hγA : γ * A = 1 / 8 := by rw [hγ]; field_simp
  refine ⟨γ / 10, by positivity, ⌈Real.exp (2 * A + 4)⌉₊ + 1, ?_⟩
  intro n L _ hn hL₀ V hV T hT hTc
  have hlog2 := Real.log_two_gt_d9
  have hlog2' := Real.log_two_lt_d9
  have hexp := Nat.le_ceil (Real.exp (2 * A + 4))
  have hL : 2 ≤ L := by
    have : (1 : ℝ) ≤ ⌈Real.exp (2 * A + 4)⌉₊ := le_trans (by
      have := Real.add_one_le_exp (2 * A + 4); linarith) hexp
    have : 1 ≤ ⌈Real.exp (2 * A + 4)⌉₊ := by exact_mod_cast this
    omega
  have hLpos : (0 : ℝ) < L := by positivity
  have hΛ : 2 * A + 4 < Real.log L := by
    rw [Real.lt_log_iff_exp_lt hLpos]
    have : ((⌈Real.exp (2 * A + 4)⌉₊ + 1 : ℕ) : ℝ) ≤ L := by exact_mod_cast hL₀
    push_cast at this; linarith
  set Λ := Real.log L with hΛdef
  set ℓ := Real.logb 2 L with hℓdef
  have hℓ : ℓ = Λ / Real.log 2 := rfl
  have hℓ0 : 0 ≤ ℓ := by rw [hℓ]; apply div_nonneg <;> linarith
  have hℓ2 : ℓ ≤ 2 * Λ := by
    rw [hℓ, div_le_iff₀ (by linarith)]; nlinarith
  -- blocks
  have hs : 0 < n / 10 := by omega
  have hsR : (0 : ℝ) < ((n / 10 : ℕ) : ℝ) := by exact_mod_cast hs
  set K := T / (n / 10) + 1 with hKdef
  have hK : T ≤ K * (n / 10) := by
    have := Nat.lt_div_mul_add (a := T) hs
    rw [hKdef, Nat.add_mul, one_mul]; omega
  have hE : ((n - 1 : ℕ) : ℝ) ≤ 18 * ((n / 10 : ℕ) : ℝ) := by
    have : n - 1 ≤ 18 * (n / 10) := by omega
    exact_mod_cast this
  have hE0 : (0 : ℝ) ≤ ((n - 1 : ℕ) : ℝ) := by positivity
  have hTs : (T : ℝ) / ((n / 10 : ℕ) : ℝ) ≤ 18 * c * ℓ := by
    rw [div_le_iff₀ hsR]
    calc (T : ℝ) ≤ c * ((n - 1 : ℕ) : ℝ) * ℓ := hTc
      _ ≤ c * (18 * ((n / 10 : ℕ) : ℝ)) * ℓ := by gcongr
      _ = _ := by ring
  have hKR : (K : ℝ) ≤ 18 * c * ℓ + 1 := by
    rw [hKdef]; push_cast
    have := Nat.cast_div_le (α := ℝ) (m := T) (n := n / 10)
    linarith
  set k := ⌈γ * ℓ⌉₊ with hkdef
  have hk : (k : ℝ) < γ * ℓ + 1 := Nat.ceil_lt_add_one (by positivity)
  -- the counting bound
  have hcount : (univ.filter (fun J : Fin K → SignType =>
      (univ.filter (fun i => J i ≠ 0)).card < k)).card < L := by
    have h1 := card_few_jumps_le K k hl0 hl1
    have h2 : (l ^ k)⁻¹ = Real.exp (k * A) := by
      rw [hl, inv_pow, inv_inv, Real.exp_nat_mul, hA, Real.exp_log (by linarith)]
    have h3 : (1 + 2 * l) ^ K ≤ Real.exp (K * (2 * l)) := by
      rw [Real.exp_nat_mul]
      exact pow_le_pow_left₀ (by positivity) (by linarith [Real.add_one_le_exp (2 * l)]) K
    have h4 : (k : ℝ) * A + K * (2 * l) < Λ := by
      have e1 : (k : ℝ) * A ≤ (γ * ℓ + 1) * A := by gcongr
      have e2 : (K : ℝ) * (2 * l) ≤ (18 * c * ℓ + 1) * (2 * l) := by gcongr
      have e3 : 36 * c * l * ℓ ≤ 1 / 8 * ℓ := by gcongr
      nlinarith
    have h5 : (l ^ k)⁻¹ * (1 + 2 * l) ^ K < L := by
      rw [h2]
      calc Real.exp (k * A) * (1 + 2 * l) ^ K ≤ Real.exp (k * A) * Real.exp (K * (2 * l)) := by
            gcongr
        _ = Real.exp (k * A + K * (2 * l)) := (Real.exp_add _ _).symm
        _ < Real.exp Λ := Real.exp_lt_exp.2 h4
        _ = L := Real.exp_log hLpos
    exact_mod_cast h1.trans_lt h5
  obtain ⟨x, y, px, py, hxy, hp, hcost⟩ := thm_3_2_core hn hL V hV hT hK hcount
  refine ⟨x, y, px, py, hxy, hp, ?_⟩
  have hc1 : (k : ℝ) * ((n / 10 : ℕ) + 1 : ℝ) ≤ execCost n V x px y py := by
    exact_mod_cast hcost
  have hE10 : ((n - 1 : ℕ) : ℝ) / 10 ≤ ((n / 10 : ℕ) + 1 : ℝ) := by
    have : n - 1 ≤ 10 * (n / 10 + 1) := by omega
    have : ((n - 1 : ℕ) : ℝ) ≤ 10 * ((n / 10 : ℕ) + 1 : ℝ) := by exact_mod_cast this
    linarith
  calc γ / 10 * ((n - 1 : ℕ) : ℝ) * ℓ = (γ * ℓ) * (((n - 1 : ℕ) : ℝ) / 10) := by ring
    _ ≤ (k : ℝ) * ((n / 10 : ℕ) + 1 : ℝ) := by
        gcongr
        exact Nat.le_ceil _
    _ ≤ _ := hc1

end Podc.RendezvousTimeCost
