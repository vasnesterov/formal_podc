import Papers.PODC2018.FairLeaderElection.Placement

/-!
# Attacks on `A-LEADuni` (Section 4 of [YM18])

* Lemma 4.1 (`lemma_4_1`): if the origin is honest and every honest segment has length at most
  `k - 1`, the coalition can force any outcome `w` (rushing attack with `F = n - k`, `z = 0`).
  With the origin in the coalition the paper's attack deadlocks (`lemma_4_1_attack_deadlocks`).
* Theorem 4.2 (`theorem_4_2`): `A-LEADuni` is not `ε`-`k`-resilient for `k ≥ √n`, `ε < 1 - 1/n`.
* Theorem 4.3, Cubic Attack (`theorem_4_3`, with Lemmas 4.4/4.5 inside `rushing_outcome`):
  `A-LEADuni` is not `ε`-`k`-unbiased for `k ≥ 2 ∛n`, `ε < 1 - 1/n`.
* Corollary 4.6 (`corollary_4_6`) for `0 ≤ ε < 1 - 1/n`; the paper's boundary case
  `ε = 1 - 1/n` is false (`corollary_4_6_boundary_false`).

The bounds `k ≥ √n` and `k ≥ 2∛n` are stated in the equivalent integer forms `n ≤ k^2` and
`8 n ≤ k^3` (see `sqrt_le_iff`, `two_cbrt_le_iff`).
-/

namespace Podc.FairLeaderElection

open Cslib.UniRing
open Fin.NatCast Fin.CommRing

variable {n : ℕ} [NeZero n]

/-! ### Lemma 4.1 -/

/-- **Lemma 4.1.** If the origin is honest and every honest segment has length at most `k - 1`
(`k = |C|`), then for every `w` the coalition has a deviation from `A-LEADuni` under which every
execution (every fair schedule, every choice of the honest secrets) has outcome `w`. -/
theorem lemma_4_1 {C : Finset (Fin n)} (hC : C.Nonempty) (h0 : (0 : Fin n) ∉ C)
    (hgap : ∀ a ∈ C, gap C a ≤ C.card - 1) (w : Fin n) :
    ∃ A : Profile n (Fin n), ∀ d, outcome (dev C A d) = some w ∧
      ∀ σ, Fair σ → outcomeUnder (dev C A d) σ = some w := by
  have hk : C.card ≤ n := by simpa using Finset.card_le_univ C
  have hk1 : 1 ≤ C.card := Finset.card_pos.mpr hC
  have hp : Params C (fun _ => n - C.card) (fun _ => 0) :=
    ⟨fun _ _ => le_rfl, fun _ _ => Nat.sub_le _ _, fun a ha => by have := hgap a ha; omega⟩
  have hl : Live C (fun _ => n - C.card) (fun _ => 0) := by
    obtain ⟨a, ha⟩ := hC
    exact ⟨a, ha, by simp, fun _ _ _ => by simp⟩
  refine ⟨rushProfile C (fun _ => n - C.card) (fun _ => 0) w, fun d => ?_⟩
  have := rushing_outcome (w := w) hC h0 hp hl d
  exact ⟨this, fun σ hσ => (outcomeUnder_eq _ hσ).trans this⟩

theorem reach_eq_init_of_silent {P : Profile n (Fin n)} (hP : ∀ j, (P j).sent [] = [])
    {c : Config n (Fin n)} (hc : Reach P c) : c = init := by
  induction hc with
  | refl => rfl
  | tail _ hs ih =>
    subst ih
    obtain ⟨i, he, -⟩ := hs
    have := he.2
    simp [inbox, init, hP] at this

/-- The attack of Lemma 4.1, as described in the paper (forward the first `n - k` messages, then
send `M`, zeros and the segment secrets), **deadlocks if the origin belongs to the coalition**:
nobody sends anything, and the outcome is `FAIL`. (The paper does not assume the origin to be
honest in Lemma 4.1.) -/
theorem lemma_4_1_attack_deadlocks {C : Finset (Fin n)} (h0 : (0 : Fin n) ∈ C) (hk : C.card < n)
    (w : Fin n) (d : Fin n → Fin n) :
    outcome (dev C (rushProfile C (fun _ => n - C.card) (fun _ => 0) w) d) = none := by
  have hsil : ∀ j, (dev C (rushProfile C (fun _ => n - C.card) (fun _ => 0) w) d j).sent [] = [] := by
    intro j
    by_cases hj : j ∈ C
    · rw [dev_adv hj]; simp only [rushProfile, rushing, rushSend]; simp; omega
    · rw [dev_honest hj]
      have hj0 : j ≠ 0 := fun h => hj (h ▸ h0)
      simp [aLead, hj0, normal]
  obtain ⟨h, hh⟩ : ∃ h, h ∉ C := by
    by_contra hall; push_neg at hall
    have : C = Finset.univ := Finset.eq_univ_of_forall hall
    rw [this, Finset.card_univ, Fintype.card_fin] at hk; omega
  rw [Option.eq_none_iff_forall_ne_some]
  intro v hv
  obtain ⟨c, hc, ho⟩ := (outcome_eq_some.mp hv) h
  rw [reach_eq_init_of_silent hsil hc, dev_honest hh, aLead_out] at ho
  simp [init, validate, NeZero.ne n] at ho

/-! ### All-adversary coalitions -/

/-- The strategy "terminate immediately with output `w`". -/
def sayW (w : Fin n) : Proc (Fin n) (Option (Fin n)) where
  sent _ := []
  sent_snoc _ _ := List.prefix_refl _
  out _ := some (some w)

theorem outcome_univ (w : Fin n) (d : Fin n → Fin n) :
    outcome (dev Finset.univ (fun _ => sayW w) d) = some w := by
  rw [outcome_eq_some]
  intro j
  exact ⟨init, Relation.ReflTransGen.refl, by simp [dev_adv (Finset.mem_univ j), sayW]⟩

/-! ### From a forced outcome to non-resilience -/

theorem prob_eq_one_of_forall {C : Finset (Fin n)} {A : Profile n (Fin n)} {w : Fin n}
    (h : ∀ d, outcome (dev C A d) = some w) {σ : ℕ → Fin n} (hσ : Fair σ) :
    prob (deviate aLead C A) σ (some w) = 1 := by
  classical
  unfold prob
  rw [Finset.filter_true_of_mem (fun d _ => by rw [outcomeUnder_eq _ hσ]; exact h d)]
  simp

theorem not_unbiased_of_forced {k : ℕ} {ε : ℝ} (hε : ε < 1 - 1 / n) {C : Finset (Fin n)}
    (hC : C.card = k) {A : Profile n (Fin n)} {w : Fin n} (h : ∀ d, outcome (dev C A d) = some w) :
    ¬ IsUnbiased (n := n) aLead ε k := by
  intro hU
  have := hU (roundRobin n) fair_roundRobin C hC A w
  rw [prob_eq_one_of_forall h fair_roundRobin] at this
  linarith

theorem not_resilient_of_not_unbiased {k : ℕ} {ε : ℝ} (h : ¬ IsUnbiased (n := n) aLead ε k) :
    ¬ IsResilient (n := n) aLead ε k :=
  fun hR => h ((lemma_2_4 aLead isFLE_aLead ε k).1 hR)

/-! ### Theorem 4.2 -/

theorem sum_gaps {k T : ℕ} {g : ℕ → ℕ} (hg : ∑ t ∈ Finset.range k, g t = T) :
    ∑ t ∈ Finset.range k, (g t + 1) = T + k := by
  rw [Finset.sum_add_distrib, hg]; simp

/-- **Theorem 4.2.** `A-LEADuni` is not `ε`-`k`-resilient for every `k ≥ √n` (here `n ≤ k^2`,
`k ≤ n`) and `ε < 1 - 1/n`. The coalition is placed with segments of length at most `k - 1`, the
origin honest, and runs the attack of Lemma 4.1. -/
theorem theorem_4_2 {k : ℕ} (hk : n ≤ k ^ 2) (hkn : k ≤ n) {ε : ℝ} (hε : ε < 1 - 1 / n) :
    ¬ IsResilient (n := n) aLead ε k := by
  apply not_resilient_of_not_unbiased
  rcases eq_or_lt_of_le hkn with rfl | hlt
  · exact not_unbiased_of_forced (w := 0) hε (by simp) (outcome_univ 0)
  -- `k < n`, hence `k ≥ 2`
  have hk2 : 2 ≤ k := by
    by_contra h; push_neg at h; interval_cases k <;> simp_all <;> omega
  set c : ℕ → ℕ := fun _ => k - 1
  have hcap : capSum c k 0 = k * (k - 1) := by simp [capSum, c]
  have hT : n - k ≤ capSum c k 0 := by
    rw [hcap]
    have : k * (k - 1) = k ^ 2 - k := by
      rw [Nat.mul_sub, mul_one, sq]
    omega
  set g := fillGaps c k (n - k)
  have hsum : ∑ t ∈ Finset.range k, (g t + 1) = n := by
    rw [sum_gaps (sum_fillGaps c k (n - k) hT)]; omega
  have hl : 1 ≤ g (k - 1) := by
    show 1 ≤ fillGaps c k (n - k) (k - 1)
    rw [fillGaps_last c (by omega)]; simp only [c, le_min_iff]; omega
  set C := place n k g
  have hC := place_nonempty (n := n) (by omega) hsum hl
  have hcard : C.card = k := card_place (by omega) hsum hl
  obtain ⟨A, hA⟩ := lemma_4_1 hC (zero_not_mem_place (by omega) hsum hl) (by
    intro a ha
    obtain ⟨t, ht, rfl⟩ := eq_advAt (by omega) hsum hl ha
    rw [gap_place (by omega) hsum hl ht, hcard]
    exact fillGaps_le c _ ht) 0
  exact not_unbiased_of_forced hε hcard fun d => (hA d).1

/-! ### Theorem 4.3: the Cubic Attack -/

theorem capSum_cubic (k : ℕ) :
    2 * capSum (fun t => (k - 1) * (k - t)) k 0 = (k - 1) * (k * (k + 1)) := by
  have h1 : ∑ t ∈ Finset.range k, (k - t) = ∑ t ∈ Finset.range k, (t + 1) := by
    rw [← Finset.sum_range_reflect]
    exact Finset.sum_congr rfl fun t ht => by simp at ht; omega
  have h2 : 2 * ∑ t ∈ Finset.range k, (t + 1) = k * (k + 1) := by
    rw [Finset.sum_add_distrib, mul_add, mul_comm, Finset.sum_range_id_mul_two]
    simp; cases k <;> simp; ring
  simp only [capSum, Nat.Ico_zero_eq_range, ← Finset.mul_sum, h1]
  rw [mul_left_comm, h2]

/-- **Theorem 4.3 (Cubic Attack).** `A-LEADuni` is not `ε`-`k`-unbiased for every `ε < 1 - 1/n` and
`k ≥ 2 ∛n` (here `8 n ≤ k^3`, `k ≤ n`). The coalition is placed with segment lengths
`l_1, …, l_k` (greedily from the end, `l_k ≤ k - 1`, `l_i ≤ l_{i+1} + k - 1`, total `n - k`), the
origin is honest, and adversary `a_i` runs the Cubic Attack: forward `n - k - l_i` messages, send
`k - 1` zeros, wait for `n - k` messages in total, send `M`, then the last `l_i` messages. -/
theorem theorem_4_3 {k : ℕ} (hk : 8 * n ≤ k ^ 3) (hkn : k ≤ n) {ε : ℝ} (hε : ε < 1 - 1 / n) :
    ¬ IsUnbiased (n := n) aLead ε k := by
  rcases eq_or_lt_of_le hkn with rfl | hlt
  · exact not_unbiased_of_forced (w := 0) hε (by simp) (outcome_univ 0)
  have hn := NeZero.pos n
  have hk2 : 2 ≤ k := by
    by_contra h; push_neg at h; interval_cases k <;> simp at hk <;> omega
  set c : ℕ → ℕ := fun t => (k - 1) * (k - t)
  have hT : n - k ≤ capSum c k 0 := by
    have h2 : 2 * capSum c k 0 = (k - 1) * (k * (k + 1)) := capSum_cubic k
    have : 2 * (n - k) ≤ (k - 1) * (k * (k + 1)) := by
      obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
      simp only [Nat.add_sub_cancel]
      have : (m + 1) ^ 3 = m * ((m + 1) * (m + 1 + 1)) + (m + 1) := by ring
      omega
    omega
  set g := fillGaps c k (n - k)
  have hsum : ∑ t ∈ Finset.range k, (g t + 1) = n := by
    rw [sum_gaps (sum_fillGaps c k (n - k) hT)]; omega
  have hl : 1 ≤ g (k - 1) := by
    show 1 ≤ fillGaps c k (n - k) (k - 1)
    rw [fillGaps_last c (by omega)]; simp only [c, le_min_iff]
    exact ⟨by omega, by rw [show k - (k - 1) = 1 by omega]; omega⟩
  have hglast : g (k - 1) ≤ k - 1 := by
    have : g (k - 1) ≤ c (k - 1) := fillGaps_le c (n - k) (show k - 1 < k by omega)
    simp only [c, show k - (k - 1) = 1 by omega, mul_one] at this
    exact this
  set C := place n k g
  have hC := place_nonempty (n := n) (by omega) hsum hl
  have hcard : C.card = k := card_place (by omega) hsum hl
  have hgle : ∀ a ∈ C, gap C a ≤ n - C.card := fun a ha => gap_le_honest hC ha
  -- the parameters of the Cubic Attack
  let F : Fin n → ℕ := fun a => n - C.card - gap C a
  let z : Fin n → ℕ := fun _ => k - 1
  have hp : Params C F z := ⟨fun _ _ => Nat.sub_le _ _, fun _ _ => le_rfl, fun a ha => by
    have := hgle a ha; simp only [F, z]; omega⟩
  have hgap : ∀ t < k, gap C (advAt g t) = g t := fun t ht => gap_place (by omega) hsum hl ht
  have hlive : Live C F z := by
    refine ⟨advAt g (k - 1), advAt_mem (by omega) hsum hl (by omega), ?_, ?_⟩
    · simp only [F, z, hcard, hgap (k - 1) (by omega)]
      omega
    · intro j hj hne
      obtain ⟨u, hu, rfl⟩ := eq_advAt (by omega) hsum hl hj
      rcases u with _ | u
      · exact absurd (prev_advAt_zero (by omega) hsum hl) hne
      rw [prev_advAt_succ (by omega) hsum hl hu]
      simp only [F, z, hcard, hgap _ hu, hgap u (by omega)]
      have hle : g u ≤ c u := fillGaps_le c (n - k) (show u < k by omega)
      have hle' : g (u + 1) ≤ c (u + 1) := fillGaps_le c (n - k) hu
      have hcc : c u = c (u + 1) + (k - 1) := by
        simp only [c]
        rw [show k - u = (k - (u + 1)) + 1 by omega, mul_add, mul_one]
      by_cases hfull : g (u + 1) < c (u + 1)
      · have : g u = 0 := fillGaps_zero_of_lt c hu hfull
        omega
      · omega
  exact not_unbiased_of_forced (w := 0) hε hcard fun d => rushing_outcome hC
    (zero_not_mem_place (by omega) hsum hl) hp hlive d

/-- **Corollary 4.6** (for `ε < 1 - 1/n`): `A-LEADuni` is not `ε`-`k`-resilient for `k ≥ 2∛n`. -/
theorem corollary_4_6 {k : ℕ} (hk : 8 * n ≤ k ^ 3) (hkn : k ≤ n) {ε : ℝ} (hε : ε < 1 - 1 / n) :
    ¬ IsResilient (n := n) aLead ε k :=
  not_resilient_of_not_unbiased (theorem_4_3 hk hkn hε)

/-- The boundary case `ε = 1 - 1/n` of Corollary 4.6 (stated in the paper with `ε ≤ 1 - 1/n`) is
false: every FLE protocol, in particular `A-LEADuni`, is `(1 - 1/n)`-`k`-resilient for every
`k ≥ 1`, since no deviation can raise an expected rational utility by more than `1 - 1/n`. -/
theorem corollary_4_6_boundary_false {k : ℕ} (hk : 1 ≤ k) :
    IsResilient (n := n) aLead (1 - 1 / n) k :=
  isResilient_one_sub_inv aLead isFLE_aLead hk

/-! ### The bounds in the paper's form -/

theorem sqrt_le_iff (n k : ℕ) : Real.sqrt n ≤ k ↔ n ≤ k ^ 2 := by
  rw [Real.sqrt_le_left (by positivity)]; norm_cast

theorem two_cbrt_le_iff (n k : ℕ) : 2 * (n : ℝ) ^ ((1 : ℝ) / 3) ≤ k ↔ 8 * n ≤ k ^ 3 := by
  have h : ((n : ℝ) ^ ((1 : ℝ) / 3)) ^ (3 : ℕ) = n := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]; norm_num
  have h0 : 0 ≤ 2 * (n : ℝ) ^ ((1 : ℝ) / 3) := by positivity
  constructor
  · intro hle
    have := pow_le_pow_left₀ h0 hle 3
    rw [mul_pow, h] at this
    exact_mod_cast (by linarith : (8 * n : ℝ) ≤ (k : ℝ) ^ 3)
  · intro hle
    by_contra hlt; push_neg at hlt
    have := pow_lt_pow_left₀ hlt (by positivity) (by norm_num : (3 : ℕ) ≠ 0)
    rw [mul_pow, h] at this
    have : (8 * n : ℝ) ≤ (k : ℝ) ^ 3 := by exact_mod_cast hle
    linarith

/-- **Theorem 4.2**, literally: not `ε`-`k`-resilient for `√n ≤ k ≤ n`, `ε < 1 - 1/n`. -/
theorem theorem_4_2' {k : ℕ} (hk : Real.sqrt n ≤ k) (hkn : k ≤ n) {ε : ℝ} (hε : ε < 1 - 1 / n) :
    ¬ IsResilient (n := n) aLead ε k :=
  theorem_4_2 ((sqrt_le_iff n k).mp hk) hkn hε

/-- **Theorem 4.3**, literally: not `ε`-`k`-unbiased for `2∛n ≤ k ≤ n`, `ε < 1 - 1/n`. -/
theorem theorem_4_3' {k : ℕ} (hk : 2 * (n : ℝ) ^ ((1 : ℝ) / 3) ≤ k) (hkn : k ≤ n) {ε : ℝ}
    (hε : ε < 1 - 1 / n) : ¬ IsUnbiased (n := n) aLead ε k :=
  theorem_4_3 ((two_cbrt_le_iff n k).mp hk) hkn hε

/-- **Corollary 4.6**, literally (for `ε < 1 - 1/n`). -/
theorem corollary_4_6' {k : ℕ} (hk : 2 * (n : ℝ) ^ ((1 : ℝ) / 3) ≤ k) (hkn : k ≤ n) {ε : ℝ}
    (hε : ε < 1 - 1 / n) : ¬ IsResilient (n := n) aLead ε k :=
  corollary_4_6 ((two_cbrt_le_iff n k).mp hk) hkn hε

/-- **Lemmas 4.4 and 4.5** (for every rushing attack satisfying the conditions, in particular the
Cubic Attack): every adversary terminates (with output `w`), and its incoming messages are the
`n - k` honest secrets in the order of the ring, walking backwards (`incoming`). -/
theorem lemma_4_4_4_5 {C : Finset (Fin n)} {F z : Fin n → ℕ} (hC : C.Nonempty)
    (h0 : (0 : Fin n) ∉ C) (hp : Params C F z) (hl : Live C F z) (w : Fin n) (d : Fin n → Fin n)
    {a : Fin n} (ha : a ∈ C) :
    ∃ c, Reach (atk C F z w d) c ∧ c a = incoming C d a ∧
      (atk C F z w d a).out (c a) = some (some w) := by
  refine ⟨_, reach_finalCfg hC h0 hp hl, finalCfg_adv ha, ?_⟩
  rw [atk_adv ha, finalCfg_adv ha]
  have := Finset.card_le_univ C; simp only [Fintype.card_fin] at this
  simp [rushing, incoming_length hC ha]
  omega

end Podc.FairLeaderElection
