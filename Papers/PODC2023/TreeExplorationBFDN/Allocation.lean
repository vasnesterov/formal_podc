import Papers.PODC2023.TreeExplorationBFDN.UrnSum

/-!
# Balanced allocation with removals (abstract core of Lemma 2)

Cosson, Massoulié, Viennot, PODC 2023; full version arXiv:2301.13307, Section 3.1 (Lemma 2).

Abstract version of one depth-`d` phase of BFDN, phrased with round-indexed data:

* `O t` — the "urns" alive at the start of round `t` (in BFDN: the open nodes at depth `d`);
  from round `t₀` on, urns only disappear;
* `c t w` — the load of urn `w` at the start of round `t` (in BFDN: the number of robots anchored
  at `w`); the load of an alive urn only grows during a round, and `A t` is the total growth
  (the number of anchor assignments at depth `d` in round `t`);
* loads of alive urns are balanced (differ by at most one) at the end of every round;
* capacity: `∑_{w ∈ O t} (c (t+1) w + 1) ≤ k` (each alive urn also hosts its discoverer robot);
* window: once all alive urns have load `+ 1 ≥ Δ`, the number of assignments in all later
  rounds is bounded by the number of robots that are not bound to alive urns, plus the robots
  bound to urns that die in this very round.

Conclusion (`alloc_bound`): the total number of assignments is at most
`urnSum k Δ = ∑_{u=1}^{k} min(Δ, ⌈k/u⌉)`.
-/

set_option linter.unusedSectionVars false

namespace Podc.TreeExplorationBFDN

open Finset

/-- Characterisation of `ceilDiv` from above. -/
theorem alloc_ceilDiv_le_iff {k u m : ℕ} (hu : 0 < u) : ceilDiv k u ≤ m ↔ k ≤ m * u := by
  unfold ceilDiv
  rw [← Nat.lt_succ_iff, Nat.div_lt_iff_lt_mul hu, Nat.succ_mul]
  omega

/-- `ceilDiv k u` is antitone in `u ≥ 1`. -/
theorem alloc_ceilDiv_anti {k u v : ℕ} (hu : 0 < u) (huv : u ≤ v) :
    ceilDiv k v ≤ ceilDiv k u := by
  rw [alloc_ceilDiv_le_iff (lt_of_lt_of_le hu huv)]
  have h := (alloc_ceilDiv_le_iff (k := k) (m := ceilDiv k u) hu).1 le_rfl
  exact h.trans (Nat.mul_le_mul_left _ huv)

/-- In a balanced family (values differ by at most one) whose shifted sum `∑ (v w + 1)` is at most
`k`, every `v w + 1` is at most `⌈k / |s|⌉`. -/
theorem alloc_balanced_le_ceilDiv {ι : Type*} [DecidableEq ι] {k : ℕ} (s : Finset ι) (v : ι → ℕ)
    (hbal : ∀ w ∈ s, ∀ w' ∈ s, v w ≤ v w' + 1) (hsum : ∑ w ∈ s, (v w + 1) ≤ k) :
    ∀ w ∈ s, v w + 1 ≤ ceilDiv k s.card := by
  intro w₀ hw₀
  have hn : 0 < s.card := card_pos.2 ⟨w₀, hw₀⟩
  unfold ceilDiv
  rw [Nat.le_div_iff_mul_le hn]
  have h1 : ∑ w ∈ s.erase w₀, v w₀ ≤ ∑ w ∈ s.erase w₀, (v w + 1) :=
    sum_le_sum fun w hw => hbal w₀ hw₀ w (mem_of_mem_erase hw)
  rw [sum_const, card_erase_of_mem hw₀, smul_eq_mul] at h1
  have h2 := add_sum_erase s (fun w => v w + 1) hw₀
  obtain ⟨m, hm⟩ : ∃ m, s.card = m + 1 := ⟨s.card - 1, by omega⟩
  rw [hm, Nat.add_sub_cancel] at h1
  rw [hm]
  have h3 : (v w₀ + 1) * (m + 1) = m * v w₀ + v w₀ + m + 1 := by ring
  rw [h3]
  omega

/-- A sum over `S` of terms bounded by `min Δ ⌈k/b⌉` is bounded by `∑_{u ∈ (a, b]} min Δ ⌈k/u⌉`
when `|S| = b - a`. -/
theorem alloc_sum_le_sum_Ioc {ι : Type*} (S : Finset ι) (f : ι → ℕ) (k Δ a b : ℕ)
    (hS : S.card = b - a) (hf : ∀ w ∈ S, f w ≤ min Δ (ceilDiv k b)) :
    ∑ w ∈ S, f w ≤ ∑ u ∈ Ioc a b, min Δ (ceilDiv k u) := by
  calc ∑ w ∈ S, f w ≤ ∑ w ∈ S, min Δ (ceilDiv k b) := sum_le_sum hf
    _ = ∑ u ∈ Ioc a b, min Δ (ceilDiv k b) := by
      rw [sum_const, sum_const, hS, Nat.card_Ioc]
    _ ≤ ∑ u ∈ Ioc a b, min Δ (ceilDiv k u) := by
      apply sum_le_sum
      intro u hu
      rw [mem_Ioc] at hu
      exact min_le_min_left _ (alloc_ceilDiv_anti (by omega) hu.2)

/-- Final accounting step of Lemma 2: `X + u₀ ≤ k + ∑_{u ∈ (x, u₀]} min Δ ⌈k/u⌉` implies
`X ≤ S_k(Δ)`. -/
theorem alloc_le_urnSum {k Δ x u₀ X : ℕ} (hΔ : 1 ≤ Δ) (hu₀ : u₀ ≤ k)
    (h : X + u₀ ≤ k + ∑ u ∈ Ioc x u₀, min Δ (ceilDiv k u)) : X ≤ urnSum k Δ := by
  have e : Icc 1 k = Ioc 0 k := by ext u; simp only [mem_Icc, mem_Ioc]; omega
  unfold urnSum
  rw [e, ← sum_Ioc_consecutive _ (Nat.zero_le u₀) hu₀]
  have h1 : ∑ u ∈ Ioc x u₀, min Δ (ceilDiv k u) ≤ ∑ u ∈ Ioc 0 u₀, min Δ (ceilDiv k u) :=
    sum_le_sum_of_subset (Ioc_subset_Ioc_left (Nat.zero_le x))
  have h2 : ∑ u ∈ Ioc u₀ k, 1 ≤ ∑ u ∈ Ioc u₀ k, min Δ (ceilDiv k u) := by
    apply sum_le_sum
    intro u hu
    rw [mem_Ioc] at hu
    refine le_min hΔ ?_
    rw [ceilDiv, Nat.le_div_iff_mul_le (by omega)]
    omega
  rw [sum_const, smul_eq_mul, mul_one, Nat.card_Ioc] at h2
  omega

/-- Abstract core of Lemma 2 of [CMV23, full version]: balanced allocation with removals. -/
theorem alloc_bound {ι : Type*} [DecidableEq ι] (k Δ : ℕ) (hΔ : 1 ≤ Δ)
    (O : ℕ → Finset ι) (c : ℕ → ι → ℕ) (A : ℕ → ℕ) (t₀ : ℕ)
    (hA0 : ∀ t < t₀, A t = 0)
    (hO : ∀ t, t₀ ≤ t → O (t + 1) ⊆ O t)
    (hc0 : ∀ w ∈ O t₀, c t₀ w = 0)
    (hmono : ∀ t, t₀ ≤ t → ∀ w ∈ O t, c t w ≤ c (t + 1) w)
    (hA : ∀ t, t₀ ≤ t → A t = ∑ w ∈ O t, (c (t + 1) w - c t w))
    (hbal : ∀ t, t₀ ≤ t → ∀ w ∈ O t, ∀ w' ∈ O t, c (t + 1) w ≤ c (t + 1) w' + 1)
    (hcap : ∀ t, t₀ ≤ t → ∑ w ∈ O t, (c (t + 1) w + 1) ≤ k)
    (hwin : ∀ s, t₀ ≤ s → (O s).Nonempty → (∀ w ∈ O s, Δ ≤ c (s + 1) w + 1) →
      ∀ t₁, ∑ t ∈ Ico (s + 1) t₁, A t + ∑ w ∈ O s, (c (s + 1) w + 1) ≤
        k + ∑ w ∈ O s \ O (s + 1), (c s w + 1)) :
    ∀ t₁, ∑ t ∈ range t₁, A t ≤ urnSum k Δ := by
  classical
  have hsub : ∀ t t', t₀ ≤ t → t ≤ t' → O t' ⊆ O t := by
    intro t t' ht htt'
    induction t', htt' using Nat.le_induction with
    | base => exact subset_rfl
    | succ n hn ih => exact (hO n (le_trans ht hn)).trans ih
  have hu₀ : (O t₀).card ≤ k := by
    calc (O t₀).card = ∑ w ∈ O t₀, 1 := by simp
      _ ≤ ∑ w ∈ O t₀, (c (t₀ + 1) w + 1) := sum_le_sum fun _ _ => by omega
      _ ≤ k := hcap t₀ le_rfl
  have hN' : ∀ t, t₀ ≤ t → ∑ w ∈ O t, (c (t + 1) w + 1) = ∑ w ∈ O t, (c t w + 1) + A t := by
    intro t ht
    rw [hA t ht, ← sum_add_distrib]
    apply sum_congr rfl
    intro w hw
    have := hmono t ht w hw
    omega
  have hsplit : ∀ t, t₀ ≤ t → ∑ w ∈ O t, (c (t + 1) w + 1) =
      ∑ w ∈ O (t + 1), (c (t + 1) w + 1) + ∑ w ∈ O t \ O (t + 1), (c (t + 1) w + 1) := by
    intro t ht
    exact (sum_sdiff (hO t ht)).symm.trans (add_comm _ _)
  have hNk : ∀ t, t₀ ≤ t → ∑ w ∈ O t, (c t w + 1) ≤ k := by
    intro t ht
    have := hN' t ht
    have := hcap t ht
    omega
  have hceil : ∀ t, t₀ ≤ t → ∀ w ∈ O t, c (t + 1) w + 1 ≤ ceilDiv k (O t).card :=
    fun t ht => alloc_balanced_le_ceilDiv (O t) (fun w => c (t + 1) w) (hbal t ht) (hcap t ht)
  have hcard : ∀ t, t₀ ≤ t → (O (t + 1)).card ≤ (O t).card := fun t ht => card_le_card (hO t ht)
  have hcard₀ : ∀ t, t₀ ≤ t → (O t).card ≤ (O t₀).card :=
    fun t ht => card_le_card (hsub t₀ t le_rfl ht)
  -- invariant while all rounds are below the threshold
  have hinv : ∀ t, t₀ ≤ t → (∀ t', t₀ ≤ t' → t' < t → ∃ w ∈ O t', c (t' + 1) w + 1 < Δ) →
      ∑ t' ∈ range t, A t' + (O t₀).card ≤
        ∑ w ∈ O t, (c t w + 1) + ∑ u ∈ Ioc (O t).card (O t₀).card, min Δ (ceilDiv k u) := by
    intro t ht
    induction t, ht using Nat.le_induction with
    | base =>
      intro _
      have h1 : ∑ t' ∈ range t₀, A t' = 0 := sum_eq_zero fun t' ht' => hA0 t' (mem_range.1 ht')
      have h2 : ∑ w ∈ O t₀, (c t₀ w + 1) = (O t₀).card := by
        rw [sum_congr rfl fun w hw => by rw [hc0 w hw]]
        simp
      simp [h1, h2]
    | succ t ht ih =>
      intro hB
      have ih := ih fun t' h1 h2 => hB t' h1 (by omega)
      obtain ⟨w₀, hw₀, hlt⟩ := hB t ht (by omega)
      have hR : ∑ w ∈ O t \ O (t + 1), (c (t + 1) w + 1) ≤
          ∑ u ∈ Ioc (O (t + 1)).card (O t).card, min Δ (ceilDiv k u) := by
        apply alloc_sum_le_sum_Ioc
        · rw [card_sdiff_of_subset (hO t ht)]
        · intro w hw
          have hw' := (mem_sdiff.1 hw).1
          refine le_min ?_ (hceil t ht w hw')
          have := hbal t ht w hw' w₀ hw₀
          omega
      have hc1 := hcard t ht
      have hc2 := hcard₀ t ht
      rw [sum_range_succ, ← sum_Ioc_consecutive _ hc1 hc2]
      have := hN' t ht
      have := hsplit t ht
      omega
  intro t₁
  by_cases ht₁ : t₁ ≤ t₀
  · have : ∑ t ∈ range t₁, A t = 0 :=
      sum_eq_zero fun t ht => hA0 t (by rw [mem_range] at ht; omega)
    omega
  push Not at ht₁
  by_cases hex : ∃ s, t₀ ≤ s ∧ s < t₁ ∧ ∀ w ∈ O s, Δ ≤ c (s + 1) w + 1
  · obtain ⟨s, ⟨hs0, hs1, hsB⟩, hmin⟩ : ∃ s, (t₀ ≤ s ∧ s < t₁ ∧ ∀ w ∈ O s, Δ ≤ c (s + 1) w + 1) ∧
        ∀ t < s, ¬ (t₀ ≤ t ∧ t < t₁ ∧ ∀ w ∈ O t, Δ ≤ c (t + 1) w + 1) :=
      ⟨Nat.find hex, Nat.find_spec hex, fun t ht => Nat.find_min hex ht⟩
    have hmin' : ∀ t', t₀ ≤ t' → t' < s → ∃ w ∈ O t', c (t' + 1) w + 1 < Δ := by
      intro t' h1 h2
      by_contra h
      push Not at h
      exact hmin t' h2 ⟨h1, by omega, h⟩
    have hI := hinv s hs0 hmin'
    have hcs := hcard₀ s hs0
    have hsplitA : ∑ t ∈ range t₁, A t =
        ∑ t ∈ range s, A t + A s + ∑ t ∈ Ico (s + 1) t₁, A t := by
      rw [← sum_range_succ, sum_range_add_sum_Ico _ (by omega)]
    rcases (O s).eq_empty_or_nonempty with hE | hne
    · have hz : ∑ t ∈ Ico (s + 1) t₁, A t = 0 := sum_eq_zero fun t ht => by
        rw [mem_Ico] at ht
        have h' := hsub s t hs0 (by omega)
        rw [hE, subset_empty] at h'
        rw [hA t (by omega), h']
        simp
      have hAs : A s = 0 := by rw [hA s hs0, hE]; simp
      apply alloc_le_urnSum (x := (O s).card) hΔ hu₀
      have := hNk s hs0
      omega
    · have hW := hwin s hs0 hne hsB t₁
      have hQ : ∑ w ∈ O s \ O (s + 1), (c s w + 1) ≤
          ∑ u ∈ Ioc (O (s + 1)).card (O s).card, min Δ (ceilDiv k u) := by
        apply alloc_sum_le_sum_Ioc
        · rw [card_sdiff_of_subset (hO s hs0)]
        · intro w hw
          have hw' := (mem_sdiff.1 hw).1
          refine le_min ?_ ((Nat.add_le_add_right (hmono s hs0 w hw') 1).trans (hceil s hs0 w hw'))
          rcases Nat.eq_or_lt_of_le hs0 with h | h
          · subst h
            rw [hc0 w hw']
            omega
          · obtain ⟨w₀, hw₀, hlt⟩ := hmin' (s - 1) (by omega) (by omega)
            have := hbal (s - 1) (by omega) w (hsub (s - 1) s (by omega) (by omega) hw') w₀ hw₀
            have e : s - 1 + 1 = s := by omega
            rw [e] at this hlt
            omega
      have hc1 := hcard s hs0
      have hN's := hN' s hs0
      apply alloc_le_urnSum (x := (O (s + 1)).card) hΔ hu₀
      rw [← sum_Ioc_consecutive _ hc1 hcs]
      omega
  · push Not at hex
    have hI := hinv t₁ ht₁.le fun t' h1 h2 => by
      obtain ⟨w, hw, h⟩ := hex t' h1 h2
      exact ⟨w, hw, h⟩
    apply alloc_le_urnSum (x := (O t₁).card) hΔ hu₀
    have := hNk t₁ ht₁.le
    omega

end Podc.TreeExplorationBFDN
