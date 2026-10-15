import Papers.PODC2024.ListDefectiveColoring.Basic

/-!
# Lemma 3.1 of [FK24]: choosing the sublist `S_v` in Phase I

In Phase I of the Two-Sweep algorithm a node `v` knows, for every colour `x ∈ L_v`, the number
`k_v(x)` of out-neighbours `u ∈ N_<(v)` (already processed) with `x ∈ S_u`, and it knows
`|N_>(v)|`. It chooses `S_v ⊆ L_v` with

* (3) `|S_v| ≤ p`, and
* (4) `|N_>(v)| + ∑_{x ∈ S_v} k_v(x) < ∑_{x ∈ S_v} (d_v(x) + 1)`.

Algorithm 1 sorts `L_v` by `d_v(x) − k_v(x)` and takes the first `p` colours, i.e. it takes a
`min(p, |L_v|)`-subset maximizing `∑_{x ∈ S} (d_v(x) − k_v(x))`. We model this as *any* such
maximizer (`IsBestSubset`), which covers every tie-breaking of the sort.

## Main results

* `sum_powersetCard_sum`: double counting `∑_{S ∈ (L choose m)} ∑_{x ∈ S} g x
  = (|L|-1 choose m-1) ∑_{x ∈ L} g x` (the identity used in the paper's proof).
* `IsBestSubset.mul_sum_le`: a best `m`-subset has at least the average value,
  `m ∑_{x ∈ L} g x ≤ |L| ∑_{x ∈ S} g x`.
* `IsBestSubset.lemma_3_1`: Lemma 3.1 together with the Remark after it: every best subset (in
  particular the sorted prefix of Algorithm 1) satisfies (3) and (4).
* `lemma_3_1`: the existence statement of Lemma 3.1.

The paper's final pigeonhole step compares with `∑_{x ∈ L_v} (d_v(x)+1)` instead of
`∑_{x ∈ S_v} (d_v(x)+1)`, which does not give (4); the correct argument averages the *difference*
of the two sides of (4) over all `p`-subsets (equivalently: a best subset is at least as good as the
average). See `differencies.md`.
-/

open Finset

namespace FK24

variable {α : Type*}

/-- Double counting over `m`-subsets (`1 ≤ m`):
`∑_{S ∈ (L choose m)} ∑_{x ∈ S} g x = (|L| - 1 choose m - 1) · ∑_{x ∈ L} g x`. -/
theorem sum_powersetCard_sum [DecidableEq α] (L : Finset α) {m : ℕ} (hm : 1 ≤ m) (g : α → ℤ) :
    ∑ S ∈ L.powersetCard m, ∑ x ∈ S, g x =
      ((L.card - 1).choose (m - 1) : ℤ) * ∑ x ∈ L, g x := by
  rw [Finset.sum_comm' (t' := L) (s' := fun x => (L.powersetCard m).filter (fun S => x ∈ S))]
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [Finset.sum_const, nsmul_eq_mul]
    congr 1
    have h := Finset.card_filter_powersetCard_subset {x} L m (by simpa using hx)
      (by simpa using hm)
    simp only [Finset.singleton_subset_iff, Finset.card_singleton] at h
    rw [h]
  · intro S x
    simp only [Finset.mem_filter, Finset.mem_powersetCard]
    constructor
    · intro h; exact ⟨h, h.1.1 h.2⟩
    · intro h; exact h.1

/-- `S` is a best `m`-subset of `L` for the score `g`: it has `m` elements and maximizes
`∑_{x ∈ S} g x` among all `m`-subsets of `L`. Sorting `L` by `g` (descending) and taking the first
`m` elements produces such a set. -/
def IsBestSubset (L : Finset α) (m : ℕ) (g : α → ℤ) (S : Finset α) : Prop :=
  S ∈ L.powersetCard m ∧ ∀ T ∈ L.powersetCard m, ∑ x ∈ T, g x ≤ ∑ x ∈ S, g x

theorem exists_isBestSubset (L : Finset α) {m : ℕ} (hm : m ≤ L.card) (g : α → ℤ) :
    ∃ S, IsBestSubset L m g S := by
  obtain ⟨S, hS, hmax⟩ := Finset.exists_max_image (L.powersetCard m) (fun S => ∑ x ∈ S, g x)
    (Finset.powersetCard_nonempty.2 hm)
  exact ⟨S, hS, hmax⟩

/-- A best `m`-subset is at least as good as the average `m`-subset:
`m · ∑_{x ∈ L} g x ≤ |L| · ∑_{x ∈ S} g x`. -/
theorem IsBestSubset.mul_sum_le {L : Finset α} {m : ℕ} {g : α → ℤ} {S : Finset α}
    (hS : IsBestSubset L m g S) (hm : 1 ≤ m) :
    (m : ℤ) * ∑ x ∈ L, g x ≤ L.card * ∑ x ∈ S, g x := by
  classical
  obtain ⟨hSmem, hmax⟩ := hS
  have hmL : m ≤ L.card := (Finset.mem_powersetCard.1 hSmem).2 ▸
    Finset.card_le_card (Finset.mem_powersetCard.1 hSmem).1
  -- sum over all m-subsets ≤ (number of subsets) * best
  have h1 : ∑ T ∈ L.powersetCard m, ∑ x ∈ T, g x ≤
      ((L.powersetCard m).card : ℤ) * ∑ x ∈ S, g x := by
    calc ∑ T ∈ L.powersetCard m, ∑ x ∈ T, g x
        ≤ ∑ _T ∈ L.powersetCard m, ∑ x ∈ S, g x := Finset.sum_le_sum hmax
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
  rw [sum_powersetCard_sum L hm, Finset.card_powersetCard] at h1
  generalize L.card = n at h1 hmL ⊢
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at h1
  have hid : ((n' + 1 : ℕ) : ℤ) * (n'.choose m' : ℤ) =
      ((n' + 1).choose (m' + 1) : ℤ) * ((m' + 1 : ℕ) : ℤ) := by
    exact_mod_cast Nat.add_one_mul_choose_eq n' m'
  have hpos : (0 : ℤ) < ((n' + 1).choose (m' + 1) : ℤ) := by
    exact_mod_cast Nat.choose_pos (by omega)
  set c := ((n' + 1).choose (m' + 1) : ℤ)
  set A := ∑ x ∈ L, g x
  set B := ∑ x ∈ S, g x
  have h2 := mul_le_mul_of_nonneg_left h1 (show (0 : ℤ) ≤ ((n' + 1 : ℕ) : ℤ) by positivity)
  have h3 : c * (((m' + 1 : ℕ) : ℤ) * A) ≤ c * (((n' + 1 : ℕ) : ℤ) * B) := by
    have e : ((n' + 1 : ℕ) : ℤ) * ((n'.choose m' : ℤ) * A) = c * (((m' + 1 : ℕ) : ℤ) * A) := by
      rw [← mul_assoc, hid, mul_assoc]
    have e' : ((n' + 1 : ℕ) : ℤ) * (c * B) = c * (((n' + 1 : ℕ) : ℤ) * B) := by ring
    rw [← e, ← e']; exact h2
  exact le_of_mul_le_mul_left h3 hpos

/-- Optimality of the sorted prefix: if `l` is sorted by `g` in descending order, then the first
`m` entries of `l` have maximal `g`-sum among all `m`-subsets of `l`. -/
theorem sum_le_sum_take [DecidableEq α] {g : α → ℤ} :
    ∀ (l : List α), l.Nodup → l.Pairwise (fun a b => g b ≤ g a) →
      ∀ (m : ℕ) (T : Finset α), T ⊆ l.toFinset → T.card = m →
        ∑ x ∈ T, g x ≤ ∑ x ∈ (l.take m).toFinset, g x
  | [], _, _, m, T, hT, hcard => by
    have : T = ∅ := by simpa using hT
    subst this; simp
  | a :: l, hnd, hs, m, T, hT, hcard => by
    obtain ⟨hal, hnd'⟩ := List.nodup_cons.1 hnd
    obtain ⟨hga, hs'⟩ := List.pairwise_cons.1 hs
    rcases m with _ | k
    · have : T = ∅ := Finset.card_eq_zero.1 hcard
      subst this; simp
    · rw [List.take_succ_cons, List.toFinset_cons,
        Finset.sum_insert (fun h => hal (List.mem_of_mem_take (List.mem_toFinset.1 h)))]
      by_cases haT : a ∈ T
      · rw [← Finset.insert_erase haT, Finset.sum_insert (Finset.notMem_erase a T)]
        have hT' : T.erase a ⊆ l.toFinset := by
          intro x hx
          obtain ⟨hxa, hxT⟩ := Finset.mem_erase.1 hx
          have := hT hxT
          simp only [List.toFinset_cons, Finset.mem_insert, List.mem_toFinset] at this
          exact List.mem_toFinset.2 (this.resolve_left hxa)
        have := sum_le_sum_take l hnd' hs' k (T.erase a) hT'
          (by rw [Finset.card_erase_of_mem haT, hcard]; rfl)
        linarith
      · obtain ⟨t, htT⟩ : T.Nonempty := Finset.card_pos.1 (by omega)
        rw [← Finset.insert_erase htT, Finset.sum_insert (Finset.notMem_erase t T)]
        have hT' : T ⊆ l.toFinset := by
          intro x hxT
          have := hT hxT
          simp only [List.toFinset_cons, Finset.mem_insert, List.mem_toFinset] at this
          exact List.mem_toFinset.2 (this.resolve_left (fun h => haT (h ▸ hxT)))
        have ht : g t ≤ g a := hga t (List.mem_toFinset.1 (hT' htT))
        have := sum_le_sum_take l hnd' hs' k (T.erase t) ((Finset.erase_subset t T).trans hT')
          (by rw [Finset.card_erase_of_mem htT, hcard]; rfl)
        linarith

/-- Line 4 of Algorithm 1 of [FK24]: sorting `L_v` by `g` in descending order (`l` is such a
sorted enumeration of `L`) and taking the first `m ≤ |L|` colours yields a best `m`-subset. -/
theorem isBestSubset_take [DecidableEq α] {g : α → ℤ} (l : List α) (hnd : l.Nodup)
    (hs : l.Pairwise (fun a b => g b ≤ g a)) {m : ℕ} (hm : m ≤ l.length) :
    IsBestSubset l.toFinset m g (l.take m).toFinset := by
  refine ⟨Finset.mem_powersetCard.2 ⟨?_, ?_⟩, fun T hT => ?_⟩
  · intro x hx
    exact List.mem_toFinset.2 (List.mem_of_mem_take (List.mem_toFinset.1 hx))
  · rw [List.toFinset_card_of_nodup (hnd.sublist (List.take_sublist m l)), List.length_take]
    omega
  · obtain ⟨hTsub, hTcard⟩ := Finset.mem_powersetCard.1 hT
    exact sum_le_sum_take l hnd hs m T hTsub hTcard

/-- The slack condition (2) of [FK24], `∑_{x ∈ L_v} (d_v(x)+1) > max(p, |L_v|/p) · β_v`, in the
equivalent natural-number form `max(p², |L_v|) · β_v < p · ∑_{x ∈ L_v} (d_v(x)+1)`. -/
theorem slack_iff_nat {p : ℕ} (hp : 1 ≤ p) (n β W : ℕ) :
    (max (p : ℝ) ((n : ℝ) / p) * β < W) ↔ max (p ^ 2) n * β < p * W := by
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  have key : max (p : ℝ) ((n : ℝ) / p) * p = ((max (p ^ 2) n : ℕ) : ℝ) := by
    rw [max_mul_of_nonneg _ _ hp'.le, div_mul_cancel₀ _ hp'.ne']
    push_cast; rw [sq]
  constructor
  · intro h
    have := mul_lt_mul_of_pos_right h hp'
    rw [mul_right_comm, key] at this
    exact_mod_cast (by linarith : ((max (p ^ 2) n : ℕ) : ℝ) * β < p * W)
  · intro h
    have h' : ((max (p ^ 2) n : ℕ) : ℝ) * β < p * W := by exact_mod_cast h
    rw [← key] at h'
    nlinarith

/-- **Lemma 3.1** of [FK24] (with the Remark following it). Let `v` be active in Phase I, with
`|N_<(v)| = nlt`, `|N_>(v)| = ngt`, `nlt + ngt ≤ β` (`β = β_v`), and let `k = k_v` count the
occurrences of colours in the sublists `S_u` (`|S_u| ≤ p`) of the out-neighbours in `N_<(v)`, so
that `∑_{x ∈ L_v} k_v(x) ≤ nlt · p`. If the slack condition (2) holds (in the form
`max(p², |L_v|) · β < p · ∑_{x ∈ L_v} (d_v(x)+1)`, see `slack_iff_nat`), then every
`min(p, |L_v|)`-subset `S` of `L_v` maximizing `∑_{x ∈ S} (d_v(x) − k_v(x))` satisfies (3) and
(4): `|S| ≤ p` and `ngt + ∑_{x ∈ S} k_v(x) < ∑_{x ∈ S} (d_v(x) + 1)`. -/
theorem IsBestSubset.lemma_3_1 {L : Finset α} {d k : α → ℕ} {p nlt ngt β : ℕ} (hp : 1 ≤ p)
    (hβ : nlt + ngt ≤ β) (hk : ∑ x ∈ L, k x ≤ nlt * p)
    (hslack : max (p ^ 2) L.card * β < p * ∑ x ∈ L, (d x + 1)) {S : Finset α}
    (hS : IsBestSubset L (min p L.card) (fun x => (d x : ℤ) - k x) S) :
    S.card ≤ p ∧ ngt + ∑ x ∈ S, k x < ∑ x ∈ S, (d x + 1) := by
  have hSmem := Finset.mem_powersetCard.1 hS.1
  refine ⟨hSmem.2 ▸ min_le_left _ _, ?_⟩
  set n := L.card with hn
  set W := ∑ x ∈ L, (d x + 1) with hW
  have hWsum : (W : ℤ) = ∑ x ∈ L, (d x : ℤ) + n := by
    simp [hW, Finset.sum_add_distrib, hn]
  have hn1 : 1 ≤ n := by
    by_contra h0
    have : n = 0 := by omega
    have hL : L = ∅ := Finset.card_eq_zero.1 this
    simp [hW, hL] at hslack
  -- work in ℤ
  have hgoal : ((ngt : ℕ) : ℤ) + ∑ x ∈ S, (k x : ℤ) < ∑ x ∈ S, ((d x : ℤ) + 1) := by
    rcases le_total p n with hpn | hnp
    · -- m = p
      have hm : min p n = p := min_eq_left hpn
      have havg := hS.mul_sum_le (by rw [hm]; exact hp)
      rw [hm] at havg hSmem
      simp only [Finset.sum_sub_distrib] at havg
      have hsumS : ∑ x ∈ S, ((d x : ℤ) + 1) = ∑ x ∈ S, (d x : ℤ) + p := by
        simp [Finset.sum_add_distrib, hSmem.2]
      rw [hsumS]
      have hslackZ : ((max (p ^ 2) n : ℕ) : ℤ) * β < p * W := by exact_mod_cast hslack
      have hkZ : ∑ x ∈ L, (k x : ℤ) ≤ nlt * p := by exact_mod_cast hk
      have hβZ : (nlt : ℤ) + ngt ≤ β := by exact_mod_cast hβ
      have hmax1 : (p : ℤ) ^ 2 ≤ ((max (p ^ 2) n : ℕ) : ℤ) := by exact_mod_cast le_max_left _ _
      have hmax2 : (n : ℤ) ≤ ((max (p ^ 2) n : ℕ) : ℤ) := by exact_mod_cast le_max_right _ _
      have hn1Z : (1 : ℤ) ≤ n := by exact_mod_cast hn1
      have hpZ : (1 : ℤ) ≤ p := by exact_mod_cast hp
      set M : ℤ := ((max (p ^ 2) n : ℕ) : ℤ)
      set A := ∑ x ∈ S, (d x : ℤ)
      set B := ∑ x ∈ S, (k x : ℤ)
      set DL := ∑ x ∈ L, (d x : ℤ)
      set KL := ∑ x ∈ L, (k x : ℤ)
      -- havg : p * (DL - KL) ≤ n * (A - B)
      -- goal : ngt + B < A + p ; multiply by n
      have hngt : (0 : ℤ) ≤ ngt := by positivity
      have hnlt : (0 : ℤ) ≤ nlt := by positivity
      have key : (n : ℤ) * ngt < n * (A - B + p) := by
        have e1 : (n : ℤ) * (A - B + p) ≥ p * (DL - KL) + n * p := by nlinarith
        have e2 : (p : ℤ) * (DL - KL) + n * p = p * W - p * KL := by rw [hWsum]; ring
        have e3 : (p : ℤ) * KL ≤ nlt * p ^ 2 := by nlinarith
        have e4 : M * β ≥ M * (nlt + ngt) := by
          apply mul_le_mul_of_nonneg_left hβZ; positivity
        have e5 : M * (nlt + ngt) - nlt * p ^ 2 ≥ n * ngt := by nlinarith
        nlinarith
      have := lt_of_mul_lt_mul_left key (by positivity)
      linarith
    · -- m = n, S = L
      have hm : min p n = n := min_eq_right hnp
      rw [hm] at hSmem
      have hSL : S = L := Finset.eq_of_subset_of_card_le hSmem.1 (by rw [hSmem.2])
      subst hSL
      have hslackZ : ((max (p ^ 2) n : ℕ) : ℤ) * β < p * W := by exact_mod_cast hslack
      have hkZ : ∑ x ∈ S, (k x : ℤ) ≤ nlt * p := by exact_mod_cast hk
      have hβZ : (nlt : ℤ) + ngt ≤ β := by exact_mod_cast hβ
      have hmax1 : (p : ℤ) ^ 2 ≤ ((max (p ^ 2) n : ℕ) : ℤ) := by exact_mod_cast le_max_left _ _
      have hpZ : (1 : ℤ) ≤ p := by exact_mod_cast hp
      have hWS : (W : ℤ) = ∑ x ∈ S, ((d x : ℤ) + 1) := by simp [hW]
      rw [← hWS]
      -- p * W > p^2 * β ≥ p * (nlt * p + ngt)
      have e1 : (p : ℤ) * W > p * (nlt * p + ngt) := by
        have : ((max (p ^ 2) n : ℕ) : ℤ) * β ≥ p ^ 2 * β :=
          mul_le_mul_of_nonneg_right hmax1 (by positivity)
        have hngt0 : (0 : ℤ) ≤ ngt := by positivity
        have : (p : ℤ) ^ 2 * β ≥ p * (nlt * p + ngt) := by
          have h1 : (p : ℤ) ^ 2 * β ≥ p ^ 2 * (nlt + ngt) :=
            mul_le_mul_of_nonneg_left hβZ (by positivity)
          have h2 : (p : ℤ) ^ 2 * ngt ≥ p * ngt :=
            mul_le_mul_of_nonneg_right (by nlinarith) hngt0
          nlinarith
        linarith
      have e2 : (W : ℤ) > nlt * p + ngt := lt_of_mul_lt_mul_left e1 (by positivity)
      linarith
  exact_mod_cast hgoal

/-- **Lemma 3.1** of [FK24] (existence form): under the hypotheses of `IsBestSubset.lemma_3_1`
there is `S_v ⊆ L_v` satisfying (3) and (4). -/
theorem lemma_3_1 {L : Finset α} {d k : α → ℕ} {p nlt ngt β : ℕ} (hp : 1 ≤ p)
    (hβ : nlt + ngt ≤ β) (hk : ∑ x ∈ L, k x ≤ nlt * p)
    (hslack : max (p ^ 2) L.card * β < p * ∑ x ∈ L, (d x + 1)) :
    ∃ S ⊆ L, S.card ≤ p ∧ ngt + ∑ x ∈ S, k x < ∑ x ∈ S, (d x + 1) := by
  obtain ⟨S, hS⟩ := exists_isBestSubset L (min_le_right p L.card) (fun x => (d x : ℤ) - k x)
  exact ⟨S, (Finset.mem_powersetCard.1 hS.1).1, hS.lemma_3_1 hp hβ hk hslack⟩

end FK24
