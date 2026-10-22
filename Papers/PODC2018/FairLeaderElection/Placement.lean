import Papers.PODC2018.FairLeaderElection.Rushing

/-!
# Placing a coalition with prescribed segment lengths

Given `k ≥ 1` segment lengths `g 0, …, g (k-1)` with `∑ (g t + 1) = n` and `g (k-1) ≥ 1`, the
coalition `place n k g` puts adversary `t` at position `pos g t = 1 + ∑_{s<t} (g s + 1)`; then the
honest segment after adversary `t` has length `g t`, the origin `0` lies in the last segment, and the
adversary before adversary `t+1` is adversary `t`.

We also provide a "greedy from the end" choice of segment lengths below given caps (`fillGaps`),
used for the equally spaced coalition of Theorem 4.2 and the cubic coalition of Theorem 4.3.
-/

namespace Podc.FairLeaderElection

open Cslib.UniRing
open Fin.NatCast Fin.CommRing

variable {n : ℕ} [NeZero n]

theorem gap_eq_iff {C : Finset (Fin n)} {a : Fin n} (ha : a ∈ C) {g : ℕ} :
    gap C a = g ↔ a + ((g + 1 : ℕ) : Fin n) ∈ C ∧ ∀ s < g, a + ((s + 1 : ℕ) : Fin n) ∉ C := by
  constructor
  · rintro rfl; exact ⟨gap_mem ha, fun s hs => not_mem_of_lt_gap ha hs⟩
  · rintro ⟨h1, h2⟩
    apply le_antisymm
    · by_contra hlt; push_neg at hlt
      exact not_mem_of_lt_gap ha hlt h1
    · by_contra hlt; push_neg at hlt
      exact h2 _ hlt (gap_mem ha)

/-- Position (as a natural number) of adversary `t`. -/
def posN (g : ℕ → ℕ) (t : ℕ) : ℕ := 1 + ∑ s ∈ Finset.range t, (g s + 1)

theorem posN_succ (g : ℕ → ℕ) (t : ℕ) : posN g (t + 1) = posN g t + g t + 1 := by
  simp [posN, Finset.sum_range_succ]; ring

theorem posN_strictMono (g : ℕ → ℕ) : StrictMono (posN g) :=
  strictMono_nat_of_lt_succ fun t => by rw [posN_succ]; omega

variable (n) in
/-- The coalition with segment lengths `g 0, …, g (k-1)`. -/
def place (k : ℕ) (g : ℕ → ℕ) : Finset (Fin n) :=
  (Finset.range k).image fun t => ((posN g t : ℕ) : Fin n)

section Place

variable {k : ℕ} {g : ℕ → ℕ} (hk : 1 ≤ k) (hsum : ∑ t ∈ Finset.range k, (g t + 1) = n)
  (hlast : 1 ≤ g (k - 1))
include hk hsum hlast

theorem posN_last : posN g (k - 1) + g (k - 1) + 1 = n + 1 := by
  rw [← posN_succ, Nat.sub_add_cancel hk, posN, hsum]; ring

theorem posN_lt {t : ℕ} (ht : t < k) : 1 ≤ posN g t ∧ posN g t < n := by
  have h1 := posN_last hk hsum hlast
  have h2 : posN g t ≤ posN g (k - 1) := (posN_strictMono g).monotone (by omega)
  exact ⟨by simp [posN], by omega⟩

theorem mem_place_iff (x : Fin n) :
    x ∈ place n k g ↔ ∃ t < k, x.val = posN g t := by
  simp only [place, Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨t, ht, by rw [Fin.val_natCast, Nat.mod_eq_of_lt (posN_lt hk hsum hlast ht).2]⟩
  · rintro ⟨t, ht, hx⟩
    exact ⟨t, ht, Fin.ext (by rw [Fin.val_natCast, Nat.mod_eq_of_lt (posN_lt hk hsum hlast ht).2, hx])⟩

theorem card_place : (place n k g).card = k := by
  rw [place, Finset.card_image_of_injOn, Finset.card_range]
  intro a ha b hb hab
  simp only [Finset.coe_range, Set.mem_Iio] at ha hb
  have := congrArg Fin.val hab
  simp only [Fin.val_natCast, Nat.mod_eq_of_lt (posN_lt hk hsum hlast ha).2,
    Nat.mod_eq_of_lt (posN_lt hk hsum hlast hb).2] at this
  exact (posN_strictMono g).injective this

theorem zero_not_mem_place : (0 : Fin n) ∉ place n k g := by
  rw [mem_place_iff hk hsum hlast]
  rintro ⟨t, ht, h⟩
  have := (posN_lt hk hsum hlast ht).1
  simp at h; omega

theorem place_nonempty : (place n k g).Nonempty :=
  ⟨_, Finset.mem_image_of_mem _ (Finset.mem_range.mpr (show 0 < k by omega))⟩

/-- The adversary `t` of the placed coalition. -/
def advAt (g : ℕ → ℕ) (t : ℕ) : Fin n := ((posN g t : ℕ) : Fin n)

theorem advAt_mem {t : ℕ} (ht : t < k) : (advAt g t : Fin n) ∈ place n k g :=
  Finset.mem_image_of_mem _ (Finset.mem_range.mpr ht)

theorem gap_place {t : ℕ} (ht : t < k) : gap (place n k g) (advAt g t) = g t := by
  rw [gap_eq_iff (advAt_mem hk hsum hlast ht)]
  have hP := posN_lt hk hsum hlast ht
  constructor
  · rcases Nat.lt_or_ge (t + 1) k with h | h
    · have e : advAt g t + ((g t + 1 : ℕ) : Fin n) = (advAt g (t + 1) : Fin n) := by
        simp only [advAt, posN_succ]; push_cast; ring
      rw [e]; exact advAt_mem hk hsum hlast h
    · have ht' : t = k - 1 := by omega
      subst ht'
      convert advAt_mem hk hsum hlast (show 0 < k by omega) using 1
      have h1 := posN_last hk hsum hlast
      simp only [advAt]
      rw [← Nat.cast_add, show posN g (k - 1) + (g (k - 1) + 1) = n + 1 by omega]
      simp [posN]
  · intro s hs
    rw [mem_place_iff hk hsum hlast]
    rintro ⟨u, hu, hval⟩
    simp only [advAt, Fin.val_add, Fin.val_natCast, Nat.mod_eq_of_lt hP.2] at hval
    by_cases hlt : posN g t + (s + 1) < n
    · rw [Nat.mod_eq_of_lt (by rw [Nat.mod_eq_of_lt (by omega)]; exact hlt),
        Nat.mod_eq_of_lt (by omega)] at hval
      -- `posN g t < posN g u < posN g (t+1)` is impossible
      have h1 : t < u := (posN_strictMono g).lt_iff_lt.mp (by omega)
      have h2 : u < t + 1 := (posN_strictMono g).lt_iff_lt.mp (by rw [posN_succ]; omega)
      omega
    · have h1 := posN_last hk hsum hlast
      have h2 : posN g t ≤ posN g (k - 1) := (posN_strictMono g).monotone (by omega)
      have hu' := posN_lt hk hsum hlast hu
      have hK : posN g k = n + 1 := by rw [posN, hsum]; ring
      have h3 : posN g (t + 1) ≤ posN g k := (posN_strictMono g).monotone (by omega)
      rw [posN_succ, hK] at h3
      have hs1 : s + 1 < n := by omega
      rw [Nat.mod_eq_of_lt hs1] at hval
      have : posN g t + (s + 1) < 2 * n := by omega
      rw [show posN g t + (s + 1) = (posN g t + (s + 1) - n) + n by omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt (by omega)] at hval
      -- then `t = k - 1` and the position wraps to `≤ g (k-1)`, before `posN g 0 = 1`? no:
      have ht' : t = k - 1 := by
        by_contra hne
        have : posN g (t + 1) ≤ posN g (k - 1) := (posN_strictMono g).monotone (by omega)
        rw [posN_succ] at this; omega
      subst ht'
      have h0 : posN g 0 = 1 := by simp [posN]
      have : posN g u ≥ 1 := hu'.1
      omega

theorem eq_advAt {a : Fin n} (ha : a ∈ place n k g) : ∃ t < k, a = advAt g t := by
  obtain ⟨t, ht, hv⟩ := (mem_place_iff hk hsum hlast a).mp ha
  exact ⟨t, ht, Fin.ext (by rw [hv, advAt, Fin.val_natCast,
    Nat.mod_eq_of_lt (posN_lt hk hsum hlast ht).2])⟩

theorem next_advAt {t : ℕ} (ht : t + 1 < k) :
    next (place n k g) (advAt g t) = (advAt g (t + 1) : Fin n) := by
  rw [next, gap_place hk hsum hlast (by omega)]
  simp only [advAt, posN_succ]; push_cast; ring

theorem prev_advAt_succ {t : ℕ} (ht : t + 1 < k) :
    prev (place n k g) (advAt g (t + 1)) = (advAt g t : Fin n) := by
  rw [← next_advAt hk hsum hlast ht, prev_next (place_nonempty hk hsum hlast)
    (advAt_mem hk hsum hlast (by omega))]

theorem prev_advAt_zero : prev (place n k g) (advAt g 0) = (advAt g (k - 1) : Fin n) := by
  have hn : next (place n k g) (advAt g (k - 1)) = (advAt g 0 : Fin n) := by
    rw [next, gap_place hk hsum hlast (by omega)]
    have h1 := posN_last hk hsum hlast
    simp only [advAt]
    rw [← Nat.cast_add, show posN g (k - 1) + (g (k - 1) + 1) = n + 1 by omega]
    simp [posN]
  rw [← hn, prev_next (place_nonempty hk hsum hlast) (advAt_mem hk hsum hlast (by omega))]

end Place

/-! ### Greedy choice of segment lengths -/

/-- `∑_{t ≤ s < k} c s`. -/
def capSum (c : ℕ → ℕ) (k t : ℕ) : ℕ := ∑ s ∈ Finset.Ico t k, c s

/-- Greedy from the end: fill the segments `k-1, k-2, …` up to their caps `c` until the total
`T` is used up. -/
def fillGaps (c : ℕ → ℕ) (k T t : ℕ) : ℕ := min T (capSum c k t) - min T (capSum c k (t + 1))

theorem capSum_succ (c : ℕ → ℕ) {k t : ℕ} (ht : t < k) :
    capSum c k t = c t + capSum c k (t + 1) := by
  rw [capSum, Finset.sum_eq_sum_Ico_succ_bot ht]; rfl

theorem capSum_ge (c : ℕ → ℕ) {k t : ℕ} (ht : k ≤ t) : capSum c k t = 0 := by
  simp [capSum, Finset.Ico_eq_empty_of_le ht]

theorem capSum_anti (c : ℕ → ℕ) (k t : ℕ) : capSum c k (t + 1) ≤ capSum c k t := by
  rcases Nat.lt_or_ge t k with h | h
  · rw [capSum_succ c h]; omega
  · rw [capSum_ge c h, capSum_ge c (by omega)]

theorem fillGaps_le (c : ℕ → ℕ) {k : ℕ} (T : ℕ) {t : ℕ} (ht : t < k) : fillGaps c k T t ≤ c t := by
  unfold fillGaps; rw [capSum_succ c ht]; omega

theorem fillGaps_zero_of_lt (c : ℕ → ℕ) {k T t : ℕ} (ht : t + 1 < k)
    (h : fillGaps c k T (t + 1) < c (t + 1)) : fillGaps c k T t = 0 := by
  unfold fillGaps at *
  rw [capSum_succ c (show t + 1 < k from ht)] at h
  have := capSum_anti c k (t + 1 + 1)
  rw [capSum_succ c (show t < k by omega), capSum_succ c ht]
  omega

theorem fillGaps_last (c : ℕ → ℕ) {k : ℕ} (hk : 1 ≤ k) (T : ℕ) :
    fillGaps c k T (k - 1) = min T (c (k - 1)) := by
  unfold fillGaps
  rw [capSum_succ c (by omega), Nat.sub_add_cancel hk, capSum_ge c le_rfl]; simp

theorem sum_fillGaps (c : ℕ → ℕ) (k T : ℕ) (hT : T ≤ capSum c k 0) :
    ∑ t ∈ Finset.range k, fillGaps c k T t = T := by
  have key : ∀ m, ∑ t ∈ Finset.range m, fillGaps c k T t =
      min T (capSum c k 0) - min T (capSum c k m) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Finset.sum_range_succ, ih]
      unfold fillGaps
      have h1 := capSum_anti c k m
      have h2 : ∀ t, capSum c k t ≤ capSum c k 0 := by
        intro t; induction t with
        | zero => exact le_rfl
        | succ t iht => exact (capSum_anti c k t).trans iht
      have := h2 m; have := h2 (m + 1)
      omega
  rw [key, capSum_ge c le_rfl]; simp [hT]

end Podc.FairLeaderElection
