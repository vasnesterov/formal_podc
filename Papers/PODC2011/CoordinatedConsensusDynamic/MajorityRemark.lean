import Papers.PODC2011.CoordinatedConsensusDynamic.CountBound
import Papers.PODC2011.CoordinatedConsensusDynamic.UpperBounds

/-!
# The remark after Theorem 4.1: a bound `N < 2(n-1)` allows early decisions

"If nodes have access to an upper bound `N < 2(n − 1)`, then the claim no longer holds, and nodes
can halt without being causally influenced by everyone on both the all-zeroes and all-ones input
assignments": the majority protocol decides `v` as soon as it has heard `⌊N/2⌋ + 1` copies of `v`
(and otherwise decides the majority at time `N - 1`). We prove that this rule solves consensus in
the system `BoundN` (any valid bound `N ≥ n`), is comparison-based, and, for every
`3 ≤ n ≤ N ≤ 2n - 3`, decides before hearing from everybody in the static line with all inputs
`0`, and also with all inputs `1`.
-/

namespace CoordCons

open DGraph Relation Function Classical
open Cslib.DynNet (Journey)

/-- The majority protocol with an upper bound `N` on the count. -/
noncomputable def majRule : Decision Bool := fun G u t =>
  if G.N / 2 + 1 ≤ heard G u t true then some true
  else if G.N / 2 + 1 ≤ heard G u t false then some false
  else if G.N ≤ t + 1 then some (decide (heard G u t false < heard G u t true)) else none

theorem majRule_local : Local majRule := by
  intro G H u t h
  simp only [majRule, heard_congr h, h.N_eq]

theorem heard_mono {G : DGraph Bool} {u t t' : ℕ} (h : t ≤ t') (b : Bool) :
    heard G u t b ≤ heard G u t' b :=
  Finset.card_le_card (Finset.filter_subset_filter _ (past_mono_left h))

/-- In `BoundN`, every decision of `majRule` is the majority value. -/
theorem majRule_eq {G : DGraph Bool} (hG : BoundN G) {u : ℕ} (hu : u ∈ G.V) {t : ℕ} {v : Bool}
    (h : majRule G u t = some v) : v = majority G := by
  have hsum := cnt_add G
  have hN := hG.2
  have h1 := heard_le_cnt (G := G) u t true
  have h2 := heard_le_cnt (G := G) u t false
  simp only [majRule] at h
  unfold majority
  split_ifs at h with ha hb hc
  · cases h; symm; simp only [decide_eq_true_eq]; omega
  · cases h; symm; simp only [decide_eq_false_iff_not]; omega
  · cases h
    rw [heard_eq_cnt hG.1 hu (by omega), heard_eq_cnt hG.1 hu (by omega)]

theorem majority_valid {G : DGraph Bool} (hG : G.Valid) :
    ∃ w ∈ G.V, G.input w = majority G := by
  have hsum := cnt_add G
  have hpos := Finset.card_pos.2 hG.nonempty
  have : 0 < cnt G (majority G) := by
    unfold majority
    by_cases h : cnt G false < cnt G true
    · simp only [h, decide_true]; omega
    · simp only [h, decide_false]; omega
  obtain ⟨w, hw⟩ := Finset.card_pos.1 this
  exact ⟨w, (Finset.mem_filter.1 hw).1, (Finset.mem_filter.1 hw).2⟩

theorem majRule_isSome {G : DGraph Bool} {u t : ℕ} (ht : G.N ≤ t + 1) :
    (majRule G u t).isSome := by
  simp only [majRule]
  split_ifs <;> rfl

theorem majRule_consensus : Consensus BoundN majRule := by
  refine ⟨majRule_local, fun G hG u hu t v h => ?_, fun G hG u hu w hw t t' a b ha hb => ?_,
    fun G hG u hu t v h => ?_, fun G hG u hu => ⟨G.N, majRule_isSome (by omega)⟩⟩
  · have hv := majRule_eq hG hu h
    -- some branch fires at `t + 1`, and every decision is the majority
    have hsome : (majRule G u (t + 1)).isSome := by
      simp only [majRule] at h ⊢
      have h1 := heard_mono (G := G) (u := u) (by omega : t ≤ t + 1) true
      have h2 := heard_mono (G := G) (u := u) (by omega : t ≤ t + 1) false
      split_ifs at h ⊢ <;> first | rfl | omega
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 hsome
    rw [hb, majRule_eq hG hu hb, hv]
  · rw [majRule_eq hG hu ha, majRule_eq hG hw hb]
  · rw [majRule_eq hG hu h]; exact majority_valid hG.1

/-! ### Comparison-basedness -/

theorem past_embed {G : DGraph Bool} {f : ℕ → ℕ} (hf : Injective f) (u t : ℕ) :
    (G.embed f).past (f u) t 0 = (G.past u t 0).image f := by
  ext x
  simp only [mem_past, Finset.mem_image]
  constructor
  · rintro ⟨hx, hr⟩
    obtain ⟨w, rfl, hw⟩ := reach_of_embed hf hr u rfl
    refine ⟨w, ⟨?_, hw⟩, rfl⟩
    obtain ⟨w', hw', he⟩ := Finset.mem_image.1 hx
    rwa [← hf he]
  · rintro ⟨w, ⟨hw, hr⟩, rfl⟩
    exact ⟨Finset.mem_image_of_mem f hw, reach_embed hf hr⟩

theorem heard_embed {G : DGraph Bool} {f : ℕ → ℕ} (hf : Injective f) (u t : ℕ) (b : Bool) :
    heard (G.embed f) (f u) t b = heard G u t b := by
  unfold heard
  rw [past_embed hf, Finset.filter_image, Finset.card_image_of_injective _ hf]
  congr 1
  apply Finset.filter_congr
  intro w _
  simp [embed_input hf]

theorem majRule_comparisonBased : ComparisonBased majRule := by
  intro f hf G u t
  simp only [majRule, heard_embed hf.injective, show (G.embed f).N = G.N from rfl]

/-! ### Early decisions in the static line -/

/-- The static line `0 — 1 — ⋯ — (n-1)` with constant input `b` and bound `N`. -/
def line (n : ℕ) (b : Bool) (N : ℕ) : DGraph Bool where
  V := Finset.range n
  input := fun _ => b
  N := N
  adj := fun _ x y => x < n ∧ y < n ∧ (x + 1 = y ∨ y + 1 = x)

theorem line_valid {n : ℕ} (hn : 1 ≤ n) (b : Bool) (N : ℕ) : (line n b N).Valid := by
  refine ⟨⟨0, by simp [line]; omega⟩, fun r x y h => ?_, fun r x y h => ?_,
    fun r x h => by simp [line] at h, fun r _ x hx y hy => ?_⟩
  · simp only [line, Finset.mem_range]; exact ⟨h.1, h.2.1⟩
  · exact ⟨h.2.1, h.1, h.2.2.symm⟩
  · simp only [line, Finset.mem_range] at hx hy
    -- every node is connected to `0`
    have key : ∀ z, z < n → ReflTransGen ((line n b N).adj r) z 0 := by
      intro z
      induction z with
      | zero => intro _; exact .refl
      | succ z ih => intro hz; exact ReflTransGen.head ⟨hz, by omega, Or.inr rfl⟩ (ih (by omega))
    exact (key x hx).trans ((key y hy).symm_of (fun p q h => ⟨h.2.1, h.1, h.2.2.symm⟩))

theorem line_reach_le {n N : ℕ} {b : Bool} {w s u t : ℕ} (h : (line n b N).Reach w s u t) :
    w ≤ u + (t - s) := by
  induction h with
  | refl => omega
  | step hr hs ih =>
    have := hr.le
    rcases hs with rfl | ⟨-, -, h | h⟩ <;> omega

theorem line_reach_zero {n N : ℕ} {b : Bool} {j : ℕ} (hj : j < n) (s : ℕ) :
    (line n b N).Reach j s 0 (s + j) := by
  induction j generalizing s with
  | zero => exact .refl
  | succ j ih =>
    have := ih (by omega) (s + 1)
    rw [show s + 1 + j = s + (j + 1) by ring] at this
    exact Journey.cons (Or.inr ⟨hj, by omega, Or.inr rfl⟩) this

/-- **Remark after Theorem 4.1.** For `3 ≤ n ≤ N ≤ 2n - 3` (i.e. a valid bound `N < 2(n-1)`),
the comparison-based majority protocol, which solves consensus for every valid bound, lets node
`0` of the static line decide at time `n - 2`, before hearing from node `n - 1`, both when all
inputs are `0` and when all inputs are `1`. -/
theorem majority_remark :
    Consensus BoundN majRule ∧ ComparisonBased majRule ∧
      ∀ n N : ℕ, 3 ≤ n → n ≤ N → N + 3 ≤ 2 * n → ∀ i : Bool,
        BoundN (line n i N) ∧ (line n i N).V.card = n ∧ (∀ w ∈ (line n i N).V, (line n i N).input w = i) ∧
        (majRule (line n i N) 0 (n - 2)).isSome ∧ (line n i N).past 0 (n - 2) 0 ≠ (line n i N).V := by
  refine ⟨majRule_consensus, majRule_comparisonBased, fun n N h3 hnN hN i => ?_⟩
  have hcard : (line n i N).V.card = n := by simp [line]
  refine ⟨⟨line_valid (by omega) i N, by rw [hcard]; exact hnN⟩, hcard, fun _ _ => rfl, ?_, ?_⟩
  · -- heard `n - 1 ≥ N/2 + 1` copies of `i`
    have hsub : Finset.range (n - 1) ⊆ ((line n i N).past 0 (n - 2) 0).filter
        (fun w => (line n i N).input w = i) := by
      intro j hj
      simp only [Finset.mem_range] at hj
      refine Finset.mem_filter.2 ⟨mem_past.2 ⟨by simp [line]; omega, ?_⟩, rfl⟩
      have := line_reach_zero (n := n) (N := N) (b := i) (j := j) (by omega) 0
      exact this.trans (Journey.self (by omega))
    have hh : n - 1 ≤ heard (line n i N) 0 (n - 2) i := by
      have := Finset.card_le_card hsub; simpa [heard] using this
    simp only [majRule, show (line n i N).N = N from rfl]
    cases i <;> split_ifs <;> first | rfl | omega
  · intro h
    have hm : n - 1 ∈ (line n i N).past 0 (n - 2) 0 := by rw [h]; simp [line]; omega
    have := line_reach_le (mem_past.1 hm).2
    omega

end CoordCons
