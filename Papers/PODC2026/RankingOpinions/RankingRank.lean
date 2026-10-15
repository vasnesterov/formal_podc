import Papers.PODC2026.RankingOpinions.RankingReach
import Papers.PODC2026.RankingOpinions.RankingLayers

/-!
# Rankings of colors, and the stable braket multiset on rankings

* `rnk x c = |{ℓ : x ℓ > x c}|` (the ranking `r(c)` of Definition 6.4), a bijection when `x` is
  injective (no ties).
* Once Circles is stabilized on a consistent configuration, the multiset of brakets on rankings is
  `⋃_p f(G_p)` for the counts `y (σ c) = x c` (Lemma 3.7 transported along the ranking `σ`).
-/

set_option linter.unusedSectionVars false

namespace RankingOpinions.Ranking

open Cslib.PopulationProtocol Cslib.PopulationProtocol.Protocol Finset

variable {k : ℕ}

/-! ### The correct ranking -/

/-- The ranking `r(c) = |{ℓ : x_ℓ > x_c}|` of Definition 6.4. -/
def rnk (x : Fin k → ℕ) (c : Fin k) : Fin k :=
  ⟨(univ.filter fun l => x c < x l).card, by
    calc (univ.filter fun l => x c < x l).card < (univ : Finset (Fin k)).card := by
          apply card_lt_card
          refine ⟨subset_univ _, fun h => ?_⟩
          have := h (mem_univ c); simp at this
      _ = k := by simp⟩

lemma rnk_val (x : Fin k → ℕ) (c : Fin k) :
    (rnk x c : ℕ) = (univ.filter fun l => x c < x l).card := rfl

lemma rnk_lt_of_lt {x : Fin k → ℕ} {c d : Fin k} (h : x c < x d) : rnk x d < rnk x c := by
  rw [Fin.lt_def, rnk_val, rnk_val]
  apply card_lt_card
  refine ⟨fun l hl => ?_, fun hs => ?_⟩
  · simp only [mem_filter, mem_univ, true_and] at hl ⊢; omega
  · have := hs (show d ∈ univ.filter fun l => x c < x l by simpa using h)
    simp at this

lemma rnk_injective {x : Fin k → ℕ} (hx : Function.Injective x) : Function.Injective (rnk x) := by
  intro c d h
  by_contra hne
  rcases Nat.lt_or_gt_of_ne (fun e => hne (hx e)) with h' | h'
  · exact (rnk_lt_of_lt h').ne h.symm
  · exact (rnk_lt_of_lt h').ne h

lemma lt_of_rnk_lt {x : Fin k → ℕ} (hx : Function.Injective x) {c d : Fin k}
    (h : rnk x c < rnk x d) : x d < x c := by
  rcases Nat.lt_trichotomy (x c) (x d) with h' | h' | h'
  · exact absurd (rnk_lt_of_lt h') (not_lt.2 h.le)
  · rw [hx h'] at h; exact absurd h (lt_irrefl _)
  · exact h'

lemma rnk_surjective {x : Fin k → ℕ} (hx : Function.Injective x) :
    Function.Surjective (rnk x) :=
  Finite.surjective_of_injective (rnk_injective hx)

lemma rnk_eq_zero {x : Fin k → ℕ} (hx : Function.Injective x) {u : Fin k}
    (h : (rnk x u : ℕ) = 0) (c : Fin k) (hc : c ≠ u) : x c < x u := by
  rw [rnk_val, card_eq_zero, filter_eq_empty_iff] at h
  have := h (mem_univ c)
  rcases Nat.lt_or_gt_of_ne (fun e => hc (hx e)) with h' | h'
  · exact h'
  · exact absurd h' this

/-! ### Counts on rankings -/

variable [NeZero k] {A : Type*} [DecidableEq A] [Fintype A]

/-- The number of agents whose input color has ranking `m` under `σ`. -/
def ycount (input : A → Fin k) (σ : Fin k → Fin k) (m : Fin k) : ℕ :=
  ((univ.val.map input).map σ).count m

lemma count_map_input (input : A → Fin k) (c : Fin k) :
    (univ.val.map input).count c = inputCount input c := by
  rw [Multiset.count_map, inputCount, Finset.card_def, Finset.filter_val]
  congr 1
  apply Multiset.filter_congr
  intro a _; exact eq_comm

lemma ycount_apply (input : A → Fin k) {σ : Fin k → Fin k} (hσ : Function.Injective σ)
    (c : Fin k) : ycount input σ (σ c) = inputCount input c := by
  rw [ycount, Multiset.count_map_eq_count' _ _ hσ, count_map_input]

lemma counts_brk {input : A → Fin k} {σ : Fin k → Fin k} {C : Config A (RState k)}
    (hC : Inv input C) (hc : Cons σ C) : Counts (brakets (brk C)) (ycount input σ) := by
  intro m
  constructor
  · simp only [brakets, brk, Multiset.map_map, Function.comp_def, ycount]
    congr 2; funext a; rw [(hc a).1, hC.bc]
  · have : (brakets (brk C)).map Prod.snd = ((univ.val.map input).map σ) := by
      rw [← hC.kc]
      simp only [brakets, brk, kcs, Multiset.map_map, Function.comp_def]
      congr 1; funext a; exact (hc a).2
    rw [this]; rfl

/-- **Lemma 3.7 on rankings**: in a stable consistent configuration the brakets on rankings are
`⋃_p f(G_p)` for the counts `ycount`. -/
lemma brk_eq_layers {input : A → Fin k} {σ : Fin k → Fin k} {C : Config A (RState k)}
    (hC : Inv input C) (hc : Cons σ C) (hs : Stable (brk C)) :
    brakets (brk C) = layers (ycount input σ) :=
  eq_layers_of_stable _ _ (counts_brk hC hc) hs.mstable

lemma brk_mem_layers {input : A → Fin k} {σ : Fin k → Fin k} {C : Config A (RState k)}
    (hC : Inv input C) (hc : Cons σ C) (hs : Stable (brk C)) (a : A) :
    ((C a).br, (C a).kr) ∈ layers (ycount input σ) := by
  rw [← brk_eq_layers hC hc hs]
  exact Multiset.mem_map_of_mem _ (mem_univ_val a)

lemma exists_of_mem_layers {input : A → Fin k} {σ : Fin k → Fin k} {C : Config A (RState k)}
    (hC : Inv input C) (hc : Cons σ C) (hs : Stable (brk C)) {e : Braket k}
    (he : e ∈ layers (ycount input σ)) : ∃ a, (C a).br = e.1 ∧ (C a).kr = e.2 := by
  rw [← brk_eq_layers hC hc hs] at he
  obtain ⟨a, -, ha⟩ := Multiset.mem_map.1 he
  exact ⟨a, by rw [← ha]; rfl, by rw [← ha]; rfl⟩

end RankingOpinions.Ranking
