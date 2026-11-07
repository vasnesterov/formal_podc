import Papers.PODC2013.SourceDetectionCongest.Main

/-!
# Corollary 4.4 (second part) fails as stated; Lemma 4.6 under a per-round Line 16

Both concern Line 16 ("delete all entries with `h_s > h`"), which the journal pseudocode places
after the loop.

* `corollary_4_4_literal_false`: with Line 16 after the loop (Algorithm 1 as printed), the
  second part of Corollary 4.4, "if `top_k(L_v^{(h)}) ⊆ L_v^r` then
  `top_k(L_v^r) = top_k(L_v^{(h)})`", fails: `L_v^r` may contain an entry at distance `> h` while
  `L_v^{(h)}` has fewer than `k` entries. Only "`top_k(L_v^{(h)})` is a prefix of `L_v^r`"
  (`mem_topk_of_mem_entries`) and the filtered version (`output_eq_of_subset`) hold, and that is
  all the proofs use.
* `lemma_4_6_truncated_false`: if Line 16 is instead executed in every round, Lemma 4.6(i)
  fails for `d > h` (which its range `d + k ≤ r + 1 ≤ h + σ` allows). Theorem 1.2 only needs
  `d ≤ h` and holds for both readings (`theorem_1_2`, `theorem_1_2_truncated`). As printed
  (Line 16 after the loop) Lemma 4.6 holds for all `d`, so this is not a mistake of the paper.

Instance: the path `0 — 1 — 2`, `S = {0}`, `h = 1`, `σ = 2`, `k = 1`, `v = 2`, `r = 2`.
-/

namespace Podc.SourceDetectionCongest.Counterexample

open Finset

/-- The path `0 — 1 — 2`. -/
def pathE (a b : Fin 3) : Prop := (a : ℕ) + 1 = b ∨ (b : ℕ) + 1 = a

instance : DecidableRel pathE := fun a b => by unfold pathE; infer_instance

lemma hd_0_2 : hd pathE 0 2 = 2 := by
  apply le_antisymm
  · exact hd_le_of_reach (n := 2) ⟨1, ⟨0, rfl, by decide⟩, by decide⟩
  · by_contra hlt
    rw [not_le] at hlt
    have : hd pathE 0 2 = 0 ∨ hd pathE 0 2 = 1 := by
      generalize hd pathE 0 2 = x at hlt ⊢
      induction x using ENat.recTopCoe with
      | top => simp at hlt
      | coe x =>
        have : x < 2 := by exact_mod_cast hlt
        interval_cases x <;> simp
    rcases this with h | h
    · exact absurd (hd_eq_zero.1 h) (by decide)
    · obtain ⟨u, hu, hu0⟩ := exists_pred_of_hd_eq_succ (n := 0) (by simpa using h)
      obtain rfl := hd_eq_zero.1 (by simpa using hu0)
      exact absurd hu (by decide)

lemma topk_one_Lspec_two : toLex (2, (0 : Fin 3)) ∈ topk 1 (Lspec pathE {0} 2 2) := by
  refine mem_topk.2 ⟨mem_Lspec.2 ⟨by simp, hd_0_2, le_rfl⟩, ?_⟩
  rw [Nat.lt_one_iff, card_eq_zero, filter_eq_empty_iff]
  intro y hy hlt
  obtain ⟨⟨m, s⟩, rfl⟩ := toLex.surjective y
  obtain ⟨hs, hm, -⟩ := mem_Lspec.1 hy
  simp only [mem_singleton] at hs
  subst hs
  rw [hd_0_2] at hm
  have : m = 2 := by exact_mod_cast hm.symm
  subst this
  exact lt_irrefl _ hlt

lemma Lspec_one_two : Lspec pathE {0} 1 2 = ∅ := by
  ext x
  obtain ⟨⟨m, s⟩, rfl⟩ := toLex.surjective x
  simp only [notMem_empty, iff_false]
  rw [mem_Lspec]
  rintro ⟨hs, hm, hm1⟩
  simp only [mem_singleton] at hs
  subst hs
  rw [hd_0_2] at hm
  have : m = 2 := by exact_mod_cast hm.symm
  omega

/-- The second part of Corollary 4.4, literally: `top_k(L_v^{(h)}) ⊆ L_v^r` implies
`top_k(L_v^r) = top_k(L_v^{(h)})`. -/
def Corollary44Literal {V : Type*} [Fintype V] [LinearOrder V] (E : V → V → Prop)
    [DecidableRel E] (S : Finset V) (h : ℕ) : Prop :=
  ∀ (v : V) (r k : ℕ), 1 ≤ k → topk k (Lspec E S h v) ⊆ (alg1 E S r v).entries →
    topk k (alg1 E S r v).entries = topk k (Lspec E S h v)

/-- Corollary 4.4 (second part) is false as stated, for Algorithm 1 as printed (Line 16 after
the loop): on the path `0 — 1 — 2` with `S = {0}`, `h = 1`, node `2` has `L_2^{(1)} = ∅` but
`L_2^2 = {(2, 0)}`. -/
theorem corollary_4_4_literal_false : ¬ Corollary44Literal pathE {0} 1 := by
  intro H
  have h1 := H 2 2 1 le_rfl (by rw [Lspec_one_two]; intro x hx; simp [topk] at hx)
  rw [Lspec_one_two] at h1
  have hmem : toLex (2, (0 : Fin 3)) ∈ (alg1 pathE {0} 2 2).entries :=
    (lemma_4_6 (le_refl 1) 2 2 2 1 le_top (by decide)).1 topk_one_Lspec_two
  have : toLex (2, (0 : Fin 3)) ∈ topk 1 (alg1 pathE {0} 2 2).entries := by
    refine mem_topk.2 ⟨hmem, ?_⟩
    rw [Nat.lt_one_iff, card_eq_zero, filter_eq_empty_iff]
    intro y hy hlt
    obtain ⟨⟨m, s⟩, rfl⟩ := toLex.surjective y
    have hm := State.mem_entries.1 hy
    obtain ⟨hs, hle⟩ := lemma_4_3 2 2 s (by rw [hm]; simp)
    simp only [mem_singleton] at hs
    subst hs
    rw [hm, hd_0_2] at hle
    have : 2 ≤ m := by exact_mod_cast hle
    rw [Prod.Lex.toLex_lt_toLex] at hlt
    simp only [lt_self_iff_false, and_false, or_false] at hlt
    omega
  rw [h1] at this
  simp [topk] at this

/-- Lemma 4.6(i) fails for `d > h` if Line 16 is executed in every round (`cap = h = 1`):
`h = 1`, `σ = 2`, `r = 2 ≤ h + σ - 1`, `d = 2`, `k = 1`, `d + k ≤ r + 1`, but
`top_1(L_2^{(2)}) = {(2, 0)} ⊄ L_2^2`. -/
theorem lemma_4_6_truncated_false :
    ¬ topk 1 (Lspec pathE {0} 2 2) ⊆ (run pathE {0} 1 (1 : ℕ) 2 2).entries := by
  intro H
  have hm := State.mem_entries.1 (H topk_one_Lspec_two)
  rcases est_le_cap (E := pathE) (S := {0}) (β := 1) (cap := ((1 : ℕ) : ℕ∞)) 2 2 0 with h | h
  · rw [hm] at h; exact ENat.natCast_ne_top 2 h
  · rw [hm] at h
    have : (2 : ℕ) ≤ 1 := by exact_mod_cast h
    omega

end Podc.SourceDetectionCongest.Counterexample
