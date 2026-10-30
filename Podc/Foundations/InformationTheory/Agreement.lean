import Mathlib

-- CSLib candidate: Cslib/Foundations/InformationTheory/Agreement.lean

/-!
# Codes with small pairwise agreement (Gilbert–Varshamov, `q`-ary)

The *agreement* of two words `x y : P → Σ` is the number of positions where they coincide
(`Fintype.card P - hammingDist x y`). A code with small pairwise agreement is a code with large
distance. We prove the greedy (Gilbert–Varshamov) existence bound in agreement form: if
`N · 2^M · q^(M - (a+1)) ≤ q^M` (`M = |P|`, `q = |A|`, `a + 1 ≤ M`), there are `N` words with
pairwise agreement `≤ a`. In particular, over a constant alphabet with `q^(a+1) ≥ 4^M` there are
`2^M` words of length `M` with pairwise agreement `≤ a`.

* `Cslib.agree x y`, `Cslib.agree_eq_card_sub_hammingDist`.
* `Cslib.exists_finset_agree_le`: the greedy bound.
* `Cslib.exists_code_agree_le`: an injective code `Fin (2^M) → (P → A)` with pairwise agreement
  `≤ a` when `4^M ≤ q^(a+1)`.
-/

namespace Cslib

open Finset

variable {P A : Type*} [Fintype P] [DecidableEq A]

/-- Number of positions where two words agree. -/
def agree (x y : P → A) : ℕ := (univ.filter fun h => x h = y h).card

theorem agree_comm (x y : P → A) : agree x y = agree y x := by
  simp only [agree, eq_comm]

theorem agree_eq_card_sub_hammingDist (x y : P → A) :
    agree x y = Fintype.card P - hammingDist x y := by
  have h := Finset.card_filter_add_card_filter_not (s := (univ : Finset P)) (fun h => x h = y h)
  rw [card_univ] at h
  unfold agree hammingDist
  simp only [ne_eq] at h ⊢
  omega

variable [DecidableEq P] [Fintype A]

/-- The words that coincide with `s` on `T` are `|A|^(|P| - |T|)` many. -/
theorem card_filter_forall_eq (s : P → A) (T : Finset P) :
    (univ.filter fun y : P → A => ∀ h ∈ T, y h = s h).card =
      Fintype.card A ^ (Fintype.card P - T.card) := by
  classical
  have : (univ.filter fun y : P → A => ∀ h ∈ T, y h = s h) =
      Fintype.piFinset (fun h => if h ∈ T then {s h} else univ) := by
    ext y
    simp only [mem_filter, mem_univ, true_and, Fintype.mem_piFinset]
    constructor
    · intro hy h
      split_ifs with hh
      · simp [hy h hh]
      · simp
    · intro hy h hh
      simpa [hh] using hy h
  rw [this, Fintype.card_piFinset]
  simp only [apply_ite Finset.card, card_singleton, card_univ]
  rw [Finset.prod_ite, prod_const_one, one_mul, prod_const]
  congr 1
  rw [Finset.filter_not, Finset.card_sdiff_of_subset (Finset.filter_subset _ _)]
  simp

/-- **Gilbert–Varshamov (greedy), agreement form.** (The alphabet must be nonempty: otherwise,
for `a + 1 < |P|`, the hypothesis `hN` reads `0 ≤ 0` but there are no words at all.) -/
theorem exists_finset_agree_le [Nonempty A] (a N : ℕ) (ha : a + 1 ≤ Fintype.card P)
    (hN : N * (2 ^ Fintype.card P * Fintype.card A ^ (Fintype.card P - (a + 1))) ≤
      Fintype.card A ^ Fintype.card P) :
    ∃ S : Finset (P → A), N ≤ S.card ∧ ∀ x ∈ S, ∀ y ∈ S, x ≠ y → agree x y ≤ a := by
  set X := 2 ^ Fintype.card P * Fintype.card A ^ (Fintype.card P - (a + 1)) with hX
  have hX0 : 0 < X := Nat.mul_pos (Nat.two_pow_pos _) (Nat.pow_pos Fintype.card_pos)
  suffices key : ∀ n, n ≤ N →
      ∃ S : Finset (P → A), S.card = n ∧ ∀ x ∈ S, ∀ y ∈ S, x ≠ y → agree x y ≤ a by
    obtain ⟨S, hS, h⟩ := key N le_rfl
    exact ⟨S, hS.ge, h⟩
  intro n
  induction n with
  | zero => exact fun _ => ⟨∅, by simp⟩
  | succ n ih =>
    intro hn
    obtain ⟨S, hSc, hS⟩ := ih (by omega)
    -- the bad words
    set B : Finset (P → A) := univ.filter fun y => ∃ s ∈ S, a + 1 ≤ agree s y
    have hBsub : B ⊆ S.biUnion fun s => (powersetCard (a + 1) (univ : Finset P)).biUnion
        fun T => univ.filter fun y : P → A => ∀ h ∈ T, y h = s h := by
      intro y hy
      obtain ⟨s, hs, hsy⟩ := (mem_filter.mp hy).2
      obtain ⟨T, hT, hTc⟩ := Finset.exists_subset_card_eq hsy
      simp only [mem_biUnion, mem_powersetCard, mem_filter, mem_univ, true_and]
      refine ⟨s, hs, T, ⟨subset_univ _, hTc⟩, fun h hh => ?_⟩
      exact ((mem_filter.mp (hT hh)).2).symm
    have hBcard : B.card < (univ : Finset (P → A)).card := by
      calc B.card ≤ _ := card_le_card hBsub
        _ ≤ ∑ s ∈ S, ∑ T ∈ powersetCard (a + 1) (univ : Finset P),
            (univ.filter fun y : P → A => ∀ h ∈ T, y h = s h).card :=
          card_biUnion_le.trans (sum_le_sum fun _ _ => card_biUnion_le)
        _ = ∑ s ∈ S, ∑ T ∈ powersetCard (a + 1) (univ : Finset P),
            Fintype.card A ^ (Fintype.card P - (a + 1)) := by
          refine sum_congr rfl fun s _ => sum_congr rfl fun T hT => ?_
          rw [card_filter_forall_eq, (mem_powersetCard.mp hT).2]
        _ = n * ((Fintype.card P).choose (a + 1) *
            Fintype.card A ^ (Fintype.card P - (a + 1))) := by
          simp [hSc, card_powersetCard]
        _ ≤ n * X := by
          apply Nat.mul_le_mul_left
          exact Nat.mul_le_mul_right _ (Nat.choose_le_two_pow _ _)
        _ < N * X := Nat.mul_lt_mul_of_pos_right (by omega) hX0
        _ ≤ _ := by simpa [card_univ, Fintype.card_fun] using hN
    obtain ⟨y, -, hy⟩ := exists_mem_notMem_of_card_lt_card hBcard
    have hyB : ∀ s ∈ S, agree s y ≤ a := by
      intro s hs
      by_contra h
      exact hy (mem_filter.mpr ⟨mem_univ _, s, hs, by omega⟩)
    have hyS : y ∉ S := by
      intro h
      have := hyB y h
      have : agree y y = Fintype.card P := by simp [agree]
      omega
    refine ⟨insert y S, by rw [card_insert_of_notMem hyS, hSc], ?_⟩
    intro x hx z hz hxz
    rcases mem_insert.mp hx with hx | hx <;> rcases mem_insert.mp hz with hz | hz
    · exact absurd (hx.trans hz.symm) hxz
    · rw [hx, agree_comm]; exact hyB z hz
    · rw [hz]; exact hyB x hx
    · exact hS x hx z hz hxz

/-- A code `Fin (2^M) → (P → A)` (`M = |P|`) with pairwise agreement `≤ a`, provided
`4^M ≤ |A|^(a+1)` and `a + 1 ≤ M`. -/
theorem exists_code_agree_le (a : ℕ) (ha : a + 1 ≤ Fintype.card P)
    (hq : 4 ^ Fintype.card P ≤ Fintype.card A ^ (a + 1)) :
    ∃ c : Fin (2 ^ Fintype.card P) → P → A, ∀ m m', m ≠ m' → agree (c m) (c m') ≤ a := by
  set M := Fintype.card P
  have hq0 : 0 < Fintype.card A := by
    rcases Nat.eq_zero_or_pos (Fintype.card A) with h | h
    · rw [h, zero_pow (by omega)] at hq
      have : 0 < 4 ^ M := by positivity
      omega
    · exact h
  have : Nonempty A := Fintype.card_pos_iff.mp hq0
  obtain ⟨S, hS, hSa⟩ := exists_finset_agree_le (P := P) (A := A) a (2 ^ M) ha (by
    calc 2 ^ M * (2 ^ M * Fintype.card A ^ (M - (a + 1)))
        = 4 ^ M * Fintype.card A ^ (M - (a + 1)) := by
          rw [← mul_assoc, ← mul_pow]; norm_num
      _ ≤ Fintype.card A ^ (a + 1) * Fintype.card A ^ (M - (a + 1)) :=
          Nat.mul_le_mul_right _ hq
      _ = Fintype.card A ^ M := by rw [← pow_add]; congr 1; omega)
  refine ⟨fun m => (S.equivFin.symm (Fin.castLE hS m)).1, fun m m' hmm' => ?_⟩
  refine hSa _ (S.equivFin.symm _).2 _ (S.equivFin.symm _).2 fun h => hmm' ?_
  have := S.equivFin.symm.injective (Subtype.ext h)
  exact Fin.castLE_injective hS this

end Cslib
