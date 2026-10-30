import Papers.PODC2017.LCLGrids.Theorem9

/-!
# Lemma 13: the row sum does not depend on the identifiers

Section 9 of Brandt et al., *LCL problems on grids* (PODC 2017).

Lemma 13 of the paper: `s(G₁) = s(G₂)` for any two `n × n` grids (identifier assignments) when
`T(n) < n/4`. We prove it (`lemma13`) for an algorithm with `T` rounds that properly 3-colours
every torus with identifiers in `[0, B)`, `B ≥ 3n²` (room for fresh identifiers), under
`4(T + 2) ≤ n`: the label `ℓ(v)` reads the colours of the `3 × 3` block around `v`, so it depends
on the identifiers within distance `T + 2`; the paper hides this additive constant in its
convention that checking an LCL of radius `1` costs `O(1)` extra rounds.

The proof is the paper's: replace the identifiers of the lower half of the torus by the same
fresh identifiers in both instances; a row in the upper half sees no change, a row in the lower
half sees the same identifiers in both modified instances, and Lemma 12 moves between rows.
-/

namespace Podc.LCLGrids

open Finset

variable {n : ℕ} [NeZero n] {T : ℕ} {A : (ℤ × ℤ → ℕ) → Col}

/-- The row sum of row `r` only depends on the identifiers of the rows `r - T - 1, …, r + T + 1`. -/
lemma rowSum_congr (hA : GridLocal T A) {I I' : Pos n → ℕ} (r : ZMod n)
    (h : ∀ (x : ZMod n) (e : ℤ), |e| ≤ T + 1 → I (x, r + e) = I' (x, r + e)) :
    rowSum (colouring A I) r = rowSum (colouring A I') r := by
  unfold rowSum
  refine sum_congr rfl fun x _ => ?_
  rw [ell_eq_block, ell_eq_block]
  have e : ∀ a b : ℤ, |b| ≤ 1 → colouring A I (sh (x, r) a b) = colouring A I' (sh (x, r) a b) := by
    intro a b hb
    refine hA _ _ fun d hd => ?_
    simp only [gview, sh_sh]
    have hpos : sh (x, r) (a + d.1) (b + d.2) =
        (x + ((a + d.1 : ℤ) : ZMod n), r + ((b + d.2 : ℤ) : ZMod n)) := rfl
    rw [hpos]
    refine h _ _ ?_
    have := abs_add_le b d.2
    have := abs_nonneg d.1
    linarith
  simp only [block]
  have e0 := e 0 0 (by norm_num)
  simp only [sh_zero] at e0
  rw [e (-1) 1 (by norm_num), e 0 1 (by norm_num), e 1 1 (by norm_num),
    e (-1) 0 (by norm_num), e0, e 1 0 (by norm_num), e (-1) (-1) (by norm_num),
    e 0 (-1) (by norm_num), e 1 (-1) (by norm_num)]

/-- Lemma 13 of the paper: for a `T`-round algorithm that properly 3-colours all `n × n` tori with
identifiers in `[0, B)`, `B ≥ 3n²`, and `4(T + 2) ≤ n`, the row sum `s` is the same for any two
identifier assignments (and any two rows). -/
theorem lemma13 {B : ℕ} (hA : GridLocal T A) (hcol : Colours3 n B A) (hB : 3 * n ^ 2 ≤ B)
    (hT : 4 * (T + 2) ≤ n) {I₁ I₂ : Pos n → ℕ} (h₁ : Function.Injective I₁)
    (h₂ : Function.Injective I₂)
    (hb₁ : ∀ v, I₁ v < B) (hb₂ : ∀ v, I₂ v < B) (r₁ r₂ : ZMod n) :
    rowSum (colouring A I₁) r₁ = rowSum (colouring A I₂) r₂ := by
  classical
  -- fresh identifiers
  set S : Finset ℕ := univ.image I₁ ∪ univ.image I₂
  set F : Finset ℕ := range B \ S
  have hS : S.card ≤ 2 * n ^ 2 := by
    refine (card_union_le _ _).trans ?_
    have := card_image_le (s := (univ : Finset (Pos n))) (f := I₁)
    have := card_image_le (s := (univ : Finset (Pos n))) (f := I₂)
    simp only [card_univ, Fintype.card_prod, ZMod.card] at *
    nlinarith
  have hF : Fintype.card (Pos n) ≤ Fintype.card F := by
    rw [Fintype.card_coe, Fintype.card_prod, ZMod.card]
    have := le_card_sdiff S (range B)
    rw [card_range] at this
    simp only [F]
    rw [show n * n = n ^ 2 from (sq n).symm] at *
    generalize n ^ 2 = N at *
    omega
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hF
  have heF : ∀ v, (e v : ℕ) ∈ F := fun v => (e v).2
  have heB : ∀ v, (e v : ℕ) < B := fun v => mem_range.1 (mem_sdiff.1 (heF v)).1
  have heS : ∀ v w, (e v : ℕ) ≠ I₁ w ∧ (e v : ℕ) ≠ I₂ w := by
    intro v w
    have := heF v
    simp only [F, S, mem_sdiff, mem_union, mem_image, mem_univ, true_and, not_or] at this
    exact ⟨fun h => this.2.1 ⟨w, h.symm⟩, fun h => this.2.2 ⟨w, h.symm⟩⟩
  -- the lower half `y < m` gets the fresh identifiers
  set m := n / 2
  let H : (Pos n → ℕ) → Pos n → ℕ := fun I v => if v.2.val < m then (e v : ℕ) else I v
  have hH : ∀ I, Function.Injective I → (∀ v, I v < B) → (∀ v w, (e v : ℕ) ≠ I w) →
      Function.Injective (H I) ∧ ∀ v, H I v < B := by
    intro I hI hIB hIe
    refine ⟨fun v w hvw => ?_, fun v => ?_⟩
    · simp only [H] at hvw
      split_ifs at hvw with h1 h2 h2
      · exact e.injective (Subtype.ext hvw)
      · exact absurd hvw (hIe v w)
      · exact absurd hvw.symm (hIe w v)
      · exact hI hvw
    · simp only [H]; split_ifs
      exacts [heB v, hIB v]
  obtain ⟨hH₁, hHb₁⟩ := hH I₁ h₁ hb₁ fun v w => (heS v w).1
  obtain ⟨hH₂, hHb₂⟩ := hH I₂ h₂ hb₂ fun v w => (heS v w).2
  have hp₁ := hcol _ h₁ hb₁
  have hp₂ := hcol _ h₂ hb₂
  have hq₁ := hcol _ hH₁ hHb₁
  have hq₂ := hcol _ hH₂ hHb₂
  -- a row in the upper half and a row in the lower half
  set rout : ℕ := m + (n - m) / 2
  set rin : ℕ := m / 2
  have hout : ∀ (e : ℤ), |e| ≤ T + 1 → ¬ ((rout : ZMod n) + (e : ZMod n)).val < m := by
    intro e he
    rw [abs_le] at he
    have := val_intCast_of_nonneg (n := n) (z := (rout : ℤ) + e) (by omega) (by omega)
    push_cast at this
    omega
  have hin : ∀ (e : ℤ), |e| ≤ T + 1 → ((rin : ZMod n) + (e : ZMod n)).val < m := by
    intro e he
    rw [abs_le] at he
    have := val_intCast_of_nonneg (n := n) (z := (rin : ℤ) + e) (by omega) (by omega)
    push_cast at this
    omega
  have s1 : rowSum (colouring A I₁) rout = rowSum (colouring A (H I₁)) rout :=
    rowSum_congr hA _ fun x e he => by
      simp only [H]; rw [ite_eq_right_of_eq_false _ _ (eq_false (hout e he))]
  have s2 : rowSum (colouring A I₂) rout = rowSum (colouring A (H I₂)) rout :=
    rowSum_congr hA _ fun x e he => by
      simp only [H]; rw [ite_eq_right_of_eq_false _ _ (eq_false (hout e he))]
  have s3 : rowSum (colouring A (H I₁)) rin = rowSum (colouring A (H I₂)) rin :=
    rowSum_congr hA _ fun x e he => by
      simp only [H]
      rw [ite_eq_left_of_eq_true _ _ (eq_true (hin e he)),
        ite_eq_left_of_eq_true _ _ (eq_true (hin e he))]
  rw [rowSum_eq hp₁ r₁ rout, s1, rowSum_eq hq₁ rout rin, s3, rowSum_eq hq₂ rin rout, ← s2,
    rowSum_eq hp₂ rout r₂]

end Podc.LCLGrids
