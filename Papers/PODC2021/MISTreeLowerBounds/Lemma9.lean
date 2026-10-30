import Papers.PODC2021.MISTreeLowerBounds.Family

/-!
# Lemma 9: `Π⁺_Δ(a, x)` is at least as hard as `Π_Δ(⌊(a-2x-1)/2⌋, x+1)` (§3.3)

Given a `Δ`-edge colouring (ports = colours, so the edge of colour `c` joins position `c` at both
endpoints), a solution of `Π⁺_Δ(a, x)` is turned into a solution of `Π_Δ(b, x+1)`,
`b = ⌊(a-2x-1)/2⌋`, in 0 rounds. Let `h = ⌊(a-1)/2⌋`; the colours `1, …, h` of the paper are the
positions `i` with `i.val < h`.

* `M^{Δ-x-1} X^{x+1}` and `P O^{Δ-1}` are kept (they are configurations of `Π_Δ(b, x+1)`).
* `A^{a-x-1} X^{Δ-a+x+1}`: `A` is written on exactly `b` positions of colour `≥ h` that carried
  `A`, and `X` everywhere else (there are at least `a - x - 1 - h ≥ b` such positions).
* `C^{Δ-x} X^x`: `A` is written on exactly `b` positions of colour `< h` that carried `C`, and `X`
  everywhere else (there are at least `h - x ≥ b` such positions).

A new `A` at colour `c` thus comes from an `A` with `c ≥ h` or from a `C` with `c < h` (`Good`),
which is all the edge argument needs (`good_edge`).
-/

namespace Podc.MISTreeLowerBounds

open Finset

variable {Δ : ℕ}

namespace Lemma9

/-- A subset of `T` with `min n |T|` elements. -/
noncomputable def pick (T : Finset (Fin Δ)) (n : ℕ) : Finset (Fin Δ) :=
  Classical.choose (Finset.exists_subset_card_eq (min_le_right n T.card))

theorem pick_subset (T : Finset (Fin Δ)) (n : ℕ) : pick T n ⊆ T :=
  (Classical.choose_spec (Finset.exists_subset_card_eq (min_le_right n T.card))).1

theorem card_pick (T : Finset (Fin Δ)) (n : ℕ) : (pick T n).card = min n T.card :=
  (Classical.choose_spec (Finset.exists_subset_card_eq (min_le_right n T.card))).2

/-- The relabelling used for the configurations without `A` or `C`. -/
def g : L6 → L5
  | .M => .M
  | .P => .P
  | .O => .O
  | _ => .X

/-- The 0-round map of Lemma 9 (`b = ⌊(a-2x-1)/2⌋`, `h = ⌊(a-1)/2⌋`). -/
noncomputable def f (a x : ℕ) (σ : Fin Δ → L6) : Fin Δ → L5 :=
  if 0 < cnt σ .C then
    fun i => if i ∈ pick (univ.filter fun j => j.val < (a - 1) / 2 ∧ σ j = .C)
      ((a - 2 * x - 1) / 2) then .A else .X
  else if cnt σ .A = a - x - 1 ∧ cnt σ .X = Δ - a + x + 1 then
    fun i => if i ∈ pick (univ.filter fun j => (a - 1) / 2 ≤ j.val ∧ σ j = .A)
      ((a - 2 * x - 1) / 2) then .A else .X
  else fun i => g (σ i)

/-- The output label `m` at position `i` is justified by the input label `ℓ`. -/
def Good (h : ℕ) (ℓ : L6) (i : Fin Δ) (m : L5) : Prop :=
  m = .X ∨ (m = .A ∧ ((ℓ = .C ∧ i.val < h) ∨ (ℓ = .A ∧ h ≤ i.val))) ∨ (m = .M ∧ ℓ = .M) ∨
    (m = .P ∧ ℓ = .P) ∨ (m = .O ∧ ℓ = .O)

theorem good_edge {h : ℕ} {ℓ ℓ' : L6} {i : Fin Δ} {m m' : L5} (hm : Good h ℓ i m)
    (hm' : Good h ℓ' i m') (he : E6 ℓ ℓ') : E5 m m' := by
  rcases hm with rfl | ⟨rfl, ⟨rfl, h1⟩ | ⟨rfl, h1⟩⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
  rcases hm' with rfl | ⟨rfl, ⟨rfl, h2⟩ | ⟨rfl, h2⟩⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
  first | decide | omega | simp [E6] at he

theorem good_f (a x : ℕ) (σ : Fin Δ → L6) (i : Fin Δ) :
    Good ((a - 1) / 2) (σ i) i (f a x σ i) := by
  unfold f
  split_ifs with h1 h2 <;> dsimp only
  · split_ifs with h3
    · have := pick_subset _ _ h3
      simp only [mem_filter, mem_univ, true_and] at this
      exact Or.inr (Or.inl ⟨rfl, Or.inl ⟨this.2, this.1⟩⟩)
    · exact Or.inl rfl
  · split_ifs with h3
    · have := pick_subset _ _ h3
      simp only [mem_filter, mem_univ, true_and] at this
      exact Or.inr (Or.inl ⟨rfl, Or.inr ⟨this.2, this.1⟩⟩)
    · exact Or.inl rfl
  · unfold Good g; cases σ i <;> simp

/-- A configuration using only `ℓ₁, ℓ₂` contains no other label. -/
theorem cnt_eq_zero_of {σ : Fin Δ → L6} {ℓ₁ ℓ₂ ℓ : L6} (hne : ℓ₁ ≠ ℓ₂)
    (h : cnt σ ℓ₁ + cnt σ ℓ₂ = Δ) (h1 : ℓ ≠ ℓ₁) (h2 : ℓ ≠ ℓ₂) : cnt σ ℓ = 0 := by
  unfold cnt
  rw [card_eq_zero, filter_eq_empty_iff]
  intro i _ hi
  rcases eq_or_eq_of_cnt_add_cnt hne h i with h' | h' <;> simp_all

/-- On a configuration using only `ℓ₁, ℓ₂` with `g` injective on them, `g` preserves counts. -/
theorem cnt_g {σ : Fin Δ → L6} {ℓ₁ ℓ₂ : L6} (hne : ℓ₁ ≠ ℓ₂) (h : cnt σ ℓ₁ + cnt σ ℓ₂ = Δ)
    (hg : g ℓ₁ ≠ g ℓ₂) (ℓ : L6) (hℓ : ℓ = ℓ₁ ∨ ℓ = ℓ₂) :
    cnt (fun i => g (σ i)) (g ℓ) = cnt σ ℓ := by
  unfold cnt
  congr 1
  ext i
  simp only [mem_filter, mem_univ, true_and]
  rcases eq_or_eq_of_cnt_add_cnt hne h i with h' | h' <;> rcases hℓ with rfl | rfl <;>
    simp_all [Ne.symm hg, Ne.symm hne]

theorem f_mem {a x : ℕ} (hxa : 2 * x + 1 ≤ a) (ha : a ≤ Δ) {σ : Fin Δ → L6}
    (hσ : σ ∈ (PiPlus Δ a x).node) : f a x σ ∈ (Pi Δ ((a - 2 * x - 1) / 2) (x + 1)).node := by
  have hb : (a - 2 * x - 1) / 2 ≤ Δ := by omega
  have hAX : ∀ S : Finset (Fin Δ), S.card = (a - 2 * x - 1) / 2 →
      (fun i => if i ∈ S then L5.A else L5.X) ∈ (Pi Δ ((a - 2 * x - 1) / 2) (x + 1)).node := by
    intro S hS
    have := cnt_ite (Δ := Δ) S (ℓ₁ := L5.A) (ℓ₂ := L5.X) (by decide)
    exact Or.inr (Or.inl ⟨this.1.trans hS, this.2.trans (by rw [hS])⟩)
  unfold f
  split_ifs with h1 h2
  · -- `C`-configuration
    apply hAX
    rw [card_pick, min_eq_left]
    have hC : cnt σ .C = Δ - x ∧ cnt σ .X = x := by
      rcases hσ with hσ | hσ | hσ | hσ
      · have := cnt_eq_zero_of (ℓ := .C) (by decide) (show cnt σ .M + cnt σ .X = Δ by omega)
          (by decide) (by decide); omega
      · have := cnt_eq_zero_of (ℓ := .C) (by decide) (show cnt σ .P + cnt σ .O = Δ by omega)
          (by decide) (by decide); omega
      · have := cnt_eq_zero_of (ℓ := .C) (by decide) (show cnt σ .A + cnt σ .X = Δ by omega)
          (by decide) (by decide); omega
      · exact hσ
    have hsub : (univ.filter fun j : Fin Δ => j.val < (a - 1) / 2) ⊆
        (univ.filter fun j => j.val < (a - 1) / 2 ∧ σ j = .C) ∪ univ.filter fun j => σ j = .X := by
      intro j hj
      simp only [mem_filter, mem_univ, true_and, mem_union] at hj ⊢
      rcases eq_or_eq_of_cnt_add_cnt (show L6.C ≠ L6.X by decide)
        (show cnt σ .C + cnt σ .X = Δ by omega) j with h' | h'
      · exact Or.inl ⟨hj, h'⟩
      · exact Or.inr h'
    have := (card_le_card hsub).trans (card_union_le _ _)
    rw [Fin.card_filter_val_lt] at this
    change _ ≤ _ + cnt σ .X at this
    omega
  · -- `A`-configuration
    apply hAX
    rw [card_pick, min_eq_left]
    have hsub : (univ.filter fun j => σ j = .A) ⊆
        (univ.filter fun j : Fin Δ => (a - 1) / 2 ≤ j.val ∧ σ j = .A) ∪
          univ.filter fun j : Fin Δ => j.val < (a - 1) / 2 := by
      intro j hj
      simp only [mem_filter, mem_univ, true_and, mem_union] at hj ⊢
      by_cases hj' : (a - 1) / 2 ≤ j.val
      · exact Or.inl ⟨hj', hj⟩
      · exact Or.inr (by omega)
    have := (card_le_card hsub).trans (card_union_le _ _)
    rw [Fin.card_filter_val_lt] at this
    change cnt σ .A ≤ _ at this
    omega
  · -- `M`- or `P`-configuration
    rcases hσ with hσ | hσ | hσ | hσ
    · have hs : cnt σ .M + cnt σ .X = Δ := by omega
      have e1 := cnt_g (by decide) hs (by decide) .M (Or.inl rfl)
      have e2 := cnt_g (by decide) hs (by decide) .X (Or.inr rfl)
      change cnt (fun i => g (σ i)) .M = _ at e1
      change cnt (fun i => g (σ i)) .X = _ at e2
      exact Or.inl ⟨by omega, by omega⟩
    · have hs : cnt σ .P + cnt σ .O = Δ := by omega
      have e1 := cnt_g (by decide) hs (by decide) .P (Or.inl rfl)
      have e2 := cnt_g (by decide) hs (by decide) .O (Or.inr rfl)
      change cnt (fun i => g (σ i)) .P = _ at e1
      change cnt (fun i => g (σ i)) .O = _ at e2
      exact Or.inr (Or.inr ⟨by omega, by omega⟩)
    · exact absurd hσ h2
    · have := cnt_le σ .X
      omega

end Lemma9

open Lemma9 in
/-- Lemma 9 of [paper]: with a Δ-edge colouring as input, Π⁺_Δ(a, x) is at least as hard as
Π_Δ(⌊(a-2x-1)/2⌋, x+1). -/
theorem lemma_9 {Δ a x : ℕ} (hxa : 2 * x + 1 ≤ a) (ha : a ≤ Δ) :
    ZeroRoundReduction (PiPlus Δ a x) (Pi Δ ((a - 2 * x - 1) / 2) (x + 1)) :=
  ⟨f a x, fun _ hσ => f_mem hxa ha hσ,
    fun σ _ τ _ c he => good_edge (good_f a x σ c) (good_f a x τ c) he⟩

end Podc.MISTreeLowerBounds
