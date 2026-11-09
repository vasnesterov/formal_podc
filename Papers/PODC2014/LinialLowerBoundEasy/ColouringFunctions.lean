import Mathlib
import Cslib.Foundations.Data.Nat.LogStar
import Podc.Foundations.Combinatorics.ShiftGraph

/-!
# Colouring functions (§3–§4 of Laurinharju–Suomela)

[Juhana Laurinharju, Jukka Suomela, *Brief announcement: Linial's lower bound made easy*,
PODC 2014; arXiv:1402.2552v1]

Identifiers are `1, …, n`. A *`k`-ary `c`-colouring function* is a map `A` from `k`-tuples of
identifiers to colours such that

* (2) `A (x₁, …, x_k) ∈ {1, …, c}` for all `1 ≤ x₁ < ⋯ < x_k ≤ n`;
* (3) `A (x₁, …, x_k) ≠ A (x₂, …, x_{k+1})` for all `1 ≤ x₁ < ⋯ < x_{k+1} ≤ n`.

Tuples are functions `Fin k → ℕ`; `(x₁, …, x_k)` and `(x₂, …, x_{k+1})` are `Fin.init x` and
`Fin.tail x` of a `(k+1)`-tuple `x`.

## Main statements

* `lemma1`: Lemma 1, a `1`-ary `c`-colouring function has `c ≥ n`.
* `lemma2`: Lemma 2, a `k`-ary `c`-colouring function gives a `(k-1)`-ary `2^c`-colouring function
  (for `k ≥ 2`; for `k = 1` the statement is false: `lemma2_false_of_k_eq_one`).
* `le_tower_of_isColouringFunction_three`: a `k`-ary `3`-colouring function with `k ≥ 1` has
  `n ≤ ^{k+1}2` (`Nat.tower (k + 1)`).
-/

namespace Podc.LinialLowerBoundEasy

open Finset

/-- §3 of [Laurinharju–Suomela]: `A` is a **`k`-ary `c`-colouring function** for identifiers
`1, …, n`. Only strictly increasing tuples of identifiers are constrained. -/
structure IsColouringFunction (n k c : ℕ) (A : (Fin k → ℕ) → ℕ) : Prop where
  /-- Condition (2): colours are in `{1, …, c}`. -/
  mem : ∀ x : Fin k → ℕ, StrictMono x → (∀ i, x i ∈ Icc 1 n) → A x ∈ Icc 1 c
  /-- Condition (3): `A (x₁, …, x_k) ≠ A (x₂, …, x_{k+1})` for `1 ≤ x₁ < ⋯ < x_{k+1} ≤ n`. -/
  ne : ∀ x : Fin (k + 1) → ℕ, StrictMono x → (∀ i, x i ∈ Icc 1 n) →
    A (Fin.init x) ≠ A (Fin.tail x)

variable {n k c : ℕ} {A : (Fin k → ℕ) → ℕ}

/-- A `c`-colouring function is a `c'`-colouring function for `c ≤ c'`
("certainly it is also a `k`-ary `²2`-colouring function"). -/
theorem IsColouringFunction.mono {c' : ℕ} (h : IsColouringFunction n k c A) (hc : c ≤ c') :
    IsColouringFunction n k c' A where
  mem x hx hmem := by
    have := mem_Icc.1 (h.mem x hx hmem)
    exact mem_Icc.2 ⟨this.1, this.2.trans hc⟩
  ne := h.ne

/-- **Lemma 1** of [Laurinharju–Suomela]: if `A` is a `1`-ary `c`-colouring function, then
`c ≥ n`. -/
theorem lemma1 {A : (Fin 1 → ℕ) → ℕ} (h : IsColouringFunction n 1 c A) : n ≤ c := by
  have hlt : ∀ y z, y ∈ Icc 1 n → z ∈ Icc 1 n → y < z → A (fun _ => y) ≠ A (fun _ => z) := by
    intro y z hy hz hyz heq
    refine h.ne ![y, z] ?_ ?_ ?_
    · rw [Fin.strictMono_iff_lt_succ]
      intro i; fin_cases i; simpa using hyz
    · intro i; fin_cases i
      · simpa using hy
      · simpa using hz
    · convert heq using 2 <;> funext i <;> fin_cases i <;> rfl
  have hinj : Set.InjOn (fun y : ℕ => A (fun _ => y)) (Icc 1 n : Set ℕ) := by
    intro y hy z hz hyz
    by_contra hne
    rcases lt_or_gt_of_ne hne with hl | hl
    · exact hlt y z hy hz hl hyz
    · exact hlt z y hz hy hl hyz.symm
  have hmaps : Set.MapsTo (fun y : ℕ => A (fun _ => y)) (Icc 1 n : Set ℕ) (Icc 1 c : Set ℕ) :=
    fun y hy => h.mem _ (Subsingleton.strictMono _) (fun _ => hy)
  simpa using Finset.card_le_card_of_injOn _ hmaps hinj

/-- The set of colours (shifted down by one, so that it is a subset of `{0, …, c-1}`) of the
extensions `(x₁, …, x_{k-1}, x_k)` with `x_k > x_{k-1}`, `x_k ≤ n`, of a `(k-1)`-tuple `x`. -/
def colourSet (n : ℕ) {k : ℕ} (A : (Fin (k + 2) → ℕ) → ℕ) (x : Fin (k + 1) → ℕ) : Finset ℕ :=
  ((Icc 1 n).filter fun y => x (Fin.last k) < y).image fun y => A (Fin.snoc x y) - 1

/-- The colouring function `B` of Lemma 2:
`B (x₁, …, x_{k-1}) = {A (x₁, …, x_{k-1}, x_k) : x_k > x_{k-1}}`, a subset of `{1, …, c}`,
represented as an integer in `{1, …, 2^c}` (the binary code of the set, plus one). -/
def lemma2B (n : ℕ) {k : ℕ} (A : (Fin (k + 2) → ℕ) → ℕ) (x : Fin (k + 1) → ℕ) : ℕ :=
  1 + ∑ a ∈ colourSet n A x, 2 ^ a

/-- Extending an increasing tuple of identifiers by a larger identifier gives an increasing tuple
of identifiers. -/
theorem snoc_ext {m : ℕ} {x : Fin (m + 1) → ℕ} (hx : StrictMono x) (hmem : ∀ i, x i ∈ Icc 1 n)
    {y : ℕ} (hy : y ∈ Icc 1 n) (hlt : x (Fin.last m) < y) :
    StrictMono (Fin.snoc x y : Fin (m + 2) → ℕ) ∧ ∀ i, (Fin.snoc x y : Fin (m + 2) → ℕ) i ∈ Icc 1 n := by
  refine ⟨Fin.strictMono_snoc hx hlt, fun i => ?_⟩
  induction i using Fin.lastCases with
  | last => simpa using hy
  | cast j => simpa using hmem j

/-- **Lemma 2** of [Laurinharju–Suomela]: if `A` is a `k`-ary `c`-colouring function (`k ≥ 2`,
written `k + 2` here), then `B = lemma2B n A` is a `(k-1)`-ary `2^c`-colouring function. -/
theorem lemma2 {A : (Fin (k + 2) → ℕ) → ℕ} (h : IsColouringFunction n (k + 2) c A) :
    IsColouringFunction n (k + 1) (2 ^ c) (lemma2B n A) := by
  refine ⟨fun x hx hmem => ?_, fun x hx hmem heq => ?_⟩
  · -- (2): the colour set lies in `{0, …, c-1}`
    have hsub : ∀ a ∈ colourSet n A x, a < c := by
      intro a ha
      obtain ⟨y, hy, rfl⟩ := mem_image.1 ha
      obtain ⟨hyn, hlt⟩ := mem_filter.1 hy
      obtain ⟨h1, h2⟩ := snoc_ext hx hmem hyn hlt
      have := mem_Icc.1 (h.mem _ h1 h2)
      omega
    have := Nat.geomSum_lt (le_refl 2) hsub
    simp only [lemma2B, mem_Icc]
    omega
  · -- (3): if `B (x₁, …) = B (x₂, …)`, then `A x` is the colour of an extension of `(x₂, …)`
    have hset : colourSet n A (Fin.init x) = colourSet n A (Fin.tail x) := by
      have h' : (∑ a ∈ colourSet n A (Fin.init x), 2 ^ a) =
          ∑ a ∈ colourSet n A (Fin.tail x), 2 ^ a := by
        simp only [lemma2B] at heq; omega
      exact Finset.equivBitIndices.symm.injective (by simpa using h')
    have hα : A x - 1 ∈ colourSet n A (Fin.init x) := by
      refine mem_image.2 ⟨x (Fin.last _), mem_filter.2 ⟨hmem _, ?_⟩, by rw [Fin.snoc_init_self]⟩
      exact hx (by simp [Fin.lt_def])
    rw [hset] at hα
    obtain ⟨y, hy, hAy⟩ := mem_image.1 hα
    obtain ⟨hyn, hlt⟩ := mem_filter.1 hy
    have hlt' : x (Fin.last (k + 1)) < y := by simpa [Fin.tail] using hlt
    obtain ⟨h1, h2⟩ := snoc_ext hx hmem hyn hlt'
    have hA1 := mem_Icc.1 (h.mem x hx hmem)
    obtain ⟨h1', h2'⟩ := snoc_ext (x := Fin.tail x) (hx.comp Fin.strictMono_succ) (fun i => hmem _)
      hyn hlt
    have hA2 := mem_Icc.1 (h.mem _ h1' h2')
    refine h.ne _ h1 h2 ?_
    rw [Fin.init_snoc]
    change A x = A (Fin.snoc x y ∘ Fin.succ)
    rw [Fin.snoc_comp_succ]
    change A x = A (Fin.snoc (Fin.tail x) y)
    omega

/-- There is no `0`-ary colouring function as soon as `n ≥ 1`: condition (3) would require
`A () ≠ A ()`. -/
theorem not_isColouringFunction_zero {A : (Fin 0 → ℕ) → ℕ} (hn : 1 ≤ n) :
    ¬ IsColouringFunction n 0 c A := by
  intro h
  have hmono : StrictMono (fun _ : Fin 1 => (1 : ℕ)) := Subsingleton.strictMono _
  exact h.ne (fun _ => 1) hmono (fun _ => by simp [hn]) (congrArg A (Subsingleton.elim _ _))

/-- A `1`-ary `n`-colouring function: the identifier itself. -/
theorem isColouringFunction_id (n : ℕ) : IsColouringFunction n 1 n (fun x => x 0) := by
  refine ⟨fun x _ hmem => hmem 0, fun x hx _ => ?_⟩
  have := hx (show (0 : Fin 2) < 1 by decide)
  exact this.ne

/-- Lemma 2 is false for `k = 1` (the paper only applies it with `k ≥ 2`): for every `n ≥ 1`,
the identifier itself is a `1`-ary `n`-colouring function, but there is no `0`-ary
`2^n`-colouring function (indeed no `0`-ary colouring function at all). -/
theorem lemma2_false_of_k_eq_one (hn : 1 ≤ n) :
    IsColouringFunction n 1 n (fun x => x 0) ∧ ∀ B, ¬ IsColouringFunction n 0 (2 ^ n) B :=
  ⟨isColouringFunction_id n, fun _ => not_isColouringFunction_zero hn⟩

/-- Iterating Lemma 2 down to Lemma 1: a `(k+1)`-ary `^m2`-colouring function forces
`n ≤ ^{m+k}2`. -/
theorem le_tower_of_isColouringFunction :
    ∀ (k m : ℕ) (A : (Fin (k + 1) → ℕ) → ℕ), IsColouringFunction n (k + 1) (Nat.tower m) A →
      n ≤ Nat.tower (m + k)
  | 0, m, A, h => by simpa using lemma1 h
  | k + 1, m, A, h => by
    have := le_tower_of_isColouringFunction k (m + 1) _ (lemma2 h)
    rwa [show m + 1 + k = m + (k + 1) by omega] at this

/-- End of §4 of [Laurinharju–Suomela], tower form: if `A` is a `k`-ary `3`-colouring function
with `k ≥ 1`, then `^{k+1}2 ≥ n`. -/
theorem le_tower_of_isColouringFunction_three (hk : 1 ≤ k) (h : IsColouringFunction n k 3 A) :
    n ≤ Nat.tower (k + 1) := by
  obtain ⟨k, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have h4 : IsColouringFunction n (k + 1) (Nat.tower 2) A := h.mono (by decide)
  have := le_tower_of_isColouringFunction k 2 A h4
  rwa [show 2 + k = k + 1 + 1 by omega] at this

end Podc.LinialLowerBoundEasy
