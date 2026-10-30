import Papers.PODC2021.MISTreeLowerBounds.Model

/-!
# The problem family `Π_Δ(a, x)`, the problem `Π⁺_Δ(a, x)` and `k`-outdegree dominating sets (§3.1)

* Labels `M, P, O, A, X` (`L5`); `Π_Δ(a, x)` (`Pi Δ a x`) has the node configurations
  `M^{Δ-x} X^x`, `A^a X^{Δ-a}`, `P O^{Δ-1}` and the edge configurations
  `M[PAOX]`, `O[MAOX]`, `P[MX]`, `A[MOX]`, `X[MPAOX]`.
* `Π⁺_Δ(a, x)` (`PiPlus Δ a x`, §3.3) has the extra label `C` (`L6`), the node configurations
  `M^{Δ-x-1} X^{x+1}`, `P O^{Δ-1}`, `A^{a-x-1} X^{Δ-a+x+1}`, `C^{Δ-x} X^x` and the edge
  configurations `M[PACOX]`, `O[MACOX]`, `P[MX]`, `A[MCOX]`, `X[MPACOX]`, `C[MAOX]`.
* `k`-outdegree dominating sets (`SolvesODS`): every node outputs whether it is in `S` and a
  direction bit per incident edge; `S` is dominating, every edge inside `S` is oriented (exactly one
  endpoint claims it as outgoing) and every node of `S` has at most `k` outgoing edges inside `S`.

A configuration `ℓ₁^{n₁} ℓ₂^{n₂}` is expressed with label counts (`cnt`); since the counts of a
configuration of `Fin Δ → L` add up to `Δ`, `cnt σ ℓ₁ = n₁ ∧ cnt σ ℓ₂ = n₂` with `n₁ + n₂ = Δ`
says exactly that the configuration is `ℓ₁^{n₁} ℓ₂^{n₂}`. (Natural-number subtraction is truncated;
in the paper `0 ≤ a, x ≤ Δ`.)
-/

namespace Podc.MISTreeLowerBounds

open Cslib.ColourSystem FreeCox

/-- The labels of `Π_Δ(a, x)`. -/
inductive L5 | M | P | O | A | X
  deriving DecidableEq, Repr

instance : Fintype L5 where
  elems := {.M, .P, .O, .A, .X}
  complete x := by cases x <;> decide

/-- The labels of `Π⁺_Δ(a, x)`. -/
inductive L6 | M | P | O | A | X | C
  deriving DecidableEq, Repr

instance : Fintype L6 where
  elems := {.M, .P, .O, .A, .X, .C}
  complete x := by cases x <;> decide

variable {Δ : ℕ}

/-- Number of occurrences of the label `ℓ` in the configuration `σ`. -/
def cnt {α : Type*} [DecidableEq α] (σ : Fin Δ → α) (ℓ : α) : ℕ :=
  (Finset.univ.filter fun i => σ i = ℓ).card

theorem cnt_le {α : Type*} [DecidableEq α] (σ : Fin Δ → α) (ℓ : α) : cnt σ ℓ ≤ Δ := by
  unfold cnt
  exact (Finset.card_filter_le _ _).trans (by simp)

theorem cnt_add_cnt_le {α : Type*} [DecidableEq α] (σ : Fin Δ → α) {ℓ₁ ℓ₂ : α} (h : ℓ₁ ≠ ℓ₂) :
    cnt σ ℓ₁ + cnt σ ℓ₂ ≤ Δ := by
  unfold cnt
  rw [← Finset.card_union_of_disjoint]
  · exact (Finset.card_le_univ _).trans (by simp)
  · rw [Finset.disjoint_filter]; rintro i - h1 h2; exact h (h1.symm.trans h2)

/-- A configuration with `cnt σ ℓ₁ + cnt σ ℓ₂ = Δ` uses only `ℓ₁` and `ℓ₂`. -/
theorem eq_or_eq_of_cnt_add_cnt {α : Type*} [DecidableEq α] {σ : Fin Δ → α} {ℓ₁ ℓ₂ : α}
    (hne : ℓ₁ ≠ ℓ₂) (h : cnt σ ℓ₁ + cnt σ ℓ₂ = Δ) (i : Fin Δ) : σ i = ℓ₁ ∨ σ i = ℓ₂ := by
  by_contra hi
  push Not at hi
  have : (Finset.univ.filter fun j => σ j = ℓ₁) ∪ (Finset.univ.filter fun j => σ j = ℓ₂) ⊆
      Finset.univ.erase i := by
    intro j hj
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] at hj
    simp only [Finset.mem_erase, Finset.mem_univ, and_true]
    rintro rfl; rcases hj with hj | hj <;> [exact hi.1 hj; exact hi.2 hj]
  have h2 := Finset.card_le_card this
  rw [Finset.card_union_of_disjoint (by
    rw [Finset.disjoint_filter]; rintro j - h1 h2; exact hne (h1.symm.trans h2))] at h2
  simp only [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin] at h2
  unfold cnt at h
  have : 0 < Δ := Fin.pos i
  omega

theorem cnt_ite {α : Type*} [DecidableEq α] (S : Finset (Fin Δ)) {ℓ₁ ℓ₂ : α} (hne : ℓ₁ ≠ ℓ₂) :
    cnt (fun i => if i ∈ S then ℓ₁ else ℓ₂) ℓ₁ = S.card ∧
      cnt (fun i => if i ∈ S then ℓ₁ else ℓ₂) ℓ₂ = Δ - S.card := by
  unfold cnt
  constructor
  · congr 1; ext i; by_cases hi : i ∈ S <;> simp [hi, Ne.symm hne]
  · have : (Finset.univ.filter fun i => (if i ∈ S then ℓ₁ else ℓ₂) = ℓ₂) = Finset.univ \ S := by
      ext i; by_cases hi : i ∈ S <;> simp [hi, hne]
    rw [this, Finset.card_sdiff_of_subset (Finset.subset_univ _)]; simp

theorem cnt_ite_other {α : Type*} [DecidableEq α] (S : Finset (Fin Δ)) {ℓ₁ ℓ₂ ℓ : α}
    (h1 : ℓ ≠ ℓ₁) (h2 : ℓ ≠ ℓ₂) : cnt (fun i => if i ∈ S then ℓ₁ else ℓ₂) ℓ = 0 := by
  unfold cnt
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro i _; by_cases hi : i ∈ S <;> simp [hi, h1.symm, h2.symm]

/-- The edge constraint `E_Δ(a, x)`: `M[PAOX]`, `O[MAOX]`, `P[MX]`, `A[MOX]`, `X[MPAOX]` (i.e. all
pairs except `MM`, `AA`, `PP`, `PA`, `PO`). -/
def E5 : L5 → L5 → Prop
  | .M, .M => False
  | .A, .A => False
  | .P, .P => False
  | .P, .A => False
  | .A, .P => False
  | .P, .O => False
  | .O, .P => False
  | _, _ => True

instance : DecidableRel E5 := fun a b => by cases a <;> cases b <;> simp [E5] <;> infer_instance

/-- `Π_Δ(a, x)` (§3.1). -/
def Pi (Δ a x : ℕ) : Problem Δ L5 where
  node := {σ | (cnt σ .M = Δ - x ∧ cnt σ .X = x) ∨ (cnt σ .A = a ∧ cnt σ .X = Δ - a) ∨
    (cnt σ .P = 1 ∧ cnt σ .O = Δ - 1)}
  edge := E5
  edge_symm a b := by cases a <;> cases b <;> simp [E5]

/-- The edge constraint of `Π⁺_Δ(a, x)`: `M[PACOX]`, `O[MACOX]`, `P[MX]`, `A[MCOX]`, `X[MPACOX]`,
`C[MAOX]`. -/
def E6 : L6 → L6 → Prop
  | .M, .M => False
  | .A, .A => False
  | .C, .C => False
  | .P, .P => False
  | .P, .A => False
  | .A, .P => False
  | .P, .O => False
  | .O, .P => False
  | .P, .C => False
  | .C, .P => False
  | _, _ => True

instance : DecidableRel E6 := fun a b => by cases a <;> cases b <;> simp [E6] <;> infer_instance

/-- `Π⁺_Δ(a, x)` (§3.3). -/
def PiPlus (Δ a x : ℕ) : Problem Δ L6 where
  node := {σ | (cnt σ .M = Δ - x - 1 ∧ cnt σ .X = x + 1) ∨ (cnt σ .P = 1 ∧ cnt σ .O = Δ - 1) ∨
    (cnt σ .A = a - x - 1 ∧ cnt σ .X = Δ - a + x + 1) ∨ (cnt σ .C = Δ - x ∧ cnt σ .X = x)}
  edge := E6
  edge_symm a b := by cases a <;> cases b <;> simp [E6]

/-! ### `k`-outdegree dominating sets -/

/-- `A` computes a `k`-outdegree dominating set: the output `(inS, out)` at a node says whether it
is in `S` and, for each colour `c`, whether the edge of colour `c` is oriented away from it. -/
def SolvesODS (k : ℕ) (A : Orientation Δ → Bool × (Fin Δ → Bool)) : Prop :=
  ∀ (I : Orientation Δ) (v : FreeCox Δ),
    let o := fun w => A (I.shift w)
    -- `S` is dominating
    ((o v).1 = true ∨ ∃ c, (o (v * gen c)).1 = true) ∧
    -- every edge of `G[S]` gets exactly one orientation
    (∀ c, (o v).1 = true → (o (v * gen c)).1 = true → (o v).2 c ≠ (o (v * gen c)).2 c) ∧
    -- outdegree at most `k` in `G[S]`
    ((o v).1 = true → (Finset.univ.filter fun c => (o (v * gen c)).1 = true ∧ (o v).2 c = true).card ≤ k)

/-- The `k`-outdegree dominating set problem can be solved in `t` rounds. -/
def ODSSolvableIn (Δ k t : ℕ) : Prop :=
  ∃ A : Orientation Δ → Bool × (Fin Δ → Bool), IsLocal t A ∧ SolvesODS k A

end Podc.MISTreeLowerBounds
