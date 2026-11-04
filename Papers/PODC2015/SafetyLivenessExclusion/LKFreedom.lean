import Mathlib

/-!
# `(l, k)`-freedom (Section 5)

Definition 5.1 of Bushkov–Guerraoui (PODC 2015) only depends, for a fair execution, on three
sets of processes: the correct ones, those taking infinitely many steps, and those making
progress (infinitely many "good" responses). We call this triple a `Summary`; it satisfies
`prog ⊆ inf ⊆ correct`. The order on `(l, k)`-freedom properties is implication on summaries
(set inclusion of the execution sets).

* `LKFree l k`: Definition 5.1.
* `theorem_5_2`, `theorem_5_3`: the strongest non-excluded and weakest excluded `(l,k)`-freedom
  properties, for any safety property for which the cited (im)possibilities hold — consensus from
  registers ((1,1) implementable [20, 17], (1,2) excluded [5]) and TM with opacity ((1,n)
  implementable [9], (2,2) excluded [4]). The cited results are hypotheses.
* `section_5_3`: if `(2,2)` and `(1,3)` exclude `S` but `(1,2)` does not (the paper's §5.3
  property; Lemma 5.4 is the implementability of `(1,2)`), there is no weakest excluded
  `(l,k)`-freedom property.
* `incomparable_1_3_2_2`: the example of §5.1.
* `lf_union_of_not_iff`: the remark "`LF_l ∪ OF_k` is the set of executions ensuring
  `(l,k)`-freedom" is false (only `⊆` holds, `lkFree_imp_lf_or_of`).
-/

namespace Podc.SafetyLivenessExclusion.LK

/-- What Definition 5.1 sees of a fair execution: the correct processes, the processes taking
infinitely many steps, and the processes making progress. -/
structure Summary (n : ℕ) where
  /-- Correct (non-crashed) processes. -/
  correct : Finset (Fin n)
  /-- Processes taking infinitely many steps. -/
  inf : Finset (Fin n)
  /-- Processes making progress. -/
  prog : Finset (Fin n)
  inf_sub : inf ⊆ correct
  prog_sub : prog ⊆ inf

variable {n : ℕ}

/-- **Definition 5.1.** A fair execution ensures `(l, k)`-freedom if, whenever at most `k`
processes take infinitely many steps, at least `l` processes make progress if at least `l` are
correct, and all correct processes make progress otherwise. -/
def LKFree (l k : ℕ) (s : Summary n) : Prop :=
  s.inf.card ≤ k →
    (l ≤ s.correct.card → l ≤ s.prog.card) ∧ (s.correct.card < l → s.correct ⊆ s.prog)

/-- The admissible parameters: `1 ≤ l ≤ k ≤ n`. -/
def Adm (n l k : ℕ) : Prop := 1 ≤ l ∧ l ≤ k ∧ k ≤ n

/-- `(l, k)`-freedom is stronger than `(l', k')`-freedom. -/
def Stronger (n l k l' k' : ℕ) : Prop := ∀ s : Summary n, LKFree l k s → LKFree l' k' s

/-! ## Exclusion -/

variable {ι : Type*} (ens : ι → Prop) (sums : ι → Set (Summary n))

/-- `(l, k)`-freedom excludes the safety property: no implementation ensuring it (`ens`) has all
its fair executions (`sums`) `(l,k)`-free. -/
def Excl (l k : ℕ) : Prop := ¬ ∃ I, ens I ∧ ∀ s ∈ sums I, LKFree l k s

/-- Strongest `(l,k)`-freedom property that does not exclude the safety property. -/
def IsStrongestNonExcl (l k : ℕ) : Prop :=
  Adm n l k ∧ ¬ Excl ens sums l k ∧ ∀ l' k', Adm n l' k' → ¬ Excl ens sums l' k' → Stronger n l k l' k'

/-- Weakest `(l,k)`-freedom property that excludes the safety property. -/
def IsWeakestExcl (l k : ℕ) : Prop :=
  Adm n l k ∧ Excl ens sums l k ∧ ∀ l' k', Adm n l' k' → Excl ens sums l' k' → Stronger n l' k' l k

variable {ens sums}

theorem Excl.mono {l k l' k' : ℕ} (h : Stronger n l k l' k') (hex : Excl ens sums l' k') :
    Excl ens sums l k := by
  rintro ⟨I, hI, hs⟩
  exact hex ⟨I, hI, fun s hs' => h s (hs s hs')⟩

theorem stronger_refl (l k : ℕ) : Stronger n l k l k := fun _ h => h

/-! ## The order -/

/-- `l`-lock-freedom (as a condition on a summary). -/
def LF (l : ℕ) (s : Summary n) : Prop :=
  (l ≤ s.correct.card → l ≤ s.prog.card) ∧ (s.correct.card < l → s.correct ⊆ s.prog)

theorem lf_mono {l l' : ℕ} (h : l' ≤ l) (s : Summary n) (hs : LF l s) : LF l' s := by
  obtain ⟨h1, h2⟩ := hs
  constructor
  · intro hl'
    by_cases hl : l ≤ s.correct.card
    · exact le_trans h (h1 hl)
    · exact le_trans hl' (Finset.card_le_card (h2 (by omega)))
  · intro hl'
    by_cases hl : l ≤ s.correct.card
    · omega
    · exact h2 (by omega)

/-- `(l,k)`-freedom is stronger than `(l',k')`-freedom when `l' ≤ l` and `k' ≤ k`. -/
theorem stronger_of_le {l k l' k' : ℕ} (hl : l' ≤ l) (hk : k' ≤ k) : Stronger n l k l' k' :=
  fun s hs hinf => lf_mono hl s (hs (le_trans hinf hk))

/-- `(1, n)`-freedom (lock-freedom) is stronger than every `(1, k)`-freedom. -/
theorem stronger_one_n (k : ℕ) : Stronger n 1 n 1 k := by
  intro s hs _
  exact hs (le_trans (Finset.card_le_univ _) (by simp))

/-! ## Theorems 5.2 and 5.3 -/

/-- **Theorem 5.2** (consensus from registers). If `(1,1)`-freedom (obstruction-freedom) does not
exclude the safety property [20, 17] and `(1,2)`-freedom excludes it [5], then `(1,1)` is the
strongest non-excluding and `(1,2)` the weakest excluding `(l,k)`-freedom property. -/
theorem theorem_5_2 (hn : 2 ≤ n) (h11 : ¬ Excl ens sums 1 1) (h12 : Excl ens sums 1 2) :
    IsStrongestNonExcl ens sums 1 1 ∧ IsWeakestExcl ens sums 1 2 := by
  have hk : ∀ l k, Adm n l k → ¬ Excl ens sums l k → k = 1 := by
    intro l k hadm hne
    by_contra hk1
    exact hne (h12.mono (stronger_of_le hadm.1 (by have := hadm.1; have := hadm.2.1; omega)))
  refine ⟨⟨⟨le_rfl, le_rfl, by omega⟩, h11, fun l k hadm hne => ?_⟩,
    ⟨⟨le_rfl, by omega, hn⟩, h12, fun l k hadm hex => ?_⟩⟩
  · have := hk l k hadm hne
    have hl : l = 1 := by have := hadm.1; have := hadm.2.1; omega
    subst this; subst hl; exact stronger_refl 1 1
  · have hk2 : 2 ≤ k := by
      by_contra hk2
      have hk1 : k = 1 := by have := hadm.1; have := hadm.2.1; omega
      have hl1 : l = 1 := by have := hadm.1; have := hadm.2.1; omega
      subst hk1; subst hl1; exact h11 hex
    exact stronger_of_le hadm.1 hk2

/-- **Theorem 5.3** (TM with opacity). If `(1,n)`-freedom does not exclude the safety
property [9] and `(2,2)`-freedom excludes it [4], then `(1,n)` is the strongest non-excluding and
`(2,2)` the weakest excluding `(l,k)`-freedom property. -/
theorem theorem_5_3 (hn : 2 ≤ n) (h1n : ¬ Excl ens sums 1 n) (h22 : Excl ens sums 2 2) :
    IsStrongestNonExcl ens sums 1 n ∧ IsWeakestExcl ens sums 2 2 := by
  refine ⟨⟨⟨le_rfl, by omega, le_rfl⟩, h1n, fun l k hadm hne => ?_⟩,
    ⟨⟨by omega, le_rfl, hn⟩, h22, fun l k hadm hex => ?_⟩⟩
  · have hl : l = 1 := by
      by_contra hl
      exact hne (h22.mono (stronger_of_le (by have := hadm.1; omega)
        (by have := hadm.1; have := hadm.2.1; omega)))
    subst hl
    exact stronger_one_n k
  · have hl : 2 ≤ l := by
      by_contra hl
      have hl1 : l = 1 := by have := hadm.1; omega
      subst hl1
      exact h1n (hex.mono (stronger_one_n k)) |>.elim
    exact stronger_of_le hl (by have := hadm.2.1; omega)

/-! ## Section 5.3 and the examples -/

section Witnesses

variable (hn : 3 ≤ n)
include hn

/-- Three distinct processes. -/
def pa : Fin n := ⟨0, by omega⟩
/-- Three distinct processes. -/
def pb : Fin n := ⟨1, by omega⟩
/-- Three distinct processes. -/
def pc : Fin n := ⟨2, by omega⟩

/-- Two processes take steps, only one makes progress. -/
def s₁ : Summary n where
  correct := {pa hn, pb hn}
  inf := {pa hn, pb hn}
  prog := {pa hn}
  inf_sub := le_rfl
  prog_sub := by simp

/-- Three processes take steps, none makes progress. -/
def s₂ : Summary n where
  correct := {pa hn, pb hn, pc hn}
  inf := {pa hn, pb hn, pc hn}
  prog := ∅
  inf_sub := le_rfl
  prog_sub := by simp

theorem card_s₁ : (s₁ hn).correct.card = 2 ∧ (s₁ hn).inf.card = 2 ∧ (s₁ hn).prog.card = 1 := by
  simp [s₁, pa, pb, Fin.ext_iff]

theorem card_s₂ : (s₂ hn).correct.card = 3 ∧ (s₂ hn).inf.card = 3 ∧ (s₂ hn).prog.card = 0 := by
  have : ({pa hn, pb hn, pc hn} : Finset (Fin n)).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_pair] <;> simp [pa, pb, pc, Fin.ext_iff]
  simp [s₂, this]

theorem s₁_mem_1_3 : LKFree 1 3 (s₁ hn) := by
  obtain ⟨h1, h2, h3⟩ := card_s₁ hn
  intro _; refine ⟨fun _ => by omega, fun h => by omega⟩

theorem s₁_not_mem {l k : ℕ} (hl : 2 ≤ l) (hk : 2 ≤ k) : ¬ LKFree l k (s₁ hn) := by
  obtain ⟨h1, h2, h3⟩ := card_s₁ hn
  intro h
  obtain ⟨ha, hb⟩ := h (by omega)
  by_cases hl2 : l ≤ 2
  · have := ha (by omega); omega
  · have := Finset.card_le_card (hb (by omega)); omega

theorem s₂_mem_2_2 : LKFree 2 2 (s₂ hn) := by
  obtain ⟨h1, h2, h3⟩ := card_s₂ hn
  intro h; omega

theorem s₂_not_mem {k : ℕ} (hk : 3 ≤ k) : ¬ LKFree 1 k (s₂ hn) := by
  obtain ⟨h1, h2, h3⟩ := card_s₂ hn
  intro h
  have := (h (by omega)).1 (by omega)
  omega

/-- §5.1: `(1,3)`-freedom and `(2,2)`-freedom are incomparable. -/
theorem incomparable_1_3_2_2 : ¬ Stronger n 1 3 2 2 ∧ ¬ Stronger n 2 2 1 3 :=
  ⟨fun h => s₁_not_mem hn le_rfl le_rfl (h _ (s₁_mem_1_3 hn)),
    fun h => s₂_not_mem hn le_rfl (h _ (s₂_mem_2_2 hn))⟩

/-- **§5.3.** If `(2,2)`- and `(1,3)`-freedom exclude the safety property `S` while
`(1,2)`-freedom does not (Lemma 5.4), there is no weakest excluding `(l,k)`-freedom property. -/
theorem section_5_3 (h22 : Excl ens sums 2 2) (h13 : Excl ens sums 1 3)
    (h12 : ¬ Excl ens sums 1 2) : ¬ ∃ l k, IsWeakestExcl ens sums l k := by
  rintro ⟨l, k, hadm, hex, hweak⟩
  have hw13 := hweak 1 3 ⟨le_rfl, by omega, hn⟩ h13
  have hw22 := hweak 2 2 ⟨by omega, le_rfl, by omega⟩ h22
  have hl : l = 1 := by
    by_contra hl
    exact s₁_not_mem hn (by have := hadm.1; omega) (by have := hadm.1; have := hadm.2.1; omega)
      (hw13 _ (s₁_mem_1_3 hn))
  subst hl
  have hk : k ≤ 2 := by
    by_contra hk
    exact s₂_not_mem hn (by omega) (hw22 _ (s₂_mem_2_2 hn))
  exact h12 (Excl.mono (stronger_of_le le_rfl hk) hex)

end Witnesses

/-- `k`-obstruction-freedom (as a condition on a summary): if at most `k` processes take
infinitely many steps, all of them make progress. -/
def OF (k : ℕ) (s : Summary n) : Prop := s.inf.card ≤ k → s.inf ⊆ s.prog

/-- Every `(l,k)`-free execution is `l`-lock-free or `k`-obstruction-free. -/
theorem lkFree_imp_lf_or_of {l k : ℕ} (s : Summary n) (h : LKFree l k s) : LF l s ∨ OF k s := by
  by_cases hk : s.inf.card ≤ k
  · exact Or.inl (h hk)
  · exact Or.inr fun h' => absurd h' hk

/-- §5.1 remark "`LF_l ∪ OF_k` is the set of all executions that ensure `(l,k)`-freedom" is
false: with two correct processes of which one takes infinitely many steps and makes progress,
the execution is `2`-obstruction-free but not `(2,2)`-free. -/
theorem lf_union_of_not_iff (hn : 2 ≤ n) :
    ¬ ∀ s : Summary n, LKFree 2 2 s ↔ LF 2 s ∨ OF 2 s := by
  intro h
  let a : Fin n := ⟨0, by omega⟩
  let b : Fin n := ⟨1, by omega⟩
  let s : Summary n := ⟨{a, b}, {a}, {a}, by simp, le_rfl⟩
  have hab : a ≠ b := by simp [a, b, Fin.ext_iff]
  have hc : s.correct.card = 2 := Finset.card_pair hab
  have := (h s).2 (Or.inr fun _ => le_rfl)
  have := (this (by simp [s])).1 (by omega)
  simp [s] at this

end Podc.SafetyLivenessExclusion.LK
