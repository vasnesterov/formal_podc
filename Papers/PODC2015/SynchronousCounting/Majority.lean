import Mathlib

/-!
# Majority votes

`maj s` returns a value held by a strict majority of the indices of `s : Fin n → α`, and a default
`0`-like value if there is none (the paper: "`majority x = a` if `a` is contained in `x` more than
half of the times, `∗` otherwise"). It is computable: it scans the indices for the first one whose
value has a strict majority.
-/

namespace SynchronousCounting

variable {α : Type*} [DecidableEq α]

/-- Number of indices holding the value `a`. -/
def cnt {n : ℕ} (s : Fin n → α) (a : α) : ℕ := (Finset.univ.filter fun j => s j = a).card

/-- The strict-majority value of `s`, or `d` if there is none. -/
def maj {n : ℕ} (s : Fin n → α) (d : α) : α :=
  match (List.finRange n).find? (fun j => decide (n < 2 * cnt s (s j))) with
  | some j => s j
  | none => d

/-- Two strict majorities coincide. -/
lemma eq_of_two_maj {n : ℕ} (s : Fin n → α) {a b : α} (ha : n < 2 * cnt s a)
    (hb : n < 2 * cnt s b) : a = b := by
  by_contra hne
  have hdisj : Disjoint (Finset.univ.filter fun j => s j = a)
      (Finset.univ.filter fun j => s j = b) := by
    rw [Finset.disjoint_filter]; intro j _ h1 h2; exact hne (h1.symm.trans h2)
  have := Finset.card_union_of_disjoint hdisj
  have hle := Finset.card_le_univ ((Finset.univ.filter fun j => s j = a) ∪
    (Finset.univ.filter fun j => s j = b))
  simp only [Fintype.card_fin] at hle
  unfold cnt at ha hb
  omega

/-- If `a` holds a strict majority, the majority vote returns `a`. -/
lemma maj_eq {n : ℕ} (s : Fin n → α) (d : α) {a : α} (ha : n < 2 * cnt s a) : maj s d = a := by
  have hpos : 0 < cnt s a := by omega
  obtain ⟨j₀, hj₀⟩ : ∃ j, s j = a := by
    unfold cnt at hpos
    obtain ⟨j, hj⟩ := Finset.card_pos.1 hpos
    exact ⟨j, (Finset.mem_filter.1 hj).2⟩
  unfold maj
  split
  · rename_i j hj
    have := List.find?_some hj
    simp only [decide_eq_true_eq] at this
    exact eq_of_two_maj s this ha
  · rename_i hnone
    rw [List.find?_eq_none] at hnone
    have := hnone j₀ (List.mem_finRange j₀)
    simp only [hj₀, decide_eq_true_eq] at this
    exact absurd ha this

/-- A sufficient condition for a strict majority: all indices outside a set `B` with
`2 |B| < n` hold `a`. -/
lemma lt_two_mul_cnt {n : ℕ} (s : Fin n → α) {a : α} (B : Finset (Fin n)) (hB : 2 * B.card < n)
    (h : ∀ j ∉ B, s j = a) : n < 2 * cnt s a := by
  have : Bᶜ ⊆ Finset.univ.filter fun j => s j = a := by
    intro j hj; simp only [Finset.mem_compl] at hj; simp [h j hj]
  have h1 := Finset.card_le_card this
  rw [Finset.card_compl, Fintype.card_fin] at h1
  unfold cnt; omega

/-- Majority vote with all values outside a minority `B` equal to `a`. -/
lemma maj_eq_of_minority {n : ℕ} (s : Fin n → α) (d : α) {a : α} (B : Finset (Fin n))
    (hB : 2 * B.card < n) (h : ∀ j ∉ B, s j = a) : maj s d = a :=
  maj_eq s d (lt_two_mul_cnt s B hB h)

/-- The majority vote is one of the values or the default. -/
lemma maj_mem {n : ℕ} (s : Fin n → α) (d : α) : maj s d = d ∨ ∃ j, maj s d = s j := by
  unfold maj
  split
  · exact Or.inr ⟨_, rfl⟩
  · exact Or.inl rfl

end SynchronousCounting
