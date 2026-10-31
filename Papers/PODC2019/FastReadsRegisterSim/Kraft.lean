import Mathlib

/-!
# Prefix-free families of binary strings

A family `S : α → List Bool` is *prefix-free* if `S a <+: S b` implies `a = b` (in particular
`S` is injective). If all strings have length `≤ n`, then `|α| ≤ 2 ^ n`
(`card_le_two_pow_of_prefixFree`), and if moreover `|α| = 2 ^ n`, every string has length
exactly `n` and every binary string of length `n` occurs (`complete_of_prefixFree`): the
family is the set of leaves of the complete binary tree of depth `n`.

These are the counting facts behind Lemma 3.3 of the paper (the decision tree of a read with at
most `log₂ k` reads is a complete binary tree with `k` leaves at depth `log₂ k`).
-- CSLib candidate (`Foundations/Data/List/PrefixFree.lean`)
-/

namespace Podc.FastReadsRegisterSim

open List

lemma prefix_or_prefix_of_getD {l₁ l₂ : List Bool}
    (h : ∀ i, i < l₁.length → i < l₂.length → l₁.getD i false = l₂.getD i false) :
    l₁ <+: l₂ ∨ l₂ <+: l₁ := by
  rcases le_total l₁.length l₂.length with hle | hle
  · left
    rw [prefix_iff_eq_take]
    apply ext_getElem (by simp [hle])
    intro i h1 h2
    have := h i h1 (by omega)
    simp only [getD_eq_getElem?_getD, getElem?_eq_getElem h1,
      getElem?_eq_getElem (show i < l₂.length by omega), Option.getD_some] at this
    simp [this]
  · right
    rw [prefix_iff_eq_take]
    apply ext_getElem (by simp [hle])
    intro i h1 h2
    have := h i (by omega) h1
    simp only [getD_eq_getElem?_getD, getElem?_eq_getElem h1,
      getElem?_eq_getElem (show i < l₁.length by omega), Option.getD_some] at this
    simp [this]

variable {α : Type} [Fintype α] (S : α → List Bool)

/-- Padding a string with `false` to a function `Fin n → Bool`. -/
def pad (n : ℕ) (a : α) : Fin n → Bool := fun i => (S a).getD i false

variable {S}

omit [Fintype α] in
lemma pad_injective (hpf : ∀ a b, S a <+: S b → a = b) {n : ℕ}
    (hlen : ∀ a, (S a).length ≤ n) : Function.Injective (pad S n) := by
  intro a b hab
  rcases prefix_or_prefix_of_getD (l₁ := S a) (l₂ := S b) (fun i hi _ =>
      congrFun hab ⟨i, lt_of_lt_of_le hi (hlen a)⟩) with h | h
  · exact hpf a b h
  · exact (hpf b a h).symm

/-- A prefix-free family of binary strings of length `≤ n` has at most `2 ^ n` members. -/
theorem card_le_two_pow_of_prefixFree (hpf : ∀ a b, S a <+: S b → a = b) (n : ℕ)
    (hlen : ∀ a, (S a).length ≤ n) : Fintype.card α ≤ 2 ^ n := by
  have := Fintype.card_le_of_injective _ (pad_injective hpf hlen)
  simpa using this

/-- A prefix-free family of `2 ^ n` binary strings of length `≤ n` consists of all strings of
length exactly `n`. -/
theorem complete_of_prefixFree (hpf : ∀ a b, S a <+: S b → a = b) (n : ℕ)
    (hlen : ∀ a, (S a).length ≤ n) (hcard : Fintype.card α = 2 ^ n) :
    (∀ a, (S a).length = n) ∧ ∀ u : List Bool, u.length = n → ∃ a, S a = u := by
  have hinj := pad_injective hpf hlen
  have hbij : Function.Bijective (pad S n) := by
    rw [Fintype.bijective_iff_injective_and_card]; simp [hinj, hcard]
  have hl : ∀ a, (S a).length = n := by
    intro a
    by_contra hne
    have hlt : (S a).length < n := lt_of_le_of_ne (hlen a) hne
    let f : Fin n → Bool := fun i => if (i : ℕ) = (S a).length then true else (S a).getD i false
    obtain ⟨b, hb⟩ := hbij.2 f
    have hag : ∀ i, i < (S a).length → i < (S b).length →
        (S a).getD i false = (S b).getD i false := by
      intro i hi _
      have := congrFun hb ⟨i, by omega⟩
      simp only [pad, f] at this
      rw [this]; split_ifs with h
      · omega
      · rfl
    have hab : a = b := by
      rcases prefix_or_prefix_of_getD hag with h | h
      · exact hpf a b h
      · exact (hpf b a h).symm
    subst hab
    have := congrFun hb ⟨(S a).length, hlt⟩
    simp [pad, f] at this
  refine ⟨hl, fun u hu => ?_⟩
  obtain ⟨a, ha⟩ := hbij.2 (fun i => u.getD i false)
  refine ⟨a, ?_⟩
  apply ext_getElem (by rw [hl a, hu])
  intro i h1 h2
  have := congrFun ha ⟨i, by rw [hl a] at h1; exact h1⟩
  simp only [pad, getD_eq_getElem?_getD, getElem?_eq_getElem h1, getElem?_eq_getElem h2,
    Option.getD_some] at this
  exact this

end Podc.FastReadsRegisterSim
