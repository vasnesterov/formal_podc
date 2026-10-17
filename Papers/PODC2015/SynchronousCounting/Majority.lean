import Mathlib
import Cslib.Foundations.Data.Finset.Quorum

/-!
# Majority votes

`maj s` returns a value held by a strict majority of the indices of `s : Fin n → α`, and a default
`0`-like value if there is none (the paper: "`majority x = a` if `a` is contained in `x` more than
half of the times, `∗` otherwise"). It is computable: it scans the indices for the first one whose
value has a strict majority; `maj_eq_majority?` identifies it with the library selector
`Finset.majority?`.
-/

namespace SynchronousCounting

variable {α : Type*} [DecidableEq α]

/-- Number of indices holding the value `a`. -/
abbrev cnt {n : ℕ} (s : Fin n → α) (a : α) : ℕ := Finset.univ.countEq s a

/-- The strict-majority value of `s`, or `d` if there is none. -/
def maj {n : ℕ} (s : Fin n → α) (d : α) : α :=
  match (List.finRange n).find? (fun j => decide (n < 2 * cnt s (s j))) with
  | some j => s j
  | none => d

/-- Two strict majorities coincide. -/
lemma eq_of_two_maj {n : ℕ} (s : Fin n → α) {a b : α} (ha : n < 2 * cnt s a)
    (hb : n < 2 * cnt s b) : a = b :=
  Finset.eq_of_card_lt_countEq_add_countEq (s := .univ) (f := s)
    (by rw [Finset.card_univ, Fintype.card_fin]; change n < cnt s a + cnt s b; omega)

/-- `maj` is the library's strict-majority selector `Finset.majority?` (with default `d`). -/
lemma maj_eq_majority? {n : ℕ} (s : Fin n → α) (d : α) :
    maj s d = (Finset.univ.majority? fun j => some (s j)).getD d := by
  unfold maj
  rw [← Finset.find?_map_eq_majority? (L := List.finRange n) (fun j _ => List.mem_finRange j)
    (p := fun j => decide (n < 2 * cnt s (s j))) (fun j => by simp)]
  cases (List.finRange n).find? fun j => decide (n < 2 * cnt s (s j)) <;> rfl

/-- If `a` holds a strict majority, the majority vote returns `a`. -/
lemma maj_eq {n : ℕ} (s : Fin n → α) (d : α) {a : α} (ha : n < 2 * cnt s a) : maj s d = a := by
  rw [maj_eq_majority?, Finset.majority?_eq_some_iff.2 (by simpa using ha), Option.getD_some]

/-- A sufficient condition for a strict majority: all indices outside a set `B` with
`2 |B| < n` hold `a`. -/
lemma lt_two_mul_cnt {n : ℕ} (s : Fin n → α) {a : α} (B : Finset (Fin n)) (hB : 2 * B.card < n)
    (h : ∀ j ∉ B, s j = a) : n < 2 * cnt s a := by
  have h1 : (Finset.univ \ B).card ≤ cnt s a :=
    Finset.card_sdiff_le_countEq fun j _ hj => h j hj
  rw [← Finset.compl_eq_univ_sdiff, Finset.card_compl, Fintype.card_fin] at h1
  omega

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
