import Papers.PODC2014.WritableObjects.Lemma48Inv

/-!
# Lemma 4.8, part 5: appending one event to a transcript
-/

namespace Podc.WritableObjects.WF

open Cslib.SharedMemory

variable {n : ℕ} {T : ObjSpec}

section
variable {α : Type} {l : List α} {e x : α} {k : ℕ}

lemma get_concat_iff : (l ++ [e])[k]? = some x ↔ (l[k]? = some x) ∨ (k = l.length ∧ e = x) := by
  rcases Nat.lt_or_ge k l.length with h | h
  · rw [List.getElem?_append_left h]
    constructor
    · exact Or.inl
    · rintro (h' | ⟨rfl, _⟩); exacts [h', absurd h (lt_irrefl _)]
  · rw [List.getElem?_append_right h]
    have : l[k]? = none := List.getElem?_eq_none h
    rw [this]
    rcases Nat.eq_or_lt_of_le h with h' | h'
    · subst h'; simp
    · rw [List.getElem?_eq_none (by simp; omega)]; simp; omega

lemma get_concat_of (h : l[k]? = some x) : (l ++ [e])[k]? = some x := get_concat_iff.2 (Or.inl h)

lemma get_concat_len : (l ++ [e])[l.length]? = some e := get_concat_iff.2 (Or.inr ⟨rfl, rfl⟩)

lemma lt_of_get (h : l[k]? = some x) : k < l.length := (List.getElem?_eq_some_iff.1 h).1

end

variable {tr : List (Ev (Fin n) (Idx n) T)} {e : Ev (Fin n) (Idx n) T}

lemma ptrAt_concat_le {t : ℕ} (h : t ≤ tr.length) : ptrAt (tr ++ [e]) t = ptrAt tr t := by
  unfold ptrAt; rw [List.take_append_of_le_length h]

lemma ptrAt_concat_ptr {p : Fin n} {i : Idx n} :
    ptrAt (tr ++ [.ptr p i]) (tr.length + 1) = some i := by
  unfold ptrAt
  rw [show tr.length + 1 = (tr ++ [Ev.ptr p i]).length by simp, List.take_length]
  simp [Ev.ptrVal]

lemma ptrAt_concat_of_ne (he : ∀ p i, e ≠ .ptr p i) :
    ptrAt (tr ++ [e]) (tr.length + 1) = ptrAt tr tr.length := by
  unfold ptrAt
  rw [show tr.length + 1 = (tr ++ [e]).length by simp, List.take_length, List.take_length]
  have : e.ptrVal = none := by cases e <;> simp_all [Ev.ptrVal]
  simp [this]

lemma SWF.concat {i : Idx n} {ts : ℕ} (h : SWF tr i ts) (he : ∀ p v, e ≠ .swinv p i v) :
    SWF (tr ++ [e]) i ts := by
  intro a p v ha
  rcases get_concat_iff.1 ha with ha | ⟨_, rfl⟩
  · obtain ⟨b, r, h1, h2, h3⟩ := h a p v ha
    exact ⟨b, r, h1, h2, get_concat_of h3⟩
  · exact absurd rfl (he p v)

lemma SWF.mono {i : Idx n} {ts ts' : ℕ} (h : SWF tr i ts) (hle : ts ≤ ts') : SWF tr i ts' := by
  intro a p v ha
  obtain ⟨b, r, h1, h2, h3⟩ := h a p v ha
  exact ⟨b, r, h1, by omega, h3⟩

lemma getElem_concat_lt {k : ℕ} (hk : k < tr.length) (hk' : k < (tr ++ [e]).length) :
    (tr ++ [e])[k] = tr[k] := List.getElem_append_left hk

lemma getElem_concat_len (hk : tr.length < (tr ++ [e]).length) :
    (tr ++ [e])[tr.length] = e := by simp

/-! ## `Sval` -/

lemma Sval_succ [NeZero n] (m : ℕ) :
    Sval n (m + 1) = (Sval n m + 1) % (2 * n : ℤ) := by
  have hn := Nat.pos_of_neZero n
  unfold Sval
  rcases m with _ | m
  · simp
  · simp only [Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel]
    have : (((m % (2 * n) : ℕ) : ℤ) + 1) % (2 * n : ℤ) = (((m % (2 * n) + 1) % (2 * n) : ℕ) : ℤ) := by
      push_cast; rfl
    rw [this, Nat.mod_add_mod]

lemma Sval_nonneg [NeZero n] {m : ℕ} (h : 1 ≤ m) : 0 ≤ Sval n m := by
  unfold Sval; rw [if_neg (by omega)]; exact Int.natCast_nonneg _

lemma Sval_lt [NeZero n] (m : ℕ) : Sval n m < 2 * n := by
  have hn := Nat.pos_of_neZero n
  unfold Sval; split_ifs
  · omega
  · have := Nat.mod_lt (m - 1) (show 0 < 2 * n by omega); omega

/-- `Sval` is injective on windows of fewer than `2n` epochs. -/
lemma Sval_inj [NeZero n] {a b : ℕ} (hab : a ≤ b) (hw : b < a + 2 * n) (h : Sval n a = Sval n b) :
    a = b := by
  have hn := Nat.pos_of_neZero n
  unfold Sval at h
  split_ifs at h with h1 h2 h2
  · omega
  · have h' : (a - 1) % (2 * n) = (b - 1) % (2 * n) := by exact_mod_cast h
    have := Nat.sub_mod_eq_zero_of_mod_eq h'.symm
    rw [show b - 1 - (a - 1) = b - a by omega] at this
    rcases Nat.eq_zero_or_pos (b - a) with h0 | h0
    · omega
    · have := Nat.le_of_dvd h0 (Nat.dvd_of_mod_eq_zero this); omega

/-- The reset index `x mod n` of line 44 is `(m - 1) mod n`. -/
lemma Sval_mod [NeZero n] {m : ℕ} (h : 1 ≤ m) {x : ℕ} (hx : (x : ℤ) = Sval n m) :
    x % n = (m - 1) % n := by
  unfold Sval at hx; rw [if_neg (by omega)] at hx
  have : x = (m - 1) % (2 * n) := by exact_mod_cast hx
  rw [this, Nat.mod_mul_left_mod]

end Podc.WritableObjects.WF
