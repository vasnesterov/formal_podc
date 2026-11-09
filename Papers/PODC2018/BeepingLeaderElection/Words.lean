import Mathlib

/-!
# Binary words and the α-encoding (Section 2.1)

Dufoulon, Burman, Beauquier. *Beeping a Deterministic Time-Optimal Leader Election.* DISC 2018
(full version of the PODC 2018 brief announcement).

A binary word is a `List Bool` (`true` = bit `1`), most significant bit first. The paper's order
"`x` is higher than `y`" (`x ≻ y`: `y` is a proper prefix of `x`, or `x` has `1` and `y` has `0` at the
first differing position) is the lexicographic order of Mathlib's `LinearOrder (List Bool)`, i.e.
`x ≻ y ↔ y < x`.

* `bin i` — binary representation of `i` (most significant bit first, no leading zeros);
* `alpha i = 1^{|bin i|} 0 bin i` — the α-encoding of [Casteigts et al.];
* `alpha_lt_alpha_iff` — the α-encoding is strictly monotone for the lexicographic order;
* `alpha_prefix_alpha` — no α-word is a prefix of another one (prefix-freeness);
* `alphaInv` — the decoding `α⁻¹` on well-formed words.
-/

namespace Podc.BeepingLeaderElection

/-- Binary words, most significant bit first (`true` = `1`). -/
abbrev Word := List Bool

/-- Binary representation of a natural number, most significant bit first (`bin 0 = []`). -/
def bin (i : ℕ) : Word := (Nat.bits i).reverse

/-- The α-encoding `α(i) = 1^{|bin i|} ‖ 0 ‖ bin i`. -/
def alpha (i : ℕ) : Word := List.replicate (bin i).length true ++ false :: bin i

/-- A word is *well-formed* if it is the α-encoding of a positive integer. -/
def WellFormed (x : Word) : Prop := ∃ i, 0 < i ∧ x = alpha i

/-! ### Lengths -/

/-- `|bin i|` is the bit size of `i`. -/
theorem bin_length (i : ℕ) : (bin i).length = Nat.size i := by
  simp [bin, Nat.size_eq_bits_len]

/-- For `0 < i`, `|bin i| = ⌊log₂ i⌋ + 1`. -/
theorem bin_length_of_pos {i : ℕ} (h : 0 < i) : (bin i).length = Nat.log 2 i + 1 := by
  rw [bin_length]
  apply le_antisymm
  · exact Nat.size_le.2 (Nat.lt_pow_succ_log_self (by norm_num) i)
  · exact Nat.lt_size.2 (Nat.pow_log_le_self 2 h.ne')

/-- `|α(i)| = 2|bin i| + 1`. -/
theorem alpha_length (i : ℕ) : (alpha i).length = 2 * (bin i).length + 1 := by
  simp [alpha]; omega

/-- For `0 < i`, `|α(i)| = 2⌊log₂ i⌋ + 3`. -/
theorem alpha_length_le {i : ℕ} (h : 0 < i) : (alpha i).length = 2 * Nat.log 2 i + 3 := by
  rw [alpha_length, bin_length_of_pos h]; ring

/-- `α(i)` is never empty. -/
theorem alpha_ne_nil (i : ℕ) : alpha i ≠ [] := by
  simp [alpha]

/-! ### Decoding binary words -/

/-- The number encoded by a binary word, most significant bit first. -/
def ofBits (x : Word) : ℕ := x.foldl (fun acc b => 2 * acc + b.toNat) 0

private theorem foldl_bits (x : Word) (acc : ℕ) :
    x.foldl (fun acc b => 2 * acc + b.toNat) acc = acc * 2 ^ x.length + ofBits x := by
  induction x generalizing acc with
  | nil => simp [ofBits]
  | cons a x ih =>
    simp only [ofBits, List.foldl_cons, List.length_cons] at ih ⊢
    rw [ih, ih (2 * 0 + a.toNat)]; ring

@[simp] theorem ofBits_nil : ofBits [] = 0 := rfl

theorem ofBits_cons (a : Bool) (x : Word) :
    ofBits (a :: x) = a.toNat * 2 ^ x.length + ofBits x := by
  rw [ofBits, List.foldl_cons, foldl_bits]; simp

theorem ofBits_append_singleton (x : Word) (a : Bool) :
    ofBits (x ++ [a]) = 2 * ofBits x + a.toNat := by
  simp [ofBits, List.foldl_append]

theorem ofBits_lt (x : Word) : ofBits x < 2 ^ x.length := by
  induction x with
  | nil => simp
  | cons a x ih =>
    rw [ofBits_cons, List.length_cons, pow_succ]
    cases a <;> simp <;> omega

theorem bin_bit (b : Bool) (n : ℕ) (h : n = 0 → b = true) :
    bin (Nat.bit b n) = bin n ++ [b] := by
  simp [bin, Nat.bits_append_bit n b h]

/-- `bin` is a right inverse of `ofBits`. -/
@[simp] theorem ofBits_bin (i : ℕ) : ofBits (bin i) = i := by
  induction i using Nat.binaryRec' with
  | zero => rfl
  | bit b n h ih => rw [bin_bit b n h, ofBits_append_singleton, ih, Nat.bit_val]

/-- `bin` is injective. -/
theorem bin_injective : Function.Injective bin := fun i j h => by
  rw [← ofBits_bin i, ← ofBits_bin j, h]

/-- The binary representation of a positive integer starts with `1`. -/
theorem bin_head {i : ℕ} (h : 0 < i) : (bin i).head? = some true := by
  induction i using Nat.binaryRec' with
  | zero => omega
  | bit b n hb ih =>
    rw [bin_bit b n hb]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [bin, hb rfl]
    · obtain ⟨c, l, hl⟩ := List.exists_cons_of_ne_nil (l := bin n) (by
        intro h0; simpa [h0] using ih hn)
      have := ih hn
      simp_all

/-- `α(i)` starts with `1` for `0 < i`. -/
theorem alpha_head {i : ℕ} (h : 0 < i) : (alpha i).head? = some true := by
  obtain ⟨c, l, hl⟩ := List.exists_cons_of_ne_nil
    (fun h0 : bin i = [] => by simpa [h0] using bin_head h)
  simp [alpha, hl, List.replicate_succ]

/-! ### Order -/

/-- For binary words of equal length, the lexicographic order agrees with the numeric order. -/
theorem lt_iff_ofBits_lt {x y : Word} (h : x.length = y.length) :
    x < y ↔ ofBits x < ofBits y := by
  induction x generalizing y with
  | nil => cases y <;> simp_all
  | cons a x ih =>
    cases y with
    | nil => simp at h
    | cons b y =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at h
      have hx := ofBits_lt x
      have hy := ofBits_lt y
      rw [List.cons_lt_cons_iff, ofBits_cons, ofBits_cons, ih h, h]
      rw [h] at hx
      cases a <;> cases b <;> simp [Bool.lt_iff] <;> omega

/-- Common-prefix cancellation for the lexicographic order. -/
theorem append_lt_append_iff (l : Word) {x y : Word} : l ++ x < l ++ y ↔ x < y := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

private theorem alpha_eq_of_lt {j k : ℕ} (h : k < (bin j).length) :
    alpha j = List.replicate k true ++
      true :: (List.replicate ((bin j).length - k - 1) true ++ false :: bin j) := by
  obtain ⟨m, hm⟩ : ∃ m, (bin j).length = k + 1 + m := ⟨_, (Nat.add_sub_of_le h).symm⟩
  rw [alpha, hm, List.replicate_add, List.replicate_add, show k + 1 + m - k - 1 = m by omega]
  simp [List.replicate_succ]

/-- The α-encoding is strictly increasing for the lexicographic order. -/
theorem alpha_strictMono : StrictMono alpha := by
  intro i j hij
  have hs : (bin i).length ≤ (bin j).length := by
    simp only [bin_length]; exact Nat.size_le_size hij.le
  rcases hs.lt_or_eq with hs | hs
  · rw [alpha_eq_of_lt hs, alpha, append_lt_append_iff, List.cons_lt_cons_iff]
    simp
  · rw [alpha, alpha, hs, append_lt_append_iff, List.cons_lt_cons_iff]
    right
    refine ⟨rfl, ?_⟩
    rw [lt_iff_ofBits_lt (by rw [hs]), ofBits_bin, ofBits_bin]
    exact hij

/-- Lemma (Section 2.1): `α(i) < α(j)` lexicographically iff `i < j`; i.e. `α(j) ≻ α(i)` iff `j > i`. -/
theorem alpha_lt_alpha_iff {i j : ℕ} : alpha i < alpha j ↔ i < j :=
  alpha_strictMono.lt_iff_lt

/-- The α-encoding is injective. -/
theorem alpha_injective : Function.Injective alpha :=
  alpha_strictMono.injective

/-- Prefix-freeness: if `α(i)` is a prefix of `α(j)` then `i = j`. -/
theorem alpha_prefix_alpha {i j : ℕ} (h : alpha i <+: alpha j) : i = j := by
  rcases lt_trichotomy (bin i).length (bin j).length with hs | hs | hs
  · rw [alpha_eq_of_lt hs, alpha, List.prefix_append_right_inj, List.cons_prefix_cons] at h
    simp at h
  · apply alpha_injective
    apply h.eq_of_length
    rw [alpha_length, alpha_length, hs]
  · rw [alpha_eq_of_lt hs, alpha, List.prefix_append_right_inj, List.cons_prefix_cons] at h
    simp at h

/-! ### The decoding `α⁻¹` -/

/-- Number of leading `1`s of a word. -/
def leadingOnes : Word → ℕ
  | true :: x => leadingOnes x + 1
  | _ => 0

theorem take_leadingOnes (x : Word) :
    x.take (leadingOnes x) = List.replicate (leadingOnes x) true := by
  induction x with
  | nil => rfl
  | cons a x ih => cases a <;> simp [leadingOnes, ih, List.replicate_succ]

theorem leadingOnes_replicate_append (n : ℕ) (b : Word) :
    leadingOnes (List.replicate n true ++ false :: b) = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, leadingOnes, ih]

/-- The decoding `α⁻¹`: returns `some i` iff the word is `α(i)`. -/
def alphaInv (x : Word) : Option ℕ :=
  match x.drop (leadingOnes x) with
  | false :: b => if b.length = leadingOnes x ∧ bin (ofBits b) = b then some (ofBits b) else none
  | _ => none

/-- `α⁻¹(α(i)) = i`. -/
@[simp] theorem alphaInv_alpha (i : ℕ) : alphaInv (alpha i) = some i := by
  have h1 := leadingOnes_replicate_append (bin i).length (bin i)
  unfold alphaInv alpha
  rw [h1, List.drop_left' (by simp)]
  simp

/-- `α⁻¹` only succeeds on α-words. -/
theorem eq_alpha_of_alphaInv {x : Word} {i : ℕ} (h : alphaInv x = some i) : x = alpha i := by
  unfold alphaInv at h
  have hx := List.take_append_drop (leadingOnes x) x
  split at h
  next b hb =>
    split_ifs at h with hc
    cases h
    rw [← hx, take_leadingOnes, hb, alpha, hc.2, hc.1]
  · simp at h

theorem alphaInv_eq_some_iff {x : Word} {i : ℕ} : alphaInv x = some i ↔ x = alpha i :=
  ⟨eq_alpha_of_alphaInv, fun h => h ▸ alphaInv_alpha i⟩

/-- Well-formed words are exactly those decoded by `α⁻¹` to a positive integer. -/
theorem wellFormed_iff_alphaInv {x : Word} : WellFormed x ↔ ∃ i, 0 < i ∧ alphaInv x = some i := by
  simp [WellFormed, alphaInv_eq_some_iff]

instance : DecidablePred WellFormed := fun x =>
  decidable_of_iff (∃ i ∈ alphaInv x, 0 < i) (by
    rw [wellFormed_iff_alphaInv]; simp [and_comm])

end Podc.BeepingLeaderElection
