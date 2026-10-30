import Cslib.Probability.Finite.Uniform
import Cslib.Foundations.Data.Nat.Log

/-!
# Isolating one element with a pairwise independent hash function (Lemma 4)

A random hash function `h : U → [r]` is drawn uniformly from a finite family `Ω`
(`h : Ω → U → ℕ`). It is *pairwise independent* on the key set `K` (`IsPairwiseIndep`) if every
key is mapped uniformly to `[r] = {0, …, r - 1}` and any two distinct keys independently so.

* `card_isolated_ge` — for `m ≤ r`, the number of seeds for which *exactly one* element of
  `W ⊆ K` hashes below `m` is at least `|Ω| (|W| m / r - |W| (|W| - 1) m² / r²)` (the paper's
  chain of (in)equalities, by the pointwise Bonferroni inequality `[k = 1] ≥ 2k - k²`).
* `lemma4_strong` — **Lemma 4** with the constant `3/16`: if `r = 2^ℓ` and `0 < |W| < 2^(ℓ-1)`,
  then with probability `≥ 3/16` some `j < ℓ` has exactly one `w ∈ W` with `h(w) ∈ [2^j]`;
  `lemma4` is the paper's statement with `1/16`. The witness is the paper's
  `j = ℓ - ⌈lg |W|⌉ - 1` (`exists_good_j`).
-/

namespace Podc.MSTImpromptuRepair

open Finset Cslib.Probability

variable {Ω U : Type*} [Fintype Ω] [DecidableEq U]

-- CSLib candidate: `Cslib/Probability/Finite/` (pairwise independent families, isolation)
/-- `h` is a pairwise independent (2-independent) family of functions `K → [r]`: for keys
`x ≠ y` of `K` and values `a, b < r`, `Pr[h(x) = a] = 1/r` and `Pr[h(x) = a ∧ h(y) = b] = 1/r²`
(stated by counting seeds). -/
def IsPairwiseIndep (r : ℕ) (K : Finset U) (h : Ω → U → ℕ) : Prop :=
  (∀ x ∈ K, ∀ a < r, r * #(univ.filter fun ω => h ω x = a) = Fintype.card Ω) ∧
  (∀ x ∈ K, ∀ y ∈ K, x ≠ y → ∀ a < r, ∀ b < r,
    r * r * #(univ.filter fun ω => h ω x = a ∧ h ω y = b) = Fintype.card Ω)

variable {r : ℕ} {K : Finset U} {h : Ω → U → ℕ}

/-- `Pr[h(x) < m] = m / r` for `m ≤ r`. -/
theorem IsPairwiseIndep.card_lt {hp : IsPairwiseIndep r K h} {x : U} (hx : x ∈ K) {m : ℕ}
    (hm : m ≤ r) : r * #(univ.filter fun ω => h ω x < m) = m * Fintype.card Ω := by
  rw [card_eq_sum_card_fiberwise (f := fun ω => h ω x) (t := range m)
    (fun ω hω => by simpa using hω), mul_sum]
  rw [show m * Fintype.card Ω = ∑ _a ∈ range m, Fintype.card Ω by simp]
  refine sum_congr rfl fun a ha => ?_
  rw [← hp.1 x hx a (by simp at ha; omega), filter_filter]
  congr 2; ext ω; simp only [mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨-, h⟩; exact h
  · intro h; exact ⟨by simp at ha; omega, h⟩

/-- `Pr[h(x) < m ∧ h(y) < m] = m² / r²` for distinct keys and `m ≤ r`. -/
theorem IsPairwiseIndep.card_lt_lt {hp : IsPairwiseIndep r K h} {x y : U} (hx : x ∈ K)
    (hy : y ∈ K) (hxy : x ≠ y) {m : ℕ} (hm : m ≤ r) :
    r * r * #(univ.filter fun ω => h ω x < m ∧ h ω y < m) = m * m * Fintype.card Ω := by
  rw [card_eq_sum_card_fiberwise (f := fun ω => h ω x) (t := range m)
    (fun ω hω => by simp at hω; simpa using hω.1), mul_sum]
  rw [show m * m * Fintype.card Ω = ∑ _a ∈ range m, m * Fintype.card Ω by simp; ring]
  refine sum_congr rfl fun a ha => ?_
  simp only [mem_range] at ha
  rw [filter_filter, card_eq_sum_card_fiberwise (f := fun ω => h ω y) (t := range m)
    (fun ω hω => by simp at hω; simpa using hω.1.2), mul_sum]
  rw [show m * Fintype.card Ω = ∑ _b ∈ range m, Fintype.card Ω by simp]
  refine sum_congr rfl fun b hb => ?_
  simp only [mem_range] at hb
  rw [← hp.2 x hx y hy hxy a (by omega) b (by omega), filter_filter]
  congr 2; ext ω; simp only [mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨⟨-, h1⟩, h2⟩; exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨⟨⟨by omega, by omega⟩, h1⟩, h2⟩

/-- **The chain of inequalities in the proof of Lemma 4.** For `W ⊆ K` and `m ≤ r`,
`r² · #{ω | exactly one w ∈ W has h(w) < m} ≥ (|W| m r - |W| (|W| - 1) m²) |Ω|`. -/
theorem card_isolated_ge (hp : IsPairwiseIndep r K h) {W : Finset U} (hW : W ⊆ K) {m : ℕ}
    (hm : m ≤ r) :
    ((#W : ℝ) * m * r - #W * (#W - 1) * m ^ 2) * Fintype.card Ω ≤
      (r : ℝ) ^ 2 * #(univ.filter fun ω => #(W.filter fun w => h ω w < m) = 1) := by
  classical
  set k : Ω → ℕ := fun ω => #(W.filter fun w => h ω w < m)
  -- pointwise Bonferroni: `[k = 1] ≥ 2k - k²`
  have hpt : ∀ ω, (2 * (k ω : ℝ) - (k ω : ℝ) ^ 2) ≤ if k ω = 1 then 1 else 0 := by
    intro ω
    split_ifs with h1
    · rw [h1]; norm_num
    · have : (k ω : ℝ) * (k ω - 2) ≥ 0 := by
        rcases Nat.lt_or_ge (k ω) 2 with h2 | h2
        · have : k ω = 0 := by omega
          simp [this]
        · have : (2 : ℝ) ≤ k ω := by exact_mod_cast h2
          positivity
      nlinarith
  have hsum1 : ∑ ω, (k ω : ℝ) = ∑ w ∈ W, (#(univ.filter fun ω => h ω w < m) : ℝ) := by
    simp only [k, card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
    exact sum_comm
  have hsum2 : ∑ ω, (k ω : ℝ) ^ 2 = ∑ w ∈ W, ∑ w' ∈ W,
      (#(univ.filter fun ω => h ω w < m ∧ h ω w' < m) : ℝ) := by
    simp only [k, card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero, sq,
      sum_mul_sum]
    rw [sum_comm]
    refine sum_congr rfl fun w _ => ?_
    rw [sum_comm]
    refine sum_congr rfl fun w' _ => ?_
    refine sum_congr rfl fun ω _ => ?_
    split_ifs <;> simp_all
  have hr0 : (0 : ℝ) ≤ r := by positivity
  -- the single and pair counts
  have h1 : ∀ w ∈ W, (r : ℝ) * #(univ.filter fun ω => h ω w < m) = m * Fintype.card Ω := by
    intro w hw; exact_mod_cast hp.card_lt (hW hw) hm
  have h2 : ∀ w ∈ W, ∀ w' ∈ W, w ≠ w' → (r : ℝ) * r *
      #(univ.filter fun ω => h ω w < m ∧ h ω w' < m) = m * m * Fintype.card Ω := by
    intro w hw w' hw' hne; exact_mod_cast hp.card_lt_lt (hW hw) (hW hw') hne hm
  have hdiag : ∀ w, (#(univ.filter fun ω => h ω w < m ∧ h ω w < m) : ℝ) =
      #(univ.filter fun ω => h ω w < m) := by
    intro w; simp
  -- `r² ∑ k² = |W| m r |Ω| + |W|(|W|-1) m² |Ω|`
  have hS2 : (r : ℝ) ^ 2 * ∑ ω, (k ω : ℝ) ^ 2 =
      #W * m * r * Fintype.card Ω + #W * (#W - 1) * m ^ 2 * Fintype.card Ω := by
    rw [hsum2, mul_sum]
    have : ∀ w ∈ W, (r : ℝ) ^ 2 * ∑ w' ∈ W,
        (#(univ.filter fun ω => h ω w < m ∧ h ω w' < m) : ℝ) =
        m * r * Fintype.card Ω + (#W - 1) * m ^ 2 * Fintype.card Ω := by
      intro w hw
      rw [← add_sum_erase W _ hw, hdiag, mul_add, mul_sum]
      have e1 : (r : ℝ) ^ 2 * #(univ.filter fun ω => h ω w < m) = m * r * Fintype.card Ω := by
        rw [sq, mul_assoc, h1 w hw]; ring
      have e2 : ∑ w' ∈ W.erase w, (r : ℝ) ^ 2 *
          #(univ.filter fun ω => h ω w < m ∧ h ω w' < m) =
          ∑ _w' ∈ W.erase w, (m : ℝ) ^ 2 * Fintype.card Ω := by
        refine sum_congr rfl fun w' hw' => ?_
        rw [sq, h2 w hw w' (mem_of_mem_erase hw') (ne_of_mem_erase hw').symm, sq]
      rw [e1, e2, sum_const, card_erase_of_mem hw, nsmul_eq_mul]
      have : 1 ≤ #W := card_pos.2 ⟨w, hw⟩
      push_cast [this]; ring
    rw [sum_congr rfl this, sum_const, nsmul_eq_mul]; ring
  have hS1 : (r : ℝ) ^ 2 * ∑ ω, (k ω : ℝ) = #W * m * r * Fintype.card Ω := by
    rw [hsum1, mul_sum]
    rw [sum_congr rfl fun w hw => show (r : ℝ) ^ 2 * #(univ.filter fun ω => h ω w < m) =
        m * r * Fintype.card Ω by rw [sq, mul_assoc, h1 w hw]; ring]
    rw [sum_const, nsmul_eq_mul]; ring
  have hcount : (#(univ.filter fun ω => k ω = 1) : ℝ) = ∑ ω, if k ω = 1 then (1 : ℝ) else 0 := by
    rw [card_filter]; push_cast; rfl
  have hle : ∑ ω, (2 * (k ω : ℝ) - (k ω : ℝ) ^ 2) ≤ (#(univ.filter fun ω => k ω = 1) : ℝ) := by
    rw [hcount]; exact sum_le_sum fun ω _ => hpt ω
  rw [sum_sub_distrib, ← mul_sum] at hle
  have hr2 : (0 : ℝ) ≤ (r : ℝ) ^ 2 := by positivity
  have := mul_le_mul_of_nonneg_left hle hr2
  nlinarith [hS1, hS2]

/-- The paper's choice `j = ℓ - ⌈lg |W|⌉ - 1` satisfies `2^ℓ ≤ 4 |W| 2^j` and `2 |W| 2^j ≤ 2^ℓ`
(i.e. `1/(4|W|) ≤ 2^j / 2^ℓ ≤ 1/(2|W|)`) as soon as `0 < |W| ≤ 2^(ℓ-1)`. -/
theorem exists_good_j {ℓ w : ℕ} (hw0 : 0 < w) (hw : 2 * w ≤ 2 ^ ℓ) :
    ∃ j < ℓ, j = ℓ - Nat.clog 2 w - 1 ∧ 2 ^ ℓ < 4 * w * 2 ^ j ∧ 2 * w * 2 ^ j ≤ 2 ^ ℓ := by
  set c := Nat.clog 2 w
  have hc1 : w ≤ 2 ^ c := Nat.le_pow_clog (by norm_num) w
  have hc2 : 2 ^ c < 2 * w := Nat.pow_clog_lt_mul (by norm_num) hw0.ne'
  have hcℓ : c + 1 ≤ ℓ := by
    by_contra hlt
    push_neg at hlt
    have : 2 ^ ℓ ≤ 2 ^ c := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  refine ⟨ℓ - c - 1, by omega, rfl, ?_, ?_⟩
  · have e : 2 ^ ℓ = 2 * 2 ^ c * 2 ^ (ℓ - c - 1) := by
      rw [mul_comm 2, mul_assoc, ← pow_succ', ← pow_add]; congr 1; omega
    rw [e]
    have : 0 < 2 ^ (ℓ - c - 1) := by positivity
    nlinarith
  · have e : 2 ^ ℓ = 2 * 2 ^ c * 2 ^ (ℓ - c - 1) := by
      rw [mul_comm 2, mul_assoc, ← pow_succ', ← pow_add]; congr 1; omega
    rw [e]
    have : 0 < 2 ^ (ℓ - c - 1) := by positivity
    nlinarith

/-- **Lemma 4 (with the sharper constant `3/16`).** Let `h` be a pairwise independent family of
functions from `K` into `[2^ℓ]` and `W ⊆ K` with `0 < |W| < 2^(ℓ-1)`. Then with probability at
least `3/16`, for `j = ℓ - ⌈lg |W|⌉ - 1` exactly one `w ∈ W` hashes into `[2^j]`. -/
theorem lemma4_strong [Nonempty Ω] {ℓ : ℕ} (hp : IsPairwiseIndep (2 ^ ℓ) K h) {W : Finset U}
    (hW : W ⊆ K) (hW0 : 0 < #W) (hWℓ : 2 * #W < 2 ^ ℓ) :
    ∃ j < ℓ, j = ℓ - Nat.clog 2 #W - 1 ∧
      3 / 16 ≤ uprob (fun ω => #(W.filter fun w => h ω w < 2 ^ j) = 1) := by
  classical
  obtain ⟨j, hjℓ, hjdef, hj1, hj2⟩ := exists_good_j hW0 hWℓ.le
  refine ⟨j, hjℓ, hjdef, ?_⟩
  have hm : 2 ^ j ≤ 2 ^ ℓ := Nat.pow_le_pow_right (by norm_num) hjℓ.le
  have key := card_isolated_ge hp hW hm
  rw [uprob_eq_card_filter]
  have hΩ : (0 : ℝ) < Fintype.card Ω := by exact_mod_cast Fintype.card_pos
  rw [le_div_iff₀ hΩ]
  set A : ℝ := #W * 2 ^ j
  set R : ℝ := 2 ^ ℓ
  have hR : 0 < R := by positivity
  have h1 : R < 4 * A := by simp only [A, R]; exact_mod_cast (by linarith [hj1] : 2 ^ ℓ < 4 * (#W * 2 ^ j))
  have h2 : 2 * A ≤ R := by simp only [A, R]; exact_mod_cast (by linarith [hj2] : 2 * (#W * 2 ^ j) ≤ 2 ^ ℓ)
  push_cast at key
  have hW1 : (#W : ℝ) * (#W - 1) * ((2 : ℝ) ^ j) ^ 2 ≤ A ^ 2 := by
    simp only [A]
    have : (0 : ℝ) ≤ ((2 : ℝ) ^ j) ^ 2 := by positivity
    have : (0 : ℝ) ≤ #W := by positivity
    nlinarith
  -- `(A R - A²) ≥ 3/16 R²` for `R/4 < A ≤ R/2`
  have hq : 3 / 16 * R ^ 2 ≤ A * R - A ^ 2 := by nlinarith
  have hC : 0 ≤ (Fintype.card Ω : ℝ) := hΩ.le
  have : (#W : ℝ) * 2 ^ j * 2 ^ ℓ = A * R := by simp only [A, R]
  rw [this] at key
  have hkey : (A * R - A ^ 2) * Fintype.card Ω ≤ R ^ 2 * #(univ.filter fun ω =>
      #(W.filter fun w => h ω w < 2 ^ j) = 1) := by
    refine le_trans ?_ key
    exact mul_le_mul_of_nonneg_right (by linarith) hC
  have : 3 / 16 * R ^ 2 * Fintype.card Ω ≤ R ^ 2 * #(univ.filter fun ω =>
      #(W.filter fun w => h ω w < 2 ^ j) = 1) :=
    le_trans (mul_le_mul_of_nonneg_right hq hC) hkey
  have hR2 : 0 < R ^ 2 := by positivity
  nlinarith

/-- **Lemma 4.** Let `h` be a pairwise independent family of functions from `K` into `[2^ℓ]`
(`ℓ ≥ 2`) and `W ⊆ K` with `0 < |W| < 2^(ℓ-1)`. With probability at least `1/16` there is an
integer `j` such that exactly one `w ∈ W` hashes to a value in `[2^j]`. -/
theorem lemma4 [Nonempty Ω] {ℓ : ℕ} (hp : IsPairwiseIndep (2 ^ ℓ) K h) {W : Finset U}
    (hW : W ⊆ K) (hW0 : 0 < #W) (hWℓ : 2 * #W < 2 ^ ℓ) :
    1 / 16 ≤ uprob (fun ω => ∃ j, #(W.filter fun w => h ω w < 2 ^ j) = 1) := by
  obtain ⟨j, -, -, hj⟩ := lemma4_strong hp hW hW0 hWℓ
  refine le_trans (by linarith) (le_trans hj (uprob_mono fun ω hω => ⟨j, hω⟩))

end Podc.MSTImpromptuRepair
