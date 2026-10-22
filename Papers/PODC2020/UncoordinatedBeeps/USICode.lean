import Papers.PODC2020.UncoordinatedBeeps.Words
import Mathlib.Tactic.Ring

/-!
# Uncoordinated superimposed codes (Section 3.1 of the paper)

Dufoulon, Burman, Beauquier. *Can Uncoordinated Beeps tell Stories?* PODC 2020.

* `IsUSI₂ C k` — the `k`-cover-free property of Definition 2 (extended shifted codewords).
* `IsUSI₃ C k` — the property of Definition 3 (shifted codewords, decoding of the codeword starting
  at shift `0`).
* `IsUSICode C h k` / `IsUSICode' C h k` — a `USI(h, k)`-code according to Definition 2 / 3.
* `theorem_1` — Definitions 2 and 3 are equivalent (for codeword length `l ≥ 1`).

A "set of codeword and shift pairs" is a `Finset (Word l × ℤ)`; pairs are compared as pairs, so
`(c, t) ∉ X` means "the pair `(c, t)` is not in `X`", which is how the paper's proofs use it.
-/

namespace Podc.UncoordinatedBeeps

open Word

variable {l : ℕ}

/-- Admissible sets of codeword–shift pairs for a code `C`: codewords from `C`, shifts in
`{-l+1, …, l-1}`. -/
def Admissible (C : Finset (Word l)) (X : Finset (Word l × ℤ)) : Prop :=
  ∀ p ∈ X, p.1 ∈ C ∧ InShiftRange l p.2

/-- The cover-free property of **Definition 2**: no extended uncoordinated superposition of at most
`k` admissible codeword–shift pairs `X` contains an extended shifted codeword `σ̄(c', t)` with
`(c', t) ∉ X`. -/
def IsUSI₂ (C : Finset (Word l)) (k : ℕ) : Prop :=
  ∀ X : Finset (Word l × ℤ), X.card ≤ k → Admissible C X →
    ∀ c ∈ C, ∀ t, InShiftRange l t → (c, t) ∉ X →
      ¬ (superpose X fun p => extShift p.1 p.2).Contains (extShift c t)

/-- The decoding property of **Definition 3**: the uncoordinated superposition of at most `k`
admissible codeword–shift pairs `X` contains `σ(c', 0)` (i.e. `c'`) iff `(c', 0) ∈ X`. -/
def IsUSI₃ (C : Finset (Word l)) (k : ℕ) : Prop :=
  ∀ X : Finset (Word l × ℤ), X.card ≤ k → Admissible C X →
    ∀ c ∈ C, ((superpose X fun p => shift p.1 p.2).Contains (shift c 0) ↔ (c, 0) ∈ X)

/-- **Definition 2.** `C` is an `(h, k)`-uncoordinated superimposed code (`USI(h, k)`-code) of
length `l`: a set of `h` codewords of length `l` with the property `IsUSI₂`. -/
def IsUSICode (C : Finset (Word l)) (h k : ℕ) : Prop := C.card = h ∧ IsUSI₂ C k

/-- **Definition 3.** `C` is a `USI(h, k)`-code of length `l` in the sense of Definition 3. -/
def IsUSICode' (C : Finset (Word l)) (h k : ℕ) : Prop := C.card = h ∧ IsUSI₃ C k

/-- A non-empty code with the property of Definition 3 has positive length. -/
theorem IsUSI₃.length_pos {C : Finset (Word l)} {k : ℕ} (hC : IsUSI₃ C k) {c : Word l}
    (hc : c ∈ C) : 0 < l := by
  rcases Nat.eq_zero_or_pos l with rfl | h
  · have := (hC ∅ (by simp) (by simp [Admissible]) c hc).1 (fun i => i.elim0)
    simp at this
  · exact h

theorem isUSI₃_of_isUSI₂ {C : Finset (Word l)} {k : ℕ} (hl : 0 < l) (hC : IsUSI₂ C k) :
    IsUSI₃ C k := by
  intro X hX hXC c hc
  constructor
  · intro hcont
    by_contra hn
    refine hC X hX hXC c hc 0 ⟨by omega, by omega⟩ hn ?_
    intro j hj
    have hb := getZ_eq_true_bounds hj
    -- the position `j` of the extended word is position `i = j - (l - 1)` of the window
    let i : Fin l := ⟨((j : ℕ) - ((l : ℤ) - 1 + 0)).toNat, by omega⟩
    have hi : (i : ℕ) = ((j : ℕ) : ℤ) - ((l : ℤ) - 1 + 0) := by simp only [i]; omega
    have hci : shift c 0 i = true := by
      simp only [shift_zero]
      rw [← getZ_natCast c i, hi]; exact hj
    obtain ⟨p, hp, hpi⟩ := superpose_eq_true.1 (hcont i hci)
    refine superpose_eq_true.2 ⟨p, hp, ?_⟩
    simp only [shift, extShift] at hpi ⊢
    rw [hi] at hpi
    convert hpi using 2; ring
  · intro hmem i hi
    exact superpose_eq_true.2 ⟨(c, 0), hmem, hi⟩

theorem isUSI₂_of_isUSI₃ {C : Finset (Word l)} {k : ℕ} (hC : IsUSI₃ C k) : IsUSI₂ C k := by
  classical
  intro X hX hXC c hc t ht hcX hcont
  -- shift everything by `-t`, dropping the pairs that no longer meet the window
  set X' : Finset (Word l × ℤ) :=
    (X.filter fun p => InShiftRange l (p.2 - t)).image fun p => (p.1, p.2 - t) with hX'
  have hcard : X'.card ≤ k :=
    Finset.card_image_le.trans ((Finset.card_filter_le _ _).trans hX)
  have hadm : Admissible C X' := by
    intro p hp
    simp only [hX', Finset.mem_image, Finset.mem_filter] at hp
    obtain ⟨q, ⟨hq, hqr⟩, rfl⟩ := hp
    exact ⟨(hXC q hq).1, hqr⟩
  have hcov : (superpose X' fun p => shift p.1 p.2).Contains (shift c 0) := by
    intro i hi
    simp only [shift_zero] at hi
    obtain ⟨ht1, ht2⟩ := ht
    have hiL := i.isLt
    let j : Fin (3 * l - 2) := ⟨(i : ℕ) + ((l : ℤ) - 1 + t).toNat, by omega⟩
    have hj : ((j : ℕ) : ℤ) = (i : ℕ) + ((l : ℤ) - 1 + t) := by simp only [j]; omega
    have hcj : extShift c t j = true := by
      simp only [extShift]; rw [hj, add_sub_cancel_right, getZ_natCast]; exact hi
    obtain ⟨p, hp, hpj⟩ := superpose_eq_true.1 (hcont j hcj)
    simp only [extShift] at hpj
    rw [hj] at hpj
    have hb := getZ_eq_true_bounds hpj
    refine superpose_eq_true.2 ⟨(p.1, p.2 - t), ?_, ?_⟩
    · simp only [hX', Finset.mem_image, Finset.mem_filter]
      exact ⟨p, ⟨hp, by constructor <;> omega⟩, rfl⟩
    · simp only [shift]
      convert hpj using 2; ring
  have := (hC X' hcard hadm c hc).1 hcov
  simp only [hX', Finset.mem_image, Finset.mem_filter, Prod.mk.injEq] at this
  obtain ⟨p, ⟨hp, -⟩, h1, h2⟩ := this
  apply hcX
  have : p = (c, t) := Prod.ext h1 (by omega)
  exact this ▸ hp

/-- **Theorem 1.** Definitions 2 and 3 of `USI(h, k)`-codes are equivalent (for codewords of length
`l ≥ 1`; for `l = 0` Definition 2 is vacuous, see `theorem_1_length_zero`). -/
theorem theorem_1 {C : Finset (Word l)} {h k : ℕ} (hl : 0 < l) :
    IsUSICode C h k ↔ IsUSICode' C h k :=
  ⟨fun H => ⟨H.1, isUSI₃_of_isUSI₂ hl H.2⟩, fun H => ⟨H.1, isUSI₂_of_isUSI₃ H.2⟩⟩

/-- The hypothesis `l ≥ 1` of `theorem_1` is needed: for length `0` the single (empty) codeword
forms a `USI(1, 0)`-code by Definition 2 (no shift is admissible) but not by Definition 3. -/
theorem theorem_1_length_zero :
    IsUSICode ({fun i => i.elim0} : Finset (Word 0)) 1 0 ∧
      ¬ IsUSICode' ({fun i => i.elim0} : Finset (Word 0)) 1 0 := by
  refine ⟨⟨rfl, ?_⟩, ?_⟩
  · intro X _ _ c _ t ht
    exact absurd ht (by simp [InShiftRange]; omega)
  · rintro ⟨-, H⟩
    have := (H ∅ (by simp) (by simp [Admissible]) _ (Finset.mem_singleton_self _)).1
      (fun i => i.elim0)
    simp at this

end Podc.UncoordinatedBeeps
