import Mathlib.LinearAlgebra.Lagrange

-- CSLib candidate: Cslib/Foundations/InformationTheory/MDSCode.lean

/-!
# Codes with the MDS property; Reed–Solomon codes

An `(n, k)` code with data `α` and symbols `β` is an encoding `enc : α → Fin n → β`. It has the
*MDS property* ("dimension `k`", "maximum distance separable" for linear codes) if any `k` symbols of
a codeword determine the data. Coded protocols (error-free multi-valued Byzantine agreement,
coded storage, AVID, …) use codes only through this property, so we keep the code abstract and give
the Reed–Solomon code as an instance.

## Main definitions

* `Cslib.MDSCode n k α β`: an encoding with the MDS property.
* `Cslib.MDSCode.Consistent C A V` (`V/A ∈ C`): some codeword agrees with `V` on the positions `A`.
* `Cslib.MDSCode.decode C d A V` (`C⁻¹(V/A)`): the data of such a codeword, or the default `d`.
* `Cslib.MDSCode.reedSolomon n k pts`: the Reed–Solomon code over a field with distinct
  evaluation points `pts` (polynomials of degree `< k`, Lagrange interpolation).

## Main statements

* `Cslib.MDSCode.decode_eq`: decoding a vector agreeing with the codeword of `x` on `≥ k`
  positions gives `x`.
* `Cslib.MDSCode.agree_of_consistent`: if `V/A ∈ C` and `V` agrees with the codeword of `x` on
  `B ⊆ A` with `k ≤ |B|`, then it agrees with it on all of `A`.

## Implementation notes

Mathlib has Hamming distance (`Mathlib.InformationTheory.Hamming`) but no notion of code; the MDS
property is stated combinatorially (no linearity), which is all that the distributed-computing uses
need.
-/

namespace Cslib

/-- An `(n, k)` code with data `α` and symbols `β` in which any `k` positions of a codeword
determine the data (the MDS / "dimension `k`" property). -/
structure MDSCode (n k : ℕ) (α β : Type*) where
  /-- The encoding function `C(·)`; `enc x i` is the `i`-th symbol of the codeword of `x`. -/
  enc : α → Fin n → β
  /-- Two codewords agreeing on `k` positions encode the same data. -/
  eq_of_agree : ∀ A : Finset (Fin n), k ≤ A.card → ∀ x y : α,
    (∀ i ∈ A, enc x i = enc y i) → x = y

namespace MDSCode

variable {n k : ℕ} {α β : Type*} (C : MDSCode n k α β)

/-- `V/A ∈ C`: some codeword agrees with `V` at the positions in `A`. -/
def Consistent (A : Finset (Fin n)) (V : Fin n → β) : Prop :=
  ∃ x, ∀ i ∈ A, C.enc x i = V i

open Classical in
/-- `C⁻¹(V/A)`: the data of a codeword agreeing with `V` on `A` (unique if `k ≤ |A|`), or the
default `d` if no codeword agrees with `V` on `A`. -/
noncomputable def decode (d : α) (A : Finset (Fin n)) (V : Fin n → β) : α :=
  if h : C.Consistent A V then h.choose else d

/-- Decoding a vector that agrees on `A` (with `k ≤ |A|`) with the codeword of `x` gives `x`. -/
theorem decode_eq {d x : α} {A : Finset (Fin n)} {V : Fin n → β} (hA : k ≤ A.card)
    (hx : ∀ i ∈ A, C.enc x i = V i) : C.decode d A V = x := by
  have h : C.Consistent A V := ⟨x, hx⟩
  simp only [decode, h, dite_true]
  exact C.eq_of_agree A hA _ _ fun i hi => (h.choose_spec i hi).trans (hx i hi).symm

/-- Consistency on a set implies consistency on every subset. -/
theorem Consistent.mono {A B : Finset (Fin n)} {V : Fin n → β} (h : C.Consistent B V)
    (hAB : A ⊆ B) : C.Consistent A V :=
  let ⟨x, hx⟩ := h; ⟨x, fun i hi => hx i (hAB hi)⟩

/-- If `V` agrees with the codeword of `x` on `B` (with `k ≤ |B|`) and `V/A ∈ C` for some
`A ⊇ B`, then `V` agrees with the codeword of `x` on all of `A`. -/
theorem agree_of_consistent {x : α} {A B : Finset (Fin n)} {V : Fin n → β}
    (h : C.Consistent A V) (hBA : B ⊆ A) (hB : k ≤ B.card) (hx : ∀ i ∈ B, C.enc x i = V i) :
    ∀ i ∈ A, C.enc x i = V i := by
  obtain ⟨y, hy⟩ := h
  have : y = x := C.eq_of_agree B hB _ _ fun i hi => (hy i (hBA hi)).trans (hx i hi).symm
  subst this
  exact hy

/-- The encoding is injective (as soon as `k ≤ n`). -/
theorem enc_injective (hk : k ≤ n) : Function.Injective C.enc := fun x y h =>
  C.eq_of_agree Finset.univ (by simpa using hk) x y fun i _ => congrFun h i

end MDSCode

/-! ### Reed–Solomon codes -/

open Polynomial in
/-- The `(n, k)` **Reed–Solomon code** over a field `K` with pairwise distinct evaluation points
`pts : Fin n ↪ K`: the data are the polynomials of degree `< k`, the `i`-th symbol is the value at
`pts i`. Any `k` values determine the polynomial (Lagrange interpolation), so it is an MDS code. -/
noncomputable def MDSCode.reedSolomon {K : Type*} [Field K] (n k : ℕ) (pts : Fin n ↪ K) :
    MDSCode n k (degreeLT K k) K where
  enc p i := (p : K[X]).eval (pts i)
  eq_of_agree A hA p q h := by
    apply Subtype.ext
    apply Polynomial.eq_of_degree_sub_lt_of_eval_finset_eq (A.map pts)
    · have hp := Polynomial.mem_degreeLT.mp p.2
      have hq := Polynomial.mem_degreeLT.mp q.2
      calc (p.1 - q.1).degree ≤ max p.1.degree q.1.degree := degree_sub_le _ _
        _ < k := max_lt hp hq
        _ ≤ (A.map pts).card := by simpa using hA
    · intro x hx
      obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hx
      exact h i hi

end Cslib
