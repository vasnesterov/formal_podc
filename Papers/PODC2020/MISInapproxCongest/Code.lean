import Podc.Foundations.InformationTheory.Agreement
import Podc.Foundations.InformationTheory.MDSCode

/-!
# Large-distance codes (Section 2.2 of Efron–Grossman–Khoury)

* `theorem4`: **Theorem 4** for a prime alphabet size `q`: for `L ≤ M ≤ q` there is a code-mapping
  `(ZMod q)^L → (ZMod q)^M` with pairwise distance `≥ M - L` (Reed–Solomon; in fact `≥ M - L + 1`).
* `rsCode`: the Reed–Solomon code used in Section 4, with messages `Fin α → ZMod q` and `q`
  positions, pairwise agreement `≤ α - 1`.
-/

namespace Podc.MISInapproxCongest

open Cslib Finset

open Polynomial in
/-- The message polynomial `∑ i, m i X^i` (degree `< L`). -/
noncomputable def rsPoly {q L : ℕ} (m : Fin L → ZMod q) : (ZMod q)[X] :=
  ∑ i : Fin L, C (m i) * X ^ (i : ℕ)

theorem rsPoly_coeff {q L : ℕ} (m : Fin L → ZMod q) (i : Fin L) :
    (rsPoly m).coeff i = m i := by
  simp [rsPoly, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Fin.val_inj]

/-- The Reed–Solomon code over `ZMod q` (`q` prime) with messages `Fin L → ZMod q` (coefficients
of a polynomial of degree `< L`) and the `M` evaluation points `0, …, M-1` (`M ≤ q`). -/
noncomputable def rsCode (q L M : ℕ) [Fact q.Prime] (_hM : M ≤ q) :
    (Fin L → ZMod q) → Fin M → ZMod q :=
  fun m j => (rsPoly m).eval ((j : ℕ) : ZMod q)

/-- Two distinct Reed–Solomon codewords agree in at most `L - 1` positions. -/
theorem rsCode_agree (q L M : ℕ) [Fact q.Prime] (hM : M ≤ q) {m m' : Fin L → ZMod q}
    (h : m ≠ m') : agree (rsCode q L M hM m) (rsCode q L M hM m') ≤ L - 1 := by
  by_contra hlt
  rw [not_le] at hlt
  let A := univ.filter fun j : Fin M => rsCode q L M hM m j = rsCode q L M hM m' j
  have hA : L ≤ A.card := by
    have : agree (rsCode q L M hM m) (rsCode q L M hM m') = A.card := rfl
    omega
  have hinj : Set.InjOn (fun j : Fin M => ((j : ℕ) : ZMod q)) A := by
    intro i _ j _ hij
    have := (ZMod.natCast_eq_natCast_iff' i j q).mp hij
    rw [Nat.mod_eq_of_lt (i.2.trans_le hM), Nat.mod_eq_of_lt (j.2.trans_le hM)] at this
    exact Fin.ext this
  have hpoly : rsPoly m = rsPoly m' := by
    apply Polynomial.eq_of_degree_sub_lt_of_eval_finset_eq
      (A.image fun j : Fin M => ((j : ℕ) : ZMod q))
    · rw [card_image_of_injOn hinj]
      calc (rsPoly m - rsPoly m').degree ≤ max (rsPoly m).degree (rsPoly m').degree :=
            Polynomial.degree_sub_le _ _
        _ < L := max_lt (Polynomial.degree_sum_fin_lt m) (Polynomial.degree_sum_fin_lt m')
        _ ≤ A.card := by exact_mod_cast hA
    · intro x hx
      obtain ⟨j, hj, rfl⟩ := mem_image.mp hx
      exact (mem_filter.mp hj).2
  apply h
  funext i
  rw [← rsPoly_coeff m i, ← rsPoly_coeff m' i, hpoly]

/-- **Theorem 4** (for a prime alphabet size `q`): for `L ≤ M ≤ q` there is a code-mapping
`C : Σ^L → Σ^M`, `Σ = ZMod q`, with `d(C x, C y) ≥ M - L` for all `x ≠ y`. -/
theorem theorem4 (q L M : ℕ) [Fact q.Prime] (hLM : L ≤ M) (hM : M ≤ q) :
    ∃ C : (Fin L → ZMod q) → Fin M → ZMod q, ∀ x y, x ≠ y → M - L ≤ hammingDist (C x) (C y) := by
  refine ⟨rsCode q L M hM, fun x y hxy => ?_⟩
  have h1 := rsCode_agree q L M hM hxy
  have h2 := agree_eq_card_sub_hammingDist (rsCode q L M hM x) (rsCode q L M hM y)
  have h3 := hammingDist_le_card_fintype (x := rsCode q L M hM x) (y := rsCode q L M hM y)
  rw [Fintype.card_fin] at h2 h3
  omega

end Podc.MISInapproxCongest
