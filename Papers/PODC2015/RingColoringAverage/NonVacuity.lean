import Papers.PODC2015.RingColoringAverage.Model

/-!
# Non-vacuity: a valid 3-colouring algorithm exists

Theorem 1 of [Feuilloley, PODC 2015] quantifies over valid 3-colouring algorithms
(`Alg.Valid` with colours `Fin 3`). We exhibit one, so the hypothesis is satisfiable.

The algorithm `seeAll` ("see the whole ring"): at radius `r` with view `f`, a node stops as soon
as it sees its own identifier again, i.e. `f p = f 0` for some `1 ≤ p ≤ r`. Then the least such
`p` is the ring size `n` (`period`), and the node knows the whole ring. Let `i ∈ [0, n)` be the
offset with `f (-i)` minimal among `f (-j)`, `j < n` (`minOffset`): the node is `i` steps to the
right of the node with the smallest identifier. It outputs `i % 2`, except for `i = n - 1` with
`n` odd, where it outputs `2` (`colourOf`). Going right, offsets increase by one modulo `n`,
which makes the colouring proper. Everything only reads the view on `[-r, r]` since `n ≤ r`.
-/

namespace Podc.RingColoringAverage

namespace NonVacuity

/-- The least `p ≥ 1` with `f p = f 0` (on a ring view, the ring size). -/
noncomputable def period (f : ℤ → ℕ) : ℕ := sInf {p : ℕ | 1 ≤ p ∧ f p = f 0}

/-- The offset `i < n` such that `f (-i)` is minimal among `f (-j)`, `j < n`. -/
noncomputable def minOffset (n : ℕ) (f : ℤ → ℕ) : ℕ :=
  sInf {i : ℕ | i < n ∧ ∀ j < n, f (-(i : ℤ)) ≤ f (-(j : ℤ))}

/-- Colour of the node at offset `i` from the minimum on a ring of size `n`. -/
def colourOf (n i : ℕ) : Fin 3 :=
  if i + 1 = n ∧ n % 2 = 1 then 2 else if i % 2 = 0 then 0 else 1

theorem colourOf_ne_succ {n i : ℕ} (hi : i + 1 < n) : colourOf n i ≠ colourOf n (i + 1) := by
  unfold colourOf
  split_ifs <;> first | decide | omega

theorem colourOf_ne_zero {n : ℕ} (hn : 3 ≤ n) : colourOf n (n - 1) ≠ colourOf n 0 := by
  unfold colourOf
  split_ifs <;> first | decide | omega

open Classical in
/-- The "see the whole ring" 3-colouring algorithm. -/
noncomputable def seeAll : Alg (Fin 3) where
  out r f := if ∃ p : ℕ, 1 ≤ p ∧ p ≤ r ∧ f p = f 0 then
      some (colourOf (period f) (minOffset (period f) f)) else none
  out_congr r f g h := by
    have h0 : f 0 = g 0 := h 0 (by simp)
    have hiff : (∃ p : ℕ, 1 ≤ p ∧ p ≤ r ∧ f p = f 0) ↔ ∃ p : ℕ, 1 ≤ p ∧ p ≤ r ∧ g p = g 0 := by
      constructor
      · rintro ⟨p, h1, h2, h3⟩
        exact ⟨p, h1, h2, by rw [← h p (by rw [abs_le]; omega), ← h0, h3]⟩
      · rintro ⟨p, h1, h2, h3⟩
        exact ⟨p, h1, h2, by rw [h p (by rw [abs_le]; omega), h0, h3]⟩
    by_cases hf : ∃ p : ℕ, 1 ≤ p ∧ p ≤ r ∧ f p = f 0
    · have hg := hiff.1 hf
      simp only [hf, hg, ↓reduceIte]
      -- the periods agree and are at most `r`
      have key : ∀ (f g : ℤ → ℕ), AgreeOn r f g → (∃ p : ℕ, 1 ≤ p ∧ p ≤ r ∧ f p = f 0) →
          period g ≤ period f ∧ period f ≤ r := by
        intro f g h ⟨p, h1, h2, h3⟩
        have hmem : period f ∈ {p : ℕ | 1 ≤ p ∧ f p = f 0} := Nat.sInf_mem ⟨p, h1, h3⟩
        have hle : period f ≤ r := (Nat.sInf_le (⟨h1, h3⟩ : p ∈ {p : ℕ | 1 ≤ p ∧ f p = f 0})).trans h2
        refine ⟨Nat.sInf_le ⟨hmem.1, ?_⟩, hle⟩
        rw [← h _ (by rw [abs_le]; omega), ← h 0 (by simp), hmem.2]
      have e1 := key f g h hf
      have e2 := key g f h.symm hg
      have hp : period f = period g := le_antisymm e2.1 e1.1
      rw [← hp]
      congr 2
      unfold minOffset
      congr 1
      ext i
      simp only [Set.mem_ofPred_eq]
      constructor
      · rintro ⟨hi, hj⟩
        refine ⟨hi, fun j hj' => ?_⟩
        rw [← h _ (by rw [abs_le]; omega), ← h _ (by rw [abs_le]; omega)]
        exact hj j hj'
      · rintro ⟨hi, hj⟩
        refine ⟨hi, fun j hj' => ?_⟩
        rw [h _ (by rw [abs_le]; omega), h _ (by rw [abs_le]; omega)]
        exact hj j hj'
    · have hg : ¬ ∃ p : ℕ, 1 ≤ p ∧ p ≤ r ∧ g p = g 0 := fun hg => hf (hiff.2 hg)
      simp only [hf, hg, ↓reduceIte]

theorem seeAll_stops (R : IdRing) (v : ℤ) : seeAll.Stops (R.view v) := by
  refine ⟨R.n, ?_⟩
  have : ∃ p : ℕ, 1 ≤ p ∧ p ≤ R.n ∧ R.view v p = R.view v 0 :=
    ⟨R.n, by have := R.three_le; omega, le_rfl, by simpa using R.id_add_mul v 1⟩
  simp only [seeAll]
  simp only [this, ↓reduceIte, Option.isSome_some]

theorem seeAll_output (R : IdRing) (v : ℤ) :
    seeAll.outAt R v = colourOf (period (R.view v)) (minOffset (period (R.view v)) (R.view v)) := by
  have hs := Alg.rad_spec (seeAll_stops R v)
  unfold Alg.outAt Alg.output
  revert hs
  generalize seeAll.rad (R.view v) = r
  unfold seeAll
  dsimp only
  split_ifs <;> simp

theorem period_view (R : IdRing) (v : ℤ) : period (R.view v) = R.n := by
  have hn := R.three_le
  have hmem : R.n ∈ {p : ℕ | 1 ≤ p ∧ R.view v p = R.view v 0} :=
    ⟨by omega, by simpa using R.id_add_mul v 1⟩
  refine le_antisymm (Nat.sInf_le hmem) (le_csInf ⟨_, hmem⟩ fun p ⟨hp1, hp2⟩ => ?_)
  simp only [IdRing.view_apply, add_zero] at hp2
  obtain ⟨m, hm⟩ := R.id_eq_iff.1 hp2
  have : (p : ℤ) = R.n * m := by linarith
  have hm1 : 1 ≤ m := by
    by_contra hc
    have : (R.n : ℤ) * m ≤ 0 := Int.mul_nonpos_of_nonneg_of_nonpos (by positivity) (by omega)
    omega
  have : (R.n : ℤ) ≤ p := by rw [this]; nlinarith
  exact_mod_cast this

/-- Characterisation of `minOffset` on ring views: the offset of the global minimum. -/
theorem minOffset_view (R : IdRing) (v : ℤ) (i : ℕ) (hi : i < R.n)
    (hmin : ∀ w, R.id (v - i) ≤ R.id w) : minOffset R.n (R.view v) = i := by
  set S := {i : ℕ | i < R.n ∧ ∀ j < R.n, R.view v (-(i : ℤ)) ≤ R.view v (-(j : ℤ))}
  show sInf S = i
  have hiS : i ∈ S := ⟨hi, fun j _ => by simpa [sub_eq_add_neg] using hmin _⟩
  have hmem : sInf S ∈ S := Nat.sInf_mem ⟨i, hiS⟩
  obtain ⟨hk, hkmin⟩ := hmem
  have h1 := hkmin i hi
  have h2 := hiS.2 _ hk
  simp only [IdRing.view_apply] at h1 h2
  have he : R.id (v + -((sInf S : ℕ) : ℤ)) = R.id (v + -(i : ℤ)) := le_antisymm h1 h2
  by_contra hne
  exact R.id_ne_of_lt (by omega) (by rw [abs_lt]; omega) he

theorem exists_minOffset (R : IdRing) (v : ℤ) :
    ∃ i < R.n, ∀ w, R.id (v - i) ≤ R.id w := by
  have hn : (0 : ℤ) < R.n := by exact_mod_cast R.n_pos
  set m := Function.argmin R.id
  have h0 := Int.emod_nonneg (v - m) hn.ne'
  have h1 := Int.emod_lt_of_pos (v - m) hn
  refine ⟨((v - m) % R.n).toNat, by omega, fun w => ?_⟩
  have : R.id (v - ((v - m) % R.n).toNat) = R.id m := by
    rw [R.id_eq_iff, Int.toNat_of_nonneg (Int.emod_nonneg _ hn.ne')]
    have := Int.emod_add_mul_ediv (v - m) R.n
    exact ⟨(v - m) / R.n, by linarith⟩
  rw [this]
  exact Function.argmin_le R.id w

/-- **Non-vacuity of Theorem 1**: there is a valid 3-colouring algorithm on rings. -/
theorem seeAll_valid : seeAll.Valid where
  stops := seeAll_stops
  proper R v := by
    rw [seeAll_output, seeAll_output, period_view, period_view]
    obtain ⟨i, hi, hmin⟩ := exists_minOffset R v
    rw [minOffset_view R v i hi hmin]
    by_cases hi1 : i + 1 < R.n
    · rw [minOffset_view R (v + 1) (i + 1) hi1 (by push_cast; simpa [add_sub_add_right_eq_sub] using hmin)]
      exact colourOf_ne_succ hi1
    · have hi' : i = R.n - 1 := by omega
      rw [minOffset_view R (v + 1) 0 R.n_pos (fun w => ?_)]
      · rw [hi']; exact colourOf_ne_zero R.three_le
      · have : R.id (v + 1 - ((0 : ℕ) : ℤ)) = R.id (v - i) := by
          rw [R.id_eq_iff]; exact ⟨1, by push_cast; omega⟩
        rw [this]; exact hmin w

end NonVacuity

/-- **Non-vacuity of Theorem 1** of [Feuilloley, PODC 2015]: valid 3-colouring algorithms
(stopping everywhere, proper output) on rings of unknown size exist. -/
theorem exists_valid_three : ∃ A : Alg (Fin 3), A.Valid := ⟨_, NonVacuity.seeAll_valid⟩

end Podc.RingColoringAverage
