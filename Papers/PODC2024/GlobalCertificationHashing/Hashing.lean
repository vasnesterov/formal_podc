import Podc.Foundations.Combinatorics.PerfectHash

/-!
# Theorem 7 (perfect hash families) as used in the paper

* `theorem_7`: Theorem 7 with "size at most `⌈k e^k ln ℓ⌉`", for `1 ≤ k ≤ ℓ`, `2 ≤ ℓ`.
* `theorem_7_false_l_one`: the literal statement fails for `k = ℓ = 1` (the bound is `0`).
* `theorem_7_exact_size_false`: "has size exactly `⌈k e^k log ℓ⌉`" fails for `k = ℓ = 2`
  (there are only `4` functions), for both `log = ln` and `log = log₂`.
* `exists_hashList`: the form used by the certification scheme — functions `ℕ → ℕ`, at most
  `max 1 ⌈k e^k ln ℓ⌉` of them, for all `k ≤ ℓ`.
-/

open Finset Real

namespace Podc.GlobalCertificationHashing

/-- **Theorem 7** of [Bousquet–Feuilloley–Zeitoun, PODC 2024] (cited from Mehlhorn), in the
corrected form "at most": for `1 ≤ k ≤ ℓ` and `ℓ ≥ 2` there is a `(k, ℓ)`-perfect hash family
of at most `⌈k e^k ln ℓ⌉` functions (`Cslib.exists_isPerfectHashFamily_card_le_logb` gives the
same with `log₂ ℓ`). -/
theorem theorem_7 {k ℓ : ℕ} (hk : 1 ≤ k) (hkℓ : k ≤ ℓ) (hℓ : 2 ≤ ℓ) :
    ∃ H : Finset (Fin ℓ → Fin k), Cslib.IsPerfectHashFamily k ℓ H ∧
      H.card ≤ ⌈(k : ℝ) * exp k * log ℓ⌉₊ :=
  Cslib.exists_isPerfectHashFamily_card_le hk hkℓ hℓ

/-- Theorem 7 as stated (`k ≤ ℓ` only) fails for `k = ℓ = 1`: the claimed size is
`⌈1 · e · log 1⌉ = 0` (in any base), but the empty family is not `(1,1)`-perfect. -/
theorem theorem_7_false_l_one (b : ℝ) :
    ¬ ∃ H : Finset (Fin 1 → Fin 1), Cslib.IsPerfectHashFamily 1 1 H ∧
      H.card ≤ ⌈((1 : ℕ) : ℝ) * exp (1 : ℕ) * logb b (1 : ℕ)⌉₊ := by
  rintro ⟨H, hH, hc⟩
  simp only [Nat.cast_one, logb_one, mul_zero, Nat.ceil_zero, nonpos_iff_eq_zero,
    card_eq_zero] at hc
  subst hc
  obtain ⟨h, hh, -⟩ := hH univ (by simp)
  simp at hh

/-- Read literally ("has size `⌈k e^k log ℓ⌉`"), Theorem 7 fails for `k = ℓ = 2`: the claimed
size exceeds the number `2² = 4` of all functions `Fin 2 → Fin 2`; this holds both for
`log = ln` and for `log = log₂` (`b = e` or `b = 2`). -/
theorem theorem_7_exact_size_false (b : ℝ) (hb : b = exp 1 ∨ b = 2) :
    ¬ ∃ H : Finset (Fin 2 → Fin 2),
      H.card = ⌈((2 : ℕ) : ℝ) * exp (2 : ℕ) * logb b (2 : ℕ)⌉₊ := by
  rintro ⟨H, hc⟩
  have h4 : H.card ≤ 4 := by
    have := card_le_univ H
    simpa [Fintype.card_fun] using this
  have he : (2.7 : ℝ) < exp 1 := by have := exp_one_gt_d9; linarith
  have hlog : (0.69 : ℝ) ≤ logb b 2 := by
    rcases hb with rfl | rfl
    · rw [logb, log_exp, div_one]; have := log_two_gt_d9; linarith
    · rw [logb_self_eq_one one_lt_two]; norm_num
  have he2 : (7 : ℝ) < exp 2 := by
    have : exp 2 = exp 1 * exp 1 := by rw [← exp_add]; norm_num
    rw [this]; nlinarith
  have : ((4 : ℕ) : ℝ) < ((2 : ℕ) : ℝ) * exp ((2 : ℕ) : ℝ) * logb b ((2 : ℕ) : ℝ) := by
    norm_num; nlinarith
  have := Nat.lt_ceil.mpr this
  omega

/-- The hash family in the form used by the scheme: functions `ℕ → ℕ` such that every
`k`-subset of `{0, …, ℓ - 1}` is mapped injectively into `{0, …, k - 1}` by one of them; at most
`max 1 ⌈k e^k ln ℓ⌉` functions. (For `k > ℓ` the first property is vacuous.) -/
theorem exists_hashList (k ℓ : ℕ) : ∃ L : List (ℕ → ℕ),
    (k ≤ ℓ → ∀ S : Finset ℕ, (∀ x ∈ S, x < ℓ) → S.card = k →
      ∃ h ∈ L, Set.InjOn h S ∧ ∀ x ∈ S, h x < k) ∧
    L.length ≤ max 1 ⌈(k : ℝ) * exp k * log ℓ⌉₊ := by
  classical
  by_cases hsmall : k = 0 ∨ ℓ ≤ k
  · -- `k = 0` (only `S = ∅`) or `k = ℓ` (only `S = range ℓ`, and `id` works)
    refine ⟨[id], fun hkℓ S hS hc => ⟨id, List.mem_singleton_self _, Function.injective_id.injOn,
      fun x hx => ?_⟩, by simp⟩
    rcases hsmall with rfl | h
    · simp at hc; subst hc; simp at hx
    · exact (hS x hx).trans_le h
  push Not at hsmall
  obtain ⟨hk0, hkl⟩ := hsmall
  obtain ⟨H, hH, hc⟩ := theorem_7 (k := k) (ℓ := ℓ) (by omega) hkl.le (by omega)
  let lift : (Fin ℓ → Fin k) → ℕ → ℕ := fun f x => if hx : x < ℓ then (f ⟨x, hx⟩ : ℕ) else 0
  refine ⟨H.toList.map lift, fun _ S hS hcard => ?_, ?_⟩
  · let S' : Finset (Fin ℓ) := univ.filter fun i => (i : ℕ) ∈ S
    have hmap : S'.map Fin.valEmbedding = S := by
      ext x
      simp only [S', mem_map, mem_filter, mem_univ, true_and, Fin.valEmbedding_apply]
      exact ⟨fun ⟨i, hi, he⟩ => he ▸ hi, fun hx => ⟨⟨x, hS x hx⟩, hx, rfl⟩⟩
    have hS' : S'.card = k := by rw [← card_map Fin.valEmbedding, hmap, hcard]
    obtain ⟨f, hf, hinj⟩ := hH S' hS'
    refine ⟨lift f, List.mem_map.mpr ⟨f, mem_toList.mpr hf, rfl⟩, ?_, ?_⟩
    · intro x hx y hy hxy
      simp only [Finset.mem_coe] at hx hy
      simp only [lift, dite_eq_left (hS x hx), dite_eq_left (hS y hy)] at hxy
      have := hinj (by simp [S', hx] : (⟨x, hS x hx⟩ : Fin ℓ) ∈ S')
        (by simp [S', hy] : (⟨y, hS y hy⟩ : Fin ℓ) ∈ S') (Fin.ext hxy)
      simpa using this
    · intro x hx
      simp only [lift, dite_eq_left (hS x hx)]
      exact (f _).isLt
  · simp only [List.length_map, length_toList]
    exact hc.trans (le_max_right _ _)

end Podc.GlobalCertificationHashing
