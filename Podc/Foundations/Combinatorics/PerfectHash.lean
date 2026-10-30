import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Nat.Choose.Bounds

-- CSLib candidate: Cslib/Foundations/Combinatorics/PerfectHash.lean

/-!
# Perfect hash families

A function `h : Fin ℓ → Fin k` is *perfect* for `S ⊆ Fin ℓ` if it is injective on `S`. A family
`H` of such functions is a `(k, ℓ)`-*perfect hash family* if every `k`-element subset `S ⊆ Fin ℓ`
has a perfect function in `H`.

The classical counting (probabilistic) argument of Fredman–Komlós and Mehlhorn shows that for
`1 ≤ k ≤ ℓ`, `2 ≤ ℓ` there is a `(k, ℓ)`-perfect hash family with at most `⌈k e^k ln ℓ⌉` functions:
a uniformly random function is perfect for a fixed `S` with probability `k!/k^k ≥ e^{-k}`, so
`t = ⌈k e^k ln ℓ⌉` independent random functions all fail on `S` with probability
`(1 - k!/k^k)^t < e^{-k ln ℓ} = ℓ^{-k}`; a union bound over the `≤ ℓ^k` sets `S` concludes. We phrase
it as double counting of `t`-tuples of functions.

## Main statements

* `Cslib.IsPerfectHashFamily`: the definition.
* `Cslib.exists_isPerfectHashFamily_card_le`: existence of a family of size `≤ ⌈k e^k ln ℓ⌉`.
* `Cslib.exists_isPerfectHashFamily_card_le_logb`: the same with `log₂ ℓ`.
* `Cslib.isPerfectHashFamily_univ_id`: for `k = ℓ` a single function suffices.
-/

open Finset Real
open scoped Nat

namespace Cslib

variable {k ℓ : ℕ}

/-- `H` is a `(k, ℓ)`-perfect hash family: every `k`-element subset of `Fin ℓ` has a function in
`H` which is injective on it. -/
def IsPerfectHashFamily (k ℓ : ℕ) (H : Finset (Fin ℓ → Fin k)) : Prop :=
  ∀ S : Finset (Fin ℓ), S.card = k → ∃ h ∈ H, Set.InjOn h S

namespace PerfectHash

/-- At least `k! * k ^ (ℓ - k)` functions `Fin ℓ → Fin k` are injective on a given `k`-set. -/
theorem card_injOn_ge (S : Finset (Fin ℓ)) (hS : S.card = k) :
    k ! * k ^ (ℓ - k) ≤ (univ.filter fun h : Fin ℓ → Fin k => Set.InjOn h S).card := by
  classical
  have hcS : Fintype.card S = k := by simp [hS]
  let e0 : S ≃ Fin k := Fintype.equivFinOfCardEq hcS
  let F : (S ≃ Fin k) × ({x // x ∉ S} → Fin k) → {h : Fin ℓ → Fin k // Set.InjOn h S} :=
    fun p => ⟨fun x => if hx : x ∈ S then p.1 ⟨x, hx⟩ else p.2 ⟨x, hx⟩, by
      intro x hx y hy hxy
      simp only [Finset.mem_coe] at hx hy
      simp only [hx, hy, dite_true] at hxy
      simpa using p.1.injective hxy⟩
  have hF : Function.Injective F := by
    rintro ⟨e, g⟩ ⟨e', g'⟩ h
    simp only [F, Subtype.mk.injEq] at h
    have h1 : e = e' := by
      ext ⟨x, hx⟩
      have := congrFun h x
      simp only [hx, dite_true] at this
      rw [this]
    have h2 : g = g' := by
      funext ⟨x, hx⟩
      have := congrFun h x
      simp only [hx, dite_false] at this
      exact this
    rw [h1, h2]
  have := Fintype.card_le_of_injective F hF
  rw [Fintype.card_prod, Fintype.card_equiv e0, Fintype.card_fun, Fintype.card_fin,
    Fintype.card_subtype_compl, Fintype.card_fin, hcS, Fintype.card_subtype] at this
  exact this

/-- `k ^ k / k! ≤ e ^ k`, i.e. a random function is perfect for a `k`-set with probability
`≥ e^{-k}`. -/
theorem exp_neg_le_factorial_div (k : ℕ) : exp (-k) ≤ (k ! : ℝ) / (k : ℝ) ^ k := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  have h := pow_div_factorial_le_exp (x := (k : ℝ)) (by positivity) k
  have hf : (0 : ℝ) < k ! := by exact_mod_cast Nat.factorial_pos k
  have hp : (0 : ℝ) < (k : ℝ) ^ k := by positivity
  rw [exp_neg, inv_le_iff_one_le_mul₀ (exp_pos _)]
  rw [div_le_iff₀ hf] at h
  rw [div_mul_eq_mul_div, le_div_iff₀ hp, one_mul]
  linarith [mul_comm (exp (k : ℝ)) (k ! : ℝ)]

/-- The analytic core of the union bound: `C(ℓ,k) · b ^ t < N ^ t` whenever `b / N ≤ 1 - k!/k^k`
and `t ≥ k e^k ln ℓ`. -/
theorem union_bound_lt (hk : 1 ≤ k) (hℓ : 2 ≤ ℓ) (N b t : ℕ) (hN : 0 < N)
    (hb : (b : ℝ) ≤ N * (1 - (k ! : ℝ) / (k : ℝ) ^ k))
    (ht : (k : ℝ) * exp k * log ℓ ≤ t) :
    (ℓ.choose k : ℝ) * (b : ℝ) ^ t < (N : ℝ) ^ t := by
  set p : ℝ := (k ! : ℝ) / (k : ℝ) ^ k with hp_def
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hp0 : 0 < p := by positivity
  have hpe : exp (-k) ≤ p := exp_neg_le_factorial_div k
  have hp1 : p ≤ 1 := by
    rw [hp_def, div_le_one (by positivity)]
    exact_mod_cast Nat.factorial_le_pow k
  have hlogℓ : 0 < log ℓ := log_pos (by exact_mod_cast (by omega : 1 < ℓ))
  have htpos : 0 < t := by
    have : (0 : ℝ) < k * exp k * log ℓ := by
      have : (0 : ℝ) < k := by exact_mod_cast hk
      positivity
    exact_mod_cast this.trans_le ht
  -- `(b/N)^t ≤ (1-p)^t < exp(-p)^t = exp(-p t) ≤ exp(-k ln ℓ) = ℓ^{-k}`
  have h1 : ((b : ℝ) / N) ^ t ≤ (1 - p) ^ t := by
    exact pow_le_pow_left₀ (by positivity) (by rwa [div_le_iff₀ hNr, mul_comm]) t
  have h2 : (1 - p) ^ t < exp (-p) ^ t := by
    apply pow_lt_pow_left₀ _ (by linarith) htpos.ne'
    have := add_one_lt_exp (x := -p) (by linarith)
    linarith
  have h3 : exp (-p) ^ t ≤ exp (-(k * log ℓ)) := by
    rw [← exp_nat_mul, exp_le_exp]
    have hk0 : (0 : ℝ) ≤ k := by positivity
    have : (k : ℝ) * log ℓ ≤ p * t := by
      calc (k : ℝ) * log ℓ = exp (-k) * (k * exp k * log ℓ) := by
              rw [show exp (-(k : ℝ)) * (k * exp k * log ℓ) = k * log ℓ * (exp (-k) * exp k) by ring,
                ← exp_add]; simp
        _ ≤ p * t := by
              apply mul_le_mul hpe ht (by positivity) hp0.le
    nlinarith
  have h4 : exp (-(k * log ℓ)) = ((ℓ : ℝ) ^ k)⁻¹ := by
    rw [exp_neg, ← log_pow, exp_log (by positivity)]
  have hC : (ℓ.choose k : ℝ) ≤ (ℓ : ℝ) ^ k := by exact_mod_cast Nat.choose_le_pow ℓ k
  have hℓk : (0 : ℝ) < (ℓ : ℝ) ^ k := by positivity
  have key : (ℓ.choose k : ℝ) * ((b : ℝ) / N) ^ t < 1 := by
    calc (ℓ.choose k : ℝ) * ((b : ℝ) / N) ^ t ≤ (ℓ : ℝ) ^ k * ((b : ℝ) / N) ^ t := by
          gcongr
      _ < (ℓ : ℝ) ^ k * ((ℓ : ℝ) ^ k)⁻¹ := by
          gcongr
          exact (h1.trans_lt h2).trans_le (h3.trans h4.le)
      _ = 1 := mul_inv_cancel₀ hℓk.ne'
  rw [div_pow, ← mul_div_assoc, div_lt_one (by positivity)] at key
  exact key

end PerfectHash

open PerfectHash in
/-- **Perfect hash families** (Fredman–Komlós; Mehlhorn, *Data Structures and Algorithms 1*,
1984, Sect. III.2.3): for `1 ≤ k ≤ ℓ` and `ℓ ≥ 2` there is a `(k, ℓ)`-perfect hash family with at most
`⌈k e^k ln ℓ⌉` functions. -/
theorem exists_isPerfectHashFamily_card_le (hk : 1 ≤ k) (hkℓ : k ≤ ℓ) (hℓ : 2 ≤ ℓ) :
    ∃ H : Finset (Fin ℓ → Fin k), IsPerfectHashFamily k ℓ H ∧
      H.card ≤ ⌈(k : ℝ) * exp k * log ℓ⌉₊ := by
  classical
  set t := ⌈(k : ℝ) * exp k * log ℓ⌉₊
  -- bad `t`-tuples: some `k`-set has no perfect function among them
  let good : Finset (Fin ℓ) → Finset (Fin ℓ → Fin k) := fun S => univ.filter fun h => Set.InjOn h S
  let bad : Finset (Fin t → Fin ℓ → Fin k) :=
    (univ.powersetCard k).biUnion fun S => Fintype.piFinset fun _ => (good S)ᶜ
  set N := Fintype.card (Fin ℓ → Fin k) with hN
  have hNpos : 0 < N := by
    rw [hN, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]; positivity
  have hNk : (N : ℝ) = (k : ℝ) ^ ℓ := by
    rw [hN, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]; push_cast; rfl
  have hbadS : ∀ S ∈ univ.powersetCard k,
      (((good S)ᶜ).card : ℝ) ≤ N * (1 - (k ! : ℝ) / (k : ℝ) ^ k) := by
    intro S hS
    rw [mem_powersetCard] at hS
    have hg := card_injOn_ge (k := k) S hS.2
    rw [card_compl]
    have hle : (good S).card ≤ N := card_le_univ _
    rw [Nat.cast_sub hle, hNk, mul_sub, mul_one]
    have hk0 : (0 : ℝ) < (k : ℝ) ^ k := by
      have : (0 : ℝ) < k := by exact_mod_cast hk
      positivity
    have : (k : ℝ) ^ ℓ * ((k ! : ℝ) / (k : ℝ) ^ k) = (k ! * k ^ (ℓ - k) : ℕ) := by
      push_cast
      rw [show ℓ = k + (ℓ - k) by omega, pow_add]
      simp only [show k + (ℓ - k) - k = ℓ - k by omega]
      field_simp
    rw [this]
    have : ((k ! * k ^ (ℓ - k) : ℕ) : ℝ) ≤ (good S).card := by exact_mod_cast hg
    linarith
  -- each `S` contributes at most `N (1 - k!/k^k)` bad functions per coordinate
  set B := ⌊(N : ℝ) * (1 - (k ! : ℝ) / (k : ℝ) ^ k)⌋₊
  have hbad : (bad.card : ℝ) ≤ (ℓ.choose k : ℝ) * (B : ℝ) ^ t := by
    have h := card_biUnion_le (s := univ.powersetCard k)
      (t := fun S => Fintype.piFinset fun _ : Fin t => (good S)ᶜ)
    have h' : ∀ S ∈ univ.powersetCard k,
        (Fintype.piFinset fun _ : Fin t => (good S)ᶜ).card ≤ B ^ t := by
      intro S hS
      rw [Fintype.card_piFinset, prod_const, card_univ, Fintype.card_fin]
      gcongr
      apply Nat.le_floor
      exact hbadS S hS
    have := h.trans (sum_le_sum h')
    rw [sum_const, card_powersetCard, card_univ, Fintype.card_fin, smul_eq_mul] at this
    exact_mod_cast this
  have hlt : bad.card < Fintype.card (Fin t → Fin ℓ → Fin k) := by
    rw [Fintype.card_fun, Fintype.card_fin, ← hN]
    have hB : (B : ℝ) ≤ N * (1 - (k ! : ℝ) / (k : ℝ) ^ k) := by
      apply Nat.floor_le
      have : (k ! : ℝ) / (k : ℝ) ^ k ≤ 1 := by
        have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
        rw [div_le_one (by positivity)]
        exact_mod_cast Nat.factorial_le_pow k
      have : (0 : ℝ) ≤ N := by positivity
      nlinarith
    have := union_bound_lt hk hℓ N B t hNpos hB (Nat.le_ceil _)
    exact_mod_cast hbad.trans_lt this
  obtain ⟨f, -, hf⟩ := exists_mem_notMem_of_card_lt_card (s := bad) (t := univ)
    (by simpa using hlt)
  refine ⟨univ.image f, ?_, ?_⟩
  · intro S hS
    by_contra hno
    push Not at hno
    apply hf
    simp only [bad, mem_biUnion, mem_powersetCard, Fintype.mem_piFinset]
    refine ⟨S, ⟨subset_univ _, hS⟩, fun i => ?_⟩
    simp only [good, mem_compl, mem_filter, mem_univ, true_and]
    exact hno (f i) (mem_image_of_mem f (mem_univ i))
  · calc (univ.image f).card ≤ (univ : Finset (Fin t)).card := card_image_le
      _ = t := by simp

/-- Theorem 7 with the binary logarithm `log₂ ℓ ≥ ln ℓ`. -/
theorem exists_isPerfectHashFamily_card_le_logb (hk : 1 ≤ k) (hkℓ : k ≤ ℓ) (hℓ : 2 ≤ ℓ) :
    ∃ H : Finset (Fin ℓ → Fin k), IsPerfectHashFamily k ℓ H ∧
      H.card ≤ ⌈(k : ℝ) * exp k * logb 2 ℓ⌉₊ := by
  obtain ⟨H, hH, hc⟩ := exists_isPerfectHashFamily_card_le hk hkℓ hℓ
  refine ⟨H, hH, hc.trans (Nat.ceil_mono ?_)⟩
  have hlog : log ℓ ≤ logb 2 ℓ := by
    have hl : 0 ≤ log (ℓ : ℝ) := log_nonneg (by exact_mod_cast (by omega : 1 ≤ ℓ))
    rw [logb, le_div_iff₀ (log_pos one_lt_two)]
    have : log 2 ≤ 1 := by
      have := log_two_lt_d9; linarith
    nlinarith
  gcongr

/-- For `k = ℓ` a single function (the identity) is a `(k, k)`-perfect hash family. -/
theorem isPerfectHashFamily_univ_id : IsPerfectHashFamily k k {id} :=
  fun _ _ => ⟨id, mem_singleton_self _, Function.injective_id.injOn⟩

end Cslib
