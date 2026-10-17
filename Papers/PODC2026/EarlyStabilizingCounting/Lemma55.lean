import Mathlib

/-!
# Lemma 5.5 of [LL26]: few collisions between two leader schedules

Lenzen, Loss, *Early-Stabilizing Counting*, PODC 2026.

For `b ∈ {0,1}`, instance `L` of schedule `b` occupies the window `[k_b L, k_b L + R]`; it collides
with schedule `1-b` (shifted by `o`) if the window meets `{k_{1-b} L' + o | L' ∈ ℤ}`.
Lemma 5.5: for every `0 < ε < 1` and `R` there are `R < k₀, k₁` such that among `L ∈ {0,…,L_max}`
at most `ε L_max + 1` collide.

* `collides` / `collCount`: the collision predicate and the number of colliding `L ≤ L_max`.
* `collides_sep`: with `k₀ = (R+1) q`, `k₁ = k₀ + R + 1`, two colliding `L < L'` satisfy
  `L' - L ≥ q` (the separation used in Lemma 5.6).
* `lemma_5_5`: the lemma, for real `ε`, with `k₀ = (R+1)⌈1/ε⌉`, `k₁ = k₀ + R + 1`.
* `lemma_5_5_proof_constants_fail`: the constants chosen in the paper's proof,
  `k₀ = ⌈(R+1)/ε⌉`, `k₁ = k₀ + R + 1`, do not work in general: for `ε = 2/3`, `R = 1`
  (`k₀ = 3`, `k₁ = 5`), `b = 1`, `o = 0`, `L_max = 1` both `L = 0, 1` collide, and `2 > ε + 1`.
  (For `ε = 1/4`, the only value used in the paper, both choices coincide.)
-/

namespace EarlyStabilizingCounting

/-- Window `[kb L, kb L + R]` meets the progression `ko ℤ + o`. -/
def collides (kb ko R : ℕ) (o : ℤ) (L : ℕ) : Prop :=
  ∃ j : ℕ, j ≤ R ∧ ∃ L' : ℤ, (kb : ℤ) * L + j = ko * L' + o

/-- Decidable via the residue test `(kb L + j - o) % ko = 0` for `j ≤ R`. -/
theorem collides_iff (kb ko R : ℕ) (o : ℤ) (L : ℕ) :
    collides kb ko R o L ↔ ∃ j ∈ Finset.range (R + 1), ((kb : ℤ) * L + j - o) % ko = 0 := by
  constructor
  · rintro ⟨j, hj, L', h⟩
    refine ⟨j, by simp; omega, ?_⟩
    rw [show (kb : ℤ) * L + j - o = ko * L' by linarith]
    simp
  · rintro ⟨j, hj, h⟩
    refine ⟨j, by simp at hj; omega, ((kb : ℤ) * L + j - o) / ko, ?_⟩
    have := Int.emod_add_mul_ediv ((kb : ℤ) * L + j - o) ko
    rw [h] at this; linarith

instance (kb ko R : ℕ) (o : ℤ) (L : ℕ) : Decidable (collides kb ko R o L) :=
  decidable_of_iff _ (collides_iff kb ko R o L).symm

/-- Number of `L ∈ {0, …, Lmax}` whose window collides. -/
def collCount (kb ko R : ℕ) (o : ℤ) (Lmax : ℕ) : ℕ :=
  ((Finset.range (Lmax + 1)).filter (collides kb ko R o)).card

/-- An integer multiple of `D > 0` of absolute value `< D` is zero. -/
theorem int_eq_zero_of_mul_small {D k e : ℤ} (hD : 0 < D) (h : D * k = e) (he1 : -D < e)
    (he2 : e < D) : k = 0 := by
  rcases lt_trichotomy k 0 with hk | hk | hk
  · have : D * k ≤ -D := by nlinarith
    omega
  · exact hk
  · have : D ≤ D * k := by nlinarith
    omega

/-- Separation: with `k₀ = (R+1) q` and `k₁ = k₀ + R + 1`, colliding instances of either schedule
are at least `q` apart. -/
theorem collides_sep (R q : ℕ) (_hq : 1 ≤ q) (b : Bool) (o : ℤ) {L L' : ℕ}
    (hL : collides (if b then (R + 1) * q + R + 1 else (R + 1) * q)
      (if b then (R + 1) * q else (R + 1) * q + R + 1) R o L)
    (hL' : collides (if b then (R + 1) * q + R + 1 else (R + 1) * q)
      (if b then (R + 1) * q else (R + 1) * q + R + 1) R o L')
    (hlt : L < L') : q ≤ L' - L := by
  obtain ⟨j, hj, A, hA⟩ := hL
  obtain ⟨j', hj', A', hA'⟩ := hL'
  have hD : (0 : ℤ) < R + 1 := by positivity
  cases b
  · -- kb = D q, ko = D (q+1): D * ((q+1) (A' - A) + (L' - L)) = j' - j ... rearranged
    simp only [Bool.false_eq_true, ↓reduceIte] at hA hA'
    push_cast at hA hA'
    have hk := int_eq_zero_of_mul_small (D := (R : ℤ) + 1)
      (k := ((q : ℤ) + 1) * (A' - A) - q * ((L' : ℤ) - L))
      (e := (j' : ℤ) - j) hD (by linear_combination hA - hA') (by omega) (by omega)
    have hΔ : (0 : ℤ) < (L' : ℤ) - L := by omega
    have h1 : (L' : ℤ) - L = ((q : ℤ) + 1) * ((L' : ℤ) - L - (A' - A)) := by linarith
    have hY : 1 ≤ (L' : ℤ) - L - (A' - A) := by
      by_contra hcon
      push Not at hcon
      nlinarith
    have : (q : ℤ) + 1 ≤ (L' : ℤ) - L := by nlinarith
    omega
  · simp only [↓reduceIte] at hA hA'
    push_cast at hA hA'
    have hk := int_eq_zero_of_mul_small (D := (R : ℤ) + 1)
      (k := (q : ℤ) * (A' - A) - ((q : ℤ) + 1) * ((L' : ℤ) - L))
      (e := (j' : ℤ) - j) hD (by linear_combination hA - hA') (by omega) (by omega)
    have hΔ : (0 : ℤ) < (L' : ℤ) - L := by omega
    by_contra hcon
    have hlt' : (L' : ℤ) - L < q := by omega
    have h1 : (q : ℤ) * (A' - A - ((L' : ℤ) - L)) = (L' : ℤ) - L := by linarith
    rcases lt_trichotomy (A' - A - ((L' : ℤ) - L)) 0 with h | h | h
    · nlinarith
    · rw [h] at h1; omega
    · nlinarith

/-- Elements of `range (Lmax + 1)` that are pairwise at least `q ≥ 1` apart number at most
`Lmax / q + 1`. -/
theorem card_le_of_sep {S : Finset ℕ} {q Lmax : ℕ} (hq : 1 ≤ q) (hS : S ⊆ Finset.range (Lmax + 1))
    (hsep : ∀ L ∈ S, ∀ L' ∈ S, L < L' → q ≤ L' - L) : S.card ≤ Lmax / q + 1 := by
  have hinj : Set.InjOn (fun L => L / q) S := by
    intro L hL L' hL' h
    simp only at h
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have := hsep L hL L' hL' hlt
      have h1 := Nat.div_add_mod L q
      have h2 := Nat.div_add_mod L' q
      have h3 := Nat.mod_lt L (by omega : 0 < q)
      have h4 := Nat.mod_lt L' (by omega : 0 < q)
      rw [h] at h1
      omega
    · have := hsep L' hL' L hL hlt
      have h1 := Nat.div_add_mod L q
      have h2 := Nat.div_add_mod L' q
      have h3 := Nat.mod_lt L (by omega : 0 < q)
      have h4 := Nat.mod_lt L' (by omega : 0 < q)
      rw [h] at h1
      omega
  have himg : S.image (fun L => L / q) ⊆ Finset.range (Lmax / q + 1) := by
    intro x hx
    simp only [Finset.mem_image] at hx
    obtain ⟨L, hL, rfl⟩ := hx
    have := Finset.mem_range.1 (hS hL)
    simp only [Finset.mem_range]
    exact Nat.lt_succ_of_le (Nat.div_le_div_right (by omega))
  rw [← Finset.card_image_of_injOn hinj]
  simpa using Finset.card_le_card himg

/-- Lemma 5.5 of [LL26]. -/
theorem lemma_5_5 (ε : ℝ) (hε0 : 0 < ε) (_hε1 : ε < 1) (R : ℕ) :
    ∃ k₀ k₁ : ℕ, R < k₀ ∧ R < k₁ ∧ ∀ (o : ℤ) (b : Bool) (Lmax : ℕ), 0 < Lmax →
      (collCount (if b then k₁ else k₀) (if b then k₀ else k₁) R o Lmax : ℝ) ≤ ε * Lmax + 1 := by
  set q := ⌈1 / ε⌉₊ with hqdef
  have hq1 : 1 ≤ q := by
    rw [hqdef, Nat.one_le_ceil_iff]; positivity
  have hqε : 1 / (q : ℝ) ≤ ε := by
    have : 1 / ε ≤ q := Nat.le_ceil _
    rw [div_le_iff₀ (by exact_mod_cast hq1)]
    rw [div_le_iff₀ hε0] at this
    linarith
  refine ⟨(R + 1) * q, (R + 1) * q + R + 1, by nlinarith, by omega, fun o b Lmax _ => ?_⟩
  have hcard : collCount (if b then (R + 1) * q + R + 1 else (R + 1) * q)
      (if b then (R + 1) * q else (R + 1) * q + R + 1) R o Lmax ≤ Lmax / q + 1 := by
    unfold collCount
    refine card_le_of_sep hq1 (Finset.filter_subset _ _) fun L hL L' hL' hlt => ?_
    exact collides_sep R q hq1 b o (Finset.mem_filter.1 hL).2 (Finset.mem_filter.1 hL').2 hlt
  have h2 : ((Lmax / q : ℕ) : ℝ) ≤ ε * Lmax := by
    calc ((Lmax / q : ℕ) : ℝ) ≤ (Lmax : ℝ) / q := Nat.cast_div_le
      _ = (1 / (q : ℝ)) * Lmax := by ring
      _ ≤ ε * Lmax := by gcongr
  have h3 : (collCount (if b then (R + 1) * q + R + 1 else (R + 1) * q)
      (if b then (R + 1) * q else (R + 1) * q + R + 1) R o Lmax : ℝ) ≤ (Lmax / q : ℕ) + 1 := by
    exact_mod_cast hcard
  linarith

/-- The constants of the paper's proof of Lemma 5.5 fail for `ε = 2/3`, `R = 1`. -/
theorem lemma_5_5_proof_constants_fail :
    let ε : ℚ := 2 / 3
    let R := 1
    let k₀ := ⌈((R + 1 : ℕ) : ℚ) / ε⌉.toNat
    let k₁ := k₀ + R + 1
    k₀ = 3 ∧ k₁ = 5 ∧ ((collCount k₁ k₀ R 0 1 : ℕ) : ℚ) > ε * 1 + 1 := by
  have h0 : ⌈((1 + 1 : ℕ) : ℚ) / (2 / 3)⌉.toNat = 3 := by
    norm_num [Int.ceil_eq_iff]
  have hc : collCount 5 3 1 0 1 = 2 := by decide
  simp only [h0, hc]
  norm_num

end EarlyStabilizingCounting
