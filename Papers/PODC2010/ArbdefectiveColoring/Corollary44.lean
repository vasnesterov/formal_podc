import Papers.PODC2010.ArbdefectiveColoring.Theorem43

/-!
# Corollary 4.4: `O(a)`-colouring in `O(a^μ + (log n)^{1+μ})` rounds

The paper runs Procedure Legal-Coloring with `p = ⌊a^{μ'}/log n⌋` for "superlogarithmic" `a`,
claiming that then `p > a^{μ'/2}` for large `n`, and uses Theorem 4.3 for polylogarithmic `a`.
The claim `p > a^{μ'/2}` needs `a^{μ'/2} > log n`, i.e. `a > (log n)^{2/μ'}`, not merely
`a = ω(log n)`: e.g. for `a = log² n` and `μ' < 1` we get `p < 1`. The corollary is still true:
we split at `a^{μ/4} ≈ log n` instead (three cases):

1. `p₁ = ⌊a^{μ/2}/ℓ⌋ ≥ 16` and `(3+ε)a^{μ/4} ≤ p₁` (`ℓ = ⌊log₂ n⌋ + 1`): Legal-Coloring with `p₁`
   (`legalColoring_general`, `θ = μ/4`) takes `O(a^μ + log n)` rounds;
2. otherwise `a^{μ/4} ≤ 5ℓ`; if `⌊a^{μ²/8}⌋ ≥ 16`, Theorem 4.3 with `μ'' = μ²/4` takes
   `O(a^{μ''} log n) = O(ℓ^{1+μ})` rounds;
3. otherwise `a < 16^{8/μ²}` is a constant, and Lemma 2.2(1) takes `O(log n)` rounds.

* `corollary_4_4` (**Corollary 4.4**): constants `c₁, c₂, c₃` depending only on `ε, μ, C` such
  that for every `n`-vertex identifier space and every `a ≥ 1` there is an algorithm computing a
  legal colouring with fewer than `c₃ a` colours on every graph of arboricity `≤ a`, in at most
  `c₁ (a^μ + ℓ^{1+μ}) + c₂ R` rounds (`R = O(log* n)` the rounds of Lemma 2.1).
-/

open Finset Cslib.Local

namespace Podc.ArbdefectiveColoring

open scoped Classical

set_option linter.unusedSectionVars false

variable {V : Type*} [Fintype V]

section Cases

variable {C R : ℕ} {ε μ : ℝ} {a : ℕ}

/-- `ℓ = ⌊log₂ n⌋ + 1`, as a real number. -/
noncomputable def ellR (V : Type*) [Fintype V] : ℝ := ((Nat.log 2 (Fintype.card V) + 1 : ℕ) : ℝ)

lemma one_le_ellR : (1 : ℝ) ≤ ellR V := by
  simp only [ellR]; exact_mod_cast Nat.succ_pos _

lemma Lε_eq (ε : ℝ) : (Lε ε (Fintype.card V) : ℝ) = (⌈2 / ε⌉₊ : ℝ) * ellR V := by
  simp [Lε, ellR]

lemma ellR_le_rpow (hμ : 0 ≤ μ) : ellR V ≤ ellR V ^ (1 + μ) := by
  have h1 := one_le_ellR (V := V)
  calc ellR V = ellR V ^ (1 : ℝ) := (Real.rpow_one _).symm
    _ ≤ ellR V ^ (1 + μ) := Real.rpow_le_rpow_of_exponent_le h1 (by linarith)

/-- Case 1: `p = ⌊a^{μ/2}/ℓ⌋ ≥ 16` and `(3+ε) a^{μ/4} ≤ p`. -/
lemma cor44_case1 (hK : Lemma21 V C R) (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) (hμ : 0 < μ) (ha : 1 ≤ a)
    (hp : 16 ≤ ⌊(a : ℝ) ^ (μ / 2) / ellR V⌋₊)
    (hy : (3 + ε) * (a : ℝ) ^ (μ / 4) ≤ ⌊(a : ℝ) ^ (μ / 2) / ellR V⌋₊) :
    ∃ (f : SimpleGraph V → V → ℕ) (T : ℕ), IsLocalG T f ∧
      (T : ℝ) ≤ (4 / μ + 1) * (9 * C * ⌈2 / ε⌉₊ * (a : ℝ) ^ μ + 2 * ⌈2 / ε⌉₊ * ellR V + R) ∧
      ∀ G : SimpleGraph V, G.ArboricityLE a → IsLegal G (f G) ∧
        ∀ v, (f G v : ℝ) < (3 + ε) ^ (4 / μ + 1) * a := by
  set p := ⌊(a : ℝ) ^ (μ / 2) / ellR V⌋₊
  obtain ⟨h1, h2, h3⟩ := legalColoring_general hK (a := a) hε hε2 (θ := μ / 4) (by positivity) hp
    hy ha
  rw [one_div_div] at h2 h3
  refine ⟨_, _, h1, h2.trans ?_, h3⟩
  have hl := one_le_ellR (V := V)
  have hpx : (p : ℝ) ≤ (a : ℝ) ^ (μ / 2) / ellR V := Nat.floor_le (by positivity)
  have hp2 : (p : ℝ) ^ 2 * ellR V ≤ (a : ℝ) ^ μ := by
    have hx : ((a : ℝ) ^ (μ / 2)) ^ 2 = (a : ℝ) ^ μ := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg a)]; norm_num
    have h0 : (0 : ℝ) ≤ p := Nat.cast_nonneg _
    have h1 : (p : ℝ) * ellR V ≤ (a : ℝ) ^ (μ / 2) := by rwa [le_div_iff₀ (by linarith)] at hpx
    have h2 : ((p : ℝ) * ellR V) ^ 2 ≤ ((a : ℝ) ^ (μ / 2)) ^ 2 :=
      pow_le_pow_left₀ (by positivity) h1 2
    have h3 : (p : ℝ) ^ 2 * ellR V ≤ ((p : ℝ) * ellR V) ^ 2 := by
      have : (0 : ℝ) ≤ (p : ℝ) ^ 2 := by positivity
      nlinarith
    rw [← hx]; linarith
  rw [Lε_eq]
  have hm : (0 : ℝ) ≤ ⌈2 / ε⌉₊ := Nat.cast_nonneg _
  have hC : (0 : ℝ) ≤ C := Nat.cast_nonneg _
  have : (⌈2 / ε⌉₊ : ℝ) * ellR V * (9 * C * (p : ℝ) ^ 2 + 2) + R ≤
      9 * C * ⌈2 / ε⌉₊ * (a : ℝ) ^ μ + 2 * ⌈2 / ε⌉₊ * ellR V + R := by
    have : (⌈2 / ε⌉₊ : ℝ) * ellR V * (9 * C * (p : ℝ) ^ 2) ≤ 9 * C * ⌈2 / ε⌉₊ * (a : ℝ) ^ μ := by
      have := mul_le_mul_of_nonneg_left hp2 (by positivity : (0 : ℝ) ≤ 9 * C * ⌈2 / ε⌉₊)
      nlinarith
    nlinarith
  gcongr

/-- In the complement of case 1, `a^{μ/4} ≤ 5ℓ`. -/
lemma rpow_le_of_not_case1 (hε2 : ε ≤ 1 / 2)
    (h : ¬ (16 ≤ ⌊(a : ℝ) ^ (μ / 2) / ellR V⌋₊ ∧
      (3 + ε) * (a : ℝ) ^ (μ / 4) ≤ ⌊(a : ℝ) ^ (μ / 2) / ellR V⌋₊)) :
    (a : ℝ) ^ (μ / 4) ≤ 5 * ellR V := by
  set y := (a : ℝ) ^ (μ / 4)
  have hl := one_le_ellR (V := V)
  have hy0 : 0 ≤ y := by positivity
  have hxy : (a : ℝ) ^ (μ / 2) = y ^ 2 := by
    simp only [y, ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg a)]; ring_nf
  rw [hxy] at h
  have hfl : y ^ 2 / ellR V < ⌊y ^ 2 / ellR V⌋₊ + 1 := Nat.lt_floor_add_one _
  rw [div_lt_iff₀ (by linarith)] at hfl
  by_contra hcon
  push Not at hcon
  apply h
  constructor
  · -- `y² / ℓ ≥ 25 ℓ ≥ 16`
    apply Nat.le_floor
    rw [le_div_iff₀ (by linarith)]
    push_cast
    have h5 : 5 * ellR V * (5 * ellR V) ≤ y * y := by
      have : 0 ≤ 5 * ellR V := by linarith
      exact mul_le_mul hcon.le hcon.le this (by linarith)
    nlinarith
  · -- `(3+ε) y ≤ y²/ℓ - 1 < ⌊y²/ℓ⌋`
    have : (3 + ε) * y + 1 ≤ y ^ 2 / ellR V := by
      rw [le_div_iff₀ (by linarith)]
      have hy1 : 1 ≤ y := by linarith
      have h5 : 5 * ellR V * y ≤ y * y := mul_le_mul_of_nonneg_right hcon.le hy0
      have h6 : ((3 + ε) * y + 1) * ellR V ≤ 5 * ellR V * y := by
        have : (3 + ε) * y + 1 ≤ 5 * y := by nlinarith
        have := mul_le_mul_of_nonneg_right this (by linarith : (0 : ℝ) ≤ ellR V)
        linarith
      nlinarith
    have hfl' : y ^ 2 / ellR V < ⌊y ^ 2 / ellR V⌋₊ + 1 := Nat.lt_floor_add_one _
    linarith

/-- Case 2: Theorem 4.3 with `μ'' = μ²/4`, when `a^{μ/4} ≤ 5ℓ`. -/
lemma cor44_case2 (hK : Lemma21 V C R) (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) (hμ : 0 < μ) (hμ1 : μ ≤ 1)
    (hsmall : (a : ℝ) ^ (μ / 4) ≤ 5 * ellR V) (hp : 16 ≤ pμ (μ ^ 2 / 4) a) :
    ∃ (f : SimpleGraph V → V → ℕ) (T : ℕ), IsLocalG T f ∧
      (T : ℝ) ≤ (16 / μ ^ 2 + 1) * ((45 * C + 2) * ⌈2 / ε⌉₊ * ellR V ^ (1 + μ) + R) ∧
      ∀ G : SimpleGraph V, G.ArboricityLE a → IsLegal G (f G) ∧
        ∀ v, (f G v : ℝ) < (3 + ε) ^ (16 / μ ^ 2 + 1) * a := by
  have hμ'' : 0 < μ ^ 2 / 4 := by positivity
  obtain ⟨h1, h2, h3⟩ := theorem_4_3 hK hε hε2 hμ'' hp
  have e : 4 / (μ ^ 2 / 4) = 16 / μ ^ 2 := by field_simp; ring
  rw [e] at h2 h3
  refine ⟨_, _, h1, h2.trans ?_, h3⟩
  have hl := one_le_ellR (V := V)
  -- `a^{μ²/4} = (a^{μ/4})^μ ≤ (5ℓ)^μ ≤ 5 ℓ^μ`
  have hpow : (a : ℝ) ^ (μ ^ 2 / 4) ≤ 5 * ellR V ^ μ := by
    have e2 : (a : ℝ) ^ (μ ^ 2 / 4) = ((a : ℝ) ^ (μ / 4)) ^ μ := by
      rw [← Real.rpow_mul (Nat.cast_nonneg a)]; ring_nf
    rw [e2]
    calc ((a : ℝ) ^ (μ / 4)) ^ μ ≤ (5 * ellR V) ^ μ :=
          Real.rpow_le_rpow (by positivity) hsmall hμ.le
      _ = 5 ^ μ * ellR V ^ μ := Real.mul_rpow (by norm_num) (by linarith)
      _ ≤ 5 * ellR V ^ μ := by
          gcongr
          calc (5 : ℝ) ^ μ ≤ 5 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hμ1
            _ = 5 := Real.rpow_one 5
  have hlr : ellR V * ellR V ^ μ = ellR V ^ (1 + μ) := by
    rw [Real.rpow_add (by linarith), Real.rpow_one]
  have hl1 : ellR V ≤ ellR V ^ (1 + μ) := ellR_le_rpow hμ.le
  rw [Lε_eq]
  have hm : (0 : ℝ) ≤ ⌈2 / ε⌉₊ := Nat.cast_nonneg _
  have hC : (0 : ℝ) ≤ C := Nat.cast_nonneg _
  have : (⌈2 / ε⌉₊ : ℝ) * ellR V * (9 * C * (a : ℝ) ^ (μ ^ 2 / 4) + 2) ≤
      (45 * C + 2) * ⌈2 / ε⌉₊ * ellR V ^ (1 + μ) := by
    have hA : (⌈2 / ε⌉₊ : ℝ) * ellR V * (9 * C * (a : ℝ) ^ (μ ^ 2 / 4)) ≤
        45 * C * ⌈2 / ε⌉₊ * ellR V ^ (1 + μ) := by
      rw [← hlr]
      have := mul_le_mul_of_nonneg_left hpow
        (by positivity : (0 : ℝ) ≤ (⌈2 / ε⌉₊ : ℝ) * ellR V * (9 * C))
      nlinarith
    have hB : (⌈2 / ε⌉₊ : ℝ) * ellR V * 2 ≤ 2 * ⌈2 / ε⌉₊ * ellR V ^ (1 + μ) := by nlinarith
    nlinarith
  gcongr

/-- Case 3: `a < 16^{8/μ²}` is bounded; Lemma 2.2(1) with the legal colourings of Lemma 2.1. -/
lemma cor44_case3 (hK : Lemma21 V C R) (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) (hμ : 0 < μ) (ha : 1 ≤ a)
    (hp : pμ (μ ^ 2 / 4) a < 16) :
    ∃ (f : SimpleGraph V → V → ℕ) (T : ℕ), IsLocalG T f ∧
      (T : ℝ) ≤ ⌈2 / ε⌉₊ * (C * (7 / 2 * (16 : ℝ) ^ (8 / μ ^ 2) + 1) ^ 2 + 2) * ellR V + R ∧
      ∀ G : SimpleGraph V, G.ArboricityLE a → IsLegal G (f G) ∧
        ∀ v, (f G v : ℝ) < (3 + ε) * a := by
  set A := Aε ε a
  set L := Lε ε (Fintype.card V)
  set D := hK.legal A
  refine ⟨legalCol A L (C * (A + 1) ^ 2) D.col, _, legalCol_isLocal _ _ _ D.isLocal, ?_,
    fun G hG => ?_⟩
  · -- `a < 16^{8/μ²}`
    have ha16 : (a : ℝ) < (16 : ℝ) ^ (8 / μ ^ 2) := by
      have hx : (a : ℝ) ^ (μ ^ 2 / 4 / 2) < 16 := by
        by_contra hc
        push Not at hc
        have : 16 ≤ pμ (μ ^ 2 / 4) a := Nat.le_floor (by exact_mod_cast hc)
        omega
      have e : (a : ℝ) = ((a : ℝ) ^ (μ ^ 2 / 4 / 2)) ^ (8 / μ ^ 2) := by
        rw [← Real.rpow_mul (Nat.cast_nonneg a)]
        have : μ ^ 2 / 4 / 2 * (8 / μ ^ 2) = 1 := by field_simp; ring
        rw [this, Real.rpow_one]
      rw [e]
      exact Real.rpow_lt_rpow (by positivity) hx (by positivity)
    have hA : (A : ℝ) + 1 ≤ 7 / 2 * (16 : ℝ) ^ (8 / μ ^ 2) + 1 := by
      have := Aε_le hε.le a
      nlinarith
    have hL := one_le_Lε hε (Fintype.card V)
    have hnat : L * (C * (A + 1) ^ 2) - 1 + (1 + (R + L)) ≤ L * (C * (A + 1) ^ 2) + R + 2 * L := by
      omega
    have hcast : ((L * (C * (A + 1) ^ 2) - 1 + (1 + (R + L)) : ℕ) : ℝ) ≤
        (L : ℝ) * (C * ((A : ℝ) + 1) ^ 2) + R + 2 * L := by exact_mod_cast hnat
    refine hcast.trans ?_
    rw [Lε_eq]
    have hm : (0 : ℝ) ≤ ⌈2 / ε⌉₊ := Nat.cast_nonneg _
    have hC : (0 : ℝ) ≤ C := Nat.cast_nonneg _
    have hl := one_le_ellR (V := V)
    have hsq : ((A : ℝ) + 1) ^ 2 ≤ (7 / 2 * (16 : ℝ) ^ (8 / μ ^ 2) + 1) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hA 2
    have : (C : ℝ) * ((A : ℝ) + 1) ^ 2 ≤ C * (7 / 2 * (16 : ℝ) ^ (8 / μ ^ 2) + 1) ^ 2 :=
      mul_le_mul_of_nonneg_left hsq hC
    have := mul_le_mul_of_nonneg_left this (by positivity : (0 : ℝ) ≤ ⌈2 / ε⌉₊ * ellR V)
    nlinarith
  · obtain ⟨hleg, hle⟩ := legalColoring_spec hG.hasOutDegLE (hRounds_ok hε _ a) D
    refine ⟨hleg, fun v => ?_⟩
    have h1 : (legalCol A L (C * (A + 1) ^ 2) D.col G v : ℝ) ≤ A := by exact_mod_cast hle v
    have h2 := Aε_le hε.le a
    have ha' : (1 : ℝ) ≤ a := by exact_mod_cast ha
    nlinarith

end Cases

/-- **The gap in the proof of Corollary 4.4.** The paper takes `p = ⌊a^{μ'}/log n⌋` and claims
that `p > a^{μ'/2}` for every superlogarithmic `a` and large `n`. This fails for the
superlogarithmic family `a = (log₂ n)²` and every `0 < μ' ≤ 1/2` (i.e. `μ = 2μ' ≤ 1`): for all
`n ≥ 4` we get `p ≤ 1 < a^{μ'/2}` (so Legal-Coloring is invoked with `p ≤ 1`, and its while-loop
does not terminate, see `line15_one`). -/
theorem corollary_4_4_proof_gap {μ' : ℝ} (hμ : 0 < μ') (hμ2 : μ' ≤ 1 / 2) {n : ℕ} (hn : 4 ≤ n) :
    let k := Nat.log 2 n
    let a := k ^ 2
    ⌊((a : ℕ) : ℝ) ^ μ' / k⌋₊ ≤ 1 ∧ (1 : ℝ) < ((a : ℕ) : ℝ) ^ (μ' / 2) := by
  intro k a
  have hk : 2 ≤ k := by
    have : Nat.log 2 4 ≤ Nat.log 2 n := Nat.log_mono_right hn
    simpa [k, show Nat.log 2 4 = 2 by decide] using this
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) ≤ k := by linarith
  have ha : ((a : ℕ) : ℝ) = (k : ℝ) ^ (2 : ℝ) := by
    simp only [a]; push_cast; rw [Real.rpow_two]
  constructor
  · apply Nat.le_of_lt_succ
    rw [Nat.floor_lt (by positivity)]
    rw [ha, ← Real.rpow_mul hk0, div_lt_iff₀ (by linarith)]
    have : (k : ℝ) ^ (2 * μ') ≤ (k : ℝ) ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    rw [Real.rpow_one] at this
    push_cast
    linarith
  · rw [ha, ← Real.rpow_mul hk0]
    exact Real.one_lt_rpow (by linarith) (by positivity)

/-- With `p = 1`, the bound of line 15 of Algorithm 2 never decreases (`⌊α + (2+ε)α⌋ ≥ α`), so the
while-loop `α > p` never terminates once `α > 1`. -/
theorem line15_one {ε : ℝ} (hε : 0 ≤ ε) (α : ℕ) :
    α ≤ ⌊(α : ℝ) / (1 : ℕ) + (2 + ε) * α / (1 : ℕ)⌋₊ := by
  apply Nat.le_floor
  push_cast
  simp only [div_one]
  have : (0 : ℝ) ≤ α := Nat.cast_nonneg _
  nlinarith

/-- **Corollary 4.4.** Assume Lemma 2.1 with constant `C` (`hK`, `R` rounds). For every
`0 < ε ≤ 1/2` and `0 < μ ≤ 1` there are constants `c₁, c₂, c₃` (depending only on `ε, μ, C`) such
that for every vertex set of size `n`, every `a ≥ 1` admits an algorithm that computes, on every
graph of arboricity `≤ a`, a legal colouring with fewer than `c₃ · a` colours, in at most
`c₁ · (a^μ + ℓ^{1+μ}) + c₂ · R` rounds, where `ℓ = ⌊log₂ n⌋ + 1`. With `R = O(log* n)` this is
`O(a^μ + (log n)^{1+μ})`. -/
theorem corollary_4_4 (C : ℕ) {ε μ : ℝ} (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) (hμ : 0 < μ)
    (hμ1 : μ ≤ 1) :
    ∃ c₁ c₂ c₃ : ℝ, ∀ (V : Type) [Fintype V] (R : ℕ), Lemma21 V C R → ∀ a : ℕ, 1 ≤ a →
      ∃ (f : SimpleGraph V → V → ℕ) (T : ℕ), IsLocalG T f ∧
        (T : ℝ) ≤ c₁ * ((a : ℝ) ^ μ + ellR V ^ (1 + μ)) + c₂ * R ∧
        ∀ G : SimpleGraph V, G.ArboricityLE a → IsLegal G (f G) ∧
          ∀ v, (f G v : ℝ) < c₃ * a := by
  set m : ℝ := ((⌈2 / ε⌉₊ : ℕ) : ℝ)
  set a₀ : ℝ := (16 : ℝ) ^ (8 / μ ^ 2)
  have hm : 0 ≤ m := Nat.cast_nonneg _
  have hC : (0 : ℝ) ≤ C := Nat.cast_nonneg _
  have hc2 : 4 / μ + 1 ≤ 16 / μ ^ 2 + 1 := by
    have : 4 / μ ≤ 16 / μ ^ 2 := by
      rw [div_le_div_iff₀ hμ (by positivity)]; nlinarith
    linarith
  have hc2' : (1 : ℝ) ≤ 16 / μ ^ 2 + 1 := by have : 0 ≤ 16 / μ ^ 2 := by positivity
                                             linarith
  have h3 : (1 : ℝ) ≤ 3 + ε := by linarith
  refine ⟨(16 / μ ^ 2 + 1) * m * (54 * C + 6 + C * (7 / 2 * a₀ + 1) ^ 2), 16 / μ ^ 2 + 1,
    (3 + ε) ^ (16 / μ ^ 2 + 1), fun V _ R hK a ha => ?_⟩
  have hl := one_le_ellR (V := V)
  have haμ : (0 : ℝ) ≤ (a : ℝ) ^ μ := by positivity
  have hlμ : (1 : ℝ) ≤ ellR V ^ (1 + μ) := Real.one_le_rpow hl (by linarith)
  have hR : (0 : ℝ) ≤ R := Nat.cast_nonneg _
  have hl1 := ellR_le_rpow (V := V) hμ.le
  have ha' : (0 : ℝ) ≤ a := Nat.cast_nonneg _
  have hpow1 : (3 + ε) ^ (4 / μ + 1) ≤ (3 + ε) ^ (16 / μ ^ 2 + 1) :=
    Real.rpow_le_rpow_of_exponent_le h3 hc2
  have hpow0 : (3 + ε) ≤ (3 + ε) ^ (16 / μ ^ 2 + 1) := by
    calc (3 + ε) = (3 + ε) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le h3 hc2'
  set K := (16 / μ ^ 2 + 1) * m * (54 * C + 6 + C * (7 / 2 * a₀ + 1) ^ 2)
  have hK0 : 0 ≤ C * (7 / 2 * a₀ + 1) ^ 2 := by positivity
  by_cases h1 : 16 ≤ ⌊(a : ℝ) ^ (μ / 2) / ellR V⌋₊ ∧
      (3 + ε) * (a : ℝ) ^ (μ / 4) ≤ ⌊(a : ℝ) ^ (μ / 2) / ellR V⌋₊
  · obtain ⟨f, T, hloc, hT, hcol⟩ := cor44_case1 hK hε hε2 hμ ha h1.1 h1.2
    refine ⟨f, T, hloc, hT.trans ?_, fun G hG => ⟨(hcol G hG).1, fun v =>
      ((hcol G hG).2 v).trans_le (by gcongr)⟩⟩
    have : 9 * C * m * (a : ℝ) ^ μ + 2 * m * ellR V ≤
        m * (54 * C + 6 + C * (7 / 2 * a₀ + 1) ^ 2) * ((a : ℝ) ^ μ + ellR V ^ (1 + μ)) := by
      have P1 := mul_nonneg (mul_nonneg hC hm) haμ
      have P2 := mul_nonneg hm haμ
      have P3 := mul_nonneg (mul_nonneg hm hK0) haμ
      have P4 := mul_nonneg (mul_nonneg hC hm) (le_trans zero_le_one hlμ)
      have P5 := mul_nonneg hm (le_trans zero_le_one hlμ)
      have P6 := mul_nonneg (mul_nonneg hm hK0) (le_trans zero_le_one hlμ)
      have P7 := mul_le_mul_of_nonneg_left hl1 hm
      nlinarith
    calc (4 / μ + 1) * (9 * C * m * (a : ℝ) ^ μ + 2 * m * ellR V + R)
        ≤ (16 / μ ^ 2 + 1) * (9 * C * m * (a : ℝ) ^ μ + 2 * m * ellR V + R) := by
          gcongr
      _ ≤ (16 / μ ^ 2 + 1) * (m * (54 * C + 6 + C * (7 / 2 * a₀ + 1) ^ 2) *
            ((a : ℝ) ^ μ + ellR V ^ (1 + μ)) + R) := by gcongr
      _ = K * ((a : ℝ) ^ μ + ellR V ^ (1 + μ)) + (16 / μ ^ 2 + 1) * R := by ring
  have hsmall := rpow_le_of_not_case1 (V := V) hε2 h1
  by_cases h2 : 16 ≤ pμ (μ ^ 2 / 4) a
  · obtain ⟨f, T, hloc, hT, hcol⟩ := cor44_case2 hK hε hε2 hμ hμ1 hsmall h2
    refine ⟨f, T, hloc, hT.trans ?_, hcol⟩
    have : (45 * C + 2) * m * ellR V ^ (1 + μ) ≤
        m * (54 * C + 6 + C * (7 / 2 * a₀ + 1) ^ 2) * ((a : ℝ) ^ μ + ellR V ^ (1 + μ)) := by
      have P1 := mul_nonneg (mul_nonneg hC hm) haμ
      have P2 := mul_nonneg hm haμ
      have P3 := mul_nonneg (mul_nonneg hm hK0) haμ
      have P4 := mul_nonneg (mul_nonneg hC hm) (le_trans zero_le_one hlμ)
      have P5 := mul_nonneg hm (le_trans zero_le_one hlμ)
      have P6 := mul_nonneg (mul_nonneg hm hK0) (le_trans zero_le_one hlμ)
      nlinarith
    calc (16 / μ ^ 2 + 1) * ((45 * C + 2) * m * ellR V ^ (1 + μ) + R)
        ≤ (16 / μ ^ 2 + 1) * (m * (54 * C + 6 + C * (7 / 2 * a₀ + 1) ^ 2) *
            ((a : ℝ) ^ μ + ellR V ^ (1 + μ)) + R) := by gcongr
      _ = K * ((a : ℝ) ^ μ + ellR V ^ (1 + μ)) + (16 / μ ^ 2 + 1) * R := by ring
  · push Not at h2
    obtain ⟨f, T, hloc, hT, hcol⟩ := cor44_case3 hK hε hε2 hμ ha h2
    refine ⟨f, T, hloc, hT.trans ?_, fun G hG => ⟨(hcol G hG).1, fun v =>
      ((hcol G hG).2 v).trans_le (by gcongr)⟩⟩
    have hB : m * (C * (7 / 2 * a₀ + 1) ^ 2 + 2) * ellR V ≤
        K * ((a : ℝ) ^ μ + ellR V ^ (1 + μ)) := by
      have e1 : m * (C * (7 / 2 * a₀ + 1) ^ 2 + 2) * ellR V ≤
          m * (54 * C + 6 + C * (7 / 2 * a₀ + 1) ^ 2) * ellR V ^ (1 + μ) := by
        have : C * (7 / 2 * a₀ + 1) ^ 2 + 2 ≤ 54 * C + 6 + C * (7 / 2 * a₀ + 1) ^ 2 := by
          linarith
        have hlpos : (0 : ℝ) ≤ ellR V := by linarith
        calc m * (C * (7 / 2 * a₀ + 1) ^ 2 + 2) * ellR V
            ≤ m * (54 * C + 6 + C * (7 / 2 * a₀ + 1) ^ 2) * ellR V := by gcongr
          _ ≤ m * (54 * C + 6 + C * (7 / 2 * a₀ + 1) ^ 2) * ellR V ^ (1 + μ) := by gcongr
      have e2 : m * (54 * C + 6 + C * (7 / 2 * a₀ + 1) ^ 2) * ellR V ^ (1 + μ) ≤
          K * ((a : ℝ) ^ μ + ellR V ^ (1 + μ)) := by
        have hX : (0 : ℝ) ≤ m * (54 * C + 6 + C * (7 / 2 * a₀ + 1) ^ 2) := by positivity
        calc m * (54 * C + 6 + C * (7 / 2 * a₀ + 1) ^ 2) * ellR V ^ (1 + μ)
            = 1 * (m * (54 * C + 6 + C * (7 / 2 * a₀ + 1) ^ 2) * ellR V ^ (1 + μ)) := by ring
          _ ≤ (16 / μ ^ 2 + 1) * (m * (54 * C + 6 + C * (7 / 2 * a₀ + 1) ^ 2) *
                ellR V ^ (1 + μ)) :=
              mul_le_mul_of_nonneg_right hc2' (by positivity)
          _ = (16 / μ ^ 2 + 1) * (m * (54 * C + 6 + C * (7 / 2 * a₀ + 1) ^ 2)) *
                ellR V ^ (1 + μ) := by ring
          _ ≤ K * ((a : ℝ) ^ μ + ellR V ^ (1 + μ)) := by
              simp only [K]
              have : (0 : ℝ) ≤ (16 / μ ^ 2 + 1) * m * (54 * C + 6 + C * (7 / 2 * a₀ + 1) ^ 2) := by
                positivity
              nlinarith
      linarith
    have hR' : (R : ℝ) ≤ (16 / μ ^ 2 + 1) * R := by nlinarith
    linarith

end Podc.ArbdefectiveColoring
