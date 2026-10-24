import Papers.PODC2010.ArbdefectiveColoring.Theorem43
import Papers.PODC2010.ArbdefectiveColoring.NonVacuity

/-!
# Lemma 4.1: a legal `O(a)`-colouring in `O(a^{2/3} log n)` rounds

One invocation of Arbdefective-Coloring with `k = t = ⌊a^{1/3}⌋`, followed by legal colourings of
the `k` subgraphs with disjoint palettes (Lemma 2.2(1)). The final step needs the
`(Δ+1)`-colouring algorithm of [BE09] in `O(Δ + log* n)` rounds (used in the proof of Lemma 3.3),
which we take as a second black box `DeltaPlusOne V C' R'` (`C'·(Δ+1) + R'` rounds); it is
satisfiable (`DeltaPlusOne.satisfiable`).

* `lemma_4_1` (**Lemma 4.1**): fewer than `((2+ε)(3+ε) + 1) · a` colours, in at most
  `(9C + 25) · L · a^{2/3} + 25 C' a^{2/3} + R + R' + 4L = O(a^{2/3} log n)` rounds.
-/

open Finset Cslib.Local

namespace Podc.ArbdefectiveColoring

open scoped Classical

set_option linter.unusedSectionVars false

variable {V : Type*} [Fintype V]

/-- The black box of [BE09] ("Distributed `(Δ+1)`-coloring in linear (in `Δ`) time"): for every
`Δ`, a legal `(Δ+1)`-colouring of the graphs of maximum degree `≤ Δ` in `C'·(Δ+1) + R'` rounds
(`R' = O(log* n)` in [BE09]). -/
def DeltaPlusOne (V : Type*) [Fintype V] (C' R' : ℕ) : Prop :=
  ∀ Δ : ℕ, Nonempty (DefectiveAlg V Δ 0 (Δ + 1) (C' * (Δ + 1) + R'))

/-- The `(Δ+1)`-colouring black box is satisfiable (with `n` rounds). -/
theorem DeltaPlusOne.satisfiable : DeltaPlusOne V 0 (Fintype.card V) := by
  intro Δ
  have D := lovaszDefectiveAlg (V := V) Δ (Δ + 1) (Nat.succ_pos Δ)
  rw [Nat.div_eq_of_lt (Nat.lt_succ_self Δ)] at D
  exact ⟨by simpa using D⟩

/-- The parameters of the algorithm of Lemma 4.1 (`p = k = t`). -/
noncomputable def lemma41Params {C R C' R' : ℕ} (hK : Lemma21 V C R) (hB : DeltaPlusOne V C' R')
    (ε : ℝ) (p : ℕ) (hp : 0 < p) : LCParams V where
  p := p
  A := Aε ε
  L := fun _ => Lε ε (Fintype.card V)
  d := fun α => Aε ε α / (3 * p)
  K := fun _ => C * (3 * p) ^ 2
  R := fun _ => R
  D := fun α => hK.alg (Aε ε α) (3 * p) (by omega)
  KB := fun α => Aε ε α + 1
  RB := fun α => C' * (Aε ε α + 1) + R'
  B := fun α => Classical.choice (hB (Aε ε α))

/-- `p = ⌊a^{1/3}⌋`. -/
noncomputable def p13 (a : ℕ) : ℕ := ⌊(a : ℝ) ^ ((1 : ℝ) / 3)⌋₊

lemma one_le_p13 {a : ℕ} (ha : 1 ≤ a) : 1 ≤ p13 a := by
  apply Nat.le_floor
  have : (1 : ℝ) ≤ a := by exact_mod_cast ha
  simpa using Real.one_le_rpow this (by norm_num : (0 : ℝ) ≤ 1 / 3)

/-- The algorithm of Lemma 4.1: one iteration of the while-loop, then the legal colourings. -/
noncomputable def lemma41Alg {C R C' R' : ℕ} (hK : Lemma21 V C R) (hB : DeltaPlusOne V C' R')
    (ε : ℝ) (a : ℕ) (ha : 1 ≤ a) : SimpleGraph V → V → ℕ :=
  (lemma41Params hK hB ε (p13 a) (one_le_p13 ha)).proc a 1

/-- The number of rounds of the algorithm of Lemma 4.1. -/
noncomputable def lemma41Rounds {C R C' R' : ℕ} (hK : Lemma21 V C R) (hB : DeltaPlusOne V C' R')
    (ε : ℝ) (a : ℕ) (ha : 1 ≤ a) : ℕ :=
  (lemma41Params hK hB ε (p13 a) (one_le_p13 ha)).legRounds
      ((lemma41Params hK hB ε (p13 a) (one_le_p13 ha)).bound a 1) +
    (lemma41Params hK hB ε (p13 a) (one_le_p13 ha)).loopRounds a 1

/-- **Lemma 4.1.** Assume Lemma 2.1 (`hK`) and the `(Δ+1)`-colouring of [BE09] (`hB`), and let
`0 < ε ≤ 1`, `a ≥ 1`. On every graph of arboricity `≤ a`, the algorithm (Arbdefective-Coloring with
`k = t = ⌊a^{1/3}⌋`, then legal colourings of the `k` subgraphs with disjoint palettes) computes a
legal colouring `φ` with fewer than `((2+ε)(3+ε) + 1) · a = O(a)` colours, in at most
`(9C + 25) · L · a^{2/3} + 25 C' · a^{2/3} + R + R' + 4L = O(a^{2/3} log n)` rounds, where
`L = ⌈2/ε⌉(⌊log₂ n⌋ + 1)`. -/
theorem lemma_4_1 {C R C' R' : ℕ} (hK : Lemma21 V C R) (hB : DeltaPlusOne V C' R') {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) {a : ℕ} (ha : 1 ≤ a) :
    IsLocalG (lemma41Rounds hK hB ε a ha) (lemma41Alg hK hB ε a ha) ∧
    (lemma41Rounds hK hB ε a ha : ℝ) ≤
      (9 * C + 25) * Lε ε (Fintype.card V) * (a : ℝ) ^ ((2 : ℝ) / 3) +
        25 * C' * (a : ℝ) ^ ((2 : ℝ) / 3) + R + R' + 4 * Lε ε (Fintype.card V) ∧
    ∀ G : SimpleGraph V, G.ArboricityLE a →
      IsLegal G (lemma41Alg hK hB ε a ha G) ∧
      ∀ v, (lemma41Alg hK hB ε a ha G v : ℝ) < ((2 + ε) * (3 + ε) + 1) * a := by
  set p := p13 a
  have hp0 : 0 < p := one_le_p13 ha
  set P := lemma41Params hK hB ε p hp0 with hPdef
  set L := Lε ε (Fintype.card V)
  have hL := one_le_Lε hε (Fintype.card V)
  have hHR : P.HRoundsOK := fun α => hRounds_ok hε _ α
  have ha' : (1 : ℝ) ≤ a := by exact_mod_cast ha
  -- `α₁ · p ≤ (3+ε) a` (Lemma 4.2(3) for one iteration)
  have hα1 : (P.bound a 1 : ℝ) * p ≤ (3 + ε) * a := by
    have h := defect_le hε.le hε1 a p p
    have h2 : (P.bound a 1 : ℝ) ≤ (a : ℝ) / p + (2 + ε) * a / p :=
      (Nat.cast_le.2 h).trans (Nat.floor_le (by positivity))
    have hp' : (0 : ℝ) < p := by exact_mod_cast hp0
    calc (P.bound a 1 : ℝ) * p ≤ ((a : ℝ) / p + (2 + ε) * a / p) * p := by gcongr
      _ = (3 + ε) * a := by field_simp; ring
  have hA1 := Aε_le hε.le (P.bound a 1)
  -- `x = a^{1/3}`, `p ≤ x < 2p`
  set x := (a : ℝ) ^ ((1 : ℝ) / 3)
  have hx1 : 1 ≤ x := Real.one_le_rpow ha' (by norm_num)
  have hpx : (p : ℝ) ≤ x := Nat.floor_le (by positivity)
  have hxp : x < 2 * p := by
    have h1 : x < p + 1 := Nat.lt_floor_add_one x
    have h2 : (1 : ℝ) ≤ p := by exact_mod_cast hp0
    linarith
  have hx3 : x ^ 3 = a := by
    simp only [x, ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg a)]; norm_num
  have hx2 : x ^ 2 = (a : ℝ) ^ ((2 : ℝ) / 3) := by
    simp only [x, ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg a)]; norm_num
  refine ⟨P.proc_isLocal a 1, ?_, fun G hG => ?_⟩
  · -- rounds
    have hR1 : P.legRounds (P.bound a 1) ≤ (L + C') * (Aε ε (P.bound a 1) + 1) + R' + 2 * L := by
      show L * (Aε ε (P.bound a 1) + 1) - 1 + (1 + ((C' * (Aε ε (P.bound a 1) + 1) + R') + L)) ≤ _
      have e : (L + C') * (Aε ε (P.bound a 1) + 1) =
          L * (Aε ε (P.bound a 1) + 1) + C' * (Aε ε (P.bound a 1) + 1) := by ring
      omega
    have hR2 : P.loopRounds a 1 ≤ L * (C * (9 * p ^ 2)) + R + 2 * L := by
      show L * (C * (3 * p) ^ 2) - 1 + (1 + (R + L)) + 0 ≤ _
      have : C * (3 * p) ^ 2 = C * (9 * p ^ 2) := by ring
      rw [this]
      omega
    -- `A₁ + 1 ≤ 25 a^{2/3}` and `p² ≤ a^{2/3}`
    have hA : (Aε ε (P.bound a 1) : ℝ) + 1 ≤ 25 * x ^ 2 := by
      have hp' : (0 : ℝ) < p := by exact_mod_cast hp0
      have h1 : (P.bound a 1 : ℝ) * p ≤ 4 * x ^ 3 := by rw [hx3]; nlinarith
      have h2 : (P.bound a 1 : ℝ) ≤ 8 * x ^ 2 := by
        have : (P.bound a 1 : ℝ) * x < (P.bound a 1 : ℝ) * (2 * p) + 1 := by
          have : (0 : ℝ) ≤ P.bound a 1 := Nat.cast_nonneg _
          nlinarith
        nlinarith
      nlinarith
    have hp2 : (p : ℝ) ^ 2 ≤ x ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hpx 2
    have hsum : lemma41Rounds hK hB ε a ha ≤
        (L + C') * (Aε ε (P.bound a 1) + 1) + R' + 2 * L + (L * (C * (9 * p ^ 2)) + R + 2 * L) := by
      have := add_le_add hR1 hR2
      exact this
    have hcast : (lemma41Rounds hK hB ε a ha : ℝ) ≤
        ((L : ℝ) + C') * ((Aε ε (P.bound a 1) : ℝ) + 1) + R' + 2 * L +
          (L * (C * (9 * (p : ℝ) ^ 2)) + R + 2 * L) := by exact_mod_cast hsum
    rw [← hx2]
    have hC : (0 : ℝ) ≤ C := Nat.cast_nonneg _
    have hC' : (0 : ℝ) ≤ C' := Nat.cast_nonneg _
    have hL0 : (0 : ℝ) ≤ L := Nat.cast_nonneg _
    have h1 : ((L : ℝ) + C') * ((Aε ε (P.bound a 1) : ℝ) + 1) ≤ ((L : ℝ) + C') * (25 * x ^ 2) :=
      mul_le_mul_of_nonneg_left hA (by positivity)
    have h2 : (L : ℝ) * (C * (9 * (p : ℝ) ^ 2)) ≤ L * (C * (9 * x ^ 2)) := by gcongr
    nlinarith
  · -- correctness and colours
    obtain ⟨hleg, hlt⟩ := P.proc_correct hHR hp0 hG 1
    refine ⟨hleg, fun v => ?_⟩
    have h1 : (P.proc a 1 G v : ℝ) < ((p ^ 1 * (Aε ε (P.bound a 1) + 1) : ℕ) : ℝ) := by
      exact_mod_cast hlt v
    have hpa : (p : ℝ) ≤ a := by
      have : x ≤ x ^ 3 := by nlinarith
      linarith
    calc (lemma41Alg hK hB ε a ha G v : ℝ) < _ := h1
      _ = (p : ℝ) * Aε ε (P.bound a 1) + p := by push_cast; ring
      _ ≤ (p : ℝ) * ((2 + ε) * P.bound a 1) + a := by gcongr
      _ = (2 + ε) * ((P.bound a 1 : ℝ) * p) + a := by ring
      _ ≤ (2 + ε) * ((3 + ε) * a) + a := by gcongr
      _ = ((2 + ε) * (3 + ε) + 1) * a := by ring

end Podc.ArbdefectiveColoring
