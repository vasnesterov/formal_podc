import Papers.PODC2010.ArbdefectiveColoring.Parameters

/-!
# Theorem 4.3 and Lemma 4.2: `O(a)`-colouring in `O(a^μ log n)` rounds

Procedure Legal-Coloring with the paper's parameters (`kuhnParams`): `k = t = p`, H-partitions of
degree `⌊(2+ε)α⌋` with `Lε = O(log n)` rounds, the defective colourings of Lemma 2.1 with
`q = 3p` (so that the defect is `⌊⌊(2+ε)α⌋/(3p)⌋ ≤ ⌊α/p⌋`), and in the final step the legal
colourings of Lemma 2.1 with `q = Δ + 1`. The while-loop stops at the first iteration with
`α_i ≤ p` (`iters`).

* `next_le` (line 15): `α_{i+1} ≤ ⌊α_i/p + (2+ε)α_i/p⌋`.
* `bound_mul_pow_le` (**Lemma 4.2(3)**): `α_i · |𝒢_i| ≤ (3+ε)^i · a`, where `|𝒢_i| = p^i`.
* `iters_lt` (**Lemma 4.2(2)**): for `p = ⌊a^{μ/2}⌋ ≥ 16` and `ε ≤ 1/2`, the loop runs fewer than
  `4/μ` iterations.
* `theorem_4_3` (**Theorem 4.3**): a legal colouring with fewer than `(3+ε)^{4/μ+1} · a` colours,
  computed in at most `(4/μ + 1) · (Lε · (9C a^μ + 1) + R) = O(a^μ log n)` rounds.
-/

open Finset Cslib.Local

namespace Podc.ArbdefectiveColoring

open scoped Classical

set_option linter.unusedSectionVars false

variable {V : Type*} [Fintype V]

/-- The parameters of Procedure Legal-Coloring with the black box of Lemma 2.1. -/
noncomputable def kuhnParams {C R : ℕ} (hK : Lemma21 V C R) (ε : ℝ) (p : ℕ) (hp : 0 < p) :
    LCParams V where
  p := p
  A := Aε ε
  L := fun _ => Lε ε (Fintype.card V)
  d := fun α => Aε ε α / (3 * p)
  K := fun _ => C * (3 * p) ^ 2
  R := fun _ => R
  D := fun α => hK.alg (Aε ε α) (3 * p) (by omega)
  KB := fun α => C * (Aε ε α + 1) ^ 2
  RB := fun _ => R
  B := fun α => hK.legal (Aε ε α)

namespace LCParams

variable (P : LCParams V)

/-- The number of iterations of the while-loop (lines 4–16): the first `i` with `α_i ≤ p`. -/
noncomputable def iters (a : ℕ) : ℕ := sInf {i | P.bound a i ≤ P.p}

/-- Procedure Legal-Coloring with the while-loop condition of Algorithm 2. -/
noncomputable def algorithm2 (a : ℕ) : SimpleGraph V → V → ℕ := P.proc a (P.iters a)

/-- The number of rounds of Procedure Legal-Coloring. -/
noncomputable def rounds2 (a : ℕ) : ℕ := P.legRounds (P.bound a (P.iters a)) + P.loopRounds a (P.iters a)

theorem algorithm2_isLocal (a : ℕ) : IsLocalG (P.rounds2 a) (P.algorithm2 a) :=
  P.proc_isLocal a _

end LCParams

section Kuhn

variable {C R : ℕ} (hK : Lemma21 V C R) {ε : ℝ} {p : ℕ} (hp : 0 < p)

/-- Line 15 of Algorithm 2: the new arboricity bound is at most `⌊α/p + (2+ε)α/p⌋`. -/
lemma next_le (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (α : ℕ) :
    (kuhnParams hK ε p hp).next α ≤ ⌊(α : ℝ) / p + (2 + ε) * α / p⌋₊ :=
  defect_le hε hε1 α p p

lemma next_le_real (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (α : ℕ) :
    ((kuhnParams hK ε p hp).next α : ℝ) ≤ (3 + ε) * α / p := by
  have h := next_le hK hp hε hε1 α
  have h2 : ((⌊(α : ℝ) / p + (2 + ε) * α / p⌋₊ : ℕ) : ℝ) ≤ (α : ℝ) / p + (2 + ε) * α / p :=
    Nat.floor_le (by positivity)
  calc ((kuhnParams hK ε p hp).next α : ℝ) ≤ (α : ℝ) / p + (2 + ε) * α / p :=
        (Nat.cast_le.2 h).trans h2
    _ = (3 + ε) * α / p := by ring

/-- **Lemma 4.2(3)**: after `i` iterations, `α_i · |𝒢_i| ≤ (3+ε)^i · a`, where the collection `𝒢_i`
has `p^i` subgraphs (`LCParams.lab_spec`). -/
theorem bound_mul_pow_le (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (a i : ℕ) :
    ((kuhnParams hK ε p hp).bound a i : ℝ) * (p : ℝ) ^ i ≤ (3 + ε) ^ i * a := by
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  induction i with
  | zero => simp [LCParams.bound]
  | succ i ih =>
    have h := next_le_real hK hp hε hε1 ((kuhnParams hK ε p hp).bound a i)
    calc ((kuhnParams hK ε p hp).bound a (i + 1) : ℝ) * (p : ℝ) ^ (i + 1)
        = ((kuhnParams hK ε p hp).next ((kuhnParams hK ε p hp).bound a i) : ℝ) * p * p ^ i := by
          simp [LCParams.bound, pow_succ]; ring
      _ ≤ (3 + ε) * ((kuhnParams hK ε p hp).bound a i) / p * p * p ^ i := by gcongr
      _ = (3 + ε) * (((kuhnParams hK ε p hp).bound a i) * p ^ i) := by field_simp
      _ ≤ (3 + ε) * ((3 + ε) ^ i * a) := by gcongr
      _ = (3 + ε) ^ (i + 1) * a := by ring

/-- The while-loop terminates when `p > 3 + ε`. -/
lemma exists_bound_le (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hp5 : 5 ≤ p) (a : ℕ) :
    ∃ i, (kuhnParams hK ε p hp).bound a i ≤ p := by
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  have hr : (3 + ε) / p < 1 := by
    rw [div_lt_one hp']
    have : (5 : ℝ) ≤ p := by exact_mod_cast hp5
    linarith
  obtain ⟨i, hi⟩ := exists_pow_lt_of_lt_one (show (0 : ℝ) < 1 / (a + 1) by positivity) hr
  refine ⟨i, ?_⟩
  have h := bound_mul_pow_le hK hp hε hε1 a i
  have hpi : (0 : ℝ) < (p : ℝ) ^ i := by positivity
  have hlt : ((kuhnParams hK ε p hp).bound a i : ℝ) < 1 := by
    have h1 : ((kuhnParams hK ε p hp).bound a i : ℝ) ≤ ((3 + ε) / p) ^ i * a := by
      rw [div_pow, div_mul_eq_mul_div, le_div_iff₀ hpi]; exact h
    have h2 : ((3 + ε) / p) ^ i * (a : ℝ) ≤ ((3 + ε) / p) ^ i * (a + 1) := by
      have : (0 : ℝ) ≤ ((3 + ε) / p) ^ i := by positivity
      nlinarith
    have h3 : ((3 + ε) / p) ^ i * ((a : ℝ) + 1) < 1 := by
      rw [lt_div_iff₀ (by positivity)] at hi; linarith
    linarith
  have : (kuhnParams hK ε p hp).bound a i < 1 := by exact_mod_cast hlt
  omega

/-- If the loop runs `J + 1` iterations, then `p^{J+1} < (3+ε)^J · a`. -/
lemma pow_lt_of_iters_eq (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (a J : ℕ)
    (hJ : (kuhnParams hK ε p hp).iters a = J + 1) :
    (p : ℝ) ^ (J + 1) < (3 + ε) ^ J * a := by
  have hnot : J ∉ {i | (kuhnParams hK ε p hp).bound a i ≤ (kuhnParams hK ε p hp).p} :=
    Nat.notMem_of_lt_sInf (by rw [← LCParams.iters, hJ]; omega)
  simp only [Set.mem_ofPred_eq, not_le] at hnot
  have h := bound_mul_pow_le hK hp hε hε1 a J
  have hlt : (p : ℝ) < (kuhnParams hK ε p hp).bound a J := by exact_mod_cast hnot
  calc (p : ℝ) ^ (J + 1) = p * p ^ J := by ring
    _ < (kuhnParams hK ε p hp).bound a J * p ^ J := by gcongr
    _ ≤ (3 + ε) ^ J * a := h

/-- The loop stops with `α_I ≤ p`. -/
lemma bound_iters_le (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hp5 : 5 ≤ p) (a : ℕ) :
    (kuhnParams hK ε p hp).bound a ((kuhnParams hK ε p hp).iters a) ≤ p :=
  Nat.sInf_mem (exists_bound_le hK hp hε hε1 hp5 a)

/-- The number of colours: `p^I · (⌊(2+ε)α_I⌋ + 1) ≤ (3+ε)^{I+1} · a` (for `a ≥ 1`). -/
lemma colors_le (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (a : ℕ) (ha : 1 ≤ a) :
    ((p ^ (kuhnParams hK ε p hp).iters a *
      (Aε ε ((kuhnParams hK ε p hp).bound a ((kuhnParams hK ε p hp).iters a)) + 1) : ℕ) : ℝ) ≤
      (3 + ε) ^ ((kuhnParams hK ε p hp).iters a + 1) * a := by
  set P := kuhnParams hK ε p hp
  set I := P.iters a
  have hA := Aε_le hε (P.bound a I)
  have hb := bound_mul_pow_le hK hp hε hε1 a I
  have ha' : (1 : ℝ) ≤ a := by exact_mod_cast ha
  push_cast
  have h1 : ((p : ℝ) ^ I) * ((Aε ε (P.bound a I) : ℝ) + 1) ≤
      (2 + ε) * ((3 + ε) ^ I * a) + (p : ℝ) ^ I := by
    have : ((p : ℝ) ^ I) * (Aε ε (P.bound a I) : ℝ) ≤ (2 + ε) * ((P.bound a I : ℝ) * p ^ I) := by
      calc ((p : ℝ) ^ I) * (Aε ε (P.bound a I) : ℝ) ≤ (p : ℝ) ^ I * ((2 + ε) * P.bound a I) := by
            gcongr
        _ = (2 + ε) * ((P.bound a I : ℝ) * p ^ I) := by ring
    nlinarith
  rcases hI : I with _ | J
  · rw [hI] at h1
    simp only [pow_zero, one_mul, zero_add, pow_one] at h1 ⊢
    nlinarith
  · have hp' := pow_lt_of_iters_eq hK hp hε hε1 a J hI
    rw [hI] at h1
    have h3 : (0 : ℝ) ≤ (3 + ε) ^ J * a := by positivity
    calc ((p : ℝ) ^ (J + 1)) * ((Aε ε (P.bound a (J + 1)) : ℝ) + 1)
        ≤ (2 + ε) * ((3 + ε) ^ (J + 1) * a) + (p : ℝ) ^ (J + 1) := h1
      _ ≤ (2 + ε) * ((3 + ε) ^ (J + 1) * a) + (3 + ε) ^ J * a := by linarith
      _ = ((2 + ε) * (3 + ε) + 1) * ((3 + ε) ^ J * a) := by ring
      _ ≤ (3 + ε) ^ 2 * ((3 + ε) ^ J * a) := by gcongr; nlinarith
      _ = (3 + ε) ^ (J + 1 + 1) * a := by ring

/-- Rounds of one invocation of Arbdefective-Coloring and of the final step are at most
`L·C·9p² + R + 2L`. -/
lemma arbRounds_le (hε : 0 < ε) (α : ℕ) :
    (kuhnParams hK ε p hp).arbRounds α ≤
      Lε ε (Fintype.card V) * (C * (9 * p ^ 2)) + R + 2 * Lε ε (Fintype.card V) := by
  simp only [LCParams.arbRounds, kuhnParams]
  have hL := one_le_Lε hε (Fintype.card V)
  have : C * (3 * p) ^ 2 = C * (9 * p ^ 2) := by ring
  rw [this]
  omega

lemma legRounds_le (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) (hp16 : 16 ≤ p) {α : ℕ} (hα : α ≤ p) :
    (kuhnParams hK ε p hp).legRounds α ≤
      Lε ε (Fintype.card V) * (C * (9 * p ^ 2)) + R + 2 * Lε ε (Fintype.card V) := by
  simp only [LCParams.legRounds, kuhnParams]
  have hL := one_le_Lε hε (Fintype.card V)
  have hA : (Aε ε α + 1) ^ 2 ≤ 9 * p ^ 2 := by
    have h1 := Aε_le hε.le α
    have h2 : (α : ℝ) ≤ p := by exact_mod_cast hα
    have h3 : (16 : ℝ) ≤ p := by exact_mod_cast hp16
    have h4 : ((Aε ε α : ℝ) + 1) ^ 2 ≤ 9 * (p : ℝ) ^ 2 := by
      have : (Aε ε α : ℝ) ≤ 5 / 2 * p := by nlinarith
      have h0 : (0 : ℝ) ≤ Aε ε α := Nat.cast_nonneg _
      nlinarith
    exact_mod_cast h4
  have : Lε ε (Fintype.card V) * (C * (Aε ε α + 1) ^ 2) ≤
      Lε ε (Fintype.card V) * (C * (9 * p ^ 2)) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hA)
  omega

lemma loopRounds_le (hε : 0 < ε) (a i : ℕ) :
    (kuhnParams hK ε p hp).loopRounds a i ≤
      i * (Lε ε (Fintype.card V) * (C * (9 * p ^ 2)) + R + 2 * Lε ε (Fintype.card V)) := by
  induction i with
  | zero => simp [LCParams.loopRounds]
  | succ i ih =>
    simp only [LCParams.loopRounds]
    have := arbRounds_le hK hp hε ((kuhnParams hK ε p hp).bound a i)
    rw [Nat.succ_mul]
    omega

end Kuhn

/-! ### Theorem 4.3 -/

section Theorem43

variable {C R : ℕ} (hK : Lemma21 V C R) {ε μ : ℝ} {a : ℕ}

/-- The parameter `p = ⌊a^{μ/2}⌋` of Theorem 4.3. -/
noncomputable def pμ (μ : ℝ) (a : ℕ) : ℕ := ⌊(a : ℝ) ^ (μ / 2)⌋₊

/-- Procedure Legal-Coloring with `p = ⌊a^{μ/2}⌋` (Theorem 4.3). -/
noncomputable def theorem43Alg (hK : Lemma21 V C R) (ε μ : ℝ) (a : ℕ) (hp : 0 < pμ μ a) :
    SimpleGraph V → V → ℕ :=
  (kuhnParams hK ε (pμ μ a) hp).algorithm2 a

lemma one_lt_of_pμ (hμ : 0 < μ) (hp : 16 ≤ pμ μ a) : (1 : ℝ) < a := by
  by_contra h
  push Not at h
  have : (a : ℝ) ^ (μ / 2) ≤ 1 := Real.rpow_le_one (Nat.cast_nonneg _) h (by positivity)
  have : pμ μ a ≤ 1 := Nat.floor_le_one_of_le_one this
  omega

/-- `(3+ε) · a^{μ/4} ≤ p` for `p = ⌊a^{μ/2}⌋ ≥ 16` and `ε ≤ 1/2`. -/
lemma mul_rpow_le_pμ (hε2 : ε ≤ 1 / 2) (hp : 16 ≤ pμ μ a) :
    (3 + ε) * (a : ℝ) ^ (μ / 4) ≤ pμ μ a := by
  set x := (a : ℝ) ^ (μ / 2)
  set y := (a : ℝ) ^ (μ / 4)
  have hy0 : 0 ≤ y := by positivity
  have hxy : x = y ^ 2 := by
    simp only [x, y, ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg a)]
    norm_num; ring_nf
  have hx1 : x < pμ μ a + 1 := Nat.lt_floor_add_one x
  have hx16 : (16 : ℝ) ≤ x := by
    have : ((pμ μ a : ℕ) : ℝ) ≤ x := Nat.floor_le (by positivity)
    have h16 : (16 : ℝ) ≤ pμ μ a := by exact_mod_cast hp
    linarith
  have hy4 : 4 ≤ y := by nlinarith
  nlinarith

/-- The number of iterations for a general `p ≥ 16` with `(3+ε) a^θ ≤ p`: fewer than `1/θ`. -/
theorem iters_lt_of (hε : 0 ≤ ε) (hε1 : ε ≤ 1) {θ : ℝ} (hθ : 0 < θ) {p : ℕ} (hp : 16 ≤ p)
    (hy : (3 + ε) * (a : ℝ) ^ θ ≤ p) :
    ((kuhnParams hK ε p (by omega)).iters a : ℝ) < 1 / θ := by
  set I := (kuhnParams hK ε p (by omega)).iters a with hIdef
  rcases hI : I with _ | J
  · simp only [Nat.cast_zero]; positivity
  have h1 := pow_lt_of_iters_eq hK (p := p) (by omega) hε hε1 a J hI
  have hp16 : (16 : ℝ) ≤ p := by exact_mod_cast hp
  -- `a > 1`, since `16 (3+ε)^J ≤ p^{J+1} < (3+ε)^J a`
  have ha : (1 : ℝ) < a := by
    have hpJ : (3 + ε) ^ J ≤ (p : ℝ) ^ J := pow_le_pow_left₀ (by positivity) (by linarith) J
    have : 16 * (3 + ε) ^ J < (3 + ε) ^ J * (a : ℝ) := by
      calc 16 * (3 + ε) ^ J ≤ (p : ℝ) * p ^ J := by gcongr
        _ = (p : ℝ) ^ (J + 1) := by ring
        _ < _ := h1
    have hpos : (0 : ℝ) < (3 + ε) ^ J := by positivity
    nlinarith
  set y := (a : ℝ) ^ θ
  have hy0 : 0 ≤ y := by positivity
  have h3 : ((3 + ε) * y) ^ (J + 1) ≤ (p : ℝ) ^ (J + 1) := pow_le_pow_left₀ (by positivity) hy _
  have h4 : (3 + ε) * y ^ (J + 1) < a := by
    have hpos : (0 : ℝ) < (3 + ε) ^ J := by positivity
    have : (3 + ε) ^ J * ((3 + ε) * y ^ (J + 1)) < (3 + ε) ^ J * a := by
      calc (3 + ε) ^ J * ((3 + ε) * y ^ (J + 1)) = ((3 + ε) * y) ^ (J + 1) := by
            rw [mul_pow]; ring
        _ < (3 + ε) ^ J * a := h3.trans_lt h1
    exact lt_of_mul_lt_mul_left this hpos.le
  have h5 : y ^ (J + 1) < (a : ℝ) ^ (1 : ℝ) := by
    rw [Real.rpow_one]
    have : y ^ (J + 1) ≤ (3 + ε) * y ^ (J + 1) := by
      have : 0 ≤ y ^ (J + 1) := by positivity
      nlinarith
    linarith
  have h6 : y ^ (J + 1) = (a : ℝ) ^ (θ * (J + 1 : ℕ)) := by
    simp only [y, ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg a)]
  rw [h6, Real.rpow_lt_rpow_left_iff ha] at h5
  push_cast at h5 ⊢
  rw [lt_div_iff₀ hθ]
  linarith

/-- **Lemma 4.2(2)**: for `p = ⌊a^{μ/2}⌋ ≥ 16` and `0 ≤ ε ≤ 1/2`, the while-loop runs fewer than
`4/μ` iterations (a constant number). -/
theorem iters_lt (hε : 0 ≤ ε) (hε2 : ε ≤ 1 / 2) (hμ : 0 < μ) (hp : 16 ≤ pμ μ a) :
    ((kuhnParams hK ε (pμ μ a) (by omega)).iters a : ℝ) < 4 / μ := by
  have := iters_lt_of hK hε (by linarith) (θ := μ / 4) (by positivity) hp (mul_rpow_le_pμ hε2 hp)
  rwa [one_div_div] at this

/-- **Procedure Legal-Coloring, general parameter `p`.** Let `0 < ε ≤ 1/2`, `θ > 0`, `a ≥ 1`, and let
`p ≥ 16` with `(3+ε) a^θ ≤ p`. On every graph of arboricity `≤ a`, Procedure Legal-Coloring with
parameter `p` computes a legal colouring with fewer than `(3+ε)^{1/θ+1} · a` colours, in at most
`(1/θ + 1) · (L (9Cp² + 2) + R)` rounds. -/
theorem legalColoring_general (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) {θ : ℝ} (hθ : 0 < θ) {p : ℕ}
    (hp : 16 ≤ p) (hy : (3 + ε) * (a : ℝ) ^ θ ≤ p) (ha : 1 ≤ a) :
    IsLocalG ((kuhnParams hK ε p (by omega)).rounds2 a) ((kuhnParams hK ε p (by omega)).algorithm2 a) ∧
    ((kuhnParams hK ε p (by omega)).rounds2 a : ℝ) ≤
      (1 / θ + 1) * (Lε ε (Fintype.card V) * (9 * C * (p : ℝ) ^ 2 + 2) + R) ∧
    ∀ G : SimpleGraph V, G.ArboricityLE a →
      IsLegal G ((kuhnParams hK ε p (by omega)).algorithm2 a G) ∧
      ∀ v, ((kuhnParams hK ε p (by omega)).algorithm2 a G v : ℝ) < (3 + ε) ^ (1 / θ + 1) * a := by
  have hp0 : 0 < p := by omega
  set P := kuhnParams hK ε p hp0 with hPdef
  set I := P.iters a with hIdef
  have hε1 : ε ≤ 1 := by linarith
  have hI := iters_lt_of hK hε.le hε1 hθ hp hy
  have hHR : P.HRoundsOK := fun α => hRounds_ok hε _ α
  refine ⟨P.algorithm2_isLocal a, ?_, fun G hG => ?_⟩
  · -- rounds
    set L := Lε ε (Fintype.card V)
    set M := L * (C * (9 * p ^ 2)) + R + 2 * L
    have hle : P.rounds2 a ≤ (I + 1) * M := by
      have h1 : P.legRounds (P.bound a I) ≤ M :=
        legRounds_le hK hp0 hε hε2 hp (bound_iters_le hK hp0 hε.le hε1 (by omega) a)
      have h2 : P.loopRounds a I ≤ I * M := loopRounds_le hK hp0 hε a I
      show P.legRounds (P.bound a I) + P.loopRounds a I ≤ (I + 1) * M
      rw [Nat.succ_mul]
      omega
    have hM : (M : ℝ) = L * (9 * C * (p : ℝ) ^ 2 + 2) + R := by
      simp only [M]; push_cast; ring
    calc (P.rounds2 a : ℝ) ≤ ((I + 1) * M : ℕ) := by exact_mod_cast hle
      _ = ((I : ℝ) + 1) * M := by push_cast; ring
      _ ≤ (1 / θ + 1) * (L * (9 * C * (p : ℝ) ^ 2 + 2) + R) := by
          rw [← hM]
          have : (0 : ℝ) ≤ M := Nat.cast_nonneg _
          gcongr
  · -- correctness and colours
    obtain ⟨hleg, hlt⟩ := P.proc_correct hHR hp0 hG I
    refine ⟨hleg, fun v => ?_⟩
    have h1 : (P.algorithm2 a G v : ℝ) <
        ((p ^ I * (Aε ε (P.bound a I) + 1) : ℕ) : ℝ) := by exact_mod_cast hlt v
    have h2 := colors_le hK hp0 hε.le hε1 a ha
    have h3 : (3 + ε) ^ (I + 1) ≤ (3 + ε) ^ (1 / θ + 1) := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by push_cast; linarith)
    calc (P.algorithm2 a G v : ℝ) < _ := h1
      _ ≤ (3 + ε) ^ (I + 1) * a := h2
      _ ≤ (3 + ε) ^ (1 / θ + 1) * a := by gcongr

/-- **Theorem 4.3.** Assume Lemma 2.1 (`hK`, with constant `C` and `R = O(log* n)` rounds). Let
`0 < ε ≤ 1/2`, `μ > 0`, and let `a` be large enough that `p = ⌊a^{μ/2}⌋ ≥ 16` (the paper's
w.l.o.g. assumption; smaller `a` are constants, handled by Lemma 2.2(1), `legalColoring_spec`).
Procedure Legal-Coloring with parameter `p` computes, on every graph of arboricity `≤ a`, a legal
colouring with fewer than `(3+ε)^{4/μ+1} · a = O(a)` colours. It runs for at most
`(4/μ + 1) · (L · (9C a^μ + 2) + R) = O(a^μ log n)` rounds, where `L = ⌈2/ε⌉(⌊log₂ n⌋ + 1)` is the
number of rounds of an H-partition. -/
theorem theorem_4_3 (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) (hμ : 0 < μ) (hp : 16 ≤ pμ μ a) :
    IsLocalG ((kuhnParams hK ε (pμ μ a) (by omega)).rounds2 a) (theorem43Alg hK ε μ a (by omega)) ∧
    ((kuhnParams hK ε (pμ μ a) (by omega)).rounds2 a : ℝ) ≤
      (4 / μ + 1) * (Lε ε (Fintype.card V) * (9 * C * (a : ℝ) ^ μ + 2) + R) ∧
    ∀ G : SimpleGraph V, G.ArboricityLE a →
      IsLegal G (theorem43Alg hK ε μ a (by omega) G) ∧
      ∀ v, (theorem43Alg hK ε μ a (by omega) G v : ℝ) < (3 + ε) ^ (4 / μ + 1) * a := by
  have ha := one_lt_of_pμ hμ hp
  have hgen := legalColoring_general hK (a := a) hε hε2 (θ := μ / 4) (by positivity) hp
    (mul_rpow_le_pμ hε2 hp) (by exact_mod_cast ha.le)
  rw [one_div_div] at hgen
  obtain ⟨h1, h2, h3⟩ := hgen
  refine ⟨h1, h2.trans ?_, h3⟩
  have hp2 : ((pμ μ a : ℕ) : ℝ) ^ 2 ≤ (a : ℝ) ^ μ := by
    have : ((pμ μ a : ℕ) : ℝ) ≤ (a : ℝ) ^ (μ / 2) := Nat.floor_le (by positivity)
    calc ((pμ μ a : ℕ) : ℝ) ^ 2 ≤ ((a : ℝ) ^ (μ / 2)) ^ 2 :=
          pow_le_pow_left₀ (Nat.cast_nonneg _) this 2
      _ = (a : ℝ) ^ μ := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg a)]; norm_num
  gcongr

end Theorem43

end Podc.ArbdefectiveColoring
