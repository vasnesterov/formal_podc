import Papers.PODC2015.RandomizedPLS.Counterexample
import Papers.PODC2015.RandomizedPLS.Compile

/-!
# Theorems 4.4 and 4.7 and Proposition 4.3 as printed are false

The windmill counterexample (`Counterexample.lean`) satisfies every hypothesis of Theorem 4.4 with
`P(G) = FALSE`, `s = 1`, and has a PLS with `3 + log₂ log₂ r` label bits; compiled by Theorem 3.1 it
gives an edge-independent RPLS (one-sided, hence also two-sided) with `O(log log log r)`-bit
certificates. So:

* `thm_4_4_false`: no bound `κ ≥ C · log₂ r / s - D` (the printed `Ω(log r / s)`) holds;
* `thm_4_7_false`: no bound `κ ≥ C · log₂ log₂ r / s - D` (the printed `Ω(log log r / s)`) holds for
  edge-independent two-sided RPLSs;
* `prop_4_3_false`: with `r = 2^32` and `9`-bit labels (`κ < log r / 2s` holds), for *every* pair
  `i ≠ j` the windmill is rejected while the crossing is accepted (each with its prover's labels).
-/

namespace Podc.RandomizedPLS

open Windmill Filter Topology

/-- Exponentials beat linear functions. -/
lemma exists_lt_mul_two_pow {C : ℝ} (hC : 0 < C) (A B : ℝ) : ∃ m : ℕ, A + B * m < C * 2 ^ m := by
  have h1 : Tendsto (fun n : ℕ => (n : ℝ) ^ 1 / (2 : ℝ) ^ n) atTop (𝓝 0) :=
    tendsto_pow_const_div_const_pow_of_one_lt 1 (by norm_num)
  have h2 : Tendsto (fun n : ℕ => (1 : ℝ) / (2 : ℝ) ^ n) atTop (𝓝 0) := by
    have := tendsto_inv_atTop_zero.comp (tendsto_pow_atTop_atTop_of_one_lt (by norm_num :
      (1 : ℝ) < 2))
    simpa [Function.comp_def, one_div] using this
  have h3 : Tendsto (fun n : ℕ => A * (1 / (2 : ℝ) ^ n) + B * ((n : ℝ) ^ 1 / (2 : ℝ) ^ n)) atTop
      (𝓝 0) := by simpa using (h2.const_mul A).add (h1.const_mul B)
  obtain ⟨m, hm⟩ := (h3.eventually (gt_mem_nhds hC)).exists
  refine ⟨m, ?_⟩
  have hpos : (0 : ℝ) < 2 ^ m := by positivity
  have : (A + B * m) / 2 ^ m < C := by
    convert hm using 1; field_simp
  rwa [div_lt_iff₀ hpos] at this

lemma logb_two_pow_nat (n : ℕ) : Real.logb 2 ((2 ^ n : ℕ) : ℝ) = n := by
  push_cast; rw [Real.logb_pow]; simp

/-- **Theorem 4.4 of [BFP15] as printed** (with `P(G_s) ≠ P(σ^{ij}₁(G)_s)`): the verification
complexity of every PLS is `Ω(log r / s)`, i.e. at least `C · log₂ r / s - D`. -/
def Thm44AsPrinted : Prop :=
  ∃ C D : ℝ, 0 < C ∧ ∀ (S : Type) (F P : Config S → Prop) (ver : Verifier S)
    (prover : ∀ c : Config S, c.V → List Bool) (κ : ℕ),
    IsPLS ver prover F P → LabelBound prover F P (fun _ => κ) →
    ∀ (c : Config S) (r : ℕ) (K : Copies c r), F c → 0 < K.s →
      (∀ i j (hij : i ≠ j), F (K.cross i j hij) ∧ (P c ↔ ¬ P (K.cross i j hij))) →
      C * Real.logb 2 r / K.s ≤ κ + D

/-- The windmill satisfies the hypotheses of Theorem 4.4 with `P(G) = FALSE`. -/
lemma windmill_hyp (r : ℕ) (i j : Fin r) (hij : i ≠ j) :
    Windmill.F (r := r) ((Windmill.K r).cross i j hij) ∧
      (Windmill.P (Windmill.G r) ↔ ¬ Windmill.P ((Windmill.K r).cross i j hij)) :=
  ⟨Or.inr ⟨i, j, hij, rfl⟩, iff_of_false not_P_G (not_not.2 (P_cross hij))⟩

/-- **Theorem 4.4 as printed is false.** -/
theorem thm_4_4_false : ¬ Thm44AsPrinted := by
  rintro ⟨C, D, hC, h⟩
  obtain ⟨m, hm⟩ := exists_lt_mul_two_pow hC (3 + D) 1
  have := h St Windmill.F Windmill.P ver prover (3 + Nat.log 2 (Nat.log 2 (2 ^ 2 ^ m)))
    isPLS labelBound (G (2 ^ 2 ^ m)) (2 ^ 2 ^ m) (K _) (Or.inl rfl) (by rw [K_s]; norm_num)
    (windmill_hyp _)
  rw [K_s, logb_two_pow_nat, Nat.log_pow (by norm_num), Nat.log_pow (by norm_num)] at this
  push_cast at this hm
  linarith

/-- **Theorem 4.7 of [BFP15] as printed** (with `P(G_s) ≠ P(σ₁(G)_s)`): every edge-independent
(two-sided) RPLS has verification complexity `Ω(log log r / s)`. -/
def Thm47AsPrinted : Prop :=
  ∃ C D : ℝ, 0 < C ∧ ∀ (S L : Type) (F P : Config S → Prop) (e : EIScheme S L)
    (prover : ∀ c : Config S, c.V → L) (κ : ℕ),
    IsTwoSided e.toRScheme prover F P → CertBound e.toRScheme prover F P (fun _ => κ) →
    ∀ (c : Config S) (r : ℕ) (K : Copies c r), F c → 0 < K.s →
      (∀ i j (hij : i ≠ j), F (K.cross i j hij) ∧ (P c ↔ ¬ P (K.cross i j hij))) →
      C * Real.logb 2 (Real.logb 2 r) / K.s ≤ κ + D

/-- **Theorem 4.7 as printed is false**: compile the windmill PLS with Theorem 3.1. -/
theorem thm_4_7_false : ¬ Thm47AsPrinted := by
  rintro ⟨C, D, hC, h⟩
  obtain ⟨m, hm⟩ := exists_lt_mul_two_pow hC (10 + D) 2
  set r := 2 ^ 2 ^ 2 ^ m
  obtain ⟨hR, hB⟩ := theorem_3_1 (isPLS (r := r)) labelBound
  have hTwo : IsTwoSided (compileScheme ver).toRScheme (compileProver prover)
      (Windmill.F (r := r)) Windmill.P :=
    ⟨fun c hF hP => le_trans (by norm_num) (hR.1 c hF hP), hR.2⟩
  have := h St _ Windmill.F Windmill.P (compileScheme ver) (compileProver prover)
    (2 * Nat.log 2 (3 + Nat.log 2 (Nat.log 2 r)) + 6) hTwo hB (G r) r (K r) (Or.inl rfl)
    (by rw [K_s]; norm_num) (windmill_hyp r)
  have hlog : Nat.log 2 (Nat.log 2 r) = 2 ^ m := by
    simp only [r]; rw [Nat.log_pow (by norm_num), Nat.log_pow (by norm_num)]
  have hlog2 : Nat.log 2 (3 + 2 ^ m) ≤ m + 2 := by
    have : 3 + 2 ^ m < 2 ^ (m + 3) := by
      have := Nat.one_le_two_pow (n := m); rw [pow_add]; linarith
    have h := Nat.log_lt_of_lt_pow (b := 2) (by positivity : 3 + 2 ^ m ≠ 0) this
    omega
  have hr : Real.logb 2 (Real.logb 2 r) = 2 ^ m := by
    simp only [r]; rw [logb_two_pow_nat]; push_cast; rw [Real.logb_pow]; simp
  rw [K_s, hr, hlog] at this
  have hcast : ((2 * Nat.log 2 (3 + 2 ^ m) + 6 : ℕ) : ℝ) ≤ 2 * m + 10 := by
    have : 2 * Nat.log 2 (3 + 2 ^ m) + 6 ≤ 2 * m + 10 := by omega
    exact_mod_cast this
  push_cast at this hcast hm
  linarith

/-- **Proposition 4.3 of [BFP15] as printed is false** (when `G` is rejected). For `r = 2^32` the
windmill scheme has labels of `κ = 8` bits, so `(2^(κ+1) - 1)^(2s) < r` (and `κ < log r / 2s`),
yet for every pair `i ≠ j` the windmill is rejected and the crossing accepted, each with the labels
its prover assigns. -/
theorem prop_4_3_false :
    let r := 2 ^ 32
    (∀ c, Windmill.F (r := r) c → Windmill.P c → ∀ v, (prover c v).length ≤ 8) ∧
    (2 ^ (8 + 1) - 1) ^ (2 * (K r).s) < r ∧ (8 : ℝ) < Real.logb 2 r / (2 * (K r).s) ∧
    ∀ i j (hij : i ≠ j), ¬ (Accepts ver (G r) (prover (G r)) ↔
      Accepts ver ((K r).cross i j hij) (prover ((K r).cross i j hij))) := by
  intro r
  refine ⟨fun c hF hP v => ?_, ?_, ?_, fun i j hij => ?_⟩
  · have := labelBound (r := r) c hF hP v
    have h5 : Nat.log 2 (Nat.log 2 r) = 5 := by
      simp only [r]
      rw [show (32 : ℕ) = 2 ^ 5 by norm_num, Nat.log_pow (by norm_num), Nat.log_pow (by norm_num)]
    simp only [h5] at this; omega
  · rw [K_s]; norm_num [r]
  · rw [K_s, show r = 2 ^ 32 from rfl, logb_two_pow_nat]; norm_num
  · exact fun hiff => not_accepts_G _ (hiff.2 (accepts_cross hij))

end Podc.RandomizedPLS
