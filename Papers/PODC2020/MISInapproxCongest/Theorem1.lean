import Papers.PODC2020.MISInapproxCongest.Families

/-!
# Theorem 1: `(1/2 + ε)`-approximate MaxIS needs `Ω(n / (B log n))` rounds

We instantiate the construction of Section 4 not with the Reed–Solomon code of the paper (whose
alphabet has size `ℓ + α ≈ log k`, giving `Θ(log³ k)` cut edges) but with a code over a
**constant** alphabet (`Q = 4^D` symbols, length `M`, `2^M` codewords, pairwise agreement
`≤ M / D`; Gilbert–Varshamov, `Cslib.exists_code_agree_le`), and heavy weight `W = M`. Then the
cut has `O(log n)` edges and Corollary 1 gives `T · B = Ω(n / log n)`; with `B = O(log n)` this is
`T = Ω(n / log² n)`, stronger than the paper's claim `Ω(n / log³ n)`.

The Chakrabarti–Khot–Sun bound enters as the hypothesis `PPDLowerBound c`.
-/

set_option linter.unusedSectionVars false

namespace Podc.MISInapproxCongest

open Finset Cslib Cslib.Congest Cslib.CommunicationComplexity

/-- `(M + 1)² ≤ 2^M` for `M ≥ 6`. -/
theorem sq_succ_le_two_pow {M : ℕ} (hM : 6 ≤ M) : (M + 1) ^ 2 ≤ 2 ^ M := by
  induction M, hM using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    have : 2 ^ (n + 1) = 2 * 2 ^ n := by ring
    rw [this]
    nlinarith

/-- `C (M + 1) ≤ 2^M` for `M ≥ max 6 C`. -/
theorem mul_succ_le_two_pow {C M : ℕ} (hM : 6 ≤ M) (hC : C ≤ M) : C * (M + 1) ≤ 2 ^ M :=
  le_trans (Nat.mul_le_mul_right _ (by omega)) ((sq (M + 1)).symm ▸ sq_succ_le_two_pow hM)

/-- Claim 5 with `W = M` in the form used for Theorem 1. -/
theorem lin_hi {t : ℕ} {K P A : Type*} [DecidableEq K] [DecidableEq P] [DecidableEq A]
    [Fintype K] [Fintype P] [Fintype A] {c : K → P → A} {a W : ℕ}
    (hc : ∀ m m', m ≠ m' → agree (c m) (c m') ≤ a) (hW : W = Fintype.card P) (hM : 1 ≤ W)
    {x : Fin t → K → Bool} (hx : PairwiseDisjoint x) {I : Finset (Node t K P A)}
    (hI : IsIndep (graph c) I) :
    wsum (weight W x) I ≤ (t + 1) * W + a * t ^ 2 + t := by
  obtain ⟨p, hp, h⟩ := claim5_generic hc hM hx hI
  rw [← hW] at h
  refine h.trans ?_
  have hC : p.choose 2 ≤ t ^ 2 := by
    have := two_mul_choose_two p
    have : p * (p - 1) ≤ t * t := Nat.mul_le_mul hp (by omega)
    nlinarith
  have hC' : a * p.choose 2 ≤ a * t ^ 2 := Nat.mul_le_mul_left _ hC
  obtain ⟨d, rfl⟩ : ∃ d, t = p + d := ⟨t - p, by omega⟩
  rw [show p + d - p = d by omega]
  split_ifs with h0
  · subst h0; nlinarith
  · nlinarith

/-- Real-number glue for the final bound. -/
theorem final_arith {X Y E S G H M l2 Ln n : ℝ} (hY : 0 ≤ Y)
    (hcc : X ≤ Y * E + S) (hS : S ≤ X / 2) (hE : E ≤ G * M) (hG : 0 < G)
    (hlog : M * l2 ≤ Ln) (hl2 : 0 < l2) (hn : n ≤ H * X) (hH : 0 < H) :
    l2 / (2 * G * H) * n ≤ Y * Ln := by
  have h1 : X / 2 ≤ Y * (G * M) := by nlinarith [mul_le_mul_of_nonneg_left hE hY]
  have h2 : Y * M * l2 ≤ Y * Ln := by nlinarith [mul_le_mul_of_nonneg_left hlog hY]
  rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  have h3 : l2 * n ≤ l2 * (H * X) := mul_le_mul_of_nonneg_left hn hl2.le
  have h4 : X ≤ 2 * (Y * (G * M)) := by linarith
  have h5 : l2 * (H * X) ≤ l2 * H * (2 * (Y * (G * M))) := by
    rw [← mul_assoc]; exact mul_le_mul_of_nonneg_left h4 (by positivity)
  have h6 : Y * M * l2 * (2 * G * H) ≤ Y * Ln * (2 * G * H) :=
    mul_le_mul_of_nonneg_right h2 (by positivity)
  nlinarith


/-- The gap of Theorem 1: `(t + 1) M + a t² + t < (1/2 + ε) · 2tM`. -/
theorem lin_gap {ε : ℝ} (hε : 0 < ε) {t D M a : ℕ} (hεt : 1 ≤ ε * t) (hDr : 2 * t / ε ≤ D)
    (haD : a * D ≤ M) (hM : 2 / ε < M) :
    (((t + 1) * M + a * t ^ 2 + t : ℕ) : ℝ) < (1 / 2 + ε) * ((t * (M + M) : ℕ) : ℝ) := by
  have haD' : (a : ℝ) * D ≤ M := by exact_mod_cast haD
  have hat : (a : ℝ) * (2 * t) ≤ ε * M := by
    have : (a : ℝ) * (2 * t / ε) ≤ a * D := mul_le_mul_of_nonneg_left hDr (by positivity)
    rw [mul_div_assoc', div_le_iff₀ hε] at this
    nlinarith
  have hMpos : (0 : ℝ) < M := lt_of_le_of_lt (by positivity) hM
  have h1 : (2 : ℝ) < ε * M := by rwa [div_lt_iff₀ hε, mul_comm] at hM
  push_cast
  nlinarith [mul_le_mul_of_nonneg_left hεt hMpos.le, mul_le_mul_of_nonneg_right hat
    (show (0 : ℝ) ≤ t by positivity)]

/-- The additive term of Corollary 1 is at most half of the main term. -/
theorem summary_le {c t lg L M C₁ P2 cl : ℝ} (hc : 0 < c) (ht : 0 ≤ t)
    (hL : 0 ≤ L) (hM : 0 ≤ M) (htlg : 0 < t * lg) (hcl : cl ≤ L + 2 * M)
    (h2 : C₁ * (M + 1) ≤ P2) (h3 : 4 * t * t * lg * (L + 1) / c ≤ C₁) :
    t * cl ≤ c * P2 / (t * lg) / 2 := by
  rw [div_le_iff₀ hc] at h3
  rw [div_div, le_div_iff₀ (by positivity)]
  have h1 : t * cl ≤ t * (2 * (L + 1) * (M + 1)) :=
    mul_le_mul_of_nonneg_left (by nlinarith) ht
  have h4 : 4 * t * t * lg * (L + 1) * (M + 1) ≤ C₁ * c * (M + 1) :=
    mul_le_mul_of_nonneg_right h3 (by positivity)
  have h5 : C₁ * c * (M + 1) ≤ c * P2 := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left h1 (show (0 : ℝ) ≤ t * lg * 2 by positivity)]

set_option maxHeartbeats 1000000 in
/-- **Theorem 1** (repaired; conditional on the Chakrabarti–Khot–Sun bound `PPDLowerBound c`,
Theorem 3 of the paper). For every `ε > 0` there is `C > 0` such that for infinitely many `n` there
is a node set `V` of size `n` on which every randomized CONGEST algorithm with `B`-bit messages that
finds a `(1/2 + ε)`-approximate maximum weight independent set with probability `≥ 2/3` on every
weighted graph on `V` within `T` rounds satisfies `T · B · log n ≥ C · n`. With `B = O(log n)` this
gives `T = Ω(n / log² n)`, which implies the paper's `Ω(n / log³ n)`. -/
theorem theorem1 {c : ℝ} (hc : 0 < c) (hCC : PPDLowerBound c) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V),
      N ≤ Fintype.card V ∧ ∀ {σ ρ : Type} [Fintype ρ] [Nonempty ρ] (B T : ℕ)
        (A : Algorithm V (ℕ × ρ) σ B), ApproxMIS A (1 / 2 + ε) T (1 / 3) →
          C * Fintype.card V ≤ T * B * Real.log (Fintype.card V) := by
  classical
  -- parameters
  set t : ℕ := ⌈1 / ε⌉₊ + 3 with ht_def
  have ht3 : 3 ≤ t := by omega
  have hεt : 1 ≤ ε * t := by
    have : 1 / ε ≤ ⌈1 / ε⌉₊ := Nat.le_ceil _
    rw [div_le_iff₀ hε] at this
    have : (⌈1 / ε⌉₊ : ℝ) ≤ t := by simp [ht_def]
    nlinarith
  set D : ℕ := ⌈2 * t / ε⌉₊ + 2 with hD_def
  have hD2 : 2 ≤ D := by omega
  have hDr : 2 * t / ε ≤ D := by
    have := Nat.le_ceil (2 * (t : ℝ) / ε)
    have : (⌈2 * (t : ℝ) / ε⌉₊ : ℝ) ≤ D := by simp [hD_def]
    linarith
  set Q : ℕ := 4 ^ D
  have hQ : 1 ≤ Q := Nat.one_le_pow _ _ (by norm_num)
  set L : ℕ := Nat.clog 2 (2 * t)
  set lg : ℝ := Real.logb 2 t
  have hlg : 1 ≤ lg := by
    rw [show (1 : ℝ) = Real.logb 2 2 by simp]
    exact Real.logb_le_logb_of_le (by norm_num) (by norm_num) (by exact_mod_cast (by omega : 2 ≤ t))
  have htr : (3 : ℝ) ≤ t := by exact_mod_cast ht3
  set G : ℝ := t * t * Q * Q
  have hG : 0 < G := by positivity
  set H : ℝ := 2 * t * (t * lg) / c
  have hH : 0 < H := by positivity
  refine ⟨Real.log 2 / (2 * G * H), by positivity, fun N => ?_⟩
  set C₁ : ℕ := ⌈4 * t * t * lg * (L + 1) / c⌉₊ + 1
  set M : ℕ := max (max (max 6 Q) (max C₁ (⌈2 / ε⌉₊ + 1))) (max D N) with hM_def
  have hM6 : 6 ≤ M := by omega
  have hMQ : Q ≤ M := by omega
  have hMC : C₁ ≤ M := by omega
  have hMε : ⌈2 / ε⌉₊ + 1 ≤ M := by omega
  have hMN : N ≤ M := by omega
  have hMεr : 2 / ε < M := by
    have := Nat.le_ceil (2 / ε)
    have : ((⌈2 / ε⌉₊ + 1 : ℕ) : ℝ) ≤ M := by exact_mod_cast hMε
    push_cast at this
    linarith
  set a : ℕ := M / D
  have ha1 : a + 1 ≤ M := by
    have : a ≤ M / 2 := Nat.div_le_div_left hD2 (by norm_num)
    omega
  have hq : 4 ^ M ≤ Q ^ (a + 1) := by
    rw [← pow_mul]
    exact Nat.pow_le_pow_right (by norm_num) (Nat.lt_mul_div_succ M (by omega)).le
  obtain ⟨cd₀, hcd₀⟩ := exists_code_agree_le (P := Fin M) (A := Fin Q) a (by simpa using ha1)
    (by simpa using hq)
  let cd : Fin (2 ^ M) → Fin M → Fin Q := fun m => cd₀ (Fin.cast (by simp) m)
  have hcd : ∀ m m', m ≠ m' → agree (cd m) (cd m') ≤ a := fun m m' h =>
    hcd₀ _ _ fun e => h (Fin.cast_injective _ e)
  -- the vertex set
  let K := Fin (2 ^ M)
  have hK : Fintype.card K = 2 ^ M := by simp [K]
  have hcardV : Fintype.card (Node t K (Fin M) (Fin Q)) = t * (2 ^ M + M * Q) := by
    simp [Node, hK]
  have h2M : 2 ^ M ≤ Fintype.card (Node t K (Fin M) (Fin Q)) := by
    rw [hcardV]; nlinarith [Nat.zero_le (M * Q)]
  have hMQ2 : M * Q ≤ 2 ^ M := by
    have := mul_succ_le_two_pow (C := Q) hM6 hMQ; nlinarith
  have hcardV2 : Fintype.card (Node t K (Fin M) (Fin Q)) ≤ 2 * t * 2 ^ M := by
    rw [hcardV]
    calc t * (2 ^ M + M * Q) ≤ t * (2 ^ M + 2 ^ M) := Nat.mul_le_mul_left _ (by omega)
      _ = 2 * t * 2 ^ M := by ring
  refine ⟨Node t K (Fin M) (Fin Q), inferInstance, inferInstance,
    hMN.trans ((Nat.lt_two_pow_self).le.trans h2M), ?_⟩
  intro σ ρ _ _ B T A hA
  -- Corollary 1 for the family
  have hW1 : 1 ≤ M := by omega
  have hWle : ∀ x v, (linFamily (t := t) cd M).inp x v ≤ M := fun x v => by
    rcases v with ⟨i, m | hr⟩ <;> simp only [linFamily, weight] <;> (try split_ifs) <;> omega
  have hMn : M ≤ Fintype.card _ := (Nat.lt_two_pow_self).le.trans h2M
  have key := corollary1 (V := Node t K (Fin M) (Fin Q)) (σ := σ) (ρ := ρ) (B := B) hCC
    (linFamily (t := t) cd M) (by omega) (t * (M + M)) ((t + 1) * M + a * t ^ 2 + t) M
    (1 / 2 + ε)
    (fun x ⟨m, hm⟩ => by
      obtain ⟨h1, h2⟩ := claim3_generic (c := cd) (W := M) (x := x) hm
      exact ⟨_, h1, by simp only [linFamily] at *; rw [h2, Fintype.card_fin]⟩)
    (fun x hx I hI => lin_hi hcd (by simp) hW1 hx hI)
    (lin_gap hε hεt hDr (Nat.div_mul_le_self M D) hMεr)
    hWle
    A T (fun x => hA _ _ fun v => (hWle x v).trans hMn)
  rw [hK] at key
  -- the additive term
  set n := Fintype.card (Node t K (Fin M) (Fin Q))
  have hclog : Nat.clog 2 (n * M + 1) ≤ L + 2 * M := by
    rw [Nat.clog_le_iff_le_pow (by norm_num)]
    have h2t : 2 * t ≤ 2 ^ L := Nat.le_pow_clog (by norm_num) _
    have hM1 : M + 1 ≤ 2 ^ M := by simpa using mul_succ_le_two_pow (C := 1) hM6 (by omega)
    have hn1 : 1 ≤ n := le_trans (Nat.one_le_two_pow) h2M
    calc n * M + 1 ≤ n * (M + 1) := by rw [Nat.mul_succ]; omega
      _ ≤ (2 ^ L * 2 ^ M) * 2 ^ M := Nat.mul_le_mul (hcardV2.trans (Nat.mul_le_mul_right _ h2t)) hM1
      _ = 2 ^ (L + 2 * M) := by ring
  set X : ℝ := c * (2 ^ M : ℕ) / (t * lg)
  have hX : 0 < X := by positivity
  have hS : ((t * Nat.clog 2 (n * M + 1) : ℕ) : ℝ) ≤ X / 2 := by
    have h2 : (C₁ : ℝ) * (M + 1) ≤ (2 ^ M : ℕ) := by exact_mod_cast mul_succ_le_two_pow hM6 hMC
    have h3 : 4 * t * t * lg * (L + 1) / c ≤ C₁ := by
      have := Nat.le_ceil (4 * (t : ℝ) * t * lg * (L + 1) / c)
      simp only [C₁]; push_cast; linarith
    push_cast
    exact summary_le (M := (M : ℝ)) (L := (L : ℝ)) (C₁ := (C₁ : ℝ)) hc (by positivity) (by positivity) (by positivity)
      (by positivity) (by exact_mod_cast hclog) (by exact_mod_cast h2) h3
  have hE : (((linFamily (t := t) cd M).Ecut.card : ℕ) : ℝ) ≤ G * M := by
    rw [card_linFamily_Ecut, Fintype.card_fin, Fintype.card_fin]
    have : (t * t - t) * (M * (Q * Q - Q)) ≤ t * t * Q * Q * M := by
      calc (t * t - t) * (M * (Q * Q - Q)) ≤ (t * t) * (M * (Q * Q)) :=
            Nat.mul_le_mul (Nat.sub_le _ _) (Nat.mul_le_mul_left _ (Nat.sub_le _ _))
        _ = t * t * Q * Q * M := by ring
    calc ((((t * t - t) * (M * (Q * Q - Q)) : ℕ)) : ℝ) ≤ ((t * t * Q * Q * M : ℕ) : ℝ) := by
          exact_mod_cast this
      _ = G * M := by simp only [G]; push_cast; ring
  have hlog : (M : ℝ) * Real.log 2 ≤ Real.log n := by
    rw [← Real.log_pow]
    exact Real.log_le_log (by positivity) (by exact_mod_cast h2M)
  have hn : (n : ℝ) ≤ H * X := by
    have : (n : ℝ) ≤ 2 * t * (2 ^ M : ℕ) := by exact_mod_cast hcardV2
    refine this.trans (le_of_eq ?_)
    simp only [H, X]
    field_simp
  have hY : (0 : ℝ) ≤ T * B := by positivity
  have hcc : X ≤ (T * B : ℝ) * ((linFamily (t := t) cd M).Ecut.card : ℕ) +
      ((t * Nat.clog 2 (n * M + 1) : ℕ) : ℝ) := by
    refine key.trans (le_of_eq ?_)
    push_cast; ring
  have := final_arith hY hcc hS hE hG hlog (by positivity) hn hH
  exact this

end Podc.MISInapproxCongest
