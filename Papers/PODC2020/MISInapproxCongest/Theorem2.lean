import Papers.PODC2020.MISInapproxCongest.Theorem1

/-!
# Theorem 2: `(3/4 + ε)`-approximate MaxIS needs `Ω(n² / (B log n))` rounds

The construction of Section 5 instantiated, as in `Theorem1.lean`, with a Gilbert–Varshamov code
over a constant alphabet and heavy weight `W = M`. The cut has `O(log n)` edges and the strings
have `k² = Θ(n²)` bits, so Corollary 1 gives `T · B = Ω(n² / log n)`, i.e. `T = Ω(n² / log² n)`
for `B = O(log n)` (the paper claims `Ω(n² / log³ n)`).
-/

set_option linter.unusedSectionVars false

namespace Podc.MISInapproxCongest

open Finset Cslib Cslib.Congest Cslib.CommunicationComplexity

/-- Claim 7 with `W = M` in the form used for Theorem 2. -/
theorem quad_hi {t : ℕ} {K P A : Type*} [DecidableEq K] [DecidableEq P] [DecidableEq A]
    [Fintype K] [Fintype P] [Fintype A] {c : K → P → A} {a W : ℕ}
    (hc : ∀ m m', m ≠ m' → agree (c m) (c m') ≤ a) (hW : W = Fintype.card P)
    {x : Fin t → K × K → Bool} (hx : PairwiseDisjoint x) {I : Finset (Node2 t K P A)}
    (hI : IsIndep (graph2 c x) I) :
    wsum (weight2 W) I ≤ (3 * t + 1) * W + a * t ^ 2 := by
  obtain ⟨p, hp, h⟩ := claim7_generic (W := W) hc hx hI
  rw [← hW] at h
  refine h.trans ?_
  have hC := two_mul_choose_two p
  have : p * (p - 1) ≤ t * t := Nat.mul_le_mul hp (by omega)
  have hC' : 2 * a * p.choose 2 ≤ a * t ^ 2 := by
    have : 2 * p.choose 2 ≤ t ^ 2 := by rw [hC, sq]; exact this
    calc 2 * a * p.choose 2 = a * (2 * p.choose 2) := by ring
      _ ≤ a * t ^ 2 := Nat.mul_le_mul_left _ this
  obtain ⟨d, rfl⟩ : ∃ d, t = p + d := ⟨t - p, by omega⟩
  rw [show p + d - p = d by omega]
  nlinarith

/-- The gap of Theorem 2: `(3t + 1) M + a t² < (3/4 + ε) · 4tM`. -/
theorem quad_gap {ε : ℝ} (hε : 0 < ε) {t D M a : ℕ} (hεt : 1 ≤ ε * t) (hDr : 2 * t / ε ≤ D)
    (haD : a * D ≤ M) (hM : 2 / ε < M) :
    (((3 * t + 1) * M + a * t ^ 2 : ℕ) : ℝ) < (3 / 4 + ε) * ((2 * (t * (M + M)) : ℕ) : ℝ) := by
  have haD' : (a : ℝ) * D ≤ M := by exact_mod_cast haD
  have hat : (a : ℝ) * (2 * t) ≤ ε * M := by
    have : (a : ℝ) * (2 * t / ε) ≤ a * D := mul_le_mul_of_nonneg_left hDr (by positivity)
    rw [mul_div_assoc', div_le_iff₀ hε] at this
    nlinarith
  have hMpos : (0 : ℝ) < M := lt_of_le_of_lt (by positivity) hM
  push_cast
  nlinarith [mul_le_mul_of_nonneg_left hεt hMpos.le, mul_le_mul_of_nonneg_right hat
    (show (0 : ℝ) ≤ t by positivity), mul_pos (mul_pos hε hMpos) (show (0 : ℝ) < t by
      have := hεt; by_contra h; push Not at h; nlinarith)]

set_option maxHeartbeats 1000000 in
/-- **Theorem 2** (repaired; conditional on the Chakrabarti–Khot–Sun bound `PPDLowerBound c`,
Theorem 3 of the paper). For every `ε > 0` there is `C > 0` such that for infinitely many `n` there
is a node set `V` of size `n` on which every randomized CONGEST algorithm with `B`-bit messages that
finds a `(3/4 + ε)`-approximate maximum weight independent set with probability `≥ 2/3` on every
weighted graph on `V` within `T` rounds satisfies `T · B · log n ≥ C · n²`. With `B = O(log n)`
this gives `T = Ω(n² / log² n)`, which implies the paper's `Ω(n² / log³ n)`. -/
theorem theorem2 {c : ℝ} (hc : 0 < c) (hCC : PPDLowerBound c) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V),
      N ≤ Fintype.card V ∧ ∀ {σ ρ : Type} [Fintype ρ] [Nonempty ρ] (B T : ℕ)
        (A : Algorithm V (ℕ × ρ) σ B), ApproxMIS A (3 / 4 + ε) T (1 / 3) →
          C * (Fintype.card V : ℝ) ^ 2 ≤ T * B * Real.log (Fintype.card V) := by
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
  set L : ℕ := Nat.clog 2 (4 * t)
  set lg : ℝ := Real.logb 2 t
  have hlg : 1 ≤ lg := by
    rw [show (1 : ℝ) = Real.logb 2 2 by simp]
    exact Real.logb_le_logb_of_le (by norm_num) (by norm_num) (by exact_mod_cast (by omega : 2 ≤ t))
  have htr : (3 : ℝ) ≤ t := by exact_mod_cast ht3
  set G : ℝ := 2 * t * t * Q * Q
  have hG : 0 < G := by positivity
  set H : ℝ := 16 * t * t * (t * lg) / c
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
  have hcardV : Fintype.card (Node2 t K (Fin M) (Fin Q)) = t * (2 * (2 ^ M + M * Q)) := by
    simp [Node2, hK]
  have h2M : 2 ^ M ≤ Fintype.card (Node2 t K (Fin M) (Fin Q)) := by
    rw [hcardV]; nlinarith [Nat.zero_le (M * Q)]
  have hMQ2 : M * Q ≤ 2 ^ M := by
    have := mul_succ_le_two_pow (C := Q) hM6 hMQ; nlinarith
  have hcardV2 : Fintype.card (Node2 t K (Fin M) (Fin Q)) ≤ 4 * t * 2 ^ M := by
    rw [hcardV]
    calc t * (2 * (2 ^ M + M * Q)) ≤ t * (2 * (2 ^ M + 2 ^ M)) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (by omega))
      _ = 4 * t * 2 ^ M := by ring
  refine ⟨Node2 t K (Fin M) (Fin Q), inferInstance, inferInstance,
    hMN.trans ((Nat.lt_two_pow_self).le.trans h2M), ?_⟩
  intro σ ρ _ _ B T A hA
  -- Corollary 1 for the family
  have hW1 : 1 ≤ M := by omega
  have hWle : ∀ x v, (quadFamily (t := t) cd M).inp x v ≤ M := fun x v => by
    rcases v with ⟨i, b, m | hr⟩ <;> simp only [quadFamily, weight2] <;> omega
  have hMn : M ≤ Fintype.card _ := (Nat.lt_two_pow_self).le.trans h2M
  have key := corollary1 (V := Node2 t K (Fin M) (Fin Q)) (σ := σ) (ρ := ρ) (B := B) hCC
    (quadFamily (t := t) cd M) (by omega) (2 * (t * (M + M))) ((3 * t + 1) * M + a * t ^ 2) M
    (3 / 4 + ε)
    (fun x ⟨⟨m₁, m₂⟩, hm⟩ => by
      obtain ⟨h1, h2⟩ := claim6_generic (c := cd) (W := M) (x := x) hm
      exact ⟨_, h1, by simp only [quadFamily] at *; rw [h2, Fintype.card_fin]⟩)
    (fun x hx I hI => quad_hi hcd (by simp) hx hI)
    (quad_gap hε hεt hDr (Nat.div_mul_le_self M D) hMεr)
    hWle
    A T (fun x => hA _ _ fun v => (hWle x v).trans hMn)
  rw [Fintype.card_prod, hK, ← pow_two, ← pow_mul] at key
  -- the additive term
  set n := Fintype.card (Node2 t K (Fin M) (Fin Q))
  have hclog : Nat.clog 2 (n * M + 1) ≤ L + 2 * M := by
    rw [Nat.clog_le_iff_le_pow (by norm_num)]
    have h2t : 4 * t ≤ 2 ^ L := Nat.le_pow_clog (by norm_num) _
    have hM1 : M + 1 ≤ 2 ^ M := by simpa using mul_succ_le_two_pow (C := 1) hM6 (by omega)
    have hn1 : 1 ≤ n := le_trans (Nat.one_le_two_pow) h2M
    calc n * M + 1 ≤ n * (M + 1) := by rw [Nat.mul_succ]; omega
      _ ≤ (2 ^ L * 2 ^ M) * 2 ^ M := Nat.mul_le_mul (hcardV2.trans (Nat.mul_le_mul_right _ h2t)) hM1
      _ = 2 ^ (L + 2 * M) := by ring
  set X : ℝ := c * (2 ^ (M * 2) : ℕ) / (t * lg)
  have hX : 0 < X := by positivity
  have hS : ((t * Nat.clog 2 (n * M + 1) : ℕ) : ℝ) ≤ X / 2 := by
    have h2 : (C₁ : ℝ) * (M + 1) ≤ (2 ^ (M * 2) : ℕ) := by
      exact_mod_cast (mul_succ_le_two_pow hM6 hMC).trans (Nat.pow_le_pow_right (by norm_num) (by omega))
    have h3 : 4 * t * t * lg * (L + 1) / c ≤ C₁ := by
      have := Nat.le_ceil (4 * (t : ℝ) * t * lg * (L + 1) / c)
      simp only [C₁]; push_cast; linarith
    push_cast
    exact summary_le (M := (M : ℝ)) (L := (L : ℝ)) (C₁ := (C₁ : ℝ)) hc (by positivity) (by positivity) (by positivity)
      (by positivity) (by exact_mod_cast hclog) (by exact_mod_cast h2) h3
  have hE : (((quadFamily (t := t) cd M).Ecut.card : ℕ) : ℝ) ≤ G * M := by
    rw [card_quadFamily_Ecut, Fintype.card_fin, Fintype.card_fin]
    have : 2 * ((t * t - t) * (M * (Q * Q - Q))) ≤ 2 * t * t * Q * Q * M := by
      calc 2 * ((t * t - t) * (M * (Q * Q - Q))) ≤ 2 * ((t * t) * (M * (Q * Q))) :=
            Nat.mul_le_mul_left _
              (Nat.mul_le_mul (Nat.sub_le _ _) (Nat.mul_le_mul_left _ (Nat.sub_le _ _)))
        _ = 2 * t * t * Q * Q * M := by ring
    calc (((2 * ((t * t - t) * (M * (Q * Q - Q))) : ℕ)) : ℝ) ≤
        ((2 * t * t * Q * Q * M : ℕ) : ℝ) := by
          exact_mod_cast this
      _ = G * M := by simp only [G]; push_cast; ring
  have hlog : (M : ℝ) * Real.log 2 ≤ Real.log n := by
    rw [← Real.log_pow]
    exact Real.log_le_log (by positivity) (by exact_mod_cast h2M)
  have hn : (n : ℝ) ^ 2 ≤ H * X := by
    have : (n : ℝ) ≤ 4 * t * (2 ^ M : ℕ) := by exact_mod_cast hcardV2
    have h0 : (0 : ℝ) ≤ n := by positivity
    refine (pow_le_pow_left₀ h0 this 2).trans (le_of_eq ?_)
    simp only [H, X]
    field_simp
    push_cast
    ring
  have hY : (0 : ℝ) ≤ T * B := by positivity
  have hcc : X ≤ (T * B : ℝ) * ((quadFamily (t := t) cd M).Ecut.card : ℕ) +
      ((t * Nat.clog 2 (n * M + 1) : ℕ) : ℝ) := by
    refine key.trans (le_of_eq ?_)
    push_cast; ring
  have := final_arith hY hcc hS hE hG hlog (by positivity) hn hH
  exact this

end Podc.MISInapproxCongest
