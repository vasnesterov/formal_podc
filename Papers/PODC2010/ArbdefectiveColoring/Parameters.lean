import Papers.PODC2010.ArbdefectiveColoring.Recursive

/-!
# The paper's parameters: `A = ⌊(2+ε)a⌋`, `L = O(log n)`, and the black box of Lemma 2.1

* `Aε ε α = ⌊(2+ε)α⌋` (the degree of the H-partition, Lemma 2.3) and
  `Lε ε n = ⌈2/ε⌉ · (⌊log₂ n⌋ + 1)` (its number of rounds); `hRounds_ok`: these satisfy the
  termination condition `n (2α)^L < (A+1)^L` of the H-partition for every `α` (Lemma 2.3).
* `Lemma21 V C R`: the black box of **Lemma 2.1** (Kuhn, SPAA'09): for every degree bound `Δ` and
  every `q > 0`, an `R`-round algorithm computing a `⌊Δ/q⌋`-defective colouring with fewer than
  `C q²` colours (in the paper `R = O(log* n)`). It is a hypothesis of the theorems below; it is
  satisfiable (`Lemma21.satisfiable` in `NonVacuity.lean`).
* `corollary_3_6`: **Corollary 3.6** in the paper's form: a `⌊a/t + (2+ε)a/k⌋`-arbdefective
  `k`-colouring in `L(9Ct² ) + R + L = O(t² log n)` rounds (`0 < ε ≤ 1`).
* `corollary_3_4`: **Corollary 3.4**: a `⌊(2+ε)a⌋/k`-arbdefective `k`-colouring, via the complete
  orientation of Lemma 3.3.
-/

open Finset Cslib.Local

namespace Podc.ArbdefectiveColoring

open scoped Classical

set_option linter.unusedSectionVars false

variable {V : Type*} [Fintype V]

/-- The degree of the H-partition for arboricity bound `α`: `⌊(2+ε)α⌋`. -/
noncomputable def Aε (ε : ℝ) (α : ℕ) : ℕ := ⌊(2 + ε) * α⌋₊

/-- The number of rounds of the H-partition: `⌈2/ε⌉ · (⌊log₂ n⌋ + 1) = O(log n)`. -/
noncomputable def Lε (ε : ℝ) (n : ℕ) : ℕ := ⌈2 / ε⌉₊ * (Nat.log 2 n + 1)

lemma one_le_Lε {ε : ℝ} (hε : 0 < ε) (n : ℕ) : 1 ≤ Lε ε n :=
  Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (Nat.ceil_pos.2 (by positivity)).ne' (by omega))

lemma Aε_le {ε : ℝ} (hε : 0 ≤ ε) (α : ℕ) : (Aε ε α : ℝ) ≤ (2 + ε) * α :=
  Nat.floor_le (by positivity)

/-- With `A = ⌊(2+ε)α⌋` and `L = ⌈2/ε⌉(⌊log₂ n⌋ + 1)`, the H-partition algorithm terminates:
`n (2α)^L < (A+1)^L`. -/
lemma hRounds_ok {ε : ℝ} (hε : 0 < ε) (n α : ℕ) :
    n * (2 * α) ^ Lε ε n < (Aε ε α + 1) ^ Lε ε n := by
  set m := ⌈2 / ε⌉₊
  set k := Nat.log 2 n + 1
  have hm : 1 ≤ m := Nat.one_le_iff_ne_zero.2 (Nat.ceil_pos.2 (by positivity)).ne'
  have hL : Lε ε n = m * k := rfl
  have hL1 : 1 ≤ m * k := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
  rw [hL]
  rcases Nat.eq_zero_or_pos α with rfl | hα
  · simp [zero_pow (by omega : m * k ≠ 0)]
  · have h1 : (2 * α : ℝ) * (1 + ε / 2) < (Aε ε α : ℝ) + 1 := by
      have := Nat.lt_floor_add_one ((2 + ε) * (α : ℝ))
      simp only [Aε]
      linarith
    have h2 : (2 : ℝ) ≤ (1 + ε / 2) ^ m := by
      have hb := one_add_mul_le_pow (show (-2 : ℝ) ≤ ε / 2 by linarith) m
      have hc : (2 / ε : ℝ) ≤ m := Nat.le_ceil _
      have : (1 : ℝ) ≤ m * (ε / 2) := by
        rw [div_le_iff₀ hε] at hc
        linarith
      linarith
    have h3 : (n : ℝ) < 2 ^ k := by exact_mod_cast Nat.lt_pow_succ_log_self (by norm_num) n
    have h4 : (n : ℝ) < (1 + ε / 2) ^ (m * k) :=
      h3.trans_le (by rw [pow_mul]; exact pow_le_pow_left₀ (by norm_num) h2 k)
    have hpos : (0 : ℝ) < (2 * α) ^ (m * k) := by positivity
    have : (n : ℝ) * (2 * α) ^ (m * k) < ((Aε ε α : ℝ) + 1) ^ (m * k) :=
      calc (n : ℝ) * (2 * α) ^ (m * k) < (1 + ε / 2) ^ (m * k) * (2 * α) ^ (m * k) :=
            mul_lt_mul_of_pos_right h4 hpos
        _ = ((2 * α) * (1 + ε / 2)) ^ (m * k) := by rw [← mul_pow, mul_comm (1 + ε / 2)]
        _ ≤ ((Aε ε α : ℝ) + 1) ^ (m * k) := pow_le_pow_left₀ (by positivity) h1.le _
    exact_mod_cast this

/-- **Lemma 2.1** (Kuhn, SPAA'09) as a hypothesis, with explicit constant `C` and round bound `R`
(`R = O(log* n)` in [Kuhn]): for every degree bound `Δ` and every `q > 0` there is an `R`-round
algorithm computing, on every graph of maximum degree `≤ Δ`, a `⌊Δ/q⌋`-defective colouring with
fewer than `C q²` colours. -/
def Lemma21 (V : Type*) [Fintype V] (C R : ℕ) : Prop :=
  ∀ Δ q : ℕ, 0 < q → Nonempty (DefectiveAlg V Δ (Δ / q) (C * q ^ 2) R)

/-- A legal colouring algorithm from Lemma 2.1 (with `q = Δ + 1`). -/
noncomputable def Lemma21.legal {C R : ℕ} (hK : Lemma21 V C R) (Δ : ℕ) :
    DefectiveAlg V Δ 0 (C * (Δ + 1) ^ 2) R :=
  (Nat.div_eq_of_lt (Nat.lt_succ_self Δ)) ▸ Classical.choice (hK Δ (Δ + 1) (Nat.succ_pos Δ))

/-- The defective colouring algorithm of Lemma 2.1 with parameter `q`. -/
noncomputable def Lemma21.alg {C R : ℕ} (hK : Lemma21 V C R) (Δ q : ℕ) (hq : 0 < q) :
    DefectiveAlg V Δ (Δ / q) (C * q ^ 2) R :=
  Classical.choice (hK Δ q hq)

/-- `⌊A/(3t)⌋ + ⌊A/k⌋ ≤ ⌊a/t + (2+ε)a/k⌋` for `A = ⌊(2+ε)a⌋` and `ε ≤ 1`. -/
lemma defect_le {ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (a t k : ℕ) :
    Aε ε a / (3 * t) + Aε ε a / k ≤ ⌊(a : ℝ) / t + (2 + ε) * a / k⌋₊ := by
  apply Nat.le_floor
  have hA := Aε_le hε a
  have h1 : (Aε ε a / (3 * t) : ℕ) ≤ a / t := by
    have : Aε ε a ≤ 3 * a := by
      have : (Aε ε a : ℝ) ≤ 3 * a := hA.trans (by nlinarith [(Nat.cast_nonneg a : (0:ℝ) ≤ a)])
      exact_mod_cast this
    calc Aε ε a / (3 * t) ≤ 3 * a / (3 * t) := Nat.div_le_div_right this
      _ = a / t := Nat.mul_div_mul_left a t (by norm_num)
  have h1' : ((Aε ε a / (3 * t) : ℕ) : ℝ) ≤ (a : ℝ) / t :=
    (Nat.cast_le.2 h1).trans (Nat.cast_div_le)
  have h2 : ((Aε ε a / k : ℕ) : ℝ) ≤ (2 + ε) * a / k :=
    Nat.cast_div_le.trans (div_le_div_of_nonneg_right hA (Nat.cast_nonneg k))
  push_cast
  linarith

-- CSLib candidate: `SimpleGraph.ArboricityLE.mono` in `SimpleGraph/Arboricity.lean`
/-- Arboricity bounds can be weakened. -- CSLib candidate (`SimpleGraph.ArboricityLE.mono`) -/
lemma arboricityLE_mono {G : SimpleGraph V} {r r' : ℕ}
    (h : G.ArboricityLE r) (hr : r ≤ r') : G.ArboricityLE r' := by
  obtain ⟨F, hF⟩ := h
  exact ⟨fun i => if hi : (i : ℕ) < r then F ⟨i, hi⟩ else ⊥, fun i => by
    by_cases hi : (i : ℕ) < r <;> simp [hi, hF.1], fun i => by
    by_cases hi : (i : ℕ) < r <;> simp [hi, hF.2.1], fun u v huv => by
    obtain ⟨i, hi⟩ := hF.2.2 huv
    exact ⟨⟨i, i.2.trans_le hr⟩, by simp [i.2, hi]⟩⟩

/-- The number of rounds of Arbdefective-Coloring with the paper's parameters. -/
noncomputable def arbRoundsε (C R : ℕ) (ε : ℝ) (n t : ℕ) : ℕ :=
  Lε ε n * (C * (3 * t) ^ 2) - 1 + (1 + (R + Lε ε n))

/-- **Corollary 3.6.** Let `0 < ε ≤ 1` and assume Lemma 2.1 (`hK`). Procedure Arbdefective-Coloring
invoked on a graph of arboricity `≤ a` with positive integers `k` and `t` computes an
`⌊a/t + (2+ε)a/k⌋`-arbdefective `k`-colouring. It takes
`Lε·C(3t)² + R + Lε = O(t² log n)` rounds (`L = Lε = O(log n)`, `R = O(log* n)`). -/
theorem corollary_3_6 {C R : ℕ} (hK : Lemma21 V C R) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (a k t : ℕ) (hk : 0 < k) (ht : 0 < t) :
    IsLocalG (arbRoundsε C R ε (Fintype.card V) t)
      (arbCol k (Aε ε a) (Lε ε (Fintype.card V)) (C * (3 * t) ^ 2)
        (hK.alg (Aε ε a) (3 * t) (by omega)).col) ∧
    ∀ G : SimpleGraph V, G.ArboricityLE a →
      IsArbdefective G (arbCol k (Aε ε a) (Lε ε (Fintype.card V)) (C * (3 * t) ^ 2)
        (hK.alg (Aε ε a) (3 * t) (by omega)).col G) ⌊(a : ℝ) / t + (2 + ε) * a / k⌋₊ ∧
      ∀ v, arbCol k (Aε ε a) (Lε ε (Fintype.card V)) (C * (3 * t) ^ 2)
        (hK.alg (Aε ε a) (3 * t) (by omega)).col G v < k := by
  refine ⟨arbCol_isLocal _ _ _ _ (hK.alg _ _ _).isLocal, fun G hG => ?_⟩
  obtain ⟨h1, h2⟩ := arbdefectiveColoring_spec hG.hasOutDegLE (hRounds_ok hε _ a)
    (hK.alg (Aε ε a) (3 * t) (by omega)) hk
  exact ⟨arboricityLE_mono h1 (defect_le hε.le hε1 a t k), h2⟩

/-- **Corollary 3.4.** Simple-Arbdefective on the complete orientation of Lemma 3.3 computes a
`⌊⌊(2+ε)a⌋/k⌋`-arbdefective (i.e. `O(a/k)`-arbdefective) `k`-colouring of a graph of arboricity
`≤ a` in `L + R + 1 + (L·K - 1)` rounds, which is `O(a log n)` rounds with the `(Δ+1)`-colouring of
[BE09] as the legal colouring `D` (`K = A + 1`, `R = O(a + log* n)`). -/
theorem corollary_3_4 {G : SimpleGraph V} {a A L K R k : ℕ} (hG : G.ArboricityLE a)
    (hL : Fintype.card V * (2 * a) ^ L < (A + 1) ^ L) (D : DefectiveAlg V A 0 K R) (hk : 0 < k) :
    IsArbdefective G (arbCol k A L K D.col G) (A / k) ∧ ∀ v, arbCol k A L K D.col G v < k := by
  simpa using arbdefectiveColoring_spec hG.hasOutDegLE hL D hk

end Podc.ArbdefectiveColoring
