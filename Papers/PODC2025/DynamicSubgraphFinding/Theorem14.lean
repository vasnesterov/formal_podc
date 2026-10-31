import Papers.PODC2025.DynamicSubgraphFinding.Theorem14Correct

/-!
# Theorem 1.4: one-round `MemList(K₃)` under edge insertions with bandwidth `O(Δ² log log n)`

Parameters (Section 5.2): `ℓ = ⌊log₂ n⌋`, window `d = ℓ + 2` (the paper: `d = ⌈log n⌉`), period
`T = ⌊d / 2⌋`, block alphabet `K = 2^(2Δ)` (a block has `2Δ = O(Δ)` bits; `T` blocks carry a
list of `Δ` optional identifiers, `(n + 1)^Δ ≤ 2^(2ΔT)`). Messages (`Alg14.Msg`): one bit, the
recent records (`≤ Δ + Δ²` ages, each in `[0, d]`, i.e. `O(Δ² log log n)` bits), one block.
`card_msg14_le`: at most `2^(10 Δ² (⌊log₂ ⌊log₂ n⌋⌋ + 1))` messages.
-/

namespace Podc.DynamicSubgraphFinding

open Alg14

/-- Bandwidth arithmetic: `2 · (1 + (ℓ + 4)^(Δ + Δ²)) · 2^(2Δ) ≤ 2^(10 Δ² (log₂ ℓ + 1))`. -/
lemma card_bound14 (ℓ Δ : ℕ) (hΔ : 1 ≤ Δ) :
    2 * ((ℓ + 4) ^ Δ * (ℓ + 4) ^ (Δ ^ 2) + 1) * 2 ^ (2 * Δ) ≤
      2 ^ (10 * Δ ^ 2 * (Nat.log 2 ℓ + 1)) := by
  set L := Nat.log 2 ℓ
  have hℓ : ℓ < 2 ^ (L + 1) := Nat.lt_pow_succ_log_self (by norm_num) ℓ
  have h4 : ℓ + 4 ≤ 2 ^ (L + 3) := by
    have : 2 ^ (L + 3) = 2 ^ (L + 1) * 4 := by rw [show L + 3 = (L + 1) + 2 by ring, pow_add]; rfl
    have := Nat.one_le_two_pow (n := L + 1)
    omega
  have hP : (ℓ + 4) ^ Δ * (ℓ + 4) ^ (Δ ^ 2) ≤ 2 ^ ((L + 3) * (Δ + Δ ^ 2)) := by
    rw [← pow_add, pow_mul]
    exact Nat.pow_le_pow_left h4 _
  have h1 : 1 ≤ 2 ^ ((L + 3) * (Δ + Δ ^ 2)) := Nat.one_le_two_pow
  calc 2 * ((ℓ + 4) ^ Δ * (ℓ + 4) ^ (Δ ^ 2) + 1) * 2 ^ (2 * Δ)
      ≤ 2 * (2 * 2 ^ ((L + 3) * (Δ + Δ ^ 2))) * 2 ^ (2 * Δ) := by
        gcongr
        omega
    _ = 2 ^ (2 + (L + 3) * (Δ + Δ ^ 2) + 2 * Δ) := by
        rw [pow_add, pow_add]
        ring
    _ ≤ 2 ^ (10 * Δ ^ 2 * (L + 1)) := by
        apply Nat.pow_le_pow_right (by norm_num)
        have hΔ2 : Δ ≤ Δ ^ 2 := by nlinarith
        have hLΔ : L * Δ ≤ L * Δ ^ 2 := Nat.mul_le_mul_left _ hΔ2
        nlinarith

/-- The number of messages of the algorithm of Theorem 1.4 on `n` nodes. -/
lemma card_msg14_le (n Δ : ℕ) (hΔ : 1 ≤ Δ) :
    Fintype.card (Msg Δ (Nat.log 2 n + 2) (2 ^ (2 * Δ))) ≤
      2 ^ (10 * Δ ^ 2 * (Nat.log 2 (Nat.log 2 n) + 1)) := by
  simp only [Msg, RList, Fintype.card_prod, Fintype.card_bool, Fintype.card_option,
    Fintype.card_fun, Fintype.card_fin]
  have := card_bound14 (Nat.log 2 n) Δ hΔ
  rw [← mul_assoc]
  convert this using 5

/-- `T = ⌊d/2⌋` blocks of `2Δ` bits suffice to encode a list of `Δ` optional identifiers. -/
lemma card_enc14_le (n Δ : ℕ) :
    Fintype.card (Fin Δ → Option (Fin n)) ≤
      Fintype.card (Fin ((Nat.log 2 n + 2) / 2) → Fin (2 ^ (2 * Δ))) := by
  simp only [Fintype.card_fun, Fintype.card_option, Fintype.card_fin]
  have hn : n + 1 ≤ 2 ^ (Nat.log 2 n + 1) := Nat.lt_pow_succ_log_self (by norm_num) n
  calc (n + 1) ^ Δ ≤ (2 ^ (Nat.log 2 n + 1)) ^ Δ := Nat.pow_le_pow_left hn _
    _ = 2 ^ ((Nat.log 2 n + 1) * Δ) := by rw [pow_mul]
    _ ≤ 2 ^ (2 * Δ * ((Nat.log 2 n + 2) / 2)) := by
        apply Nat.pow_le_pow_right (by norm_num)
        have : Nat.log 2 n + 1 ≤ 2 * ((Nat.log 2 n + 2) / 2) := by omega
        calc (Nat.log 2 n + 1) * Δ ≤ 2 * ((Nat.log 2 n + 2) / 2) * Δ :=
              Nat.mul_le_mul_right _ this
          _ = 2 * Δ * ((Nat.log 2 n + 2) / 2) := by ring
    _ = (2 ^ (2 * Δ)) ^ ((Nat.log 2 n + 2) / 2) := by rw [pow_mul]

/-- **Theorem 1.4** of [Chang–Chen–Chen–Mishra–Yang, PODC 2025]. There exists a one-round
algorithm of `MemList(K₃)` under edge insertions with bandwidth `O(Δ² log log n)`, where `Δ` is
the maximum degree of the dynamic network: for some constant `C`, for all `n` and `Δ ≥ 1` there
is an algorithm on the identifier set `Fin n` with at most `2^(C Δ² (⌊log₂ ⌊log₂ n⌋⌋ + 1))`
distinct messages (i.e. messages of `C Δ² (log log n + 1)` bits) that, on every insertion-only
dynamic network with at most one edge insertion per round and maximum degree `≤ Δ`, outputs at
every node after every round exactly the triangles containing it. -/
theorem theorem_1_4 : ∃ C : ℕ, ∀ n Δ : ℕ, 1 ≤ Δ → ∃ (M : Type) (_ : Fintype M)
    (A : Algorithm (Fin n) M (Set (Finset (Fin n)))),
    Fintype.card M ≤ 2 ^ (C * Δ ^ 2 * (Nat.log 2 (Nat.log 2 n) + 1)) ∧
    Solves A InsNet.EdgeIns Δ MemListOK := by
  refine ⟨10, fun n Δ hΔ => ?_⟩
  have hT : 0 < (Nat.log 2 n + 2) / 2 := by omega
  obtain ⟨enc⟩ := Function.Embedding.nonempty_of_card_le (card_enc14_le n Δ)
  exact ⟨Msg Δ (Nat.log 2 n + 2) (2 ^ (2 * Δ)), inferInstance,
    alg14 (d := Nat.log 2 n + 2) hT enc, card_msg14_le n Δ hΔ,
    alg14_solves hT (by omega) enc enc.injective⟩

end Podc.DynamicSubgraphFinding
