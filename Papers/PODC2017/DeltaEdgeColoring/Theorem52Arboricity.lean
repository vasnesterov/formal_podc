import Papers.PODC2017.DeltaEdgeColoring.Section5
import Papers.PODC2010.ArbdefectiveColoring.HPartition

/-!
# Theorem 5.2 for bounded arboricity: `Δ + 6a` colours in `O(a log n)` rounds

Theorem 5.2 takes the H-partition of Barenboim–Elkin [4]. We use its formalization from
`Papers/PODC2010/ArbdefectiveColoring/HPartition.lean` (Lemma 2.3 there): if `G` has an orientation
with out-degree `≤ a` (e.g. arboricity `≤ a`), the peeling algorithm with threshold `A` produces after
`L` rounds an H-partition with `L` sets and degree `A`, provided `n (2a)^L < (A+1)^L`. With `A = 3a`
(`ε = 1`) this holds for `L = 2(⌊log₂ n⌋ + 1)`.

* `theorem_5_2_arboricity`: a graph with an orientation of out-degree `≤ a` and max degree `≤ Δ` has an
  edge colouring with `Δ + 6a` colours computed by the procedure of Theorem 5.2 whose crossing
  edges are coloured within `L · 3a` rounds, `L = 2(⌊log₂ n⌋ + 1)`, i.e. `O(a log n)` rounds.
-/

open Finset

namespace Podc.DeltaEdgeColoring

set_option linter.unusedSectionVars false

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- `n · 2^{2k} < 3^{2k}` for `k = ⌊log₂ n⌋ + 1`. -/
lemma card_mul_pow_lt (n : ℕ) :
    n * 2 ^ (2 * (Nat.log 2 n + 1)) < 3 ^ (2 * (Nat.log 2 n + 1)) := by
  set k := Nat.log 2 n + 1
  have hn : n < 2 ^ k := Nat.lt_pow_succ_log_self (by norm_num) n
  rw [pow_mul, pow_mul]
  norm_num
  calc n * 4 ^ k < 2 ^ k * 4 ^ k := Nat.mul_lt_mul_of_pos_right hn (by positivity)
    _ = 8 ^ k := by rw [← mul_pow]; norm_num
    _ ≤ 9 ^ k := Nat.pow_le_pow_left (by norm_num) k

/-- The H-partition of [4] with degree `3a` and `L = 2(⌊log₂ n⌋ + 1)` sets. -/
theorem exists_hPartition {G : SimpleGraph V} {a : ℕ} (hG : G.HasOutDegLE a) :
    ∃ h : V → ℕ, IsHPartition G h (2 * (Nat.log 2 (Fintype.card V) + 1)) (3 * a) := by
  classical
  set L := 2 * (Nat.log 2 (Fintype.card V) + 1)
  have hL : Fintype.card V * (2 * a) ^ L < (3 * a + 1) ^ L := by
    rcases Nat.eq_zero_or_pos a with rfl | ha
    · simp [L]
    · have h1 := card_mul_pow_lt (Fintype.card V)
      calc Fintype.card V * (2 * a) ^ L = Fintype.card V * 2 ^ L * a ^ L := by
            rw [mul_pow]; ring
        _ < 3 ^ L * a ^ L := Nat.mul_lt_mul_of_pos_right h1 (by positivity)
        _ = (3 * a) ^ L := by rw [mul_pow]
        _ ≤ (3 * a + 1) ^ L := Nat.pow_le_pow_left (by omega) L
  obtain ⟨hlt, hdeg⟩ := Podc.ArbdefectiveColoring.hPartition (A := 3 * a) hG hL
  refine ⟨Podc.ArbdefectiveColoring.hIdx G (3 * a) L, hlt, fun v => ?_⟩
  have := hdeg v
  rwa [← Set.ncard_coe_finset, coe_filter_univ] at this

/-- **Theorem 5.2** (`(Δ + O(a))`-edge-colouring in `O(a log n)` time). Let `G` have an orientation
with out-degree `≤ a` (e.g. arboricity `≤ a`) and max degree `≤ Δ`, and let `L = 2(⌊log₂ n⌋ + 1)`.
There are an H-partition `h` with `L` sets and degree `3a`, a labelling `lab` and an edge colouring
`c₀` of the H-sets such that the procedure of Theorem 5.2 can be run, every run is a proper edge
colouring with at most `Δ + 6a` colours, and every crossing edge is coloured within the first
`L · 3a` rounds. -/
theorem theorem_5_2_arboricity {G : SimpleGraph V} {a Δ : ℕ} (hG : G.HasOutDegLE a)
    (hΔ : ∀ v, (G.neighborSet v).ncard ≤ Δ) :
    let L := 2 * (Nat.log 2 (Fintype.card V) + 1)
    ∃ (h : V → ℕ) (lab : V → V → ℕ) (c₀ : Sym2 V → ℕ),
      IsHPartition G h L (3 * a) ∧ IsHLabeling G h lab (3 * a) ∧
      (∀ c, (schedule52 h L (3 * a) lab).Follows G c₀ c (Δ + 3 * a - 1) →
        G.IsProperEdgeColoring c (Δ + 6 * a)) ∧
      (∃ c, (schedule52 h L (3 * a) lab).Follows G c₀ c (Δ + 3 * a - 1)) ∧
      ∀ ⦃u v⦄, G.Adj u v → ¬ hPre h s(u, v) → hTime h L (3 * a) lab s(u, v) < L * (3 * a) := by
  intro L
  obtain ⟨h, hH⟩ := exists_hPartition hG
  obtain ⟨lab, hlab⟩ := exists_isHLabeling hH
  obtain ⟨c₀, h1, h2⟩ := theorem_5_2_colors hH hlab hΔ
  refine ⟨h, lab, c₀, hH, hlab, fun c hc => (h1 c hc).mono le_rfl (by omega), h2,
    fun u v huv hp => theorem_5_2_rounds hH hlab huv hp⟩

end Podc.DeltaEdgeColoring
