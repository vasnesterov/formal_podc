import Papers.PODC2020.PowerGraphApproximation.LBGraphs
import Cslib.Computability.Distributed.Congest.Randomized

/-!
# Theorem 20: exact weighted `G²`-MVC needs `Ω̃(n²)` CONGEST rounds

Bar-Yehuda, Censor-Hillel, Maus, Pai, Pemmaraju, *Distributed Approximation on Power Graphs*,
PODC 2020 (arXiv:2006.03746), Section 5.2.

Model: synchronous deterministic CONGEST (`Cslib.Congest.Algorithm`) with `B`-bit messages; the
communication network is `H_{x,y}`; every node knows its ID, its neighbourhood and its weight
(`wt`: `1` on the vertices of `G_{x,y}`, `0` on the gadget vertices `p_e`, `p^i_a`, `p^i_b`). An
algorithm *decides* the predicate in `T` rounds if, after `T` rounds, all nodes accept iff the
predicate holds (the weakest output convention; any algorithm computing a minimum weight vertex
cover of `H²` can be turned into one deciding the predicate, by `O(D)` extra rounds of
aggregation — not formalized).

With `k = 2^L`, `n = |V(H)| = 6k + 4k log k + 16 log k` (`card_HV`), the cut has `4 log k` edges,
and Theorem 19 with `CC(DISJ_{k²}) ≥ k²` gives `k² ≤ 8 T B log k + 2` (`theorem_20`), i.e.
`n² ≤ 676 log² n · (8 T B log n + 2)` (`theorem_20_n`): `T = Ω(n² / (B log³ n))`.
-/

namespace Podc.PowerGraphApproximation.LowerBound

open Finset SimpleGraph Cslib.Congest Cslib.CommunicationComplexity

variable {L : ℕ}

/-- The weighted family: as `hFamily L 1`, with the vertex weight added to every node's input. -/
def wFamily (L : ℕ) :
    LBFamily (Idx L × Idx L → Bool) (Idx L × Idx L → Bool) (HV L 1) ((HV L 1 → Bool) × ℕ) :=
  { hFamily L 1 with
    inp := fun x y v => ((hFamily L 1).inp x y v, wt v)
    inp_alice := fun x y y' v hv => by simp [(hFamily L 1).inp_alice x y y' v hv]
    inp_bob := fun x x' y v hv => by simp [(hFamily L 1).inp_bob x x' y v hv] }

instance (x y : Idx L × Idx L → Bool) : DecidableRel ((wFamily L).G x y).Adj :=
  inferInstanceAs (DecidableRel (H x y 1).Adj)

/-- The predicate `P_H`: `H²` has a vertex cover of weight at most
`W = 4(k - 1) + 4 log k`. -/
def WeightedPred (x y : Idx L × Idx L → Bool) : Prop :=
  ∃ C : Finset (HV L 1), ((H x y 1).power 2).IsVertexCover ↑C ∧
    ∑ v ∈ C, wt v ≤ 4 * (2 ^ L - 1) + 4 * L

lemma weightedPred_iff (x y : Idx L × Idx L → Bool) :
    WeightedPred x y ↔ Protocol.disj x y = false := by
  rw [WeightedPred, lemma_21, ckp17]
  simp [Protocol.disj]

/-- **Theorem 20 of [BCMPP20]** (deterministic, decision version). Let `A` be a deterministic
CONGEST algorithm with `B`-bit messages that, in `T` rounds, decides on every graph `H_{x,y}`
(nodes know their neighbourhoods and weights) whether `H²_{x,y}` has a vertex cover of weight at
most `W = 4(k - 1) + 4 log k`. Then `k² ≤ 8 T B log k + 2`. -/
theorem theorem_20 {σ : Type*} {B : ℕ} (A : Algorithm (HV L 1) ((HV L 1 → Bool) × ℕ) σ B)
    (T : ℕ)
    (hA : ∀ x y : Idx L × Idx L → Bool,
      A.Accepts (H x y 1) (fun v => (fun w => decide ((H x y 1).Adj v w), wt v)) T ↔
        ∃ C : Finset (HV L 1), ((H x y 1).power 2).IsVertexCover ↑C ∧
          ∑ v ∈ C, wt v ≤ 4 * (2 ^ L - 1) + 4 * L) :
    4 ^ L ≤ T * (8 * L * B) + 2 := by
  have h := (wFamily L).not_disj_lowerBound A T fun x y => by
    change A.Accepts (H x y 1) (fun v => (fun w => decide ((H x y 1).Adj v w), wt v)) T ↔ _
    rw [hA x y]
    exact weightedPred_iff x y
  rw [show (wFamily L).Ecut = hCut L 1 from rfl, card_hCut] at h
  have hc : Fintype.card (Idx L × Idx L) = 4 ^ L := by
    simp [Fintype.card_prod, ← mul_pow]
  rw [hc] at h
  calc 4 ^ L ≤ T * (2 * (4 * L * B)) + 2 := h
    _ = T * (8 * L * B) + 2 := by ring

/-- `n ≤ c · log k · k` and `log k ≤ log n` turn `k² ≤ 8 T B log k + 2` into the `Ω̃(n²)` form. -/
lemma sq_le_of_card_le {n c L T B : ℕ} (hn : n ≤ c * L * 2 ^ L)
    (hlog : 2 ^ L ≤ n) (h : 4 ^ L ≤ T * (8 * L * B) + 2) :
    n ^ 2 ≤ c ^ 2 * Nat.log 2 n ^ 2 * (T * (8 * Nat.log 2 n * B) + 2) := by
  have hLn : L ≤ Nat.log 2 n := Nat.le_log_of_pow_le (by norm_num) hlog
  have h4 : (4 : ℕ) ^ L = 2 ^ L * 2 ^ L := by
    rw [← mul_pow]; norm_num
  calc n ^ 2 ≤ (c * L * 2 ^ L) ^ 2 := Nat.pow_le_pow_left hn 2
    _ = c ^ 2 * L ^ 2 * 4 ^ L := by rw [h4]; ring
    _ ≤ c ^ 2 * L ^ 2 * (T * (8 * L * B) + 2) := Nat.mul_le_mul_left _ h
    _ ≤ c ^ 2 * Nat.log 2 n ^ 2 * (T * (8 * Nat.log 2 n * B) + 2) := by gcongr

/-- **Theorem 20 of [BCMPP20]**, in terms of `n = |V(H_{x,y})|` (for `k ≥ 2`):
`n² ≤ 676 log² n · (8 T B log n + 2)`, i.e. `T = Ω(n² / (B log³ n)) = Ω̃(n²)`. -/
theorem theorem_20_n (hL : 1 ≤ L) {σ : Type*} {B : ℕ}
    (A : Algorithm (HV L 1) ((HV L 1 → Bool) × ℕ) σ B) (T : ℕ)
    (hA : ∀ x y : Idx L × Idx L → Bool,
      A.Accepts (H x y 1) (fun v => (fun w => decide ((H x y 1).Adj v w), wt v)) T ↔
        ∃ C : Finset (HV L 1), ((H x y 1).power 2).IsVertexCover ↑C ∧
          ∑ v ∈ C, wt v ≤ 4 * (2 ^ L - 1) + 4 * L) :
    Fintype.card (HV L 1) ^ 2 ≤
      676 * Nat.log 2 (Fintype.card (HV L 1)) ^ 2 *
        (T * (8 * Nat.log 2 (Fintype.card (HV L 1)) * B) + 2) := by
  have hk : 1 ≤ 2 ^ L := Nat.one_le_two_pow
  have := sq_le_of_card_le (c := 26) (n := Fintype.card (HV L 1)) ?_ ?_ (theorem_20 A T hA)
  · simpa using this
  · rw [card_HV]; nlinarith
  · rw [card_HV]; nlinarith

open Classical in
/-- **Theorem 20 of [BCMPP20]** (randomized, conditional on `CC^R(DISJ_K) ≥ κ·K`). Assume that
every private-coin protocol computing "the inputs intersect" on `K = k²` bits with error `≤ ε`
sends at least `κ · K` bits (`hCC`; Kalyanasundaram–Schnitger / Razborov: true for `ε = 1/3` and
some real constant `κ > 0`, not formalized). The constant `κ` is real: a natural-number constant
would make the hypothesis false for large `k` whenever `κ ≥ 1` (the randomized complexity of
disjointness is about `0.49 K`), leaving only `κ = 0`. The coin spaces must be nonempty, otherwise
`hCC` would force `κ ≤ 0` (`ret true` would compute `¬DISJ` with zero error count at cost 0). If a
randomized CONGEST algorithm (private random strings `r v : ρ`) decides on every `H_{x,y}`, with
error probability `≤ ε`, whether `H²_{x,y}` has a vertex cover of weight `≤ W`, then
`κ · k² ≤ 8 T B log k + 2`. -/
theorem theorem_20_randomized {σ ρ : Type} [Fintype ρ] [Nonempty ρ] {B : ℕ}
    (A : Algorithm (HV L 1) (((HV L 1 → Bool) × ℕ) × ρ) σ B) (T : ℕ) (ε κ : ℝ)
    (hCC : ∀ (RA RB : Type) [Fintype RA] [Fintype RB] [Nonempty RA] [Nonempty RB]
      (P : Protocol ((Idx L × Idx L → Bool) × RA) ((Idx L × Idx L → Bool) × RB) Bool) (b : ℕ),
      P.RandComputes (fun x y => !Protocol.disj x y) ε → P.CostLE b → κ * 4 ^ L ≤ b)
    (hA : ∀ x y : Idx L × Idx L → Bool,
      (LBFamily.Algorithm.randErr A (H x y 1)
        (fun v => (fun w => decide ((H x y 1).Adj v w), wt v)) T
        (decide (∃ C : Finset (HV L 1), ((H x y 1).power 2).IsVertexCover ↑C ∧
          ∑ v ∈ C, wt v ≤ 4 * (2 ^ L - 1) + 4 * L)) : ℝ) ≤
        ε * Fintype.card (HV L 1 → ρ)) :
    κ * 4 ^ L ≤ T * (8 * L * B) + 2 := by
  have h := (wFamily L).rand_lowerBound A T (fun x y => !Protocol.disj x y) ε (fun x y => by
    have e : (!Protocol.disj x y) = decide (∃ C : Finset (HV L 1),
        ((H x y 1).power 2).IsVertexCover ↑C ∧ ∑ v ∈ C, wt v ≤ 4 * (2 ^ L - 1) + 4 * L) := by
      rw [Bool.eq_iff_iff, decide_eq_true_iff]
      exact ((weightedPred_iff x y).trans (by simp)).symm
    rw [e]
    exact hA x y) ⌈κ * 4 ^ L⌉₊ (fun P b hP hb => Nat.ceil_le.2 (hCC _ _ P b hP hb))
  rw [show (wFamily L).Ecut = hCut L 1 from rfl, card_hCut] at h
  calc κ * 4 ^ L ≤ (⌈κ * 4 ^ L⌉₊ : ℝ) := Nat.le_ceil _
    _ ≤ ((T * (2 * (4 * L * B)) + 2 : ℕ) : ℝ) := by exact_mod_cast h
    _ = T * (8 * L * B) + 2 := by push_cast; ring

end Podc.PowerGraphApproximation.LowerBound
