import Papers.PODC2022.MultipleSpending.Safety
import Papers.PODC2022.MultipleSpending.Uniform
import Papers.PODC2022.MultipleSpending.EchoBroadcast

/-!
# Algorithms 1–2 can beat `k_max`: the optimality claim of §5 fails

The paper concludes §5 with "Theorems 5.1 and 5.2 imply that Algorithms 1 and 2 implement the
`k`-SAT abstraction with optimal `k`" (`k = k_max`, the inconsistency number). Our refined safety
analysis (`Setup.spendingNumber_le_refined`) shows that only *faulty* issuers multiply spend, so
only graphs `G_{B,S}` with the actual faulty set `B ∋ r` matter, and `B = ∅` gives no multiple
spending at all.

* `spendingNumber_le_one_of_B_empty`: without faulty processes the spending number is `≤ 1`.
* `spendingNumber_le_card_sub`: with a nonempty faulty set, it is `≤ max 1 (n − |B|)`.
* `algorithms_no_double_spending_pairsT`: in the four-process model `pairsT` of
  `theorem_5_1_false'` (`k_max = 2`), Algorithms 1–2 never let anything be spent twice.
* `algorithms_beat_kmax`: in the uniform model with `n = 3`, `q = 1`, `f = 1` (`k_max = 3`), every
  run of Algorithms 1–2 has spending number `≤ 2`.
-/

namespace Podc.MultipleSpending

open Finset

variable {P Tx : Type*} [Fintype P] [DecidableEq P] [DecidableEq Tx]

namespace Setup

variable (A : Setup P Tx)

/-- Without faulty processes nothing is spent twice. -/
theorem spendingNumber_le_one_of_B_empty (hself : A.T.SelfMem) (hhon : A.HonestIssuers)
    (hB : A.B = ∅) {σ : State P Tx} (h : A.Reachable σ) : A.X.spendingNumber (A.Γ σ) ≤ 1 := by
  rw [TxSystem.spendingNumber_le_iff]
  intro r tx _
  exact A.spend_le_one_of_correct hself hhon h (by simp [hB]) tx

/-- An independent set of `G_{B,S}` avoids `B`, so `λ(Q, {B}) ≤ n − |B|`. -/
theorem inconsistencyNumber_single_le (Q : P → Set (Finset P)) (B : Finset P) :
    inconsistencyNumber (⟨Q, {B}⟩ : TrustModel P) ≤ Fintype.card P - B.card := by
  apply TrustModel.inconsistencyNumber_le
  rintro F hF S - C hC
  rw [Set.mem_singleton_iff] at hF
  subst hF
  have : C ⊆ Fᶜ := fun p hp => Finset.mem_compl.mpr (Finset.disjoint_left.mp hC.1 hp)
  exact (Finset.card_le_card this).trans (by rw [Finset.card_compl])

/-- With faulty processes, the spending number is at most `max 1 (n − |B|)`. -/
theorem spendingNumber_le_card_sub (hq : A.T.HasQuorums) (hself : A.T.SelfMem)
    (hhon : A.HonestIssuers) {σ : State P Tx} (h : A.Reachable σ) :
    A.X.spendingNumber (A.Γ σ) ≤ max 1 ((Fintype.card P - A.B.card : ℕ) : ℕ∞) := by
  refine (A.spendingNumber_le_refined hq hself hhon h).trans (max_le_max le_rfl ?_)
  exact_mod_cast inconsistencyNumber_single_le A.T.Q A.B

end Setup

/-- **Algorithms 1–2 beat `k_max`.** In the uniform model with three processes, singleton quorums
and at most one failure, the inconsistency number is `k_max = 3`, but every run of Algorithms 1–2
(with honest issuers; compliance of the faulty set is not even needed) has spending number at most
`2`. So `k_max` is not the optimal spending number achieved by the paper's own algorithm. -/
theorem algorithms_beat_kmax {Tx : Type*} [DecidableEq Tx] (A : Setup (Fin 3) Tx)
    (hT : A.T = uniform 1 1) (hhon : A.HonestIssuers)
    {σ : State (Fin 3) Tx} (h : A.Reachable σ) :
    A.X.spendingNumber (A.Γ σ) ≤ 2 ∧ inconsistencyNumber A.T = 3 := by
  have hself : A.T.SelfMem := hT ▸ uniform_selfMem 1 1
  have hq : A.T.HasQuorums := hT ▸ uniform_hasQuorums (by norm_num) (by simp)
  refine ⟨?_, ?_⟩
  · by_cases hB0 : A.B = ∅
    · exact (A.spendingNumber_le_one_of_B_empty hself hhon hB0 h).trans (by norm_num)
    · have h1 : 1 ≤ A.B.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hB0)
      refine (A.spendingNumber_le_card_sub hq hself hhon h).trans ?_
      simp only [Fintype.card_fin]
      have : 3 - A.B.card ≤ 2 := by omega
      exact max_le (by norm_num) (by exact_mod_cast this)
  · rw [hT, theorem_3_6_needs_q_gt_f (by norm_num) le_rfl (by simp)]; simp

/-- **Algorithms 1–2 beat `k_max` without singleton quorums.** In the four-process model `pairsT`
(quorums `{a,a'}`, `{b,b'}`, `Π`, `Π`; faulty sets `∅, {a}, {b}`; `k_max = 2`), every run of
Algorithms 1–2 whose faulty set is in the fault model has spending number at most `1`. -/
theorem algorithms_no_double_spending_pairsT {Tx : Type*} [DecidableEq Tx]
    (A : Setup (Fin 4) Tx) (hT : A.T = pairsT) (hB : A.B ∈ A.T.F) (hhon : A.HonestIssuers)
    {σ : State (Fin 4) Tx} (h : A.Reachable σ) :
    A.X.spendingNumber (A.Γ σ) ≤ 1 ∧ inconsistencyNumber A.T = 2 := by
  have hself : A.T.SelfMem := hT ▸ pairsT_selfMem
  have hq : A.T.HasQuorums := hT ▸ pairsT_hasQuorums
  refine ⟨?_, by rw [hT]; exact pairsT_inconsistencyNumber⟩
  by_cases hB0 : A.B = ∅
  · exact A.spendingNumber_le_one_of_B_empty hself hhon hB0 h
  · refine (A.spendingNumber_le_refined hq hself hhon h).trans (max_le le_rfl ?_)
    have hB' : A.B = {0} ∨ A.B = {2} := by
      rw [hT] at hB
      simp only [pairsT, Set.mem_insert_iff, Set.mem_singleton_iff] at hB
      tauto
    obtain ⟨b, hb, hBb⟩ : ∃ b : Fin 4, (b = 0 ∨ b = 2) ∧ A.B = {b} := by
      rcases hB' with h' | h'
      · exact ⟨0, Or.inl rfl, h'⟩
      · exact ⟨2, Or.inr rfl, h'⟩
    have heq : (⟨A.T.Q, {A.B}⟩ : TrustModel (Fin 4)) =
        ⟨pairsT.Q, {F | F ∈ pairsT.F ∧ b ∈ F}⟩ := by
      rw [hT, hBb]
      congr 1
      ext F
      simp only [pairsT, Set.mem_singleton_iff, Set.mem_insert_iff, Set.mem_ofPred_eq]
      constructor
      · rintro rfl; rcases hb with rfl | rfl <;> simp
      · rintro ⟨hF | hF | hF, hbF⟩ <;> subst hF <;> rcases hb with rfl | rfl <;> simp_all
    rw [heq]
    exact_mod_cast pairsT_srcInconsistencyNumber_le b

end Podc.MultipleSpending
