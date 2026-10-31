import Papers.PODC2018.InteractiveDistributedProofs.Protocol1

/-!
# Lemma 3.3 is false for the literal Protocol 1

Network `K₂` on `V = Fin 2`, prime `p = 83 ∈ [10·2³, 100·2³]`. The prover commits to the root
`r = 0`, the swap `ρ`, parents `t_0 = t_1 = 0` (the paper's protocol also gives the root a parent
pointer, and nothing forbids `t_r = r`) and depths `d_0 = 0`, `d_1 = 1`. Then
`C(0) = {u ∈ N(0) | t_u = 0} = {0, 1}` contains the root itself, so the root's check
`a_0 = h_i([0, N(0)]) + a_0 + a_1` no longer determines `a_0`; it only requires
`h_i(∑_v [v, N(v)]) = 0`. For the all-ones matrix of `K₂` this holds for the index `i = -1`
(`1 - 1 + 1 - 1 = 0`). With all challenges equal to `-1` and `a_0 = b_0 = 1`, every node accepts
although `a_0 ≠ h_i(∑_v [v, N(v)]) = 0`.
-/

open Finset

namespace Podc.InteractiveDistributedProofs.Protocol1

instance fact_prime_83 : Fact (Nat.Prime 83) := ⟨by norm_num⟩

/-- The hash of the all-ones `2 × 2` matrix at seed `-1` vanishes. -/
theorem rowHash_sum_K2 :
    rowHash (-1 : ZMod 83) (0 : Fin 2) univ + rowHash (-1 : ZMod 83) (1 : Fin 2) univ = 0 := by
  have h1 : rowMat (ZMod 83) (0 : Fin 2) univ + rowMat (ZMod 83) (1 : Fin 2) univ =
      fun _ => 1 := by
    funext q
    rcases q with ⟨a, b⟩
    fin_cases a <;> simp [rowMat]
  rw [rowHash, rowHash, ← map_add, h1, polyHash_apply]
  simp only [one_mul]
  rw [← Equiv.sum_comp (Fintype.equivFin (Fin 2 × Fin 2)).symm]
  simp only [Equiv.apply_symm_apply]
  rw [Fin.sum_univ_eq_sum_range (fun i => (-1 : ZMod 83) ^ i)]
  simp [Finset.sum_range_succ]
  norm_num

/-- The cheating prover of the counterexample. -/
noncomputable def cexProver : MAMProver (Fin 2) (M₁ (Fin 2)) (ZMod 83) (M₂ 83) where
  first v := (0, v + 1, 0, ⟨v.val, by rw [Fintype.card_fin]; exact v.isLt⟩)
  second _ v := if v = 0 then (-1, 1, 1)
    else (-1, rowHash (-1 : ZMod 83) (1 : Fin 2) univ, rowHash (-1 : ZMod 83) (0 : Fin 2) univ)

theorem cnbhd_top_fin2 (v : Fin 2) : cnbhd (⊤ : SimpleGraph (Fin 2)) v = univ := by
  ext u
  simp only [mem_cnbhd, SimpleGraph.top_adj, mem_univ, iff_true]
  by_cases h : u = v
  · exact Or.inl h
  · exact Or.inr (Ne.symm h)

/-- All nodes accept the cheating prover when all challenges are `-1`. -/
theorem cex_accepts : (protocol 83 false).Accepts ⊤ cexProver fun _ => -1 := by
  intro v
  rw [out_mask, cnbhd_top_fin2]
  have hsum := rowHash_sum_K2
  fin_cases v <;>
    simp [verify, cexProver, root, rho, par, dep, chal, idx, ha, hb, Fin.sum_univ_two]
  exact ⟨by linear_combination -hsum, by linear_combination -hsum⟩

/-- **Lemma 3.3 is false** for Protocol 1 as written: there are a connected graph (`K₂`), a prover
and challenges for which all nodes accept but `a_r ≠ h_i(∑_v [v, N(v)])`. -/
theorem lemma_3_3_false :
    ∃ (P : MAMProver (Fin 2) (M₁ (Fin 2)) (ZMod 83) (M₂ 83)) (c : Fin 2 → ZMod 83),
      (protocol 83 false).Accepts ⊤ P c ∧
      ha (glob P c (root₀ P)) ≠ polyHash (c (root₀ P)) (adjSum (ZMod 83) (⊤ : SimpleGraph (Fin 2))) := by
  refine ⟨cexProver, fun _ => -1, cex_accepts, ?_⟩
  have hr : root₀ cexProver = 0 := rfl
  have hA : adjSum (ZMod 83) (⊤ : SimpleGraph (Fin 2)) =
      rowMat (ZMod 83) (0 : Fin 2) univ + rowMat (ZMod 83) (1 : Fin 2) univ := by
    simp [adjSum, Fin.sum_univ_two, cnbhd_top_fin2]
  rw [hr, hA, map_add]
  have := rowHash_sum_K2
  simp only [rowHash] at this
  rw [this]
  decide

end Podc.InteractiveDistributedProofs.Protocol1
