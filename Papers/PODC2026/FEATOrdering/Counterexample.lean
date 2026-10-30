import Papers.PODC2026.FEATOrdering.FEAT
import Mathlib.Tactic.FinCases

/-!
# Counterexample: with the paper's honest-replica score, Lemma 6.3 and Theorems 6.4, 6.6 fail

The paper defines `score(T)` as the number of **honest** replicas whose committed local orderings
include `T`. The proof of Lemma 6.3 (Case 2) concludes `τ_shaded > W_{r-1}(m, z)` from
`score(m) < τ_shaded`, forgetting that Byzantine replicas also contribute to `W(m, z)`.

Instance: `n = 7` replicas, `f = 2` (replicas `5, 6` Byzantine), `γ = 1`
(`n = 7 > (2γ+1)f/(2γ−1) = 6`), so `τ_dec = τ_shaded = 5/2`, `τ_solid = 5`. Two transactions
`z = 0`, `m = 1`.

* Honest replicas `0, 1` receive `m, z`; honest replicas `2, 3, 4` receive `z, m`.
* Round 1: replicas `0, 1` commit `[m, z]`, replicas `2, 3, 4` commit `[z]`, the Byzantine
  replicas commit `[m, z]`. Then `score(z) = 5` (solid), `score(m) = 2` (blank), and
  `W₁(m, z) = 4 > W₁(z, m) = 3 ≥ τ_dec`, so the pair is decided: `cmp_T(z, m) = False`.
  FEAT inserts `z` alone: `FO₁ = [z]`.
* Round 2: replicas `2, 3, 4` commit `m`; `score(m) = 5`, `m` is newly solid, `RO₂ = [m]`,
  and FEAT finalizes `FO₂ = [z, m]`.

FEAT never compares `z` with `m`, yet `cmp_T(z, m) = False`: `FO₂` violates Adjacent-Comparator
Consistency (Theorem 6.4), the boundary pair `(z, m)` violates Lemma 6.3, and `FO₂` is not
comparator-based γ-Batch-Order-Fair (Theorem 6.6): `{z}` and `{m}` are different batches but
`z` is output first although `cmp_T(z, m) = False`. (The γ-precedence clause is not violated:
no pair is received in the same order by all honest replicas.) All assumptions of the model
hold; rounds `≥ 3` commit nothing new (empty fragments), so `FO_r = [z, m]` for all `r ≥ 2`.
-/

namespace Podc.FEATOrdering

open Finset

/-- Committed local orderings of the counterexample. -/
def cexL : ℕ → Fin 7 → List (Fin 2)
  | 0, _ => []
  | 1, i => if i.val = 2 ∨ i.val = 3 ∨ i.val = 4 then [0] else [1, 0]
  | _ + 2, i => if i.val = 2 ∨ i.val = 3 ∨ i.val = 4 then [0, 1] else [1, 0]

/-- Receive orders of the counterexample. -/
def cexRecv (i : Fin 7) : List (Fin 2) :=
  if i.val = 2 ∨ i.val = 3 ∨ i.val = 4 then [0, 1] else [1, 0]

/-- The honest replicas `0, …, 4`. -/
def cexH : Finset (Fin 7) := {0, 1, 2, 3, 4}

/-- The counterexample system. -/
def cex : Setup (Fin 7) (Fin 2) where
  f := 2
  L := cexL
  L_mono := by
    intro r i
    rcases r with _ | _ | r <;> fin_cases i <;> simp [cexL]
  tb a b := decide (a < b)
  tb_anti := by decide
  H := cexH
  card_byz := by decide
  recv := cexRecv
  L_prefix_recv := by
    intro r i _
    rcases r with _ | _ | r <;> fin_cases i <;> simp [cexL, cexRecv]
  eventually := by
    intro i _ x _
    refine ⟨2, fun j hj => ?_⟩
    fin_cases x <;> fin_cases j <;> simp_all [cexL, cexH]

/-- Insertion orders: `z` in round 1, `m` in round 2. -/
def cexIns : ℕ → List (Fin 2)
  | 1 => [0]
  | 2 => [1]
  | _ => []

theorem cex_insOK : cex.InsOK cex.scoreHonest cexIns where
  nodup r := by
    rcases r with _ | _ | _ | r <;> simp [cexIns]
  new r x hx := by
    rcases r with _ | _ | r
    · simp [cexIns] at hx; subst hx; decide
    · simp [cexIns] at hx; subst hx; decide
    · simp [cexIns] at hx

theorem cex_pcmp0 : cex.pcmp 0 0 1 = none := by decide
theorem cex_pcmp1 : cex.pcmp 1 0 1 = some false := by decide

/-- The pair `(z, m)` is decided in round 1 in favour of `m`: `cmp_T(z, m) = False`. -/
theorem cex_cmpT : cex.cmpT 0 1 = false :=
  cex.cmpT_eq_first cex_pcmp1 fun r' hr' => by
    obtain rfl : r' = 0 := by omega
    exact cex_pcmp0

theorem cex_run1 : cex.run cex.scoreHonest cexIns id 1 = ([0], []) := by
  simp only [Setup.run, Setup.step, Setup.RO, buildTree, cexIns, List.foldl, id,
    BTree.insert, BTree.inorder, List.nil_merge, List.nil_append]
  simp only [cutLast]
  decide

theorem cex_RO2 : cex.RO cexIns id 2 = [1] := rfl

theorem cex_FO2 : cex.FO cex.scoreHonest cexIns id 2 = [0, 1] := by
  show (cex.step cex.scoreHonest cexIns id 2 (cex.run cex.scoreHonest cexIns id 1)).1 = _
  rw [cex_run1]
  simp only [Setup.step, cex_RO2, List.nil_merge]
  simp only [cutLast]
  decide

/-- Under the comparator-based definition, a two-element ordering `[x, y]` with
`cmp(x, y) = False` is never γ-Batch-Order-Fair. -/
theorem not_batchOrderFair_pair {α : Type*} {c : α → α → Bool} {G : α → α → Prop} {x y : α}
    (hxy : x ≠ y) (hc : c x y = false) : ¬ BatchOrderFair c G [x, y] := by
  rintro ⟨B, hflat, hne, hcls, hfwd, -⟩
  -- `x` reaches only itself
  have hreach : ∀ w, Reach c [x, y] x w → w = x := by
    intro w hw
    induction hw with
    | refl => rfl
    | tail _ hbc ih =>
      subst ih
      obtain ⟨-, hm, he⟩ := hbc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl
      · rfl
      · rw [hc] at he; cases he
  have hnot : ¬ SameBatch c [x, y] x y := fun h => hxy (hreach y h.1).symm
  rcases B with _ | ⟨b, B⟩
  · simp at hflat
  rw [List.flatten_cons] at hflat
  have hb := hne b (by simp)
  rcases b with _ | ⟨a, t⟩
  · exact hb rfl
  rw [List.cons_append, List.cons.injEq] at hflat
  obtain ⟨rfl, hflat⟩ := hflat
  rcases t with _ | ⟨a', t⟩
  · -- `b = [x]`, so `y` lies in a later block
    simp only [List.nil_append] at hflat
    have hy : y ∈ B.flatten := by simp [hflat]
    obtain ⟨b', hb', hyb'⟩ := List.mem_flatten.1 hy
    have := (List.pairwise_cons.1 hfwd).1 b' hb' a (by simp) y hyb'
    rw [hc] at this; cases this
  · -- `b ⊇ [x, y]`, so `x ∼ y`
    rw [List.cons_append, List.cons.injEq] at hflat
    obtain ⟨rfl, -⟩ := hflat
    exact hnot ((hcls _ List.mem_cons_self a List.mem_cons_self a').1 (by simp))

/-- **Lemma 6.3 is false with the paper's (honest-replica) score.** The last transaction `z` of
`FO₁` and the head `m` of `Merged₂` satisfy `cmp_T(z, m) = False`. -/
theorem lemma_6_3_false :
    ∃ z ∈ (cex.FO cex.scoreHonest cexIns id 1).getLast?,
    ∃ m ∈ (List.merge (cex.run cex.scoreHonest cexIns id 1).2 (cex.RO cexIns id 2) cex.cmpT).head?,
      cex.cmpT z m = false := by
  refine ⟨0, ?_, 1, ?_, cex_cmpT⟩
  · simp [Setup.FO, cex_run1]
  · simp [cex_run1, cex_RO2]

/-- **Theorem 6.4 is false with the paper's score**: `FO₂ = [z, m]` with `cmp_T(z, m) = False`. -/
theorem theorem_6_4_false :
    ¬ AdjConsistent cex.cmpT (cex.FO cex.scoreHonest cexIns id 2) := by
  rw [cex_FO2]
  simp [AdjConsistent, cex_cmpT]

/-- **Theorem 6.6 is false with the paper's score.** The counterexample satisfies all hypotheses of
`Setup.theorem_6_6` (with `γ = 1`, `n = 7`, `f = 2`, an admissible insertion order and the
identity rebalancing) except that the classification uses the honest-replica score of the paper,
and the final ordering after round 2 is not comparator-based γ-Batch-Order-Fair. -/
theorem theorem_6_6_false :
    (1 / 2 : ℝ) < 1 ∧ (2 * (1 : ℝ) + 1) * cex.f / (2 * 1 - 1) < cex.n ∧
    cex.InsOK cex.scoreHonest cexIns ∧ (∀ t : BTree (Fin 2), (id t).inorder = t.inorder) ∧
    ¬ BatchOrderFair cex.cmpT (cex.GammaPrec 1) (cex.FO cex.scoreHonest cexIns id 2) := by
  refine ⟨by norm_num, ?_, cex_insOK, fun _ => rfl, ?_⟩
  · simp only [Setup.n, Fintype.card_fin]
    norm_num [cex]
  · rw [cex_FO2]
    exact not_batchOrderFair_pair (by decide) cex_cmpT

/-- In contrast, with the score counting all replicas (`scoreAll`), `m` (supported by 4
replicas) is already shaded in round 1, so both transactions are inserted in round 1 (`z` solid
first, then `m`), and FEAT outputs `FO₁ = [m, z]`, consistent with `cmp_T`. -/
def cexInsAll : ℕ → List (Fin 2)
  | 1 => [0, 1]
  | _ => []

theorem cex_scoreAll_FO1 : cex.FO cex.scoreAll cexInsAll id 1 = [1, 0] := by
  have h10 : cex.cmpT 1 0 = true := by
    have := cex.cmpT_total 0 1
    rw [cex_cmpT] at this
    simpa using this
  show (cex.step cex.scoreAll cexInsAll id 1 ([], [])).1 = _
  simp only [Setup.step, Setup.RO, buildTree, cexInsAll, List.foldl, id, BTree.insert,
    h10, ite_true, BTree.inorder, List.nil_merge, List.nil_append]
  decide

end Podc.FEATOrdering
