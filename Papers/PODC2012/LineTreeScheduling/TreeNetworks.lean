import Papers.PODC2012.LineTreeScheduling.Composite
import Papers.PODC2012.LineTreeScheduling.IdealTD

/-!
# Tree networks: Theorem 5.3, Lemma 6.2 and Theorem 6.3

The input of Section 2: a vertex set `V` (`n = |V|`), tree networks `T q` (`q : Q`) on `V`,
demands `a : A` with end-points `src a, dst a`, profit, height and a set `acc a ⊆ Q` of accessible
networks. A demand instance is a pair `(a, q)` with `q ∈ acc a`; it uses the edges of the path
between `src a` and `dst a` in `T q` (edges of different networks are different: `E = Q × Sym2 V`).

The per-tree layered decompositions of Lemma 4.3 (`Δ = 6`, length `≤ 2⌊log₂ n⌋ + 1`) combine to a
layered decomposition of all instances (`treeLayered`), and the generic results give:

* `theorem_5_3`: unit heights, `(1-ε) · p(Opt) ≤ 7 · p(S)`;
* `lemma_6_2`: narrow instances, `(1-ε) · p(Opt) ≤ 73 · p(S)`;
* `theorem_6_3`: arbitrary heights `h_min ≤ h ≤ 1`, `(1-ε) · p(Opt) ≤ 80 · p(S)`;

each after `ℓ · b · K` steps of the first phase (one MIS computation per step), with
`ℓ = 2⌊log₂ n⌋ + 1`, `b` stages with `ξ^b ≤ ε` and `K` steps with `p_max < 2^K p_min`.
-/

set_option linter.unusedSectionVars false

namespace Podc.LineTreeScheduling

open Finset

variable {V A Q : Type*} [Fintype V] [DecidableEq V] [DecidableEq A] [DecidableEq Q]

/-- Input of the throughput maximization problem on tree networks (Section 2). -/
structure TreeInput (V A Q : Type*) where
  /-- The tree networks. -/
  T : Q → SimpleGraph V
  /-- First end-point of a demand. -/
  src : A → V
  /-- Second end-point of a demand. -/
  dst : A → V
  /-- The networks accessible to the processor owning a demand. -/
  acc : A → Finset Q
  /-- Profit. -/
  profit : A → ℝ
  /-- Height (bandwidth requirement). -/
  height : A → ℝ

namespace TreeInput

variable (P : TreeInput V A Q)

/-- Demand instances: a demand and an accessible tree network. -/
def Inst' : Type _ := {x : A × Q // x.2 ∈ P.acc x.1}

instance [Fintype A] [Fintype Q] : Fintype P.Inst' := by unfold Inst'; infer_instance
instance : DecidableEq P.Inst' := by unfold Inst'; infer_instance

/-- The abstract instance: `(a, q)` uses the edges of the `T q`-path between the end-points. -/
noncomputable def toInst : Inst A P.Inst' (Q × Sym2 V) where
  dem d := d.1.1
  path d := (pathEdges (P.T d.1.2) (P.src d.1.1) (P.dst d.1.1)).map
    ⟨fun e => (d.1.2, e), fun _ _ h => by simpa using h⟩
  profit d := P.profit d.1.1

lemma mem_path {d : P.Inst'} {e : Q × Sym2 V} :
    e ∈ P.toInst.path d ↔ e.1 = d.1.2 ∧ e.2 ∈ pathEdges (P.T d.1.2) (P.src d.1.1) (P.dst d.1.1) := by
  obtain ⟨q, e⟩ := e
  simp only [toInst, Finset.mem_map]
  constructor
  · rintro ⟨e', he', rfl, rfl⟩; exact ⟨rfl, he'⟩
  · rintro ⟨rfl, he⟩; exact ⟨e, he, rfl⟩

/-- Two demand instances overlap iff they belong to the same tree network and their paths share an
edge (Section 2); so independent sets of instances are exactly the feasible solutions of the
original problem. -/
lemma overlap_iff {d₁ d₂ : P.Inst'} :
    P.toInst.Overlap d₁ d₂ ↔ d₁.1.2 = d₂.1.2 ∧
      (pathEdges (P.T d₁.1.2) (P.src d₁.1.1) (P.dst d₁.1.1) ∩
        pathEdges (P.T d₁.1.2) (P.src d₂.1.1) (P.dst d₂.1.1)).Nonempty := by
  constructor
  · rintro ⟨⟨q, e⟩, he⟩
    rw [Finset.mem_inter, mem_path, mem_path] at he
    obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ := he
    have hq : d₁.1.2 = d₂.1.2 := h1.symm.trans h3
    refine ⟨hq, e, Finset.mem_inter.2 ⟨h2, ?_⟩⟩
    rw [hq]; exact h4
  · rintro ⟨hq, e, he⟩
    rw [Finset.mem_inter] at he
    refine ⟨(d₁.1.2, e), Finset.mem_inter.2 ⟨(P.mem_path).2 ⟨rfl, he.1⟩, (P.mem_path).2 ⟨hq, ?_⟩⟩⟩
    rw [← hq]; exact he.2

/-- The layered decompositions of the individual tree networks combine to a layered
decomposition of all demand instances (Section 5: `G_k = ⋃_q G_k^{(q)}`). -/
noncomputable def layeredOfTrees {Δ ℓ : ℕ} (LD : ∀ q, LayeredDecomp (P.T q) Δ ℓ) :
    P.toInst.Layered Δ ℓ where
  grp d := (LD d.1.2).grp (P.src d.1.1) (P.dst d.1.1)
  crit d := ((LD d.1.2).crit (P.src d.1.1) (P.dst d.1.1)).map
    ⟨fun e => (d.1.2, e), fun _ _ h => by simpa using h⟩
  grp_lt d := (LD d.1.2).grp_lt _ _
  crit_subset d := by
    intro e he
    simp only [Finset.mem_map] at he
    obtain ⟨e', he', rfl⟩ := he
    exact (P.mem_path).2 ⟨rfl, (LD d.1.2).crit_subset _ _ he'⟩
  card_crit d := by rw [Finset.card_map]; exact (LD d.1.2).card_crit _ _
  prop d₁ d₂ hg hov := by
    obtain ⟨hq, hne⟩ := (P.overlap_iff).1 hov
    obtain ⟨⟨a₂, q₂⟩, h₂⟩ := d₂
    simp only at hq; subst hq
    obtain ⟨e, he⟩ := (LD d₁.1.2).prop _ _ _ _ hg hne
    rw [Finset.mem_inter] at he
    exact ⟨(d₁.1.2, e), Finset.mem_inter.2 ⟨Finset.mem_map.2 ⟨e, he.1, rfl⟩,
      (P.mem_path).2 ⟨rfl, he.2⟩⟩⟩

/-- The layered decomposition of all instances obtained from the ideal tree decompositions
(Lemma 4.3): critical set size `6`, length `2⌊log₂ n⌋ + 1`. -/
noncomputable def treeLayered (hT : ∀ q, (P.T q).IsTree) :
    P.toInst.Layered 6 (2 * Nat.log 2 (Fintype.card V) + 1) :=
  P.layeredOfTrees fun q => Classical.choice (lemma_4_3 (hT q))

lemma ξNarrow_six (hmin : ℝ) : ξNarrow 6 hmin = 37 / (37 + hmin) := by
  unfold ξNarrow; norm_num

variable [Fintype A] [Fintype Q]

/-- **Theorem 5.3** (main result: unit-height throughput maximization on tree networks). Let
`0 < ε < 1`, `ξ = 14/15`, `b` stages with `(14/15)^b ≤ ε`, `K` steps per stage with
`p_max < 2^K p_min`, and any MIS oracle. The algorithm of Figure 7 runs `ℓ b K` steps with
`ℓ = 2⌊log₂ n⌋ + 1` and outputs a feasible solution `S` with `(1-ε) · p(Opt) ≤ 7 · p(S)`, i.e. an
approximation ratio `7/(1-ε)` (`= 7 + ε'` for `ε = ε'/(7+ε')`); the bound even holds against the
LP optimum (`theorem_5_3_lp`). -/
theorem theorem_5_3 (hT : ∀ q, (P.T q).IsTree) {pmin pmax : ℝ} (hpmin0 : 0 < pmin)
    (hpmin : ∀ a, pmin ≤ P.profit a) (hpmax : ∀ a, P.profit a ≤ pmax) {ε : ℝ}
    {b K : ℕ} (hb : (14 / 15 : ℝ) ^ b ≤ ε) (hK : pmax < 2 ^ K * pmin)
    {mis : ℕ → Finset P.Inst' → Finset P.Inst'} (hmis : ∀ t U, P.toInst.IsMIS U (mis t U)) :
    let L := P.treeLayered hT
    let S := P.toInst.solU (P.toInst.algI (unitRule L.crit) ⟨L.grp, b, K, ξUnit 6⟩ mis)
      ((2 * Nat.log 2 (Fintype.card V) + 1) * b * K)
    P.toInst.IsIndep S ∧
      ∀ O, P.toInst.IsIndep O → (1 - ε) * P.toInst.profitOf O ≤ 7 * P.toInst.profitOf S := by
  intro L S
  have hb' : ξUnit 6 ^ b ≤ ε := by rw [ξUnit_six]; exact hb
  refine ⟨(Inst.unit_alg L hpmin0 (fun d => hpmin d.1.1) (fun d => hpmax d.1.1) hb' hK hmis
    (x := 0) ⟨fun _ => le_rfl, fun e => by simp, fun a => by simp⟩).1, fun O hO => ?_⟩
  have := (Inst.unit_alg L hpmin0 (fun d => hpmin d.1.1) (fun d => hpmax d.1.1) hb' hK hmis
    (Inst.IsIndep.isLPFeasible _ hO)).2
  rw [Inst.lpValue_ind] at this
  norm_num at this
  rw [div_mul_eq_mul_div, div_le_iff₀ (by norm_num)] at this
  linarith

/-- Theorem 5.3 against the LP relaxation. -/
theorem theorem_5_3_lp (hT : ∀ q, (P.T q).IsTree) {pmin pmax : ℝ} (hpmin0 : 0 < pmin)
    (hpmin : ∀ a, pmin ≤ P.profit a) (hpmax : ∀ a, P.profit a ≤ pmax) {ε : ℝ}
    {b K : ℕ} (hb : (14 / 15 : ℝ) ^ b ≤ ε) (hK : pmax < 2 ^ K * pmin)
    {mis : ℕ → Finset P.Inst' → Finset P.Inst'} (hmis : ∀ t U, P.toInst.IsMIS U (mis t U))
    {x : P.Inst' → ℝ} (hx : P.toInst.IsLPFeasible (fun _ => 1) x) :
    let L := P.treeLayered hT
    let S := P.toInst.solU (P.toInst.algI (unitRule L.crit) ⟨L.grp, b, K, ξUnit 6⟩ mis)
      ((2 * Nat.log 2 (Fintype.card V) + 1) * b * K)
    (1 - ε) / 7 * P.toInst.lpValue x ≤ P.toInst.profitOf S := by
  intro L S
  have hb' : ξUnit 6 ^ b ≤ ε := by rw [ξUnit_six]; exact hb
  have := (Inst.unit_alg L hpmin0 (fun d => hpmin d.1.1) (fun d => hpmax d.1.1) hb' hK hmis hx).2
  norm_num at this
  exact this

/-- **Lemma 6.2** (narrow instances on tree networks). For heights `h_min ≤ h ≤ 1/2`,
`ξ = 37/(37 + h_min)`, `b` stages with `ξ^b ≤ ε`, `K` steps per stage with `p_max < 2^K p_min` and
any MIS oracle, the output is feasible and `(1-ε) · p(Opt) ≤ 73 · p(S)`. -/
theorem lemma_6_2 (hT : ∀ q, (P.T q).IsTree) {hmin : ℝ} (hmin0 : 0 < hmin)
    (hmin12 : hmin ≤ 1 / 2) (hhmin : ∀ a, hmin ≤ P.height a) (hh : ∀ a, P.height a ≤ 1 / 2)
    {pmin pmax : ℝ} (hpmin0 : 0 < pmin) (hpmin : ∀ a, pmin ≤ P.profit a)
    (hpmax : ∀ a, P.profit a ≤ pmax) {ε : ℝ} {b K : ℕ}
    (hb : (37 / (37 + hmin)) ^ b ≤ ε) (hK : pmax < 2 ^ K * pmin)
    {mis : ℕ → Finset P.Inst' → Finset P.Inst'} (hmis : ∀ t U, P.toInst.IsMIS U (mis t U)) :
    let L := P.treeLayered hT
    let S := P.toInst.solH (fun d => P.height d.1.1) (P.toInst.algI
      (narrowRule (fun d => P.height d.1.1) L.crit) ⟨L.grp, b, K, ξNarrow 6 hmin⟩ mis)
      ((2 * Nat.log 2 (Fintype.card V) + 1) * b * K)
    P.toInst.IsHFeasible (fun d => P.height d.1.1) S ∧
      ∀ O, P.toInst.IsHFeasible (fun d => P.height d.1.1) O →
        (1 - ε) * P.toInst.profitOf O ≤ 73 * P.toInst.profitOf S := by
  intro L S
  have hb' : ξNarrow 6 hmin ^ b ≤ ε := by rw [ξNarrow_six]; exact hb
  refine ⟨(Inst.narrow_alg L hmin0 hmin12 (fun d => hhmin d.1.1) (fun d => hh d.1.1) hpmin0
    (fun d => hpmin d.1.1) (fun d => hpmax d.1.1) hb' hK hmis (x := 0)
    ⟨fun _ => le_rfl, fun e => by simp, fun a => by simp⟩).1, fun O hO => ?_⟩
  have := (Inst.narrow_alg L hmin0 hmin12 (fun d => hhmin d.1.1) (fun d => hh d.1.1) hpmin0
    (fun d => hpmin d.1.1) (fun d => hpmax d.1.1) hb' hK hmis
    (Inst.IsHFeasible.isLPFeasible _ hO)).2
  rw [Inst.lpValue_ind] at this
  norm_num at this
  rw [div_mul_eq_mul_div, div_le_iff₀ (by norm_num)] at this
  linarith

/-- **Theorem 6.3** (arbitrary heights on tree networks). For heights `h_min ≤ h ≤ 1` with
`h_min ≤ 1/2`: run the unit-height algorithm (`ξ = 14/15`, `bw` stages) on the wide instances and
the narrow algorithm (`ξ = 37/(37+h_min)`, `bn` stages) on the narrow ones and keep, on every tree
network, the more profitable of the two solutions. The output is feasible and
`(1-ε) · p(Opt) ≤ 80 · p(S)` (ratio `(7 + 73)/(1-ε)`). -/
theorem theorem_6_3 (hT : ∀ q, (P.T q).IsTree) {hmin : ℝ} (hmin0 : 0 < hmin)
    (hmin12 : hmin ≤ 1 / 2) (hhmin : ∀ a, hmin ≤ P.height a) (hh1 : ∀ a, P.height a ≤ 1)
    {pmin pmax : ℝ} (hpmin0 : 0 < pmin) (hpmin : ∀ a, pmin ≤ P.profit a)
    (hpmax : ∀ a, P.profit a ≤ pmax) {ε : ℝ} (hε1 : ε < 1) {bw bn K : ℕ}
    (hbw : (14 / 15 : ℝ) ^ bw ≤ ε) (hbn : (37 / (37 + hmin)) ^ bn ≤ ε) (hK : pmax < 2 ^ K * pmin)
    (misW misN)
    (hmisW : ∀ t U, (P.toInst.restrict (Inst.Wide (fun d => P.height d.1.1))).IsMIS U (misW t U))
    (hmisN : ∀ t U, (P.toInst.restrict (Inst.Narrow (fun d => P.height d.1.1))).IsMIS U
      (misN t U)) :
    let S := P.toInst.arbSol (P.treeLayered hT) (fun d => P.height d.1.1) hmin bw bn K
      (fun d => d.1.2) misW misN
    P.toInst.IsHFeasible (fun d => P.height d.1.1) S ∧
      ∀ O, P.toInst.IsHFeasible (fun d => P.height d.1.1) O →
        (1 - ε) * P.toInst.profitOf O ≤ 80 * P.toInst.profitOf S := by
  intro S
  have hbw' : ξUnit 6 ^ bw ≤ ε := by rw [ξUnit_six]; exact hbw
  have hbn' : ξNarrow 6 hmin ^ bn ≤ ε := by rw [ξNarrow_six]; exact hbn
  have := Inst.arbitrary_alg (P.treeLayered hT) hmin0 hmin12 (fun d => hhmin d.1.1)
    (fun d => hh1 d.1.1) (fun d₁ d₂ h => by simp only [toInst] at h; rw [h]) (fun d => d.1.2)
    (fun d₁ d₂ hov => ((P.overlap_iff).1 hov).1)
    hpmin0 (fun d => hpmin d.1.1) (fun d => hpmax d.1.1) hε1 hbw' hbn' hK hmisW hmisN
  refine ⟨this.1, fun O hO => ?_⟩
  have := this.2 O hO
  norm_num at this
  exact this

end TreeInput

end Podc.LineTreeScheduling
