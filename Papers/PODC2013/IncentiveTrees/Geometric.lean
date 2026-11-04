import Papers.PODC2013.IncentiveTrees.Basic

/-!
# Theorem 1: the `(a, b)`-geometric mechanism

`R(u) = Σ_{v ∈ T_u} a^{dep_u(v)} · b · C(v)` (Algorithm 1).  With `0 < a < 1` and
`φ ≤ b ≤ (1 - a) Φ` it satisfies SL (by construction), the budget constraint, CCI, CSI,
`φ`-RPC, URO and PO, but not USA (hence not UGSA).  We additionally assume `b > 0`
(only `b = 0 = φ` is excluded; then CCI, CSI and URO fail trivially).
-/

namespace Podc.IncentiveTrees

/-- Depth-discounted contribution `W_a(T) = Σ_{v ∈ T} a^{dep(v)} C(v)`. -/
def Tree.wsum (a : ℝ) : Tree → ℝ
  | .node c ch => c + a * (ch.map (Tree.wsum a)).sum

/-- Algorithm 1: the `(a, b)`-geometric mechanism. -/
def geometric (a b : ℝ) : Mechanism := fun T => b * T.wsum a

section

variable {a : ℝ}

theorem Tree.wsum_node (c : ℝ) (ch : List Tree) :
    (Tree.node c ch).wsum a = c + a * (ch.map (Tree.wsum a)).sum := by
  simp [Tree.wsum]

theorem Tree.wsum_nonneg (ha : 0 ≤ a) : ∀ T : Tree, T.Nonneg → 0 ≤ T.wsum a := by
  refine Tree.ind fun c ch ih h => ?_
  rw [Tree.nonneg_node] at h
  rw [Tree.wsum_node]
  have : 0 ≤ (ch.map (Tree.wsum a)).sum :=
    List.sum_nonneg (by simpa using fun t ht => ih t ht (h.2 t ht))
  have := h.1
  positivity

theorem Tree.total_nonneg : ∀ T : Tree, T.Nonneg → 0 ≤ T.total := by
  refine Tree.ind fun c ch ih h => ?_
  rw [Tree.nonneg_node] at h
  simp only [Tree.total]
  have : 0 ≤ (ch.map Tree.total).sum :=
    List.sum_nonneg (by simpa using fun t ht => ih t ht (h.2 t ht))
  linarith [h.1]

theorem Tree.root_le_wsum (ha : 0 ≤ a) (T : Tree) (hT : T.Nonneg) : T.root ≤ T.wsum a := by
  obtain ⟨c, ch⟩ := T
  rw [Tree.nonneg_node] at hT
  rw [Tree.wsum_node]
  have : 0 ≤ (ch.map (Tree.wsum a)).sum :=
    List.sum_nonneg (by simpa using fun t ht => Tree.wsum_nonneg ha t (hT.2 t ht))
  simp only [Tree.root]
  nlinarith

theorem sum_map_flatten_map {α β : Type*} (L : List α) (g : α → List β) (h : β → ℝ) :
    (((L.map g).flatten).map h).sum = (L.map fun t => ((g t).map h).sum).sum := by
  induction L with
  | nil => simp
  | cons x L ih => simp only [List.map_cons, List.flatten_cons, List.map_append,
      List.sum_append, List.sum_cons, ih]

theorem Tree.wsum_lt_of_joinLeaf {d : ℝ} (ha : 0 < a) (hd : 0 < d) {T T' : Tree}
    (hJ : Tree.JoinLeaf d T T') : T.wsum a < T'.wsum a := by
  induction hJ with
  | atNode c l₁ l₂ =>
    simp [Tree.wsum_node, List.sum_append]
    nlinarith
  | inChild c l₁ l₂ t t' _ ih =>
    simp [Tree.wsum_node, List.sum_append]
    nlinarith

/-- Key budget invariant: `(1 - a) Σ_{v} W_a(T_v) + a W_a(T) ≤ C(T)`. -/
theorem Tree.budget_aux : ∀ T : Tree, T.Nonneg →
    (1 - a) * ((T.subtrees).map (Tree.wsum a)).sum + a * T.wsum a ≤ T.total := by
  refine Tree.ind fun c ch ih h => ?_
  rw [Tree.nonneg_node] at h
  have hsum : (1 - a) * ((ch.map Tree.subtrees).flatten.map (Tree.wsum a)).sum
      + a * (ch.map (Tree.wsum a)).sum ≤ (ch.map Tree.total).sum := by
    rw [sum_map_flatten_map, ← List.sum_map_mul_left, ← List.sum_map_mul_left, ← List.sum_map_add]
    exact List.sum_le_sum fun t ht => ih t ht (h.2 t ht)
  simp only [Tree.subtrees, Tree.total, List.map_cons, List.sum_cons, Tree.wsum_node] at hsum ⊢
  nlinarith

end

/-- Theorem 1 of [Lv–Moscibroda] (journal numbering; PODC Theorem 4.1):
with `0 < a < 1`, `0 < b`, `φ ≤ b ≤ (1 - a) Φ`, the
`(a, b)`-geometric mechanism satisfies nonnegative rewards, the budget constraint, CCI, CSI,
`φ`-RPC, URO and PO; it violates USA and UGSA. -/
theorem theorem_1 {a b φ Φ : ℝ} (ha : 0 < a) (ha1 : a < 1) (hb : 0 < b) (hφb : φ ≤ b)
    (hbΦ : b ≤ (1 - a) * Φ) :
    NonnegReward (geometric a b) ∧ Budget (geometric a b) Φ ∧ CCI (geometric a b) ∧
      CSI (geometric a b) ∧ RPC (geometric a b) φ ∧ URO (geometric a b) ∧
      PO (geometric a b) ∧ ¬ USA (geometric a b) ∧ ¬ UGSA (geometric a b) := by
  have hnUSA : ¬ USA (geometric a b) := by
    -- a participant with contribution 2 splits into a chain of two Sybils of contribution 1
    intro h
    have := h 2 [] [.node 1 [.node 1 [] []] []] (by norm_num) (by simp)
      (by simp) (by simp [Sybil.reals]) (by simp [Sybil.mass]; norm_num)
    simp [Sybil.reward, Sybil.toTree, geometric, Tree.wsum] at this
    nlinarith
  have hURO : URO (geometric a b) := by
    intro R c k hR hc hk
    refine ⟨.leaf (R / (a * b)) :: List.replicate (k - 1) (.leaf 0), by simp; omega, ?_, ?_⟩
    · intro t ht
      rcases List.mem_cons.mp ht with rfl | ht
      · simp; positivity
      · rw [List.eq_of_mem_replicate ht]; simp
    · simp only [geometric, Tree.wsum_node, List.map_cons, List.map_replicate, List.sum_cons,
        List.sum_replicate, List.map_nil, List.sum_nil]
      have : b * (a * (R / (a * b))) = R := by field_simp
      simp only [mul_zero, add_zero, smul_zero]
      nlinarith [mul_pos hb hc]
  refine ⟨?_, ?_, ?_, ?_, ?_, hURO, hURO.po, hnUSA, fun h => hnUSA h.usa⟩
  · intro T hT
    exact mul_nonneg hb.le (Tree.wsum_nonneg ha.le T hT)
  · intro T hT
    have h1 := Tree.budget_aux (a := a) T hT
    have h2 := Tree.wsum_nonneg ha.le T hT
    have h3 := Tree.total_nonneg T hT
    have : ((T.subtrees).map (geometric a b)).sum = b * ((T.subtrees).map (Tree.wsum a)).sum := by
      rw [← List.sum_map_mul_left]; rfl
    rw [this]
    have h4 : (1 - a) * (b * ((T.subtrees).map (Tree.wsum a)).sum) ≤ (1 - a) * (Φ * T.total) := by
      nlinarith [mul_le_mul_of_nonneg_left h1 hb.le, mul_le_mul_of_nonneg_right hbΦ h3,
        mul_nonneg (mul_nonneg hb.le ha.le) h2]
    exact le_of_mul_le_mul_left h4 (by linarith)
  · intro c c' F _ hcc' _
    simp only [geometric, Tree.wsum_node]
    nlinarith
  · intro d T T' _ _ hd hJ
    exact mul_lt_mul_of_pos_left (Tree.wsum_lt_of_joinLeaf ha hd hJ) hb
  · intro T hT
    have := Tree.root_le_wsum ha.le T hT
    obtain ⟨c, ch⟩ := T
    have hc := ((Tree.nonneg_node c ch).1 hT).1
    simp only [geometric, Tree.root] at this ⊢
    nlinarith

end Podc.IncentiveTrees
