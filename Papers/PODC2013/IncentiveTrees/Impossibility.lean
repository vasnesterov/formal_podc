import Papers.PODC2013.IncentiveTrees.Basic

/-!
# Theorem 3: SL, PO and UGSA are incompatible

* `theorem_3`: no SL mechanism satisfies PO (positive profit, as described in words) and UGSA.
  The paper's proof goes through verbatim; only the `k = 1` case of PO is used, and neither the
  budget constraint nor nonnegativity of rewards is needed.
* `theorem_3_false_for_weak_PO`: with PO read as in the paper's formal definition
  (`R(u) ≥ C(u)`, zero profit suffices) the statement is false: for `Φ = 1` the mechanism
  `R(u) = C(u)` is subtree-local, within budget, and satisfies PO, UGSA (hence USA), CCI and
  `φ`-RPC for every `φ ≤ 1`.
-/

namespace Podc.IncentiveTrees

/-- Theorem 3 of [Lv–Moscibroda] (journal numbering; PODC Theorem 4.3):
there is no Incentive Tree mechanism that simultaneously
achieves SL, PO and UGSA.  (SL is built into `Mechanism`; PO is the "positive profit" version.) -/
theorem theorem_3 (f : Mechanism) : ¬ (PO f ∧ UGSA f) := by
  rintro ⟨hPO, hU⟩
  -- PO with one child tree `T* = node c₀ F₀` gives `v*` (contribution 1) positive profit.
  obtain ⟨F, hlen, hF, hprof⟩ := hPO 1 1 one_pos one_pos
  obtain ⟨Tstar, rfl⟩ : ∃ T, F = [T] := List.length_eq_one_iff.mp hlen
  obtain ⟨c₀, F₀⟩ := Tstar
  have hT : 0 ≤ c₀ ∧ ∀ t ∈ F₀, t.Nonneg := by
    simpa [Tree.Nonneg] using hF (Tree.node c₀ F₀) (by simp)
  obtain ⟨hc₀, hF₀⟩ := hT
  -- `u*` joins as two Sybils `u_a` (contribution `1`) above `u_b` (contribution `c₀`).
  let ub : Sybil := .node c₀ [] F₀
  let ua : Sybil := .node 1 [ub] []
  have h := hU c₀ F₀ [ua] hc₀ hF₀ (by
    simp [ua, ub, hc₀]; exact hF₀)
    (by simp [ua, ub, Sybil.reals])
    (by simp [ua, ub, Sybil.mass])
  simp [ua, ub, Sybil.reward, Sybil.mass, Sybil.toTree] at h
  linarith

/-! ## The formal (weak) definition of PO: a counterexample for `Φ = 1` -/

/-- The mechanism that returns every participant exactly its contribution. -/
def refund : Mechanism := Tree.root

@[simp] theorem refund_node (c : ℝ) (ch : List Tree) : refund (.node c ch) = c := rfl

theorem Tree.sum_subtrees_root (T : Tree) : ((T.subtrees).map Tree.root).sum = T.total := by
  induction T using Tree.rec (motive_2 := fun l =>
      ∀ t ∈ l, ((t.subtrees).map Tree.root).sum = t.total) with
  | node c ch ih =>
    simp only [Tree.subtrees, Tree.total, Tree.root, List.map_cons, List.sum_cons,
      List.map_flatten, List.sum_flatten, List.map_map]
    congr 1
    exact congrArg List.sum (List.map_congr_left ih)
  | nil => rename_i h; cases h
  | cons t l ih₁ ih₂ =>
    rename_i t' ht'
    rcases List.mem_cons.mp ht' with rfl | h
    exacts [ih₁, ih₂ _ h]

theorem Sybil.reward_refund (s : Sybil) : s.reward refund = s.mass := by
  induction s using Sybil.rec (motive_2 := fun l =>
      (l.map (Sybil.reward refund)).sum = (l.map Sybil.mass).sum) with
  | node c s r ih => simp [Sybil.reward, Sybil.mass, Sybil.toTree, ih]
  | nil => simp
  | cons x l ih₁ ih₂ => simp [ih₁, ih₂]

theorem refund_UGSA : UGSA refund := by
  intro c F S _ _ _ _ _
  have : (S.map (Sybil.reward refund)) = S.map Sybil.mass :=
    List.map_congr_left (fun s _ => Sybil.reward_refund s)
  rw [this]
  simp [refund, Tree.root]

theorem refund_POWeak : POWeak refund := by
  intro c k _ _
  refine ⟨List.replicate k (.leaf 0), by simp, ?_, le_refl _⟩
  intro t ht
  rw [List.eq_of_mem_replicate ht]
  simp

theorem refund_budget : Budget refund 1 := by
  intro T _
  rw [one_mul, refund, Tree.sum_subtrees_root]

theorem refund_CCI : CCI refund := fun _ _ _ _ h _ => h

theorem refund_RPC {φ : ℝ} (hφ : φ ≤ 1) : RPC refund φ := by
  rintro ⟨c, ch⟩ h
  have hc : 0 ≤ c := by simp only [Tree.Nonneg] at h; exact h.1
  simp only [refund, Tree.root]
  nlinarith

theorem refund_nonnegReward : NonnegReward refund := by
  rintro ⟨c, ch⟩ h
  simp only [Tree.Nonneg] at h
  exact h.1

/-- Theorem 3 is false for PO as formally defined in the paper (`R(u) ≥ C(u)`): with budget
`Φ = 1` (allowed, `Φ ≤ 1`), `R(u) = C(u)` satisfies SL, PO (weak), UGSA, the budget constraint
and nonnegativity of rewards.  It also satisfies CCI, USA and `φ`-RPC (`φ ≤ 1`). -/
theorem theorem_3_false_for_weak_PO :
    ∃ f : Mechanism, NonnegReward f ∧ Budget f 1 ∧ POWeak f ∧ UGSA f ∧ USA f ∧ CCI f ∧
      ∀ φ ≤ 1, RPC f φ :=
  ⟨refund, refund_nonnegReward, refund_budget, refund_POWeak, refund_UGSA, refund_UGSA.usa,
    refund_CCI, fun _ hφ => refund_RPC hφ⟩

end Podc.IncentiveTrees
