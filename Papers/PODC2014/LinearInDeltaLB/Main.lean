import Papers.PODC2014.LinearInDeltaLB.Simulation
import Papers.PODC2014.LinearInDeltaLB.ECLowerBound
import Podc.Foundations.GroupTheory.FreeGroupLeftOrder

/-!
# Theorem 1 of [GHS14]: no `o(Δ)`-round LOCAL algorithm finds a maximal fractional matching

[M. Göös, J. Hirvonen, J. Suomela, *Linear-in-Δ lower bounds in the LOCAL model*, PODC 2014]

Deterministic LOCAL model with unique identifiers (`IDAlg`, `IDAlg.HasRunTime`, `IDAlg.Solves`):
every `t`-round algorithm that finds a maximal fractional matching on all finite graphs of maximum
degree `≤ Δ` has `t ≥ ⌊Δ/2⌋ - 1` (`theorem1`).

Proof (Section 5.5): for `k = ⌊Δ/2⌋`, order `F_k` left-invariantly (Lemma 4,
`Cslib.FreeGroupOrder.linearOrder`), pick a large homogeneous identifier set `I` (Lemma 5,
`exists_homog`), label a big ball of `F_k` order-preservingly by `I`, and simulate `A` by the
EC-algorithm `simEC` (Sections 5.1–5.4). It has run-time `t` and solves the maximal FM problem on
loopy EC-graphs with `k` colours (`Setup.simEC_isMaxFM`), so `t ≥ k - 1` by Step 1
(`ECAlg.le_runTime`, Section 4). The case `t = 0` (where `τ_0` contains no edges) is handled
directly (`not_hasRunTime_zero`).
-/

namespace Podc.LinearInDeltaLB

open Cslib.Local

/-- A `0`-round algorithm (whose output cannot depend on the graph) cannot find maximal fractional
matchings, already on paths with three nodes. -/
theorem not_hasRunTime_zero {Δ : ℕ} (hΔ : 2 ≤ Δ) {A : IDAlg} (hA : A.Solves Δ) :
    ¬ A.HasRunTime 0 := by
  intro ht
  have hconst : ∀ G G' v, A G v = A G' v := fun G G' v =>
    ht G G' v fun x hx => absurd hx (by simp)
  let G₁ := SimpleGraph.edge (0 : ℕ) 1
  let G₂ := SimpleGraph.edge (1 : ℕ) 2
  let P := G₁ ⊔ G₂
  have n₁₀ : G₁.neighborSet 0 = {1} := by ext x; simp [G₁, SimpleGraph.edge_adj]; omega
  have n₁₁ : G₁.neighborSet 1 = {0} := by ext x; simp [G₁, SimpleGraph.edge_adj]; omega
  have n₂₁ : G₂.neighborSet 1 = {2} := by ext x; simp [G₂, SimpleGraph.edge_adj]; omega
  have n₂₂ : G₂.neighborSet 2 = {1} := by ext x; simp [G₂, SimpleGraph.edge_adj]; omega
  have nP : P.neighborSet 1 = {0, 2} := by
    ext x; simp [P, G₁, G₂, SimpleGraph.edge_adj]; omega
  have fin : ∀ G : SimpleGraph ℕ, G ≤ P → G.edgeSet.Finite := by
    intro G hG
    refine Set.Finite.subset ?_ (SimpleGraph.edgeSet_mono hG)
    simp only [P, G₁, G₂, SimpleGraph.edgeSet_sup, SimpleGraph.edgeSet_edge_of_ne (by simp :
      (0 : ℕ) ≠ 1), SimpleGraph.edgeSet_edge_of_ne (by simp : (1 : ℕ) ≠ 2)]
    exact (Set.finite_singleton _).union (Set.finite_singleton _)
  have deg : ∀ G : SimpleGraph ℕ, G ≤ P → ∀ v, (G.neighborSet v).ncard ≤ Δ := by
    intro G hG v
    refine le_trans ?_ hΔ
    calc (G.neighborSet v).ncard ≤ (P.neighborSet v).ncard :=
          Set.ncard_le_ncard (fun x hx => hG hx) (by
            refine Set.Finite.subset (s := {0, 1, 2}) (by simp) ?_
            intro x hx
            simp [P, G₁, G₂, SimpleGraph.edge_adj] at hx ⊢; omega)
      _ ≤ 2 := by
          by_cases hv : v = 1
          · subst hv; rw [nP, Set.ncard_pair (by simp)]
          · have : P.neighborSet v ⊆ ({1} : Set ℕ) := by
              intro x hx; simp [P, G₁, G₂, SimpleGraph.edge_adj] at hx ⊢; omega
            exact (Set.ncard_le_ncard this (by simp)).trans (by simp)
  have h₁ := hA G₁ (fin _ le_sup_left) (deg _ le_sup_left)
  have h₂ := hA G₂ (fin _ le_sup_right) (deg _ le_sup_right)
  have hP := hA P (fin _ le_rfl) (deg _ le_rfl)
  have a₁ : G₁.Adj 0 1 := by simp [G₁, SimpleGraph.edge_adj]
  have a₂ : G₂.Adj 1 2 := by simp [G₂, SimpleGraph.edge_adj]
  -- on a single edge both endpoints output `1`
  have e₁ : A G₁ 1 0 = 1 := by
    have hm := h₁.maximal 0 1 a₁
    have hs := h₁.symm 0 1 a₁
    rw [n₁₀, n₁₁, finsum_mem_singleton, finsum_mem_singleton] at hm
    rcases hm with h | h <;> linarith
  have e₂ : A G₂ 1 2 = 1 := by
    have hm := h₂.maximal 1 2 a₂
    have hs := h₂.symm 1 2 a₂
    rw [n₂₁, n₂₂, finsum_mem_singleton, finsum_mem_singleton] at hm
    rcases hm with h | h <;> linarith
  have hl := hP.le_one 1
  have f₁ : A P 1 0 = 1 := by rw [hconst P G₁]; exact e₁
  have f₂ : A P 1 2 = 1 := by rw [hconst P G₂]; exact e₂
  rw [nP, finsum_mem_pair (by simp), f₁, f₂] at hl
  norm_num at hl

/-- **Theorem 1** of [GHS14] (deterministic LOCAL): every `t`-round ID-algorithm that finds a
maximal fractional matching on all finite graphs of maximum degree `≤ Δ` has `t ≥ ⌊Δ/2⌋ - 1`.
In particular there is no `o(Δ)`-round algorithm. -/
theorem theorem1 {Δ t : ℕ} {A : IDAlg} (hA : A.Solves Δ) (ht : A.HasRunTime t) :
    Δ / 2 - 1 ≤ t := by
  by_cases hΔ : Δ < 4
  · omega
  rcases Nat.eq_zero_or_pos t with ht0 | ht0
  · subst ht0; exact absurd ht (not_hasRunTime_zero (by omega) hA)
  set k := Δ / 2 with hk
  let _ : LinearOrder (FG k) := Cslib.FreeGroupOrder.linearOrder
  have hlo : ∀ g x y : FG k, x < y → g * x < g * y := fun g x y h =>
    (Cslib.FreeGroupOrder.lt_mul_left_iff g x y).2 h
  let B : Finset (FG k) := (ballF_finite (k := k) (Setup.bigRad t)).toFinset
  obtain ⟨I, hIc, hI⟩ := exists_homog (k := k) A t B.card
  have hS : Setup (k := k) A Δ t I := ⟨hA, ht, ht0, by omega, hI, hlo⟩
  have hΨ : StrictMonoOn (labelOf B I) (ballF k (Setup.bigRad t)) := by
    have := labelOf_strictMonoOn (X := B) hIc
    simpa [B] using this
  have hΨI : labelOf B I '' ballF k (Setup.bigRad t) ⊆ I := by
    rintro _ ⟨x, hx, rfl⟩
    exact labelOf_mem hIc (by simpa [B] using hx)
  have hsolve : (simEC A (labelOf B I) t).SolvesLoopy := fun _ _ _ hG =>
    hS.simEC_isMaxFM hΨ hΨI hG
  have := ECAlg.le_runTime (k := k) (by omega) hsolve (simEC_hasRunTime A _ t)
  omega

end Podc.LinearInDeltaLB
