import Papers.PODC2012.IterativeApproxBC.Condition

/-!
# Necessity (Theorem 1 of [VTL12])

If some iterative algorithm solves approximate Byzantine consensus on `G` against `f` faults, then
`G` satisfies `Condition G f`.

Proof (as in the paper, via local validity `IterAlg.localValid`): given a partition `F, L, C, R`
violating the condition, let `L` start at `0`, `R` at `1`, `C` at `0`, and let the faulty nodes
send `0` to everybody outside `R` and `1` to `R`. Every `i ∈ L` receives values `≠ 0` only from
`N_i⁻ ∩ (C ∪ R)`, at most `f` nodes, so (by local validity with these nodes as the suspects) it
stays at `0`; symmetrically `R` stays at `1`, and `C` stays in `[0, 1]`. So `L` and `R` never
converge.

The paper's `m⁻ < m` and `M⁺ > M` messages of the faulty nodes are not needed (we send `m`, `M`).
-/

open Finset Cslib.ApproxConsensus

namespace IterativeApproxBC

variable {V : Type*} [Fintype V] [DecidableEq V] {G : Digraph V} {f : ℕ}

/-- **Theorem 1 of [VTL12]** (necessity): if an iterative algorithm (state = output, no sense of
time) satisfies validity and convergence on `G` against up to `f` Byzantine nodes, then for every
partition `F, L, C, R` of the nodes with `|F| ≤ f`, `L, R ≠ ∅`: `C ∪ R ⇒ L` or `L ∪ C ⇒ R`. -/
theorem condition_of_correct (A : IterAlg V) (hA : A.Correct G f) : Condition G f := by
  classical
  intro F L C R hFL hFC hFR hLC hLR hCR hU hF hL hR
  by_contra hcon
  push Not at hcon
  obtain ⟨hnL, hnR⟩ := hcon
  have hmem : ∀ x, x ∈ F ∨ x ∈ L ∨ x ∈ C ∨ x ∈ R := by
    intro x; have : x ∈ F ∪ L ∪ C ∪ R := hU ▸ mem_univ x
    simp only [mem_union] at this; tauto
  let S : Scenario V := ⟨F, fun j => if j ∈ R then 1 else 0, fun _ _ i => if i ∈ R then 1 else 0⟩
  let x := A.run G S
  -- the invariant
  have inv : ∀ t, (∀ i ∈ L, x t i = 0) ∧ (∀ i ∈ R, x t i = 1) ∧
      (∀ i ∉ F, 0 ≤ x t i ∧ x t i ≤ 1) := by
    intro t
    induction t with
    | zero =>
      refine ⟨fun i hi => ?_, fun i hi => ?_, fun i _ => ?_⟩
      · simp [x, S, disjoint_left.mp hLR hi]
      · simp [x, S, hi]
      · simp only [x, IterAlg.run_zero, S]; split_ifs <;> norm_num
    | succ t ih =>
      obtain ⟨ihL, ihR, ihI⟩ := ih
      -- the received vector of `i`
      have hrec : ∀ i j, j ∈ inNbrs G i → 0 ≤ recv G S.F (S.adv t) (x t) i j ∧
          recv G S.F (S.adv t) (x t) i j ≤ 1 := by
        intro i j hj
        by_cases hjF : j ∈ F
        · rw [recv_of_mem_F hj hjF]; simp only [S]; split_ifs <;> norm_num
        · rw [recv_of_mem hj hjF]; exact ihI j hjF
      have hr0 : ∀ i, ∀ j ∉ inNbrs G i, recv G S.F (S.adv t) (x t) i j = 0 :=
        fun i j hj => recv_of_notMem hj
      have hstep : ∀ i, x (t + 1) i = A.Z i (recv G S.F (S.adv t) (x t) i) (x t i) :=
        fun i => A.run_succ G S t i
      refine ⟨fun i hi => ?_, fun i hi => ?_, fun i hi => ?_⟩
      · -- `i ∈ L`: suspects `B = N_i⁻ ∩ (C ∪ R)`, everything else sends `0`
        have hB : #(inNbrs G i ∩ (C ∪ R)) ≤ f := by
          by_contra h; exact hnL ⟨i, hi, by omega⟩
        have := A.localValid hA i (recv G S.F (S.adv t) (x t) i) (x t i) 0 0
          (inNbrs G i ∩ (C ∪ R)) inter_subset_left hB (by rw [ihL i hi]; simp)
          (fun j hj hjB => by
            have hjCR : j ∉ C ∪ R := fun h => hjB (mem_inter.mpr ⟨hj, h⟩)
            rcases hmem j with h | h | h | h
            · rw [recv_of_mem_F hj h]
              simp [S, disjoint_left.mp hLR hi]
            · rw [recv_of_mem hj (disjoint_right.mp hFL h), ihL j h]; simp
            · exact absurd (mem_union_left _ h) hjCR
            · exact absurd (mem_union_right _ h) hjCR) (hr0 i)
        rw [hstep]; linarith [this.1, this.2]
      · -- `i ∈ R`: suspects `B = N_i⁻ ∩ (L ∪ C)`, everything else sends `1`
        have hB : #(inNbrs G i ∩ (L ∪ C)) ≤ f := by
          by_contra h; exact hnR ⟨i, hi, by omega⟩
        have := A.localValid hA i (recv G S.F (S.adv t) (x t) i) (x t i) 1 1
          (inNbrs G i ∩ (L ∪ C)) inter_subset_left hB (by rw [ihR i hi]; simp)
          (fun j hj hjB => by
            have hjLC : j ∉ L ∪ C := fun h => hjB (mem_inter.mpr ⟨hj, h⟩)
            rcases hmem j with h | h | h | h
            · rw [recv_of_mem_F hj h]
              simp [S, hi]
            · exact absurd (mem_union_left _ h) hjLC
            · exact absurd (mem_union_right _ h) hjLC
            · rw [recv_of_mem hj (disjoint_right.mp hFR h), ihR j h]; simp) (hr0 i)
        rw [hstep]; linarith [this.1, this.2]
      · -- any fault-free node stays in `[0, 1]`
        have := A.localValid hA i (recv G S.F (S.adv t) (x t) i) (x t i) 0 1 ∅
          (empty_subset _) (by simp) (ihI i hi) (fun j hj _ => hrec i j hj) (hr0 i)
        rw [hstep]; exact this
  obtain ⟨l, hl⟩ := hL
  obtain ⟨r, hr⟩ := hR
  obtain ⟨T, hT⟩ := (hA S hF).2 (1 / 2) (by norm_num)
  have h := hT T le_rfl l (disjoint_right.mp hFL hl) r (disjoint_right.mp hFR hr)
  change |x T l - x T r| ≤ 1 / 2 at h
  rw [(inv T).1 l hl, (inv T).2.1 r hr] at h
  norm_num at h

end IterativeApproxBC
