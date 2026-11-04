import Papers.PODC2011.PartialReversalAcyclicity.Simulation

/-!
# Counterexamples

1. Invariant 3.2 claims that *exactly one* of its two parts holds for every node. For an isolated
   node both parts hold (`inv_3_2_exactlyOne_false`).
2. The proof of Lemma 5.3 (b), Case 2, claims that if `t.parity[w]` is odd and `w` is a sink
   then `s.list[w] = in-nbrs_w` "by Corollary 3.4", and simulates the step of `w` by a single
   `reverse(w)` of `NewPR` whenever `s.list[w] ≠ nbrs_w`. Both fail for a related pair of
   reachable states on three nodes: `G'init` has one edge `0 → 1`, the destination `2` is
   isolated; `s` is the initial state of `OneStepPR`; `t` is reached in `NewPR` by
   `reverse(1), reverse(0), reverse(0)` and has the initial orientation with
   `count = (2, 1, 0)`. Then `(s, t) ∈ R`, node `1` is a sink, `t.parity[1]` is odd,
   `s.list[1] = ∅ ≠ in-nbrs_1 = {0}`, and the prescribed single step `reverse(1)` of `NewPR`
   reverses nothing while `OneStepPR` reverses the edge `{0,1}` (`lemma_5_3_paper_step_fails`).
   Lemma 5.3 (b) itself is true (`lemma_5_3_b`, two steps are needed here).
-/

noncomputable section
open Classical

namespace Podc.PartialReversalAcyclicity

namespace Counterexamples

/-- Two nodes, no edges, destination `0`. -/
def emptyNet : Network (Fin 2) where
  init _ _ := False
  acyclic u h := by
    cases h with
    | single h => exact h
    | tail _ h => exact h
  dest := 0

/-- Invariant 3.2 ("exactly one of parts 1, 2") is false for an isolated node: in the initial
state of `PR` on a graph without edges, node `1` satisfies both parts. -/
theorem inv_3_2_exactlyOne_false :
    PR.Reachable emptyNet (PR.init emptyNet) ∧
      Part1 emptyNet (PR.init emptyNet) 1 ∧ Part2 emptyNet (PR.init emptyNet) 1 := by
  refine ⟨.refl, PR.part1_and_part2_iff.mpr ⟨?_, rfl⟩⟩
  ext v; simp [Network.nbrs, Network.Adj, emptyNet]

/-- Three nodes, one edge `0 → 1`, destination `2`. -/
def net3 : Network (Fin 3) where
  init a b := a = 0 ∧ b = 1
  acyclic u h := by
    have key : ∀ a b, Relation.TransGen (fun a b : Fin 3 => a = 0 ∧ b = 1) a b →
        a = 0 ∧ b = 1 := by
      intro a b h
      induction h with
      | single h => exact h
      | tail _ h ih => exact absurd (ih.2.symm.trans h.1) (by decide)
    have := key u u h
    exact absurd (this.1.symm.trans this.2) (by decide)
  dest := 2

/-- The `NewPR` state with the initial orientation and `count = (2, 1, 0)`. -/
def t3 : NewPRState (Fin 3) := ⟨net3.initDir, ![2, 1, 0]⟩

theorem net3_adj (a b : Fin 3) : net3.Adj a b ↔ (a = 0 ∧ b = 1 ∨ a = 1 ∧ b = 0) := by
  simp [Network.Adj, net3, and_comm]

theorem net3_initDir (a b : Fin 3) : net3.initDir a b = if b = 0 ∧ a = 1 then .inc else .out := by
  unfold Network.initDir; split_ifs <;> simp_all [net3]

theorem t3_reachable : NewPR.Reachable net3 t3 := by
  -- `reverse(1)`: `1` is an initial sink with even parity, it reverses `in-nbrs_1 = {0}`
  have h1 : NewPR.Step net3 (NewPR.init net3) (NewPR.effect net3 1 (NewPR.init net3)) := by
    refine ⟨1, by decide, ?_, rfl⟩
    intro v hv
    rw [Network.mem_nbrs, net3_adj] at hv
    simp only [NewPR.init, net3_initDir]
    fin_cases v <;> simp_all
  set u1 := NewPR.effect net3 1 (NewPR.init net3)
  have hu1 : u1.dir = fun a b => if a = 0 ∧ b = 1 then .inc else .out := by
    funext a b
    simp only [u1, NewPR.effect, flipAt_apply, NewPR.revSet, NewPR.init, net3_initDir]
    fin_cases a <;> fin_cases b <;> simp [net3]
  have hc1 : u1.count = ![0, 1, 0] := by
    funext a; fin_cases a <;> simp [u1, NewPR.effect, NewPR.init, ]
  -- `reverse(0)`: now a sink with even parity and `in-nbrs_0 = ∅`: a dummy step
  have h2 : NewPR.Step net3 u1 (NewPR.effect net3 0 u1) := by
    refine ⟨0, by decide, ?_, rfl⟩
    intro v hv
    rw [Network.mem_nbrs, net3_adj] at hv
    rw [hu1]; fin_cases v <;> simp_all
  set u2 := NewPR.effect net3 0 u1
  have hu2 : u2.dir = u1.dir := by
    funext a b
    simp only [u2, NewPR.effect, flipAt_apply, NewPR.revSet, hc1]
    fin_cases a <;> fin_cases b <;> simp [net3]
  have hc2 : u2.count = ![1, 1, 0] := by
    funext a; fin_cases a <;> simp [u2, NewPR.effect, hc1, ]
  -- `reverse(0)` again: odd parity, it reverses `out-nbrs_0 = {1}`
  have h3 : NewPR.Step net3 u2 (NewPR.effect net3 0 u2) := by
    refine ⟨0, by decide, ?_, rfl⟩
    intro v hv
    rw [Network.mem_nbrs, net3_adj] at hv
    rw [hu2, hu1]; fin_cases v <;> simp_all
  have h4 : NewPR.effect net3 0 u2 = t3 := by
    ext a b
    · simp only [NewPR.effect, flipAt_apply, NewPR.revSet, hc2, hu2, hu1, t3, net3_initDir]
      fin_cases a <;> fin_cases b <;> simp [net3]
    · fin_cases a <;> simp [NewPR.effect, hc2, t3, ]
  rw [← h4]; exact ((Relation.ReflTransGen.single h1).tail h2).tail h3

/-- The proof of Lemma 5.3 (b), Case 2 (`t.parity[w]` odd, Case 2.1 `s.list[w] ≠ nbrs_w`),
fails on a related pair of reachable states: `s` the initial state of `OneStepPR`, `t = t3`,
`w = 1`. Corollary 3.4 does not give `s.list[w] = in-nbrs_w`, and the single prescribed step
`reverse(w)` of `NewPR` does not reverse the edges that `OneStepPR` reverses. -/
theorem lemma_5_3_paper_step_fails :
    OneStepPR.Reachable net3 (PR.init net3) ∧ NewPR.Reachable net3 t3 ∧
      Rel net3 (PR.init net3) t3 ∧
      OneStepPR.Step net3 (PR.init net3) (PR.effect net3 {1} (PR.init net3)) ∧
      Odd (t3.count 1) ∧ (PR.init net3).list 1 ≠ net3.nbrs 1 ∧
      (PR.init net3).list 1 ≠ net3.inNbrs 1 ∧
      NewPR.Step net3 t3 (NewPR.effect net3 1 t3) ∧
      arcs net3 (NewPR.effect net3 1 t3).dir ≠ arcs net3 (PR.effect net3 {1} (PR.init net3)).dir := by
  have hsink : IsSink net3 net3.initDir 1 := by
    intro v hv
    rw [Network.mem_nbrs, net3_adj] at hv
    rw [net3_initDir]; fin_cases v <;> simp_all
  have h01 : (0 : Fin 3) ∈ net3.nbrs 1 := by rw [Network.mem_nbrs, net3_adj]; simp
  refine ⟨.refl, t3_reachable, ⟨rfl, fun _ _ => Set.empty_subset _, fun _ _ => Set.empty_subset _⟩,
    ⟨1, by decide, hsink, rfl⟩, by decide, ?_, ?_, ⟨1, by decide, hsink, rfl⟩, ?_⟩
  · intro h
    have : (0 : Fin 3) ∈ (PR.init net3).list 1 := h ▸ h01
    simp [PR.init] at this
  · intro h
    have : (0 : Fin 3) ∈ (PR.init net3).list 1 := h ▸ (by simp [net3] : (0 : Fin 3) ∈ net3.inNbrs 1)
    simp [PR.init] at this
  · intro h
    have := congrFun (congrFun h 1) 0
    -- after `NewPR`'s step the edge still points `0 → 1`; after `OneStepPR`'s it points `1 → 0`
    have hrev : (0 : Fin 3) ∈ PR.revSet net3 (PR.init net3) 1 := by
      rw [PR.revSet_eq_nbrs (Or.inl rfl)]; exact h01
    simp only [arcs, PR.effect_singleton_dir, flipAt_apply, hrev, and_self, ite_true,
      eq_iff_iff] at this
    have hn : (0 : Fin 3) ∉ NewPR.revSet net3 t3 1 := by
      simp [NewPR.revSet, t3, net3]
    simp [NewPR.effect, flipAt_apply, t3, net3_initDir, net3_adj] at this
    exact hn this

end Counterexamples

end Podc.PartialReversalAcyclicity

end
