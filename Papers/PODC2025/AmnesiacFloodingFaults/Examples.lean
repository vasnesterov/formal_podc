import Papers.PODC2025.AmnesiacFloodingFaults.Faults

/-!
# Counterexamples and concrete runs

* `lemma_5_2_as_stated_false` — Lemma 5.2 with `T` the sinks of `S` (as printed) is false;
  `lemma_5_2` uses the sinks of `S̄`, as the paper's proof does.
* `theorem_5_7_multi_false` — the first claim of Theorem 5.7 is false for initiator sets with
  two nodes: on the path `0 – 1 – 2` with initiators `{0, 2}` no single uni-directional link
  failure breaks broadcast or termination.
* `theorem_5_8_broadcast_false` — the broadcast part of Theorem 5.8 is false: on the same path with
  initiators `{0, 2}`, the Byzantine set `{1}` is a cut vertex set, yet no adversary can prevent
  any node from receiving the message.
* `random_flooding_window_false` — the window argument in the proof of Proposition C.2 (Random
  Flooding terminates once `D + 1` all-ones rounds are followed by an all-zeros round) is false on
  the 5-cycle.

Concrete runs are computed by `decide` with a `Finset` simulation proved equal to the model.
-/

namespace AmnesiacFloodingFaults

open SimpleGraph Finset

section Compute

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- `A_{I,G}` on finite sets. -/
def stepF (I : Finset V) (S : Finset (V × V)) : Finset (V × V) :=
  univ.filter fun e => G.Adj e.1 e.2 ∧ (e.2, e.1) ∉ S ∧ (e.1 ∈ I ∨ ∃ w, (w, e.1) ∈ S)

lemma coe_stepF (I : Finset V) (S : Finset (V × V)) :
    ((stepF G I S : Finset (V × V)) : Config V) = step G I S := by
  ext ⟨u, v⟩; simp [stepF, Active]

/-- `uniRun` on finite sets. -/
def uniSim (I : Finset V) (X : Finset (V × V)) : ℕ → Finset (V × V)
  | 0 => stepF G I ∅ \ X
  | t + 1 => stepF G ∅ (uniSim I X t) \ X

lemma coe_uniSim (I : Finset V) (X : Finset (V × V)) (t : ℕ) :
    ((uniSim G I X t : Finset (V × V)) : Config V) = uniRun G I X t := by
  induction t with
  | zero => simp [uniSim, uniRun, coe_stepF]
  | succ t ih =>
    simp only [uniSim, uniRun, Finset.coe_sdiff, coe_stepF, ih, Finset.coe_empty]

end Compute

/-! ### Lemma 5.2 as printed -/

/-- **Lemma 5.2 as printed is false.** With `T = {u | ∀ v ∈ N(u), (v, u) ∈ S}` (the sinks of `S`,
as in the statement), `A_T(\overline{A_∅(S̄)}) ≠ S` for the single message `S = {(0, 1)}` on an
edge. -/
theorem lemma_5_2_as_stated_false :
    ∃ (S : Config (Fin 2)), IsConfig (⊤ : SimpleGraph (Fin 2)) S ∧
      step ⊤ {u | ∀ v, (⊤ : SimpleGraph (Fin 2)).Adj u v → (v, u) ∈ S}
        (rev (af ⊤ (rev S))) ≠ S := by
  refine ⟨{(0, 1)}, ?_, ?_⟩
  · intro u v h; simp only [Set.mem_singleton_iff, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h; decide
  · intro h
    have : ((1 : Fin 2), (0 : Fin 2)) ∈ step ⊤ {u | ∀ v, (⊤ : SimpleGraph (Fin 2)).Adj u v →
        (v, u) ∈ ({(0, 1)} : Config (Fin 2))} (rev (af ⊤ (rev {(0, 1)}))) := by
      refine ⟨by decide, ?_, Or.inl ?_⟩
      · simp only [mem_rev, mem_step, Set.mem_empty_iff_false, false_or, Active]
        rintro ⟨-, -, w, hw⟩
        simp at hw
      · intro v hv
        fin_cases v
        · simp
        · exact absurd hv (by decide)
    rw [h] at this
    simp at this

/-! ### Theorem 5.7 with two initiators -/

/-- The path `0 – 1 – 2`. -/
def p3 : SimpleGraph (Fin 3) where
  Adj x y := (x = 1 ∨ y = 1) ∧ x ≠ y
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.2 rfl⟩

instance : DecidableRel p3.Adj := fun x y =>
  inferInstanceAs (Decidable ((x = 1 ∨ y = 1) ∧ x ≠ y))

lemma p3_connected : p3.Connected := by
  have h01 : p3.Adj 0 1 := by decide
  have h21 : p3.Adj 2 1 := by decide
  refine Connected.mk fun x y => ?_
  have hx : ∀ x, p3.Reachable x 1 := by
    intro x; fin_cases x
    · exact h01.reachable
    · rfl
    · exact h21.reachable
  exact (hx x).trans (hx y).symm

/-- **The first claim of Theorem 5.7 is false for non-singleton initiator sets.** On the
(connected) path `0 – 1 – 2` with initiators `I = {0, 2} ⊊ V`, for every single failed directed
link, amnesiac flooding still informs every node and terminates. -/
theorem theorem_5_7_multi_false (e : Fin 3 × Fin 3) : ¬ UniFails p3 {0, 2} {e} := by
  have key : ∀ e : Fin 3 × Fin 3, uniSim p3 {0, 2} {e} 2 = ∅ ∧
      ∃ w, (w, 1) ∈ uniSim p3 {0, 2} {e} 0 := by decide
  have hI : (({0, 2} : Finset (Fin 3)) : Set (Fin 3)) = {0, 2} := by simp
  have hX : (({e} : Finset (Fin 3 × Fin 3)) : Set (Fin 3 × Fin 3)) = {e} := by simp
  have hrun : ∀ t, uniRun p3 {0, 2} {e} t = ↑(uniSim p3 {0, 2} {e} t) := by
    intro t; rw [coe_uniSim, hI, hX]
  rintro (h | ⟨v, hv, hna⟩)
  · apply h 2
    rw [hrun, (key e).1]; simp
  · have : v = 1 := by
      fin_cases v <;> simp_all
    subst this
    obtain ⟨w, hw⟩ := (key e).2
    exact hna 0 ⟨w, by rw [hrun]; exact_mod_cast hw⟩

/-- **The PODC version's bound `2|E| - 3` (Theorem 4.1(2) there) fails on the path with two edges.**
The configuration `{(0, 1)}` (a message towards the middle node) needs two rounds to die out, while
`2|E| - 3 = 1`. (The full version's bound `2|E|`, `corollary_5_1_1`, holds.) -/
theorem podc_bound_false :
    p3.edgeFinset.card = 2 ∧ (af p3)^[2 * p3.edgeFinset.card - 3] {((0 : Fin 3), (1 : Fin 3))} ≠ ∅ := by
  have hE : p3.edgeFinset.card = 2 := by decide
  refine ⟨hE, ?_⟩
  rw [hE]
  intro h
  have : ((1 : Fin 3), (2 : Fin 3)) ∈ (af p3)^[2 * 2 - 3] {((0 : Fin 3), (1 : Fin 3))} := by
    simp only [show 2 * 2 - 3 = 1 from rfl, Function.iterate_one]
    refine ⟨by decide, by simp, Or.inr ⟨0, by simp⟩⟩
  rw [h] at this; exact this

/-! ### Theorem 5.8, broadcast part -/

/-- **The broadcast part of Theorem 5.8 is false.** On the path `0 – 1 – 2` with initiators
`{0, 2}` and Byzantine set `J = {1}`: `J` is a cut vertex set (every walk from `0` to `2` passes
through it), yet for every adversary every node receives the message or is an initiator. -/
theorem theorem_5_8_broadcast_false :
    (∀ p : p3.Walk 0 2, ∃ x ∈ p.support, x ∈ ({1} : Set (Fin 3))) ∧
      ∀ (k : ℕ) (B : ℕ → Config (Fin 3)) (v : Fin 3),
        v ∈ ({0, 2} : Set (Fin 3)) ∨ ∃ t, Active (byzRun p3 {0, 2} {1} k B t) v := by
  constructor
  · intro p
    cases p with
    | cons h q =>
      rename_i y
      have : y = 1 := by
        have h' := h; simp only [p3] at h'; omega
      exact ⟨y, by simp, this⟩
  · intro k B v
    fin_cases v
    · left; simp
    · right
      refine ⟨0, 0, ?_⟩
      have h01 : ((0 : Fin 3), (1 : Fin 3)) ∈ step p3 {0, 2} ∅ :=
        ⟨by decide, by simp, Or.inl (by simp)⟩
      simp only [byzRun, byzMix]
      split_ifs
      · exact Or.inl ⟨h01, by simp⟩
      · exact h01
    · left; simp

/-! ### Random Flooding (Appendix C.2) -/

/-- One round of Random Flooding with bits `β`: a node with bit `true` forwards to all its
neighbours, a node with bit `false` performs amnesiac flooding. -/
def rfStep {V : Type*} (G : SimpleGraph V) (β : V → Bool) (S : Config V) : Config V :=
  {e | G.Adj e.1 e.2 ∧ Active S e.1 ∧ (β e.1 = true ∨ (e.2, e.1) ∉ S)}

/-- `rfStep` on finite sets. -/
def rfStepF {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (β : V → Bool) (S : Finset (V × V)) : Finset (V × V) :=
  univ.filter fun e => G.Adj e.1 e.2 ∧ (∃ w, (w, e.1) ∈ S) ∧ (β e.1 = true ∨ (e.2, e.1) ∉ S)

lemma coe_rfStepF {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (β : V → Bool) (S : Finset (V × V)) :
    ((rfStepF G β S : Finset (V × V)) : Config V) = rfStep G β S := by
  ext ⟨u, v⟩; simp [rfStepF, rfStep, Active]

/-- The 5-cycle. -/
def c5 : SimpleGraph (Fin 5) where
  Adj x y := x = y + 1 ∨ y = x + 1
  symm := ⟨fun x y h => h.symm⟩
  loopless := ⟨fun x h => by fin_cases x <;> simp_all⟩

instance : DecidableRel c5.Adj := fun x y => inferInstanceAs (Decidable (x = y + 1 ∨ y = x + 1))

/-- **The window argument of Proposition C.2 is false.** On the 5-cycle (diameter `D = 2`),
start Random Flooding at node `0`, and choose the bits: all `0` except node `2` in the third
round. After six rounds the only message is `(0, 1)`. Then `D + 1 = 3` rounds with all bits `1`
followed by rounds with all bits `0` do not stop the flood within the `D + 2` rounds claimed by the
proof (the configuration is still non-empty two rounds after the all-zeros round starts). -/
theorem random_flooding_window_false :
    let β₀ : Fin 5 → Bool := fun _ => false
    let β₂ : Fin 5 → Bool := fun x => decide (x = 2)
    let β₁ : Fin 5 → Bool := fun _ => true
    let S₆ := rfStep c5 β₀ (rfStep c5 β₀ (rfStep c5 β₀ (rfStep c5 β₂ (rfStep c5 β₀
      (rfStep c5 β₀ (step c5 {0} ∅))))))
    S₆ = {(0, 1)} ∧ rfStep c5 β₀ (rfStep c5 β₀ (rfStep c5 β₁ (rfStep c5 β₁
      (rfStep c5 β₁ S₆)))) ≠ ∅ := by
  intro β₀ β₂ β₁ S₆
  have h0 : step c5 {0} ∅ = ↑(stepF c5 {0} ∅) := by rw [coe_stepF]; simp
  simp only [S₆, h0, ← coe_rfStepF]
  constructor
  · have : rfStepF c5 β₀ (rfStepF c5 β₀ (rfStepF c5 β₀ (rfStepF c5 β₂ (rfStepF c5 β₀
        (rfStepF c5 β₀ (stepF c5 {0} ∅)))))) = {(0, 1)} := by decide
    rw [this]; simp
  · have : rfStepF c5 β₀ (rfStepF c5 β₀ (rfStepF c5 β₁ (rfStepF c5 β₁ (rfStepF c5 β₁
        (rfStepF c5 β₀ (rfStepF c5 β₀ (rfStepF c5 β₀ (rfStepF c5 β₂ (rfStepF c5 β₀
        (rfStepF c5 β₀ (stepF c5 {0} ∅))))))))))) ≠ ∅ := by decide
    exact_mod_cast this

/-! ### Faux-even cycles exist (non-vacuity of `FEC`) -/

/-- Two triangles sharing the vertex `0` (a bowtie). -/
def bowtie : SimpleGraph (Fin 5) :=
  SimpleGraph.fromEdgeSet {s(0, 1), s(1, 2), s(2, 0), s(0, 3), s(3, 4), s(4, 0)}

instance : DecidableRel bowtie.Adj := fun _ _ => by unfold bowtie; infer_instance

/-- The bowtie is a faux-even cycle `FEC_{1,0,1}` (two odd cycles sharing one node). -/
def bowtieFEC : FEC bowtie where
  u := 0
  v := 0
  c₁ := .cons (by decide : bowtie.Adj 0 1) (.cons (by decide : bowtie.Adj 1 2)
    (.cons (by decide : bowtie.Adj 2 0) .nil))
  p := .nil
  c₂ := .cons (by decide : bowtie.Adj 0 3) (.cons (by decide : bowtie.Adj 3 4)
    (.cons (by decide : bowtie.Adj 4 0) .nil))
  isCycle₁ := by rw [Walk.isCycle_def, Walk.isTrail_def]; decide
  isCycle₂ := by rw [Walk.isCycle_def, Walk.isTrail_def]; decide
  odd₁ := by decide
  odd₂ := by decide
  isPath := Walk.IsPath.nil
  inter₁₂ := by decide
  inter₁ := by decide
  inter₂ := by decide

/-- Two triangles joined by an edge (a dumbbell). -/
def dumbbell : SimpleGraph (Fin 6) :=
  SimpleGraph.fromEdgeSet {s(0, 1), s(1, 2), s(2, 0), s(0, 3), s(3, 4), s(4, 5), s(5, 3)}

instance : DecidableRel dumbbell.Adj := fun _ _ => by unfold dumbbell; infer_instance

/-- The dumbbell is a faux-even cycle `FEC_{1,1,1}` (two disjoint odd cycles joined by a path). -/
def dumbbellFEC : FEC dumbbell where
  u := 0
  v := 3
  c₁ := .cons (by decide : dumbbell.Adj 0 1) (.cons (by decide : dumbbell.Adj 1 2)
    (.cons (by decide : dumbbell.Adj 2 0) .nil))
  p := .cons (by decide : dumbbell.Adj 0 3) .nil
  c₂ := .cons (by decide : dumbbell.Adj 3 4) (.cons (by decide : dumbbell.Adj 4 5)
    (.cons (by decide : dumbbell.Adj 5 3) .nil))
  isCycle₁ := by rw [Walk.isCycle_def, Walk.isTrail_def]; decide
  isCycle₂ := by rw [Walk.isCycle_def, Walk.isTrail_def]; decide
  odd₁ := by decide
  odd₂ := by decide
  isPath := by rw [Walk.isPath_def]; decide
  inter₁₂ := by decide
  inter₁ := by decide
  inter₂ := by decide

end AmnesiacFloodingFaults
