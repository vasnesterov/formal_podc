import Papers.PODC2019.CommComplexityBA.Theorem13
import Papers.PODC2019.CommComplexityBA.Basic

/-!
# Theorem 13 fails for `n = 2`

With two nodes (sender `0` and node `1`), `C = 1`: the sender sends its bit once; node `1` outputs
`true` iff it received `true` from the sender in round 0. This solves Byzantine broadcast with
probability `1` against every adaptive adversary corrupting one node, and only the sender ever
speaks. So the paper's Theorem 13 (BB; Theorem 3 for BA is unaffected) needs an assumption such as `n ≥ C + 2` (our
`theorem_13`); the proof needs a forever-honest node other than `S` in `W_{h,b}`.
-/

set_option linter.unusedSectionVars false

open MeasureTheory

namespace CommComplexityBA.NoSetup

/-- Did node `1` receive `true` from the sender? -/
def rcvTrue (i0 : MInbox (Fin 2) Bool) : Bool := decide (true ∈ i0 0)

/-- The two-node protocol. -/
def twoNode : Protocol (Fin 2) (Option Bool) Bool Unit where
  send _ x _ h _ := match x, h with
    | some b, [] => {b}
    | _, _ => 0
  decide _ x _ h := match x, h with
    | some b, _ => some b
    | none, [] => none
    | none, i0 :: _ => some (rcvTrue i0)

section

variable {R : Type*} (A : Adversary (Fin 2) Bool R 1) (ρ : R) (b : Bool) (ω : Fin 2 → Unit)

lemma twoNode_output0 : twoNode.output (bbInput 0 b) ω A ρ 0 = some b := by
  rw [Protocol.output, firstSome_eq_some_iff]
  exact ⟨0, by simp [twoNode, bbInput], fun r hr => by omega⟩

lemma twoNode_output1 : twoNode.output (bbInput 0 b) ω A ρ 1 =
    some (rcvTrue (fun p => twoNode.sent (bbInput 0 b) ω (fun _ => []) p 1 + A.inject ρ [] p 1)) := by
  rw [Protocol.output, firstSome_eq_some_iff]
  refine ⟨1, ?_, fun r hr => ?_⟩
  · simp [Protocol.run, Protocol.runI, twoNode, bbInput]
  · obtain rfl : r = 0 := by omega
    simp [Protocol.run, Protocol.runI, twoNode, bbInput]

lemma twoNode_sent1 (h : Fin 2 → MHistory (Fin 2) Bool) (q : Fin 2) :
    twoNode.sent (bbInput 0 b) ω h 1 q = 0 := by
  simp [Protocol.sent, twoNode, bbInput]

lemma twoNode_good : BBGood twoNode 0 b A ω ρ := by
  have h0 := twoNode_output0 A ρ b ω
  have h1 := twoNode_output1 A ρ b ω
  -- if both nodes are honest, node 1 outputs `b`
  have hboth : twoNode.Honest (bbInput 0 b) ω A ρ 0 → twoNode.Honest (bbInput 0 b) ω A ρ 1 →
      twoNode.output (bbInput 0 b) ω A ρ 1 = some b := by
    intro hH0 hH1
    have hinj : A.inject ρ [] 0 1 = 0 := by
      by_contra hne
      rcases A.inject_spec ρ [] 0 1 hne with h | h
      · exact hH0 0 h
      · exact hH1 0 h
    rw [h1]
    cases b <;> simp [rcvTrue, hinj, Protocol.sent, twoNode, bbInput]
  have hall : ∀ p, twoNode.output (bbInput 0 b) ω A ρ p ≠ none := by
    intro p; fin_cases p
    · simp [h0]
    · simp [h1]
  refine ⟨⟨fun p _ => Option.isSome_iff_ne_none.mpr (hall p), ?_⟩, ?_⟩
  · intro p q x y hp hq hpx hqy
    have h01 : ∀ r : Fin 2, r = 0 ∨ r = 1 := by decide
    have hpq : twoNode.output (bbInput 0 b) ω A ρ p = twoNode.output (bbInput 0 b) ω A ρ q := by
      rcases h01 p with rfl | rfl <;> rcases h01 q with rfl | rfl
      · rfl
      · rw [h0, hboth hp hq]
      · rw [h0, hboth hq hp]
      · rfl
    rw [hpq, hqy] at hpx
    exact (Option.some.inj hpx).symm
  · intro hs p hp
    fin_cases p
    · exact h0
    · exact hboth hs hp

lemma twoNode_few : FewSpeakers twoNode 0 b A ω ρ := by
  unfold FewSpeakers
  have hsub : {p | twoNode.Honest (bbInput 0 b) ω A ρ p ∧ twoNode.Speaks (bbInput 0 b) ω A ρ p} ⊆
      {0} := by
    rintro p ⟨-, r, q, hq⟩
    fin_cases p
    · rfl
    · exact absurd (twoNode_sent1 b ω _ q) hq
  exact (Set.ncard_le_ncard hsub (Set.toFinite _)).trans (by simp)

end

/-- **Counterexample to Theorem 13 for `n = 2`**: with `C = 1`, the two-node protocol solves
Byzantine broadcast and has at most `C` honest speakers, both with probability `1 > 5/6`. -/
theorem theorem_13_false_n2 :
    SolvesBB twoNode (fun _ => Measure.dirac ()) 0 1 1 ∧
      FewSpeakersWP twoNode (fun _ => Measure.dirac ()) 0 1 1 := by
  constructor
  · intro A b
    have : {x : (Fin 2 → Unit) × (Fin 2 → Unit) | ¬ BBGood twoNode 0 b A x.1 x.2} = ∅ := by
      ext x; simp [twoNode_good A x.2 b x.1]
    simp [this]
  · intro A b
    have : {x : (Fin 2 → Unit) × (Fin 2 → Unit) | ¬ FewSpeakers twoNode 0 b A x.1 x.2} = ∅ := by
      ext x; simp [twoNode_few A x.2 b x.1]
    simp [this]

end CommComplexityBA.NoSetup
