import Papers.PODC2016.AnalysingSI.Characterisation
import Papers.PODC2016.AnalysingSI.Cycles

/-!
# Dynamic robustness criteria (Cerone–Gotsman, PODC 2016, §6)

A dependency graph is viewed as an edge-labelled multigraph with labels `SO`, `WR`, `WW`, `RW`
(`DepGraph.edge`). Cycles may repeat vertices.

* **Theorem 19**: `G ∈ GraphSI \ GraphSER` iff `𝒯_G ⊨ INT`, `G` has a cycle, and every cycle has
  two adjacent anti-dependency edges.
* **Theorem 22**: `G ∈ GraphPSI \ GraphSI` iff `𝒯_G ⊨ INT`, `G` has a cycle without adjacent
  anti-dependency edges, and every cycle has at least two anti-dependency edges.
-/

namespace Podc.AnalysingSI

open Relation

/-- Edge labels of a dependency graph. -/
inductive DLbl where
  | so | wr | ww | rw
  deriving DecidableEq

variable {Obj V : Type*} [DecidableEq Obj] {τ : Type*}

namespace DepGraph

variable (G : DepGraph τ Obj V)

/-- The edges of `G` as an edge-labelled multigraph. -/
def edge : DLbl → τ → τ → Prop
  | .so => G.SO
  | .wr => G.WRu
  | .ww => G.WWu
  | .rw => G.RWu

/-- The cycle has two adjacent anti-dependency edges. -/
def HasAdjRW (w : List (DLbl × τ)) : Prop :=
  CycAdj (fun a b => a = DLbl.rw ∧ b = DLbl.rw) (labels w)

omit [DecidableEq Obj] in
/-- Anti-dependency edges are irreflexive. -/
theorem edge_rw_irrefl (T : τ) : ¬ G.edge DLbl.rw T T := by
  rintro ⟨x, h, -⟩
  exact h rfl

omit [DecidableEq Obj] in
theorem b_iff (T S : τ) : G.B T S ↔ ∃ l, l ≠ DLbl.rw ∧ G.edge l T S := by
  constructor
  · rintro (h | h | h)
    exacts [⟨.so, by decide, h⟩, ⟨.wr, by decide, h⟩, ⟨.ww, by decide, h⟩]
  · rintro ⟨l, hl, h⟩
    cases l
    exacts [Or.inl h, Or.inr (Or.inl h), Or.inr (Or.inr h), absurd rfl hl]

omit [DecidableEq Obj] in
theorem b_eq : G.B = fun T S => ∃ l, l ≠ DLbl.rw ∧ G.edge l T S := by
  funext T S
  exact propext (G.b_iff T S)

omit [DecidableEq Obj] in
theorem union_eq : (fun T S => G.B T S ∨ G.RWu T S) = fun T S => ∃ l, G.edge l T S := by
  funext T S
  apply propext
  rw [b_iff]
  constructor
  · rintro (⟨l, -, h⟩ | h)
    exacts [⟨l, h⟩, ⟨.rw, h⟩]
  · rintro ⟨l, h⟩
    by_cases hl : l = .rw
    · subst hl
      exact Or.inr h
    · exact Or.inl ⟨l, hl, h⟩

omit [DecidableEq Obj] in
/-- `(SO ∪ WR ∪ WW) ; RW?` is acyclic iff no cycle lacks adjacent anti-dependency edges. -/
theorem acyclic_si_iff :
    Acyclic (Comp G.B (ReflGen G.RWu)) ↔ ∀ w, IsCycle G.edge w → HasAdjRW w := by
  have := exists_transGen_comp_iff (E := G.edge) DLbl.rw G.edge_rw_irrefl
  rw [b_eq]
  unfold HasAdjRW
  constructor
  · intro h w hw
    by_contra hn
    obtain ⟨a, ha⟩ := this.mpr ⟨w, hw, hn⟩
    exact h a ha
  · intro h a ha
    obtain ⟨w, hw, hn⟩ := this.mp ⟨a, ha⟩
    exact hn (h w hw)

omit [DecidableEq Obj] in
/-- `SO ∪ WR ∪ WW ∪ RW` is acyclic iff the graph has no cycle. -/
theorem acyclic_ser_iff :
    Acyclic (fun T S => G.B T S ∨ G.RWu T S) ↔ ¬ ∃ w, IsCycle G.edge w := by
  rw [union_eq, exists_cycle_iff]
  unfold Acyclic
  simp only [not_exists]

omit [DecidableEq Obj] in
/-- `(SO ∪ WR ∪ WW)⁺ ; RW?` is irreflexive iff every cycle has at least two anti-dependency
edges. -/
theorem irrefl_psi_iff :
    (∀ T, ¬ Comp (TransGen G.B) (ReflGen G.RWu) T T) ↔
      ∀ w, IsCycle G.edge w → 2 ≤ (labels w).count DLbl.rw := by
  have := exists_comp_transGen_iff (E := G.edge) DLbl.rw G.edge_rw_irrefl
  rw [b_eq]
  constructor
  · intro h w hw
    by_contra hn
    obtain ⟨a, ha⟩ := this.mpr ⟨w, hw, by omega⟩
    exact h a ha
  · intro h a ha
    obtain ⟨w, hw, hn⟩ := this.mp ⟨a, ha⟩
    have := h w hw
    omega

/-- **Theorem 19** of Cerone–Gotsman: `G ∈ GraphSI \ GraphSER` iff `𝒯_G ⊨ INT`, `G` contains a
cycle, and all its cycles have at least two adjacent anti-dependency edges. -/
theorem theorem19 (hG : G.IsDepGraph) :
    (G.IsSI ∧ ¬ G.IsSER) ↔
      G.IntAll ∧ (∃ w, IsCycle G.edge w) ∧ ∀ w, IsCycle G.edge w → HasAdjRW w := by
  unfold IsSI IsSER
  rw [acyclic_si_iff, acyclic_ser_iff]
  tauto

/-- **Theorem 22** of Cerone–Gotsman: `G ∈ GraphPSI \ GraphSI` iff `𝒯_G ⊨ INT`, `G` contains at
least one cycle with no adjacent anti-dependency edges, and all its cycles have at least two
anti-dependency edges. -/
theorem theorem22 (hG : G.IsDepGraph) :
    (G.IsPSI ∧ ¬ G.IsSI) ↔
      G.IntAll ∧ (∃ w, IsCycle G.edge w ∧ ¬ HasAdjRW w) ∧
        ∀ w, IsCycle G.edge w → 2 ≤ (labels w).count DLbl.rw := by
  unfold IsPSI IsSI
  rw [irrefl_psi_iff, acyclic_si_iff]
  have : (∃ w, IsCycle G.edge w ∧ ¬ HasAdjRW w) ↔ ¬ ∀ w, IsCycle G.edge w → HasAdjRW w := by
    simp only [not_forall, exists_prop]
  rw [this]
  tauto

end DepGraph

end Podc.AnalysingSI
