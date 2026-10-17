import Mathlib

/-!
# Generic system model (Section 3 of Nowak–Schmid–Winkler)

T. Nowak, U. Schmid, K. Winkler. *Topological Characterization of Consensus under General Message
Adversaries.* PODC 2019 (full version: *Topological Characterization of Consensus in Distributed
Systems*, arXiv:1905.09590v3).

The paper's generic model for full-information executions:

* a type `C` of configurations and a finite set `P` of processes;
* for every process `p` an equivalence relation `indist p` on configurations
  (`C ∼ₚ D`: `p` has the same view in `C` and `D`);
* the obedient processes `Ob C ⊆ P` of a configuration;
* weak clocks `clock p : C → ℕ`;
* the input values `input C : P → V` (meaningful for initial configurations);
* the set `adm ⊆ (ℕ → C)` of admissible executions `Σ`.

The paper's restrictions are fields of `Model`: disobedient processes do not recover, all processes
are obedient initially, every execution has an obedient process, weak-clock properties, inputs are
locally accessible, and initial configurations are determined by the inputs.

A *decision algorithm* (`DecisionAlg`) is a family `Δₚ : C → Option V` (`none` = `⊥`) that is
constant on `∼ₚ`-classes and irrevocable along admissible executions (the paper's "`C'` reachable
from `C`" is read as "`C'` occurs later than `C` in an admissible execution").

Consensus (Definition 3.1): `SolvesNonUniform` (Termination, Agreement among obedient processes,
Validity) and `SolvesUniform` (Uniform Agreement among all processes). Validity is required for
obedient processes; for uniform consensus this implies validity for all deciding processes
(`SolvesUniform.validity_all`).
-/

namespace TopoConsensus

open Set Filter

/-- The generic system model of Section 3. `P`: processes, `C`: configurations, `V`: values. -/
structure Model (P C V : Type*) where
  /-- `indist p c d`: process `p` cannot distinguish the configurations `c` and `d`. -/
  indist : P → C → C → Prop
  indist_equiv : ∀ p, Equivalence (indist p)
  /-- The obedient processes of a configuration. -/
  Ob : C → Set P
  /-- Weak clocks `χₚ`. -/
  clock : P → C → ℕ
  /-- The input values recorded in a configuration (used for initial configurations). -/
  input : C → P → V
  /-- The admissible executions `Σ`. -/
  adm : Set (ℕ → C)
  /-- Disobedient processes cannot become obedient again. -/
  ob_anti : ∀ γ ∈ adm, ∀ s t, s ≤ t → Ob (γ t) ⊆ Ob (γ s)
  /-- All processes are obedient in initial configurations. -/
  ob_init : ∀ γ ∈ adm, Ob (γ 0) = univ
  /-- Every execution has an obedient process. -/
  ob_nonempty : ∀ γ ∈ adm, (⋂ t, Ob (γ t)).Nonempty
  /-- Weak clocks never run ahead of global time. -/
  clock_le : ∀ p, ∀ δ ∈ adm, ∀ c t, indist p c (δ t) → clock p c ≤ t
  /-- Weak clocks of obedient processes are unbounded. -/
  clock_tendsto : ∀ δ ∈ adm, ∀ p ∈ ⋂ t, Ob (δ t), Tendsto (fun t => clock p (δ t)) atTop atTop
  /-- A process knows its own input value. -/
  input_local : ∀ p, ∀ γ ∈ adm, ∀ δ ∈ adm, ∀ s t, indist p (γ s) (δ t) →
    input (γ 0) p = input (δ 0) p
  /-- There is a unique initial configuration for every input assignment. -/
  init_unique : ∀ γ ∈ adm, ∀ δ ∈ adm, input (γ 0) = input (δ 0) → γ 0 = δ 0

namespace Model

variable {P C V : Type*} (M : Model P C V)

/-- The obedient processes of an execution: `Ob(γ) = ⋂ₜ Ob(Cᵗ)`. -/
def obe (γ : ℕ → C) : Set P := ⋂ t, M.Ob (γ t)

/-- `γ` is `v`-valent: all processes start with input `v` (Definition 5.1). -/
def Valent (γ : ℕ → C) (v : V) : Prop := ∀ p, M.input (γ 0) p = v

theorem indist_refl (p : P) (c : C) : M.indist p c c := (M.indist_equiv p).refl c

theorem indist_symm {p : P} {c d : C} (h : M.indist p c d) : M.indist p d c :=
  (M.indist_equiv p).symm h

theorem indist_trans {p : P} {c d e : C} (h₁ : M.indist p c d) (h₂ : M.indist p d e) :
    M.indist p c e := (M.indist_equiv p).trans h₁ h₂

theorem mem_obe {γ : ℕ → C} {p : P} : p ∈ M.obe γ ↔ ∀ t, p ∈ M.Ob (γ t) := mem_iInter

/-- Finitely many processes: `Ob(Cᵗ)` stabilizes to `Ob(γ)`. -/
theorem exists_ob_stable [Finite P] {γ : ℕ → C} (hγ : γ ∈ M.adm) :
    ∃ T, ∀ t, T ≤ t → M.Ob (γ t) = M.obe γ := by
  classical
  -- for every non-obedient process pick a time at which it is disobedient
  have : ∀ p, ∃ T, p ∉ M.obe γ → p ∉ M.Ob (γ T) := by
    intro p
    by_cases hp : p ∈ M.obe γ
    · exact ⟨0, fun h => (h hp).elim⟩
    · rw [mem_obe] at hp
      push Not at hp
      obtain ⟨T, hT⟩ := hp
      exact ⟨T, fun _ => hT⟩
  choose f hf using this
  cases nonempty_fintype P
  refine ⟨Finset.univ.sup f, fun t ht => ?_⟩
  ext p
  constructor
  · intro hp
    by_contra hp'
    have hle : f p ≤ t := le_trans (Finset.le_sup (Finset.mem_univ p)) ht
    exact hf p hp' (M.ob_anti γ hγ _ _ hle hp)
  · intro hp
    exact (M.mem_obe).1 hp t

/-- `Ob(γ) ≠ ∅` and `Ob(γ) ⊆ Ob(γ t)`. -/
theorem obe_subset (γ : ℕ → C) (t : ℕ) : M.obe γ ⊆ M.Ob (γ t) := fun _ hp => (M.mem_obe).1 hp t

/-- The paper's synchrony requirement that its universal algorithms silently use: a process's view
determines the global time and the process's views at all earlier times (lock-step full-information
executions, or global time given by consistent cuts as in Appendix A.2). -/
def LockstepRecall : Prop :=
  ∀ p, ∀ γ ∈ M.adm, ∀ δ ∈ M.adm, ∀ s t, M.indist p (γ s) (δ t) →
    s = t ∧ ∀ u ≤ s, M.indist p (γ u) (δ u)

/-- All processes are always obedient (fault-free models such as dynamic networks under message
adversaries). -/
def FaultFree : Prop := ∀ c, M.Ob c = univ

end Model

/-- A decision algorithm: `dec p c = some v` means that `p` has decided `v` in `c`. -/
structure DecisionAlg {P C V : Type*} (M : Model P C V) where
  dec : P → C → Option V
  dec_indist : ∀ p c d, M.indist p c d → dec p c = dec p d
  dec_irrev : ∀ γ ∈ M.adm, ∀ p s t, s ≤ t → ∀ v, dec p (γ s) = some v → dec p (γ t) = some v

namespace DecisionAlg

variable {P C V : Type*} {M : Model P C V} (A : DecisionAlg M)

/-- `p` decides `v` in the execution `γ`. -/
def Decides (γ : ℕ → C) (p : P) (v : V) : Prop := ∃ t, A.dec p (γ t) = some v

/-- Termination: every obedient process decides. -/
def Termination : Prop := ∀ γ ∈ M.adm, ∀ p ∈ M.obe γ, ∃ v, A.Decides γ p v

/-- Agreement among obedient processes. -/
def Agreement : Prop :=
  ∀ γ ∈ M.adm, ∀ p ∈ M.obe γ, ∀ q ∈ M.obe γ, ∀ v w, A.Decides γ p v → A.Decides γ q w → v = w

/-- Uniform agreement: all deciding processes agree. -/
def UniformAgreement : Prop :=
  ∀ γ ∈ M.adm, ∀ p q, ∀ v w, A.Decides γ p v → A.Decides γ q w → v = w

/-- (Weak) validity: in a `v`-valent execution, obedient processes can only decide `v`. -/
def Validity : Prop :=
  ∀ γ ∈ M.adm, ∀ v, M.Valent γ v → ∀ p ∈ M.obe γ, ∀ w, A.Decides γ p w → w = v

/-- Non-uniform consensus (Definition 3.1: (T), (A), (V)). -/
def SolvesNonUniform : Prop := A.Termination ∧ A.Agreement ∧ A.Validity

/-- Uniform consensus (Definition 3.1: (T), (UA), (V)). -/
def SolvesUniform : Prop := A.Termination ∧ A.UniformAgreement ∧ A.Validity

theorem SolvesUniform.toNonUniform {A : DecisionAlg M} (h : A.SolvesUniform) :
    A.SolvesNonUniform :=
  ⟨h.1, fun γ hγ p _ q _ v w hv hw => h.2.1 γ hγ p q v w hv hw, h.2.2⟩

/-- In uniform consensus, validity also holds for disobedient deciding processes. -/
theorem SolvesUniform.validity_all {A : DecisionAlg M} (h : A.SolvesUniform) :
    ∀ γ ∈ M.adm, ∀ v, M.Valent γ v → ∀ p w, A.Decides γ p w → w = v := by
  intro γ hγ v hv p w hw
  obtain ⟨q, hq⟩ := M.ob_nonempty γ hγ
  obtain ⟨u, hu⟩ := h.1 γ hγ q hq
  have := h.2.2 γ hγ v hv q hq u hu
  rw [h.2.1 γ hγ p q w u hw hu, this]

end DecisionAlg

/-- Uniform consensus is solvable in `M`. -/
def UniformSolvable {P C V : Type*} (M : Model P C V) : Prop :=
  ∃ A : DecisionAlg M, A.SolvesUniform

/-- Non-uniform consensus is solvable in `M`. -/
def NonUniformSolvable {P C V : Type*} (M : Model P C V) : Prop :=
  ∃ A : DecisionAlg M, A.SolvesNonUniform

end TopoConsensus
