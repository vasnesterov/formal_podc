import Mathlib
import Cslib.Computability.Distributed.Byzantine.CanonicalRounds.Lemmas

/-!
# Nontrivial convergence problems (Section 2.2 of [AFW26])

[AFW26] H. Attiya, I. Flam, J. L. Welch. *Why Canonical-Round Algorithms Fail for Optimal Byzantine
Resilience.* PODC 2026, doi:10.1145/3796701.3815948.

A problem is a `Spec n V O`: a property of the inputs, the faulty set and the decisions taken so far
(`none` = undecided). Safety (`CanonAlg.Safe`) requires it at every prefix of every admissible
execution. Termination/round complexity is treated separately (`CanonAlg.rounds`).

* `ncSpec x₀ x₁ d₀ d₁`: the generic *nontrivial convergence* problem (agreement between `d₀`
  and `d₁`, validity for the two distinguished inputs).
* `consensusSpec`, `approxSpec ε` (approximate agreement on `ℝ`), `graphApproxSpec G`
  (approximate agreement on a graph, with geodesic convexity), `connectedConsensusSpec R`
  (`R = 1`: crusader agreement, `R = 2`: gradecast), each with the reduction to `ncSpec`
  stated in Section 2.2.
-/

namespace Podc2026.CanonicalRound

open Cslib.Byzantine.CanonicalRounds

variable {n : ℕ} {V O : Type*}

/-- `S` implies `S'` (pointwise). -/
def SpecImplies (S S' : Spec n V O) : Prop := ∀ I F d, S I F d → S' I F d

theorem _root_.Cslib.Byzantine.CanonicalRounds.CanonAlg.Safe.mono {R M : Type*} {alg : CanonAlg n V R M O}
    {f : ℕ} {S S' : Spec n V O} (h : alg.Safe f S) (hS : SpecImplies S S') : alg.Safe f S' :=
  fun I A hA ρ k => hS _ _ _ (h I A hA ρ k)

/-- The generic nontrivial convergence problem (Section 2.2): two distinguished inputs `x₀, x₁`
and decisions `d₀, d₁`. Agreement: `d₀` and `d₁` are not both decided by correct processes;
Validity: if all correct processes have input `xᵢ`, every correct decision is `dᵢ`. -/
def ncSpec (x₀ x₁ : V) (d₀ d₁ : O) : Spec n V O := fun I F d =>
  (∀ p ∉ F, ∀ q ∉ F, d p = some d₀ → d q ≠ some d₁) ∧
  (∀ p ∉ F, d p ≠ none → (∀ q ∉ F, I q = x₀) → d p = some d₀) ∧
  (∀ p ∉ F, d p ≠ none → (∀ q ∉ F, I q = x₁) → d p = some d₁)

/-- Consensus: agreement and (strong) validity: a decided value is the input of a correct
process. -/
def consensusSpec : Spec n V V := fun I F d =>
  (∀ p ∉ F, ∀ q ∉ F, ∀ a b, d p = some a → d q = some b → a = b) ∧
  (∀ p ∉ F, ∀ a, d p = some a → ∃ q ∉ F, I q = a)

/-- Consensus is a nontrivial convergence problem (any two distinct values). -/
theorem consensus_nc {x₀ x₁ : V} (hx : x₀ ≠ x₁) :
    SpecImplies (consensusSpec (n := n)) (ncSpec x₀ x₁ x₀ x₁) := by
  rintro I F d ⟨hag, hval⟩
  refine ⟨fun p hp q hq h0 h1 => hx (hag p hp q hq _ _ h0 h1), ?_, ?_⟩
  · intro p hp hd hall
    obtain ⟨a, ha⟩ := Option.ne_none_iff_exists'.1 hd
    obtain ⟨q, hq, rfl⟩ := hval p hp a ha
    rw [ha, hall q hq]
  · intro p hp hd hall
    obtain ⟨a, ha⟩ := Option.ne_none_iff_exists'.1 hd
    obtain ⟨q, hq, rfl⟩ := hval p hp a ha
    rw [ha, hall q hq]

/-- `ε`-approximate agreement on the reals: decisions at most `ε` apart and within the range of the
correct inputs. -/
def approxSpec (ε : ℝ) : Spec n ℝ ℝ := fun I F d =>
  (∀ p ∉ F, ∀ q ∉ F, ∀ a b, d p = some a → d q = some b → |a - b| ≤ ε) ∧
  (∀ p ∉ F, ∀ a, d p = some a → (∃ q ∉ F, I q ≤ a) ∧ ∃ q ∉ F, a ≤ I q)

/-- Approximate agreement is a nontrivial convergence problem for inputs more than `ε` apart. -/
theorem approx_nc {ε x₀ x₁ : ℝ} (hx : ε < |x₀ - x₁|) :
    SpecImplies (approxSpec (n := n) ε) (ncSpec x₀ x₁ x₀ x₁) := by
  rintro I F d ⟨hag, hval⟩
  have key : ∀ x, (∀ q ∉ F, I q = x) → ∀ p ∉ F, d p ≠ none → d p = some x := by
    intro x hall p hp hd
    obtain ⟨a, ha⟩ := Option.ne_none_iff_exists'.1 hd
    obtain ⟨⟨q, hq, h1⟩, ⟨q', hq', h2⟩⟩ := hval p hp a ha
    rw [hall q hq] at h1; rw [hall q' hq'] at h2
    rw [ha, le_antisymm h2 h1]
  refine ⟨fun p hp q hq h0 h1 => ?_, fun p hp hd hall => key _ hall p hp hd,
    fun p hp hd hall => key _ hall p hp hd⟩
  have := hag p hp q hq _ _ h0 h1
  linarith

/-- A set of vertices is geodesically convex if it contains every vertex on a shortest path
between two of its vertices. -/
def GeodConvex {W : Type*} (G : SimpleGraph W) (S : Set W) : Prop :=
  ∀ u ∈ S, ∀ v ∈ S, ∀ w, G.edist u w + G.edist w v = G.edist u v → w ∈ S

/-- The geodesic convex hull. -/
def geodHull {W : Type*} (G : SimpleGraph W) (S : Set W) : Set W :=
  ⋂₀ {T | S ⊆ T ∧ GeodConvex G T}

/-- Approximate agreement on a graph `G` [Nowak–Rybicki]: decisions within distance one, and in the
geodesic convex hull of the correct inputs. -/
def graphApproxSpec {W : Type*} (G : SimpleGraph W) : Spec n W W := fun I F d =>
  (∀ p ∉ F, ∀ q ∉ F, ∀ a b, d p = some a → d q = some b → G.edist a b ≤ 1) ∧
  (∀ p ∉ F, ∀ a, d p = some a → a ∈ geodHull G {x | ∃ q ∉ F, I q = x})

theorem geodConvex_singleton {W : Type*} (G : SimpleGraph W) (x : W) : GeodConvex G {x} := by
  rintro u rfl v rfl w h
  simp only [SimpleGraph.edist_self, add_eq_zero, SimpleGraph.edist_eq_zero_iff] at h
  exact h.1.symm

/-- Approximate agreement on a graph is a nontrivial convergence problem for two vertices at
distance `2`. -/
theorem graphApprox_nc {W : Type*} {G : SimpleGraph W} {x₀ x₁ : W} (hx : G.edist x₀ x₁ = 2) :
    SpecImplies (graphApproxSpec (n := n) G) (ncSpec x₀ x₁ x₀ x₁) := by
  rintro I F d ⟨hag, hval⟩
  have key : ∀ x, (∀ q ∉ F, I q = x) → ∀ p ∉ F, d p ≠ none → d p = some x := by
    intro x hall p hp hd
    obtain ⟨a, ha⟩ := Option.ne_none_iff_exists'.1 hd
    have hh := hval p hp a ha
    have hsub : {y | ∃ q ∉ F, I q = y} ⊆ ({x} : Set W) := by
      rintro y ⟨q, hq, rfl⟩; exact hall q hq
    have : a ∈ ({x} : Set W) := hh _ ⟨hsub, geodConvex_singleton G x⟩
    rw [ha, this]
  refine ⟨fun p hp q hq h0 h1 => ?_, fun p hp hd hall => key _ hall p hp hd,
    fun p hp hd hall => key _ hall p hp hd⟩
  have := hag p hp q hq _ _ h0 h1
  rw [hx] at this
  exact absurd this (by decide)

/-- Connected consensus with parameter `R` [Attiya–Welch, OPODIS'23]: decisions `(branch, grade)`
with `branch = none` (⊥) iff `grade = 0`, grades in `[0, R]`; grades of correct processes differ by
at most one and their non-⊥ branches agree; a non-⊥ branch is the input of a correct process; if
all correct processes have the same input, the grade is `R`. `R = 1` is crusader agreement,
`R = 2` gradecast. -/
def connectedConsensusSpec (Rg : ℕ) : Spec n V (Option V × ℕ) := fun I F d =>
  (∀ p ∉ F, ∀ a g, d p = some (a, g) → (a = none ∧ g = 0) ∨ (a ≠ none ∧ 1 ≤ g ∧ g ≤ Rg)) ∧
  (∀ p ∉ F, ∀ q ∉ F, ∀ a g b h, d p = some (a, g) → d q = some (b, h) →
    g ≤ h + 1 ∧ h ≤ g + 1 ∧ (a = none ∨ b = none ∨ a = b)) ∧
  (∀ p ∉ F, ∀ v g, d p = some (some v, g) → ∃ q ∉ F, I q = v) ∧
  (∀ p ∉ F, ∀ a g, d p = some (a, g) → (∀ q ∉ F, ∀ q' ∉ F, I q = I q') → g = Rg)

/-- Connected consensus is a nontrivial convergence problem: inputs `v ≠ v'`, decisions
`(v, R)` and `(v', R)`. -/
theorem connectedConsensus_nc {Rg : ℕ} (hR : 1 ≤ Rg) {v v' : V} (hv : v ≠ v') :
    SpecImplies (connectedConsensusSpec (n := n) Rg)
      (ncSpec v v' (some v, Rg) (some v', Rg)) := by
  rintro I F d ⟨hrange, hag, hval1, hval2⟩
  have key : ∀ x, (∀ q ∉ F, I q = x) → ∀ p ∉ F, d p ≠ none → d p = some (some x, Rg) := by
    intro x hall p hp hd
    obtain ⟨⟨a, g⟩, ha⟩ := Option.ne_none_iff_exists'.1 hd
    have hg := hval2 p hp a g ha (fun q hq q' hq' => by rw [hall q hq, hall q' hq'])
    rw [hg] at ha
    rcases hrange p hp a Rg ha with ⟨rfl, h0⟩ | ⟨hne, -, -⟩
    · omega
    · obtain ⟨u, rfl⟩ := Option.ne_none_iff_exists'.1 hne
      obtain ⟨q, hq, rfl⟩ := hval1 p hp u Rg ha
      rw [ha, hall q hq]
  refine ⟨fun p hp q hq h0 h1 => ?_, fun p hp hd hall => key _ hall p hp hd,
    fun p hp hd hall => key _ hall p hp hd⟩
  obtain ⟨-, -, h⟩ := hag p hp q hq _ _ _ _ h0 h1
  simp at h; exact hv h

end Podc2026.CanonicalRound
