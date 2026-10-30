import Mathlib

/-!
# Near-optimal adjacency labeling scheme for power-law graphs — definitions

Petersen, Rotbart, Simonsen, Wulff-Nilsen, PODC 2016 (brief announcement; full version
arXiv:1502.03971v1).

* `HasAdjLabeling n F X`: an adjacency labeling scheme for the family `F` of graphs on `Fin n`
  whose labels have at most `X` bits. The decoder is fixed before the graph is chosen (it may
  depend on `n`), the encoder sees the whole graph.
* `lg n = ⌈log₂ n⌉`: the number of bits of a vertex identifier (the paper's `log n`).
* `deg G v`, `numDeg G i = |V_i|` (number of vertices of degree `i`).
* `Sparse c G` (`c`-sparse graphs, the family `S_{c,n}`): `|E| ≤ c n`.
* `zeta α = ∑_{i ≥ 1} i^{-α}` and the normalising constant `C α = 1 / ζ(α)` (the paper never
  defines `C`; this is the only value for which its proofs go through, see `differencies.md`).
* `i₁ α n`: the smallest positive integer `i` with `⌊C n / i^α⌋ ≤ 1`.
* `IsPowerLaw α C' G` (Definition 1, the family `P_α`) and `IsProperPowerLaw α G`
  (Definition 2, the family `P'_α` of `α`-proper power-law graphs).
-/

namespace Podc.PowerLawLabeling

open Finset

-- CSLib candidate (adjacency labeling basics)
/-- An *adjacency labeling scheme* for a family `F` of graphs on the vertex set `Fin n`, with
labels of at most `X` bits: a decoder `D` (fixed for all graphs of the family) such that every
graph `G ∈ F` has a labeling `lab` with labels of length `≤ X` from which adjacency of any two
distinct vertices is decided by `D`. -/
def HasAdjLabeling (n : ℕ) (F : SimpleGraph (Fin n) → Prop) (X : ℝ) : Prop :=
  ∃ D : List Bool → List Bool → Prop, ∀ G, F G → ∃ lab : Fin n → List Bool,
    (∀ v, ((lab v).length : ℝ) ≤ X) ∧ ∀ u v, u ≠ v → (G.Adj u v ↔ D (lab u) (lab v))

/-- The paper's `log n`: the number of bits of an identifier in `{0, …, n-1}`, `⌈log₂ n⌉`. -/
abbrev lg (n : ℕ) : ℕ := Nat.clog 2 n

variable {V : Type*}

/-- Degree of a vertex (as `ncard`, so that no `Fintype`/`DecidableRel` instances are needed). -/
noncomputable def deg (G : SimpleGraph V) (v : V) : ℕ := (G.neighborSet v).ncard

/-- `|V_i|`: the number of vertices of degree `i`. -/
noncomputable def numDeg [Fintype V] (G : SimpleGraph V) (i : ℕ) : ℕ :=
  #{v | deg G v = i}

/-- A graph is `c`-*sparse* if it has at most `c n` edges (the family `S_{c,n}`). -/
def Sparse [Fintype V] (c : ℝ) (G : SimpleGraph V) : Prop :=
  (G.edgeSet.ncard : ℝ) ≤ c * Fintype.card V

/-- The Riemann zeta function on the reals, `ζ(α) = ∑_{i ≥ 1} i^{-α}`. -/
noncomputable def zeta (α : ℝ) : ℝ := ∑' i : ℕ, 1 / ((i : ℝ) + 1) ^ α

/-- The normalising constant `C = 1 / ζ(α)` of the power law `|V_k| ≈ C n / k^α`. -/
noncomputable def C (α : ℝ) : ℝ := 1 / zeta α

/-- `i₁`: the smallest positive integer `i` with `⌊C n / i^α⌋ ≤ 1` (Section 2 of the paper). -/
noncomputable def i₁ (α : ℝ) (n : ℕ) : ℕ :=
  sInf {i : ℕ | 1 ≤ i ∧ ⌊C α * n / (i : ℝ) ^ α⌋₊ ≤ 1}

/-- **Definition 1** (the family `P_α`, for a constant `C'`): for every integer `k` between
`(n / log n)^{1/α}` and `n - 1`, `∑_{i=k}^{n-1} |V_i| ≤ C' n / k^{α-1}`.
(`log = log₂`; we also require `1 ≤ k`, which is automatic for `n ≥ 2` and only excludes the
meaningless case `n = 1`, where `n / log n = 1 / 0`.) -/
def IsPowerLaw [Fintype V] (α C' : ℝ) (G : SimpleGraph V) : Prop :=
  ∀ k : ℕ, 1 ≤ k → ((Fintype.card V : ℝ) / Real.logb 2 (Fintype.card V)) ^ (1 / α) ≤ k →
    k ≤ Fintype.card V - 1 →
      ((∑ i ∈ Icc k (Fintype.card V - 1), numDeg G i : ℕ) : ℝ) ≤
        C' * ((Fintype.card V : ℝ) / (k : ℝ) ^ (α - 1))

/-- **Definition 2** (`α`-proper power-law graphs, the family `P'_α`). Here `n = |V|`. -/
structure IsProperPowerLaw [Fintype V] (α : ℝ) (G : SimpleGraph V) : Prop where
  /-- `⌊Cn⌋ - i₁ - 1 ≤ |V₁|` -/
  one_lower : (⌊C α * Fintype.card V⌋₊ : ℤ) - i₁ α (Fintype.card V) - 1 ≤ numDeg G 1
  /-- `|V₁| ≤ ⌈Cn⌉` -/
  one_upper : numDeg G 1 ≤ ⌈C α * Fintype.card V⌉₊
  /-- `⌊C n / 2^α⌋ ≤ |V₂|` -/
  two_lower : ⌊C α * Fintype.card V / (2 : ℝ) ^ α⌋₊ ≤ numDeg G 2
  /-- `|V₂| ≤ ⌈C n / 2^α⌉ + 1` -/
  two_upper : numDeg G 2 ≤ ⌈C α * Fintype.card V / (2 : ℝ) ^ α⌉₊ + 1
  /-- `|V_i| ∈ {⌊C n / i^α⌋, ⌈C n / i^α⌉}` for `3 ≤ i ≤ n` -/
  mid : ∀ i : ℕ, 3 ≤ i → i ≤ Fintype.card V →
    numDeg G i = ⌊C α * Fintype.card V / (i : ℝ) ^ α⌋₊ ∨
      numDeg G i = ⌈C α * Fintype.card V / (i : ℝ) ^ α⌉₊
  /-- `|V_i| ≥ |V_{i+1}|` for `2 ≤ i ≤ n - 1` -/
  anti : ∀ i : ℕ, 2 ≤ i → i ≤ Fintype.card V - 1 → numDeg G (i + 1) ≤ numDeg G i

end Podc.PowerLawLabeling
