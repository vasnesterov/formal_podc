import Mathlib
import Cslib.Computability.Distributed.Local.Locality

/-!
# The deterministic LOCAL model without knowledge of `n`, and `k`-hierarchical 2½-colouring

Definitions for Section 3 of *The Distributed Complexity Landscape on Trees Depends on the
Knowledge About the Network Size* (Balliu, Brandt, Kuhn, Olivetti, Picavet, Schmid; PODC 2026).

* `Inst`: a network = a finite tree whose nodes are natural numbers. The node names are the unique
  identifiers, which are arbitrary natural numbers (no bound on the ID space). Nothing else (in
  particular not `n`) is given to the nodes.
* `Inst.MaxDegLE Δ`: maximum degree at most `Δ`.
* `Alg β`: a deterministic LOCAL algorithm with per-node termination, given extensionally: the round
  `time I v` in which node `v` stops and its output `out I v`. Locality (`Alg.IsLocal`): whether `v`
  has stopped by round `t`, and its output if it has, depend only on what `v` can know after `t`
  rounds. We are generous: `v` may know all edges incident to nodes at distance `≤ t`
  (`GAgree I.G J.G v (t+1)`), one hop more than in the standard LOCAL model, which only makes the
  lower bound stronger.
* `levelSet`, `InLevel`: the levels `L₁, …, L_k` of the `k`-hierarchical 2½-colouring problem
  (`L₁` = nodes of degree `≤ 2`, `L_i` = nodes of degree `≤ 2` after removing `L₁ ∪ … ∪ L_{i-1}`).
* `IsHierColoring k I o`: `o` is a valid output of `k`-hierarchical 2½-colouring on `I`
  (Section 2.3 of the paper, constraints 1–4).
-/

namespace Podc.TreesNetworkSizeKnowledge

open SimpleGraph

/-- A network: a finite tree whose nodes are natural numbers (their unique identifiers). -/
structure Inst where
  /-- The set of nodes (= their identifiers). -/
  V : Finset ℕ
  /-- The communication graph (edges only between nodes of `V`). -/
  G : SimpleGraph ℕ
  adj_mem : ∀ ⦃a b⦄, G.Adj a b → a ∈ V
  isTree : (G.induce (V : Set ℕ)).IsTree

/-- Maximum degree at most `Δ`. -/
def Inst.MaxDegLE (I : Inst) (Δ : ℕ) : Prop := ∀ v, (I.G.neighborSet v).ncard ≤ Δ

/-- A deterministic LOCAL algorithm with per-node termination, given extensionally. -/
structure Alg (β : Type*) where
  /-- The round in which node `v` terminates on instance `I`. -/
  time : Inst → ℕ → ℕ
  /-- The output of node `v` on instance `I`. -/
  out : Inst → ℕ → β

/-- Locality of an algorithm: whether `v` stopped by round `t`, and then its output, depend only on
the radius-`t` view of `v` (edges incident to nodes at distance `≤ t`; IDs are the node names).
In particular no node knows `n = |V|`. -/
def Alg.IsLocal {β : Type*} (A : Alg β) : Prop :=
  ∀ (I J : Inst) (v t : ℕ), v ∈ I.V → v ∈ J.V → Cslib.Local.GAgree I.G J.G v (t + 1) →
    (A.time I v ≤ t ↔ A.time J v ≤ t) ∧ (A.time I v ≤ t → A.out I v = A.out J v)

/-- Output labels of 2½-colouring: Black, White, Exempt, Decline. -/
inductive Label
  | B | W | E | D
  deriving DecidableEq

/-- `levelSet G V i` = `V⁽ⁱ⁺¹⁾`, the nodes that are not in levels `1, …, i`:
`V⁽¹⁾ = V`, and `V⁽ⁱ⁺¹⁾` = nodes of `V⁽ⁱ⁾` with more than 2 neighbours in `V⁽ⁱ⁾`. -/
def levelSet (G : SimpleGraph ℕ) (V : Set ℕ) : ℕ → Set ℕ
  | 0 => V
  | i + 1 => {v | v ∈ levelSet G V i ∧ 2 < (G.neighborSet v ∩ levelSet G V i).ncard}

/-- `v` is in level `L_i` (`i ≥ 1`). -/
def InLevel (G : SimpleGraph ℕ) (V : Set ℕ) (i v : ℕ) : Prop :=
  1 ≤ i ∧ v ∈ levelSet G V (i - 1) ∧ v ∉ levelSet G V i

/-- `k`-hierarchical 2½-colouring (Section 2.3): constraints 1–4. -/
structure IsHierColoring (k : ℕ) (I : Inst) (o : ℕ → Label) : Prop where
  /-- 1. Nodes in the remainder `V⁽ᵏ⁺¹⁾` output `D`. -/
  remainder : ∀ v ∈ levelSet I.G I.V k, o v = .D
  /-- 2a. No node of level `k` outputs `D`. -/
  top_ne_D : ∀ v, InLevel I.G I.V k v → o v ≠ .D
  /-- 2b. No node of level `1` outputs `E`. -/
  bot_ne_E : ∀ v, InLevel I.G I.V 1 v → o v ≠ .E
  /-- 3. A node outputting `W` (resp. `B`) has no neighbour of the same level outputting `W`
  (resp. `B`) or `D`. -/
  color : ∀ i ≤ k, ∀ v u, InLevel I.G I.V i v → InLevel I.G I.V i u → I.G.Adj v u →
    (o v = .W ∨ o v = .B) → o u ≠ o v ∧ o u ≠ .D
  /-- 4. A node may output `E` only if it has a neighbour of a lower level outputting `B`, `W`
  or `E`. -/
  exempt : ∀ i ≤ k, ∀ v, InLevel I.G I.V i v → o v = .E →
    ∃ u j, j < i ∧ InLevel I.G I.V j u ∧ I.G.Adj v u ∧ o u ≠ .D

end Podc.TreesNetworkSizeKnowledge
