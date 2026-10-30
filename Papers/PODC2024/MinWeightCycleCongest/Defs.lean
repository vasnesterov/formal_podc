import Cslib.Computability.Distributed.Congest.Randomized
import Mathlib.Combinatorics.SimpleGraph.Diam
import Mathlib.Basic.ENNReal.Operations
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.IntervalCases
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Minimum weight cycle in the CONGEST model: problem definitions

Manoharan, Ramachandran. *Computing Minimum Weight Cycle in the CONGEST Model.* PODC 2024.

* `WDigraph V W`: a weighted directed graph on the node set `V` with arc weights in `{0, …, W}`;
  `WGraph V W`: a weighted undirected graph.
* `WDigraph.Cycle`, `WGraph.Cycle`: simple cycles, given as a periodic sequence of `len` distinct
  vertices (`len ≥ 2` for directed cycles, `len ≥ 3` for undirected ones), consecutive vertices
  joined by an arc/edge. `mwc` is the minimum weight of a simple cycle, `∞` if there is none
  (Definition 1.1).
* `net`: the communication network, the underlying undirected unweighted graph (§1.1: links are
  bidirectional and unweighted). `view v`: the local input of node `v` — the weights of its incident
  arcs (both directions) / edges.
* `ApproxOutput α opt o`: the output convention. Every node outputs `none` or an estimate; at least
  one node outputs an estimate, and every estimate `e` satisfies `opt ≤ e ≤ α · opt`. This is
  weaker than the paper's algorithms' convention (all nodes output) and is exactly the convention
  of the lower bounds ("apply even when only one node is required to know the weight").
-/

namespace Podc.MinWeightCycleCongest

open scoped ENNReal

open Finset

variable {V : Type*} {W : ℕ}

/-! ### Directed graphs -/

/-- A weighted directed graph with arc weights in `{0, …, W}`: `D.wt u v = some c` iff there is an
arc `u → v`, of weight `c`. -/
structure WDigraph (V : Type*) (W : ℕ) where
  /-- Arc weights (`none` = no arc). -/
  wt : V → V → Option (Fin (W + 1))

namespace WDigraph

variable (D : WDigraph V W)

/-- Weight of the arc `u → v` as a natural number (`0` if there is no arc). -/
def w (u v : V) : ℕ := ((D.wt u v).map Fin.val).getD 0

/-- Every arc has weight `1` (an unweighted digraph). -/
def Unweighted : Prop := ∀ u v c, D.wt u v = some c → c.val = 1

/-- A simple directed cycle of length `len ≥ 2`: a `len`-periodic sequence of vertices, pairwise
distinct within a period, with an arc from each vertex to the next. -/
structure Cycle where
  /-- Number of vertices (= number of arcs). -/
  len : ℕ
  two_le_len : 2 ≤ len
  /-- The vertices, `vtx i` for `i : ℕ`, read modulo `len`. -/
  vtx : ℕ → V
  periodic : ∀ i, vtx (i + len) = vtx i
  inj : ∀ i < len, ∀ j < len, vtx i = vtx j → i = j
  arc : ∀ i, (D.wt (vtx i) (vtx (i + 1))).isSome

/-- Weight of a cycle: the sum of its arc weights. -/
def Cycle.weight {D : WDigraph V W} (c : D.Cycle) : ℕ :=
  ∑ i ∈ range c.len, D.w (c.vtx i) (c.vtx (i + 1))

/-- **Minimum weight cycle** (Definition 1.1): the minimum weight of a simple directed cycle,
`∞` if the digraph is acyclic. -/
noncomputable def mwc : ℝ≥0∞ := ⨅ c : D.Cycle, (c.weight : ℝ≥0∞)

/-- The communication network: the underlying undirected graph. -/
def net : SimpleGraph V := SimpleGraph.fromRel fun u v => (D.wt u v).isSome

instance [DecidableEq V] : DecidableRel D.net.Adj := fun u v =>
  decidable_of_iff (u ≠ v ∧ ((D.wt u v).isSome ∨ (D.wt v u).isSome)) (by simp [net])

/-- Local input of node `v`: for every node `u`, the weights of the arcs `v → u` and `u → v`. -/
def view (v : V) : V → Option (Fin (W + 1)) × Option (Fin (W + 1)) :=
  fun u => (D.wt v u, D.wt u v)

end WDigraph

/-! ### Undirected graphs -/

/-- A weighted undirected graph with edge weights in `{0, …, W}`. -/
structure WGraph (V : Type*) (W : ℕ) where
  /-- Edge weights (`none` = no edge). -/
  wt : V → V → Option (Fin (W + 1))
  symm : ∀ u v, wt u v = wt v u
  loopless : ∀ v, wt v v = none

namespace WGraph

variable (G : WGraph V W)

/-- Weight of the edge `uv` as a natural number (`0` if there is no edge). -/
def w (u v : V) : ℕ := ((G.wt u v).map Fin.val).getD 0

/-- A simple cycle of length `len ≥ 3`: a `len`-periodic sequence of vertices, pairwise distinct
within a period, consecutive vertices adjacent. -/
structure Cycle where
  /-- Number of vertices (= number of edges). -/
  len : ℕ
  three_le_len : 3 ≤ len
  /-- The vertices, `vtx i` for `i : ℕ`, read modulo `len`. -/
  vtx : ℕ → V
  periodic : ∀ i, vtx (i + len) = vtx i
  inj : ∀ i < len, ∀ j < len, vtx i = vtx j → i = j
  adj : ∀ i, (G.wt (vtx i) (vtx (i + 1))).isSome

/-- Weight of a cycle: the sum of its edge weights. -/
def Cycle.weight {G : WGraph V W} (c : G.Cycle) : ℕ :=
  ∑ i ∈ range c.len, G.w (c.vtx i) (c.vtx (i + 1))

/-- **Minimum weight cycle** (Definition 1.1): the minimum weight of a simple cycle, `∞` if the
graph is a forest. -/
noncomputable def mwc : ℝ≥0∞ := ⨅ c : G.Cycle, (c.weight : ℝ≥0∞)

/-- The communication network: the underlying unweighted graph. -/
def net : SimpleGraph V := SimpleGraph.fromRel fun u v => (G.wt u v).isSome

instance [DecidableEq V] : DecidableRel G.net.Adj := fun u v =>
  decidable_of_iff (u ≠ v ∧ ((G.wt u v).isSome ∨ (G.wt v u).isSome)) (by simp [net])

/-- Local input of node `v`: the weights of its incident edges. -/
def view (v : V) : V → Option (Fin (W + 1)) := G.wt v

end WGraph

/-! ### Output convention and approximation -/

/-- The output convention of the lower bounds: some node outputs an estimate, and every estimate
is an `α`-approximation of `opt` (`opt ≤ e ≤ α · opt`). Nodes may output `none`. -/
def ApproxOutput (α opt : ℝ≥0∞) (o : V → Option ℝ≥0∞) : Prop :=
  (∃ v, (o v).isSome) ∧ ∀ v e, o v = some e → opt ≤ e ∧ e ≤ α * opt

open Cslib.Congest

/-- The outputs of a CONGEST algorithm `A` with output map `est` after `T` rounds on network `G`
with node inputs `inp`. (The Boolean `out` field of `A` is not used.) -/
def outputs {I σ : Type*} {B : ℕ} (A : Algorithm V I σ B) (est : V → σ → Option ℝ≥0∞)
    (G : SimpleGraph V) [DecidableRel G.Adj] (inp : V → I) (T : ℕ) : V → Option ℝ≥0∞ :=
  fun v => est v (A.run G inp T v)

/-! ### Periodic sequences -/

section Periodic

/-- The sum of a `L`-periodic sequence over any window of length `L` is the same. -/
lemma sum_shift {M : Type*} [AddCancelCommMonoid M] (g : ℕ → M) {L : ℕ}
    (hg : ∀ i, g (i + L) = g i) (s : ℕ) :
    ∑ i ∈ range L, g (s + i) = ∑ i ∈ range L, g i := by
  induction s with
  | zero => simp
  | succ s ih =>
    rw [← ih]
    have h1 := Finset.sum_range_succ' (fun i => g (s + i)) L
    have h2 := Finset.sum_range_succ (fun i => g (s + i)) L
    rw [h1] at h2
    have h3 : g (s + L) = g (s + 0) := by rw [hg, add_zero]
    rw [h3] at h2
    have : ∑ i ∈ range L, g (s + (i + 1)) = ∑ i ∈ range L, g (s + i) := add_right_cancel h2
    rw [← this]
    exact Finset.sum_congr rfl fun i _ => by rw [Nat.add_right_comm, Nat.add_assoc]

variable {vtx : ℕ → V} {L : ℕ}

lemma periodic_mul (hper : ∀ i, vtx (i + L) = vtx i) (a q : ℕ) : vtx (a + L * q) = vtx a := by
  induction q with
  | zero => simp
  | succ q ih => rw [Nat.mul_succ, ← Nat.add_assoc, hper, ih]

lemma periodic_mod (hper : ∀ i, vtx (i + L) = vtx i) (i : ℕ) : vtx i = vtx (i % L) := by
  conv_lhs => rw [← Nat.mod_add_div i L]
  exact periodic_mul hper _ _

lemma mod_eq_of_eq (hper : ∀ i, vtx (i + L) = vtx i)
    (hinj : ∀ i < L, ∀ j < L, vtx i = vtx j → i = j) (hL : 0 < L) {i j : ℕ}
    (h : vtx i = vtx j) : i % L = j % L := by
  rw [periodic_mod hper i, periodic_mod hper j] at h
  exact hinj _ (Nat.mod_lt _ hL) _ (Nat.mod_lt _ hL) h

/-- In a sequence of period `L ≥ 3` that is injective on a period, `vtx i ≠ vtx (i + 2)`. -/
lemma ne_add_two (hper : ∀ i, vtx (i + L) = vtx i)
    (hinj : ∀ i < L, ∀ j < L, vtx i = vtx j → i = j) (hL : 3 ≤ L) (i : ℕ) :
    vtx (i + 2) ≠ vtx i := by
  intro h
  have h1 := Nat.sub_mod_eq_zero_of_mod_eq (mod_eq_of_eq hper hinj (by omega) h)
  rw [Nat.add_sub_cancel_left, Nat.mod_eq_of_lt (by omega)] at h1
  omega

/-- The `4`-periodic sequence `a, b, c, d, a, b, …`. -/
def cyc4 (a b c d : V) (n : ℕ) : V :=
  match n % 4 with
  | 0 => a
  | 1 => b
  | 2 => c
  | _ => d

lemma cyc4_periodic (a b c d : V) (n : ℕ) : cyc4 a b c d (n + 4) = cyc4 a b c d n := by
  simp [cyc4]

/-- Properties of `cyc4` are checked on the residues `0, 1, 2, 3`. -/
lemma cyc4_cases {a b c d : V} (P : V → V → Prop) (h0 : P a b) (h1 : P b c) (h2 : P c d)
    (h3 : P d a) (n : ℕ) : P (cyc4 a b c d n) (cyc4 a b c d (n + 1)) := by
  have h : n % 4 < 4 := Nat.mod_lt _ (by norm_num)
  have e : (n + 1) % 4 = (n % 4 + 1) % 4 := by omega
  unfold cyc4
  rw [e]
  generalize n % 4 = m at h ⊢
  interval_cases m <;> assumption

lemma cyc4_inj {a b c d : V} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c)
    (hbd : b ≠ d) (hcd : c ≠ d) : ∀ i < 4, ∀ j < 4, cyc4 a b c d i = cyc4 a b c d j → i = j := by
  intro i hi j hj h
  interval_cases i <;> interval_cases j <;> simp_all [cyc4, eq_comm]

lemma sum_range_four_cyc4 {a b c d : V} (f : V → V → ℕ) :
    ∑ i ∈ range 4, f (cyc4 a b c d i) (cyc4 a b c d (i + 1)) = f a b + f b c + f c d + f d a := by
  simp [Finset.sum_range_succ, cyc4]

end Periodic

end Podc.MinWeightCycleCongest
