import Mathlib
import Podc.Graph.Orientation
import Podc.Local.Locality

/-!
# Sinkless orientations: basic definitions

Basic notions for *Brief Announcement: Sinkless Orientation Made Trivial* (A. Nolin, PODC 2026):

* `Orientation G` (`SimpleGraph.Orientation`, shared in `Podc/Graph/Orientation.lean`): an
  orientation of the edges of a simple graph `G`; sinks `Orientation.IsSink`.
* `Orientation.IsDeltaSink`, `Orientation.NoDeltaSink`: `δ`-sinks (sinks of degree `≥ δ`),
  orientations without `δ`-sinks.
* `Orientation.IsSinkSparse`: `k`-sinksparse orientations (distinct sinks at distance `> k`).
* `cball G v k`: the inclusive distance-`k` neighbourhood of `v` (`SimpleGraph.closedBall`,
  `Podc/Graph/Ball.lean`); `ContainsCycle G S`: some cycle of `G` has all its vertices in `S`.
* Locality (the LOCAL model): `GAgree G G' u R` (`G` and `G'` cannot be distinguished by `R` rounds
  of communication at `u`; shared in `Podc/Local/Locality.lean`), `IsLocal A R` (an orientation
  algorithm whose output at every node depends only on what the node sees in `R` rounds;
  `isLocal_iff` relates it to the shared `Cslib.Local.IsLocal`), `IsLocalRel` (the same, for
  algorithms that also get an orientation as local input), and the composition lemma
  `IsLocal.comp`.

The degree is the instance-free `deg G v = (G.neighborSet v).ncard` (`deg_eq_degree`), so that
graphs `G`, `G'` on the same vertex type can be compared without decidability instances.
-/

namespace SinklessOrientation

open SimpleGraph

variable {V : Type*}

/-! ### Degrees, balls, cycles -/

/-- The degree of `v` in `G` (instance-free version of `SimpleGraph.degree`). -/
noncomputable def deg (G : SimpleGraph V) (v : V) : ℕ := (G.neighborSet v).ncard

lemma deg_eq_degree (G : SimpleGraph V) (v : V) [Fintype (G.neighborSet v)] :
    deg G v = G.degree v := by
  rw [deg, Set.ncard_eq_toFinset_card', ← card_neighborSet_eq_degree, Set.toFinset_card]

/-- The inclusive distance-`k` neighbourhood of `v`: all nodes at distance at most `k` from `v`
(the closed ball of radius `k : ℕ`). -/
abbrev cball (G : SimpleGraph V) (v : V) (k : ℕ) : Set V := G.closedBall v k

@[simp] lemma mem_cball {G : SimpleGraph V} {v u : V} {k : ℕ} :
    u ∈ cball G v k ↔ G.edist v u ≤ k := mem_closedBall'

/-- `S` contains a cycle of `G`: there is a cycle of `G` all of whose vertices lie in `S`. -/
def ContainsCycle (G : SimpleGraph V) (S : Set V) : Prop :=
  ∃ (x : V) (c : G.Walk x x), c.IsCycle ∧ ∀ y ∈ c.support, y ∈ S

end SinklessOrientation

/-! ### `δ`-sinks and sinksparse orientations

Orientations themselves (`SimpleGraph.Orientation`, sinks `Orientation.IsSink`) are the shared
notions of `Podc/Graph/Orientation.lean`; the predicates below are specific to the paper. -/

namespace SimpleGraph.Orientation

open SinklessOrientation

variable {V : Type*} {G : SimpleGraph V} (o : Orientation G)

/-- `v` is a `δ`-sink: a sink of degree at least `δ`. -/
def IsDeltaSink (δ : ℕ) (v : V) : Prop := o.IsSink v ∧ δ ≤ deg G v

/-- The orientation has no `δ`-sink: every node of degree `≥ δ` has an outgoing edge. For `δ = 3`
this is the *sinkless orientation* problem. -/
def NoDeltaSink (δ : ℕ) : Prop := ∀ v, ¬ o.IsDeltaSink δ v

/-- A `k`-sinksparse orientation: any two distinct sinks are at distance more than `k` (the
paper: "sinks are separated by a distance of at least `k`"; its proof gives `> k`, which we use). -/
def IsSinkSparse (k : ℕ) : Prop :=
  ∀ ⦃u v⦄, o.IsSink u → o.IsSink v → u ≠ v → (k : ℕ∞) < G.edist u v

lemma noDeltaSink_iff (δ : ℕ) : o.NoDeltaSink δ ↔ ∀ v, δ ≤ deg G v → ∃ u, o.out v u := by
  simp only [NoDeltaSink, IsDeltaSink, IsSink]
  constructor
  · intro h v hv; by_contra hc; push Not at hc; exact h v ⟨hc, hv⟩
  · rintro h v ⟨hs, hv⟩; obtain ⟨u, hu⟩ := h v hv; exact hs u hu

/-- Without a degree threshold, "no `0`-sink" is plain sinklessness. -/
lemma noDeltaSink_zero_iff : o.NoDeltaSink 0 ↔ o.IsSinkless := by
  simp [NoDeltaSink, IsDeltaSink, IsSinkless]

end SimpleGraph.Orientation

namespace SinklessOrientation

open SimpleGraph
open Cslib.Local (GAgree)

variable {V : Type*}

/-! ### Locality of orientation algorithms

Agreement of views (`GAgree`) is the shared notion of `Podc/Local/Locality.lean`. -/

section Locality

variable {G G' : SimpleGraph V} {u x : V} {R : ℕ}

lemma deg_eq_of_gAgree (hA : GAgree G G' u R) (hR : 0 < R) : deg G u = deg G' u := by
  rw [deg, deg, hA.neighborSet_eq hR]

/-- Two orientations (of `G` and `G'`) agree on all edges incident to nodes at distance `< R` from
`u`. -/
def OAgree (o : Orientation G) (o' : Orientation G') (u : V) (R : ℕ) : Prop :=
  ∀ ⦃x⦄, G.edist u x < R → ∀ y, (o.out x y ↔ o'.out x y)

/-- An *orientation algorithm*: for every graph `G` on the node set `V` (whose elements serve as the
unique identifiers) it produces an orientation of `G`. It is `R`-local if the orientation of every
edge `uv` only depends on what `u` sees within `R` rounds of the LOCAL model, i.e. it can be
computed by a deterministic `R`-round LOCAL algorithm (each node gathers its radius-`R` view and
applies the rule).

Note: since `A` is any function of the whole graph on the node type `V`, the rule may depend on the
global set `V` of identifiers (not only on `n`), which is slightly more than standard LOCAL. This is
harmless for upper bounds (our algorithms are explicit and only use `n` and their local view) and
makes lower bounds (`LowerBound.lean`) stronger. -/
def IsLocal (A : ∀ G : SimpleGraph V, Orientation G) (R : ℕ) : Prop :=
  ∀ (G G' : SimpleGraph V) (u : V), GAgree G G' u R → ∀ v, ((A G).out u v ↔ (A G').out u v)

/-- Locality for algorithms that transform an input orientation (given as local input: every node
knows the directions of its incident edges). -/
def IsLocalRel (B : ∀ G : SimpleGraph V, Orientation G → Orientation G) (R : ℕ) : Prop :=
  ∀ (G G' : SimpleGraph V) (o : Orientation G) (o' : Orientation G') (u : V),
    GAgree G G' u R → OAgree o o' u R → ∀ v, ((B G o).out u v ↔ (B G' o').out u v)

/-- Running an `ρ`-local algorithm and then a `σ`-local transformation is `(σ + ρ)`-local. -/
lemma IsLocal.comp {A : ∀ G : SimpleGraph V, Orientation G}
    {B : ∀ G : SimpleGraph V, Orientation G → Orientation G} {ρ σ : ℕ}
    (hA : IsLocal A ρ) (hB : IsLocalRel B σ) : IsLocal (fun G => B G (A G)) (σ + ρ) := by
  intro G G' u hG v
  refine hB G G' (A G) (A G') u (hG.mono_radius (by omega)) ?_ v
  intro x hx y
  obtain ⟨j, hj⟩ := ENat.ne_top_iff_exists.1 (ne_top_of_lt hx)
  have hjσ : j < σ := by rw [← hj] at hx; exact_mod_cast hx
  exact hA G G' x (hG.mono (a := j) (by rw [← hj]) (by omega)) y

/-- An `R`-local orientation algorithm is one whose out-neighbourhoods `u ↦ {v | out u v}` form an
`R`-local function in the sense of `Cslib.Local.IsLocal` (with no node labels). -/
lemma isLocal_iff {A : ∀ G : SimpleGraph V, Orientation G} :
    IsLocal A R ↔ Cslib.Local.IsLocal (α := Unit) R (fun G _ u => (A G).outSet u) := by
  constructor
  · intro h G _ G' _ u hv; ext v; exact h G G' u hv.1 v
  · intro h G G' u hA v
    exact Set.ext_iff.1 (h G (fun _ => ()) G' (fun _ => ()) u ⟨hA, fun _ _ => rfl⟩) v

end Locality

end SinklessOrientation

namespace SinklessOrientation

open SimpleGraph

variable {V : Type*}

/-- Some node `x` of the ball `cball G s r` has two distinct neighbours `y ≠ y'` that are not
farther from `s` than `x` itself. Equivalently (`Lemma22.lean`), the BFS tree of depth `r` rooted at
`s` misses some edge between nodes of the ball, i.e. the ball contains a cycle. -/
def HasBackEdges (G : SimpleGraph V) (s : V) (r : ℕ) : Prop :=
  ∃ x y y', G.edist s x ≤ r ∧ G.Adj x y ∧ G.Adj x y' ∧ y ≠ y' ∧
    G.edist s y ≤ G.edist s x ∧ G.edist s y' ≤ G.edist s x

end SinklessOrientation
