import Mathlib

/-!
# Sinkless orientations: basic definitions

Basic notions for *Brief Announcement: Sinkless Orientation Made Trivial* (A. Nolin, PODC 2026):

* `Orientation G`: an orientation of the edges of a simple graph `G`.
* `Orientation.IsSink`, `Orientation.IsDeltaSink`, `Orientation.NoDeltaSink`: sinks, `δ`-sinks
  (sinks of degree `≥ δ`), orientations without `δ`-sinks.
* `Orientation.IsSinkSparse`: `k`-sinksparse orientations (distinct sinks at distance `> k`).
* `cball G v k`: the inclusive distance-`k` neighbourhood of `v`; `ContainsCycle G S`: some cycle of
  `G` has all its vertices in `S`.
* Locality (the LOCAL model): `GAgree G G' u R` (`G` and `G'` cannot be distinguished by `R` rounds
  of communication at `u`), `IsLocal A R` (an orientation algorithm whose output at every node
  depends only on what the node sees in `R` rounds), `IsLocalRel` (the same, for algorithms that
  also get an orientation as local input), and the composition lemma `IsLocal.comp`.

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

/-- The inclusive distance-`k` neighbourhood of `v`: all nodes at distance at most `k` from `v`. -/
def cball (G : SimpleGraph V) (v : V) (k : ℕ) : Set V := {u | G.edist v u ≤ k}

@[simp] lemma mem_cball {G : SimpleGraph V} {v u : V} {k : ℕ} :
    u ∈ cball G v k ↔ G.edist v u ≤ k := Iff.rfl

/-- `S` contains a cycle of `G`: there is a cycle of `G` all of whose vertices lie in `S`. -/
def ContainsCycle (G : SimpleGraph V) (S : Set V) : Prop :=
  ∃ (x : V) (c : G.Walk x x), c.IsCycle ∧ ∀ y ∈ c.support, y ∈ S

/-! ### Orientations -/

/-- An orientation of the edges of `G`: `o.out u v` means that the edge `uv` is oriented from `u`
to `v` (it is an *outgoing* edge of `u`). Every edge gets exactly one direction. -/
structure Orientation (G : SimpleGraph V) where
  /-- `out u v`: the edge `uv` is oriented from `u` to `v`. -/
  out : V → V → Prop
  adj_of_out : ∀ ⦃u v⦄, out u v → G.Adj u v
  out_or_out : ∀ ⦃u v⦄, G.Adj u v → out u v ∨ out v u
  not_out_of_out : ∀ ⦃u v⦄, out u v → ¬ out v u

namespace Orientation

variable {G : SimpleGraph V} (o : Orientation G)

/-- `v` is a sink: it has no outgoing edge. -/
def IsSink (v : V) : Prop := ∀ u, ¬ o.out v u

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

end Orientation

/-! ### Distances -/

-- CSLib candidate (this section and the next): general `edist` helpers and locality-by-agreement.

section Dist

variable {G : SimpleGraph V} {u x y : V}

lemma edist_le_add_one_of_adj (h : G.Adj x y) : G.edist u y ≤ G.edist u x + 1 :=
  G.edist_triangle.trans (by rw [edist_eq_one_iff_adj.2 h])

/-- The penultimate node of a shortest walk. -/
lemma exists_adj_of_edist_eq_succ {n : ℕ} (h : G.edist u x = (n + 1 : ℕ)) :
    ∃ y, G.edist u y = n ∧ G.Adj y x := by
  obtain ⟨p, hp⟩ := exists_walk_of_edist_eq_coe h
  cases hq : p.reverse with
  | nil => have := congrArg Walk.length hq; rw [Walk.length_reverse, hp] at this; simp at this
  | cons hxy q =>
    rename_i y
    have hlen : q.length = n := by
      have := congrArg Walk.length hq; simp at this; omega
    refine ⟨y, le_antisymm ?_ ?_, hxy.symm⟩
    · rw [SimpleGraph.edist_comm]; exact (edist_le q).trans (by rw [hlen])
    · have h1 := edist_le_add_one_of_adj (u := u) hxy.symm
      rw [h] at h1
      have : ((n : ℕ∞) + 1) ≤ G.edist u y + 1 := by simpa using h1
      exact (ENat.add_le_add_iff_right ENat.one_ne_top).1 this

lemma edist_lt_top_of_le {n : ℕ} (h : G.edist u x ≤ n) : G.edist u x ≠ ⊤ :=
  ne_top_of_le_ne_top (ENat.natCast_ne_top n) h

lemma edist_eq_coe_dist_of_le {n : ℕ} (h : G.edist u x ≤ n) : G.edist u x = G.dist u x :=
  (Reachable.coe_dist_eq_edist (reachable_of_edist_ne_top (edist_lt_top_of_le h))).symm

lemma dist_le_of_edist_le {n : ℕ} (h : G.edist u x ≤ n) : G.dist u x ≤ n := by
  have := edist_eq_coe_dist_of_le h
  rw [this] at h; exact_mod_cast h

end Dist

/-! ### Locality -/

section Locality

variable {G G' : SimpleGraph V} {u x : V} {R : ℕ}

/-- `G` and `G'` agree on everything a node `u` can learn in `R` rounds of the LOCAL model: the
edges incident to nodes at distance `< R` from `u`. (Node names, i.e. identifiers, are the same in
both graphs since they share the vertex type.) -/
def GAgree (G G' : SimpleGraph V) (u : V) (R : ℕ) : Prop :=
  ∀ ⦃x⦄, G.edist u x < R → ∀ y, (G.Adj x y ↔ G'.Adj x y)

lemma GAgree.edist_le_of_eq (hA : GAgree G G' u R) :
    ∀ (m : ℕ) {x}, G.edist u x = m → m ≤ R → G'.edist u x ≤ m := by
  intro m
  induction m with
  | zero => intro x hx _; simp at hx; subst hx; simp
  | succ m ih =>
    intro x hx hm
    obtain ⟨y, hy, hyx⟩ := exists_adj_of_edist_eq_succ hx
    have h1 := ih hy (by omega)
    have hyR : G.edist u y < R := by rw [hy]; exact_mod_cast (by omega : m < R)
    have h2 : G'.Adj y x := (hA hyR x).1 hyx
    calc G'.edist u x ≤ G'.edist u y + 1 := edist_le_add_one_of_adj h2
      _ ≤ m + 1 := by gcongr
      _ = ((m + 1 : ℕ) : ℕ∞) := by push_cast; rfl

lemma GAgree.symm (hA : GAgree G G' u R) : GAgree G' G u R := by
  -- first: `G'.edist u x = m ≤ R` implies `G.edist u x ≤ m`
  have key : ∀ (m : ℕ) {x}, G'.edist u x = m → m ≤ R → G.edist u x ≤ m := by
    intro m
    induction m with
    | zero => intro x hx _; simp at hx; subst hx; simp
    | succ m ih =>
      intro x hx hm
      obtain ⟨y, hy, hyx⟩ := exists_adj_of_edist_eq_succ hx
      have h1 := ih hy (by omega)
      have hyR : G.edist u y < R := lt_of_le_of_lt h1 (by exact_mod_cast (by omega : m < R))
      have h2 : G.Adj y x := (hA hyR x).2 hyx
      calc G.edist u x ≤ G.edist u y + 1 := edist_le_add_one_of_adj h2
        _ ≤ m + 1 := by gcongr
        _ = ((m + 1 : ℕ) : ℕ∞) := by push_cast; rfl
  intro x hx y
  have hne : G'.edist u x ≠ ⊤ := ne_top_of_lt hx
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.1 hne
  have hmR : m < R := by rw [← hm] at hx; exact_mod_cast hx
  have := key m hm.symm hmR.le
  exact (hA (lt_of_le_of_lt this (by exact_mod_cast hmR)) y).symm

lemma GAgree.edist_le_iff (hA : GAgree G G' u R) {m : ℕ} (hm : m ≤ R) :
    G'.edist u x ≤ m ↔ G.edist u x ≤ m := by
  have aux : ∀ {G G' : SimpleGraph V}, GAgree G G' u R → G.edist u x ≤ m → G'.edist u x ≤ m := by
    intro G G' hA h
    obtain ⟨j, hj⟩ := ENat.ne_top_iff_exists.1 (edist_lt_top_of_le h)
    rw [← hj] at h
    have hjm : j ≤ m := by exact_mod_cast h
    exact (hA.edist_le_of_eq j hj.symm (hjm.trans hm)).trans (by exact_mod_cast hjm)
  exact ⟨aux hA.symm, aux hA⟩

lemma GAgree.edist_eq (hA : GAgree G G' u R) (hx : G.edist u x ≤ R) :
    G'.edist u x = G.edist u x := by
  obtain ⟨j, hj⟩ := ENat.ne_top_iff_exists.1 (edist_lt_top_of_le hx)
  have hjR : j ≤ R := by rw [← hj] at hx; exact_mod_cast hx
  apply le_antisymm
  · rw [← hj]; exact (hA.edist_le_iff hjR).2 hj.symm.le
  · have h' : G'.edist u x ≤ j := (hA.edist_le_iff hjR).2 hj.symm.le
    obtain ⟨i, hi⟩ := ENat.ne_top_iff_exists.1 (edist_lt_top_of_le h')
    have hij : i ≤ j := by rw [← hi] at h'; exact_mod_cast h'
    have := (hA.edist_le_iff (m := i) (hij.trans hjR)).1 hi.symm.le
    rw [← hi]; exact this

lemma GAgree.edist_lt_iff (hA : GAgree G G' u R) {m : ℕ} (hm : m ≤ R) :
    G'.edist u x < m ↔ G.edist u x < m := by
  cases m with
  | zero => simp
  | succ m =>
    have h1 : ∀ {e : ℕ∞}, e < ((m + 1 : ℕ) : ℕ∞) ↔ e ≤ m := by
      intro e; rw [Nat.cast_add, Nat.cast_one]; exact ENat.lt_add_one_iff (ENat.natCast_ne_top m)
    rw [h1, h1]; exact hA.edist_le_iff (by omega)

lemma GAgree.mono (hA : GAgree G G' u R) {a ρ : ℕ} (hx : G.edist u x ≤ a) (h : a + ρ ≤ R) :
    GAgree G G' x ρ := by
  intro y hy z
  apply hA
  calc G.edist u y ≤ G.edist u x + G.edist x y := G.edist_triangle
    _ < a + ρ := by
      obtain ⟨j, hj⟩ := ENat.ne_top_iff_exists.1 (edist_lt_top_of_le hx)
      rw [← hj] at hx ⊢
      have hy' : G.edist x y ≠ ⊤ := ne_top_of_lt hy
      obtain ⟨i, hi⟩ := ENat.ne_top_iff_exists.1 hy'
      rw [← hi] at hy ⊢
      have : j ≤ a := by exact_mod_cast hx
      have : i < ρ := by exact_mod_cast hy
      exact_mod_cast (by omega : j + i < a + ρ)
    _ ≤ R := by exact_mod_cast h

lemma GAgree.mono_radius (hA : GAgree G G' u R) {ρ : ℕ} (h : ρ ≤ R) : GAgree G G' u ρ :=
  hA.mono (a := 0) (by simp) (by omega)

lemma GAgree.adj_iff (hA : GAgree G G' u R) (hR : 0 < R) (y : V) : G.Adj u y ↔ G'.Adj u y :=
  hA (by simp; exact_mod_cast hR) y

lemma GAgree.neighborSet_eq (hA : GAgree G G' u R) (hR : 0 < R) :
    G.neighborSet u = G'.neighborSet u := by
  ext y; exact hA.adj_iff hR y

lemma GAgree.deg_eq (hA : GAgree G G' u R) (hR : 0 < R) : deg G u = deg G' u := by
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
