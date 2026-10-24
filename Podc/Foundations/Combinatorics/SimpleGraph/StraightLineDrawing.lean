import Mathlib.Analysis.Convex.Segment
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith

-- CSLib candidate: Cslib/Foundations/Combinatorics/SimpleGraph/StraightLineDrawing.lean

/-!
# Straight-line planar drawings and the triangular lattice

Mathlib (checked 2026-10) has no notion of planarity. By Fáry's theorem a finite simple graph is
planar iff it has a *straight-line* planar drawing, so we use the latter as a combinatorial-geometric
certificate of planarity:

* `Cslib.SimpleGraph.IsStraightLineDrawing G pos`: the vertices are placed at distinct points
  `pos v ∈ ℝ²`, every edge `uv` is drawn as the segment `[pos u, pos v]`, no vertex lies on an edge
  that is not incident to it, and two different edges meet at most in a common endpoint.
* `Cslib.SimpleGraph.IsStraightLinePlanar G`: some straight-line drawing exists.

Main results:

* `Cslib.SimpleGraph.IsStraightLineDrawing.comap`: a drawing of `G` induces a drawing of `G.comap f`
  for injective `f` (so subgraphs induced on subsets of the vertex set are planar).
* `Cslib.SimpleGraph.triangularLattice`: the triangular lattice on `ℤ × ℤ` (neighbours of `(x, y)`:
  `(x ± 1, y)`, `(x, y ± 1)`, `(x + 1, y + 1)`, `(x - 1, y - 1)`).
* `Cslib.SimpleGraph.triangularLattice_isStraightLineDrawing`: the identity placement
  `(x, y) ↦ (x, y) ∈ ℝ²` is a straight-line drawing of the triangular lattice; hence every graph
  `triangularLattice.comap f` with `f` injective is straight-line planar.
-/

namespace Cslib.SimpleGraph

open _root_.SimpleGraph

variable {V W : Type*}

/-- `pos` is a straight-line planar drawing of `G`: vertices at distinct points of the plane, edges as
segments, no vertex in the interior of a non-incident edge, and two different edges meet at most in a
common endpoint. -/
structure IsStraightLineDrawing (G : SimpleGraph V) (pos : V → ℝ × ℝ) : Prop where
  injective : Function.Injective pos
  /-- A vertex lies on an edge only if it is one of its endpoints. -/
  vertex_mem_segment : ∀ ⦃u v w⦄, G.Adj u v → pos w ∈ segment ℝ (pos u) (pos v) → w = u ∨ w = v
  /-- Two edges `uv`, `u'v'` meet only in a common endpoint (or they are the same edge). -/
  segment_inter : ∀ ⦃u v u' v'⦄, G.Adj u v → G.Adj u' v' → ∀ z,
    z ∈ segment ℝ (pos u) (pos v) → z ∈ segment ℝ (pos u') (pos v') →
    (s(u, v) = s(u', v')) ∨ ∃ w, (w = u ∨ w = v) ∧ (w = u' ∨ w = v') ∧ z = pos w

/-- `G` has a straight-line planar drawing (for finite graphs: `G` is planar, by Fáry's theorem). -/
def IsStraightLinePlanar (G : SimpleGraph V) : Prop :=
  ∃ pos : V → ℝ × ℝ, IsStraightLineDrawing G pos

/-- A drawing of `G` induces a drawing of `G.comap f` for injective `f`. -/
lemma IsStraightLineDrawing.comap {G : SimpleGraph W} {pos : W → ℝ × ℝ}
    (h : IsStraightLineDrawing G pos) {f : V → W} (hf : Function.Injective f) :
    IsStraightLineDrawing (G.comap f) (pos ∘ f) where
  injective := h.injective.comp hf
  vertex_mem_segment _ _ _ huv hw := (h.vertex_mem_segment huv hw).imp (hf ·) (hf ·)
  segment_inter _ _ _ _ huv huv' z hz hz' := by
    rcases h.segment_inter huv huv' z hz hz' with he | ⟨w, hw, hw', rfl⟩
    · exact .inl (Sym2.map.injective hf (by rwa [Sym2.map_mk, Sym2.map_mk]))
    · rcases hw with rfl | rfl <;> rcases hw' with h' | h' <;>
        first
        | exact .inr ⟨_, .inl rfl, .inl (hf h'), rfl⟩ | exact .inr ⟨_, .inl rfl, .inr (hf h'), rfl⟩
        | exact .inr ⟨_, .inr rfl, .inl (hf h'), rfl⟩ | exact .inr ⟨_, .inr rfl, .inr (hf h'), rfl⟩

lemma IsStraightLinePlanar.comap {G : SimpleGraph W} (h : IsStraightLinePlanar G) {f : V → W}
    (hf : Function.Injective f) : IsStraightLinePlanar (G.comap f) :=
  let ⟨pos, hpos⟩ := h
  ⟨pos ∘ f, hpos.comap hf⟩

/-- Adjacency in the triangular lattice: the difference `q - p` is one of `±(1, 0)`, `±(0, 1)`,
`±(1, 1)`. -/
def TriAdj (p q : ℤ × ℤ) : Prop :=
  (q.1 - p.1 = 1 ∧ q.2 - p.2 = 0) ∨ (q.1 - p.1 = -1 ∧ q.2 - p.2 = 0) ∨
  (q.1 - p.1 = 0 ∧ q.2 - p.2 = 1) ∨ (q.1 - p.1 = 0 ∧ q.2 - p.2 = -1) ∨
  (q.1 - p.1 = 1 ∧ q.2 - p.2 = 1) ∨ (q.1 - p.1 = -1 ∧ q.2 - p.2 = -1)

/-- The triangular lattice on `ℤ × ℤ` (the square grid with one diagonal `(x, y) ~ (x+1, y+1)` per
cell): every vertex has degree `6`. -/
def triangularLattice : SimpleGraph (ℤ × ℤ) where
  Adj := TriAdj
  symm := ⟨fun _ _ h => by unfold TriAdj at *; omega⟩
  loopless := ⟨fun _ h => by unfold TriAdj at *; omega⟩

lemma triangularLattice_adj {p q : ℤ × ℤ} : triangularLattice.Adj p q ↔ TriAdj p q := Iff.rfl

/-- The identity placement of `ℤ × ℤ` in `ℝ²`. -/
def latticePos (p : ℤ × ℤ) : ℝ × ℝ := ((p.1 : ℝ), (p.2 : ℝ))

lemma latticePos_injective : Function.Injective latticePos := fun p q h => by
  simp only [latticePos, Prod.mk.injEq, Int.cast_inj] at h
  exact Prod.ext h.1 h.2

/-- Every lattice edge is `{a, a + d}` for one of the three directions `(1, 0)`, `(0, 1)`, `(1, 1)`. -/
lemma exists_eq_add_dir {u v : ℤ × ℤ} (h : TriAdj u v) : ∃ a d : ℤ × ℤ,
    (d = (1, 0) ∨ d = (0, 1) ∨ d = (1, 1)) ∧ s(u, v) = s(a, a + d) := by
  unfold TriAdj at h
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨u, (1, 0), by simp, Sym2.eq_iff.2 (.inl ⟨rfl, Prod.ext (by simp; omega) (by simp; omega)⟩)⟩
  · exact ⟨v, (1, 0), by simp, Sym2.eq_iff.2 (.inr ⟨Prod.ext (by simp; omega) (by simp; omega), rfl⟩)⟩
  · exact ⟨u, (0, 1), by simp, Sym2.eq_iff.2 (.inl ⟨rfl, Prod.ext (by simp; omega) (by simp; omega)⟩)⟩
  · exact ⟨v, (0, 1), by simp, Sym2.eq_iff.2 (.inr ⟨Prod.ext (by simp; omega) (by simp; omega), rfl⟩)⟩
  · exact ⟨u, (1, 1), by simp, Sym2.eq_iff.2 (.inl ⟨rfl, Prod.ext (by simp; omega) (by simp; omega)⟩)⟩
  · exact ⟨v, (1, 1), by simp, Sym2.eq_iff.2 (.inr ⟨Prod.ext (by simp; omega) (by simp; omega), rfl⟩)⟩

lemma segment_latticePos_eq {u v a b : ℤ × ℤ} (h : s(u, v) = s(a, b)) :
    segment ℝ (latticePos u) (latticePos v) = segment ℝ (latticePos a) (latticePos b) := by
  rcases Sym2.eq_iff.1 h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rfl
  · exact segment_symm ℝ _ _

/-- Parametrization of a lattice segment `[a, a + d]`. -/
lemma exists_of_mem_segment_latticePos {a d : ℤ × ℤ} {z : ℝ × ℝ}
    (h : z ∈ segment ℝ (latticePos a) (latticePos (a + d))) :
    ∃ s : ℝ, 0 ≤ s ∧ s ≤ 1 ∧ z.1 = a.1 + s * d.1 ∧ z.2 = a.2 + s * d.2 := by
  rw [segment_eq_image'] at h
  obtain ⟨s, ⟨h0, h1⟩, rfl⟩ := h
  refine ⟨s, h0, h1, ?_, ?_⟩ <;> simp [latticePos]

/-- A real number in `[0, 1]` that is an integer is `0` or `1`. -/
lemma eq_zero_or_one_of_eq_intCast {s : ℝ} (h0 : 0 ≤ s) (h1 : s ≤ 1) (m : ℤ) (h : s = m) :
    s = 0 ∨ s = 1 := by
  subst h
  have : (0 : ℤ) ≤ m := by exact_mod_cast h0
  have : m ≤ 1 := by exact_mod_cast h1
  rcases (show m = 0 ∨ m = 1 by omega) with rfl | rfl <;> simp

/-- Two reals in `[0, 1]` with integer difference `m`: either `m = 0` or they are `0` and `1`. -/
lemma eq_zero_or_of_sub_eq_intCast {s t : ℝ} (s0 : 0 ≤ s) (s1 : s ≤ 1) (t0 : 0 ≤ t) (t1 : t ≤ 1)
    (m : ℤ) (h : t - s = m) : m = 0 ∨ ((s = 0 ∨ s = 1) ∧ (t = 0 ∨ t = 1)) := by
  have : (-1 : ℤ) ≤ m := by exact_mod_cast (show (-1 : ℝ) ≤ m by linarith)
  have : m ≤ 1 := by exact_mod_cast (show (m : ℝ) ≤ 1 by linarith)
  rcases (show m = -1 ∨ m = 0 ∨ m = 1 by omega) with rfl | rfl | rfl
  · exact .inr ⟨.inr (by push_cast at h; linarith), .inl (by push_cast at h; linarith)⟩
  · exact .inl rfl
  · exact .inr ⟨.inl (by push_cast at h; linarith), .inr (by push_cast at h; linarith)⟩

/-- Closes goals `p = q` (in `ℤ × ℤ`) or `z = latticePos p` from linear real coordinate equations. -/
local macro "latticePos_tac" : tactic => `(tactic|
  (ext <;> try simp only [Prod.fst_add, Prod.snd_add, latticePos]) <;>
    first
    | (apply Int.cast_injective (α := ℝ); push_cast; linarith)
    | (push_cast; linarith))

/-- If a point lies on the lattice segments `[a, a + d]` (at parameter `s`) and `[b, b + e]`
(at parameter `t`) with `s, t ∈ {0, 1}`, it is a common endpoint. -/
lemma exists_common_endpoint {a b d e : ℤ × ℤ} {z : ℝ × ℝ} {s t : ℝ} (hs : s = 0 ∨ s = 1)
    (ht : t = 0 ∨ t = 1) (ha1 : z.1 = a.1 + s * d.1) (ha2 : z.2 = a.2 + s * d.2)
    (hb1 : z.1 = b.1 + t * e.1) (hb2 : z.2 = b.2 + t * e.2) :
    ∃ w, (w = a ∨ w = a + d) ∧ (w = b ∨ w = b + e) ∧ z = latticePos w := by
  rcases hs with rfl | rfl <;> rcases ht with rfl | rfl
  · refine ⟨a, .inl rfl, .inl ?_, ?_⟩ <;> latticePos_tac
  · refine ⟨a, .inl rfl, .inr ?_, ?_⟩ <;> latticePos_tac
  · refine ⟨a + d, .inr rfl, .inl ?_, ?_⟩ <;> latticePos_tac
  · refine ⟨a + d, .inr rfl, .inr ?_, ?_⟩ <;> latticePos_tac

/-- Two lattice edges `[a, a + d]`, `[b, b + e]` meet only in a common endpoint, unless they
coincide. -/
lemma segment_latticePos_inter {a d b e : ℤ × ℤ} (hd : d = (1, 0) ∨ d = (0, 1) ∨ d = (1, 1))
    (he : e = (1, 0) ∨ e = (0, 1) ∨ e = (1, 1)) {z : ℝ × ℝ}
    (hz : z ∈ segment ℝ (latticePos a) (latticePos (a + d)))
    (hz' : z ∈ segment ℝ (latticePos b) (latticePos (b + e))) :
    (a = b ∧ d = e) ∨ ∃ w, (w = a ∨ w = a + d) ∧ (w = b ∨ w = b + e) ∧ z = latticePos w := by
  obtain ⟨s, s0, s1, hs1, hs2⟩ := exists_of_mem_segment_latticePos hz
  obtain ⟨t, t0, t1, ht1, ht2⟩ := exists_of_mem_segment_latticePos hz'
  suffices h : (a = b ∧ d = e) ∨ ((s = 0 ∨ s = 1) ∧ (t = 0 ∨ t = 1)) by
    rcases h with h | ⟨hs, ht⟩
    · exact .inl h
    · exact .inr (exists_common_endpoint hs ht hs1 hs2 ht1 ht2)
  have h01 := eq_zero_or_one_of_eq_intCast s0 s1
  have h01' := eq_zero_or_one_of_eq_intCast t0 t1
  have hdiff := eq_zero_or_of_sub_eq_intCast s0 s1 t0 t1
  rcases hd with rfl | rfl | rfl <;> rcases he with rfl | rfl | rfl <;>
    norm_num at hs1 hs2 ht1 ht2
  · rcases hdiff (a.1 - b.1) (by push_cast; linarith) with hm | h
    · have : (a.1 : ℝ) = b.1 := by exact_mod_cast (show a.1 = b.1 by omega)
      exact .inl ⟨Prod.ext (by omega) (Int.cast_injective (α := ℝ) (by linarith)), rfl⟩
    · exact .inr h
  · exact .inr ⟨h01 (b.1 - a.1) (by push_cast; linarith), h01' (a.2 - b.2) (by push_cast; linarith)⟩
  · exact .inr ⟨h01 (b.1 - a.1 + a.2 - b.2) (by push_cast; linarith),
      h01' (a.2 - b.2) (by push_cast; linarith)⟩
  · exact .inr ⟨h01 (b.2 - a.2) (by push_cast; linarith), h01' (a.1 - b.1) (by push_cast; linarith)⟩
  · rcases hdiff (a.2 - b.2) (by push_cast; linarith) with hm | h
    · have : (a.2 : ℝ) = b.2 := by exact_mod_cast (show a.2 = b.2 by omega)
      exact .inl ⟨Prod.ext (Int.cast_injective (α := ℝ) (by linarith)) (by omega), rfl⟩
    · exact .inr h
  · exact .inr ⟨h01 (b.2 - a.2 + a.1 - b.1) (by push_cast; linarith),
      h01' (a.1 - b.1) (by push_cast; linarith)⟩
  · exact .inr ⟨h01 (b.2 - a.2) (by push_cast; linarith),
      h01' (a.1 - b.1 + b.2 - a.2) (by push_cast; linarith)⟩
  · exact .inr ⟨h01 (b.1 - a.1) (by push_cast; linarith),
      h01' (a.2 - b.2 + b.1 - a.1) (by push_cast; linarith)⟩
  · rcases hdiff (a.1 - b.1) (by push_cast; linarith) with hm | h
    · have : (a.1 : ℝ) = b.1 := by exact_mod_cast (show a.1 = b.1 by omega)
      exact .inl ⟨Prod.ext (by omega) (Int.cast_injective (α := ℝ) (by linarith)), rfl⟩
    · exact .inr h

/-- The triangular lattice, drawn at the integer points with straight edges, is a planar drawing. -/
theorem triangularLattice_isStraightLineDrawing :
    IsStraightLineDrawing triangularLattice latticePos where
  injective := latticePos_injective
  vertex_mem_segment u v w huv hw := by
    obtain ⟨a, d, hd, hs⟩ := exists_eq_add_dir huv
    rw [segment_latticePos_eq hs] at hw
    rw [← Sym2.mem_iff, hs, Sym2.mem_iff]
    rcases segment_latticePos_inter hd (.inl rfl : ((1, 0) : ℤ × ℤ) = (1, 0) ∨ _) hw
      (left_mem_segment ℝ _ (latticePos (w + (1, 0)))) with ⟨rfl, -⟩ | ⟨w', h1, -, h3⟩
    · exact .inl rfl
    · rwa [latticePos_injective h3]
  segment_inter u v u' v' huv huv' z hz hz' := by
    obtain ⟨a, d, hd, hs⟩ := exists_eq_add_dir huv
    obtain ⟨b, e, he, hs'⟩ := exists_eq_add_dir huv'
    rw [segment_latticePos_eq hs] at hz
    rw [segment_latticePos_eq hs'] at hz'
    rcases segment_latticePos_inter hd he hz hz' with ⟨rfl, rfl⟩ | ⟨w, h1, h2, h3⟩
    · exact .inl (hs.trans hs'.symm)
    · refine .inr ⟨w, ?_, ?_, h3⟩
      · rwa [← Sym2.mem_iff, hs, Sym2.mem_iff]
      · rwa [← Sym2.mem_iff, hs', Sym2.mem_iff]

/-- Every graph obtained from the triangular lattice by an injective relabelling (in particular every
finite triangulated grid) is straight-line planar. -/
theorem isStraightLinePlanar_comap_triangularLattice {f : V → ℤ × ℤ} (hf : Function.Injective f) :
    IsStraightLinePlanar (triangularLattice.comap f) :=
  IsStraightLinePlanar.comap ⟨_, triangularLattice_isStraightLineDrawing⟩ hf

end Cslib.SimpleGraph
