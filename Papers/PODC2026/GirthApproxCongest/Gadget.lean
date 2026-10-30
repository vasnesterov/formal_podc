import Papers.PODC2024.MinWeightCycleCongest.Reduction
import Podc.Computability.Distributed.Congest.MovingCut
import Mathlib.Combinatorics.SimpleGraph.Girth
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The lower-bound graph of §6.0.1 (Chechik–Lifshitz–Mukhtar, PODC 2026)

Fix a bipartite graph `H` with sides `L`, `R` and edge set `E ⊆ L × R`. Alice's and Bob's inputs
are subsets of `E`, given as bit vectors `x y : E → Bool`. The graph `G_{x,y}` (Figure 1):

* **layers**: `q` copies `l u c`, `r w c` (`c : Fin q`) of the vertices `u ∈ L`, `w ∈ R`;
* **pipes**: `r w c → r w (c+1)` and `l u (c+1) → l u c`;
* **input arcs**: `l u 0 → r w 0` if `x (u, w)` (Alice, layer `0`) and
  `r w (q-1) → l u (q-1)` if `y (u, w)` (Bob, layer `q-1`);
* **shortcut tree**: a balanced binary tree whose nodes are `t (h, c)` (level `h ≤ d`, leftmost
  leaf `c`, a multiple of `2^h`; the parent of `(h, c)` is `(h+1, ⌊c / 2^{h+1}⌋ 2^{h+1})`), arcs
  directed from parents to children, and an arc from every layer vertex in column `c` to the leaf
  `t (0, c)`. With `q ≤ 2^d` the root is `t (d, 0)`.
* **padding**: `p` pendant vertices `pad i` with an arc `root → pad i` (our addition, to realise
  every number of nodes `n`).

Columns are `0, …, q-1` (the paper's layers `1, …, q`). The undirected weighted graph of §6.1 has
the same edges, with weight `1` on pipes, `Win` on input edges and `Wt` on tree, leaf and padding
edges.
-/

namespace Podc.GirthApproxCongest

open Finset Podc.MinWeightCycleCongest

/-- Shortcut-tree nodes: level `h ≤ d` and leftmost leaf `c < q`, with `2^h ∣ c`. -/
abbrev TNode (q d : ℕ) := {z : Fin (d + 1) × Fin q // 2 ^ (z.1 : ℕ) ∣ (z.2 : ℕ)}

/-- Vertices of the lower-bound graph. -/
inductive Vtx (L R : Type*) (q d p : ℕ) where
  /-- Copy of `u ∈ L` in column `c`. -/
  | l (u : L) (c : Fin q)
  /-- Copy of `w ∈ R` in column `c`. -/
  | r (w : R) (c : Fin q)
  /-- Shortcut-tree node. -/
  | t (z : TNode q d)
  /-- Padding vertex. -/
  | pad (i : Fin p)
  deriving DecidableEq, Fintype

variable {L R : Type*} {q d p : ℕ}

namespace TNode

/-- Level of a tree node. -/
abbrev h (z : TNode q d) : ℕ := z.1.1
/-- Leftmost leaf (column) of a tree node. -/
abbrev c (z : TNode q d) : ℕ := z.1.2

/-- `z'` is a child of `z`. -/
def Child (z' z : TNode q d) : Prop :=
  z'.h + 1 = z.h ∧ z.c = z'.c / 2 ^ z.h * 2 ^ z.h

instance : DecidableRel (Child (q := q) (d := d)) := fun _ _ => by
  unfold Child; infer_instance

lemma Child.c_le {z' z : TNode q d} (h : Child z' z) : z.c ≤ z'.c := by
  rw [h.2]; exact Nat.div_mul_le_self _ _

lemma Child.lt {z' z : TNode q d} (h : Child z' z) : z'.c < z.c + 2 ^ z.h := by
  rw [h.2]
  have := Nat.lt_div_mul_add (a := z'.c) (b := 2 ^ z.h) (by positivity)
  linarith

/-- The leaf of column `c`. -/
def leaf (c : Fin q) : TNode q d := ⟨(0, c), by simp⟩

/-- The parent of a node below level `d`. -/
def parent (z : TNode q d) (hz : z.h < d) : TNode q d :=
  ⟨(⟨z.h + 1, by omega⟩, ⟨z.c / 2 ^ (z.h + 1) * 2 ^ (z.h + 1),
    lt_of_le_of_lt (Nat.div_mul_le_self _ _) z.1.2.2⟩), by simp⟩

lemma child_parent (z : TNode q d) (hz : z.h < d) : Child z (z.parent hz) := by
  simp [Child, parent]

/-- The root `(d, 0)`. -/
def root (hq : 0 < q) : TNode q d := ⟨(Fin.last d, ⟨0, hq⟩), by simp⟩

lemma h_le (z : TNode q d) : z.h ≤ d := Nat.lt_succ_iff.1 z.1.1.2

@[simp] lemma parent_h (z : TNode q d) (hz : z.h < d) : (z.parent hz).h = z.h + 1 := rfl
@[simp] lemma root_h (hq : 0 < q) : (root hq : TNode q d).h = d := rfl
@[simp] lemma root_c (hq : 0 < q) : (root hq : TNode q d).c = 0 := rfl
@[simp] lemma leaf_h (c : Fin q) : (leaf c : TNode q d).h = 0 := rfl
@[simp] lemma leaf_c (c : Fin q) : (leaf c : TNode q d).c = c := rfl

/-- With `q ≤ 2^d`, the only node of level `d` is the root. -/
lemma eq_root (hqd : q ≤ 2 ^ d) (hq : 0 < q) (z : TNode q d) (hz : z.h = d) : z = root hq := by
  have h1 : 2 ^ d ∣ z.c := by
    have h := z.2
    rwa [show (z.1.1 : ℕ) = d from hz] at h
  have h2 : z.c < 2 ^ d := lt_of_lt_of_le z.1.2.2 hqd
  have h3 : z.c = 0 := Nat.eq_zero_of_dvd_of_lt h1 h2
  apply Subtype.ext
  apply Prod.ext
  · exact Fin.ext hz
  · exact Fin.ext h3

end TNode

namespace Vtx

/-- The column of a vertex (for tree nodes: the leftmost leaf; padding: `0`). -/
def col : Vtx L R q d p → ℕ
  | l _ c => c
  | r _ c => c
  | t z => z.c
  | pad _ => 0

/-- Layer vertices (`l` and `r`). -/
def isLayer : Vtx L R q d p → Bool
  | l _ _ => true
  | r _ _ => true
  | _ => false

lemma col_lt (hq : 0 < q) (v : Vtx L R q d p) : v.col < q := by
  cases v with
  | l _ c => exact c.2
  | r _ c => exact c.2
  | t z => exact z.1.2.2
  | pad _ => exact hq

end Vtx

open Vtx TNode

/-- The bipartite graph `H` on `L ⊕ R` with edge set `E ⊆ L × R`. -/
def bipGraph (E : Finset (L × R)) : SimpleGraph (L ⊕ R) where
  Adj a b := match a, b with
    | .inl u, .inr w => (u, w) ∈ E
    | .inr w, .inl u => (u, w) ∈ E
    | _, _ => False
  symm := ⟨fun a b h => by cases a <;> cases b <;> simp_all⟩
  loopless := ⟨fun a h => by cases a <;> simp_all⟩

@[simp] lemma bipGraph_adj_inl_inr {E : Finset (L × R)} {u : L} {w : R} :
    (bipGraph E).Adj (.inl u) (.inr w) ↔ (u, w) ∈ E := Iff.rfl

@[simp] lemma bipGraph_adj_inr_inl {E : Finset (L × R)} {u : L} {w : R} :
    (bipGraph E).Adj (.inr w) (.inl u) ↔ (u, w) ∈ E := Iff.rfl

@[simp] lemma bipGraph_not_adj_inl_inl {E : Finset (L × R)} {u u' : L} :
    ¬ (bipGraph E).Adj (.inl u) (.inl u') := id

@[simp] lemma bipGraph_not_adj_inr_inr {E : Finset (L × R)} {w w' : R} :
    ¬ (bipGraph E).Adj (.inr w) (.inr w') := id

/-- **Dense bipartite graphs of large girth** (the hypothesis of §6.2): for every `a ≥ 1` there
is a bipartite graph with sides of size `a`, girth at least `2k` and at least
`c · a^{1 + 1/(k-1)}` edges. This is the bipartite (Zarankiewicz) form
`z(a, C_{<2k}) = Ω(a^{1+1/(k-1)})` of the Erdős–Simonovits even cycle conjecture used in the
paper; it is a theorem for `k ∈ {3, 4, 6}` (generalized polygons) and open otherwise. -/
def DenseHighGirth (k : ℕ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ a : ℕ, 1 ≤ a → ∃ E : Finset (Fin a × Fin a),
    ((2 * k : ℕ) : ℕ∞) ≤ (bipGraph E).egirth ∧ c * (a : ℝ) ^ (1 + 1 / ((k : ℝ) - 1)) ≤ E.card

variable (E : Finset (L × R))

/-- The input edge `(u, w)` is present in the input bit vector `x`. -/
def inSet (x : E → Bool) (u : L) (w : R) : Prop := ∃ h : (u, w) ∈ E, x ⟨(u, w), h⟩ = true

instance [DecidableEq L] [DecidableEq R] (x : E → Bool) (u : L) (w : R) :
    Decidable (inSet E x u w) := by
  unfold inSet; infer_instance

/-- Arcs of the directed lower-bound graph `G_{x,y}`. -/
def darc (x y : E → Bool) : Vtx L R q d p → Vtx L R q d p → Prop
  | .r w c, .r w' c' => w = w' ∧ (c' : ℕ) = c + 1
  | .l u c, .l u' c' => u = u' ∧ (c : ℕ) = c' + 1
  | .l u c, .r w c' => (c : ℕ) = 0 ∧ (c' : ℕ) = 0 ∧ inSet E x u w
  | .r w c, .l u c' => (c : ℕ) + 1 = q ∧ (c' : ℕ) + 1 = q ∧ inSet E y u w
  | .l _ c, .t z => z.h = 0 ∧ z.c = c
  | .r _ c, .t z => z.h = 0 ∧ z.c = c
  | .t z, .t z' => Child z' z
  | .t z, .pad _ => z.h = d ∧ z.c = 0
  | _, _ => False

instance [DecidableEq L] [DecidableEq R] (x y : E → Bool) :
    DecidableRel (darc (q := q) (d := d) (p := p) E x y) := fun u v => by
  cases u <;> cases v <;> unfold darc <;> infer_instance

variable {E}

lemma not_darc_self (x y : E → Bool) (v : Vtx L R q d p) : ¬ darc E x y v v := by
  cases v <;> simp [darc, Child]

/-- The underlying undirected network of `G_{x,y}`. -/
def gnet (x y : E → Bool) : SimpleGraph (Vtx L R q d p) := SimpleGraph.fromRel (darc E x y)

/-- Weight of an edge of the undirected graph of §6.1: `1` on pipes, `Win` on input edges (both
ends in the same column), `Wt` on the tree, leaf and padding edges. -/
def ew (Win Wt : ℕ) (u v : Vtx L R q d p) : ℕ :=
  if u.isLayer ∧ v.isLayer then (if u.col = v.col then Win else 1) else Wt

lemma ew_comm (Win Wt : ℕ) (u v : Vtx L R q d p) : ew Win Wt u v = ew Win Wt v u := by
  unfold ew
  by_cases hu : u.isLayer <;> by_cases hv : v.isLayer <;> simp [hu, hv, eq_comm]

variable [DecidableEq L] [DecidableEq R]

/-- The directed lower-bound graph `G_{x,y}` of §6.0.1 (all arcs of weight `1`). -/
def dGraph (W : ℕ) (x y : E → Bool) : WDigraph (Vtx L R q d p) (W + 1) where
  wt u v := if darc E x y u v then some 1 else none

/-- The undirected weighted lower-bound graph of §6.1 (weights in `{0, …, Wm}`). -/
def uGraph (Wm Win Wt : ℕ) (x y : E → Bool) : WGraph (Vtx L R q d p) Wm where
  wt u v := if darc E x y u v ∨ darc E x y v u then some (Fin.ofNat (Wm + 1) (ew Win Wt u v))
    else none
  symm u v := by
    rw [ew_comm]
    by_cases h : darc E x y u v ∨ darc E x y v u
    · rw [if_pos h, if_pos (Or.comm.1 h)]
    · rw [if_neg h, if_neg (fun h' => h (Or.comm.1 h'))]
  loopless v := by rw [if_neg (by simp only [or_self]; exact not_darc_self x y v)]

variable {W Wm Win Wt : ℕ} {x y : E → Bool}

lemma dGraph_isSome {u v : Vtx L R q d p} : ((dGraph W x y).wt u v).isSome ↔ darc E x y u v := by
  simp only [dGraph]; split_ifs with h <;> simp [h]

lemma dGraph_w {u v : Vtx L R q d p} (h : darc E x y u v) : (dGraph W x y).w u v = 1 := by
  simp [WDigraph.w, dGraph, h]

lemma dGraph_unweighted : (dGraph (q := q) (d := d) (p := p) W x y).Unweighted := by
  intro u v c h
  simp only [dGraph] at h
  split_ifs at h with h'
  cases h
  simp

lemma uGraph_isSome {u v : Vtx L R q d p} :
    ((uGraph Wm Win Wt x y).wt u v).isSome ↔ darc E x y u v ∨ darc E x y v u := by
  simp only [uGraph]; split_ifs with h <;> simp [h]

lemma uGraph_w {u v : Vtx L R q d p} (hW : Win ≤ Wm) (hWt : Wt ≤ Wm) (hW1 : 1 ≤ Wm)
    (h : darc E x y u v ∨ darc E x y v u) : (uGraph Wm Win Wt x y).w u v = ew Win Wt u v := by
  have hle : ew Win Wt u v ≤ Wm := by unfold ew; split_ifs <;> omega
  simp only [WGraph.w, uGraph, if_pos h, Option.map_some, Option.getD_some, Fin.val_ofNat]
  exact Nat.mod_eq_of_lt (by omega)

/-! ### Independence of the arcs from the inputs -/

/-- Arcs not touching Bob's input column (`r w (q-1)`, `l u (q-1)` both) do not depend on `y`. -/
lemma darc_indep_y (x : E → Bool) (y y' : E → Bool) {u v : Vtx L R q d p}
    (h : u.col + 1 ≠ q ∨ v.col + 1 ≠ q) : darc E x y u v ↔ darc E x y' u v := by
  cases u <;> cases v <;> simp_all [darc, col]
  all_goals (intros; exfalso; omega)

/-- Arcs not touching Alice's input column `0` (both ends) do not depend on `x`. -/
lemma darc_indep_x (x x' : E → Bool) (y : E → Bool) {u v : Vtx L R q d p}
    (h : u.col ≠ 0 ∨ v.col ≠ 0) : darc E x y u v ↔ darc E x' y u v := by
  cases u <;> cases v <;> simp_all [darc, col]
  all_goals (intros; exfalso; omega)

/-- Shape of an arc: the columns differ by at most one, or it is a tree arc from a parent to a
child. -/
lemma darc_cases {u v : Vtx L R q d p} (h : darc E x y u v) :
    (u.col ≤ v.col + 1 ∧ v.col ≤ u.col + 1) ∨
      ∃ z z', u = .t z ∧ v = .t z' ∧ Child z' z := by
  cases u <;> cases v <;> simp_all [darc, col] <;> omega

end Podc.GirthApproxCongest
