import Cslib.Foundations.Combinatorics.SimpleGraph.WeightedSpanner
import Mathlib

/-!
# The graphs `H_{b,ℓ}` and `G_{b,ℓ}` of Kosowski–Uznański–Viennot (PODC 2019)

Kosowski, Uznański, Viennot. *Hardness of exact distance queries in sparse graphs through hub
labeling.* PODC 2019, arXiv:1902.07055v3, Section 2 (proof of Theorem 2.1).

Notation (0-indexed coordinates; the paper indexes coordinates from 1):

* `s = 2^b` (`side`), `A = 3ℓs²` (`bigA`).
* `Main b ℓ = Fin (2ℓ+1) × (Fin ℓ → Fin s)`: the vertex `v_{i,j}` of `H_{b,ℓ}` (level `i`, vector `j`).
* `cnat ℓ i`: the coordinate that may change between levels `i` and `i+1`
  (`i` for `i < ℓ`, `2ℓ-1-i` for `i ≥ ℓ`; the paper's `c = i+1`, resp. `c = 2ℓ-i`).
* `H b ℓ`: `v_{i,j} ~ v_{i+1,j'}` iff `j, j'` agree outside coordinate `cnat ℓ i`;
  weight `hw u v = A + Σ_k (u_k - v_k)²` (which is `A + (j_c - j'_c)²` on edges), `wlen` = weight of a walk.
* `GV b ℓ`, `G b ℓ`: the max-degree-3 graph `G_{b,ℓ}`: every vertex `v` of `H` gets an in-tree
  (`tin`, leaves = lower neighbours, absent at level 0) and an out-tree (`tout`, leaves = upper neighbours,
  absent at level `2ℓ`), perfect binary trees with `s` leaves in heap numbering (node `n` has children
  `2n+1, 2n+2`; the leaf of value `t` is `s-1+t`); every edge `e` of `H` becomes a path of
  `w(e) - 2b - 2` edges (`mid` vertices) between the corresponding leaves.
-/

namespace Podc.HubLabelingHardness

open SimpleGraph Finset

/-- The side length `s = 2^b`. -/
abbrev side (b : ℕ) : ℕ := 2 ^ b

/-- The base weight `A = 3ℓs²`. -/
abbrev bigA (b ℓ : ℕ) : ℕ := 3 * ℓ * side b ^ 2

lemma one_le_side (b : ℕ) : 1 ≤ side b := Nat.one_le_two_pow

/-- Vectors `[0, s-1]^ℓ`. -/
abbrev Vec (b ℓ : ℕ) := Fin ℓ → Fin (side b)

/-- Vertices of `H_{b,ℓ}`: `v_{i,j}` with level `i ∈ [0, 2ℓ]` and `j ∈ [0, s-1]^ℓ`. -/
abbrev Main (b ℓ : ℕ) := Fin (2 * ℓ + 1) × Vec b ℓ

/-- The coordinate that may change between levels `i` and `i + 1` (0-indexed). -/
def cnat (ℓ i : ℕ) : ℕ := if i < ℓ then i else 2 * ℓ - 1 - i

/-- `cnat` as an element of `Fin ℓ`. -/
def cc {ℓ : ℕ} (i : Fin (2 * ℓ)) : Fin ℓ :=
  ⟨cnat ℓ i, by unfold cnat; split_ifs <;> omega⟩

@[simp] lemma cc_val {ℓ : ℕ} (i : Fin (2 * ℓ)) : (cc i).val = cnat ℓ i := rfl

/-- Squared difference of two naturals, as a natural number. -/
def sqd (a c : ℕ) : ℕ := (Int.natAbs ((a : ℤ) - c)) ^ 2

@[simp] lemma sqd_cast (a c : ℕ) : ((sqd a c : ℕ) : ℤ) = ((a : ℤ) - c) ^ 2 := by
  simp [sqd]

lemma sqd_comm (a c : ℕ) : sqd a c = sqd c a := by
  simp only [sqd]; rw [show ((a : ℤ) - c) = -((c : ℤ) - a) by ring, Int.natAbs_neg]

@[simp] lemma sqd_self (a : ℕ) : sqd a a = 0 := by simp [sqd]

/-! ## The weighted layered graph `H_{b,ℓ}` -/

/-- Adjacency of `H_{b,ℓ}`: consecutive levels, vectors agreeing outside coordinate `cnat`. -/
def HAdj (b ℓ : ℕ) (u v : Main b ℓ) : Prop :=
  (v.1.val = u.1.val + 1 ∧ ∀ k : Fin ℓ, k.val ≠ cnat ℓ u.1.val → v.2 k = u.2 k) ∨
  (u.1.val = v.1.val + 1 ∧ ∀ k : Fin ℓ, k.val ≠ cnat ℓ v.1.val → u.2 k = v.2 k)

/-- The layered graph `H_{b,ℓ}` (unweighted structure). -/
def H (b ℓ : ℕ) : SimpleGraph (Main b ℓ) where
  Adj := HAdj b ℓ
  symm := ⟨fun _ _ h => Or.symm h⟩
  loopless := ⟨fun _ h => by rcases h with ⟨h, _⟩ | ⟨h, _⟩ <;> omega⟩

/-- Edge weights of `H_{b,ℓ}`: `w(u, v) = A + Σ_k (u_k - v_k)²`; on an edge only the coordinate
`c` can differ, so this is the paper's `A + (j_c - j'_c)²`. -/
def hw (b ℓ : ℕ) (u v : Main b ℓ) : ℕ := bigA b ℓ + ∑ k, sqd (u.2 k) (v.2 k)

lemma hw_comm (b ℓ : ℕ) (u v : Main b ℓ) : hw b ℓ u v = hw b ℓ v u := by
  simp only [hw, sqd_comm]

/-- The weight function on unordered pairs. -/
def hwS (b ℓ : ℕ) : Sym2 (Main b ℓ) → ℕ := Sym2.lift ⟨hw b ℓ, hw_comm b ℓ⟩

/-- Weighted length of a walk of `H_{b,ℓ}`. -/
def wlen {b ℓ : ℕ} : {u v : Main b ℓ} → (H b ℓ).Walk u v → ℕ
  | _, _, .nil => 0
  | u, _, .cons (v := v) _ p => hw b ℓ u v + wlen p

@[simp] lemma wlen_nil {b ℓ : ℕ} {u : Main b ℓ} : wlen (Walk.nil : (H b ℓ).Walk u u) = 0 := rfl

@[simp] lemma wlen_cons {b ℓ : ℕ} {u v w : Main b ℓ} (h : (H b ℓ).Adj u v) (p : (H b ℓ).Walk v w) :
    wlen (Walk.cons h p) = hw b ℓ u v + wlen p := rfl

/-- `wlen` is CSLib's `Walk.wlength` for the weights `hwS`. -/
lemma wlen_eq_wlength {b ℓ : ℕ} {u v : Main b ℓ} (p : (H b ℓ).Walk u v) :
    (wlen p : ENNReal) = p.wlength (fun e => (hwS b ℓ e : NNReal)) := by
  induction p with
  | nil => simp
  | cons h p ih => simp [ih, hwS]

/-- The bottom vertex `v_{0,x}`. -/
def bot {b ℓ : ℕ} (x : Vec b ℓ) : Main b ℓ := (0, x)

/-- The top vertex `v_{2ℓ,z}`. -/
def top {b ℓ : ℕ} (z : Vec b ℓ) : Main b ℓ := (Fin.last _, z)

/-- The middle vertex `v_{ℓ,y}`. -/
def midl {b ℓ : ℕ} (y : Vec b ℓ) : Main b ℓ := (⟨ℓ, by omega⟩, y)

/-- Coordinatewise midpoint `(x + z) / 2` (rounded down). -/
def midpt {b ℓ : ℕ} (x z : Vec b ℓ) : Vec b ℓ :=
  fun k => ⟨((x k : ℕ) + z k) / 2, by have := (x k).2; have := (z k).2; omega⟩

/-- The parity condition of Lemma 2.2: `z_k - x_k` is even for all `k`. -/
def EvenDiff {b ℓ : ℕ} (x z : Vec b ℓ) : Prop := ∀ k, Even ((z k : ℤ) - x k)

/-- The length of the unique shortest `v_{0,x}`–`v_{2ℓ,z}` path:
`2ℓA + 2 Σ_k ((z_k - x_k)/2)² = 2ℓA + Σ_k (z_k - x_k)²/2`. -/
def Lopt {b ℓ : ℕ} (x z : Vec b ℓ) : ℕ :=
  2 * ℓ * bigA b ℓ + 2 * ∑ k, sqd (x k) (midpt x z k)

/-! ## The max-degree-3 graph `G_{b,ℓ}` -/

/-- Number of edges of the path replacing the `H`-edge from `v_{i,j}` to `v_{i+1,j[c ↦ t]}`:
`w(e) - 2b - 2`. -/
def plen (b ℓ : ℕ) (i : Fin (2 * ℓ)) (j : Vec b ℓ) (t : Fin (side b)) : ℕ :=
  bigA b ℓ + sqd (j (cc i)) t - 2 * b - 2

/-- Vertices of `G_{b,ℓ}`.
* `main i j` — the vertex `v_{i,j}` of `H`;
* `tin i j n` — node `n` of the in-tree `T^in` of `v_{i+1,j}` (leaves ↔ neighbours in level `i`);
* `tout i j n` — node `n` of the out-tree `T^out` of `v_{i,j}` (leaves ↔ neighbours in level `i+1`);
* `mid i j t p` — the `p`-th internal vertex (`0 ≤ p < w - 2b - 3`) of the path replacing the edge
  from `v_{i,j}` to `v_{i+1, j[c ↦ t]}`, counted from the out-tree side. -/
inductive GV (b ℓ : ℕ) where
  | main (i : Fin (2 * ℓ + 1)) (j : Vec b ℓ)
  | tin (i : Fin (2 * ℓ)) (j : Vec b ℓ) (n : Fin (2 * side b - 1))
  | tout (i : Fin (2 * ℓ)) (j : Vec b ℓ) (n : Fin (2 * side b - 1))
  | mid (i : Fin (2 * ℓ)) (j : Vec b ℓ) (t : Fin (side b)) (p : Fin (plen b ℓ i j t - 1))

namespace GV

variable {b ℓ : ℕ}

/-- The four kinds of vertices as a sum type (used for the `Fintype` instance and counting). -/
abbrev Code (b ℓ : ℕ) :=
  Main b ℓ ⊕ (Fin (2 * ℓ) × Vec b ℓ × Fin (2 * side b - 1)) ⊕
    (Fin (2 * ℓ) × Vec b ℓ × Fin (2 * side b - 1)) ⊕
    (Σ e : Fin (2 * ℓ) × Vec b ℓ × Fin (side b), Fin (plen b ℓ e.1 e.2.1 e.2.2 - 1))

/-- Encoding of vertices. -/
def equivCode : GV b ℓ ≃ Code b ℓ where
  toFun
    | main i j => .inl (i, j)
    | tin i j n => .inr (.inl (i, j, n))
    | tout i j n => .inr (.inr (.inl (i, j, n)))
    | mid i j t p => .inr (.inr (.inr ⟨(i, j, t), p⟩))
  invFun
    | .inl (i, j) => main i j
    | .inr (.inl (i, j, n)) => tin i j n
    | .inr (.inr (.inl (i, j, n))) => tout i j n
    | .inr (.inr (.inr ⟨(i, j, t), p⟩)) => mid i j t p
  left_inv a := by cases a <;> rfl
  right_inv c := by rcases c with ⟨_, _⟩ | ⟨_, _, _⟩ | ⟨_, _, _⟩ | ⟨⟨_, _, _⟩, _⟩ <;> rfl

noncomputable instance : DecidableEq (GV b ℓ) := Classical.decEq _

instance : Fintype (GV b ℓ) := Fintype.ofEquiv _ equivCode.symm

end GV

open GV

/-- The root of a tree (heap index `0`). -/
def root (b : ℕ) : Fin (2 * side b - 1) := ⟨0, by have := one_le_side b; omega⟩

/-- The leaf of value `t` (heap index `s - 1 + t`). -/
def leaf {b : ℕ} (t : Fin (side b)) : Fin (2 * side b - 1) :=
  ⟨side b - 1 + t, by have := t.2; omega⟩

/-- The edges of `G_{b,ℓ}`, each listed once (oriented upwards / away from the main vertex). -/
inductive E (b ℓ : ℕ) : GV b ℓ → GV b ℓ → Prop
  /-- `v_{i+1,j}` — root of its in-tree. -/
  | inRoot (i : Fin (2 * ℓ)) (j : Vec b ℓ) : E b ℓ (main i.succ j) (tin i j (root b))
  /-- `v_{i,j}` — root of its out-tree. -/
  | outRoot (i : Fin (2 * ℓ)) (j : Vec b ℓ) : E b ℓ (main i.castSucc j) (tout i j (root b))
  /-- in-tree: parent `n` — child `m ∈ {2n+1, 2n+2}`. -/
  | inChild (i : Fin (2 * ℓ)) (j : Vec b ℓ) (n m : Fin (2 * side b - 1))
      (h : m.val = 2 * n.val + 1 ∨ m.val = 2 * n.val + 2) : E b ℓ (tin i j n) (tin i j m)
  /-- out-tree: parent `n` — child `m ∈ {2n+1, 2n+2}`. -/
  | outChild (i : Fin (2 * ℓ)) (j : Vec b ℓ) (n m : Fin (2 * side b - 1))
      (h : m.val = 2 * n.val + 1 ∨ m.val = 2 * n.val + 2) : E b ℓ (tout i j n) (tout i j m)
  /-- out-leaf `v_{i,j}^{out}` of the edge — first internal path vertex. -/
  | pathStart (i : Fin (2 * ℓ)) (j : Vec b ℓ) (t : Fin (side b)) (p : Fin (plen b ℓ i j t - 1))
      (hp : p.val = 0) : E b ℓ (tout i j (leaf t)) (mid i j t p)
  /-- consecutive internal path vertices. -/
  | pathStep (i : Fin (2 * ℓ)) (j : Vec b ℓ) (t : Fin (side b)) (p q : Fin (plen b ℓ i j t - 1))
      (h : q.val = p.val + 1) : E b ℓ (mid i j t p) (mid i j t q)
  /-- last internal path vertex — in-leaf of the upper endpoint `v_{i+1, j[c ↦ t]}`, labelled by
  the lower endpoint's coordinate `j_c`. -/
  | pathEnd (i : Fin (2 * ℓ)) (j : Vec b ℓ) (t : Fin (side b)) (p : Fin (plen b ℓ i j t - 1))
      (hp : p.val + 2 = plen b ℓ i j t) :
      E b ℓ (mid i j t p) (tin i (Function.update j (cc i) t) (leaf (j (cc i))))

/-- The graph `G_{b,ℓ}` of Theorem 2.1. -/
def G (b ℓ : ℕ) : SimpleGraph (GV b ℓ) := SimpleGraph.fromRel (E b ℓ)

lemma G_adj {b ℓ : ℕ} {a c : GV b ℓ} : (G b ℓ).Adj a c ↔ a ≠ c ∧ (E b ℓ a c ∨ E b ℓ c a) :=
  Iff.rfl

end Podc.HubLabelingHardness
