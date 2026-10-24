import Cslib.Computability.Distributed.Local.Locality
import Podc.Foundations.Combinatorics.SimpleGraph.StraightLineDrawing

/-!
# The triangulated grid, identifier assignments and local views

The graph `G` of Hilke–Lenzen–Suomela (Figure 1a) is a `W × H` piece of the triangular lattice:
node `(x, y)` (`x < W` columns, `y < H` rows) is adjacent to `(x ± 1, y)`, `(x, y ± 1)` and
`(x + 1, y + 1)`, `(x - 1, y - 1)` (`grid W H`, the triangular lattice pulled back along the
integer embedding `pt`). It is planar (`grid_isStraightLinePlanar`).

In the LOCAL model with unique identifiers `{0, …, n - 1}` (`n = W · H`), an instance is an
identifier assignment `σ : GV W H ≃ Fin n`; the network is the copy `lab σ` of the grid whose
nodes are the identifiers.

`view T σ v` is the `(2T+1) × (2T+1)` array of identifiers around `v` (`none` outside the grid). The
key fact (`out_eq_of_view_eq`): a `T`-round LOCAL algorithm gives the same output at two nodes whose
views agree (`Cslib.Local.IsLocal`), because the radius-`T` neighbourhood of a node lies in this array
and the triangular lattice is translation invariant. This is the paper's "the local output of `v`
only depends on the identifiers in the `k × k` region `R_v`" (Figure 1c).
-/

namespace Podc.PlanarMDSLowerBound

open SimpleGraph Cslib.SimpleGraph

/-- Grid nodes: `x < W` (column), `y < H` (row). -/
abbrev GV (W H : ℕ) := Fin W × Fin H

/-- Integer coordinates of a grid node. -/
def pt {W H : ℕ} (p : GV W H) : ℤ × ℤ := ((p.1 : ℕ), (p.2 : ℕ))

lemma pt_injective {W H : ℕ} : Function.Injective (pt (W := W) (H := H)) := by
  intro p q h
  simp only [pt, Prod.mk.injEq, Nat.cast_inj] at h
  exact Prod.ext (Fin.ext h.1) (Fin.ext h.2)

/-- The `W × H` triangulated grid (Figure 1a of the paper, as one strip of `r` blocks). -/
def grid (W H : ℕ) : SimpleGraph (GV W H) := triangularLattice.comap pt

lemma grid_adj {W H : ℕ} {p q : GV W H} :
    (grid W H).Adj p q ↔ TriAdj (pt p) (pt q) := Iff.rfl

/-- The triangulated grid is planar (it has a straight-line planar drawing). -/
theorem grid_isStraightLinePlanar (W H : ℕ) : IsStraightLinePlanar (grid W H) :=
  isStraightLinePlanar_comap_triangularLattice pt_injective

/-- The network with identifier assignment `σ`: the copy of the grid on the identifiers. -/
def lab {W H n : ℕ} (σ : GV W H ≃ Fin n) : SimpleGraph (Fin n) := (grid W H).comap σ.symm

lemma lab_adj {W H n : ℕ} {σ : GV W H ≃ Fin n} {a b : Fin n} :
    (lab σ).Adj a b ↔ TriAdj (pt (σ.symm a)) (pt (σ.symm b)) := Iff.rfl

/-- `lab σ` is isomorphic to the grid. -/
def labIso {W H n : ℕ} (σ : GV W H ≃ Fin n) : lab σ ≃g grid W H := ⟨σ.symm, Iff.rfl⟩

/-! ### Distances -/

/-- A function changing by at most `1` along edges changes by at most the length of a walk. -/
lemma abs_sub_le_length {V : Type*} {G : SimpleGraph V} (f : V → ℤ)
    (hf : ∀ u v, G.Adj u v → |f u - f v| ≤ 1) {u v : V} (p : G.Walk u v) :
    |f u - f v| ≤ p.length := by
  induction p with
  | nil => simp
  | cons h p ih =>
    rename_i a b c
    have h1 := hf _ _ h
    rw [Walk.length_cons, Nat.cast_add, Nat.cast_one]
    calc |f a - f c| = |(f a - f b) + (f b - f c)| := by ring_nf
      _ ≤ |f a - f b| + |f b - f c| := abs_add_le _ _
      _ ≤ 1 + p.length := add_le_add h1 ih
      _ = _ := add_comm _ _

/-- Nodes at distance `< T` from `a` in `lab σ` are within `T - 1` in both coordinates. -/
lemma coord_close {W H n : ℕ} {σ : GV W H ≃ Fin n} {a b : Fin n} {T : ℕ}
    (h : (lab σ).edist a b < T) :
    |(pt (σ.symm a)).1 - (pt (σ.symm b)).1| < T ∧ |(pt (σ.symm a)).2 - (pt (σ.symm b)).2| < T := by
  obtain ⟨p, hp⟩ := exists_walk_of_edist_ne_top (ne_top_of_lt h)
  rw [← hp] at h
  have hl : (p.length : ℤ) < T := by exact_mod_cast h
  constructor
  · refine lt_of_le_of_lt (abs_sub_le_length (fun z => (pt (σ.symm z)).1) ?_ p) hl
    intro u v huv
    rw [lab_adj, TriAdj] at huv
    rw [abs_le]; omega
  · refine lt_of_le_of_lt (abs_sub_le_length (fun z => (pt (σ.symm z)).2) ?_ p) hl
    intro u v huv
    rw [lab_adj, TriAdj] at huv
    rw [abs_le]; omega

/-! ### Identifiers at integer points and local views -/

/-- The identifier at the integer point `(x, y)` (`none` outside the grid). -/
def idAt {W H n : ℕ} (σ : GV W H ≃ Fin n) (x y : ℤ) : Option (Fin n) :=
  if h : 0 ≤ x ∧ x < W ∧ 0 ≤ y ∧ y < H then
    some (σ (⟨x.toNat, by omega⟩, ⟨y.toNat, by omega⟩))
  else none

lemma idAt_eq_some {W H n : ℕ} {σ : GV W H ≃ Fin n} {x y : ℤ} {z : Fin n} :
    idAt σ x y = some z ↔ pt (σ.symm z) = (x, y) := by
  unfold idAt
  split_ifs with h
  · rw [Option.some_inj, ← Equiv.eq_symm_apply]
    constructor
    · intro e; rw [← e]; simp only [pt, Prod.mk.injEq]; omega
    · intro e
      apply pt_injective
      rw [e]; simp only [pt, Prod.mk.injEq]; omega
  · simp only [false_iff]
    intro e
    simp only [pt, Prod.mk.injEq] at e
    have := (σ.symm z).1.isLt
    have := (σ.symm z).2.isLt
    omega

lemma idAt_pt {W H n : ℕ} (σ : GV W H ≃ Fin n) (p : GV W H) :
    idAt σ (pt p).1 (pt p).2 = some (σ p) :=
  idAt_eq_some.2 (by simp)

/-- The local view of `v`: the identifiers in the `(2T+1) × (2T+1)` square `R_v` centred at `v`
(column offset `i - T`, row offset `j - T`). -/
def view {W H n : ℕ} (T : ℕ) (σ : GV W H ≃ Fin n) (v : GV W H) :
    Fin (2 * T + 1) → Fin (2 * T + 1) → Option (Fin n) :=
  fun i j => idAt σ ((pt v).1 + ((i : ℕ) - T : ℤ)) ((pt v).2 + ((j : ℕ) - T : ℤ))

lemma idAt_eq_of_view_eq {W H n : ℕ} {T : ℕ} {σ τ : GV W H ≃ Fin n} {v w : GV W H}
    (h : view T σ v = view T τ w) {dx dy : ℤ} (hx : |dx| ≤ T) (hy : |dy| ≤ T) :
    idAt σ ((pt v).1 + dx) ((pt v).2 + dy) = idAt τ ((pt w).1 + dx) ((pt w).2 + dy) := by
  rw [abs_le] at hx hy
  have := congrFun (congrFun h ⟨(dx + T).toNat, by omega⟩) ⟨(dy + T).toNat, by omega⟩
  simp only [view] at this
  have e1 : (((dx + T).toNat : ℕ) : ℤ) - T = dx := by omega
  have e2 : (((dy + T).toNat : ℕ) : ℤ) - T = dy := by omega
  rwa [e1, e2] at this

/-- One direction of the edge transfer in `out_eq_of_view_eq`. -/
private lemma adj_transfer {W H n : ℕ} {T : ℕ} {σ τ : GV W H ≃ Fin n} {v w : GV W H}
    (h : view T σ v = view T τ w) {z y : Fin n} {dx dy : ℤ} (hx : |dx| < T) (hy : |dy| < T)
    (hzσ : pt (σ.symm z) = ((pt v).1 + dx, (pt v).2 + dy))
    (hzτ : pt (τ.symm z) = ((pt w).1 + dx, (pt w).2 + dy))
    (hadj : (lab σ).Adj z y) : (lab τ).Adj z y := by
  rw [lab_adj] at hadj ⊢
  have hex : -1 ≤ (pt (σ.symm y)).1 - (pt (σ.symm z)).1 ∧ (pt (σ.symm y)).1 - (pt (σ.symm z)).1 ≤ 1 ∧
      -1 ≤ (pt (σ.symm y)).2 - (pt (σ.symm z)).2 ∧ (pt (σ.symm y)).2 - (pt (σ.symm z)).2 ≤ 1 := by
    simp only [TriAdj] at hadj; omega
  set ex := (pt (σ.symm y)).1 - (pt (σ.symm z)).1
  set ey := (pt (σ.symm y)).2 - (pt (σ.symm z)).2
  rw [abs_lt] at hx hy
  have hyσ : pt (σ.symm y) = ((pt v).1 + (dx + ex), (pt v).2 + (dy + ey)) := by
    rw [Prod.ext_iff] at hzσ ⊢; simp only at hzσ ⊢; omega
  have key := idAt_eq_of_view_eq h (dx := dx + ex) (dy := dy + ey)
    (by rw [abs_le]; omega) (by rw [abs_le]; omega)
  rw [idAt_eq_some.2 hyσ] at key
  have hyτ := idAt_eq_some.1 key.symm
  rw [hzτ, hyτ]
  rw [hzσ, hyσ] at hadj
  simp only [TriAdj] at hadj ⊢
  omega

/-- **Locality** (Figure 1c): a `T`-round LOCAL algorithm produces the same output at two nodes
whose `(2T+1) × (2T+1)` views coincide. -/
theorem out_eq_of_view_eq {W H n T : ℕ} {β : Type*} {A : SimpleGraph (Fin n) → Fin n → β}
    (hA : Cslib.Local.IsLocal T (fun G (_ : Fin n → Unit) v => A G v))
    {σ τ : GV W H ≃ Fin n} {v w : GV W H} (h : view T σ v = view T τ w) :
    A (lab σ) (σ v) = A (lab τ) (τ w) := by
  have h0 := idAt_eq_of_view_eq h (dx := 0) (dy := 0) (by simp) (by simp)
  simp only [add_zero] at h0
  rw [idAt_pt, idAt_pt, Option.some_inj] at h0
  rw [← h0]
  refine hA (lab σ) (fun _ => ()) (lab τ) (fun _ => ()) (σ v) ⟨?_, fun _ _ => rfl⟩
  intro z hz y
  obtain ⟨c1, c2⟩ := coord_close hz
  simp only [Equiv.symm_apply_apply] at c1 c2
  set dx := (pt (σ.symm z)).1 - (pt v).1
  set dy := (pt (σ.symm z)).2 - (pt v).2
  have hx : |dx| < T := by rw [abs_sub_comm]; exact c1
  have hy : |dy| < T := by rw [abs_sub_comm]; exact c2
  have hzσ : pt (σ.symm z) = ((pt v).1 + dx, (pt v).2 + dy) := by
    ext <;> simp [dx, dy]
  have key := idAt_eq_of_view_eq h (dx := dx) (dy := dy) hx.le hy.le
  rw [idAt_eq_some.2 hzσ] at key
  have hzτ := idAt_eq_some.1 key.symm
  constructor
  · exact adj_transfer h hx hy hzσ hzτ
  · exact adj_transfer h.symm hx hy hzτ hzσ

end Podc.PlanarMDSLowerBound
