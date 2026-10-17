import Podc.CongestLB.Congest
import Podc.Graph.Ball

/-!
# The lower-bound graphs for minimum dominating set (Section 2.1)

Bachrach, Censor-Hillel, Dory, Efron, Leitersdorf, Paz. *Hardness of Distributed Optimization.*
PODC 2019 (arXiv:1905.10284).

`k = 2 ^ L`. A row index `i ∈ [k]` is a bit string `i : Fin L → Bool`.

* Rows: `row s ℓ i` is `a^i_1` (`s = false`, `ℓ = false`), `a^i_2` (`s = false`, `ℓ = true`),
  `b^i_1`, `b^i_2` (`s = true`).
* Bit gadgets: `gad s ℓ h κ` with `κ = 0, 1, 2` is `f^h_S`, `t^h_S`, `u^h_S` for `S = A_ℓ` / `B_ℓ`.
  For every `ℓ, h` the six vertices `f_A, t_A, u_A, f_B, t_B, u_B` form a 6-cycle (in this order).
* `row s ℓ i` is adjacent to `bin(i) = {f^h | i_h = 0} ∪ {t^h | i_h = 1}` as in the
  paper; the dominating set of the `⇐` direction uses the complementary sets `bin̄`, as in the paper.
* Input edges: `a^i_1 – a^j_2` iff `x(i, j) = 1`, `b^i_1 – b^j_2` iff `y(i, j) = 1`.
-/

namespace HardnessOptimization

/-- A row index: a `log k`-bit string. -/
abbrev Idx (L : ℕ) := Fin L → Bool

/-- Vertices of the MDS lower-bound graph. `side = false` is Alice's side (`A`), `layer = false`
is the first row (`A₁`, `B₁`). Gadget kinds: `0 = f`, `1 = t`, `2 = u`. -/
inductive MV (L : ℕ) where
  | row (side layer : Bool) (i : Idx L)
  | gad (side layer : Bool) (h : Fin L) (kind : Fin 3)
  deriving DecidableEq, Fintype

namespace MV

variable {L : ℕ}

/-- The side of a vertex (`false` = Alice's part `V_A`). -/
def side : MV L → Bool
  | row s _ _ => s
  | gad s _ _ _ => s

/-- `none` for rows, `some (ℓ, h)` for the vertices of the 6-cycle `(ℓ, h)`. -/
def cyc : MV L → Option (Bool × Fin L)
  | row _ _ _ => none
  | gad _ ℓ h _ => some (ℓ, h)

end MV

/-- The gadget kind adjacent to a row with bit `b` at position `h`: `t` (1) if `b = 1`, else
`f` (0). -/
def bitK (b : Bool) : Fin 3 := if b then 1 else 0

/-- Position on the 6-cycle `f_A, t_A, u_A, f_B, t_B, u_B`. -/
def cpos (s : Bool) (κ : Fin 3) : Fin 6 := ⟨3 * s.toNat + κ.val, by cases s <;> simp <;> omega⟩

/-- Adjacency on the 6-cycle. -/
def CycAdj (s : Bool) (κ : Fin 3) (s' : Bool) (κ' : Fin 3) : Prop :=
  cpos s' κ' = cpos s κ + 1 ∨ cpos s κ = cpos s' κ' + 1

instance : ∀ s κ s' κ', Decidable (CycAdj s κ s' κ') := fun s κ s' κ' =>
  inferInstanceAs (Decidable (cpos s' κ' = cpos s κ + 1 ∨ cpos s κ = cpos s' κ' + 1))

/-- The input matrix of side `s`. -/
def xy (x y : Idx L → Idx L → Bool) (s : Bool) : Idx L → Idx L → Bool := if s then y else x

/-- Is there an input edge between `row s ℓ i` and `row s (!ℓ) j`? -/
def redge (x y : Idx L → Idx L → Bool) (s ℓ : Bool) (i j : Idx L) : Bool :=
  if ℓ then xy x y s j i else xy x y s i j

/-- The one-directional edge relation, symmetrized by `SimpleGraph.fromRel`. -/
def mdsRel (x y : Idx L → Idx L → Bool) : MV L → MV L → Prop
  | .row s ℓ i, .gad s' ℓ' h κ => s' = s ∧ ℓ' = ℓ ∧ κ = bitK (i h)
  | .row s ℓ i, .row s' ℓ' j => s' = s ∧ ℓ = false ∧ ℓ' = true ∧ xy x y s i j = true
  | .gad s ℓ h κ, .gad s' ℓ' h' κ' => ℓ' = ℓ ∧ h' = h ∧ cpos s' κ' = cpos s κ + 1
  | _, _ => False

instance (x y : Idx L → Idx L → Bool) : DecidableRel (mdsRel x y) := fun a b =>
  match a, b with
  | .row s ℓ i, .gad s' ℓ' h κ => inferInstanceAs (Decidable (s' = s ∧ ℓ' = ℓ ∧ κ = bitK (i h)))
  | .row s ℓ i, .row s' ℓ' j =>
    inferInstanceAs (Decidable (s' = s ∧ ℓ = false ∧ ℓ' = true ∧ xy x y s i j = true))
  | .gad s ℓ h κ, .gad s' ℓ' h' κ' =>
    inferInstanceAs (Decidable (ℓ' = ℓ ∧ h' = h ∧ cpos s' κ' = cpos s κ + 1))
  | .gad _ _ _ _, .row _ _ _ => instDecidableFalse

/-- The graph `G_{x,y}` of Section 2.1. -/
def mdsGraph (x y : Idx L → Idx L → Bool) : SimpleGraph (MV L) := SimpleGraph.fromRel (mdsRel x y)

instance (x y : Idx L → Idx L → Bool) : DecidableRel (mdsGraph x y).Adj := fun a b =>
  inferInstanceAs (Decidable (a ≠ b ∧ (mdsRel x y a b ∨ mdsRel x y b a)))

section Adj

variable (x y : Idx L → Idx L → Bool)

lemma cpos_succ_ne (s : Bool) (κ : Fin 3) : cpos s κ + 1 ≠ cpos s κ := by
  intro h
  have := congrArg Fin.val h
  rw [Fin.val_add] at this
  revert this; cases s <;> fin_cases κ <;> decide

lemma adj_row_row {s ℓ s' ℓ' : Bool} {i j : Idx L} :
    (mdsGraph x y).Adj (.row s ℓ i) (.row s' ℓ' j) ↔
      s' = s ∧ ℓ' = !ℓ ∧ redge x y s ℓ i j = true := by
  simp only [mdsGraph, SimpleGraph.fromRel_adj, mdsRel, redge, ne_eq, MV.row.injEq]
  constructor
  · rintro ⟨-, ⟨rfl, rfl, rfl, h⟩ | ⟨rfl, rfl, rfl, h⟩⟩ <;> simp_all
  · rintro ⟨rfl, rfl, h⟩
    cases ℓ <;> simp_all

lemma adj_row_gad {s ℓ s' ℓ' : Bool} {i : Idx L} {h : Fin L} {κ : Fin 3} :
    (mdsGraph x y).Adj (.row s ℓ i) (.gad s' ℓ' h κ) ↔ s' = s ∧ ℓ' = ℓ ∧ κ = bitK (i h) := by
  simp [mdsGraph, SimpleGraph.fromRel_adj, mdsRel]

lemma adj_gad_row {s ℓ s' ℓ' : Bool} {i : Idx L} {h : Fin L} {κ : Fin 3} :
    (mdsGraph x y).Adj (.gad s' ℓ' h κ) (.row s ℓ i) ↔ s' = s ∧ ℓ' = ℓ ∧ κ = bitK (i h) := by
  rw [SimpleGraph.adj_comm, adj_row_gad]

lemma adj_gad_gad {s ℓ s' ℓ' : Bool} {h h' : Fin L} {κ κ' : Fin 3} :
    (mdsGraph x y).Adj (.gad s ℓ h κ) (.gad s' ℓ' h' κ') ↔
      ℓ' = ℓ ∧ h' = h ∧ CycAdj s κ s' κ' := by
  simp only [mdsGraph, SimpleGraph.fromRel_adj, mdsRel, CycAdj, ne_eq, MV.gad.injEq]
  constructor
  · rintro ⟨-, ⟨rfl, rfl, h1⟩ | ⟨rfl, rfl, h1⟩⟩
    · exact ⟨rfl, rfl, Or.inl h1⟩
    · exact ⟨rfl, rfl, Or.inr h1⟩
  · rintro ⟨rfl, rfl, h1 | h1⟩
    · refine ⟨fun ⟨hs, _, _, hk⟩ => ?_, Or.inl ⟨rfl, rfl, h1⟩⟩
      subst hs hk; exact cpos_succ_ne s κ h1.symm
    · refine ⟨fun ⟨hs, _, _, hk⟩ => ?_, Or.inr ⟨rfl, rfl, h1⟩⟩
      subst hs hk; exact cpos_succ_ne s κ h1.symm

end Adj

/-- A dominating set: every vertex is in `D` or has a neighbour in `D`
(`SimpleGraph.IsDominatingSet` for a finset). -/
abbrev IsDominating {V : Type*} (G : SimpleGraph V) (D : Finset V) : Prop :=
  G.IsDominatingSet ↑D

end HardnessOptimization
