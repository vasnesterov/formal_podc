import Mathlib.Combinatorics.SimpleGraph.Metric

/-!
# The lower-bound graph of Lemma 3.2: its diameter can exceed `D'`

Ghaffari–Haeupler, *Low-Congestion Shortcuts for Graphs Excluding Dense Minors*, PODC 2021
(arXiv 2008.03091), Section 3.2, proof of Lemma 3.2.

To show that shortcut quality `Ω̃(δ D)` is sometimes necessary, the proof sets `δ = δ' - 2`,
`k = ⌊D'/(2δ)⌋`, `D = kδ`, and builds the following graph:

* a path `p_1, …, p_{(δ-1)k+1}` (the "top path");
* for each `i ∈ [(δ-1)D+1]` a path `v_{i,1}, …, v_{i,(δ-1)D+1}` (the rows);
* for each `j ∈ [δ]`, the nodes `v_{1,(j-1)D+1}, …, v_{(δ-1)D+1,(j-1)D+1}` form a path
  (the columns);
* for all `j, j' ∈ [δ]`, the node `v_{(j'-1)D+1,(j-1)D+1}` is adjacent to `p_{(j-1)k+1}`.

The paper then claims that the diameter is at most `1.5 D + 1 ≤ D'`; the computation given is
really an eccentricity bound from a central node, not a bound on the diameter. We define the
graph faithfully (`lbGraph δ k`, 0-indexed) and show that for `δ' = 5`, `D' = 12`
(so `δ = 3`, `k = 2`, `D = 6`; 174 vertices) the nodes `v_{3,3}` and `v_{10,11}` are at
distance exactly `15 > 12 = D'` (`paperGraph_dist_eq`, `paperGraph_not_diam_le`).

This is a counterexample to the **diameter claim inside the proof** of Lemma 3.2, not to the
statement of Lemma 3.2 (which is existential). Numerically (Python BFS, small parameters) the
diameter of this construction is about `3D`, and choosing e.g. `k = ⌊(D' - 2)/(3δ)⌋` instead gave
diameter `≤ D'` in all tested cases, so the proof is repairable up to constants (not formalized).

The lower bound on the distance uses a 1-Lipschitz potential certificate
(`le_add_dist_of_lipschitz`): the BFS distances from `v_{3,3}`, checked edge by edge by `decide`.
-/

namespace LowCongestionShortcuts.LowerBound

/-- Vertices of the lower-bound graph with parameters `δ, k` (`D = δ k`), 0-indexed:
`Sum.inl a` is the top-path node `p_{a+1}` (`a < (δ-1)k+1`) and `Sum.inr (i, j)` is the grid
node `v_{i+1,j+1}` (`i, j < (δ-1)D+1`). -/
abbrev Vtx (δ k : ℕ) : Type :=
  Fin ((δ - 1) * k + 1) ⊕ (Fin ((δ - 1) * (δ * k) + 1) × Fin ((δ - 1) * (δ * k) + 1))

/-- One orientation of each edge of the construction in the proof of Lemma 3.2
(0-indexed, `D = δ k`):
* top path: `p_a — p_{a+1}`;
* rows: `v_{i,j} — v_{i,j+1}`;
* columns: `v_{i,j} — v_{i+1,j}` when `D ∣ j`;
* attachments: `p_a — v_{i,j}` when `D ∣ i`, `D ∣ j` and `a = (j / D) k`. -/
def baseRel (δ k : ℕ) : Vtx δ k → Vtx δ k → Prop
  | .inl a, .inl b => b.val = a.val + 1
  | .inr (i, j), .inr (i', j') =>
      (i = i' ∧ j'.val = j.val + 1) ∨ (j = j' ∧ j.val % (δ * k) = 0 ∧ i'.val = i.val + 1)
  | .inl a, .inr (i, j) =>
      i.val % (δ * k) = 0 ∧ j.val % (δ * k) = 0 ∧ a.val = j.val / (δ * k) * k
  | .inr _, .inl _ => False

instance (δ k : ℕ) : DecidableRel (baseRel δ k) := fun x y =>
  match x, y with
  | .inl _, .inl _ => inferInstanceAs (Decidable (_ = _))
  | .inr _, .inr _ => inferInstanceAs (Decidable (_ ∨ _))
  | .inl _, .inr _ => inferInstanceAs (Decidable (_ ∧ _))
  | .inr _, .inl _ => inferInstanceAs (Decidable False)

/-- The lower-bound graph of the proof of Lemma 3.2 of Ghaffari–Haeupler (PODC 2021), with
`D = δ k` (see `baseRel` for the edges). -/
def lbGraph (δ k : ℕ) : SimpleGraph (Vtx δ k) := SimpleGraph.fromRel (baseRel δ k)

/-- The graph as parametrized in the paper: `δ = δ' - 2`, `k = ⌊D' / (2δ)⌋`. -/
abbrev paperGraph (δ' D' : ℕ) : SimpleGraph (Vtx (δ' - 2) (D' / (2 * (δ' - 2)))) :=
  lbGraph (δ' - 2) (D' / (2 * (δ' - 2)))

instance (δ k : ℕ) : DecidableRel (lbGraph δ k).Adj := fun x y =>
  decidable_of_iff _ (SimpleGraph.fromRel_adj (baseRel δ k) x y).symm

/-- A 1-Lipschitz potential gives lower bounds on distances. -- CSLib candidate -/
theorem le_add_dist_of_lipschitz {V : Type*} {G : SimpleGraph V} (f : V → ℕ)
    (hf : ∀ x y, G.Adj x y → f y ≤ f x + 1) {a b : V} (h : G.Reachable a b) :
    f b ≤ f a + G.dist a b := by
  obtain ⟨w, hw⟩ := h.exists_walk_length_eq_dist
  rw [← hw]
  clear hw h
  induction w with
  | nil => simp
  | cons hadj p ih =>
    have := hf _ _ hadj
    simp only [SimpleGraph.Walk.length_cons]
    omega

/-! ### The instance `δ' = 5`, `D' = 12` -/

/-- BFS distances from `v_{3,3}` (0-indexed `(2, 2)`) in the grid part of `lbGraph 3 2`. -/
def gridPot : List (List ℕ) :=
  [[4, 5, 6, 7, 8, 7, 6, 7, 8, 9, 10, 11, 10],
   [3, 4, 5, 6, 7, 6, 5, 6, 7, 8, 9, 10, 11],
   [2, 1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10],
   [3, 4, 5, 6, 7, 6, 5, 6, 7, 8, 9, 10, 11],
   [4, 5, 6, 7, 8, 7, 6, 7, 8, 9, 10, 11, 12],
   [5, 6, 7, 8, 9, 8, 7, 8, 9, 10, 11, 12, 11],
   [6, 7, 8, 9, 10, 9, 8, 9, 10, 11, 12, 11, 10],
   [7, 8, 9, 10, 11, 10, 9, 10, 11, 12, 13, 12, 11],
   [8, 9, 10, 11, 12, 11, 10, 11, 12, 13, 14, 13, 12],
   [9, 10, 11, 12, 13, 12, 11, 12, 13, 14, 15, 14, 13],
   [8, 9, 10, 11, 12, 11, 10, 11, 12, 13, 14, 13, 12],
   [7, 8, 9, 10, 11, 10, 9, 10, 11, 12, 13, 12, 11],
   [6, 7, 8, 9, 10, 9, 8, 9, 10, 11, 12, 11, 10]]

/-- BFS distances from `v_{3,3}` in `lbGraph 3 2` (the top path has `p_a ↦ a + 5`). -/
def pot : Vtx 3 2 → ℕ
  | .inl a => a.val + 5
  | .inr (i, j) => (gridPot.getD i.val []).getD j.val 0

theorem pot_lipschitz_base (x y : Vtx 3 2) (h : baseRel 3 2 x y) :
    pot y ≤ pot x + 1 ∧ pot x ≤ pot y + 1 := by
  match x, y with
  | .inl a, .inl b =>
    simp only [baseRel, pot] at h ⊢
    omega
  | .inr (i, j), .inr (i', j') =>
    simp only [baseRel] at h
    rcases h with ⟨rfl, h⟩ | ⟨rfl, hj, h⟩
    · revert i j j'
      decide +kernel
    · revert i i' j
      decide +kernel
  | .inl a, .inr (i, j) =>
    revert a i j
    simp only [baseRel]
    decide +kernel

theorem pot_lipschitz (x y : Vtx 3 2) (h : (lbGraph 3 2).Adj x y) : pot y ≤ pot x + 1 := by
  rcases (SimpleGraph.fromRel_adj _ _ _).1 h with ⟨-, h | h⟩
  · exact (pot_lipschitz_base x y h).1
  · exact (pot_lipschitz_base y x h).2

/-- The paper's `v_{i+1,j+1}` in `lbGraph 3 2`. -/
abbrev vv (i j : Fin 13) : Vtx 3 2 := .inr (i, j)

/-- The paper's `p_{a+1}` in `lbGraph 3 2`. -/
abbrev pp (a : Fin 5) : Vtx 3 2 := .inl a

/-- A walk of length 15 from `v_{3,3}` to `v_{10,11}`: left along row 3 to column 1, up to
`v_{1,1}`, along the whole top path, down from `p_5` to `v_{7,13}`, down column 13 to
`v_{10,13}` and left along row 10. -/
def shortWalk : (lbGraph 3 2).Walk (vv 2 2) (vv 9 10) :=
  .cons (v := vv 2 1) (by decide) <| .cons (v := vv 2 0) (by decide) <|
  .cons (v := vv 1 0) (by decide) <| .cons (v := vv 0 0) (by decide) <|
  .cons (v := pp 0) (by decide) <| .cons (v := pp 1) (by decide) <|
  .cons (v := pp 2) (by decide) <| .cons (v := pp 3) (by decide) <|
  .cons (v := pp 4) (by decide) <| .cons (v := vv 6 12) (by decide) <|
  .cons (v := vv 7 12) (by decide) <| .cons (v := vv 8 12) (by decide) <|
  .cons (v := vv 9 12) (by decide) <| .cons (v := vv 9 11) (by decide) <|
  .cons (v := vv 9 10) (by decide) .nil

theorem shortWalk_length : shortWalk.length = 15 := rfl

/-- In the lower-bound graph of Lemma 3.2 for `δ = 3`, `k = 2` (i.e. `δ' = 5`, `D' = 12`),
the nodes `v_{3,3}` and `v_{10,11}` are at distance exactly `15`. -/
theorem lbGraph_dist_eq : (lbGraph 3 2).dist (vv 2 2) (vv 9 10) = 15 := by
  apply le_antisymm
  · exact shortWalk_length ▸ SimpleGraph.dist_le shortWalk
  · have := le_add_dist_of_lipschitz pot pot_lipschitz ⟨shortWalk⟩
    simpa [pot, gridPot] using this

/-- **Counterexample to the diameter claim in the proof of Lemma 3.2** (Ghaffari–Haeupler,
PODC 2021): for `δ' = 5`, `D' = 12` the construction (with `δ = δ' - 2 = 3`,
`k = ⌊D'/(2δ)⌋ = 2`) has two nodes, `v_{3,3}` and `v_{10,11}`, at distance `15 > D'`. -/
theorem paperGraph_dist_eq :
    (paperGraph 5 12).dist (.inr (2, 2)) (.inr (9, 10)) = 15 :=
  lbGraph_dist_eq

/-- **Counterexample to the diameter claim in the proof of Lemma 3.2** (Ghaffari–Haeupler,
PODC 2021): for `δ' = 5`, `D' = 12` the construction does not have diameter `≤ D'`. (This
refutes only the claim inside the proof, not the existential statement of Lemma 3.2.) -/
theorem paperGraph_not_diam_le : ¬ ∀ u v, (paperGraph 5 12).dist u v ≤ 12 := fun h => by
  have := h (.inr (2, 2)) (.inr (9, 10))
  rw [paperGraph_dist_eq] at this
  omega

end LowCongestionShortcuts.LowerBound
