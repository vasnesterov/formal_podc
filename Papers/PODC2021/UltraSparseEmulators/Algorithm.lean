import Papers.PODC2021.UltraSparseEmulators.Stretch

/-!
# Algorithm 1 (Section 2.1) and the invariants of one phase

Elkin, Matar. *Ultra-Sparse Near-Additive Emulators.* PODC 2021 (arXiv:2106.01036v1).

## Representation

A phase `i` works only with the set `C` of *centers* of the clusters of `P_i` (the clusters
themselves are reconstructed in `Hierarchy.lean`). The state of a phase records, for every vertex
`x`, a tag `stat x`:

* `S` — `x ∈ S_i` (not yet considered); `N` — `x ∈ N_i` (buffer);
* `U` — `x` was considered and found unpopular (its cluster joined `U_i`);
* `T` — `x` was considered and found popular: a supercluster was formed around it (`x ∈ P_{i+1}`);
* `J` — the cluster of `x` joined a supercluster (`x ∈ Γ(r)` for a popular `r`, or it was left in
  `N_i` at the end of the phase);
* `out` — `x` is not a center of `P_i`;

together with `par x`, the center of the supercluster that `x` joined (or, for `x ∈ N_i`, the one
"that was formed when `x` joined `N_i`", line 23), and the emulator edges `E` built so far.

**Order of consideration.** The paper removes "a cluster center" from `S_i` in an arbitrary order
(line 6). We consider the vertices in the order of an arbitrary list `L` containing all centers,
skipping those no longer in `S_i`. Every execution of the while loop is of this form (extend the
sequence of considered centers by the remaining ones), and conversely, so quantifying over all
lists is quantifying over all executions of Algorithm 1.

**Line 18** reads `d_G(r_C, r_{C'}) ≤ 2δ_i`; the bound variable is `r_{C''}` (typo; the text of
Section 2.1.1 says `δ_i < d_G(r_C, r_{C''}) ≤ 2δ_i`, which is the same set after lines 14–15).
-/

namespace Podc.UltraSparseEmulators

open SimpleGraph Finset
open scoped Classical

variable {V : Type*} [Fintype V] (G : SimpleGraph V)

/-- `x` and `y` are at distance at most `t` in `G` (and connected). -/
def Near (t : ℝ) (x y : V) : Prop := G.Reachable x y ∧ (G.dist x y : ℝ) ≤ t

variable {G}

omit [Fintype V] in
lemma Near.symm {t : ℝ} {x y : V} (h : Near G t x y) : Near G t y x :=
  ⟨h.1.symm, by rw [dist_comm]; exact h.2⟩

omit [Fintype V] in
lemma Near.trans {t t' : ℝ} {x y z : V} (h : Near G t x y) (h' : Near G t' y z) :
    Near G (t + t') x z := by
  refine ⟨h.1.trans h'.1, ?_⟩
  have h3 : (G.dist x z : ℝ) ≤ G.dist x y + G.dist y z := by
    exact_mod_cast h.1.dist_triangle_left z
  linarith [h.2, h'.2]

/-- The status of a vertex during a phase (see the module docstring). -/
inductive Tag
  | S | N | U | T | J | out
  deriving DecidableEq

/-- The state of a phase. -/
structure St (V : Type*) where
  /-- The status of every vertex. -/
  stat : V → Tag
  /-- The supercluster center a vertex joined (or will join, for `N`). -/
  par : V → V
  /-- The emulator edges built so far (each of weight `d_G` of its endpoints). -/
  E : Finset (Sym2 V)

variable (G)

/-- The number of vertices with status `t`. -/
noncomputable def St.cnt (s : St V) (t : Tag) : ℕ := (univ.filter fun x => s.stat x = t).card

/-- `Γ(r)`: the centers in `S_i ∪ N_i` discovered by the exploration from `r` to depth `δ`
(`r` itself excluded). -/
noncomputable def gam (δ : ℝ) (s : St V) (r : V) : Finset V :=
  univ.filter fun x => x ≠ r ∧ (s.stat x = .S ∨ s.stat x = .N) ∧ Near G δ r x

/-- Lines 6–21 of Algorithm 1: consider the center `r` (skipped if it is no longer in `S_i`).
Edges to all of `Γ(r)` are added; if `|Γ(r)| < deg`, `r` becomes unclustered (`U`); otherwise a
supercluster is formed around `r` (`T`), `Γ(r)` joins it (`J`), and the remaining centers of `S_i`
within `2δ` of `r` move to `N_i` (`N`). -/
noncomputable def step (δ d : ℝ) (s : St V) (r : V) : St V :=
  if s.stat r = .S then
    if ((gam G δ s r).card : ℝ) < d then
      ⟨Function.update s.stat r .U, s.par, s.E ∪ (gam G δ s r).image fun x => s(r, x)⟩
    else
      ⟨fun x => if x = r then .T else if x ∈ gam G δ s r then .J
          else if s.stat x = .S ∧ Near G (2 * δ) r x then .N else s.stat x,
       fun x => if x = r ∨ x ∈ gam G δ s r ∨ (s.stat x = .S ∧ Near G (2 * δ) r x) then r
          else s.par x,
       s.E ∪ (gam G δ s r).image fun x => s(r, x)⟩
  else s

/-- The initial state of a phase with centers `C` and emulator edges `E` (lines 3–4). -/
noncomputable def init (C : Finset V) (E : Finset (Sym2 V)) : St V :=
  ⟨fun x => if x ∈ C then .S else .out, id, E⟩

/-- Lines 22–26: the centers left in `N_i` join their superclusters. -/
noncomputable def finish (s : St V) : St V :=
  ⟨fun x => if s.stat x = .N then .J else s.stat x, s.par,
   s.E ∪ (univ.filter fun x => s.stat x = .N).image fun x => s(s.par x, x)⟩

/-- One phase of Algorithm 1 with threshold `δ`, degree `d`, centers `C`, current emulator
edges `E`, considering the centers in the order of `L`. -/
noncomputable def phase (δ d : ℝ) (C : Finset V) (E : Finset (Sym2 V)) (L : List V) : St V :=
  finish (L.foldl (step G δ d) (init C E))

/-- **Algorithm 1.** `run G δ deg ord i` is the state at the end of phase `i`, for thresholds
`δ i`, degrees `deg i` and orders `ord i`. The centers of phase `i + 1` are the vertices tagged
`T` in phase `i`. -/
noncomputable def run (δ dg : ℕ → ℝ) (ord : ℕ → List V) : ℕ → St V
  | 0 => phase G (δ 0) (dg 0) univ ∅ (ord 0)
  | i + 1 => phase G (δ (i + 1)) (dg (i + 1))
      (univ.filter fun x => (run δ dg ord i).stat x = .T) (run δ dg ord i).E (ord (i + 1))

/-- The centers of the clusters of `P_i`. -/
noncomputable def centers (δ dg : ℕ → ℝ) (ord : ℕ → List V) : ℕ → Finset V
  | 0 => univ
  | i + 1 => univ.filter fun x => (run G δ dg ord i).stat x = .T

/-- The emulator edges at the beginning of phase `i`. -/
noncomputable def edgesBefore (δ dg : ℕ → ℝ) (ord : ℕ → List V) : ℕ → Finset (Sym2 V)
  | 0 => ∅
  | i + 1 => (run G δ dg ord i).E

lemma run_eq (δ dg : ℕ → ℝ) (ord : ℕ → List V) (i : ℕ) :
    run G δ dg ord i = phase G (δ i) (dg i) (centers G δ dg ord i) (edgesBefore G δ dg ord i)
      (ord i) := by
  cases i <;> rfl

/-- The emulator produced by phases `0, …, ℓ`; its edges are weighted by `distW G`. -/
noncomputable def emulator (δ dg : ℕ → ℝ) (ord : ℕ → List V) (ℓ : ℕ) : SimpleGraph V :=
  SimpleGraph.fromEdgeSet ((run G δ dg ord ℓ).E : Set (Sym2 V))

end Podc.UltraSparseEmulators
