import Mathlib.Combinatorics.SimpleGraph.Diam
import Mathlib.Basic.Real.Basic
import Cslib.Computability.Distributed.Congest.Gather
import Cslib.Computability.Distributed.Congest.Randomized
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-!
# Distinguishing diameter 2 from 3 takes `Ω(n/B)` rounds (Section 7.1 and Section 8 of [HW12])

[HW12] S. Holzer, R. Wattenhofer, *Optimal Distributed All Pairs Shortest Paths and Applications*,
PODC 2012.

## The lower-bound graphs `G_{a,b}` (proof of Theorem 8)

For `k ≥ 1` and inputs `a b : Fin k × Fin k → Bool` (the `k²` bits of `disj_{k²}`):

* Alice's side: `l_ν` (`ν < 2k`; the *upper* half `ν < k` is `Vtx.l false i`, the *lower* half
  `l_{k+j}` is `Vtx.l true j`) and `c_L`. Edges: `c_L – l_ν` for all `ν`; a clique on each half;
  `l_i – l_{k+j}` iff `a(i, j) = 0`.
* Bob's side: the same with `r_ν`, `c_R` and `b`, plus `f` fill-up nodes `w_j` adjacent to all of
  `R ∪ {c_R}`.
* Cut (`2k + 1` edges): `l_ν – r_ν` for all `ν`, and `c_L – c_R`.

The paper's bit `a(i)`, `i < k²`, is the pair `(i mod k, ⌊i/k⌋)` (edge `l_{i mod k} – l_{k+⌊i/k⌋}`);
we index the bits by `Fin k × Fin k` directly.

## Main results

* `Diam23.card_vtx` + `Diam23.shape` : Lemma 15 and Theorem 9 (all distances `≤ 3`; diameter `2`
  iff `a`, `b` are disjoint, else `3`), packaged as the abstract distance profile `Diam23.Shape`;
  `Diam23.Shape.radius_eq_two`, `Shape.center_eq_univ_iff`, … : the facts used in Lemmas 10, 11.
* `Diam23.lowerBound` : the reduction (any algorithm whose acceptance on the profile is "diameter
  `= 2`" needs `k² ≤ T · 2 · (2k+1) · B + 2`, `k = ⌊(n-2)/4⌋`), via CSLib's
  `LBFamily.disj_lowerBound` (`CC(DISJ_K) ≥ K`, proved).
* `theorem8`, `theorem8_accepts` : Theorem 8 (deterministic); `n_le_of_bound` turns the bound into
  `n ≤ 16 T B + 13`.
* `lemma10_apsp`, `lemma10_eccentricity`, `lemma10_peripheral`, `lemma11_center`, `lemma16`,
  `theorem11` : the exact parts of Lemmas 10 and 11, Lemma 16 and Theorem 11 (each node runs a local
  test on its own output; "all nodes accept" iff the inputs are disjoint, so no aggregation step is
  needed).
* `theorem8_randomized` : Theorem 8 for `ε`-error randomized algorithms, conditional on the
  randomized `CC(DISJ)` bound `Diam23.RandDisjLB ε κ` (not formalized in CSLib).
* `theorem8_nonvacuous`, … : CSLib's full-information gathering algorithm satisfies the hypotheses
  (with `T = n` and `n + n²`-bit messages).

Model: synchronous deterministic (resp. private-coin randomized) CONGEST with `B`-bit messages, node
IDs = vertex names, each node knows its incident edges; no failures.
-/

namespace Podc.OptimalAPSP

open SimpleGraph Cslib.Congest Cslib.CommunicationComplexity Cslib.CommunicationComplexity.Protocol

namespace Diam23

/-! ### Generic graph facts -/

section Generic

variable {V W : Type*}

-- CSLib candidate
/-- Graph homomorphisms do not increase extended distances. -/
lemma edist_hom_le {G : SimpleGraph V} {G' : SimpleGraph W} (φ : G →g G') (u v : V) :
    G'.edist (φ u) (φ v) ≤ G.edist u v := by
  by_cases hr : G.Reachable u v
  · obtain ⟨p, hp⟩ := hr.exists_walk_length_eq_edist
    rw [← hp, ← Walk.length_map φ]
    exact edist_le _
  · rw [edist_eq_top_of_not_reachable hr]
    exact le_top

-- CSLib candidate
/-- Relabelling a graph along an equivalence preserves extended distances. -/
lemma edist_comap_equiv (G : SimpleGraph W) (e : V ≃ W) (u v : V) :
    (G.comap e).edist u v = G.edist (e u) (e v) := by
  apply le_antisymm
  · have h := edist_hom_le (Iso.comap e G).symm.toHom (e u) (e v)
    simpa using h
  · exact edist_hom_le (Iso.comap e G).toHom u v

lemma edist_le_two_of_adj {G : SimpleGraph V} {u z v : V} (h1 : G.Adj u z) (h2 : G.Adj z v) :
    G.edist u v ≤ 2 :=
  (edist_le (Walk.cons h1 (Walk.cons h2 Walk.nil))).trans (by simp)

lemma two_le_edist {G : SimpleGraph V} {u v : V} (hne : u ≠ v) (hn : ¬ G.Adj u v) :
    2 ≤ G.edist u v := by
  have h1 : ¬ G.edist u v ≤ 1 := by
    rw [edist_le_one_iff_adj_or_eq]
    tauto
  have h2 : (1 : ℕ∞) < G.edist u v := not_le.1 h1
  exact Order.add_one_le_of_lt h2

end Generic


/-! ### The vertex set -/

/-- Vertices of the lower-bound graph `G_{a,b}`: `l h i` is `l_i` (`h = false`, upper half) or
`l_{k+i}` (`h = true`, lower half); `r h i` likewise; `cL`, `cR`; fill-up nodes `w j`. -/
inductive Vtx (k f : ℕ)
  | l (h : Bool) (i : Fin k)
  | r (h : Bool) (i : Fin k)
  | cL
  | cR
  | w (j : Fin f)
  deriving DecidableEq

namespace Vtx

variable {k f : ℕ}

/-- `Vtx k f` as a sum type. -/
def equivSum : Vtx k f ≃ (Bool × Fin k) ⊕ (Bool × Fin k) ⊕ Bool ⊕ Fin f where
  toFun
    | l h i => .inl (h, i)
    | r h i => .inr (.inl (h, i))
    | cL => .inr (.inr (.inl false))
    | cR => .inr (.inr (.inl true))
    | w j => .inr (.inr (.inr j))
  invFun
    | .inl (h, i) => l h i
    | .inr (.inl (h, i)) => r h i
    | .inr (.inr (.inl false)) => cL
    | .inr (.inr (.inl true)) => cR
    | .inr (.inr (.inr j)) => w j
  left_inv v := by cases v <;> rfl
  right_inv := by
    rintro (⟨h, i⟩ | ⟨h, i⟩ | b | j)
    · rfl
    · rfl
    · cases b <;> rfl
    · rfl

instance : Fintype (Vtx k f) := Fintype.ofEquiv _ equivSum.symm

/-- Alice's vertices: `L ∪ {c_L}`. -/
def isAlice : Vtx k f → Bool
  | l _ _ => true
  | cL => true
  | _ => false

end Vtx

open Vtx

variable {k f : ℕ}

/-- Lemma 15 (node count): `G_{a,b}` has `4k + 2 + f` nodes. -/
lemma card_vtx : Fintype.card (Vtx k f) = 4 * k + 2 + f := by
  rw [Fintype.card_congr Vtx.equivSum]
  simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_bool, Fintype.card_fin]
  ring

/-! ### The graph -/

/-- The (directed) edge relation of `G_{a,b}`; the graph is its symmetrisation. -/
def Rel (a b : Fin k → Fin k → Bool) : Vtx k f → Vtx k f → Prop
  | cL, l _ _ => True
  | cL, cR => True
  | cR, r _ _ => True
  | w _, r _ _ => True
  | w _, cR => True
  | l h i, r h' i' => h = h' ∧ i = i'
  | l h i, l h' i' => (h = h' ∧ i ≠ i') ∨ (h = false ∧ h' = true ∧ a i i' = false)
  | r h i, r h' i' => (h = h' ∧ i ≠ i') ∨ (h = false ∧ h' = true ∧ b i i' = false)
  | _, _ => False

/-- The lower-bound graph `G_{a,b}` of the proof of Theorem 8 of [HW12] (`f` fill-up nodes). -/
def graph (a b : Fin k → Fin k → Bool) : SimpleGraph (Vtx k f) := SimpleGraph.fromRel (Rel a b)

variable {a b : Fin k → Fin k → Bool}

lemma adj_iff {u v : Vtx k f} :
    (graph a b).Adj u v ↔ u ≠ v ∧ (Rel a b u v ∨ Rel a b v u) := fromRel_adj _ _ _

/-- Every Alice vertex is `c_L` or adjacent to it. -/
lemma edist_cL_le (u : Vtx k f) (hu : u.isAlice = true) : (graph a b).edist u cL ≤ 1 := by
  rw [edist_le_one_iff_adj_or_eq]
  cases u <;> simp_all [adj_iff, Rel, isAlice]

/-- Every Bob vertex is `c_R` or adjacent to it. -/
lemma edist_cR_le (u : Vtx k f) (hu : u.isAlice = false) : (graph a b).edist u cR ≤ 1 := by
  rw [edist_le_one_iff_adj_or_eq]
  cases u <;> simp_all [adj_iff, Rel, isAlice]

lemma adj_cL_cR : (graph a b (f := f)).Adj cL cR := by simp [adj_iff, Rel]

/-- Lemma 15 (distance part): all distances in `G_{a,b}` are at most `3`. -/
lemma edist_le_three (u v : Vtx k f) : (graph a b).edist u v ≤ 3 := by
  have hc : (graph a b (f := f)).edist cL cR ≤ 1 := (edist_eq_one_iff_adj.2 adj_cL_cR).le
  cases hu : u.isAlice <;> cases hv : v.isAlice
  · calc (graph a b).edist u v ≤ (graph a b).edist u cR + (graph a b).edist cR v :=
          SimpleGraph.edist_triangle
      _ ≤ 1 + 1 := by
          gcongr
          · exact edist_cR_le u hu
          · rw [edist_comm]; exact edist_cR_le v hv
      _ ≤ 3 := by norm_num
  · calc (graph a b).edist u v
        ≤ (graph a b).edist u cR + ((graph a b).edist cR cL + (graph a b).edist cL v) :=
          SimpleGraph.edist_triangle.trans (by gcongr; exact SimpleGraph.edist_triangle)
      _ ≤ 1 + (1 + 1) := by
          gcongr
          · exact edist_cR_le u hu
          · rw [edist_comm]; exact hc
          · rw [edist_comm]; exact edist_cL_le v hv
      _ = 3 := by norm_num
  · calc (graph a b).edist u v
        ≤ (graph a b).edist u cL + ((graph a b).edist cL cR + (graph a b).edist cR v) :=
          SimpleGraph.edist_triangle.trans (by gcongr; exact SimpleGraph.edist_triangle)
      _ ≤ 1 + (1 + 1) := by
          gcongr
          · exact edist_cL_le u hu
          · rw [edist_comm]; exact edist_cR_le v hv
      _ = 3 := by norm_num
  · calc (graph a b).edist u v ≤ (graph a b).edist u cL + (graph a b).edist cL v :=
          SimpleGraph.edist_triangle
      _ ≤ 1 + 1 := by
          gcongr
          · exact edist_cL_le u hu
          · rw [edist_comm]; exact edist_cL_le v hv
      _ ≤ 3 := by norm_num

lemma edist_le_one_of_adj {u v : Vtx k f} (h : (graph a b).Adj u v) : (graph a b).edist u v ≤ 1 :=
  (edist_eq_one_iff_adj.2 h).le

/-- Theorem 9, case 3: if `a` and `b` are disjoint, every Alice vertex is within distance `2` of every
Bob vertex. -/
lemma edist_le_two_of_disjoint (hd : ∀ i j, ¬ (a i j = true ∧ b i j = true)) (u v : Vtx k f)
    (hu : u.isAlice = true) (hv : v.isAlice = false) : (graph a b).edist u v ≤ 2 := by
  rcases u with ⟨h, i⟩ | ⟨h, i⟩ | _ | _ | m <;> simp [isAlice] at hu <;>
    rcases v with ⟨h', j⟩ | ⟨h', j⟩ | _ | _ | m' <;> simp [isAlice] at hv
  · -- `l h i`, `r h' j`
    by_cases hh : h = h'
    · subst hh
      by_cases hij : i = j
      · subst hij
        exact (edist_le_one_of_adj (by simp [adj_iff, Rel])).trans (by norm_num)
      · exact edist_le_two_of_adj (z := l h j) (by simp [adj_iff, Rel, hij])
          (by simp [adj_iff, Rel])
    · cases h <;> cases h'
      · exact absurd rfl hh
      · by_cases ha : a i j = false
        · exact edist_le_two_of_adj (z := l true j) (by simp [adj_iff, Rel, ha])
            (by simp [adj_iff, Rel])
        · have hb : b i j = false := by
            have := hd i j; cases ha' : a i j <;> cases hb' : b i j <;> simp_all
          exact edist_le_two_of_adj (z := r false i) (by simp [adj_iff, Rel])
            (by simp [adj_iff, Rel, hb])
      · by_cases ha : a j i = false
        · exact edist_le_two_of_adj (z := l false j) (by simp [adj_iff, Rel, ha])
            (by simp [adj_iff, Rel])
        · have hb : b j i = false := by
            have := hd j i; cases ha' : a j i <;> cases hb' : b j i <;> simp_all
          exact edist_le_two_of_adj (z := r true i) (by simp [adj_iff, Rel])
            (by simp [adj_iff, Rel, hb])
      · exact absurd rfl hh
  · exact edist_le_two_of_adj (z := cL) (by simp [adj_iff, Rel]) (by simp [adj_iff, Rel])
  · exact edist_le_two_of_adj (z := r h i) (by simp [adj_iff, Rel]) (by simp [adj_iff, Rel])
  · exact edist_le_two_of_adj (z := l h' j) (by simp [adj_iff, Rel]) (by simp [adj_iff, Rel])
  · exact (edist_le_one_of_adj adj_cL_cR).trans (by norm_num)
  · exact edist_le_two_of_adj (z := cR) (by simp [adj_iff, Rel]) (by simp [adj_iff, Rel])

/-- Theorem 9 (disjoint case): if `a` and `b` are disjoint, all distances are at most `2`. -/
lemma edist_le_two (hd : ∀ i j, ¬ (a i j = true ∧ b i j = true)) (u v : Vtx k f) :
    (graph a b).edist u v ≤ 2 := by
  cases hu : u.isAlice <;> cases hv : v.isAlice
  · calc (graph a b).edist u v ≤ (graph a b).edist u cR + (graph a b).edist cR v :=
          SimpleGraph.edist_triangle
      _ ≤ 1 + 1 := by
          gcongr
          · exact edist_cR_le u hu
          · rw [edist_comm]; exact edist_cR_le v hv
      _ = 2 := by norm_num
  · rw [edist_comm]; exact edist_le_two_of_disjoint hd v u hv hu
  · exact edist_le_two_of_disjoint hd u v hu hv
  · calc (graph a b).edist u v ≤ (graph a b).edist u cL + (graph a b).edist cL v :=
          SimpleGraph.edist_triangle
      _ ≤ 1 + 1 := by
          gcongr
          · exact edist_cL_le u hu
          · rw [edist_comm]; exact edist_cL_le v hv
      _ = 2 := by norm_num

/-- Theorem 9 (intersecting case): if `a(i, j) = b(i, j) = 1`, then `d(l_i, r_{k+j}) ≥ 3`. -/
lemma two_lt_edist {i j : Fin k} (ha : a i j = true) (hb : b i j = true) :
    2 < (graph a b (f := f)).edist (l false i) (r true j) := by
  rw [two_lt_edist_iff]
  refine ⟨by simp, by simp [adj_iff, Rel], ?_⟩
  ext z
  simp only [commonNeighbors, Set.mem_inter_iff, mem_neighborSet, Set.mem_empty_iff_false,
    iff_false, not_and]
  intro h1 h2
  rcases z with ⟨h, i'⟩ | ⟨h, i'⟩ | _ | _ | m <;> simp [adj_iff, Rel] at h1 h2
  · obtain ⟨rfl, rfl⟩ := h2
    simp_all
  · obtain ⟨rfl, rfl⟩ := h1
    simp_all

/-- `c_L` has eccentricity at most `2`. -/
lemma edist_cL_le_two (v : Vtx k f) : (graph a b).edist cL v ≤ 2 := by
  cases hv : v.isAlice
  · calc (graph a b).edist cL v ≤ (graph a b).edist cL cR + (graph a b).edist cR v :=
          SimpleGraph.edist_triangle
      _ ≤ 1 + 1 := by
          gcongr
          · exact edist_le_one_of_adj adj_cL_cR
          · rw [edist_comm]; exact edist_cR_le v hv
      _ = 2 := by norm_num
  · rw [edist_comm]; exact (edist_cL_le v hv).trans (by norm_num)

/-- No vertex is adjacent to all others (for `k ≥ 1`). -/
lemma exists_two_le_edist (i₀ : Fin k) (u : Vtx k f) : ∃ v, 2 ≤ (graph a b).edist u v := by
  rcases u with ⟨h, i⟩ | ⟨h, i⟩ | _ | _ | m
  · exact ⟨cR, two_le_edist (by simp) (by simp [adj_iff, Rel])⟩
  · exact ⟨cL, two_le_edist (by simp) (by simp [adj_iff, Rel])⟩
  · exact ⟨r false i₀, two_le_edist (by simp) (by simp [adj_iff, Rel])⟩
  · exact ⟨l false i₀, two_le_edist (by simp) (by simp [adj_iff, Rel])⟩
  · exact ⟨cL, two_le_edist (by simp) (by simp [adj_iff, Rel])⟩


/-! ### The distance profile of the lower-bound graphs -/

/-- The distance profile of the lower-bound graphs of Theorem 8, with `d` = "the inputs are
disjoint": all distances are `≤ 3` (Lemma 15), all are `≤ 2` if `d` holds and some is `≥ 3`
otherwise (Theorem 9), some vertex (`c_L`) has eccentricity `≤ 2`, and no vertex is adjacent to all
others. Every consequence used in Lemmas 10, 11, 16 and Theorem 11 follows from these facts. -/
structure Shape {V : Type*} (G : SimpleGraph V) (d : Prop) : Prop where
  le_three : ∀ u v, G.edist u v ≤ 3
  le_two : d → ∀ u v, G.edist u v ≤ 2
  gt_two : ¬ d → ∃ u v, 2 < G.edist u v
  hub : ∃ c, ∀ v, G.edist c v ≤ 2
  far : ∀ u, ∃ v, 2 ≤ G.edist u v

namespace Shape

variable {V : Type*} {G : SimpleGraph V} {d : Prop}

lemma nonempty (h : Shape G d) : Nonempty V := ⟨h.hub.choose⟩

lemma ediam_le_three (h : Shape G d) : G.ediam ≤ 3 := ediam_le_of_edist_le h.le_three

lemma connected (h : Shape G d) : G.Connected :=
  have := h.nonempty
  connected_of_ediam_ne_top (ne_top_of_le_ne_top (by decide) h.ediam_le_three)

lemma two_le_eccent (h : Shape G d) (u : V) : 2 ≤ G.eccent u :=
  let ⟨_, hv⟩ := h.far u
  hv.trans edist_le_eccent

lemma ediam_eq_two (h : Shape G d) (hd : d) : G.ediam = 2 :=
  le_antisymm (ediam_le_of_edist_le (h.le_two hd))
    ((h.two_le_eccent h.hub.choose).trans eccent_le_ediam)

lemma ediam_eq_three (h : Shape G d) (hd : ¬ d) : G.ediam = 3 := by
  refine le_antisymm h.ediam_le_three ?_
  obtain ⟨u, v, huv⟩ := h.gt_two hd
  exact (Order.add_one_le_of_lt huv).trans edist_le_ediam

/-- Theorem 9 (disjoint case): the diameter is `2`. -/
lemma diam_eq_two (h : Shape G d) (hd : d) : G.diam = 2 := by
  simp [diam, h.ediam_eq_two hd]

/-- Theorem 9 (intersecting case): the diameter is `3`. -/
lemma diam_eq_three (h : Shape G d) (hd : ¬ d) : G.diam = 3 := by
  simp only [diam, h.ediam_eq_three hd]
  rfl

lemma diam_eq_two_iff (h : Shape G d) : G.diam = 2 ↔ d := by
  by_cases hd : d
  · simp [hd, h.diam_eq_two hd]
  · simp [hd, h.diam_eq_three hd]

lemma diam_two_or_three (h : Shape G d) : G.diam = 2 ∨ G.diam = 3 := by
  by_cases hd : d
  · exact Or.inl (h.diam_eq_two hd)
  · exact Or.inr (h.diam_eq_three hd)

/-- The radius is always `2` (witnessed by `c_L`), as claimed in the proof of Lemma 11. -/
lemma radius_eq_two (h : Shape G d) : G.radius = 2 := by
  obtain ⟨c, hc⟩ := h.hub
  refine le_antisymm (radius_le_eccent.trans ((eccent_le_iff _ _).2 hc)) ?_
  exact le_iInf h.two_le_eccent

lemma coe_dist (h : Shape G d) (u v : V) : (G.dist u v : ℕ∞) = G.edist u v :=
  (h.connected u v).coe_dist_eq_edist

/-- All pairwise distances are `≤ 2` iff `d` (APSP, 2-BFS trees). -/
lemma dist_le_two_iff (h : Shape G d) : (∀ u v, G.dist u v ≤ 2) ↔ d := by
  constructor
  · intro hall
    by_contra hd
    obtain ⟨u, v, huv⟩ := h.gt_two hd
    have := hall u v
    rw [← h.coe_dist] at huv
    exact absurd (by exact_mod_cast huv) (not_lt.2 this)
  · intro hd u v
    have := h.le_two hd u v
    rw [← h.coe_dist] at this
    exact_mod_cast this

/-- All eccentricities are `≤ 2` iff `d`. -/
lemma eccent_le_two_iff (h : Shape G d) : (∀ u, G.eccent u ≤ 2) ↔ d := by
  constructor
  · intro hall
    by_contra hd
    obtain ⟨u, v, huv⟩ := h.gt_two hd
    exact absurd ((edist_le_eccent).trans (hall u)) (not_le.2 huv)
  · intro hd u
    exact (eccent_le_iff _ _).2 (h.le_two hd u)

/-- Every vertex is peripheral (`ecc v = diam`) iff `d` (Lemma 10, peripheral vertices). -/
lemma peripheral_iff (h : Shape G d) : (∀ u, G.eccent u = G.ediam) ↔ d := by
  constructor
  · intro hall
    by_contra hd
    obtain ⟨c, hc⟩ := h.hub
    have h1 := hall c
    rw [h.ediam_eq_three hd] at h1
    have h2 := (eccent_le_iff _ _).2 hc
    rw [h1] at h2
    exact absurd h2 (by decide)
  · intro hd u
    rw [h.ediam_eq_two hd]
    exact le_antisymm ((eccent_le_iff _ _).2 (h.le_two hd u)) (h.two_le_eccent u)

/-- The center is the whole vertex set iff `d` (Lemma 11). -/
lemma center_eq_univ_iff (h : Shape G d) : G.center = Set.univ ↔ d := by
  have := h.nonempty
  rw [center_eq_univ_iff_radius_eq_ediam, h.radius_eq_two]
  by_cases hd : d
  · simp [hd, h.ediam_eq_two hd]
  · simp only [hd, iff_false, h.ediam_eq_three hd]
    decide

end Shape


/-- Relabelling along an equivalence preserves the distance profile. -/
lemma Shape.comap {V W : Type*} {G : SimpleGraph W} {d : Prop} (h : Shape G d) (e : V ≃ W) :
    Shape (G.comap e) d where
  le_three u v := by rw [edist_comap_equiv]; exact h.le_three _ _
  le_two hd u v := by rw [edist_comap_equiv]; exact h.le_two hd _ _
  gt_two hd := by
    obtain ⟨u, v, huv⟩ := h.gt_two hd
    exact ⟨e.symm u, e.symm v, by simpa [edist_comap_equiv] using huv⟩
  hub := by
    obtain ⟨c, hc⟩ := h.hub
    exact ⟨e.symm c, fun v => by rw [edist_comap_equiv]; simpa using hc (e v)⟩
  far u := by
    obtain ⟨v, hv⟩ := h.far (e u)
    exact ⟨e.symm v, by simpa [edist_comap_equiv] using hv⟩

/-- **Lemma 15 and Theorem 9 of [HW12]** (for `k ≥ 1`): `G_{a,b}` has the distance profile `Shape`
with `d` = "`a` and `b` are disjoint": all distances `≤ 3`, diameter `2` if disjoint and `3`
otherwise (witnessed by `d(l_i, r_{k+j}) = 3` for a common element `(i, j)`), `ecc(c_L) = 2`, and no
vertex is adjacent to all others. -/
theorem shape (hk : 1 ≤ k) :
    Shape (graph a b (f := f)) (∀ i j, ¬ (a i j = true ∧ b i j = true)) where
  le_three := edist_le_three
  le_two hd := edist_le_two hd
  gt_two hd := by
    push Not at hd
    obtain ⟨i, j, ha, hb⟩ := hd
    exact ⟨_, _, two_lt_edist ha hb⟩
  hub := ⟨cL, edist_cL_le_two⟩
  far := exists_two_le_edist ⟨0, hk⟩

/-! ### Independence properties of the family -/

lemma adj_cut_cases {u v : Vtx k f} (huv : (graph a b).Adj u v) (hu : u.isAlice = true)
    (hv : v.isAlice = false) : (∃ h i, u = l h i ∧ v = r h i) ∨ (u = cL ∧ v = cR) := by
  cases u <;> cases v <;> simp_all [adj_iff, Rel, isAlice]

lemma adj_alice_indep (b' : Fin k → Fin k → Bool) {u v : Vtx k f} (hu : u.isAlice = true)
    (hv : v.isAlice = true) : (graph a b).Adj u v ↔ (graph a b').Adj u v := by
  cases u <;> cases v <;> simp_all [adj_iff, Rel, isAlice]

lemma adj_bob_indep (a' : Fin k → Fin k → Bool) {u v : Vtx k f} (hu : u.isAlice = false)
    (hv : v.isAlice = false) : (graph a b).Adj u v ↔ (graph a' b).Adj u v := by
  cases u <;> cases v <;> simp_all [adj_iff, Rel, isAlice]

lemma adj_cut_indep (a' b' : Fin k → Fin k → Bool) {u v : Vtx k f} (hu : u.isAlice = true)
    (hv : v.isAlice = false) : (graph a b).Adj u v ↔ (graph a' b').Adj u v := by
  cases u <;> cases v <;> simp_all [adj_iff, Rel, isAlice]

/-! ### The family of lower-bound graphs on an arbitrary vertex set -/

/-- The input bits `x : Fin k × Fin k → Bool` as a matrix: `mat x i j = x(i, j)` is the paper's bit
`x(i + k·j)`. -/
def mat (x : Fin k × Fin k → Bool) : Fin k → Fin k → Bool := fun i j => x (i, j)

lemma disj_eq_true_iff {x y : Fin k × Fin k → Bool} :
    disj x y = true ↔ ∀ i j, ¬ (mat x i j = true ∧ mat y i j = true) := by
  simp [disj, mat, Prod.forall]

variable {V : Type*}

/-- The cut edges `(l_ν, r_ν)` and `(c_L, c_R)`, relabelled to `V`. -/
noncomputable def cutEdges (e : V ≃ Vtx k f) : Finset (V × V) := by
  classical
  exact (Finset.univ.image fun p : Bool × Fin k => (e.symm (l p.1 p.2), e.symm (r p.1 p.2))) ∪
    {(e.symm cL, e.symm cR)}

/-- The cut has (at most) `2k + 1` edges. -/
lemma card_cutEdges (e : V ≃ Vtx k f) : (cutEdges e).card ≤ 2 * k + 1 := by
  classical
  unfold cutEdges
  refine (Finset.card_union_le _ _).trans ?_
  have := Finset.card_image_le (s := (Finset.univ : Finset (Bool × Fin k)))
    (f := fun p : Bool × Fin k => (e.symm (l p.1 p.2), e.symm (r p.1 p.2)))
  simp only [Finset.card_univ, Fintype.card_prod, Fintype.card_bool, Fintype.card_fin] at this
  simpa using this

/-- The lower-bound graph `G_{x,y}`, relabelled to `V` along `e`. -/
def famGraph (e : V ≃ Vtx k f) (x y : Fin k × Fin k → Bool) : SimpleGraph V :=
  (graph (mat x) (mat y)).comap e

open Classical in
/-- The family of lower-bound graphs of Theorem 8 (Definition 1.1 of the CSLib framework): Alice
owns `L ∪ {c_L}`, Bob owns `R ∪ {c_R} ∪ W`, node inputs are the adjacency rows. -/
noncomputable def family (e : V ≃ Vtx k f) :
    LBFamily (Fin k × Fin k → Bool) (Fin k × Fin k → Bool) V (V → Bool) :=
  LBFamily.ofAdj (famGraph e) (fun v => (e v).isAlice) (cutEdges e)
    (by
      intro p hp
      simp only [cutEdges, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and,
        Finset.mem_singleton] at hp
      rcases hp with ⟨q, rfl⟩ | rfl <;> simp [isAlice])
    (by
      intro x y u v hu hv huv
      obtain ⟨u, rfl⟩ := e.symm.surjective u
      obtain ⟨v, rfl⟩ := e.symm.surjective v
      simp only [famGraph, comap_adj, Equiv.apply_symm_apply] at hu hv huv
      simp only [cutEdges, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and,
        Finset.mem_singleton, Prod.mk.injEq, EmbeddingLike.apply_eq_iff_eq, Prod.exists]
      rcases adj_cut_cases huv hu hv with ⟨h, i, rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inl ⟨h, i, rfl, rfl⟩
      · exact Or.inr ⟨rfl, rfl⟩)
    (fun x y y' u v hu hv => by
      simp only [famGraph, comap_adj] at hu hv ⊢
      exact adj_alice_indep _ hu hv)
    (fun x x' y u v hu hv => by
      simp only [famGraph, comap_adj] at hu hv ⊢
      exact adj_bob_indep _ hu hv)
    (fun x x' y y' u v hu hv => by
      simp only [famGraph, comap_adj] at hu hv ⊢
      exact adj_cut_indep _ _ hu hv)


/-! ### The reduction -/

section Reduction

variable {V I σ : Type*} {B : ℕ}

-- CSLib candidate
/-- The algorithm `A` with its local output (accept/reject) replaced by `o`; the execution is the
same. -/
def withOut (A : Algorithm V I σ B) (o : V → σ → Bool) : Algorithm V I σ B := { A with out := o }

lemma withOut_run (A : Algorithm V I σ B) (o : V → σ → Bool) (G : SimpleGraph V)
    [DecidableRel G.Adj] (inp : V → I) : ∀ t, (withOut A o).run G inp t = A.run G inp t
  | 0 => rfl
  | t + 1 => by
      funext v
      simp only [Algorithm.run, withOut_run A o G inp t]
      rfl

lemma withOut_accepts (A : Algorithm V I σ B) (o : V → σ → Bool) (G : SimpleGraph V)
    [DecidableRel G.Adj] (inp : V → I) (T : ℕ) :
    (withOut A o).Accepts G inp T ↔ ∀ v, o v (A.run G inp T v) = true := by
  simp only [Algorithm.Accepts, withOut_run]
  rfl

/-- **The reduction of Theorem 8 of [HW12]** (deterministic): on `n ≥ 6` nodes, an algorithm with
`B`-bit messages that, after `T` rounds, accepts exactly the graphs of the profile `Shape G d` with
`d` true (diameter `2`, as opposed to `3`), needs `k² ≤ T · 2 · (2k + 1) · B + 2` with
`k = ⌊(n-2)/4⌋`. Proof: the family `G_{x,y}` (relabelled to `V`) has a cut of `2k + 1` edges, so
CSLib's simulation theorem and `CC(DISJ_{k²}) ≥ k²` apply. -/
theorem lowerBound [Fintype V] {n : ℕ} (hn : Fintype.card V = n) (h6 : 6 ≤ n)
    (A : Algorithm V (V → Bool) σ B) (T : ℕ)
    (hA : ∀ (G : SimpleGraph V) [DecidableRel G.Adj] (d : Prop), Shape G d →
      (A.Accepts G (adjInput G) T ↔ d)) :
    (n - 2) / 4 * ((n - 2) / 4) ≤ T * (2 * ((2 * ((n - 2) / 4) + 1) * B)) + 2 := by
  classical
  set k := (n - 2) / 4 with hk
  have hk1 : 1 ≤ k := by omega
  have hcard : Fintype.card V = Fintype.card (Vtx k (n - 4 * k - 2)) := by
    rw [card_vtx]; omega
  let e := Fintype.equivOfCardEq hcard
  have h := (family e).disj_lowerBound A T (fun x y => by
    have hs : Shape ((family e).G x y) (disj x y = true) := by
      have := (shape (a := mat x) (b := mat y) (f := n - 4 * k - 2) hk1).comap e
      rw [← disj_eq_true_iff] at this
      exact this
    exact hA _ _ hs)
  simp only [Fintype.card_prod, Fintype.card_fin] at h
  refine h.trans ?_
  gcongr
  exact card_cutEdges e


/-- The `k²`-bound in linear form: `k² ≤ T · 2 · (2k+1) · B + 2` with `k = ⌊(n-2)/4⌋` and `n ≥ 6`
gives `n ≤ 16 T B + 13`, i.e. `T ≥ (n - 13) / (16 B) = Ω(n/B)`. -/
theorem n_le_of_bound {n T B : ℕ} (h6 : 6 ≤ n)
    (h : (n - 2) / 4 * ((n - 2) / 4) ≤ T * (2 * ((2 * ((n - 2) / 4) + 1) * B)) + 2) :
    n ≤ 16 * T * B + 13 := by
  set k := (n - 2) / 4 with hk
  have hk1 : 1 ≤ k := by omega
  have e1 : T * (2 * ((2 * k + 1) * B)) = 2 * (2 * k + 1) * (T * B) := by ring
  have e2 : 16 * T * B = 16 * (T * B) := by ring
  rw [e1] at h
  rw [e2]
  generalize T * B = m at h ⊢
  have hkle : k ≤ 4 * m + 2 := by
    by_contra hc
    push Not at hc
    have h1 : k * (4 * m + 3) ≤ k * k := Nat.mul_le_mul_left k hc
    nlinarith
  omega

/-- Generic form of the reduction: if, on every graph with the profile `Shape G d`, all nodes
satisfy the local test `o` after `T` rounds exactly when `d` holds, the `k²`-bound follows. -/
theorem lowerBound_out [Fintype V] {n : ℕ} (hn : Fintype.card V = n) (h6 : 6 ≤ n)
    (A : Algorithm V (V → Bool) σ B) (T : ℕ) (o : V → σ → Bool)
    (hA : ∀ (G : SimpleGraph V) [DecidableRel G.Adj] (d : Prop), Shape G d →
      ((∀ v, o v (A.run G (adjInput G) T v) = true) ↔ d)) :
    (n - 2) / 4 * ((n - 2) / 4) ≤ T * (2 * ((2 * ((n - 2) / 4) + 1) * B)) + 2 :=
  lowerBound hn h6 (withOut A o) T fun G _ d hs => by
    rw [withOut_accepts]; exact hA G d hs

end Reduction

end Diam23

open Diam23

/-! ### Theorem 8 -/

variable {V σ : Type*} [Fintype V] {n B : ℕ}

/-- **Theorem 8 of [HW12]** (deterministic, output convention "every node outputs the diameter"):
let `A` be a CONGEST algorithm with `B`-bit messages on `n ≥ 6` nodes whose nodes know their incident
edges, such that on every connected graph of diameter `2` or `3`, after `T` rounds, every node `v`
outputs `est v (state of v) = diam G`. Then `k² ≤ T · 2 · (2k+1) · B + 2` for `k = ⌊(n-2)/4⌋`;
hence `T = Ω(n/B)` (`theorem8_linear`). -/
theorem theorem8 (hn : Fintype.card V = n) (h6 : 6 ≤ n) (A : Algorithm V (V → Bool) σ B)
    (est : V → σ → ℕ) (T : ℕ)
    (hA : ∀ (G : SimpleGraph V) [DecidableRel G.Adj], G.Connected → (G.diam = 2 ∨ G.diam = 3) →
      ∀ v, est v (A.run G (adjInput G) T v) = G.diam) :
    (n - 2) / 4 * ((n - 2) / 4) ≤ T * (2 * ((2 * ((n - 2) / 4) + 1) * B)) + 2 := by
  refine lowerBound_out hn h6 A T (fun v s => decide (est v s ≤ 2)) fun G _ d hs => ?_
  have := hs.nonempty
  simp only [decide_eq_true_eq, hA G hs.connected hs.diam_two_or_three, forall_const]
  rw [← hs.diam_eq_two_iff]
  rcases hs.diam_two_or_three with h | h <;> rw [h] <;> decide

/-- **Theorem 8 of [HW12]**, linear form: `n ≤ 16 T B + 13`, i.e. `T = Ω(n/B)`. -/
theorem theorem8_linear (hn : Fintype.card V = n) (h6 : 6 ≤ n) (A : Algorithm V (V → Bool) σ B)
    (est : V → σ → ℕ) (T : ℕ)
    (hA : ∀ (G : SimpleGraph V) [DecidableRel G.Adj], G.Connected → (G.diam = 2 ∨ G.diam = 3) →
      ∀ v, est v (A.run G (adjInput G) T v) = G.diam) :
    n ≤ 16 * T * B + 13 :=
  n_le_of_bound h6 (theorem8 hn h6 A est T hA)

/-- **Theorem 8 of [HW12]** (deterministic, decision convention of CSLib: all nodes accept iff the
diameter is `2`, on connected graphs of diameter `2` or `3`). -/
theorem theorem8_accepts (hn : Fintype.card V = n) (h6 : 6 ≤ n)
    (A : Algorithm V (V → Bool) σ B) (T : ℕ)
    (hA : ∀ (G : SimpleGraph V) [DecidableRel G.Adj], G.Connected → (G.diam = 2 ∨ G.diam = 3) →
      (A.Accepts G (adjInput G) T ↔ G.diam = 2)) :
    (n - 2) / 4 * ((n - 2) / 4) ≤ T * (2 * ((2 * ((n - 2) / 4) + 1) * B)) + 2 :=
  lowerBound hn h6 A T fun G _ d hs => by
    rw [hA G hs.connected hs.diam_two_or_three, hs.diam_eq_two_iff]

/-! ### Lemmas 10, 11, 16 and Theorem 11 (exact versions via local tests) -/

/-- **Lemma 10 (1) of [HW12]**, APSP: if every node `v` outputs `est v (state) u = d(u, v)` for all
`u` (on connected graphs of diameter `2` or `3`) after `T` rounds, the `k²`-bound of Theorem 8
holds. (Node `v` accepts iff all its distances are `≤ 2`; no aggregation needed.) -/
theorem lemma10_apsp (hn : Fintype.card V = n) (h6 : 6 ≤ n) (A : Algorithm V (V → Bool) σ B)
    (est : V → σ → V → ℕ) (T : ℕ)
    (hA : ∀ (G : SimpleGraph V) [DecidableRel G.Adj], G.Connected → (G.diam = 2 ∨ G.diam = 3) →
      ∀ v u, est v (A.run G (adjInput G) T v) u = G.dist u v) :
    (n - 2) / 4 * ((n - 2) / 4) ≤ T * (2 * ((2 * ((n - 2) / 4) + 1) * B)) + 2 := by
  refine lowerBound_out hn h6 A T (fun v s => decide (∀ u, est v s u ≤ 2)) fun G _ d hs => ?_
  simp only [decide_eq_true_eq, hA G hs.connected hs.diam_two_or_three]
  rw [← hs.dist_le_two_iff]
  exact forall_comm

/-- **Lemma 10 (2) of [HW12]**, eccentricities: if every node `v` outputs its eccentricity. -/
theorem lemma10_eccentricity (hn : Fintype.card V = n) (h6 : 6 ≤ n)
    (A : Algorithm V (V → Bool) σ B) (ecc : V → σ → ℕ) (T : ℕ)
    (hA : ∀ (G : SimpleGraph V) [DecidableRel G.Adj], G.Connected → (G.diam = 2 ∨ G.diam = 3) →
      ∀ v, (ecc v (A.run G (adjInput G) T v) : ℕ∞) = G.eccent v) :
    (n - 2) / 4 * ((n - 2) / 4) ≤ T * (2 * ((2 * ((n - 2) / 4) + 1) * B)) + 2 := by
  refine lowerBound_out hn h6 A T (fun v s => decide (ecc v s ≤ 2)) fun G _ d hs => ?_
  rw [← hs.eccent_le_two_iff]
  refine forall_congr' fun v => ?_
  rw [decide_eq_true_eq, ← hA G hs.connected hs.diam_two_or_three v]
  exact_mod_cast Iff.rfl

/-- **Lemma 10 (3) of [HW12]**, peripheral vertices: if every node `v` outputs whether it is
peripheral (`ecc v = diam G`). Here all nodes are peripheral iff the inputs are disjoint, because
`ecc(c_L) = 2` always. -/
theorem lemma10_peripheral (hn : Fintype.card V = n) (h6 : 6 ≤ n)
    (A : Algorithm V (V → Bool) σ B) (per : V → σ → Bool) (T : ℕ)
    (hA : ∀ (G : SimpleGraph V) [DecidableRel G.Adj], G.Connected → (G.diam = 2 ∨ G.diam = 3) →
      ∀ v, per v (A.run G (adjInput G) T v) = true ↔ G.eccent v = G.ediam) :
    (n - 2) / 4 * ((n - 2) / 4) ≤ T * (2 * ((2 * ((n - 2) / 4) + 1) * B)) + 2 := by
  refine lowerBound_out hn h6 A T per fun G _ d hs => ?_
  simp only [hA G hs.connected hs.diam_two_or_three]
  exact hs.peripheral_iff

/-- **Lemma 11 of [HW12]** (exact part), center: if every node `v` outputs whether it belongs to
the center of `G`. Here the radius is always `2`, so the center is everything iff the diameter is
`2`. -/
theorem lemma11_center (hn : Fintype.card V = n) (h6 : 6 ≤ n)
    (A : Algorithm V (V → Bool) σ B) (cen : V → σ → Bool) (T : ℕ)
    (hA : ∀ (G : SimpleGraph V) [DecidableRel G.Adj], G.Connected → (G.diam = 2 ∨ G.diam = 3) →
      ∀ v, cen v (A.run G (adjInput G) T v) = true ↔ v ∈ G.center) :
    (n - 2) / 4 * ((n - 2) / 4) ≤ T * (2 * ((2 * ((n - 2) / 4) + 1) * B)) + 2 := by
  refine lowerBound_out hn h6 A T cen fun G _ d hs => ?_
  simp only [hA G hs.connected hs.diam_two_or_three]
  rw [← hs.center_eq_univ_iff, Set.eq_univ_iff_forall]

/-- **Lemma 16 of [HW12]**: a `(×, 3/2 − ε)`-approximation of APSP (`ε > 0`; node `v` outputs
estimates `est v (state) u` with `d(u, v) ≤ est ≤ (3/2 − ε) · d(u, v)`) on connected graphs of
diameter `2` or `3` needs the `k²`-bound of Theorem 8 (node `v` accepts iff all its estimates are
`< 3`). -/
theorem lemma16 (hn : Fintype.card V = n) (h6 : 6 ≤ n) (A : Algorithm V (V → Bool) σ B)
    (est : V → σ → V → ℝ) (ε : ℝ) (hε : 0 < ε) (T : ℕ)
    (hA : ∀ (G : SimpleGraph V) [DecidableRel G.Adj], G.Connected → (G.diam = 2 ∨ G.diam = 3) →
      ∀ v u, (G.dist u v : ℝ) ≤ est v (A.run G (adjInput G) T v) u ∧
        est v (A.run G (adjInput G) T v) u ≤ (3 / 2 - ε) * G.dist u v) :
    (n - 2) / 4 * ((n - 2) / 4) ≤ T * (2 * ((2 * ((n - 2) / 4) + 1) * B)) + 2 := by
  classical
  refine lowerBound_out hn h6 A T (fun v s => decide (∀ u, est v s u < 3)) fun G _ d hs => ?_
  have hA' := hA G hs.connected hs.diam_two_or_three
  simp only [decide_eq_true_eq]
  rw [← hs.dist_le_two_iff]
  constructor
  · intro h u v
    have h1 := (hA' v u).1
    have h2 := h v u
    have : (G.dist u v : ℝ) < 3 := lt_of_le_of_lt h1 h2
    exact_mod_cast Nat.lt_succ_iff.1 (by exact_mod_cast this)
  · intro h v u
    have h1 := (hA' v u).2
    have h0 : (0 : ℝ) ≤ G.dist u v := Nat.cast_nonneg _
    rcases (show G.dist u v ≤ 1 ∨ G.dist u v = 2 by have := h u v; omega) with h2 | h2
    · have h2' : (G.dist u v : ℝ) ≤ 1 := by exact_mod_cast h2
      nlinarith
    · rw [h2] at h1
      push_cast at h1
      linarith

/-- **Theorem 11 of [HW12]** (deterministic), all 2-BFS trees: if every node `v` outputs, for every
`u`, whether `u` lies in its depth-2 BFS tree (`d(v, u) ≤ 2`), the `k²`-bound of Theorem 8 holds. -/
theorem theorem11 (hn : Fintype.card V = n) (h6 : 6 ≤ n) (A : Algorithm V (V → Bool) σ B)
    (bfs : V → σ → V → Bool) (T : ℕ)
    (hA : ∀ (G : SimpleGraph V) [DecidableRel G.Adj], G.Connected → (G.diam = 2 ∨ G.diam = 3) →
      ∀ v u, bfs v (A.run G (adjInput G) T v) u = true ↔ G.dist v u ≤ 2) :
    (n - 2) / 4 * ((n - 2) / 4) ≤ T * (2 * ((2 * ((n - 2) / 4) + 1) * B)) + 2 := by
  refine lowerBound_out hn h6 A T (fun v s => decide (∀ u, bfs v s u = true)) fun G _ d hs => ?_
  simp only [decide_eq_true_eq, hA G hs.connected hs.diam_two_or_three]
  exact hs.dist_le_two_iff


/-! ### Theorem 8, randomized (conditional on the randomized `CC(DISJ)` bound) -/

/-- The randomized communication lower bound for set disjointness, as a hypothesis
(Kalyanasundaram–Schnitger / Razborov: true for `ε = 1/3` and some real `κ > 0`; not formalized):
every private-coin protocol computing `DISJ_K` with error `≤ ε` on every input sends at least
`κ · K` bits. Coin spaces are nonempty (otherwise the hypothesis forces `κ ≤ 0`). -/
def Diam23.RandDisjLB (ε κ : ℝ) : Prop :=
  ∀ (ι RA RB : Type) [Fintype ι] [Fintype RA] [Fintype RB] [Nonempty RA] [Nonempty RB]
    (P : Protocol ((ι → Bool) × RA) ((ι → Bool) × RB) Bool) (c : ℕ),
    P.RandComputes (fun x y => disj x y) ε → P.CostLE c → κ * Fintype.card ι ≤ c

/-- **Theorem 8 of [HW12]** (randomized, conditional on `RandDisjLB ε κ`): a randomized algorithm
(private random strings `r v : ρ`) in which, on every connected `n`-node graph of diameter `2` or
`3`, all nodes accept iff the diameter is `2`, except with probability `≤ ε`, satisfies
`κ · k² ≤ T · 2 · (2k+1) · B + 2` with `k = ⌊(n-2)/4⌋`, i.e. `T = Ω(κ n / B)`. -/
theorem theorem8_randomized {V σ ρ : Type} [Fintype V] [DecidableEq V] [Fintype ρ] [Nonempty ρ]
    {n B : ℕ} (hn : Fintype.card V = n) (h6 : 6 ≤ n) (A : Algorithm V ((V → Bool) × ρ) σ B)
    (T : ℕ) {ε κ : ℝ} (hCC : Diam23.RandDisjLB ε κ)
    (hA : ∀ (G : SimpleGraph V) [DecidableRel G.Adj], G.Connected → (G.diam = 2 ∨ G.diam = 3) →
      (LBFamily.Algorithm.randErr A G (adjInput G) T (decide (G.diam = 2)) : ℝ) ≤
        ε * Fintype.card (V → ρ)) :
    κ * ((n - 2) / 4 * ((n - 2) / 4) : ℕ) ≤
      ((T * (2 * ((2 * ((n - 2) / 4) + 1) * B)) + 2 : ℕ) : ℝ) := by
  classical
  set k := (n - 2) / 4 with hk
  have hk1 : 1 ≤ k := by omega
  have hcard : Fintype.card V = Fintype.card (Vtx k (n - 4 * k - 2)) := by
    rw [card_vtx]; omega
  let e := Fintype.equivOfCardEq hcard
  have h := (family e).rand_lowerBound A T (fun x y => disj x y) ε (fun x y => by
    have hs : Shape ((family e).G x y) (disj x y = true) := by
      have := (shape (a := mat x) (b := mat y) (f := n - 4 * k - 2) hk1).comap e
      rw [← disj_eq_true_iff] at this
      exact this
    have h1 := hA _ hs.connected hs.diam_two_or_three
    have h2 : decide (((family e).G x y).diam = 2) = disj x y :=
      Bool.eq_iff_iff.2 (by simp [hs.diam_eq_two_iff])
    rw [h2] at h1
    exact h1) ⌈κ * (k * k : ℕ)⌉₊ (fun P c hP hc => Nat.ceil_le.2 (by
      have := hCC _ _ _ P c hP hc
      simpa using this))
  have h' : T * (2 * ((family e).Ecut.card * B)) + 2 ≤ T * (2 * ((2 * k + 1) * B)) + 2 := by
    gcongr
    exact card_cutEdges e
  calc κ * ((k * k : ℕ) : ℝ) ≤ (⌈κ * (k * k : ℕ)⌉₊ : ℝ) := Nat.le_ceil _
    _ ≤ _ := by exact_mod_cast h.trans h'

/-! ### Non-vacuity: full-information gathering satisfies all hypotheses (for large `B`) -/

section NonVacuity

variable [DecidableEq V]

/-- After `|V|` rounds of CSLib's gathering algorithm on a connected graph, every node knows the
whole adjacency matrix. -/
lemma Diam23.gather_knows (P : (V → V → Bool) → Prop) (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.Connected) (v : V) :
    SimpleGraph.fromRel (fun a b => ((gatherAlg P).run G (adjInput G) (Fintype.card V) v).2 a b
      = true) = G := by
  have hall : ∀ a, ∃ p : G.Walk v a, p.length ≤ Fintype.card V := by
    intro a
    obtain ⟨p⟩ := hG.preconnected v a
    exact ⟨p.bypass, (p.bypass_isPath.length_lt).le⟩
  have hadj : ((gatherAlg P).run G (adjInput G) (Fintype.card V) v).2 = adjInput G := by
    funext a b
    have := (gather_run P G (Fintype.card V) v).2 a b
    simp only [hall a, true_and] at this
    cases h : ((gatherAlg P).run G (adjInput G) (Fintype.card V) v).2 a b <;>
      simp_all [adjInput]
  rw [hadj, fromRel_adjInput]

/-- The graph a gathering node has reconstructed. -/
noncomputable def Diam23.known (s : Know V) : SimpleGraph V :=
  SimpleGraph.fromRel fun a b => s.2 a b = true

/-- Non-vacuity of `theorem8`: gathering + local computation outputs the diameter in `|V|` rounds
(with `gatherBits V = n + n²`-bit messages). -/
theorem theorem8_nonvacuous :
    ∀ (G : SimpleGraph V) [DecidableRel G.Adj], G.Connected → (G.diam = 2 ∨ G.diam = 3) →
      ∀ v, (known ((gatherAlg fun _ => True).run G (adjInput G) (Fintype.card V) v)).diam
        = G.diam :=
  fun G _ hG _ v => by simp only [known, gather_knows _ G hG v]

/-- Non-vacuity of `theorem8_accepts`. -/
theorem theorem8_accepts_nonvacuous :
    ∀ (G : SimpleGraph V) [DecidableRel G.Adj], G.Connected → (G.diam = 2 ∨ G.diam = 3) →
      ((gatherAlg fun M => (SimpleGraph.fromRel fun a b => M a b = true).diam = 2).Accepts G
        (adjInput G) (Fintype.card V) ↔ G.diam = 2) :=
  fun G _ hG _ => gather_accepts_graph G (fun H => H.diam = 2) hG

/-- Non-vacuity of `lemma10_apsp` (and of `lemma16` with `ε = 1/2`, exact distances). -/
theorem lemma10_apsp_nonvacuous :
    ∀ (G : SimpleGraph V) [DecidableRel G.Adj], G.Connected → (G.diam = 2 ∨ G.diam = 3) →
      ∀ v u, (known ((gatherAlg fun _ => True).run G (adjInput G) (Fintype.card V) v)).dist u v
        = G.dist u v :=
  fun G _ hG _ v u => by simp only [known, gather_knows _ G hG v]

/-- Non-vacuity of `lemma16`: exact distances are a `(×, 3/2 − 1/2)`-approximation. -/
theorem lemma16_nonvacuous :
    ∀ (G : SimpleGraph V) [DecidableRel G.Adj], G.Connected → (G.diam = 2 ∨ G.diam = 3) →
      ∀ v u, let δ : ℝ :=
        (known ((gatherAlg fun _ => True).run G (adjInput G) (Fintype.card V) v)).dist u v
      (G.dist u v : ℝ) ≤ δ ∧ δ ≤ (3 / 2 - 1 / 2) * G.dist u v := by
  intro G _ hG hd v u
  simp only [lemma10_apsp_nonvacuous G hG hd v u]
  norm_num

/-- Non-vacuity of `lemma10_eccentricity`, `lemma10_peripheral`, `lemma11_center`, `theorem11`: the
gathered graph is `G` itself, so every node can compute its eccentricity, peripherality, center
membership and 2-neighbourhood locally. -/
theorem known_gather_eq :
    ∀ (G : SimpleGraph V) [DecidableRel G.Adj], G.Connected →
      ∀ v, known ((gatherAlg fun _ => True).run G (adjInput G) (Fintype.card V) v) = G :=
  fun G _ hG v => gather_knows _ G hG v

/-- Sanity check: the non-vacuity witness plugs into `theorem8_linear`. -/
example {n : ℕ} (hn : Fintype.card V = n) (h6 : 6 ≤ n) :
    n ≤ 16 * Fintype.card V * gatherBits V + 13 :=
  theorem8_linear hn h6 (gatherAlg fun _ => True) (fun _ s => (known s).diam) _
    theorem8_nonvacuous

end NonVacuity

end Podc.OptimalAPSP
