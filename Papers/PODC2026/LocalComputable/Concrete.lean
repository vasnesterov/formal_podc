import Papers.PODC2026.LocalComputable.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.Order.Monoid.Unbundled.Pow

/-!
# The concrete LOCAL model of Section 3

Networks `(G, x, deg, id, {p_v})` of Section 3: finite simple graphs of maximum degree `Δ`,
port numbering (the order of each node's neighbour list), unique identifiers in `[1, n^c]`,
and inputs from a finite alphabet `{0, …, k-1}`. Nodes are `0, …, n-1`.

Views: the radius-`t` *full-information view* of `v` — what `v` knows after `t` rounds of
unbounded message passing: its identifier, input and degree and, for `t > 0`, the radius-`(t-1)`
views of its neighbours in port order. With unique identifiers this carries the same information
as the rooted labelled neighbourhood `N^t(v)` of Definition 3.1 (nodes at distance `≤ t` with
their degrees, edges with an endpoint at distance `≤ t-1`, ports, identifiers, inputs). The
abstract results only use the restriction property (`fview_restrict`), which holds for both.
-/

namespace LocalComputable

/-- A raw port-numbered network with identifiers and inputs (`nbr[v]` = neighbours of `v` in
port order). -/
structure PNet where
  /-- number of nodes -/
  n : ℕ
  /-- port-ordered neighbour lists -/
  nbr : List (List ℕ)
  /-- identifiers -/
  id : List ℕ
  /-- local inputs -/
  inp : List ℕ
  deriving DecidableEq

namespace PNet

/-- Neighbours of `v` in port order. -/
def nbrOf (G : PNet) (v : ℕ) : List ℕ := G.nbr.getD v []
/-- Identifier of `v`. -/
def idOf (G : PNet) (v : ℕ) : ℕ := G.id.getD v 0
/-- Input of `v`. -/
def inpOf (G : PNet) (v : ℕ) : ℕ := G.inp.getD v 0

/-- Well-formed networks of Section 3: simple undirected graphs of maximum degree `Δ`, unique
identifiers in `[1, n^c]`, inputs in `{0, …, k-1}`. -/
structure WF (Δ c k : ℕ) (G : PNet) : Prop where
  len_nbr : G.nbr.length = G.n
  len_id : G.id.length = G.n
  len_inp : G.inp.length = G.n
  nodup : ∀ v < G.n, (G.nbrOf v).Nodup
  deg_le : ∀ v < G.n, (G.nbrOf v).length ≤ Δ
  nbr_lt : ∀ v < G.n, ∀ u ∈ G.nbrOf v, u < G.n
  irrefl : ∀ v < G.n, v ∉ G.nbrOf v
  symm : ∀ v < G.n, ∀ u ∈ G.nbrOf v, v ∈ G.nbrOf u
  id_inj : ∀ u < G.n, ∀ v < G.n, G.idOf u = G.idOf v → u = v
  id_pos : ∀ v < G.n, 1 ≤ G.idOf v
  id_le : ∀ v < G.n, G.idOf v ≤ G.n ^ c
  inp_lt : ∀ v < G.n, G.inpOf v < k

end PNet

/-- Full-information views: identifier, input, degree, and the children's views. -/
inductive VTree
  | node (id inp deg : ℕ) (kids : List VTree)

namespace VTree

/-- Truncation of a view to radius `s`. -/
def trunc : ℕ → VTree → VTree
  | 0, node i p d _ => node i p d []
  | s + 1, node i p d ks => node i p d (ks.map (trunc s))

/-- All identifiers occurring in a view. -/
def ids : VTree → List ℕ
  | node i _ _ ks => i :: ks.flatMap fun k => ids k

end VTree

open PNet VTree

/-- The radius-`t` full-information view of `v` in `G`. -/
def fview (G : PNet) : ℕ → ℕ → VTree
  | v, 0 => node (G.idOf v) (G.inpOf v) (G.nbrOf v).length []
  | v, t + 1 => node (G.idOf v) (G.inpOf v) (G.nbrOf v).length
      ((G.nbrOf v).map fun u => fview G u t)

theorem trunc_fview (G : PNet) {s t : ℕ} (h : s ≤ t) (v : ℕ) :
    (fview G v t).trunc s = fview G v s := by
  induction s generalizing t v with
  | zero => cases t <;> rfl
  | succ s ih =>
    obtain ⟨t, rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
    simp only [fview, trunc, List.map_map]
    congr 1
    exact List.map_congr_left fun u _ => ih (by omega) u

/-- The restriction property: the radius-`t` view determines all smaller views. -/
theorem fview_restrict {G G' : PNet} {v v' t s : ℕ} (h : s ≤ t)
    (he : fview G v t = fview G' v' t) : fview G v s = fview G' v' s := by
  rw [← trunc_fview G h, ← trunc_fview G' h, he]

/-- Identifiers in the view of a node are identifiers of nodes of the network. -/
theorem mem_ids_fview {Δ c k : ℕ} {G : PNet} (hG : G.WF Δ c k) {i : ℕ} :
    ∀ {t v : ℕ}, v < G.n → i ∈ (fview G v t).ids → ∃ u < G.n, G.idOf u = i := by
  intro t
  induction t with
  | zero =>
    intro v hv h
    simp only [fview, ids, List.flatMap_nil, List.mem_cons, List.not_mem_nil, or_false] at h
    exact ⟨v, hv, h.symm⟩
  | succ t ih =>
    intro v hv h
    simp only [fview, ids, List.mem_cons, List.mem_flatMap, List.mem_map] at h
    rcases h with h | ⟨_, ⟨u, hu, rfl⟩, hi⟩
    · exact ⟨v, hv, h.symm⟩
    · exact ih (hG.nbr_lt v hv u hu) hi

/-- A network containing a node whose view shows `m` distinct identifiers has at least `m`
nodes. -/
theorem card_ids_le {Δ c k : ℕ} {G : PNet} (hG : G.WF Δ c k) {v t : ℕ} (hv : v < G.n) :
    (fview G v t).ids.toFinset.card ≤ G.n := by
  classical
  calc (fview G v t).ids.toFinset.card ≤ ((Finset.range G.n).image G.idOf).card := by
        refine Finset.card_le_card fun i hi => ?_
        obtain ⟨u, hu, rfl⟩ := mem_ids_fview hG hv (List.mem_toFinset.mp hi)
        exact Finset.mem_image_of_mem _ (Finset.mem_range.mpr hu)
    _ ≤ (Finset.range G.n).card := Finset.card_image_le
    _ = G.n := Finset.card_range _

/-- Well-formed networks. -/
def Net (Δ c k : ℕ) := {G : PNet // G.WF Δ c k}

/-- **The LOCAL model of Section 3** as an instance of the abstract model: networks of maximum
degree `Δ` with identifiers in `[1, n^c]` and inputs `< k`, full-information views. -/
def concreteModel (Δ c k : ℕ) : Model (Net Δ c k) VTree where
  size G := G.1.n
  view G v t := fview G.1 v t
  restrict h he := fview_restrict h he

end LocalComputable
