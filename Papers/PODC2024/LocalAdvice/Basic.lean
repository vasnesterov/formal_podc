import Mathlib
import Cslib.Foundations.Combinatorics.SimpleGraph.Ball

/-!
# Local advice for 3-colouring: basic notions

Notation of Appendix D of Balliu et al., *Distributed Computation with Local Advice*
(arXiv:2405.04519). Colours are `Fin 3`; the paper's colour `1, 2, 3` is our `0, 1, 2`.

* `restrict G P`: the subgraph of `G` keeping only the edges between nodes satisfying `P` (on the
  same vertex type; the other nodes become isolated).
* `IsGreedy G φ`: `φ` is a proper colouring in which every node of colour `i` has neighbours of all
  colours `< i`.
* `H23 G φ`: the graph `G_{2,3}` induced by the nodes of (paper) colours 2 and 3; its connected
  components are the "maximal connected components" `C` of the paper, and distances in it are the
  distances `dist_C`.
* `nbr0 G φ v`: the neighbours of `v` of (paper) colour 1.
* `IsLarge H D u`: the component of `u` in `H` has (strong) diameter `> D`.
-/

namespace Podc.LocalAdvice

open SimpleGraph Finset

variable {V : Type*}

-- CSLib candidate (with `gAgree_restrict` of `Decoder.lean`)
/-- The subgraph of `G` keeping the edges between nodes satisfying `P`. -/
def restrict (G : SimpleGraph V) (P : V → Prop) : SimpleGraph V where
  Adj u v := G.Adj u v ∧ P u ∧ P v
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩
  loopless := ⟨fun _ h => G.loopless.irrefl _ h.1⟩

@[simp] lemma restrict_adj {G : SimpleGraph V} {P : V → Prop} {u v : V} :
    (restrict G P).Adj u v ↔ G.Adj u v ∧ P u ∧ P v := Iff.rfl

lemma restrict_le (G : SimpleGraph V) (P : V → Prop) : restrict G P ≤ G := fun _ _ h => h.1

/-- `φ` is a *greedy* 3-colouring of `G`: proper, and every node of colour `i` has a neighbour of
each colour `j < i`. -/
def IsGreedy (G : SimpleGraph V) (φ : V → Fin 3) : Prop :=
  (∀ u v, G.Adj u v → φ u ≠ φ v) ∧ ∀ v (j : Fin 3), j < φ v → ∃ w, G.Adj v w ∧ φ w = j

/-- Every 3-colourable finite graph has a greedy 3-colouring (take a proper colouring with minimal
sum of colours). -/
theorem exists_isGreedy [Finite V] (G : SimpleGraph V) (h : G.Colorable 3) :
    ∃ φ : V → Fin 3, IsGreedy G φ := by
  classical
  have := Fintype.ofFinite V
  obtain ⟨c⟩ := h
  let P : Finset (V → Fin 3) := univ.filter fun φ => ∀ u v, G.Adj u v → φ u ≠ φ v
  have hP : P.Nonempty := ⟨c, by simp [P]; exact fun u v huv => c.valid huv⟩
  obtain ⟨φ, hφP, hmin⟩ := P.exists_min_image (fun φ => ∑ v, (φ v : ℕ)) hP
  have hprop : ∀ u v, G.Adj u v → φ u ≠ φ v := by simpa [P] using hφP
  refine ⟨φ, hprop, fun v j hj => ?_⟩
  by_contra hne
  push Not at hne
  let ψ := Function.update φ v j
  have hψ : ψ ∈ P := by
    simp only [P, mem_filter, mem_univ, true_and]
    intro a b hab
    by_cases ha : a = v
    · subst ha
      have hb : b ≠ a := G.ne_of_adj hab |>.symm
      simp only [ψ, Function.update_self, Function.update_of_ne hb]
      exact fun h => hne b hab h.symm
    · by_cases hb : b = v
      · subst hb
        simp only [ψ, Function.update_self, Function.update_of_ne ha]
        exact fun h => hne a hab.symm h
      · simp only [ψ, Function.update_of_ne ha, Function.update_of_ne hb]
        exact hprop a b hab
  have h1 := hmin ψ hψ
  have h2 : ∑ w, (ψ w : ℕ) < ∑ w, (φ w : ℕ) := by
    apply Finset.sum_lt_sum
    · intro w _
      by_cases hw : w = v
      · subst hw; simp only [ψ, Function.update_self]; exact le_of_lt (by exact_mod_cast hj)
      · simp [ψ, Function.update_of_ne hw]
    · exact ⟨v, mem_univ _, by simp only [ψ, Function.update_self]; exact_mod_cast hj⟩
  omega

/-- The graph `G_{2,3}`: the edges of `G` between nodes of (paper) colours 2 and 3. -/
abbrev H23 (G : SimpleGraph V) (φ : V → Fin 3) : SimpleGraph V := restrict G (fun v => φ v ≠ 0)

/-- The neighbours of `v` of (paper) colour 1. -/
noncomputable def nbr0 [Fintype V] (G : SimpleGraph V) (φ : V → Fin 3) (v : V) : Finset V :=
  open scoped Classical in univ.filter fun w => G.Adj v w ∧ φ w = 0

@[simp] lemma mem_nbr0 [Fintype V] {G : SimpleGraph V} {φ : V → Fin 3} {v w : V} :
    w ∈ nbr0 G φ v ↔ G.Adj v w ∧ φ w = 0 := by
  classical
  simp [nbr0]

/-- The component of `u` in `H` has (strong) diameter larger than `D`. -/
def IsLarge (H : SimpleGraph V) (D : ℕ) (u : V) : Prop :=
  ∃ x y, H.Reachable u x ∧ H.Reachable u y ∧ D < H.dist x y

/-! ### Geodesics -/

/-- A geodesic from `u` to a node `x` at distance `k`: nodes `f 0 = u, …, f k = x`, consecutive
ones adjacent, with `d(u, f i) = i`. -/
lemma exists_geodesic (H : SimpleGraph V) (u : V) :
    ∀ (k : ℕ) (x : V), H.edist u x = k → ∃ f : ℕ → V, f 0 = u ∧ f k = x ∧
      (∀ i < k, H.Adj (f i) (f (i + 1))) ∧ ∀ i ≤ k, H.edist u (f i) = i := by
  intro k
  induction k with
  | zero =>
    intro x hx
    simp only [CharP.cast_eq_zero, edist_eq_zero_iff] at hx
    subst hx
    exact ⟨fun _ => u, rfl, rfl, by simp, fun i hi => by simp [show i = 0 by omega]⟩
  | succ k ih =>
    intro x hx
    obtain ⟨y, hy, hyx⟩ := SimpleGraph.exists_adj_of_edist_eq_succ hx
    obtain ⟨f, hf0, hfk, hadj, hd⟩ := ih y hy
    refine ⟨fun i => if i = k + 1 then x else f i, by simp [hf0], by simp, fun i hi => ?_,
      fun i hi => ?_⟩
    · by_cases h : i = k
      · subst h; simp [hfk, hyx]
      · simp only [show i ≠ k + 1 by omega, ite_false, show i + 1 ≠ k + 1 by omega]
        exact hadj i (by omega)
    · by_cases h : i = k + 1
      · subst h; simp [hx]
      · simp only [h, ite_false]; exact hd i (by omega)

/-- If `x` is at finite distance at least `m` from `u`, some node is at distance exactly `m`;
in fact there is a geodesic of length `m` starting at `u`. -/
lemma exists_geodesic_of_le (H : SimpleGraph V) {u x : V} {m : ℕ} (hr : H.Reachable u x)
    (hm : m ≤ H.dist u x) : ∃ f : ℕ → V, f 0 = u ∧
      (∀ i < m, H.Adj (f i) (f (i + 1))) ∧ ∀ i ≤ m, H.edist u (f i) = i := by
  obtain ⟨f, hf0, -, hadj, hd⟩ := exists_geodesic H u (H.dist u x) x hr.coe_dist_eq_edist.symm
  exact ⟨f, hf0, fun i hi => hadj i (by omega), fun i hi => hd i (by omega)⟩

/-- In a component of diameter `> D`, every node has eccentricity `≥ D / 2`: there is a geodesic
of any length `m ≤ D / 2` from it. -/
lemma IsLarge.exists_geodesic {H : SimpleGraph V} {D : ℕ} {u : V} (h : IsLarge H D u)
    {m : ℕ} (hm : 2 * m ≤ D) : ∃ f : ℕ → V, f 0 = u ∧
      (∀ i < m, H.Adj (f i) (f (i + 1))) ∧ ∀ i ≤ m, H.edist u (f i) = i := by
  obtain ⟨x, y, hx, hy, hxy⟩ := h
  have htri : H.dist x y ≤ H.dist x u + H.dist u y := hx.symm.dist_triangle_left y
  have hc : H.dist x u = H.dist u x := dist_comm
  by_cases h1 : m ≤ H.dist u x
  · exact exists_geodesic_of_le H hx h1
  · exact exists_geodesic_of_le H hy (by omega)

/-- `IsLarge` only depends on the component. -/
lemma IsLarge.of_reachable {H : SimpleGraph V} {D : ℕ} {u v : V} (h : IsLarge H D u)
    (huv : H.Reachable u v) : IsLarge H D v := by
  obtain ⟨x, y, hx, hy, hxy⟩ := h
  exact ⟨x, y, huv.symm.trans hx, huv.symm.trans hy, hxy⟩

end Podc.LocalAdvice
