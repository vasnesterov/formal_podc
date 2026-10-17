import Mathlib
import Cslib.Foundations.Combinatorics.SimpleGraph.Arboricity
import Podc.Graph.Ball

/-!
# Weighted dominating sets, packings, weak duality

Basic notions of Dory–Ghaffari–Ilchi, *Near-Optimal Distributed Dominating Set in Bounded Arboricity
Graphs* (PODC 2022), Section 2.

* `cnbr G v` — the closed neighbourhood `N⁺_v = {v} ∪ N_v` (`SimpleGraph.closedNeighborFinset`).
* `IsDominating G D` — every vertex is in `D` or has a neighbour in `D` (equivalently
  `G.IsDominatingSet ↑D`, `isDominating_iff_isDominatingSet`).
* `dom G S` — `N⁺_S`, the vertices dominated by `S`.
* `wt w D` — the total weight `w_D`.
* `IsPacking G w x` — `x ≥ 0` and `X_u = ∑_{v ∈ N⁺_u} x_v ≤ w_u` for every `u`.
* `tau G w v` — `τ_v = min_{u ∈ N⁺_v} w_u`, and `tauNode G w v ∈ N⁺_v` attaining it.

Main result: weak duality, Lemma 2.1 (`sum_le_wt_of_isPacking`).
-/

namespace DominatingSetArboricity

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The closed neighbourhood `N⁺_v` (`SimpleGraph.closedNeighborFinset`). -/
def cnbr (v : V) : Finset V := G.closedNeighborFinset v

variable {G}

theorem cnbr_eq_insert (v : V) : cnbr G v = insert v (G.neighborFinset v) := rfl

theorem mem_cnbr {v u : V} : u ∈ cnbr G v ↔ u = v ∨ G.Adj v u :=
  SimpleGraph.mem_closedNeighborFinset

theorem self_mem_cnbr (v : V) : v ∈ cnbr G v := mem_cnbr.2 (Or.inl rfl)

theorem coe_cnbr (v : V) : (cnbr G v : Set V) = G.closedNeighborSet v :=
  SimpleGraph.coe_closedNeighborFinset

theorem mem_cnbr_comm {v u : V} : u ∈ cnbr G v ↔ v ∈ cnbr G u := by
  rw [← mem_coe, ← mem_coe, coe_cnbr, coe_cnbr, SimpleGraph.mem_closedNeighborSet_comm]

theorem cnbr_nonempty (v : V) : (cnbr G v).Nonempty := ⟨v, self_mem_cnbr v⟩

theorem card_cnbr (v : V) : (cnbr G v).card = G.degree v + 1 :=
  SimpleGraph.card_closedNeighborFinset

theorem card_cnbr_le (v : V) : (cnbr G v).card ≤ G.maxDegree + 1 := by
  rw [card_cnbr]; exact Nat.add_le_add_right (G.degree_le_maxDegree v) 1

variable (G)

/-- `D` is a dominating set: every vertex is in `D` or adjacent to a vertex of `D`. -/
def IsDominating (D : Finset V) : Prop := ∀ v, ∃ u ∈ D, u ∈ cnbr G v

theorem isDominating_iff_isDominatingSet {D : Finset V} :
    IsDominating G D ↔ G.IsDominatingSet ↑D := by
  simp only [IsDominating, SimpleGraph.isDominatingSet_iff_forall_exists_mem, mem_coe,
    ← coe_cnbr]

/-- `N⁺_S`: the vertices dominated by `S`. -/
def dom (S : Finset V) : Finset V := univ.filter fun v => ∃ u ∈ S, u ∈ cnbr G v

variable {G} in
theorem mem_dom {S : Finset V} {v : V} : v ∈ dom G S ↔ ∃ u ∈ S, u ∈ cnbr G v := by
  simp [dom]

/-- Total weight of a set. -/
def wt (w : V → ℝ) (D : Finset V) : ℝ := ∑ v ∈ D, w v

/-- A (fractional) packing: `x ≥ 0` and `X_u = ∑_{v ∈ N⁺_u} x_v ≤ w_u` for all `u`. -/
def IsPacking (w x : V → ℝ) : Prop := (∀ v, 0 ≤ x v) ∧ ∀ u, ∑ v ∈ cnbr G u, x v ≤ w u

/-- **Lemma 2.1** (weak duality): the value of a packing is at most the weight of any dominating
set, hence at most `OPT`. -/
theorem sum_le_wt_of_isPacking {w x : V → ℝ} (hx : IsPacking G w x) {D : Finset V}
    (hD : IsDominating G D) : ∑ v, x v ≤ wt w D := by
  classical
  -- every `v` is counted at least once in `∑_{u ∈ D} X_u`
  have key : ∑ v, x v ≤ ∑ u ∈ D, ∑ v ∈ cnbr G u, x v := by
    rw [Finset.sum_comm' (t' := univ) (s' := fun v => D.filter fun u => v ∈ cnbr G u)
      (h := by intro u v; simp)]
    refine sum_le_sum fun v _ => ?_
    obtain ⟨u, huD, hu⟩ := hD v
    have : u ∈ D.filter fun u => v ∈ cnbr G u := by simp [huD, mem_cnbr_comm.1 hu]
    calc x v = ∑ _u ∈ ({u} : Finset V), x v := by simp
      _ ≤ ∑ _u ∈ D.filter fun u => v ∈ cnbr G u, x v :=
        sum_le_sum_of_subset_of_nonneg (by simpa using this) fun _ _ _ => hx.1 v
  exact key.trans (sum_le_sum fun u _ => hx.2 u)

/-- `τ_v`: the minimum weight of a vertex dominating `v`. -/
def tau (w : V → ℝ) (v : V) : ℝ := (cnbr G v).inf' (cnbr_nonempty v) w

/-- A vertex of `N⁺_v` of weight `τ_v` (an arbitrary one, chosen by `Classical.epsilon` so that a
distributed node choosing from the same candidate set makes the same choice). -/
noncomputable def tauNode (w : V → ℝ) (v : V) : V :=
  haveI : Nonempty V := ⟨v⟩
  Classical.epsilon fun u => u ∈ cnbr G v ∧ w u = tau G w v

variable {G}

theorem tau_le {w : V → ℝ} {v u : V} (hu : u ∈ cnbr G v) : tau G w v ≤ w u :=
  inf'_le _ hu

theorem exists_tauNode (w : V → ℝ) (v : V) : ∃ u, u ∈ cnbr G v ∧ w u = tau G w v := by
  obtain ⟨u, hu, h⟩ := (cnbr G v).exists_min_image w (cnbr_nonempty v)
  exact ⟨u, hu, le_antisymm (le_inf' _ _ h) (tau_le hu)⟩

theorem tauNode_spec (w : V → ℝ) (v : V) :
    tauNode G w v ∈ cnbr G v ∧ w (tauNode G w v) = tau G w v :=
  Classical.epsilon_spec (exists_tauNode w v)

theorem tauNode_mem (w : V → ℝ) (v : V) : tauNode G w v ∈ cnbr G v := (tauNode_spec w v).1

theorem w_tauNode (w : V → ℝ) (v : V) : w (tauNode G w v) = tau G w v := (tauNode_spec w v).2

theorem tau_pos {w : V → ℝ} (hw : ∀ v, 0 < w v) (v : V) : 0 < tau G w v := by
  rw [← w_tauNode]; exact hw _

/-- `τ_v ≤ w_u` whenever `u` dominates `v`; in particular `τ_v ≤ w_v`. -/
theorem tau_le_self (w : V → ℝ) (v : V) : tau G w v ≤ w v := tau_le (self_mem_cnbr v)

end DominatingSetArboricity
