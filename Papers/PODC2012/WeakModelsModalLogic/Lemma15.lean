import Papers.PODC2012.WeakModelsModalLogic.Bisimulation
import Papers.PODC2012.WeakModelsModalLogic.PortExists
import Cslib.Foundations.Combinatorics.Matrix.Birkhoff

/-!
# Lemma 15 of Hella et al.

* `deg_eq_card_filter`: `deg` as a `Finset` card.
* `portEquivOfRegular`: for a `k`-regular graph, `Port G ≃ V × Fin k`.
* `lemma15`: every regular graph has a port numbering in which all nodes are bisimilar in
  `K_{+,+}(G, p)`.

The proof of Lemma 15 follows the paper: the edge set of the bipartite double cover of a
`k`-regular graph is a disjoint union of `k` perfect matchings. We obtain them from CSLib's
Birkhoff–König decomposition `Matrix.exists_perm_decomposition` applied to the adjacency matrix:
permutations `σ 0, …, σ (k-1)` of `V` such that the neighbours of `v` are exactly the distinct
nodes `σ c v`. The port numbering is `p((v, c)) = (σ c v, c)`, so `R(i,j) = ∅` for `i ≠ j`.
-/

namespace Podc.WeakModelsModalLogic

open Function

variable {V : Type*}

/-- With decidable adjacency on a finite type, `deg` is the size of a filtered `Finset`. -/
theorem deg_eq_card_filter [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    deg G v = (Finset.univ.filter (G.Adj v)).card := by
  rw [deg, Nat.card_eq_fintype_card, SimpleGraph.card_neighborSet_eq_degree,
    SimpleGraph.degree, SimpleGraph.neighborFinset_eq_filter]

section Regular

variable {G : SimpleGraph V} {k : ℕ}

/-- For a `k`-regular graph, the ports are pairs `(v, c)` with `c < k`. -/
noncomputable def portEquivOfRegular (hk : ∀ v, deg G v = k) : Port G ≃ V × Fin k where
  toFun x := (x.1, Fin.cast (hk x.1) x.2)
  invFun y := ⟨y.1, Fin.cast (hk y.1).symm y.2⟩
  left_inv := by rintro ⟨v, i⟩; rfl
  right_inv := by rintro ⟨v, c⟩; rfl

@[simp] theorem portEquivOfRegular_apply (hk : ∀ v, deg G v = k) (x : Port G) :
    portEquivOfRegular hk x = (x.1, Fin.cast (hk x.1) x.2) := rfl

@[simp] theorem portEquivOfRegular_symm_apply (hk : ∀ v, deg G v = k) (y : V × Fin k) :
    (portEquivOfRegular hk).symm y = ⟨y.1, Fin.cast (hk y.1).symm y.2⟩ := rfl

/-- The port numbering `p` of a `k`-regular graph read on `V × Fin k`. -/
noncomputable def PortNumbering.onProd (P : PortNumbering G) (hk : ∀ v, deg G v = k) :
    Equiv.Perm (V × Fin k) :=
  (portEquivOfRegular hk).symm.trans (P.p.trans (portEquivOfRegular hk))

/-- In a `k`-regular graph, `R(i,j) u v ↔ p((v, j)) = (u, i)` read on `V × Fin k`. -/
theorem PortNumbering.R_iff_onProd (P : PortNumbering G) (hk : ∀ v, deg G v = k)
    (i j : ℕ) (u v : V) :
    P.R i j u v ↔ ∃ (hi : i < k) (hj : j < k), P.onProd hk (v, ⟨j, hj⟩) = (u, ⟨i, hi⟩) := by
  simp only [PortNumbering.R, PortNumbering.onProd, Equiv.trans_apply, hk]
  constructor
  · rintro ⟨hj, hi, h⟩
    refine ⟨hi, hj, ?_⟩
    simp only [portEquivOfRegular_symm_apply, portEquivOfRegular_apply]
    have : (⟨v, Fin.cast (hk v).symm ⟨j, hj⟩⟩ : Port G) = ⟨v, ⟨j, hk v ▸ hj⟩⟩ := rfl
    rw [this, h]
    rfl
  · rintro ⟨hi, hj, h⟩
    refine ⟨hk v ▸ hj, hk u ▸ hi, ?_⟩
    rw [← Equiv.eq_symm_apply] at h
    simp only [portEquivOfRegular_symm_apply] at h
    have e1 : (⟨v, ⟨j, hk v ▸ hj⟩⟩ : Port G) = ⟨v, Fin.cast (hk v).symm ⟨j, hj⟩⟩ := rfl
    have e2 : (⟨u, ⟨i, hk u ▸ hi⟩⟩ : Port G) = ⟨u, Fin.cast (hk u).symm ⟨i, hi⟩⟩ := rfl
    rw [e1, e2, ← h]

end Regular

/-- Lemma 15 of [Hella et al.]. A regular graph has a port numbering `p` such that all nodes are
bisimilar in `K_{+,+}(G, p)`. -/
theorem lemma15 [Finite V] (G : SimpleGraph V) (k : ℕ) (hk : ∀ v, deg G v = k) :
    ∃ P : PortNumbering G, ∀ u v, P.BisimilarPP u v := by
  classical
  have : Fintype V := Fintype.ofFinite V
  -- The adjacency matrix is `k`-regular.
  let B : Matrix V V ℕ := fun u v => if G.Adj u v then 1 else 0
  have hdeg : ∀ u, (Finset.univ.filter (G.Adj u)).card = k := by
    intro u; rw [← hk u, deg_eq_card_filter]
  have hr : ∀ u, ∑ v, B u v = k := by
    intro u; simp only [B, Finset.sum_boole, Nat.cast_id]; exact hdeg u
  have hc : ∀ v, ∑ u, B u v = k := by
    intro v; simp only [B, Finset.sum_boole, Nat.cast_id]
    rw [← hdeg v]; congr 1; ext; simp [G.adj_comm]
  obtain ⟨σ, hσ⟩ := Matrix.exists_perm_decomposition B k hr hc
  have hadj : ∀ c u, G.Adj u (σ c u) := by
    intro c u
    have h := hσ u (σ c u)
    by_contra hn
    simp only [B, hn, ite_false] at h
    have := Finset.card_eq_zero.1 h.symm
    exact (Finset.eq_empty_iff_forall_notMem.1 this c) (by simp)
  have hcov : ∀ u v, G.Adj u v → ∃ c, σ c u = v := by
    intro u v h
    have h' := hσ u v
    simp only [B, h, ite_true] at h'
    obtain ⟨c, hc⟩ := Finset.card_pos.1 (by rw [← h']; exact one_pos)
    exact ⟨c, (Finset.mem_filter.1 hc).2⟩
  -- The permutation `(v, c) ↦ (σ c v, c)` of `V × Fin k`.
  let q : Equiv.Perm (V × Fin k) :=
    { toFun := fun y => (σ y.2 y.1, y.2)
      invFun := fun y => ((σ y.2).symm y.1, y.2)
      left_inv := fun y => by simp
      right_inv := fun y => by simp }
  let E := portEquivOfRegular hk
  let P : PortNumbering G :=
    { p := E.trans (q.trans E.symm)
      adj := fun x => by simpa [E, q] using hadj (Fin.cast (hk x.1) x.2) x.1
      cover := fun u v h => by
        obtain ⟨c, rfl⟩ := hcov u v h
        exact ⟨E.symm (u, c), rfl, by simp [E, q]⟩ }
  have hPq : P.onProd hk = q := by
    ext y <;> simp [PortNumbering.onProd, P, E]
  have hR : ∀ i j u v, P.R i j u v ↔ ∃ hi : i < k, j = i ∧ σ ⟨i, hi⟩ v = u := by
    intro i j u v
    rw [P.R_iff_onProd hk, hPq]
    constructor
    · rintro ⟨hi, hj, h⟩
      simp only [q, Equiv.coe_fn_mk, Prod.mk.injEq, Fin.mk.injEq] at h
      obtain ⟨h1, rfl⟩ := h
      exact ⟨hi, rfl, h1⟩
    · rintro ⟨hi, rfl, h⟩
      exact ⟨hi, hi, by simp [q, h]⟩
  refine ⟨P, fun u v => ⟨fun _ _ => True, fun v v' _ => ⟨by rw [hk, hk], ?_, ?_⟩, trivial⟩⟩
  · intro i j w h
    obtain ⟨hi, hji, -⟩ := (hR _ _ _ _).1 h
    exact ⟨(σ ⟨i, hi⟩).symm v', (hR _ _ _ _).2 ⟨hi, hji, by simp⟩, trivial⟩
  · intro i j w' h
    obtain ⟨hi, hji, -⟩ := (hR _ _ _ _).1 h
    exact ⟨(σ ⟨i, hi⟩).symm v, (hR _ _ _ _).2 ⟨hi, hji, by simp⟩, trivial⟩

end Podc.WeakModelsModalLogic
