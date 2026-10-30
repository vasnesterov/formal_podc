import Papers.PODC2013.AsyncRendezvousPoly.Main
import Papers.PODC2013.AsyncRendezvousPoly.Ports

/-!
# Theorem 3.1 in the port-labelled model

The abstract exploration family of `Explorer` is instantiated by port-local deterministic
procedures (`Ports.lean`): `R(k, v)` = the trajectory of procedure `A k` run for `P k` steps from
`v`. The hypothesis on `A` is the conclusion of Reingold's theorem (with the "visit all neighbours"
transformation, §2): `A k` traverses every edge of every simple connected port-labelled graph with
at most `k` nodes (`TraversesUpTo`). We take it as a hypothesis (the UXS "axiom").
-/

namespace Podc.AsyncRendezvousPoly

open Cslib.PortNumbering

/-- Procedure `A`, run for `L` steps, traverses every edge of every simple connected
port-labelled graph with at most `k` nodes, from every starting node. -/
def TraversesUpTo (A : Proc) (L k : ℕ) : Prop :=
  ∀ (W : Type) [Fintype W] (H : PNGraph W), H.IsSimple → H.toSimpleGraph.Connected →
    Fintype.card W ≤ k → ∀ w x y : W, H.toSimpleGraph.Adj x y →
      ∃ t < L, (walk H A w t = x ∧ walk H A w (t + 1) = y) ∨
        (walk H A w t = y ∧ walk H A w (t + 1) = x)

/-- Positive degrees in a connected simple port-labelled graph with at least two nodes. -/
theorem deg_pos {V : Type} [Nontrivial V] {G : PNGraph V}
    (hC : G.toSimpleGraph.Connected) (v : V) : 0 < G.deg v := by
  classical
  obtain ⟨u, hu⟩ := hC.preconnected.exists_adj_of_nontrivial v
  obtain ⟨i, hi, -⟩ := G.exists_port_of_adj hu
  omega

/-- The exploration family given by port-local procedures `A k` run for `P k` steps. -/
noncomputable def Explorer.ofProc {V : Type} [Fintype V] [Nontrivial V] (G : PNGraph V)
    (hS : G.IsSimple) (hC : G.toSimpleGraph.Connected) (A : ℕ → Proc) (P : ℕ → ℕ)
    (hP1 : ∀ k, 1 ≤ P k) (hcov : ∀ k, TraversesUpTo (A k) (P k) k) :
    Explorer G.toSimpleGraph P where
  R k v := ⟨P k, Podc.AsyncRendezvousPoly.walk G (A k) v⟩
  len_eq _ _ := rfl
  start _ _ := rfl
  walk k v i _ := by
    show G.toSimpleGraph.Adj (Podc.AsyncRendezvousPoly.walk G (A k) v i)
      (Podc.AsyncRendezvousPoly.walk G (A k) v (i + 1))
    rw [walk_succ]; exact G.adj_nbr hS (Nat.mod_lt _ (deg_pos hC _))
  covers k v hk := fun x y hxy => by
    obtain ⟨t, ht, h⟩ := hcov k V G hS hC hk v x y hxy
    exact ⟨t, ht, h⟩
  P_pos := hP1

/-- **Theorem 3.1** of [DPV13] in the port-labelled model. Let `A k` be deterministic port-local
procedures whose `P k`-step runs traverse all edges of all graphs of size `≤ k`, with `P`
non-decreasing, positive and polynomially bounded (Reingold). There is a polynomial
`Π(n, m) = C (n + m + 1)^d` such that two agents with distinct positive labels `L₁`, `L₂`,
starting at different nodes of any simple connected port-labelled graph of size `n` and executing
Algorithm RV-asynch-poly (built from `A`), meet, against every adversary, no later than the moment
one of them performs `Π(n, min(|L₁|, |L₂|))` edge traversals. -/
theorem theorem_3_1_ports (A : ℕ → Proc) (P : ℕ → ℕ) (hP : Monotone P) (hpoly : PolyBounded P)
    (hP1 : ∀ k, 1 ≤ P k) (hcov : ∀ k, TraversesUpTo (A k) (P k) k) :
    ∃ C d : ℕ, ∀ (V : Type) [Fintype V] [DecidableEq V] (G : PNGraph V)
      (hS : G.IsSimple) (hC : G.toSimpleGraph.Connected) (L₁ L₂ : ℕ), 0 < L₁ → 0 < L₂ →
      L₁ ≠ L₂ → ∀ (va vb : V) (hab : va ≠ vb) (Wa Wb : Walk),
      haveI : Nontrivial V := ⟨va, vb, hab⟩
      ∃ t, Meet ((Explorer.ofProc G hS hC A P hP1 hcov).route (modLabel L₁) va)
          ((Explorer.ofProc G hS hC A P hP1 hcov).route (modLabel L₂) vb) Wa Wb t ∧
        t ≤ Wa.τ (C * (Fintype.card V + min (binLen L₁) (binLen L₂) + 1) ^ d) ∧
        t ≤ Wb.τ (C * (Fintype.card V + min (binLen L₁) (binLen L₂) + 1) ^ d) := by
  obtain ⟨C, d, h⟩ := theorem_3_1 P hP hpoly
  refine ⟨C, d, fun V _ _ G hS hC L₁ L₂ h₁ h₂ hne va vb hab Wa Wb => ?_⟩
  have : Nontrivial V := ⟨va, vb, hab⟩
  exact h V G.toSimpleGraph hC _ L₁ L₂ h₁ h₂ hne va vb Wa Wb

end Podc.AsyncRendezvousPoly
