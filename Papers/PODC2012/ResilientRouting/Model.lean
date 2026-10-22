import Mathlib

-- CSLib candidate: static fast-failover forwarding model (`Pattern`, `FwdPath`, `Good`,
-- `IsResilient`, trajectory semantics `good_of` / `not_good_of_trap`).

/-!
# Resilient routing tables: the model

Feigenbaum, Godfrey, Panda, Schapira, Shenker, Singla, *Brief announcement: On the resilience of
routing tables*, PODC 2012 (full version arXiv:1207.3732v2), Section 2.

The network is a simple graph `G` with a destination `d`. A *forwarding pattern* gives every node
`i` a function that maps the link on which a packet arrived (represented by the neighbour `u` it
came from) and the set of live incident links (represented by the set `A` of neighbours over live
links) to an outgoing incident link (represented by a neighbour of `i`). If the chosen link is down
the packet is lost.

For a failure set `F` (a set of edges), a *forwarding path* is a walk `x₀ x₁ … x_k` (`k ≥ 1`) in
`G \ F` such that every interior vertex `x_j` (`0 < j < k`) is not the destination and forwards
`x_{j-1} → x_j` to `x_{j+1}`. The first hop is not constrained (the paper does not model the
source's choice). The destination is a sink: a packet is not forwarded any further once it reaches
`d` (the paper puts no constraint at `d`, which makes every pattern loop; see `literal_K2`).

A pattern is *good* for `F` if (1) every node connected to `d` in `G \ F` has a forwarding path
to `d`, and (2) no forwarding path repeats a directed edge (the paper's notion of a forwarding
loop, Section 4). It is *t-resilient* if it is good for every `F ⊆ E` with `|F| ≤ t`, and
*perfectly resilient* if it is good for every `F ⊆ E`.

Besides the definitions, this file contains the trajectory semantics used in the proofs:
a forwarding path is the beginning of the deterministic trajectory `δ, nxt δ, nxt² δ, …` of
its first dart, so loop-freedom follows from termination of trajectories (`good_of`), and a
"trap" (a set of darts closed under forwarding and avoiding `d`) refutes condition (1)
(`not_reach_of_trap`).
-/

namespace Podc.ResilientRouting

open SimpleGraph

variable {V : Type*}

/-- A forwarding pattern on `G` (the paper's `f^d = (f^d_1, …, f^d_n)`): `next i A u` is the
neighbour to which node `i` sends a packet that arrived from `u`, when `A` is the set of
neighbours of `i` over live links. As in the paper (`f^d_i : E_i × 2^{E_i} → E_i`), the output is
an incident link (it may be a failed one: then the packet is lost). The function at `d` is never
used. -/
structure Pattern (G : SimpleGraph V) where
  /-- The forwarding function of node `i`. -/
  next : V → Set V → V → V
  /-- The output is an incident link. -/
  adj_next : ∀ i A u, G.Adj i u → G.Adj i (next i A u)

/-- The link `uv` exists and has not failed. -/
def Live (G : SimpleGraph V) (F : Set (Sym2 V)) (u v : V) : Prop := G.Adj u v ∧ s(u, v) ∉ F

/-- The local view of node `i` in failure scenario `F`: its neighbours over live links. -/
def view (G : SimpleGraph V) (F : Set (Sym2 V)) (i : V) : Set V := {u | Live G F i u}

/-- Forwarding paths in failure scenario `F`, as lists of vertices `[x₀, x₁, …, x_k]`, `k ≥ 1`. -/
inductive FwdPath (G : SimpleGraph V) (d : V) (f : Pattern G) (F : Set (Sym2 V)) : List V → Prop
  | single {u v : V} : Live G F u v → FwdPath G d f F [u, v]
  | cons {u v w : V} {l : List V} : Live G F u v → v ≠ d → f.next v (view G F v) u = w →
      FwdPath G d f F (v :: w :: l) → FwdPath G d f F (u :: v :: w :: l)

/-- The pattern `f` behaves well in failure scenario `F`: (1) every node `i ≠ d` that is connected
to `d` in `G \ F` has a forwarding path to `d`, and (2) no forwarding path repeats a directed
edge. -/
def Good (G : SimpleGraph V) (d : V) (f : Pattern G) (F : Set (Sym2 V)) : Prop :=
  (∀ i, i ≠ d → (G.deleteEdges F).Reachable i d →
      ∃ l : List V, FwdPath G d f F (i :: l) ∧ (i :: l).getLast (List.cons_ne_nil _ _) = d) ∧
  ∀ l : List V, FwdPath G d f F l → (l.zip l.tail).Nodup

/-- `f` is `t`-resilient: good for every failure set `F ⊆ E` with `|F| ≤ t`. -/
def IsResilient (G : SimpleGraph V) (d : V) (f : Pattern G) (t : ℕ∞) : Prop :=
  ∀ F : Set (Sym2 V), F ⊆ G.edgeSet → F.encard ≤ t → Good G d f F

/-- `f` is perfectly resilient: good for every failure set `F ⊆ E`. -/
def PerfectlyResilient (G : SimpleGraph V) (d : V) (f : Pattern G) : Prop :=
  ∀ F : Set (Sym2 V), F ⊆ G.edgeSet → Good G d f F

theorem PerfectlyResilient.isResilient {G : SimpleGraph V} {d : V} {f : Pattern G}
    (h : PerfectlyResilient G d f) (t : ℕ∞) : IsResilient G d f t :=
  fun F hF _ => h F hF

theorem Live.symm {G : SimpleGraph V} {F : Set (Sym2 V)} {u v : V} (h : Live G F u v) :
    Live G F v u :=
  ⟨h.1.symm, by rw [Sym2.eq_swap]; exact h.2⟩

/-- A set of vertices closed under live links that contains `i` but not `d`: `i` is cut off. -/
theorem not_reachable_of_closed {G : SimpleGraph V} {F : Set (Sym2 V)} (S : Set V) {i d : V}
    (hi : i ∈ S) (hd : d ∉ S) (hS : ∀ x y, x ∈ S → Live G F x y → y ∈ S) :
    ¬ (G.deleteEdges F).Reachable i d := by
  rintro ⟨p⟩
  have key : ∀ {x y : V} (p : (G.deleteEdges F).Walk x y), x ∈ S → y ∈ S := by
    intro x y p
    induction p with
    | nil => exact id
    | cons h _ ih => exact fun hx => ih (hS _ _ hx (deleteEdges_adj.1 h))
  exact hd (key p hi)

/-! ### Trajectory semantics -/

section Traj

variable (G : SimpleGraph V) (d : V) (f : Pattern G) (F : Set (Sym2 V))

/-- The dart following the dart `δ = (u, v)` (a packet at `v` that came from `u`). -/
def nxt (δ : V × V) : V × V := (δ.2, f.next δ.2 (view G F δ.2) δ.1)

/-- The trajectory of `δ` stops after `δ`: the packet is delivered, or forwarded on a dead link. -/
def Stops (δ : V × V) : Prop := δ.2 = d ∨ ¬ Live G F (nxt G f F δ).1 (nxt G f F δ).2

/-- The trajectory of `δ` reaches the destination. -/
inductive Delivers : V × V → Prop
  | base {δ : V × V} : δ.2 = d → Delivers δ
  | step {δ : V × V} : ¬ Stops G d f F δ → Delivers (nxt G f F δ) → Delivers δ

/-- The trajectory of `δ` stops. -/
inductive Terminates : V × V → Prop
  | base {δ : V × V} : Stops G d f F δ → Terminates δ
  | step {δ : V × V} : Terminates (nxt G f F δ) → Terminates δ

/-- The vertex list of the first `n + 1` darts of the trajectory of `δ`. -/
def walkOf : V × V → ℕ → List V
  | δ, 0 => [δ.1, δ.2]
  | δ, n + 1 => δ.1 :: walkOf (nxt G f F δ) n

variable {G d f F}

theorem Delivers.of_next {x v y : V} (hv : v ≠ d) (hn : f.next v (view G F v) x = y)
    (hl : Live G F v y) (h : Delivers G d f F (v, y)) : Delivers G d f F (x, v) := by
  refine .step ?_ ?_
  · simp only [Stops, nxt, hn, not_or, not_not]; exact ⟨hv, hl⟩
  · simp only [nxt, hn]; exact h

/-- Cut-off criterion with an explicit list `D` of dead links (for concrete networks). -/
theorem not_reachable_of_dead (S : Finset V) (D : List (V × V))
    (hD : ∀ p ∈ D, ¬ Live G F p.1 p.2) (hcl : ∀ x ∈ S, ∀ y, G.Adj x y → y ∈ S ∨ (x, y) ∈ D)
    {i : V} (hi : i ∈ S) (hd : d ∉ S) : ¬ (G.deleteEdges F).Reachable i d := by
  refine not_reachable_of_closed (S : Set V) hi (by simpa using hd) fun x y hx hl => ?_
  rcases hcl x hx y hl.1 with h | h
  · exact h
  · exact absurd hl (hD _ h)

theorem Delivers.terminates {δ : V × V} (h : Delivers G d f F δ) : Terminates G d f F δ := by
  induction h with
  | base h => exact .base (Or.inl h)
  | step _ _ ih => exact .step ih

theorem nxt_fst (δ : V × V) : (nxt G f F δ).1 = δ.2 := rfl

theorem walkOf_head (δ : V × V) (n : ℕ) : ∃ l, walkOf G f F δ n = δ.1 :: δ.2 :: l := by
  cases n with
  | zero => exact ⟨[], rfl⟩
  | succ n =>
    obtain ⟨l, hl⟩ := walkOf_head (nxt G f F δ) n
    exact ⟨_, by rw [walkOf, hl]; rfl⟩

theorem walkOf_getLast (δ : V × V) (n : ℕ) (h) :
    (walkOf G f F δ n).getLast h = ((nxt G f F)^[n] δ).2 := by
  induction n generalizing δ with
  | zero => rfl
  | succ n ih =>
    obtain ⟨l, hl⟩ := walkOf_head (G := G) (f := f) (F := F) (nxt G f F δ) n
    simp only [walkOf]
    rw [List.getLast_cons (by simp [hl]), ih, Function.iterate_succ_apply]

theorem walkOf_darts (δ : V × V) (n : ℕ) :
    (walkOf G f F δ n).zip (walkOf G f F δ n).tail =
      (List.range (n + 1)).map (fun k => (nxt G f F)^[k] δ) := by
  induction n generalizing δ with
  | zero => rfl
  | succ n ih =>
    obtain ⟨l, hl⟩ := walkOf_head (G := G) (f := f) (F := F) (nxt G f F δ) n
    have ih' := ih (nxt G f F δ)
    rw [hl] at ih'
    simp only [List.tail_cons] at ih'
    simp only [walkOf]
    rw [hl, List.tail_cons, List.zip_cons_cons, ih', List.range_succ_eq_map (n := n + 1), List.map_cons,
      List.map_map]
    rfl

/-- Every forwarding path is the beginning of a trajectory. -/
theorem FwdPath.exists_walkOf {l : List V} (h : FwdPath G d f F l) :
    ∃ δ n, l = walkOf G f F δ n ∧ (∀ k ≤ n, Live G F ((nxt G f F)^[k] δ).1 ((nxt G f F)^[k] δ).2) ∧
      ∀ k < n, ((nxt G f F)^[k] δ).2 ≠ d := by
  induction h with
  | @single u v h => exact ⟨(u, v), 0, rfl, by simpa using h, by simp⟩
  | @cons u v w l hl hv hw _ ih =>
    obtain ⟨δ, n, he, hlive, hne⟩ := ih
    have hδ : δ = nxt G f F (u, v) := by
      obtain ⟨l', hl'⟩ := walkOf_head (G := G) (f := f) (F := F) δ n
      rw [hl'] at he
      simp only [List.cons.injEq] at he
      obtain ⟨h1, h2, -⟩ := he
      ext <;> simp [nxt, ← h1, ← h2, hw]
    refine ⟨(u, v), n + 1, by rw [walkOf, ← hδ, ← he], fun k hk => ?_, fun k hk => ?_⟩
    · cases k with
      | zero => exact hl
      | succ k => rw [Function.iterate_succ_apply, ← hδ]; exact hlive k (by omega)
    · cases k with
      | zero => exact hv
      | succ k => rw [Function.iterate_succ_apply, ← hδ]; exact hne k (by omega)

/-- A trajectory that stays live is a forwarding path. -/
theorem fwdPath_walkOf (δ : V × V) (n : ℕ)
    (hlive : ∀ k ≤ n, Live G F ((nxt G f F)^[k] δ).1 ((nxt G f F)^[k] δ).2)
    (hne : ∀ k < n, ((nxt G f F)^[k] δ).2 ≠ d) : FwdPath G d f F (walkOf G f F δ n) := by
  induction n generalizing δ with
  | zero => exact .single (by simpa using hlive 0 le_rfl)
  | succ n ih =>
    have h := ih (nxt G f F δ) (fun k hk => hlive (k + 1) (by omega))
      (fun k hk => hne (k + 1) (by omega))
    obtain ⟨l, hl⟩ := walkOf_head (G := G) (f := f) (F := F) (nxt G f F δ) n
    rw [hl] at h
    simp only [walkOf, hl]
    exact .cons (hlive 0 (by omega)) (hne 0 (by omega)) rfl h

theorem Delivers.exists_fwdPath {δ : V × V} (h : Delivers G d f F δ) (hδ : Live G F δ.1 δ.2) :
    ∃ l, FwdPath G d f F (δ.1 :: l) ∧ (δ.1 :: l).getLast (List.cons_ne_nil _ _) = d := by
  -- extract the delivery time
  have key : ∃ n, (∀ k < n, ¬ Stops G d f F ((nxt G f F)^[k] δ)) ∧ ((nxt G f F)^[n] δ).2 = d := by
    clear hδ
    induction h with
    | base h => exact ⟨0, by simp, h⟩
    | @step δ hs _ ih =>
      obtain ⟨n, h1, h2⟩ := ih
      refine ⟨n + 1, fun k hk => ?_, by rwa [Function.iterate_succ_apply]⟩
      cases k with
      | zero => exact hs
      | succ k => rw [Function.iterate_succ_apply]; exact h1 k (by omega)
  obtain ⟨n, h1, h2⟩ := key
  have hlive : ∀ k ≤ n, Live G F ((nxt G f F)^[k] δ).1 ((nxt G f F)^[k] δ).2 := by
    intro k hk
    induction k with
    | zero => exact hδ
    | succ k ih =>
      have := h1 k (by omega)
      simp only [Stops, not_or, not_not] at this
      rw [Function.iterate_succ_apply']
      exact this.2
  have hne : ∀ k < n, ((nxt G f F)^[k] δ).2 ≠ d := fun k hk => by
    have := h1 k hk
    simp only [Stops, not_or] at this
    exact this.1
  obtain ⟨l, hl⟩ := walkOf_head (G := G) (f := f) (F := F) δ n
  refine ⟨δ.2 :: l, ?_, ?_⟩
  · rw [← hl]; exact fwdPath_walkOf δ n hlive hne
  · have := walkOf_getLast (G := G) (f := f) (F := F) δ n (by simp [hl])
    simp only [hl] at this
    rw [this, h2]

/-- If all trajectories terminate, no forwarding path repeats a dart. -/
theorem FwdPath.nodup_of_terminates (hT : ∀ δ, Terminates G d f F δ) {l : List V}
    (h : FwdPath G d f F l) : (l.zip l.tail).Nodup := by
  obtain ⟨δ, n, rfl, hlive, hne⟩ := h.exists_walkOf
  rw [walkOf_darts]
  refine (List.nodup_range).map_on fun i hi j hj hij => ?_
  simp only [List.mem_range] at hi hj
  by_contra hne'
  -- wlog i < j
  have main : ∀ i j, i < j → j ≤ n → (nxt G f F)^[i] δ = (nxt G f F)^[j] δ → False := by
    intro i j hij hjn heq
    -- no stop at any time
    have back : ∀ m, ∃ m' < j, (nxt G f F)^[m] δ = (nxt G f F)^[m'] δ := by
      intro m
      induction m using Nat.strong_induction_on with
      | _ m ih =>
        by_cases hm : m < j
        · exact ⟨m, hm, rfl⟩
        · obtain ⟨m', hm', he⟩ := ih (m - j + i) (by omega)
          refine ⟨m', hm', ?_⟩
          rw [← he]
          conv_lhs => rw [show m = (m - j) + j by omega, Function.iterate_add_apply, ← heq,
            ← Function.iterate_add_apply]
    have nostop : ∀ m, ¬ Stops G d f F ((nxt G f F)^[m] δ) := by
      intro m
      obtain ⟨m, hm, he⟩ := back m
      rw [he]
      simp only [Stops, not_or, not_not]
      refine ⟨hne m (by omega), ?_⟩
      rw [← Function.iterate_succ_apply' (nxt G f F)]
      exact hlive (m + 1) (by omega)
    -- but the trajectory terminates
    have ht := hT δ
    have : ∀ δ', Terminates G d f F δ' → ∀ m, δ' = (nxt G f F)^[m] δ → False := by
      intro δ' ht'
      induction ht' with
      | base hs => intro m hm; exact nostop m (hm ▸ hs)
      | step _ ih => intro m hm; exact ih (m + 1) (by rw [hm, Function.iterate_succ_apply'])
    exact this δ ht 0 rfl
  rcases Nat.lt_or_gt_of_ne hne' with h' | h'
  · exact main i j h' (by omega) hij
  · exact main j i h' (by omega) hij.symm

/-- Reduction: a scenario is good if all trajectories terminate and every node connected to `d`
has a live first hop whose trajectory is delivered. -/
theorem good_of (hT : ∀ δ, Terminates G d f F δ)
    (hD : ∀ i, i ≠ d → (G.deleteEdges F).Reachable i d →
      ∃ y, Live G F i y ∧ Delivers G d f F (i, y)) : Good G d f F := by
  refine ⟨fun i hi hr => ?_, fun l hl => hl.nodup_of_terminates hT⟩
  obtain ⟨y, hy, hdel⟩ := hD i hi hr
  exact hdel.exists_fwdPath hy

/-- A *trap*: a set of darts avoiding `d` and closed under live forwarding. No forwarding path that
starts in a trap reaches `d`. -/
theorem not_reach_of_trap (S : Set (V × V))
    (hS : ∀ δ ∈ S, Live G F δ.1 δ.2 → δ.2 ≠ d ∧
      (Live G F (nxt G f F δ).1 (nxt G f F δ).2 → nxt G f F δ ∈ S))
    {u v : V} {l : List V} (h : FwdPath G d f F (u :: v :: l)) (huv : (u, v) ∈ S) :
    (u :: v :: l).getLast (List.cons_ne_nil _ _) ≠ d := by
  obtain ⟨δ, n, he, hlive, -⟩ := h.exists_walkOf
  have hδ : δ = (u, v) := by
    obtain ⟨l', hl'⟩ := walkOf_head (G := G) (f := f) (F := F) δ n
    rw [hl'] at he
    simp only [List.cons.injEq] at he
    ext <;> simp [he.1, he.2.1]
  subst hδ
  have mem : ∀ k ≤ n, (nxt G f F)^[k] (u, v) ∈ S := by
    intro k hk
    induction k with
    | zero => exact huv
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact (hS _ (ih (by omega)) (hlive k (by omega))).2
        (by rw [← Function.iterate_succ_apply' (nxt G f F)]; exact hlive (k + 1) hk)
  have := walkOf_getLast (G := G) (f := f) (F := F) (u, v) n (by simp [← he])
  simp only [← he] at this
  rw [this]
  exact (hS _ (mem n le_rfl) (hlive n le_rfl)).1

/-- Condition (1) refuted by a trap: if `i ≠ d` is connected to `d`, but every live first hop of
`i` lies in a trap, then the scenario is not good. -/
theorem not_good_of_trap (S : Set (V × V))
    (hS : ∀ δ ∈ S, Live G F δ.1 δ.2 → δ.2 ≠ d ∧
      (Live G F (nxt G f F δ).1 (nxt G f F δ).2 → nxt G f F δ ∈ S))
    {i : V} (hi : i ≠ d) (hr : (G.deleteEdges F).Reachable i d)
    (hfirst : ∀ y, Live G F i y → (i, y) ∈ S) : ¬ Good G d f F := by
  rintro ⟨h1, -⟩
  obtain ⟨l, hl, hlast⟩ := h1 i hi hr
  cases hl with
  | single h => exact not_reach_of_trap S hS (.single h) (hfirst _ h) hlast
  | cons h hv hw hp => exact not_reach_of_trap S hS (.cons h hv hw hp) (hfirst _ h) hlast

end Traj

end Podc.ResilientRouting
