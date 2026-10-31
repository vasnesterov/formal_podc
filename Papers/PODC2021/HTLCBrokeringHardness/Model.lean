/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib

/-!
# Transaction graphs, brokering and adequate leader sets

Model of §§2–3 of E. Chan, M. Lesani, *Brief Announcement: Brokering with Hashed Timelock Contracts is
NP-Hard*, PODC 2021.

A transaction graph has parties `P` and contracts (edges) `E`; each contract transfers `amt e` units of
asset `asset e` from `src e` to `dst e`. Every party `p` initially owns `own p a` units of asset `a`.

HTLCP edge-creation rules with brokering (§§2–3): a contract is created by its sender, one at a time.
* A **leader** may create its outgoing contracts at any time; a **follower** only once *all* its
  incoming contracts have been created.
* The sender must (tentatively) own the transferred amount: its initial endowment plus everything it
  received on created incoming contracts minus everything it already escrowed on created outgoing
  contracts (the "master contract" bookkeeping of §3).

A leader set `L` is **adequate** if some order of creations following these rules creates every
contract (`Adequate`). A **minimum leader set** is an adequate leader set of minimum cardinality.

Besides the definitions this file contains the generic tools used for the reduction
(`Reachable.closed`, `Reachable.balance`, `Adequate.first_hit`, `Reachable.batch`) and the §3 claims
about graphs without brokering: there, the adequate leader sets are exactly the feedback vertex sets
(`adequate_iff_isFVS`); with brokering, every adequate leader set is still a feedback vertex set
(`Adequate.isFVS`).
-/

namespace Podc.HTLCBrokeringHardness

open Finset

/-- A transaction graph: contracts `E` between parties `P`, each moving `amt e` units of asset
`asset e` from `src e` to `dst e`. Parallel contracts are allowed. -/
structure TxGraph (P E A : Type*) where
  /-- Sender of a contract. -/
  src : E → P
  /-- Receiver of a contract. -/
  dst : E → P
  /-- Asset (blockchain) of a contract. -/
  asset : E → A
  /-- Amount transferred by a contract. -/
  amt : E → ℕ

namespace TxGraph

variable {P E A : Type*} [DecidableEq P] [DecidableEq A] [DecidableEq E] (G : TxGraph P E A)

/-- Amount of asset `a` that party `p` receives on the contracts of `S`. -/
def inflow (S : Finset E) (p : P) (a : A) : ℕ :=
  ∑ e ∈ S with G.dst e = p ∧ G.asset e = a, G.amt e

/-- Amount of asset `a` that party `p` sends on the contracts of `S`. -/
def outflow (S : Finset E) (p : P) (a : A) : ℕ :=
  ∑ e ∈ S with G.src e = p ∧ G.asset e = a, G.amt e

/-- A party is a *broker* (§3) if it has an incoming and an outgoing contract on the same asset. -/
def IsBroker (p : P) : Prop :=
  ∃ e e', G.dst e = p ∧ G.src e' = p ∧ G.asset e = G.asset e'

variable (own : P → A → ℕ) (L : Finset P)

/-- `p` may create contracts in state `S` (set of created contracts): it is a leader, or all its
incoming contracts have been created. -/
def Allowed (S : Finset E) (p : P) : Prop :=
  p ∈ L ∨ ∀ e, G.dst e = p → e ∈ S

/-- Contract `e` can be created in state `S`. -/
def Enabled (S : Finset E) (e : E) : Prop :=
  e ∉ S ∧ G.Allowed L S (G.src e) ∧
    G.outflow S (G.src e) (G.asset e) + G.amt e ≤ own (G.src e) (G.asset e) + G.inflow S (G.src e) (G.asset e)

/-- One creation step. -/
def Step (S S' : Finset E) : Prop :=
  ∃ e, G.Enabled own L S e ∧ S' = insert e S

/-- `S` is the set of created contracts after some execution from the empty state. -/
def Reachable (S : Finset E) : Prop :=
  Relation.ReflTransGen (G.Step own L) ∅ S

/-- §3: the leader set `L` is *adequate* if the HTLCP edge-creation rules can create all edges. -/
def Adequate [Fintype E] : Prop :=
  G.Reachable own L Finset.univ

/-- §3: a *minimum leader set*: adequate and of minimum cardinality among adequate leader sets. -/
def IsMinimumLeaderSet [Fintype E] : Prop :=
  G.Adequate own L ∧ ∀ L' : Finset P, G.Adequate own L' → L.card ≤ L'.card

/-- Edge relation of the subgraph induced by the followers (non-leaders). -/
def FollowerEdge (u v : P) : Prop :=
  u ∉ L ∧ v ∉ L ∧ ∃ e, G.src e = u ∧ G.dst e = v

/-- `L` is a *feedback vertex set*: removing `L` leaves the graph acyclic. -/
def IsFVS : Prop :=
  ∀ u, ¬ Relation.TransGen (G.FollowerEdge L) u u

/-- Total amount of asset `a` that `p` sends in the whole graph. -/
def outTotal [Fintype E] (p : P) (a : A) : ℕ := G.outflow Finset.univ p a

variable {G own L}

/-! ### Flows -/

lemma inflow_insert {S : Finset E} {e : E} (he : e ∉ S) (p : P) (a : A) :
    G.inflow (insert e S) p a = G.inflow S p a + if G.dst e = p ∧ G.asset e = a then G.amt e else 0 := by
  unfold inflow; rw [Finset.filter_insert]; split_ifs with h
  · rw [Finset.sum_insert (by simp [he]), add_comm]
  · simp

lemma outflow_insert {S : Finset E} {e : E} (he : e ∉ S) (p : P) (a : A) :
    G.outflow (insert e S) p a = G.outflow S p a + if G.src e = p ∧ G.asset e = a then G.amt e else 0 := by
  unfold outflow; rw [Finset.filter_insert]; split_ifs with h
  · rw [Finset.sum_insert (by simp [he]), add_comm]
  · simp

omit [DecidableEq E] in
lemma inflow_mono {S S' : Finset E} (h : S ⊆ S') (p : P) (a : A) : G.inflow S p a ≤ G.inflow S' p a :=
  Finset.sum_le_sum_of_subset (Finset.filter_subset_filter _ h)

omit [DecidableEq E] in
lemma outflow_mono {S S' : Finset E} (h : S ⊆ S') (p : P) (a : A) :
    G.outflow S p a ≤ G.outflow S' p a :=
  Finset.sum_le_sum_of_subset (Finset.filter_subset_filter _ h)

omit [DecidableEq E] in
lemma amt_le_outflow {S : Finset E} {e : E} (he : e ∈ S) : G.amt e ≤ G.outflow S (G.src e) (G.asset e) :=
  Finset.single_le_sum (f := G.amt) (fun _ _ => Nat.zero_le _) (by simp [he])

/-- Flows as sums over an explicit finset of candidate contracts. -/
lemma sum_filter_eq_of_iff {S T : Finset E} {Q : E → Prop} [DecidablePred Q] (f : E → ℕ)
    (hT : ∀ e, Q e ↔ e ∈ T) : ∑ e ∈ S with Q e, f e = ∑ e ∈ T, if e ∈ S then f e else 0 := by
  rw [Finset.sum_filter, ← Finset.sum_filter, ← Finset.sum_filter]
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext e; simp [hT, and_comm]

/-! ### Invariants of executions -/

omit [DecidableEq P] [DecidableEq A] [DecidableEq E] in
lemma Allowed.mono {S S' : Finset E} {p : P} (h : G.Allowed L S p) (hS : S ⊆ S') : G.Allowed L S' p :=
  h.imp id fun h e he => hS (h e he)

/-- Every created contract was created by an allowed sender. -/
lemma Reachable.closed {S : Finset E} (hS : G.Reachable own L S) {e : E} (he : e ∈ S) :
    G.Allowed L S (G.src e) := by
  induction hS generalizing e with
  | refl => simp at he
  | tail _ hst ih =>
    obtain ⟨e', ⟨-, hal, -⟩, rfl⟩ := hst
    rcases Finset.mem_insert.1 he with rfl | he
    · exact hal.mono (Finset.subset_insert _ _)
    · exact (ih he).mono (Finset.subset_insert _ _)

/-- Nobody ever escrows more than it (tentatively) owns. -/
lemma Reachable.balance {S : Finset E} (hS : G.Reachable own L S) (p : P) (a : A) :
    G.outflow S p a ≤ own p a + G.inflow S p a := by
  induction hS with
  | refl => simp [outflow]
  | tail _ hst ih =>
    obtain ⟨e, ⟨he, -, hpay⟩, rfl⟩ := hst
    rw [outflow_insert he, inflow_insert he]
    by_cases h : G.src e = p ∧ G.asset e = a
    · obtain ⟨rfl, rfl⟩ := h; rw [ite_eq_left ⟨rfl, rfl⟩]; split_ifs <;> omega
    · rw [ite_eq_right h]; split_ifs <;> omega

-- CSLib candidate (generic monotone reachability tool)
/-- **First hit.** If `L` is adequate and `T` is a nonempty set of contracts, then some reachable
state avoiding `T` enables a contract of `T` (consider the first creation of a contract of `T`). -/
lemma Adequate.first_hit [Fintype E] (hL : G.Adequate own L) {T : Finset E} (hT : T.Nonempty) :
    ∃ S, G.Reachable own L S ∧ Disjoint S T ∧ ∃ e ∈ T, G.Enabled own L S e := by
  suffices ∀ S', G.Reachable own L S' → ¬ Disjoint S' T →
      ∃ S, G.Reachable own L S ∧ Disjoint S T ∧ ∃ e ∈ T, G.Enabled own L S e from
    this _ hL (fun h => hT.elim fun e he => Finset.disjoint_left.1 h (Finset.mem_univ e) he)
  intro S' hS' hd
  induction hS' with
  | refl => simp at hd
  | @tail S S'' hreach hst ih =>
    by_cases hdS : Disjoint S T
    · obtain ⟨e, hen, rfl⟩ := hst
      refine ⟨S, hreach, hdS, e, ?_, hen⟩
      by_contra heT
      exact hd (Finset.disjoint_insert_left.2 ⟨heT, hdS⟩)
    · exact ih hdS

/-- **Batch creation.** From a reachable state `S`, a set `A'` of new contracts can be created if
their senders are allowed in `S` and every sender can pay, in each asset it sends in `A'`, for all of its
contracts of `S ∪ A'` from what it owns in `S`. -/
lemma Reachable.batch {S A' : Finset E} (hS : G.Reachable own L S) (hdis : Disjoint A' S)
    (hal : ∀ e ∈ A', G.Allowed L S (G.src e))
    (hpay : ∀ e ∈ A', G.outflow (S ∪ A') (G.src e) (G.asset e) ≤
      own (G.src e) (G.asset e) + G.inflow S (G.src e) (G.asset e)) :
    G.Reachable own L (S ∪ A') := by
  suffices ∀ B ⊆ A', G.Reachable own L (S ∪ B) from this A' le_rfl
  intro B hB
  induction B using Finset.induction_on with
  | empty => simpa using hS
  | @insert e B heB ih =>
    have hBA : B ⊆ A' := (Finset.subset_insert _ _).trans hB
    have heA : e ∈ A' := hB (Finset.mem_insert_self _ _)
    have heS : e ∉ S ∪ B := by
      simp only [Finset.mem_union, not_or]
      exact ⟨Finset.disjoint_left.1 hdis heA, heB⟩
    refine Relation.ReflTransGen.tail (ih hBA) ⟨e, ⟨heS, (hal e heA).mono Finset.subset_union_left, ?_⟩,
      by rw [Finset.union_insert]⟩
    have h1 : G.outflow (insert e (S ∪ B)) (G.src e) (G.asset e) ≤ G.outflow (S ∪ A') (G.src e) (G.asset e) :=
      outflow_mono (Finset.insert_subset (Finset.mem_union_right _ heA)
        (Finset.union_subset_union le_rfl hBA)) _ _
    rw [outflow_insert heS, ite_eq_left ⟨rfl, rfl⟩] at h1
    have h2 := hpay e heA
    have h3 := inflow_mono (G := G) (Finset.subset_union_left (s₁ := S) (s₂ := B)) (G.src e) (G.asset e)
    omega

-- CSLib candidate
/-- `Reachable.batch` phrased with the target state `S' ⊇ S`. -/
lemma Reachable.batch' {S S' : Finset E} (hS : G.Reachable own L S) (hSS : S ⊆ S')
    (hal : ∀ e ∈ S', e ∉ S → G.Allowed L S (G.src e))
    (hpay : ∀ e ∈ S', e ∉ S → G.outflow S' (G.src e) (G.asset e) ≤
      own (G.src e) (G.asset e) + G.inflow S (G.src e) (G.asset e)) :
    G.Reachable own L S' := by
  have := hS.batch (A' := S' \ S) Finset.sdiff_disjoint
    (fun e he => hal e (Finset.mem_sdiff.1 he).1 (Finset.mem_sdiff.1 he).2)
    (by rw [Finset.union_sdiff_of_subset hSS]
        exact fun e he => hpay e (Finset.mem_sdiff.1 he).1 (Finset.mem_sdiff.1 he).2)
  rwa [Finset.union_sdiff_of_subset hSS] at this

/-- More leaders can only help. -/
lemma Reachable.mono_leaders {L' : Finset P} (hLL : L ⊆ L') {S : Finset E} (hS : G.Reachable own L S) :
    G.Reachable own L' S := by
  induction hS with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hst ih =>
    obtain ⟨e, ⟨he, hal, hpay⟩, rfl⟩ := hst
    exact ih.tail ⟨e, ⟨he, hal.imp (fun h => hLL h) id, hpay⟩, rfl⟩

lemma Adequate.mono [Fintype E] {L' : Finset P} (hLL : L ⊆ L') (h : G.Adequate own L) :
    G.Adequate own L' :=
  Reachable.mono_leaders hLL h

/-- In an adequate execution every party ends with a nonnegative balance in every asset. -/
lemma Adequate.outTotal_le [Fintype E] (h : G.Adequate own L) (p : P) (a : A) :
    G.outTotal p a ≤ own p a + G.inflow Finset.univ p a :=
  Reachable.balance h p a

/-! ### Section 3: leader sets and feedback vertex sets -/

/-- §3: "It is always necessary that the leader set forms a feedback vertex set" (with or without
brokering, for any initial endowment). -/
theorem Adequate.isFVS [Fintype E] [Fintype P] (h : G.Adequate own L) : G.IsFVS L := by
  classical
  intro u hu
  -- the vertices of a follower cycle through `u`
  set C : Finset P := Finset.univ.filter fun v =>
    Relation.TransGen (G.FollowerEdge L) u v ∧ Relation.TransGen (G.FollowerEdge L) v u
  -- every vertex of `C` has an incoming contract from a vertex of `C`
  have hpred : ∀ v ∈ C, ∃ e, G.dst e = v ∧ G.src e ∈ C ∧ G.src e ∉ L := by
    intro v hv
    simp only [C, Finset.mem_filter, Finset.mem_univ, true_and] at hv
    obtain ⟨huv, hvu⟩ := hv
    rcases Relation.TransGen.tail'_iff.1 huv with ⟨x, hux, hxv⟩
    obtain ⟨hxL, -, e, rfl, rfl⟩ := hxv
    refine ⟨e, rfl, ?_, hxL⟩
    simp only [C, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨?_, Relation.TransGen.head ⟨hxL, ?_, e, rfl, rfl⟩ hvu⟩
    · rcases Relation.reflTransGen_iff_eq_or_transGen.1 hux with h | h
      · rw [h]; exact hu
      · exact h
    · exact (Relation.TransGen.head'_iff.1 hvu).elim fun _ h => h.1.1
  have huC : u ∈ C := by simp [C, hu]
  obtain ⟨e₀, -, he₀C, -⟩ := hpred u huC
  obtain ⟨S, -, hdis, e, heT, -, hal, -⟩ :=
    h.first_hit (T := Finset.univ.filter fun e => G.src e ∈ C) ⟨e₀, by simp [he₀C]⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at heT
  obtain ⟨e', he'd, he'C, he'L⟩ := hpred _ heT
  have hvL : G.src e ∉ L := by
    simp only [C, Finset.mem_filter, Finset.mem_univ, true_and] at heT
    exact (Relation.TransGen.head'_iff.1 heT.2).elim fun _ h => h.1.1
  have := hal.resolve_left hvL e' he'd
  exact Finset.disjoint_left.1 hdis this (by simp [he'C])

/-- §3: in a transaction graph **without brokering** (every party owns the assets of its outgoing
contracts) every feedback vertex set is an adequate leader set. -/
theorem adequate_of_isFVS [Fintype E] [Finite P] (hown : ∀ p a, G.outTotal p a ≤ own p a) (hL : G.IsFVS L) :
    G.Adequate own L := by
  classical
  have hwf : WellFounded (G.FollowerEdge L) := by
    have : WellFounded (Relation.TransGen (G.FollowerEdge L)) := by
      have : IsTrans P (Relation.TransGen (G.FollowerEdge L)) := ⟨fun _ _ _ => Relation.TransGen.trans⟩
      have : Std.Irrefl (Relation.TransGen (G.FollowerEdge L)) := ⟨hL⟩
      exact Finite.wellFounded_of_trans_of_irrefl _
    exact Subrelation.wf (fun h => Relation.TransGen.single h) this
  -- progress: from every reachable state other than `univ` some contract is enabled
  have prog : ∀ S, G.Reachable own L S → S ≠ Finset.univ → ∃ e, G.Enabled own L S e := by
    intro S hS hne
    have hpay : ∀ e, e ∉ S → G.outflow S (G.src e) (G.asset e) + G.amt e ≤
        own (G.src e) (G.asset e) + G.inflow S (G.src e) (G.asset e) := by
      intro e he
      have := outflow_mono (G := G) (Finset.insert_subset (Finset.mem_univ e) (Finset.subset_univ S))
        (G.src e) (G.asset e)
      rw [outflow_insert he, ite_eq_left ⟨rfl, rfl⟩] at this
      have := hown (G.src e) (G.asset e); unfold outTotal at this; omega
    obtain ⟨e₁, he₁⟩ : ∃ e, e ∉ S := by
      by_contra hc; push Not at hc; exact hne (Finset.eq_univ_iff_forall.2 hc)
    by_cases hl : G.src e₁ ∈ L
    · exact ⟨e₁, he₁, Or.inl hl, hpay e₁ he₁⟩
    -- a follower with a pending contract, minimal for the follower-edge relation
    obtain ⟨u, ⟨hu, e₀, he₀, rfl⟩, hmin⟩ := hwf.has_min {u | u ∉ L ∧ ∃ e, e ∉ S ∧ G.src e = u}
      ⟨_, hl, e₁, he₁, rfl⟩
    by_cases hin : ∀ e, G.dst e = G.src e₀ → e ∈ S
    · exact ⟨e₀, he₀, Or.inr hin, hpay e₀ he₀⟩
    push Not at hin
    obtain ⟨e', he'd, he'S⟩ := hin
    by_cases hx : G.src e' ∈ L
    · exact ⟨e', he'S, Or.inl hx, hpay e' he'S⟩
    · exact absurd ⟨hx, hu, e', rfl, he'd⟩ (hmin _ ⟨hx, e', he'S, rfl⟩)
  -- every reachable state extends to `univ`
  suffices ∀ k, ∀ S, G.Reachable own L S → (Finset.univ \ S).card = k → G.Adequate own L from
    this _ ∅ Relation.ReflTransGen.refl rfl
  intro k
  induction k with
  | zero =>
    intro S hS hk
    rw [Finset.card_eq_zero, Finset.sdiff_eq_empty_iff_subset] at hk
    rwa [Adequate, ← Finset.univ_subset_iff.1 hk]
  | succ k ih =>
    intro S hS hk
    have hne : S ≠ Finset.univ := by rintro rfl; simp at hk
    obtain ⟨e, hen⟩ := prog S hS hne
    refine ih (insert e S) (hS.tail ⟨e, hen, rfl⟩) ?_
    rw [Finset.sdiff_insert, Finset.card_erase_of_mem (by simp [hen.1]), hk]; rfl

/-- §3: for transaction graphs **without brokering** (every party owns what it sends), the adequate
leader sets are exactly the feedback vertex sets; hence minimum leader sets are minimum feedback vertex
sets, and finding them is NP-hard. -/
theorem adequate_iff_isFVS [Fintype E] [Fintype P] (hown : ∀ p a, G.outTotal p a ≤ own p a) :
    G.Adequate own L ↔ G.IsFVS L :=
  ⟨Adequate.isFVS, adequate_of_isFVS hown⟩

end TxGraph

end Podc.HTLCBrokeringHardness
