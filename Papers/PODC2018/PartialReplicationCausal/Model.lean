import Mathlib

/-!
# Partially replicated causally consistent shared memory: the model

Z. Xiang, N. H. Vaidya. *Partially Replicated Causally Consistent Shared Memory: Lower Bounds and
An Algorithm.* PODC 2018 (brief announcement); full version arXiv:1703.05424v3.

This file fixes the model of Sections 2–3 (peer-to-peer architecture):

* replicas `ι`, registers `Reg`, replica `i` stores the registers `X i`;
* the share graph (Definition 1) `Adj X j k` and the `(i, e_jk)`-loops (Definition 6);
* the timestamp graph `E_i` (Definition 7) as the predicate `TsEdge X i j k` ("`e_jk ∈ E_i`");
* the edge-indexed timestamp algorithm of Section 3.2 as a transition system `Step X`;
* the happened-before relation `↪` on updates (Definition 4) and replica-centric causal
  consistency (Definition 5): `Safe` and the liveness property in `Liveness.lean`.

## Execution model

Asynchronous, reliable, non-FIFO point-to-point channels, no failures. A state records the
updates issued so far (`log 0, …, log (n-1)`), the replicas' timestamps `τ` and, for each replica,
the set of updates it has applied (`app`). An update can be applied at a replica `i` at any time
after it has been issued, provided its register is stored at `i` and the algorithm's predicate
holds: since channels have arbitrary delays, this is exactly the set of behaviours of the paper's
system (a message is received at some point, sits in `pending_i`, and is applied when the
predicate holds). Register values and read operations play no role in causal consistency of
updates and are omitted.

The field `Update.pre` is *ghost* data: the set of updates applied at the issuing replica before
this update was issued. It is not used by the algorithm; it only serves to define `↪`
(Definition 4, condition 1).
-/

namespace Podc.PartialReplicationCausal

open Classical

variable {ι Reg : Type*}

/-! ### Share graph, loops and timestamp graphs -/

/-- Share graph (Definition 1): there is an edge `e_jk` iff `j ≠ k` and `X_jk = X_j ∩ X_k ≠ ∅`. -/
def Adj (X : ι → Set Reg) (j k : ι) : Prop := j ≠ k ∧ (X j ∩ X k).Nonempty

/-- `(i, e_jk)`-loop (Definition 6). The simple loop is `(i, l₁, …, l_s = k, j = r₁, r₂, …, r_t, i)`
with `s, t ≥ 1`; here `l = [l₁, …, l_{s-1}]` and `r = [r₂, …, r_t]` (so `r_{t+1} = i` is the
element following `r`, and `r₂ = r.headD i`). -/
structure IsLoop (X : ι → Set Reg) (i j k : ι) (l r : List ι) : Prop where
  /-- The loop is simple. -/
  nodup : (i :: (l ++ k :: j :: r)).Nodup
  /-- Consecutive replicas of the loop are neighbours in the share graph. -/
  adj : List.IsChain (Adj X) (i :: (l ++ k :: j :: r) ++ [i])
  /-- (i) `X_jk − ∪_{1 ≤ p ≤ s-1} X_{l_p} ≠ ∅`. -/
  cond_i : ∃ x ∈ X j ∩ X k, ∀ p ∈ l, x ∉ X p
  /-- (ii) `X_{j r₂} − ∪_{1 ≤ p ≤ s-1} X_{l_p} ≠ ∅`. -/
  cond_ii : ∃ x ∈ X j ∩ X (r.headD i), ∀ p ∈ l, x ∉ X p
  /-- (iii) for `2 ≤ q ≤ t`, `X_{r_q r_{q+1}} − ∪_{1 ≤ p ≤ s} X_{l_p} ≠ ∅`. -/
  cond_iii : List.IsChain (fun a b => ∃ x ∈ X a ∩ X b, x ∉ X k ∧ ∀ p ∈ l, x ∉ X p) (r ++ [i])

/-- The timestamp graph `G_i` (Definition 7): `TsEdge X i j k` means `e_jk ∈ E_i`, i.e. `e_jk` is
an edge of the share graph that is incident to `i` or for which an `(i, e_jk)`-loop exists. -/
def TsEdge (X : ι → Set Reg) (i j k : ι) : Prop :=
  Adj X j k ∧ (j = i ∨ k = i ∨ ∃ l r, IsLoop X i j k l r)

/-! ### The algorithm of Section 3.2 -/

/-- An update message `update(src, ts, reg, ·)`; `pre` is ghost data (see the module doc). -/
structure Update (ι Reg : Type*) where
  /-- The issuing replica. -/
  src : ι
  /-- The register written. -/
  reg : Reg
  /-- The timestamp attached to the update (`ts j k` is the entry for edge `e_jk`). -/
  ts : ι → ι → ℕ
  /-- Ghost: the updates applied at `src` before this update was issued. -/
  pre : Set ℕ

/-- Global state. Updates are numbered `0, 1, …` in the order in which they are issued. -/
structure State (ι Reg : Type*) where
  /-- Number of updates issued so far. -/
  n : ℕ
  /-- The issued updates are `log 0, …, log (n - 1)` (later entries are irrelevant). -/
  log : ℕ → Update ι Reg
  /-- `τ i j k` is replica `i`'s timestamp entry `τ_i[e_jk]` (only entries with `e_jk ∈ E_i` are
  ever changed or read). -/
  τ : ι → ι → ι → ℕ
  /-- The updates applied at each replica so far (including the replica's own updates). -/
  app : ι → Set ℕ

/-- Initial states: no update issued, all timestamps `0`. -/
def IsInit (s : State ι Reg) : Prop :=
  s.n = 0 ∧ s.τ = (fun _ _ _ => 0) ∧ s.app = fun _ => ∅

variable (X : ι → Set Reg)

/-- Step 2(b): replica `i` writes register `x`; `τ_i[e_ik]` is incremented for each `e_ik ∈ E_i`
with `x ∈ X_ik`. -/
noncomputable def incr (τi : ι → ι → ℕ) (i : ι) (x : Reg) : ι → ι → ℕ := fun j k =>
  if TsEdge X i j k ∧ j = i ∧ x ∈ X k then τi j k + 1 else τi j k

/-- Step 4(b): replica `i` merges the timestamp `T` of an update from `k`: entrywise maximum on
`E_i ∩ E_k`. -/
noncomputable def merge (τi : ι → ι → ℕ) (i k : ι) (T : ι → ι → ℕ) : ι → ι → ℕ := fun a b =>
  if TsEdge X i a b ∧ TsEdge X k a b then max (τi a b) (T a b) else τi a b

/-- The predicate of Step 4: `τ_i[e_ki] = T[e_ki] - 1` and `τ_i[e_ji] ≥ T[e_ji]` for each
`e_ji ∈ E_i ∩ E_k`, `j ≠ i, k` (where `k` is the sender and `T` the attached timestamp).
(`T[e_ki] ≥ 1` always holds, so `τ_i[e_ki] + 1 = T[e_ki]` is the same condition.) -/
def Ready (s : State ι Reg) (i : ι) (u : Update ι Reg) : Prop :=
  s.τ i u.src i + 1 = u.ts u.src i ∧
    ∀ j, j ≠ i → j ≠ u.src → TsEdge X i j i → TsEdge X u.src j i → u.ts j i ≤ s.τ i j i

/-- Step 2: replica `i` performs a client write on `x` (writes locally, updates its timestamp,
issues the update with the new timestamp attached). -/
noncomputable def State.write (s : State ι Reg) (i : ι) (x : Reg) : State ι Reg :=
  { n := s.n + 1
    log := Function.update s.log s.n ⟨i, x, incr X (s.τ i) i x, s.app i⟩
    τ := Function.update s.τ i (incr X (s.τ i) i x)
    app := Function.update s.app i (insert s.n (s.app i)) }

/-- Step 4: replica `i` applies update number `a` (writes locally, merges the timestamp). -/
noncomputable def State.apply (s : State ι Reg) (i : ι) (a : ℕ) : State ι Reg :=
  { s with
    τ := Function.update s.τ i (merge X (s.τ i) i (s.log a).src (s.log a).ts)
    app := Function.update s.app i (insert a (s.app i)) }

/-- Update `a` may be applied at replica `i`: it has been issued by another replica, it writes a
register stored at `i` (so it was sent to `i`), it has not been applied at `i` yet, and the
predicate of Step 4 holds. -/
def Enabled (s : State ι Reg) (i : ι) (a : ℕ) : Prop :=
  a < s.n ∧ (s.log a).src ≠ i ∧ (s.log a).reg ∈ X i ∧ a ∉ s.app i ∧ Ready X s i (s.log a)

/-- One step of the algorithm. -/
inductive Step : State ι Reg → State ι Reg → Prop
  | write (s : State ι Reg) (i : ι) (x : Reg) (hx : x ∈ X i) : Step s (s.write X i x)
  | apply (s : State ι Reg) (i : ι) (a : ℕ) (h : Enabled X s i a) : Step s (s.apply X i a)

/-- Reachable states. -/
def Reachable (s : State ι Reg) : Prop :=
  ∃ s₀, IsInit s₀ ∧ Relation.ReflTransGen (Step X) s₀ s

/-! ### Causality and consistency (Definitions 4, 5) -/

/-- Happened-before `↪` between updates (Definition 4): the transitive closure of
"`a` was applied at some replica before that replica issued `b`". -/
def HB (s : State ι Reg) : ℕ → ℕ → Prop :=
  Relation.TransGen fun a b => b < s.n ∧ a ∈ (s.log b).pre

/-- Safety of replica-centric causal consistency (Definition 5): if an update `b` has been applied
at replica `i`, then every update `a` on a register of `X_i` with `a ↪ b` has been applied at `i`. -/
def Safe (s : State ι Reg) : Prop :=
  ∀ i, ∀ b ∈ s.app i, ∀ a, (s.log a).reg ∈ X i → HB s a b → a ∈ s.app i

end Podc.PartialReplicationCausal
