import Mathlib
import Cslib.Computability.Distributed.Byzantine.SyncCounting.Model
import Papers.PODC2015.SynchronousCounting.Params
import Papers.PODC2015.SynchronousCounting.Majority
import Papers.PODC2015.SynchronousCounting.PhaseKing
import Papers.PODC2015.SynchronousCounting.Pointers

/-!
# The boosted counter `B` of Theorem 1 (§3.2–§3.5)

Nodes are pairs `(i, j) ∈ [k] × [n]` (node `j` of block `i`). The state of a node is
`(x, a, d)`: a state `x` of the base counter `A` (run inside the node's block), the phase-king
output register `a ∈ [C] ∪ {∞}` and the bit `d`. In every round node `v = (i, j)`, on the received
state vector `msg`,

1. updates the `A`-state of its block: `x ← g_A(j, (msg (i, j')).x)_{j'}`;
2. computes the leader pointers `b_{i'} = majority {b[i', j'] | j'}`,
   the leader block `B = majority {b_{i'} | i'}` and its round counter
   `R = majority {r[B, j'] | j'}`;
3. executes the instruction set `I_R` of the phase king (instruction `R mod 3`, king `⌊R/3⌋`).

The output is `a` (and `0` when `a = ∞`, which the paper leaves unspecified). Kings `ℓ ∈ [F+2]`
are identified with nodes via `finProdFinEquiv : Fin k × Fin n ≃ Fin (k * n)`.
-/

namespace SynchronousCounting

open Cslib.Byzantine.SyncCounting Finset

variable {X : Type*} {n c : ℕ} (k F C : ℕ)

/-- States of the boosted counter: base state, `a ∈ [C] ∪ {∞}`, `d ∈ {0, 1}`. -/
abbrev BState (X : Type*) (C : ℕ) := X × Option (Fin C) × Bool

/-- The base counter value of node `(i, j)` according to the received state vector. -/
def cval (A : Algorithm (Fin n) X c) (msg : Fin k × Fin n → BState X C) (i : Fin k) (j : Fin n) :
    ℕ :=
  (A.h j (msg (i, j)).1 : ℕ)

/-- `b_i = majority {b[i, j] | j ∈ [n]}`. -/
def blockPtr (A : Algorithm (Fin n) X c) (msg : Fin k × Fin n → BState X C) (i : Fin k) : ℕ :=
  maj (fun j => ptr (tau F) (half k) i (cval k C A msg i j)) 0

/-- `B = majority {b_i | i ∈ [k]}` (falling back to the node's own block if out of range). -/
def leader (A : Algorithm (Fin n) X c) (msg : Fin k × Fin n → BState X C) (v : Fin k × Fin n) :
    Fin k :=
  if h : maj (fun i => blockPtr k F C A msg i) 0 < k then ⟨_, h⟩ else v.1

/-- `R = majority {r[B, j] | j ∈ [n]}`. -/
def Rval (A : Algorithm (Fin n) X c) (msg : Fin k × Fin n → BState X C) (v : Fin k × Fin n) : ℕ :=
  maj (fun j => rnd (tau F) (cval k C A msg (leader k F C A msg v) j)) 0

/-- The node acting as king `ℓ` (falling back to `v` if `ℓ ≥ kn`, which never happens). -/
def kingNode {n : ℕ} (v : Fin k × Fin n) (ℓ : ℕ) : Fin k × Fin n :=
  if h : ℓ < k * n then finProdFinEquiv.symm ⟨ℓ, h⟩ else v

variable [NeZero C]

/-- **The algorithm `B` of Theorem 1.** -/
def construction (A : Algorithm (Fin n) X c) : Algorithm (Fin k × Fin n) (BState X C) C where
  g v msg :=
    let R := Rval k F C A msg v
    let p := pkStep F (kingNode k v (R / 3)) R (fun u => (msg u).2.1) (msg v).2.1 (msg v).2.2
    (A.g v.2 (fun j => (msg (v.1, j)).1), p.1, p.2)
  h _ s := s.2.1.getD 0

/-! ### Voting -/

variable {k F C}

lemma kingNode_eq {n : ℕ} (v w : Fin k × Fin n) {ℓ : ℕ} (h : ℓ < k * n) :
    kingNode k v ℓ = kingNode k w ℓ := by
  simp [kingNode, h]

lemma kingNode_injective {n : ℕ} (v : Fin k × Fin n) {ℓ ℓ' : ℕ} (h : ℓ < k * n) (h' : ℓ' < k * n)
    (he : kingNode k v ℓ = kingNode k v ℓ') : ℓ = ℓ' := by
  simp only [kingNode, h, h', dite_true] at he
  have := congrArg Fin.val (finProdFinEquiv.symm.injective he)
  simpa using this

omit [NeZero C] in
/-- The voting lemma (proof of Lemma 3): if a majority of blocks (all outside `bad`, with
`2 |bad| < k`) have, among their correct nodes (a strict majority of each such block), pointer `β`,
and the correct nodes of block `β` have round counter `ρ`, then every node computes `R = ρ`. -/
lemma Rval_eq (A : Algorithm (Fin n) X c) (msg : Fin k × Fin n → BState X C) (v : Fin k × Fin n)
    (Fa : Finset (Fin k × Fin n)) (bad : Finset (Fin k)) (hbad : 2 * bad.card < k)
    (hblk : ∀ i ∉ bad, 2 * (univ.filter fun j => (i, j) ∈ Fa).card < n)
    (β : Fin k) (hβ : β ∉ bad)
    (hptr : ∀ i ∉ bad, ∀ j, (i, j) ∉ Fa → ptr (tau F) (half k) i (cval k C A msg i j) = β)
    (ρ : ℕ) (hρ : ∀ j, (β, j) ∉ Fa → rnd (tau F) (cval k C A msg β j) = ρ) :
    Rval k F C A msg v = ρ := by
  have hb : ∀ i ∉ bad, blockPtr k F C A msg i = β := by
    intro i hi
    apply maj_eq_of_minority _ _ _ (hblk i hi)
    intro j hj
    exact hptr i hi j (by simpa using hj)
  have hL : leader k F C A msg v = β := by
    have : maj (fun i => blockPtr k F C A msg i) 0 = β := maj_eq_of_minority _ _ bad hbad hb
    unfold leader
    rw [dite_eq_left (this ▸ β.isLt)]
    exact Fin.ext this
  unfold Rval
  rw [hL]
  exact maj_eq_of_minority _ _ _ (hblk β hβ) fun j hj => hρ j (by simpa using hj)

end SynchronousCounting
