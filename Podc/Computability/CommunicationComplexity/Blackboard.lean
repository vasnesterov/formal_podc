import Mathlib

-- CSLib candidate: Cslib/Computability/CommunicationComplexity/Blackboard.lean

/-!
# Number-in-hand multi-party protocols on a shared blackboard

A set `ι` of players; player `i` holds an input `x i : X i` (*number-in-hand*). The players
communicate by writing on a shared **blackboard** that everyone sees. A deterministic protocol is
a tree: at an internal node, the player designated by the node writes one of `m` symbols computed
from its own input only (the content of the blackboard is the position in the tree); writing a
symbol of an `m`-letter alphabet costs `⌈log₂ m⌉` bits (`Nat.clog 2 m`). This is the model of
Definition 1 of Efron–Grossman–Khoury (PODC 2020) and of Chakrabarti–Khot–Sun (CCC 2003).

* `BBProtocol X α`, `BBProtocol.eval`, `BBProtocol.CostLE P c` ("on every path at most `c` bits
  are written").
* Randomized protocols with **private coins**: player `i` additionally holds a uniformly random
  `r i : R i`; `BBProtocol.errCount`, `BBProtocol.RandComputes P prom f ε` (error `≤ ε` on every
  input satisfying the promise `prom`).
* `PairwiseDisjoint`, `UniquelyIntersecting`, `CommonElement`: the inputs of the promise pairwise
  disjointness problem (Definition 2 of Efron–Grossman–Khoury; Chakrabarti–Khot–Sun).
* `PPDLowerBound c`: the statement of the Chakrabarti–Khot–Sun lower bound
  `CC(PPD_{k,t}) ≥ c · k / (t log₂ t)` for private-coin protocols. It is **not** proved here and is
  used as a hypothesis.
-/

namespace Cslib.CommunicationComplexity

/-- A deterministic number-in-hand blackboard protocol for the players `ι` (player `i` holds an
input of type `X i`) with output in `α`. -/
inductive BBProtocol {ι : Type*} (X : ι → Type*) (α : Type*) where
  /-- Stop and output `a`. -/
  | ret (a : α) : BBProtocol X α
  /-- Player `i` writes the symbol `f (x i) : Fin m` on the blackboard; the protocol continues with
  `next (f (x i))`. -/
  | write (i : ι) (m : ℕ) (f : X i → Fin m) (next : Fin m → BBProtocol X α) : BBProtocol X α

namespace BBProtocol

variable {ι : Type*} {X : ι → Type*} {α : Type*}

/-- The output of a protocol on the inputs `x`. -/
def eval : BBProtocol X α → (∀ i, X i) → α
  | ret a, _ => a
  | write i _ f next, x => eval (next (f (x i))) x

/-- `CostLE P c`: on every input, at most `c` bits are written on the blackboard (a symbol of an
`m`-letter alphabet costs `⌈log₂ m⌉` bits). -/
def CostLE : BBProtocol X α → ℕ → Prop
  | ret _, _ => True
  | write _ m _ next, c => Nat.clog 2 m ≤ c ∧ ∀ j, CostLE (next j) (c - Nat.clog 2 m)

@[simp] theorem eval_ret (a : α) (x : ∀ i, X i) : (ret a : BBProtocol X α).eval x = a := rfl

@[simp] theorem eval_write (i : ι) (m : ℕ) (f : X i → Fin m) (next : Fin m → BBProtocol X α)
    (x : ∀ i, X i) : (write i m f next).eval x = (next (f (x i))).eval x := rfl

/-- A cost bound can be weakened. -/
theorem CostLE.mono : ∀ {P : BBProtocol X α} {c d : ℕ}, CostLE P c → c ≤ d → CostLE P d
  | ret _, _, _, _, _ => trivial
  | write _ _ _ _, _, _, ⟨h1, h2⟩, hcd =>
      ⟨h1.trans hcd, fun j => CostLE.mono (h2 j) (Nat.sub_le_sub_right hcd _)⟩

/-- Cost bound of a `write` node from cost bounds of its children. -/
theorem costLE_write {i : ι} {m : ℕ} {f : X i → Fin m} {next : Fin m → BBProtocol X α} {c : ℕ}
    (h : ∀ j, CostLE (next j) c) : CostLE (write i m f next) (Nat.clog 2 m + c) :=
  ⟨Nat.le_add_right _ _, fun j => by simpa using h j⟩

/-! ### Private-coin randomized protocols -/

section Randomized

variable [Fintype ι] [DecidableEq ι] {R : ι → Type*} [∀ i, Fintype (R i)]

/-- Number of coin vectors `r` on which the protocol (run on `(x i, r i)`) does not output
`f x`. -/
noncomputable def errCount (P : BBProtocol (fun i => X i × R i) Bool) (f : (∀ i, X i) → Bool)
    (x : ∀ i, X i) : ℕ := by
  classical
  exact (Finset.univ.filter fun r : (∀ i, R i) => P.eval (fun i => (x i, r i)) ≠ f x).card

/-- A private-coin randomized protocol computes `f` with error at most `ε` on every input that
satisfies the promise `prom` (the coins `r i : R i` are independent and uniform). -/
def RandComputes (P : BBProtocol (fun i => X i × R i) Bool) (prom : (∀ i, X i) → Prop)
    (f : (∀ i, X i) → Bool) (ε : ℝ) : Prop :=
  ∀ x, prom x → (P.errCount f x : ℝ) ≤ ε * Fintype.card (∀ i, R i)

end Randomized

end BBProtocol

/-! ### Promise pairwise disjointness -/

section PPD

variable {ι K : Type*}

/-- The sets `x i ⊆ K` (given by indicator vectors) are pairwise disjoint. -/
def PairwiseDisjoint (x : ι → K → Bool) : Prop :=
  ∀ i j, i ≠ j → ∀ m, x i m = true → x j m = false

instance [Fintype ι] [DecidableEq ι] [Fintype K] (x : ι → K → Bool) :
    Decidable (PairwiseDisjoint x) := by
  unfold PairwiseDisjoint; infer_instance

/-- All sets contain a common element. -/
def CommonElement (x : ι → K → Bool) : Prop :=
  ∃ m, ∀ i, x i m = true

/-- The sets are *uniquely intersecting* (Chakrabarti–Khot–Sun): they have a common element `m`
and are pairwise disjoint apart from `m`. -/
def UniquelyIntersecting (x : ι → K → Bool) : Prop :=
  ∃ m, (∀ i, x i m = true) ∧ ∀ i j, i ≠ j → ∀ m', m' ≠ m → x i m' = true → x j m' = false

theorem UniquelyIntersecting.commonElement {x : ι → K → Bool} (h : UniquelyIntersecting x) :
    CommonElement x :=
  let ⟨m, hm, _⟩ := h; ⟨m, hm⟩

/-- **The lower bound of Chakrabarti–Khot–Sun** (Theorem 2.5 of [CKS03], Theorem 3 of
Efron–Grossman–Khoury) for promise pairwise disjointness, with constant `c`: for `t ≥ 2` players
holding subsets of a `k`-element set, every private-coin blackboard protocol that outputs
"pairwise disjoint" correctly with probability `≥ 2/3` on every input that is pairwise disjoint or
uniquely intersecting writes at least `c · k / (t log₂ t)` bits in the worst case.

This is a statement, not a theorem: it is used as a hypothesis. Coins are required to be nonempty
(with an empty coin space every protocol would have error `0`). Lower bounds for public-coin
protocols, as proved by Chakrabarti–Khot–Sun, imply it. -/
def PPDLowerBound (c : ℝ) : Prop :=
  ∀ (t : ℕ), 2 ≤ t → ∀ (K : Type) [Fintype K] (R : Fin t → Type) [∀ i, Fintype (R i)]
    [∀ i, Nonempty (R i)] (P : BBProtocol (fun i : Fin t => (K → Bool) × R i) Bool) (cost : ℕ),
    P.RandComputes (fun x => PairwiseDisjoint x ∨ UniquelyIntersecting x)
      (fun x => decide (PairwiseDisjoint x)) (1 / 3) →
    P.CostLE cost → c * Fintype.card K / (t * Real.logb 2 t) ≤ cost

end PPD

end Cslib.CommunicationComplexity
