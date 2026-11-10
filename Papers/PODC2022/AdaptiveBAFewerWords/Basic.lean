import Mathlib

/-!
# Make Every Word Count: common definitions

[CKS22] S. Cohen, I. Keidar, A. Spiegelman. *Make Every Word Count: Adaptive Byzantine Agreement with
Fewer Words.* PODC 2022 (brief announcement); full version arXiv:2202.09123v2 (OPODIS 2022).

This file contains what the three algorithm models share:

* the problem specifications of Section 3 (agreement, termination, Byzantine Broadcast validity,
  strong unanimity, unique validity), stated for the *outcome* of a run: the set `C` of correct
  processes and their decisions `dec : P → Option O` (`none` = has not decided);
* the quorum arithmetic for `n = 2t + 1` and the threshold `q = ⌈(n + t + 1)/2⌉` of Section 6.
-/

namespace Podc.AdaptiveBAFewerWords

section Specs

variable {P O V : Type*}

/-- **Agreement.** No two correct processes decide differently. -/
def Agreement (C : Set P) (dec : P → Option O) : Prop :=
  ∀ p ∈ C, ∀ q ∈ C, ∀ a b, dec p = some a → dec q = some b → a = b

/-- **Termination.** Every correct process decides. -/
def Termination (C : Set P) (dec : P → Option O) : Prop :=
  ∀ p ∈ C, ∃ a, dec p = some a

/-- **Validity of Byzantine Broadcast** (Definition 1): if the sender is correct, every correct
process decides the sender's input. -/
def BBValidity (C : Set P) (sender : P) (vSender : O) (dec : P → Option O) : Prop :=
  sender ∈ C → ∀ p ∈ C, dec p = some vSender

/-- **Strong unanimity** (Definition 2): if all correct processes propose the same `v`, every
decision of a correct process is `v`. -/
def StrongUnanimity (C : Set P) (inp : P → V) (dec : P → Option V) : Prop :=
  ∀ v, (∀ p ∈ C, inp p = v) → ∀ p ∈ C, ∀ a, dec p = some a → a = v

/-- **Unique validity** (Definition 3). Decisions are in `Option V`, `none` being the default `⊥`.
`valid` is the external predicate and `Ex` the set of values that *exist* in the run (inputs of
correct processes and values Byzantine processes can generate). A correct decision is `⊥` or a valid
value, and `⊥` only if two different valid values exist. -/
def UniqueValidity (valid : V → Prop) (Ex : Set V) (C : Set P) (dec : P → Option (Option V)) :
    Prop :=
  ∀ p ∈ C, ∀ d, dec p = some d →
    match d with
    | some v => valid v
    | none => ∃ a ∈ Ex, ∃ b ∈ Ex, valid a ∧ valid b ∧ a ≠ b

end Specs

section Quorums

/-- The threshold `⌈(n + t + 1)/2⌉` of Algorithm 4. -/
def quorum (n t : ℕ) : ℕ := (n + t + 2) / 2

lemma quorum_spec (n t : ℕ) : n + t + 1 ≤ 2 * quorum n t ∧ 2 * quorum n t ≤ n + t + 2 := by
  unfold quorum; omega

/-- Two quorums out of `n` intersect in at least `t + 1` processes. -/
lemma quorum_inter (n t : ℕ) : n + (t + 1) ≤ 2 * quorum n t := by
  have := quorum_spec n t; omega

/-- `n - q + t < q`: after `q - t` correct processes leave, the rest cannot form a quorum. -/
lemma quorum_rest (n t : ℕ) : n + t < 2 * quorum n t := by
  have := quorum_spec n t; omega

/-- The paper's condition `f < (n - t - 1)/2` implies that the correct processes form a quorum
(`q ≤ n - f`). -/
lemma quorum_le_correct {n t f : ℕ} (h : 2 * f < n - t - 1) (ht : t < n) : quorum n t ≤ n - f := by
  have := quorum_spec n t; omega

end Quorums

end Podc.AdaptiveBAFewerWords
