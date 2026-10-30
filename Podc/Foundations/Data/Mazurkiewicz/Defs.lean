/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
-- CSLib candidate: Cslib/Foundations/Data/Mazurkiewicz/Defs.lean
import Mathlib

/-!
# Mazurkiewicz traces: basic definitions

Schedules are lists over an alphabet `α`; a *dependence* (conflict) relation `D` on `α` says
which letters may not be reordered.

* `Mazurkiewicz.Before l a b`: `a` occurs (strictly) before `b` in `l`.
* `Mazurkiewicz.NEquiv D l l'`: equivalence of *duplicate-free* schedules: `l'` is a permutation of
  `l` that preserves the relative order of every pair of dependent letters.
* `Mazurkiewicz.Commute δ a b q`, `Mazurkiewicz.Conflict δ a b`: commutation of two operations of a
  deterministic machine `δ : Q → α → Q × R` in a state `q` (same responses and same final state in
  both orders), and the induced conflict relation (non-commutation in some state).
-/

namespace Cslib.Mazurkiewicz

variable {α : Type*}

/-- `a` occurs strictly before `b` in `l` (some occurrence of `a` precedes some occurrence of
`b`). For duplicate-free lists this is the order of the unique occurrences. -/
def Before (l : List α) (a b : α) : Prop :=
  ∃ i j : ℕ, i < j ∧ l[i]? = some a ∧ l[j]? = some b

/-- Equivalence of duplicate-free schedules w.r.t. the dependence relation `D`: the same letters,
and every pair of dependent letters occurs in the same order. -/
def NEquiv (D : α → α → Prop) (l l' : List α) : Prop :=
  l.Perm l' ∧ ∀ a b, D a b → Before l a b → Before l' a b

/-- Operations `a` and `b` of the deterministic machine `δ` commute in state `q`: executing
`a` then `b` from `q` yields the same responses and the same final state as executing `b`
then `a`. -/
def Commute {Q R : Type*} (δ : Q → α → Q × R) (a b : α) (q : Q) : Prop :=
  (δ (δ q a).1 b).1 = (δ (δ q b).1 a).1 ∧ (δ q a).2 = (δ (δ q b).1 a).2 ∧
    (δ q b).2 = (δ (δ q a).1 b).2

/-- The conflict relation induced by commutativity: `a` and `b` conflict if they do not commute
in some state. -/
def Conflict {Q R : Type*} (δ : Q → α → Q × R) (a b : α) : Prop :=
  ∃ q, ¬ Commute δ a b q

lemma commute_comm {Q R : Type*} (δ : Q → α → Q × R) (a b : α) (q : Q) :
    Commute δ a b q ↔ Commute δ b a q := by
  unfold Commute
  constructor <;> rintro ⟨h1, h2, h3⟩ <;> exact ⟨h1.symm, h3, h2⟩

lemma conflict_comm {Q R : Type*} (δ : Q → α → Q × R) (a b : α) :
    Conflict δ a b ↔ Conflict δ b a := by
  simp [Conflict, commute_comm δ a b]

instance {Q R : Type*} (δ : Q → α → Q × R) : Std.Symm (Conflict δ) :=
  ⟨fun a b h => (conflict_comm δ a b).1 h⟩

section Run

variable {Q R : Type*} (δ : Q → α → Q × R)

/-- The state reached by running the schedule `l` from `q`. -/
def runState : Q → List α → Q
  | q, [] => q
  | q, a :: l => runState (δ q a).1 l

variable [DecidableEq α]

/-- The response of the first occurrence of `c` when running the schedule `l` from `q`
(`none` if `c` does not occur in `l`). For duplicate-free schedules this is `ret*(c, l)`. -/
def respFirst : Q → List α → α → Option R
  | _, [], _ => none
  | q, a :: l, c => if a = c then some (δ q a).2 else respFirst (δ q a).1 l c

@[simp] lemma respFirst_nil (q : Q) (c : α) : respFirst δ q [] c = none := rfl

lemma respFirst_cons (q : Q) (a : α) (l : List α) (c : α) :
    respFirst δ q (a :: l) c = if a = c then some (δ q a).2 else respFirst δ (δ q a).1 l c := rfl

end Run

end Cslib.Mazurkiewicz
