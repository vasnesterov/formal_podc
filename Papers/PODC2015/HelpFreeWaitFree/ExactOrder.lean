import Papers.PODC2015.HelpFreeWaitFree.Defs

/-!
# Exact order types (Definition 4.5.1 of [CPT15])

For a sequence of operations `S`, `S(n)` is the list of its first `n` operations, and
`(S + op?)` is the set of sequences consisting of `S` itself and of `S` with one copy of `op`
inserted at some position (`OptIns`).

A type `A` is an *exact order type* if there are an operation `op`, an infinite sequence `W` and
a sequence `R` such that for every `n` there is `m ≥ 1` such that the results of `R(m)` differ
between any execution in `W(n+1) ∘ (R(m) + op?)` and any execution in
`W(n) ∘ op ∘ (R(m) + W_{n+1}?)`.

We record which entries of a sequence belong to `R` by a Boolean tag (`true` = an `R`
operation), and `taggedResps` collects the results of the tagged operations of a sequential
execution. `R` is an infinite sequence (`ℕ → A.Op`): a finite `R` can be padded arbitrarily,
since only finite prefixes `R(m)` are used.

* `ExactOrderStrong A` — the paper's literal wording: *one* operation of `R(m)` has a different
  result in every pair of executions;
* `ExactOrder A` — every pair of executions differs in the result of *some* operation of `R(m)`
  (the form used by Aksenov–Kuznetsov–Shalyto 2018). It is implied by the strong form
  (`ExactOrderStrong.exactOrder`) and suffices for Theorem 4.3, which we therefore prove for the
  larger class.

Paper indices are 1-based (`W_{n+1}` is the `(n+1)`-st operation of `W`); here sequences are
0-indexed, so the paper's `W_{n+1}` is `W n`.
-/

set_option linter.style.longLine false

namespace Podc.HelpFreeWaitFree

open Cslib.SharedMemory

variable {α : Type}

/-- `(xs + x?)`: `xs`, or `xs` with `x` inserted at one position. -/
def OptIns (xs : List α) (x : α) : Set (List α) :=
  {ys | ys = xs ∨ ∃ k ≤ xs.length, ys = xs.insertIdx k x}

/-- The first `n` operations of a sequence. -/
def pre (S : ℕ → α) (n : ℕ) : List α := (List.range n).map S

variable (A : ObjSpec)

/-- Results of the tagged operations (tag `true`) when the sequence is executed sequentially
from state `q`. -/
def taggedResps : A.State → List (Bool × A.Op) → List A.Resp
  | _, [] => []
  | q, (t, o) :: l => (if t then [(A.δ q o).2] else []) ++ taggedResps (A.δ q o).1 l

variable {A}

/-- Tag a list of operations. -/
def tagged (t : Bool) (os : List A.Op) : List (Bool × A.Op) := os.map (t, ·)

/-- `W(n) ∘ op ∘ (R(m) + W_{n+1}?)` (with the `R` operations tagged). -/
def seqOpFirst (op : A.Op) (W R : ℕ → A.Op) (n m : ℕ) : Set (List (Bool × A.Op)) :=
  {t | ∃ u ∈ OptIns (tagged true (pre R m)) (false, W n),
    t = tagged false (pre W n) ++ (false, op) :: u}

/-- `W(n+1) ∘ (R(m) + op?)` (with the `R` operations tagged). -/
def seqWFirst (op : A.Op) (W R : ℕ → A.Op) (n m : ℕ) : Set (List (Bool × A.Op)) :=
  {t | ∃ u ∈ OptIns (tagged true (pre R m)) (false, op), t = tagged false (pre W (n + 1)) ++ u}

/-- **Definition 4.5.1** (exact order types), in the form "every pair of executions is told
apart by the results of `R(m)`". -/
def ExactOrder (A : ObjSpec) : Prop :=
  ∃ (op : A.Op) (W R : ℕ → A.Op), ∀ n, ∃ m ≥ 1,
    ∀ a ∈ seqWFirst op W R n m, ∀ b ∈ seqOpFirst op W R n m,
      taggedResps A A.init a ≠ taggedResps A A.init b

/-- **Definition 4.5.1** (exact order types), literal form: a single operation of `R(m)` (the
`i`-th) returns different results in any execution of `W(n+1) ∘ (R(m) + op?)` and any
execution of `W(n) ∘ op ∘ (R(m) + W_{n+1}?)`. -/
def ExactOrderStrong (A : ObjSpec) : Prop :=
  ∃ (op : A.Op) (W R : ℕ → A.Op), ∀ n, ∃ m ≥ 1, ∃ i < m,
    ∀ a ∈ seqWFirst op W R n m, ∀ b ∈ seqOpFirst op W R n m,
      (taggedResps A A.init a)[i]? ≠ (taggedResps A A.init b)[i]?

lemma ExactOrderStrong.exactOrder {A : ObjSpec} (h : ExactOrderStrong A) : ExactOrder A := by
  obtain ⟨op, W, R, hn⟩ := h
  refine ⟨op, W, R, fun n => ?_⟩
  obtain ⟨m, hm, i, -, hi⟩ := hn n
  exact ⟨m, hm, fun a ha b hb he => hi a ha b hb (by rw [he])⟩

end Podc.HelpFreeWaitFree
