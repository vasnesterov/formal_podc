import Mathlib

/-!
# The message-map framework of Pease–Shostak–Lamport, and non-equivocation fault models

Madsen–Debois, *On the Subject of Non-Equivocation* (PODC 2020), Section 2–4.

A synchronous system of processes `P` (a `Fintype`) with reliable point-to-point channels runs the
**full-information relay protocol** of Pease–Shostak–Lamport: in round 1 everybody broadcasts its
private value; in round `r + 1` everybody broadcasts everything it received in round `r`, together
with the route. The outcome of `k` rounds is a *message map* `σ : P⁺ → V ∪ {⊥}`
(`MsgMap P V := List P → Option V`, `none` = `⊥` = "no message"):

* `σ [p]` is the private value of `p`;
* `σ (p :: q :: w)` is what `q` told `p` (in round `|w| + 1`) about the route `q :: w`,
  e.g. `σ [p, q, r]` = "`q` told `p` that `r` told `q` the value …".

Only routes without consecutive duplicates are meaningful (`Seq`). The value `⟨⊥⟩`
(`OmitVal.omitted`) is an ordinary value of `V` with which a correct process reports an observed
omission (Definition 2.1): `rep σ(q|w) = σ(q|w)` if this is a value, and `⟨⊥⟩` otherwise.

A *fault model* (`FaultModel`) says which pairs (faulty set `F`, message map `σ` of `k` rounds) are
possible:

* `byzantine`: only Definition 2.1 (correct processes relay truthfully);
* `wne` (Definition 4.1, weak non-equivocation): additionally every process — faulty or not —
  reports, for each route, the same value to every process it does not omit;
* `sne` (Definition 3.1, strong non-equivocation): every process reports the same value (possibly
  `⊥`) to all processes.

All constraints are stated for routes of length at most `k + 1` (messages of rounds `1, …, k`), and
relative to a finite set `S` of *active* processes, so that the recursion of Algorithm 2 (which
removes the source) stays inside the same framework.

An *algorithm* (`Alg`) is a deterministic decision function: process `p` computes its
interactive-consistency vector entry for `q` from its local view `view k σ p` (`w ↦ σ (p :: w)` for
`|w| ≤ k`). `SolvesIC M k t A`: in every `σ` of fault model `M` with at most `t` faulty processes,
`A` satisfies validity and agreement of interactive consistency (termination is built in: the
decision is taken after `k` rounds).

-- CSLib candidate (with `Exec.lean`): the PSL message-map framework and its fault models.
-/

namespace NonEquivocation

/-- The distinguished value `⟨⊥⟩` ("I observed an omission"), an ordinary element of `V`. -/
class OmitVal (V : Type*) where
  /-- `⟨⊥⟩`. -/
  omitted : V

export OmitVal (omitted)

variable {P V : Type*}

/-- A message map `σ : P⁺ → V ∪ {⊥}` (`none` is `⊥`). -/
abbrev MsgMap (P V : Type*) := List P → Option V

/-- A process sequence without consecutive duplicates. -/
def Seq (w : List P) : Prop := w.IsChain (· ≠ ·)

/-- What a correct process reports about a received entry: the value itself, or `⟨⊥⟩` for `⊥`. -/
def rep [OmitVal V] (x : Option V) : V := x.getD omitted

@[simp] lemma rep_some [OmitVal V] (v : V) : rep (some v) = v := rfl
@[simp] lemma rep_none [OmitVal V] : rep (none : Option V) = omitted := rfl

/-- **Definition 2.1** (non-faulty process guarantee), for `k` rounds and active set `S`: a
non-faulty `q` truthfully relays to every `p` what it received, reporting `⟨⊥⟩` for omissions. -/
def NonFaulty [OmitVal V] (k : ℕ) (S F : Finset P) (σ : MsgMap P V) : Prop :=
  ∀ q ∈ S, q ∉ F → ∀ p ∈ S, ∀ w : List P, (∀ x ∈ w, x ∈ S) → Seq (p :: q :: w) →
    w.length < k → σ (p :: q :: w) = some (rep (σ (q :: w)))

/-- **Definition 4.1** (weak non-equivocation), for `k` rounds and active set `S`: for every route
`p :: w`, any two processes that receive a value from `p` receive the same value. -/
def WeakNE (k : ℕ) (S : Finset P) (σ : MsgMap P V) : Prop :=
  ∀ p ∈ S, ∀ r ∈ S, ∀ r' ∈ S, ∀ w : List P, (∀ x ∈ w, x ∈ S) →
    Seq (r :: p :: w) → Seq (r' :: p :: w) → w.length < k →
    σ (r :: p :: w) ≠ none → σ (r' :: p :: w) ≠ none → σ (r :: p :: w) = σ (r' :: p :: w)

/-- **Definition 3.1** (strong non-equivocation), for `k` rounds and active set `S`: for every route
`p :: w`, all processes receive the same (possibly absent) value from `p`. Following footnote 1 of the
paper, only routes without consecutive duplicates are constrained (in particular `r ≠ p`). -/
def StrongNE (k : ℕ) (S : Finset P) (σ : MsgMap P V) : Prop :=
  ∀ p ∈ S, ∀ r ∈ S, ∀ r' ∈ S, ∀ w : List P, (∀ x ∈ w, x ∈ S) →
    Seq (r :: p :: w) → Seq (r' :: p :: w) → w.length < k →
    σ (r :: p :: w) = σ (r' :: p :: w)

/-- A fault model: which (number of rounds, faulty set, message map) are possible. -/
def FaultModel (P V : Type*) := ℕ → Finset P → MsgMap P V → Prop

section Models

variable [Fintype P] [OmitVal V]

/-- The (unauthenticated) Byzantine fault model: only Definition 2.1. -/
def byzantine : FaultModel P V := fun k F σ => NonFaulty k Finset.univ F σ

/-- The weak non-equivocation fault model (Definition 4.1). -/
def wne : FaultModel P V := fun k F σ => NonFaulty k Finset.univ F σ ∧ WeakNE k Finset.univ σ

/-- The strong non-equivocation fault model (Definition 3.1). -/
def sne : FaultModel P V := fun k F σ => NonFaulty k Finset.univ F σ ∧ StrongNE k Finset.univ σ

/-- The (general send-)omission fault model: every process, faulty or not, either relays truthfully or
omits; faulty processes may omit arbitrarily (per receiver and per route). -/
def omission : FaultModel P V := fun k F σ => NonFaulty k Finset.univ F σ ∧
  ∀ x y : P, ∀ w : List P, Seq (x :: y :: w) → w.length < k →
    σ (x :: y :: w) = none ∨ σ (x :: y :: w) = some (rep (σ (y :: w)))

/-- Omission faults never equivocate: the omission model is contained in weak non-equivocation. -/
lemma wne_of_omission {k : ℕ} {F : Finset P} {σ : MsgMap P V} (h : omission k F σ) :
    wne k F σ := by
  refine ⟨h.1, ?_⟩
  intro p _ r _ r' _ w _ h₁ h₂ hw n₁ n₂
  rcases h.2 r p w h₁ hw with e₁ | e₁
  · exact absurd e₁ n₁
  rcases h.2 r' p w h₂ hw with e₂ | e₂
  · exact absurd e₂ n₂
  rw [e₁, e₂]

end Models

/-- The local view of `p` after `k` rounds: `σ_p(w) = σ(p|w)` for `|w| ≤ k`. -/
def view (k : ℕ) (σ : MsgMap P V) (p : P) : List P → Option V :=
  fun w => if w.length ≤ k then σ (p :: w) else none

/-- A deterministic interactive-consistency algorithm: `A p τ q` is the entry for `q` computed by `p`
from its local view `τ`. -/
def Alg (P V : Type*) := P → (List P → Option V) → P → V

/-- `A` solves interactive consistency in fault model `M` with `k` rounds and at most `t` faulty
processes: for every possible `σ` in which the non-faulty processes have private values,
* **validity**: the entry of a non-faulty `q` computed by a non-faulty `p` is `q`'s private value;
* **agreement**: all non-faulty processes compute the same vector. -/
def SolvesIC (M : FaultModel P V) (k t : ℕ) (A : Alg P V) : Prop :=
  ∀ (F : Finset P) (σ : MsgMap P V), F.card ≤ t → M k F σ → (∀ q, q ∉ F → σ [q] ≠ none) →
    (∀ p q, p ∉ F → q ∉ F → σ [q] = some (A p (view k σ p) q)) ∧
    (∀ p p' q, p ∉ F → p' ∉ F → A p (view k σ p) q = A p' (view k σ p') q)

/-- Interactive consistency is solvable in fault model `M` with at most `t` faults (with some finite
number of rounds). -/
def ICSolvable (M : FaultModel P V) (t : ℕ) : Prop := ∃ k A, SolvesIC M k t A

/-! ### Basic lemmas -/

lemma seq_cons_cons {a b : P} {l : List P} : Seq (a :: b :: l) ↔ a ≠ b ∧ Seq (b :: l) :=
  List.isChain_cons_cons

lemma Seq.tail {a : P} {l : List P} (h : Seq (a :: l)) : Seq l := List.IsChain.tail h

lemma seq_pair {a b : P} : Seq [a, b] ↔ a ≠ b := by
  simp [Seq]

lemma seq_append_singleton {l : List P} {q : P} :
    Seq (l ++ [q]) ↔ Seq l ∧ ∀ x ∈ l.getLast?, x ≠ q := by
  simp [Seq, List.isChain_append]

lemma view_of_le {k : ℕ} {σ : MsgMap P V} {p : P} {w : List P} (h : w.length ≤ k) :
    view k σ p w = σ (p :: w) := by simp [view, h]

end NonEquivocation
