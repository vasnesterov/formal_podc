import Mathlib

-- CSLib candidate: Cslib/Computability/Distributed/CongestedClique/Phases.lean

/-!
# Phase programs on the congested clique

A model of deterministic algorithms on the *congested clique*: the node set `V` is finite and
fully connected, computation proceeds in synchronous rounds, and in each round every node may send
one *word* (an element of `W`, standing for an `O(log n)`-bit message) to every node. Local
computation is free and unbounded. There are no failures and no randomness.

An algorithm is a `Prog V W σ ρ`: a finite sequence of communication *steps* that turns the vector
of node states `V → σ` (initially: the node inputs) into a vector of node states `V → ρ` (finally:
the node outputs). Node identifiers are known (every function takes the node `v` as argument).
In a step, node `u` computes from its own state, for every node `v`, a list of words
`send u (s u) v`; then node `v` computes its new state from its own old state and the lists
`fun u => send u (s u) v` it received. Each step is therefore local by construction: nothing a
node computes depends on the state of another node except through received words.

A step is executed in one of two modes:

* `Mode.direct`: the lists are sent over the direct links, one word per ordered pair per round.
  Such a step takes as many rounds as the longest list (`width`). This is exactly the congested
  clique; no assumption is involved.
* `Mode.routed`: the words are delivered by Lenzen's deterministic routing algorithm
  (C. Lenzen, *Optimal deterministic routing and sorting on the congested clique*, PODC 2013,
  Theorem 3.7), which requires every node to send at most `|V|` and to receive at most `|V|`
  words, and takes `lenzenRounds = 16` rounds. Each routed message carries its source and its
  index at the source, so the receiver can sort the received words by source and index; this is
  why the receiver gets the same per-source lists as in a direct step. Lenzen's theorem itself is
  formalized in `Papers/PODC2013/CongestedCliqueRouting` (`theorem_3_7`, for opaque messages);
  here it is the cost model of a routed step, not composed with that formalization.

`rounds P s` is the number of rounds of the run of `P` from `s`, and `Valid ok P s` says that all
words sent satisfy `ok` (used to bound the bit size of words) and that every routed step respects
Lenzen's load bounds.
-/

namespace Cslib.CongestedClique

/-- How a communication step is executed: over the direct links, or by Lenzen's routing. -/
inductive Mode where
  | direct
  | routed
  deriving DecidableEq

/-- A program on the congested clique with node set `V` and words `W`, transforming node states
of type `σ` into node states of type `ρ`. -/
inductive Prog (V W : Type) : Type → Type → Type 1 where
  /-- The empty program. -/
  | done (σ : Type) : Prog V W σ σ
  /-- One communication step followed by the program `rest`: node `u` in state `s u` sends the
  list `send u (s u) v` to node `v`; node `v` in state `s v` that received the lists `m`
  (`m u` from `u`) moves to state `recv v (s v) m`. -/
  | step {σ τ ρ : Type} (mode : Mode) (send : V → σ → V → List W)
      (recv : V → σ → (V → List W) → τ) (rest : Prog V W τ ρ) : Prog V W σ ρ

/-- Rounds taken by one execution of Lenzen's routing algorithm (Lenzen, PODC 2013,
Theorem 3.7; `CongestedCliqueRouting.theorem_3_7`). -/
def lenzenRounds : ℕ := 16

namespace Prog

variable {V W : Type}

/-- The state vector after one step. -/
def next {σ τ : Type} (send : V → σ → V → List W) (recv : V → σ → (V → List W) → τ)
    (s : V → σ) : V → τ :=
  fun v => recv v (s v) (fun u => send u (s u) v)

/-- The final state vector of the run of `P` from the state vector `s`. -/
def run : {σ ρ : Type} → Prog V W σ ρ → (V → σ) → V → ρ
  | _, _, done _, s => s
  | _, _, step _ send recv rest, s => rest.run (next send recv s)

/-- The longest list sent over an ordered pair in a step. -/
def width [Fintype V] {σ : Type} (send : V → σ → V → List W) (s : V → σ) : ℕ :=
  Finset.univ.sup fun p : V × V => (send p.1 (s p.1) p.2).length

/-- The number of rounds of the run of `P` from `s`: a direct step takes `width` rounds, a routed
step `lenzenRounds` rounds. -/
def rounds [Fintype V] : {σ ρ : Type} → Prog V W σ ρ → (V → σ) → ℕ
  | _, _, done _, _ => 0
  | _, _, step .direct send recv rest, s => width send s + rest.rounds (next send recv s)
  | _, _, step .routed send recv rest, s => lenzenRounds + rest.rounds (next send recv s)

/-- Lenzen's load condition: every node sends at most `|V|` and receives at most `|V|` words. -/
def LoadOK [Fintype V] {σ : Type} (send : V → σ → V → List W) (s : V → σ) : Prop :=
  (∀ u, ∑ v, (send u (s u) v).length ≤ Fintype.card V) ∧
    (∀ v, ∑ u, (send u (s u) v).length ≤ Fintype.card V)

/-- The run of `P` from `s` is valid: every word sent satisfies `ok`, and every routed step
satisfies Lenzen's load condition. -/
def Valid [Fintype V] (ok : W → Prop) : {σ ρ : Type} → Prog V W σ ρ → (V → σ) → Prop
  | _, _, done _, _ => True
  | _, _, step m send recv rest, s =>
      (∀ u v, ∀ w ∈ send u (s u) v, ok w) ∧ (m = .routed → LoadOK send s) ∧
        rest.Valid ok (next send recv s)

/-- Sequential composition. -/
def append : {σ τ ρ : Type} → Prog V W σ τ → Prog V W τ ρ → Prog V W σ ρ
  | _, _, _, done _, Q => Q
  | _, _, _, step m send recv rest, Q => step m send recv (rest.append Q)

/-- A purely local computation (a direct step without messages). -/
def compute {σ τ : Type} (f : V → σ → τ) : Prog V W σ τ :=
  step .direct (fun _ _ _ => []) (fun v s _ => f v s) (done τ)

@[simp] lemma run_done {σ : Type} (s : V → σ) : (done σ : Prog V W σ σ).run s = s := rfl

@[simp] lemma run_step {σ τ ρ : Type} (m : Mode) (send : V → σ → V → List W)
    (recv : V → σ → (V → List W) → τ) (rest : Prog V W τ ρ) (s : V → σ) :
    (step m send recv rest).run s = rest.run (next send recv s) := rfl

@[simp] lemma run_append {σ τ ρ : Type} (P : Prog V W σ τ) (Q : Prog V W τ ρ) (s : V → σ) :
    (P.append Q).run s = Q.run (P.run s) := by
  induction P with
  | done => rfl
  | step m send recv rest ih => exact ih _ _

@[simp] lemma run_compute {σ τ : Type} (f : V → σ → τ) (s : V → σ) :
    (compute f : Prog V W σ τ).run s = fun v => f v (s v) := rfl

section Fintype

variable [Fintype V]

@[simp] lemma rounds_done {σ : Type} (s : V → σ) : (done σ : Prog V W σ σ).rounds s = 0 := rfl

lemma rounds_step_direct {σ τ ρ : Type} (send : V → σ → V → List W)
    (recv : V → σ → (V → List W) → τ) (rest : Prog V W τ ρ) (s : V → σ) :
    (step .direct send recv rest).rounds s = width send s + rest.rounds (next send recv s) := rfl

lemma rounds_step_routed {σ τ ρ : Type} (send : V → σ → V → List W)
    (recv : V → σ → (V → List W) → τ) (rest : Prog V W τ ρ) (s : V → σ) :
    (step .routed send recv rest).rounds s = lenzenRounds + rest.rounds (next send recv s) := rfl

@[simp] lemma rounds_append {σ τ ρ : Type} (P : Prog V W σ τ) (Q : Prog V W τ ρ) (s : V → σ) :
    (P.append Q).rounds s = P.rounds s + Q.rounds (P.run s) := by
  induction P with
  | done => simp [append]
  | step m send recv rest ih =>
    cases m <;> simp only [append, rounds, run_step, ih] <;> omega

@[simp] lemma valid_done (ok : W → Prop) {σ : Type} (s : V → σ) :
    (done σ : Prog V W σ σ).Valid ok s := trivial

@[simp] lemma valid_append (ok : W → Prop) {σ τ ρ : Type} (P : Prog V W σ τ) (Q : Prog V W τ ρ)
    (s : V → σ) : (P.append Q).Valid ok s ↔ P.Valid ok s ∧ Q.Valid ok (P.run s) := by
  induction P with
  | done => simp [append, Valid]
  | step m send recv rest ih =>
    simp only [append, Valid, ih, run_step]
    tauto

lemma width_le_iff {σ : Type} (send : V → σ → V → List W) (s : V → σ) (B : ℕ) :
    width send s ≤ B ↔ ∀ u v, (send u (s u) v).length ≤ B := by
  simp [width, Finset.sup_le_iff]

@[simp] lemma rounds_compute {σ τ : Type} (f : V → σ → τ) (s : V → σ) :
    (compute f : Prog V W σ τ).rounds s = 0 := by
  simp [compute, rounds_step_direct, width]

@[simp] lemma valid_compute (ok : W → Prop) {σ τ : Type} (f : V → σ → τ) (s : V → σ) :
    (compute f : Prog V W σ τ).Valid ok s := by
  simp [compute, Valid]

end Fintype

end Prog

end Cslib.CongestedClique
