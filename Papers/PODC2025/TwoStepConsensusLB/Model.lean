import Mathlib
-- CSLib candidate: crash-fault partially synchronous model (generic, not paper-specific).

/-!
# Crash-prone partially synchronous message passing (Ryabinin–Gotsman–Sutra, PODC 2025, §2)

A discrete-time model of `n = Fintype.card P` deterministic processes that may **crash**,
communicating over point-to-point links in the partially synchronous model of Dwork, Lynch and
Stockmeyer. One time unit is the known message delay bound `Δ`; *round `k`* of the paper is the
time step `τ = k - 1`.

## Shape

* A `Protocol` is a family of deterministic state machines. At every time `τ` at which it is alive,
  process `p`
  1. receives the list `inbox p τ` of the messages delivered at time `τ` (pairs sender/message),
     in an order chosen by the adversary, and possibly an invocation `inv p τ : Option V`
     (for a consensus *task* this is the input at time `0`; for a consensus *object* it is a call
     `propose(v)`),
  2. moves to `st (τ + 1) p = step p τ (st τ p) (inv p τ) (inbox p τ)` (it knows the time `τ`:
     clocks are synchronized),
  3. sends `send p (st (τ + 1) p) q` to every `q` (these messages are *sent at time `τ`*).
  Its current decision (output) is `decide p (st τ p)`.
* A `Run` is the adversary's choice only: crash times (`crash p = some c`: `p` takes its steps at
  the times `τ < c` and none afterwards; `none`: `p` is correct), the GST, the invocations, the
  delivery time `dl q τ p` of the batch of messages sent by `q` at time `τ` to `p` (a batch with
  `dl q τ p ≤ τ` is lost) and the order `ord p τ` in which a process gets the messages delivered to
  it at time `τ`. States are computed (`Run.st`).
* `Run.Valid f`: at most `f` processes crash, `ord` only permutes, and links between *correct*
  processes are reliable and timely after GST: a batch sent at `τ` arrives in
  `[τ + 1, max τ gst + 1]`. Messages from or to faulty processes may be lost (reliable links
  connect correct processes; a process that crashes may lose the messages still in transit).

Since the delivery order inside a time step is chosen by the adversary, the paper's "there exists
an `E`-faulty synchronous run" quantifies over this order (the paper's model has instantaneous
local computation, so simultaneous deliveries happen in some order).

This file also contains the consensus specifications (task and object, §2 and §A) and the
paper's Definitions 2–5 (synchronous runs, two-step runs, `e`-two-step protocols).
-/

set_option linter.unusedSectionVars false

namespace TwoStepConsensus

open Finset

/-- A deterministic distributed protocol (one state machine per process); `V` values, `M` messages,
`S` local states. -/
structure Protocol (P V M S : Type*) where
  /-- Initial state. -/
  init : P → S
  /-- Transition at time `τ`, given the invocation (if any) and the ordered list of messages
  (sender, content) delivered at this time. -/
  step : P → ℕ → S → Option V → List (P × M) → S
  /-- Messages sent by `p` in (post-step) state `s` to `q`. -/
  send : P → S → P → List M
  /-- The decision exhibited by the state. -/
  decide : P → S → Option V

/-- The adversary's choices, which determine a run of any protocol. -/
structure Run (P V M : Type*) where
  /-- Crash time (`none`: correct). A process with `crash p = some c` takes steps at `τ < c`. -/
  crash : P → Option ℕ
  /-- Global stabilization time. -/
  gst : ℕ
  /-- Invocations (inputs / calls to `propose`). -/
  inv : P → ℕ → Option V
  /-- `dl q τ p`: delivery time of the batch sent by `q` at time `τ` to `p` (lost if `≤ τ`). -/
  dl : P → ℕ → P → ℕ
  /-- Order in which `p` processes the messages delivered at time `τ`. -/
  ord : P → ℕ → List (P × M) → List (P × M)

/-- `ord` only reorders the delivered messages. -/
def IsOrder {P M : Type*} (ord : P → ℕ → List (P × M) → List (P × M)) : Prop :=
  ∀ x τ l, (ord x τ l).Perm l

theorem IsOrder.id {P M : Type*} : IsOrder (fun (_ : P) (_ : ℕ) (l : List (P × M)) => l) :=
  fun _ _ _ => List.Perm.refl _

theorem IsOrder.nil {P M : Type*} {ord : P → ℕ → List (P × M) → List (P × M)} (h : IsOrder ord)
    (x : P) (τ : ℕ) : ord x τ [] = [] :=
  List.Perm.nil_eq (h x τ []).symm |>.symm

namespace Run

variable {P V M S : Type*} [Fintype P] [DecidableEq P]
variable (A : Protocol P V M S) (R : Run P V M)

/-- `p` takes a step at time `τ`. -/
def alive (p : P) (τ : ℕ) : Bool := (R.crash p).all fun c => decide (τ < c)

theorem alive_iff {p : P} {τ : ℕ} : R.alive p τ ↔ ∀ c, R.crash p = some c → τ < c := by
  unfold alive; cases R.crash p <;> simp

theorem alive_of_crash_none {p : P} (h : R.crash p = none) (τ : ℕ) : R.alive p τ := by
  simp [alive, h]

/-- Messages sent by `q` at time `τ` to `x`, given a (partial) history `h` of states. -/
def outWith (h : ℕ → P → S) (q : P) (τ : ℕ) (x : P) : List M :=
  if R.alive q τ then A.send q (h (τ + 1) q) x else []

/-- Messages delivered to `x` at time `τ` in canonical order (by send time, then sender). -/
noncomputable def canonWith (h : ℕ → P → S) (x : P) (τ : ℕ) : List (P × M) :=
  (List.range τ).flatMap fun τ' => (Finset.univ : Finset P).toList.flatMap fun q =>
    if R.dl q τ' x = τ then (R.outWith A h q τ' x).map (Prod.mk q) else []

/-- `stUpTo τ` is a history of states, correct at all times `≤ τ`. -/
noncomputable def stUpTo : ℕ → ℕ → P → S
  | 0 => fun _ p => A.init p
  | τ + 1 => fun σ p =>
      if σ ≤ τ then stUpTo τ σ p
      else if R.alive p τ then
        A.step p τ (stUpTo τ τ p) (R.inv p τ) (R.ord p τ (R.canonWith A (stUpTo τ) p τ))
      else stUpTo τ τ p

/-- The local state of `p` at time `τ` (before its step at time `τ`). -/
noncomputable def st (τ : ℕ) (p : P) : S := R.stUpTo A τ τ p

/-- Messages sent by `q` at time `τ` to `x`. -/
noncomputable def out (q : P) (τ : ℕ) (x : P) : List M := R.outWith A (R.st A) q τ x

/-- The batch sent by `q` at time `τ'` to `x`, if it is delivered at time `τ` (else `[]`). -/
noncomputable def dlv (q : P) (τ' : ℕ) (x : P) (τ : ℕ) : List M :=
  if R.dl q τ' x = τ then R.out A q τ' x else []

/-- Messages delivered to `x` at time `τ`, in canonical order. -/
noncomputable def canon (x : P) (τ : ℕ) : List (P × M) := R.canonWith A (R.st A) x τ

/-- Messages delivered to `x` at time `τ`, in the order in which `x` processes them. -/
noncomputable def inbox (x : P) (τ : ℕ) : List (P × M) := R.ord x τ (R.canon A x τ)

theorem stUpTo_eq_of_le {τ σ : ℕ} (h : σ ≤ τ) : R.stUpTo A τ σ = R.stUpTo A σ σ := by
  induction τ with
  | zero => obtain rfl : σ = 0 := by omega
            rfl
  | succ τ ih =>
    rcases Nat.lt_or_ge σ (τ + 1) with h' | h'
    · funext p
      simp only [stUpTo, show σ ≤ τ by omega, ite_true]
      rw [ih (by omega)]
    · obtain rfl : σ = τ + 1 := by omega
      rfl

@[simp] theorem st_zero (p : P) : R.st A 0 p = A.init p := rfl

theorem canonWith_congr {h h' : ℕ → P → S} {τ : ℕ} (hh : ∀ σ ≤ τ, h σ = h' σ) (x : P) :
    R.canonWith A h x τ = R.canonWith A h' x τ := by
  unfold canonWith outWith
  refine List.flatMap_congr fun τ' hτ' => List.flatMap_congr fun q _ => ?_
  have : τ' + 1 ≤ τ := by simp at hτ'; omega
  rw [hh (τ' + 1) this]

theorem st_succ (τ : ℕ) (p : P) :
    R.st A (τ + 1) p =
      if R.alive p τ then A.step p τ (R.st A τ p) (R.inv p τ) (R.inbox A p τ) else R.st A τ p := by
  change R.stUpTo A (τ + 1) (τ + 1) p = _
  simp only [stUpTo, show ¬ τ + 1 ≤ τ by omega, ite_false]
  congr 2
  unfold inbox canon
  congr 1
  exact R.canonWith_congr A (fun σ hσ => R.stUpTo_eq_of_le A hσ) p

theorem st_succ_of_alive {τ : ℕ} {p : P} (h : R.alive p τ) :
    R.st A (τ + 1) p = A.step p τ (R.st A τ p) (R.inv p τ) (R.inbox A p τ) := by
  rw [st_succ, ite_eq_left h]

theorem st_succ_of_not_alive {τ : ℕ} {p : P} (h : R.alive p τ = false) :
    R.st A (τ + 1) p = R.st A τ p := by
  rw [st_succ, ite_eq_right (by simp [h])]

/-- A process that crashes at time `0` stays in its initial state. -/
theorem st_of_crash_zero {p : P} (h : R.crash p = some 0) (τ : ℕ) : R.st A τ p = A.init p := by
  induction τ with
  | zero => rfl
  | succ τ ih => rw [st_succ_of_not_alive A R (by simp [alive, h]), ih]

theorem out_of_alive {q : P} {τ : ℕ} (h : R.alive q τ) (x : P) :
    R.out A q τ x = A.send q (R.st A (τ + 1) q) x := by
  simp [out, outWith, h]

theorem out_of_not_alive {q : P} {τ : ℕ} (h : R.alive q τ = false) (x : P) :
    R.out A q τ x = [] := by
  simp [out, outWith, h]

theorem canon_eq_flatMap (x : P) (τ : ℕ) :
    R.canon A x τ = (List.range τ).flatMap fun τ' => (Finset.univ : Finset P).toList.flatMap
      fun q => (R.dlv A q τ' x τ).map (Prod.mk q) := by
  unfold canon canonWith dlv
  refine List.flatMap_congr fun τ' _ => List.flatMap_congr fun q _ => ?_
  split_ifs <;> rfl

theorem canon_zero (x : P) : R.canon A x 0 = [] := by
  simp [canon_eq_flatMap]

/-- Two runs deliver the same messages to `x` at time `τ` if every batch coincides. -/
theorem canon_eq_of_dlv_eq {R' : Run P V M} {x : P} {τ : ℕ}
    (h : ∀ q, ∀ τ' < τ, R.dlv A q τ' x τ = R'.dlv A q τ' x τ) :
    R.canon A x τ = R'.canon A x τ := by
  rw [canon_eq_flatMap, canon_eq_flatMap]
  refine List.flatMap_congr fun τ' hτ' => List.flatMap_congr fun q _ => ?_
  rw [h q τ' (by simpa using hτ')]

theorem inbox_eq_of_dlv_eq {R' : Run P V M} {x : P} {τ : ℕ} (ho : R.ord x τ = R'.ord x τ)
    (h : ∀ q, ∀ τ' < τ, R.dlv A q τ' x τ = R'.dlv A q τ' x τ) :
    R.inbox A x τ = R'.inbox A x τ := by
  unfold inbox; rw [ho, R.canon_eq_of_dlv_eq A h]

theorem dlv_eq_nil_of_ne {q : P} {τ' : ℕ} {x : P} {τ : ℕ} (h : R.dl q τ' x ≠ τ) :
    R.dlv A q τ' x τ = [] := by simp [dlv, h]

theorem dlv_of_eq {q : P} {τ' : ℕ} {x : P} {τ : ℕ} (h : R.dl q τ' x = τ) :
    R.dlv A q τ' x τ = R.out A q τ' x := by simp [dlv, h]

/-- **Indistinguishability principle.** Let `X` be a set of processes, each `p ∈ X` compared with
a reference run `ref p`. If the processes of `X` are alive at the same times and get the same
invocations, and — as long as all processes of `X` had the same states as in their reference
runs — they also get the same inboxes, then they have the same states up to time `T`. -/
theorem st_eq_of_inbox_eq {ref : P → Run P V M} {X : Set P} {T : ℕ}
    (hal : ∀ p ∈ X, ∀ τ < T, R.alive p τ = (ref p).alive p τ)
    (hinv : ∀ p ∈ X, ∀ τ < T, R.alive p τ → R.inv p τ = (ref p).inv p τ)
    (hin : ∀ τ < T, (∀ r ∈ X, ∀ σ ≤ τ, R.st A σ r = (ref r).st A σ r) →
      ∀ p ∈ X, R.alive p τ → R.inbox A p τ = (ref p).inbox A p τ) :
    ∀ τ ≤ T, ∀ p ∈ X, R.st A τ p = (ref p).st A τ p := by
  intro τ
  induction τ using Nat.strong_induction_on with
  | _ τ ih =>
    intro hτ p hp
    rcases τ with _ | τ
    · rfl
    · have IH : ∀ r ∈ X, ∀ σ ≤ τ, R.st A σ r = (ref r).st A σ r :=
        fun r hr σ hσ => ih σ (by omega) (by omega) r hr
      rw [st_succ, st_succ, ← hal p hp τ (by omega), IH p hp τ le_rfl]
      by_cases h : R.alive p τ
      · rw [ite_eq_left h, ite_eq_left h, hinv p hp τ (by omega) h, hin τ (by omega) IH p hp h]
      · rw [ite_eq_right h, ite_eq_right h]

/-- Runs depend only on `init`, `step` and `send`. -/
theorem st_congr {A' : Protocol P V M S} (hi : A.init = A'.init) (hs : A.step = A'.step)
    (hm : A.send = A'.send) : R.st A = R.st A' := by
  have : ∀ τ, R.stUpTo A τ = R.stUpTo A' τ := by
    intro τ
    induction τ with
    | zero => funext σ p; simp [stUpTo, hi]
    | succ τ ih =>
      funext σ p
      simp only [stUpTo, ih, hs]
      congr 4
      unfold canonWith outWith
      simp [hm]
  funext τ p; simp [st, this]

/-- The faulty processes (those that crash at some time). -/
def faulty : Finset P := Finset.univ.filter fun p => R.crash p ≠ none

/-- Model constraints: at most `f` crashes, `ord` permutes, and links between correct processes
are reliable, with delay at most one time unit after GST. -/
structure Valid (f : ℕ) (R : Run P V M) : Prop where
  card_faulty : R.faulty.card ≤ f
  ord_perm : IsOrder R.ord
  dl_ge : ∀ q τ x, R.crash q = none → R.crash x = none → τ + 1 ≤ R.dl q τ x
  dl_le : ∀ q τ x, R.crash q = none → R.crash x = none → R.dl q τ x ≤ max τ R.gst + 1

/-- `p` exhibits decision `v` at time `τ`. -/
def DecidesAt (p : P) (τ : ℕ) (v : V) : Prop := A.decide p (R.st A τ p) = some v

/-- `p` *returns* `v` at time `τ`: it exhibits the decision `v` at `τ`, after an invocation. -/
def RespondsAt (p : P) (τ : ℕ) (v : V) : Prop :=
  (∃ τ₀ < τ, R.inv p τ₀ ≠ none) ∧ R.DecidesAt A p τ v

/-- Every process invokes `propose` at most once. -/
def WellFormed : Prop := ∀ p τ τ', R.inv p τ ≠ none → R.inv p τ' ≠ none → τ = τ'

end Run

variable {P V M S : Type*} [Fintype P] [DecidableEq P]

/-! ### Consensus specifications -/

/-- Invocations of a consensus *task* with initial configuration `I`: every process gets its
input at time `0`. -/
def taskInv (I : P → V) : P → ℕ → Option V := fun p τ => if τ = 0 then some (I p) else none

/-- An `f`-resilient implementation of the consensus **task** (§2, Definition 1): in every valid
run with at most `f` crashes, Validity (every decision is the input of some process), Agreement
(no two decisions differ, including decisions of processes that crash later) and Termination
(every correct process eventually decides). -/
structure SolvesTask (A : Protocol P V M S) (f : ℕ) : Prop where
  validity : ∀ (R : Run P V M) (I : P → V), R.Valid f → R.inv = taskInv I →
    ∀ p τ v, R.DecidesAt A p τ v → ∃ q, I q = v
  agreement : ∀ (R : Run P V M) (I : P → V), R.Valid f → R.inv = taskInv I →
    ∀ p q τ τ' v w, R.DecidesAt A p τ v → R.DecidesAt A q τ' w → v = w
  termination : ∀ (R : Run P V M) (I : P → V), R.Valid f → R.inv = taskInv I →
    ∀ p, R.crash p = none → ∃ τ v, R.DecidesAt A p τ v

/-- An `f`-resilient implementation of the consensus **object** (§2): in every valid run in which
every process calls `propose` at most once, responses agree, every response was proposed before
it was returned (together: linearizability w.r.t. the sequential consensus object), and every
call by a correct process returns (wait-freedom). -/
structure SolvesObject (A : Protocol P V M S) (f : ℕ) : Prop where
  validity : ∀ (R : Run P V M), R.Valid f → R.WellFormed →
    ∀ p τ v, R.RespondsAt A p τ v → ∃ q, ∃ τ₁ < τ, R.inv q τ₁ = some v
  agreement : ∀ (R : Run P V M), R.Valid f → R.WellFormed →
    ∀ p q τ τ' v w, R.RespondsAt A p τ v → R.RespondsAt A q τ' w → v = w
  waitFree : ∀ (R : Run P V M), R.Valid f → R.WellFormed →
    ∀ p τ₀ v, R.crash p = none → R.inv p τ₀ = some v → ∃ τ w, R.RespondsAt A p τ w

/-! ### Synchronous runs and two-step protocols -/

/-- **Definition 2** (`E`-faulty synchronous run): the processes of `E` crash at the beginning of
the first round, all others are correct, every message sent in a round is delivered at the
beginning of the next one. The invocations and the delivery order are parameters. -/
def syncRun (E : Finset P) (inv : P → ℕ → Option V) (ord : P → ℕ → List (P × M) → List (P × M)) :
    Run P V M where
  crash p := if p ∈ E then some 0 else none
  gst := 0
  inv := inv
  dl _ τ _ := τ + 1
  ord := ord

/-- **Definition 3** (task version): the run is *two-step for `p`*: `p` decides by time `2Δ`, i.e.
in its state after the step at time `2`. -/
def Run.DecidedBy2 (A : Protocol P V M S) (R : Run P V M) (p : P) : Prop :=
  ∃ τ ≤ 3, ∃ v, R.DecidesAt A p τ v

/-- **Definition 3** (object version): `p` returns by time `2Δ`. -/
def Run.RespondedBy2 (A : Protocol P V M S) (R : Run P V M) (p : P) : Prop :=
  ∃ τ ≤ 3, ∃ v, R.RespondsAt A p τ v

/-- **Definition 4** (`e`-two-step consensus task). For every `E` with `|E| = e`:
(1) from every initial configuration some `E`-faulty synchronous run is two-step for some
process; (2) from every initial configuration in which the processes outside `E` propose the same
value, for every `p ∉ E` some `E`-faulty synchronous run is two-step for `p`. -/
def TwoStepTask (A : Protocol P V M S) (e : ℕ) : Prop :=
  ∀ E : Finset P, E.card = e →
    (∀ I : P → V, ∃ ord, IsOrder ord ∧ ∃ p, (syncRun (M := M) E (taskInv I) ord).DecidedBy2 A p) ∧
    (∀ I : P → V, (∀ p ∉ E, ∀ q ∉ E, I p = I q) →
      ∀ p ∉ E, ∃ ord, IsOrder ord ∧ (syncRun (M := M) E (taskInv I) ord).DecidedBy2 A p)

/-- Only `p` calls `propose(v)`, at time `t₀`. -/
def singleInv (p : P) (t₀ : ℕ) (v : V) : P → ℕ → Option V :=
  fun q τ => if q = p ∧ τ = t₀ then some v else none

/-- All processes outside `E` call `propose(v)` at the beginning of the first round. -/
def allInv (E : Finset P) (v : V) : P → ℕ → Option V :=
  fun q τ => if τ = 0 ∧ q ∉ E then some v else none

/-- **Definition 5** (`e`-two-step consensus object, §A). For every `E` with `|E| = e`, every value
`v` and every `p ∉ E`: (1) some `E`-faulty synchronous run in which only `p` calls `propose(v)`
is two-step for `p`; (2) some `E`-faulty synchronous run in which all processes outside `E` call
`propose(v)` at the beginning is two-step for `p`. (The paper does not say when `p` calls
`propose` in (1); we allow any time.) -/
def TwoStepObject (A : Protocol P V M S) (e : ℕ) : Prop :=
  ∀ E : Finset P, E.card = e →
    (∀ (v : V), ∀ p ∉ E, ∃ t₀ ord, IsOrder ord ∧
      (syncRun (M := M) E (singleInv p t₀ v) ord).RespondedBy2 A p) ∧
    (∀ (v : V), ∀ p ∉ E, ∃ ord, IsOrder ord ∧
      (syncRun (M := M) E (allInv E v) ord).RespondedBy2 A p)

/-! ### Basic facts about synchronous runs -/

theorem syncRun_crash_of_mem {E : Finset P} {inv : P → ℕ → Option V}
    {ord : P → ℕ → List (P × M) → List (P × M)} {p : P} (h : p ∈ E) :
    (syncRun E inv ord).crash p = some 0 := by simp [syncRun, h]

theorem syncRun_crash_of_not_mem {E : Finset P} {inv : P → ℕ → Option V}
    {ord : P → ℕ → List (P × M) → List (P × M)} {p : P} (h : p ∉ E) :
    (syncRun E inv ord).crash p = none := by simp [syncRun, h]

theorem syncRun_faulty (E : Finset P) (inv : P → ℕ → Option V)
    (ord : P → ℕ → List (P × M) → List (P × M)) : (syncRun E inv ord).faulty = E := by
  ext p; by_cases h : p ∈ E <;> simp [Run.faulty, syncRun, h]

theorem syncRun_valid {f : ℕ} {E : Finset P} (hE : E.card ≤ f) (inv : P → ℕ → Option V)
    {ord : P → ℕ → List (P × M) → List (P × M)} (ho : IsOrder ord) :
    (syncRun E inv ord).Valid f where
  card_faulty := by rw [syncRun_faulty]; exact hE
  ord_perm := ho
  dl_ge _ _ _ _ _ := le_rfl
  dl_le _ τ _ _ _ := by simp [syncRun]

end TwoStepConsensus
