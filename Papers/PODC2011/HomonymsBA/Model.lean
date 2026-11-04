-- CSLib candidate: Cslib/Computability/Distributed/Homonyms/Model.lean
import Mathlib

/-!
# Byzantine agreement with homonyms: the model

Delporte-Gallet, Fauconnier, Guerraoui, Kermarrec, Ruppert, Tran-The, *Byzantine Agreement with
Homonyms*, PODC 2011, Section 2.

* `n` processes (a finite type `P` with `Fintype.card P = n`) share `ℓ` authenticated identifiers:
  `id : P → Fin ℓ` is surjective (every identifier is assigned to at least one process).
* An `Algorithm ℓ V M S` is deterministic and identical for processes with the same identifier:
  `init i v` is the initial state of a process with identifier `i` and input `v`; in every round
  a process in state `s` sends `send s j : Option M` to *all* processes with identifier `j` (it
  cannot address a single process); then it receives the **multiset** of `(identifier, message)`
  pairs sent to it in the round and moves to `step s inbox`. Decisions are read off the state
  (`decide s`). A process also receives its own message.
* *Numerate* processes see the multiset; *innumerate* processes only see the underlying set:
  `Algorithm.Innumerate` (the transition depends only on the set of received pairs).
* A `Run` is the adversary's choice: the identifier assignment, the (static) Byzantine set, the
  inputs, the global stabilization round `gst`, which messages between correct processes are lost
  (`drop`, only before `gst`), and the multiset of pairs that the Byzantine processes deliver to
  each process in each round (`adv`; every pair must carry the identifier of some Byzantine
  process: identifiers cannot be forged). States are computed (`Run.st`).
* *Restricted* Byzantine processes send at most one message per recipient per round: at most
  `#{b ∈ byz | id b = j}` pairs tagged `j` per recipient and round (`Run.Restricted`).
* *Synchronous* runs have `gst = 0` (no loss); *partially synchronous* runs (the basic model of
  Dwork, Lynch and Stockmeyer) lose finitely many messages, i.e. none from round `gst` on.

Byzantine agreement (`Run.BA`): termination, agreement (also for `p = q`: a correct process never
changes its decision) and validity (if all correct processes have input `v`, only `v` is decided).
An algorithm *solves* BA for `(n, ℓ, t)` if this holds in every admissible run of every `n`-process
system with `ℓ` identifiers and at most `t` Byzantine processes, whatever the identifier
assignment (`Solves`).
-/

namespace Podc.HomonymsBA

open Finset

/-- A deterministic algorithm for processes with identifiers in `Fin ℓ`, inputs and decisions in
`V`, messages `M` and local states `S`. -/
structure Algorithm (ℓ : ℕ) (V M S : Type*) where
  /-- Initial state of a process with identifier `i` and input `v`. -/
  init : Fin ℓ → V → S
  /-- The message sent in state `s` to all processes with identifier `j` (if any). -/
  send : S → Fin ℓ → Option M
  /-- Transition after receiving the multiset of `(sender identifier, message)` pairs. -/
  step : S → Multiset (Fin ℓ × M) → S
  /-- The decision exhibited by a state (`none`: not decided). -/
  decide : S → Option V

/-- Innumerate processes cannot count copies of identical messages: the transition depends only
on the *set* of received pairs. -/
def Algorithm.Innumerate {ℓ : ℕ} {V M S : Type*} (A : Algorithm ℓ V M S) : Prop :=
  ∀ s (m m' : Multiset (Fin ℓ × M)), (∀ x, x ∈ m ↔ x ∈ m') → A.step s m = A.step s m'

/-- The adversary's choices; states are computed from them (`Run.st`). -/
structure Run (P : Type*) (ℓ : ℕ) (V M : Type*) where
  /-- The identifier assignment. -/
  id : P → Fin ℓ
  /-- The Byzantine processes. -/
  byz : Finset P
  /-- The inputs (irrelevant for Byzantine processes). -/
  inp : P → V
  /-- Global stabilization round: no message between correct processes is lost from it on. -/
  gst : ℕ
  /-- `drop r q p`: the message of correct `q` to `p` in round `r` is lost. -/
  drop : ℕ → P → P → Prop
  /-- `adv r p`: the pairs that Byzantine processes deliver to `p` in round `r`. -/
  adv : ℕ → P → Multiset (Fin ℓ × M)

/-- An `Option` as a multiset with at most one element. -/
def oms {α : Type*} (o : Option α) : Multiset α := (o.toList : Multiset α)

@[simp] lemma oms_none {α : Type*} : oms (none : Option α) = 0 := rfl
@[simp] lemma oms_some {α : Type*} (a : α) : oms (some a) = {a} := rfl
@[simp] lemma mem_oms {α : Type*} {o : Option α} {a : α} : a ∈ oms o ↔ o = some a := by
  cases o <;> simp [oms, eq_comm]

namespace Run

variable {P : Type*} [Fintype P] {ℓ : ℕ} {V M S : Type*}
variable (A : Algorithm ℓ V M S) (R : Run P ℓ V M)

/-- The pairs `p` receives from correct `q` in a round, when `q` is in state `s`. -/
def msgFrom (s : S) (q p : P) : Multiset (Fin ℓ × M) :=
  oms ((A.send s (R.id p)).map fun m => (R.id q, m))

open Classical in
/-- The multiset received by `p` in round `r`, when the correct processes are in states `st`. -/
noncomputable def inboxWith (st : P → S) (r : ℕ) (p : P) : Multiset (Fin ℓ × M) :=
  (∑ q ∈ univ.filter (fun q => q ∉ R.byz ∧ ¬ R.drop r q p), R.msgFrom A (st q) q p) + R.adv r p

/-- `R.st A r p`: the state of `p` at the beginning of round `r` (meaningful for correct `p`). -/
noncomputable def st : ℕ → P → S
  | 0 => fun p => A.init (R.id p) (R.inp p)
  | r + 1 => fun p => A.step (st r p) (R.inboxWith A (st r) r p)

/-- The multiset received by `p` in round `r`. -/
noncomputable def inbox (r : ℕ) (p : P) : Multiset (Fin ℓ × M) := R.inboxWith A (R.st A r) r p

@[simp] lemma st_zero (p : P) : R.st A 0 p = A.init (R.id p) (R.inp p) := rfl

lemma st_succ (r : ℕ) (p : P) : R.st A (r + 1) p = A.step (R.st A r p) (R.inbox A r p) := rfl

/-- `p` decides `v` (at some round). -/
def Decides (p : P) (v : V) : Prop := ∃ r, A.decide (R.st A r p) = some v

/-- **Byzantine agreement** in a run: termination, agreement, validity (for correct processes). -/
structure BA : Prop where
  termination : ∀ p ∉ R.byz, ∃ v, R.Decides A p v
  agreement : ∀ p ∉ R.byz, ∀ q ∉ R.byz, ∀ v w, R.Decides A p v → R.Decides A q w → v = w
  validity : ∀ v, (∀ p ∉ R.byz, R.inp p = v) → ∀ p ∉ R.byz, ∀ w, R.Decides A p w → w = v

/-- Basic model constraints: identifiers surjective, at most `t` Byzantine processes, Byzantine
pairs carry Byzantine identifiers, no loss between correct processes from `gst` on. -/
structure Valid (t : ℕ) : Prop where
  surj : Function.Surjective R.id
  card_byz : R.byz.card ≤ t
  adv_id : ∀ r p, ∀ x ∈ R.adv r p, ∃ b ∈ R.byz, R.id b = x.1
  no_drop : ∀ r q p, R.gst ≤ r → q ∉ R.byz → p ∉ R.byz → ¬ R.drop r q p

open Classical in
/-- Restricted Byzantine processes: each sends at most one message per recipient and round. -/
def Restricted : Prop :=
  ∀ r p (j : Fin ℓ), ((R.adv r p).filter (·.1 = j)).card ≤ (R.byz.filter (R.id · = j)).card

end Run

/-- Timing models. -/
inductive Timing
  /-- Synchronous rounds (`gst = 0`). -/
  | sync
  /-- Basic partially synchronous model (finitely many losses). -/
  | psync

/-- Power of the Byzantine processes. -/
inductive Power
  /-- Any number of messages per recipient and round. -/
  | unrestricted
  /-- At most one message per recipient and round. -/
  | restricted

/-- Can correct processes count identical messages? -/
inductive Counting
  | numerate
  | innumerate

namespace Run

variable {P : Type*} [Fintype P] {ℓ : ℕ} {V M : Type*}

/-- Admissible runs of a model. -/
def Admissible (t : ℕ) (τ : Timing) (π : Power) (R : Run P ℓ V M) : Prop :=
  R.Valid t ∧ (τ = .sync → R.gst = 0) ∧ (π = .restricted → R.Restricted)

end Run

/-- `A` **solves Byzantine agreement** for `n` processes, `ℓ` identifiers and at most `t`
Byzantine processes in the model `(τ, π)`: in every admissible run of every `n`-process system
(every identifier assignment), Byzantine agreement holds. -/
def Solves {ℓ : ℕ} {V M S : Type*} (τ : Timing) (π : Power) (n t : ℕ)
    (A : Algorithm ℓ V M S) : Prop :=
  ∀ (P : Type) [Fintype P] [DecidableEq P], Fintype.card P = n →
    ∀ R : Run P ℓ V M, R.Admissible t τ π → R.BA A

/-- The algorithm class of a counting model. -/
def Counting.Allows {ℓ : ℕ} {V M S : Type*} : Counting → Algorithm ℓ V M S → Prop
  | .numerate, _ => True
  | .innumerate, A => A.Innumerate

/-- Byzantine agreement with values in `V` is **solvable** for `(n, ℓ, t)` in the model
`(τ, π, κ)`. -/
def Solvable (τ : Timing) (π : Power) (κ : Counting) (n ℓ t : ℕ) (V : Type) : Prop :=
  ∃ (M S : Type) (A : Algorithm ℓ V M S), κ.Allows A ∧ Solves τ π n t A

end Podc.HomonymsBA
