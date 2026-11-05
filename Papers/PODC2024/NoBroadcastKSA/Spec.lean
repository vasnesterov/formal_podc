import Mathlib.Tactic
import Mathlib.Data.List.Basic

/-!
# Broadcast abstractions, their symmetry properties, and algorithms on top of them

Gay, Mostéfaoui, Perrin, *No Broadcast Abstraction Characterizes k-Set-Agreement in
Message-Passing Systems* (PODC 2024 brief announcement; extended version HAL hal-04571653).

## Broadcast level (Sections 3.1, 3.2, Definition 5)

A *B-execution* (`BExec`) records the events of a broadcast abstraction at the times they occur
(`none` = no event of the abstraction at that time), together with the set of correct processes:

* `bc p m`  — `p` invokes `B.broadcast(m)`;
* `ret p m` — `p` returns from `B.broadcast(m)`;
* `dl p q m` — `p` B-delivers `m` from `q`.

A message is identified by its sender and its message object `m : M`; a process never broadcasts
the same object twice (`UniqueBc`, the paper's "each broadcast message is unique, regardless of
having identical content"). At the algorithm level the message objects are pairs
`(id, content) : ℕ × C`: the algorithm chooses the content, the identifier is arbitrary (chosen by
the environment, e.g. a local sequence number).

A *broadcast abstraction* is a set `S` of B-executions, all of which satisfy the four properties
of Section 3.1 (BC-Validity, BC-No-Duplication, BC-Local-Termination, BC-Global-CS-Termination)
and the well-formedness of the invocations (Definition 1).

* `Compositional S` (Definition 2): `S` is closed under restriction to any set of messages.
* `ContentNeutral S` (Definition 3): `S` is closed under injective renaming of the messages
  (sender-preserving: the renaming may depend on the sender).
* `NSolo N E` (Definition 5).

## Algorithm level (`CAMP_n[B]`, Section 2)

An algorithm `A` (`Algo`) is deterministic: the next action of process `p` (broadcast a content,
decide a value, or wait) is a function of its proposal and its local history (its own
invocations, returns, deliveries and decisions). An
execution of `A` on top of `S` (`AExec`, `Admissible`) is a sequence of steps whose projection to
the broadcast events belongs to `S`, whose steps of `A` follow `A`, and in which every correct
process takes infinitely many steps of `A`. `SolvesKSA k A S`: every admissible execution
satisfies k-SA-Validity, k-SA-Agreement and k-SA-Termination (Section 4.1).

Model simplification: `A` uses only the broadcast abstraction, no point-to-point channels.
The algorithms we consider (`Counterexample.lean`) never use point-to-point channels, so this is a
sub-case of the paper's `CAMP_n[B]`.
-/

namespace Podc.NoBroadcastKSA

set_option linter.unusedSectionVars false

/-! ## Broadcast executions -/

/-- Events of a broadcast abstraction. -/
inductive BEv (P M : Type) where
  /-- `p` invokes `B.broadcast(m)`. -/
  | bc (p : P) (m : M)
  /-- `p` returns from `B.broadcast(m)`. -/
  | ret (p : P) (m : M)
  /-- `p` B-delivers `m` from `q`. -/
  | dl (p q : P) (m : M)
  deriving DecidableEq

namespace BEv

variable {P M : Type}

/-- The message (sender, content) an event is about. -/
def msg : BEv P M → P × M
  | bc p m => (p, m)
  | ret p m => (p, m)
  | dl _ q m => (q, m)

/-- Renaming of the messages by `r` (the content of a message of sender `q` becomes `r q m`). -/
def rename (r : P → M → M) : BEv P M → BEv P M
  | bc p m => bc p (r p m)
  | ret p m => ret p (r p m)
  | dl p q m => dl p q (r q m)

end BEv

/-- An execution of a broadcast abstraction: the event at each time (if any), and the set of
correct processes. -/
structure BExec (P M : Type) where
  /-- The event of the abstraction at time `t`, if any. -/
  ev : ℕ → Option (BEv P M)
  /-- The correct processes. -/
  correct : Set P

namespace BExec

variable {P M : Type} (E : BExec P M)

/-- **BC-Validity.** If `p` B-delivers `m` from `q`, then `q` has previously B-broadcast `m`. -/
def Validity : Prop :=
  ∀ (t : ℕ) (p q : P) (m : M), E.ev t = some (.dl p q m) →
    ∃ t' < t, E.ev t' = some (.bc q m)

/-- **BC-No-Duplication.** A process B-delivers a message at most once. -/
def NoDuplication : Prop :=
  ∀ (t t' : ℕ) (p q : P) (m : M), E.ev t = some (.dl p q m) → E.ev t' = some (.dl p q m) → t = t'

/-- Each broadcast message is unique: a process never broadcasts the same content twice. -/
def UniqueBc : Prop :=
  ∀ (t t' : ℕ) (p : P) (m : M), E.ev t = some (.bc p m) → E.ev t' = some (.bc p m) → t = t'

/-- Well-formedness (Definition 1): a return answers a previous invocation and happens at most
once, and a process invokes `broadcast` only after returning from its previous invocations. -/
structure WellFormed : Prop where
  ret_bc : ∀ (t : ℕ) (p : P) (m : M), E.ev t = some (.ret p m) → ∃ t' < t, E.ev t' = some (.bc p m)
  ret_unique : ∀ (t t' : ℕ) (p : P) (m : M), E.ev t = some (.ret p m) →
    E.ev t' = some (.ret p m) → t = t'
  seq : ∀ (t t' : ℕ) (p : P) (m m' : M), t' < t → E.ev t = some (.bc p m) →
    E.ev t' = some (.bc p m') → ∃ s, t' < s ∧ s < t ∧ E.ev s = some (.ret p m')

/-- **BC-Local-Termination.** A correct process returns from each of its invocations. -/
def LocalTermination : Prop :=
  ∀ (t : ℕ) (p : P) (m : M), p ∈ E.correct → E.ev t = some (.bc p m) →
    ∃ t' > t, E.ev t' = some (.ret p m)

/-- **BC-Global-CS-Termination.** A message B-broadcast by a correct process is B-delivered by
every correct process. -/
def GlobalCSTermination : Prop :=
  ∀ (t : ℕ) (q : P) (m : M), q ∈ E.correct → E.ev t = some (.bc q m) →
    ∀ p ∈ E.correct, ∃ t', E.ev t' = some (.dl p q m)

/-- The properties shared by all broadcast abstractions (Section 3.1). -/
structure IsBroadcast : Prop where
  validity : E.Validity
  noDup : E.NoDuplication
  uniqueBc : E.UniqueBc
  wf : E.WellFormed
  localTerm : E.LocalTermination
  globalCS : E.GlobalCSTermination

open Classical in
/-- The restriction of `E` to the messages of `X` (Definition 2): the events about other
messages are erased. -/
noncomputable def restrict (X : Set (P × M)) : BExec P M where
  ev t := (E.ev t).bind fun e => if e.msg ∈ X then some e else none
  correct := E.correct

/-- The execution obtained by replacing every message `m` of sender `q` by `r q m`
(Definition 3). -/
def rename (r : P → M → M) : BExec P M where
  ev t := (E.ev t).map (BEv.rename r)
  correct := E.correct

/-- **Definition 5** (`N`-solo executions). There are `N` messages `sel p 0, …, sel p (N-1)`
B-broadcast by each process `p` such that, for all distinct `p`, `q`, `p` B-delivers all its
own messages `sel p _` before B-delivering any of the messages `sel q _`. -/
def NSolo (N : ℕ) : Prop :=
  ∃ sel : P → Fin N → M, (∀ p, Function.Injective (sel p)) ∧
    (∀ p j, ∃ t, E.ev t = some (.bc p (sel p j))) ∧
    ∀ p q, p ≠ q → ∀ (j' : Fin N) (t : ℕ), E.ev t = some (.dl p q (sel q j')) →
      ∀ j : Fin N, ∃ t' < t, E.ev t' = some (.dl p p (sel p j))

end BExec

/-- A broadcast abstraction: a set of B-executions satisfying the properties of Section 3.1. -/
def IsBroadcastAbstraction {P M : Type} (S : Set (BExec P M)) : Prop :=
  ∀ E ∈ S, E.IsBroadcast

/-- **Definition 2** (Compositionality). The restriction of an admitted execution to any set of
messages is admitted. -/
def Compositional {P M : Type} (S : Set (BExec P M)) : Prop :=
  ∀ E ∈ S, ∀ X : Set (P × M), E.restrict X ∈ S

/-- **Definition 3** (Content-Neutrality). Replacing the messages of an admitted execution
injectively gives an admitted execution. -/
def ContentNeutral {P M : Type} (S : Set (BExec P M)) : Prop :=
  ∀ E ∈ S, ∀ r : P → M → M, (∀ p, Function.Injective (r p)) → E.rename r ∈ S

/-! ## Algorithms on top of a broadcast abstraction -/

/-- The local events of a process, as seen by the algorithm running on it. -/
inductive LEv (P M V : Type) where
  /-- the process invoked `B.broadcast(m)` -/
  | bc (m : M)
  /-- the process returned from `B.broadcast(m)` -/
  | ret (m : M)
  /-- the process B-delivered `m` from `q` -/
  | dl (q : P) (m : M)
  /-- the process decided `v` -/
  | dec (v : V)
  deriving DecidableEq

/-- The actions of an algorithm solving k-set agreement on top of a broadcast abstraction. -/
inductive AAct (M V : Type) where
  /-- invoke `B.broadcast(m)` -/
  | bcast (m : M)
  /-- decide `v` -/
  | decide (v : V)
  deriving DecidableEq

/-- Message objects of the algorithm level: an identifier and a content. -/
abbrev Msg (C : Type) := ℕ × C

/-- The content-level action of a message-level action. -/
def AAct.cont {C V : Type} : AAct (Msg C) V → AAct C V
  | .bcast m => .bcast m.2
  | .decide v => .decide v

/-- A deterministic algorithm: the next action (`none`: wait) of process `p` with proposal `v`
after the local history `h` (oldest event first). The algorithm chooses the content `c` of the
messages it broadcasts; the message object is `(i, c)` for an identifier `i` it does not choose. -/
structure Algo (P C V : Type) where
  /-- The next action. -/
  act : P → V → List (LEv P (Msg C) V) → Option (AAct C V)

/-- A well-formed algorithm (Definition 1) never invokes `broadcast` while one of its own
invocations is pending. -/
def Algo.WellFormed {P C V : Type} (A : Algo P C V) : Prop :=
  ∀ p v h c, A.act p v h = some (.bcast c) → ∀ m, LEv.bc m ∈ h → LEv.ret m ∈ h

/-- Steps of an execution of `CAMP_n[B]`: an event of the abstraction, a decision, or an idle
step of the algorithm at `p`. -/
inductive Step (P M V : Type) where
  | b (e : BEv P M)
  | dec (p : P) (v : V)
  | tick (p : P)

namespace Step

variable {P M V : Type} [DecidableEq P]

/-- The local event of `p` produced by a step, if any. -/
def loc (p : P) : Step P M V → Option (LEv P M V)
  | b (.bc q m) => if q = p then some (.bc m) else none
  | b (.ret q m) => if q = p then some (.ret m) else none
  | b (.dl q r m) => if q = p then some (.dl r m) else none
  | dec q v => if q = p then some (.dec v) else none
  | tick _ => none

/-- If the step is a step of the algorithm at `p`, the action it performs (`none`: idle). -/
def aStep (p : P) : Step P M V → Option (Option (AAct M V))
  | b (.bc q m) => if q = p then some (some (.bcast m)) else none
  | dec q v => if q = p then some (some (.decide v)) else none
  | tick q => if q = p then some none else none
  | _ => none

/-- The broadcast event of a step, if any. -/
def toB : Step P M V → Option (BEv P M)
  | b e => some e
  | _ => none

end Step

/-- An execution of an algorithm in `CAMP_n[B]`. -/
structure AExec (P M V : Type) where
  /-- The step at time `t`, if any. -/
  st : ℕ → Option (Step P M V)
  /-- The correct processes. -/
  correct : Set P
  /-- The proposals. -/
  inp : P → V

namespace AExec

variable {P M V : Type} [DecidableEq P] (E : AExec P M V)

/-- The local history of `p` before time `t`. -/
def hist (p : P) : ℕ → List (LEv P M V)
  | 0 => []
  | t + 1 => hist p t ++ ((E.st t).bind (Step.loc p)).toList

/-- The projection of an execution onto the events of the broadcast abstraction. -/
def proj : BExec P M where
  ev t := (E.st t).bind Step.toB
  correct := E.correct

/-- `q` takes at least one step of the algorithm. -/
def Participates (q : P) : Prop :=
  ∃ t s o, E.st t = some s ∧ s.aStep q = some o

/-- `v` is decided by some process. -/
def Decided (v : V) : Prop :=
  ∃ t p, E.st t = some (.dec p v)

/-- The properties of k-set agreement (Section 4.1). -/
structure KSA (k : ℕ) : Prop where
  /-- **k-SA-Validity.** A decided value was proposed by a participating process. -/
  validity : ∀ (t : ℕ) (p : P) (v : V), E.st t = some (.dec p v) →
    ∃ q, E.inp q = v ∧ E.Participates q
  /-- **k-SA-Agreement.** No `k + 1` distinct values are decided. -/
  agreement : ∀ f : Fin (k + 1) → V, Function.Injective f → ¬ ∀ i, E.Decided (f i)
  /-- **k-SA-Termination.** Every correct process decides. -/
  termination : ∀ p ∈ E.correct, ∃ t v, E.st t = some (.dec p v)

end AExec

/-- An admissible execution of the algorithm `A` in `CAMP_n[B]`, where `B` admits the
B-executions of `S`. -/
structure Admissible {P C V : Type} [DecidableEq P] (A : Algo P C V)
    (S : Set (BExec P (Msg C))) (E : AExec P (Msg C) V) : Prop where
  /-- The broadcast events form an execution admitted by the abstraction. -/
  spec : E.proj ∈ S
  /-- The steps of the algorithm follow the algorithm. -/
  consistent : ∀ (t : ℕ) (p : P) (s : Step P (Msg C) V) (o : Option (AAct (Msg C) V)),
    E.st t = some s → s.aStep p = some o → A.act p (E.inp p) (E.hist p t) = o.map AAct.cont
  /-- Every correct process takes infinitely many steps of the algorithm. -/
  fair : ∀ p ∈ E.correct, ∀ t, ∃ t' ≥ t, ∃ (s : Step P (Msg C) V)
    (o : Option (AAct (Msg C) V)), E.st t' = some s ∧ s.aStep p = some o
  /-- A faulty process crashes: from some time on it takes no step (neither a step of the
  algorithm nor a local event of the abstraction). -/
  crash : ∀ p ∉ E.correct, ∃ T, ∀ t ≥ T, ∀ s : Step P (Msg C) V, E.st t = some s →
    s.aStep p = none ∧ s.loc p = none

/-- `A` solves k-set agreement in `CAMP_n[B]`. -/
def SolvesKSA {P C V : Type} [DecidableEq P] (k : ℕ) (A : Algo P C V)
    (S : Set (BExec P (Msg C))) : Prop :=
  ∀ E : AExec P (Msg C) V, Admissible A S E → E.KSA k

/-! ## Basic lemmas -/

namespace BExec

variable {P M : Type} {E : BExec P M}

lemma restrict_ev_eq_some {X : Set (P × M)} {t : ℕ} {e : BEv P M} :
    (E.restrict X).ev t = some e ↔ E.ev t = some e ∧ e.msg ∈ X := by
  classical
  simp only [restrict]
  cases h : E.ev t with
  | none => simp
  | some e' =>
    simp only [Option.bind_some]
    split_ifs with hx
    · constructor
      · rintro ⟨⟩; exact ⟨rfl, hx⟩
      · rintro ⟨⟨⟩, -⟩; rfl
    · constructor
      · intro h'; cases h'
      · rintro ⟨⟨⟩, h'⟩; exact absurd h' hx

lemma rename_ev_eq_some {r : P → M → M} {t : ℕ} {e : BEv P M} :
    (E.rename r).ev t = some e ↔ ∃ e', E.ev t = some e' ∧ e'.rename r = e := by
  simp [rename, Option.map_eq_some_iff]

lemma rename_ev_of {r : P → M → M} {t : ℕ} {e : BEv P M} (h : E.ev t = some e) :
    (E.rename r).ev t = some (e.rename r) :=
  rename_ev_eq_some.2 ⟨e, h, rfl⟩

lemma rename_ev_bc {r : P → M → M} (hr : ∀ p, Function.Injective (r p)) {t : ℕ} {p : P}
    {m : M} : (E.rename r).ev t = some (.bc p (r p m)) ↔ E.ev t = some (.bc p m) := by
  rw [rename_ev_eq_some]
  constructor
  · rintro ⟨e', h, he'⟩
    cases e' <;> simp only [BEv.rename, BEv.bc.injEq, reduceCtorEq] at he'
    obtain ⟨rfl, h2⟩ := he'
    rw [hr _ h2] at h; exact h
  · intro h; exact ⟨_, h, rfl⟩

lemma rename_ev_ret {r : P → M → M} (hr : ∀ p, Function.Injective (r p)) {t : ℕ} {p : P}
    {m : M} : (E.rename r).ev t = some (.ret p (r p m)) ↔ E.ev t = some (.ret p m) := by
  rw [rename_ev_eq_some]
  constructor
  · rintro ⟨e', h, he'⟩
    cases e' <;> simp only [BEv.rename, BEv.ret.injEq, reduceCtorEq] at he'
    obtain ⟨rfl, h2⟩ := he'
    rw [hr _ h2] at h; exact h
  · intro h; exact ⟨_, h, rfl⟩

lemma rename_ev_dl {r : P → M → M} (hr : ∀ p, Function.Injective (r p)) {t : ℕ} {p q : P}
    {m : M} : (E.rename r).ev t = some (.dl p q (r q m)) ↔ E.ev t = some (.dl p q m) := by
  rw [rename_ev_eq_some]
  constructor
  · rintro ⟨e', h, he'⟩
    cases e' <;> simp only [BEv.rename, BEv.dl.injEq, reduceCtorEq] at he'
    obtain ⟨rfl, rfl, h2⟩ := he'
    rw [hr _ h2] at h; exact h
  · intro h; exact ⟨_, h, rfl⟩

/-- Every `bc` event of a renamed execution comes from a `bc` event. -/
lemma rename_ev_bc' {r : P → M → M} {t : ℕ} {p : P} {m : M}
    (hh : (E.rename r).ev t = some (.bc p m)) : ∃ m', r p m' = m ∧ E.ev t = some (.bc p m') := by
  obtain ⟨e', h, he'⟩ := rename_ev_eq_some.1 hh
  cases e' <;> simp only [BEv.rename, BEv.bc.injEq, reduceCtorEq] at he'
  obtain ⟨rfl, h2⟩ := he'
  exact ⟨_, h2, h⟩

lemma rename_ev_ret' {r : P → M → M} {t : ℕ} {p : P} {m : M}
    (hh : (E.rename r).ev t = some (.ret p m)) : ∃ m', r p m' = m ∧ E.ev t = some (.ret p m') := by
  obtain ⟨e', h, he'⟩ := rename_ev_eq_some.1 hh
  cases e' <;> simp only [BEv.rename, BEv.ret.injEq, reduceCtorEq] at he'
  obtain ⟨rfl, h2⟩ := he'
  exact ⟨_, h2, h⟩

lemma rename_ev_dl' {r : P → M → M} {t : ℕ} {p q : P} {m : M}
    (hh : (E.rename r).ev t = some (.dl p q m)) :
    ∃ m', r q m' = m ∧ E.ev t = some (.dl p q m') := by
  obtain ⟨e', h, he'⟩ := rename_ev_eq_some.1 hh
  cases e' <;> simp only [BEv.rename, BEv.dl.injEq, reduceCtorEq] at he'
  obtain ⟨rfl, rfl, h2⟩ := he'
  exact ⟨_, h2, h⟩

/-- The basic properties survive restriction. -/
lemma IsBroadcast.restrict (h : E.IsBroadcast) (X : Set (P × M)) : (E.restrict X).IsBroadcast := by
  refine ⟨?_, ?_, ?_, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · intro t p q m h0
    obtain ⟨h1, h2⟩ := (restrict_ev_eq_some).1 h0
    obtain ⟨t', ht', h3⟩ := h.validity t p q m h1
    exact ⟨t', ht', (restrict_ev_eq_some).2 ⟨h3, h2⟩⟩
  · intro t t' p q m h1 h2
    exact h.noDup t t' p q m ((restrict_ev_eq_some).1 h1).1 ((restrict_ev_eq_some).1 h2).1
  · intro t t' p m h1 h2
    exact h.uniqueBc t t' p m ((restrict_ev_eq_some).1 h1).1 ((restrict_ev_eq_some).1 h2).1
  · intro t p m h1
    obtain ⟨h1, h2⟩ := (restrict_ev_eq_some).1 h1
    obtain ⟨t', ht', h3⟩ := h.wf.ret_bc t p m h1
    exact ⟨t', ht', (restrict_ev_eq_some).2 ⟨h3, h2⟩⟩
  · intro t t' p m h1 h2
    exact h.wf.ret_unique t t' p m ((restrict_ev_eq_some).1 h1).1 ((restrict_ev_eq_some).1 h2).1
  · intro t t' p m m' htt h1 h2
    obtain ⟨h2, hx⟩ := (restrict_ev_eq_some).1 h2
    obtain ⟨s, hs1, hs2, hs⟩ := h.wf.seq t t' p m m' htt ((restrict_ev_eq_some).1 h1).1 h2
    exact ⟨s, hs1, hs2, (restrict_ev_eq_some).2 ⟨hs, hx⟩⟩
  · intro t p m hp h1
    obtain ⟨h1, hx⟩ := (restrict_ev_eq_some).1 h1
    obtain ⟨t', ht', h3⟩ := h.localTerm t p m hp h1
    exact ⟨t', ht', (restrict_ev_eq_some).2 ⟨h3, hx⟩⟩
  · intro t q m hq h1 p hp
    obtain ⟨h1, hx⟩ := (restrict_ev_eq_some).1 h1
    obtain ⟨t', h3⟩ := h.globalCS t q m hq h1 p hp
    exact ⟨t', (restrict_ev_eq_some).2 ⟨h3, hx⟩⟩

/-- The basic properties survive injective renaming. -/
lemma IsBroadcast.rename (h : E.IsBroadcast) {r : P → M → M}
    (hr : ∀ p, Function.Injective (r p)) : (E.rename r).IsBroadcast := by
  refine ⟨?_, ?_, ?_, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · intro t p q m h10
    obtain ⟨m', rfl, h1⟩ := rename_ev_dl' h10
    obtain ⟨t', ht', h3⟩ := h.validity t p q m' h1
    exact ⟨t', ht', (rename_ev_bc hr).2 h3⟩
  · intro t t' p q m h10 h20
    obtain ⟨m', rfl, h1⟩ := rename_ev_dl' h10
    exact h.noDup t t' p q m' h1 ((rename_ev_dl hr).1 h20)
  · intro t t' p m h10 h20
    obtain ⟨m', rfl, h1⟩ := rename_ev_bc' h10
    exact h.uniqueBc t t' p m' h1 ((rename_ev_bc hr).1 h20)
  · intro t p m h10
    obtain ⟨m', rfl, h1⟩ := rename_ev_ret' h10
    obtain ⟨t', ht', h3⟩ := h.wf.ret_bc t p m' h1
    exact ⟨t', ht', (rename_ev_bc hr).2 h3⟩
  · intro t t' p m h10 h20
    obtain ⟨m', rfl, h1⟩ := rename_ev_ret' h10
    exact h.wf.ret_unique t t' p m' h1 ((rename_ev_ret hr).1 h20)
  · intro t t' p m m' htt h10 h20
    obtain ⟨m1, rfl, h1⟩ := rename_ev_bc' h10
    obtain ⟨m2, rfl, h2⟩ := rename_ev_bc' h20
    obtain ⟨s, hs1, hs2, hs⟩ := h.wf.seq t t' p m1 m2 htt h1 h2
    exact ⟨s, hs1, hs2, (rename_ev_ret hr).2 hs⟩
  · intro t p m hp h10
    obtain ⟨m', rfl, h1⟩ := rename_ev_bc' h10
    obtain ⟨t', ht', h3⟩ := h.localTerm t p m' hp h1
    exact ⟨t', ht', (rename_ev_ret hr).2 h3⟩
  · intro t q m hq h10 p hp
    obtain ⟨m', rfl, h1⟩ := rename_ev_bc' h10
    obtain ⟨t', h3⟩ := h.globalCS t q m' hq h1 p hp
    exact ⟨t', (rename_ev_dl hr).2 h3⟩

end BExec

namespace AExec

variable {P M V : Type} [DecidableEq P] {E : AExec P M V}

lemma mem_hist {p : P} {t : ℕ} {e : LEv P M V} :
    e ∈ E.hist p t ↔ ∃ s < t, (E.st s).bind (Step.loc p) = some e := by
  induction t with
  | zero => simp [hist]
  | succ t ih =>
    simp only [hist, List.mem_append, ih, Option.mem_toList]
    constructor
    · rintro (⟨s, hs, h⟩ | h)
      · exact ⟨s, by omega, h⟩
      · exact ⟨t, by omega, h⟩
    · rintro ⟨s, hs, h⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hs with hs | rfl
      · exact Or.inl ⟨s, hs, h⟩
      · exact Or.inr h

/-- The first entry of the history selected by `g` comes from the earliest such step. -/
lemma findSome?_hist {β : Type} {g : LEv P M V → Option β} {p : P} {t : ℕ} {w : β}
    (h : (E.hist p t).findSome? g = some w) :
    ∃ s < t, ∃ e, (E.st s).bind (Step.loc p) = some e ∧ g e = some w ∧
      ∀ s' < s, ∀ e', (E.st s').bind (Step.loc p) = some e' → g e' = none := by
  induction t with
  | zero => simp [hist] at h
  | succ t ih =>
    simp only [hist, List.findSome?_append] at h
    cases h1 : (E.hist p t).findSome? g with
    | some w' =>
      rw [h1] at h; simp at h; subst h
      obtain ⟨s, hs, rest⟩ := ih h1
      exact ⟨s, by omega, rest⟩
    | none =>
      rw [h1] at h; simp only [Option.none_or] at h
      cases h2 : (E.st t).bind (Step.loc p) with
      | none => rw [h2] at h; simp at h
      | some e =>
        rw [h2] at h
        simp only [Option.toList_some, List.findSome?_cons, List.findSome?_nil] at h
        refine ⟨t, by omega, e, h2, ?_, ?_⟩
        · cases hg : g e <;> rw [hg] at h <;> simp_all
        · intro s' hs' e' he'
          have hmem : e' ∈ E.hist p t := mem_hist.2 ⟨s', hs', he'⟩
          exact List.findSome?_eq_none_iff.1 h1 e' hmem

lemma loc_eq_some {p : P} {s : Step P M V} {e : LEv P M V} (h : s.loc p = some e) :
    (∃ m, e = .bc m ∧ s = .b (.bc p m)) ∨ (∃ m, e = .ret m ∧ s = .b (.ret p m)) ∨
    (∃ q m, e = .dl q m ∧ s = .b (.dl p q m)) ∨ (∃ v, e = .dec v ∧ s = .dec p v) := by
  rcases s with (⟨q, m⟩ | ⟨q, m⟩ | ⟨q, r, m⟩) | ⟨q, v⟩ | q <;>
    simp only [Step.loc] at h <;> (try split_ifs at h with hq) <;> (try cases h) <;>
    (try subst hq) <;> simp

lemma aStep_eq_some {p : P} {s : Step P M V} {o : Option (AAct M V)} (h : s.aStep p = some o) :
    (∃ m, o = some (.bcast m) ∧ s = .b (.bc p m)) ∨ (∃ v, o = some (.decide v) ∧ s = .dec p v) ∨
    (o = none ∧ s = .tick p) := by
  rcases s with (⟨q, m⟩ | ⟨q, m⟩ | ⟨q, r, m⟩) | ⟨q, v⟩ | q <;>
    simp only [Step.aStep, reduceCtorEq] at h <;> (try split_ifs at h with hq) <;>
    (try cases h) <;> (try subst hq) <;> simp

lemma proj_ev_eq_some {t : ℕ} {e : BEv P M} : E.proj.ev t = some e ↔ E.st t = some (.b e) := by
  simp only [proj, Option.bind_eq_some_iff]
  constructor
  · rintro ⟨s, hs, he⟩
    cases s <;> simp [Step.toB] at he
    subst he; exact hs
  · intro h; exact ⟨_, h, rfl⟩

end AExec

end Podc.NoBroadcastKSA
