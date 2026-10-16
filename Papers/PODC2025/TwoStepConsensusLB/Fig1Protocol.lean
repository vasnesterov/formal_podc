import Mathlib

/-!
# The upper-bound protocol of Ryabinin–Gotsman–Sutra (PODC 2025), Fig. 1, as a transition system

This file models the consensus protocol of Fig. 1 of *Revisiting Lower Bounds for Two-Step
Consensus* (arXiv 2505.03627v2), in both versions:

* `Version.task`: the black lines only; `initial_val` is the process's input, fixed forever;
* `Version.object`: with the red lines; `initial_val` is `⊥` until `propose(v)` is invoked.

## Model: an abstract asynchronous transition system

There is no time. A global state consists of the local states of all processes and the **set of all
messages ever sent** (`State.msgs`). Every action is one handler of Fig. 1 executed atomically by
one process; it is enabled when its triggering messages are in the set and its precondition
(`pre:` in Fig. 1) holds. This over-approximates every execution of the real protocol (messages
may be reordered, duplicated, delayed forever; a crashed process simply stops acting), so the
safety results proved about it (`Fig1Safety.lean`) hold for every real execution, under any
leader-election scheme and any timing.

Values are a linear order `V`; `⊥` is `none : Option V`. `n = Fintype.card P` (the paper's `|Π|`).

## Interpretation choices (Fig. 1 is pseudocode; these are our readings)

* Ballots: every ballot `b ≥ 1` has a unique owner `cfg.owner b` (the paper: `b ≡ i (mod n)`; any
  function `ℕ → P` is allowed here). Only the owner of `b` sends `1A(b)` (lines 21–23); **every**
  process may start any of its own ballots at any time (no leader election in the safety model).
* Lines 9–10: `bal` is the receiver's **current** ballot variable. The fast path (first disjunct)
  needs `bal = 0` and counts the `2B(0, v)` messages addressed to `p_i` (replies to its own
  `Propose`); the slow path (second disjunct) counts `2B(bal, v)` messages addressed to `p_i`
  (replies to its own `2A(bal, v)`, so `p_i` is the owner of `bal`). The set `P` of senders is
  non-empty (the handler is triggered by receiving messages).
* Line 24: the owner of `b` may run the `1B` handler for any set `Q` of `n − f` processes whose
  `1B(b, …)` messages it has received, as long as it has not yet sent a `2A(b, ·)` (a handler that
  ended with `val = ⊥` sent nothing, so it may run again later). Lines 26–38 are the relation
  `Select` (non-deterministic where Fig. 1 is: which `decided_q` at line 30, which `q` with
  `vbal_q = b_max` at line 32); a run of lines 26–38 that ends with `val = ⊥` sends nothing.
* Lines 1–4 (object version): an invocation `propose(v)` (action `invoke`, at most once per
  process — well-formed clients) sets `initial_val ← v` if `val = ⊥`; the broadcast of
  `Propose(initial_val)` is the separate action `sendPropose`, enabled whenever
  `initial_val ≠ ⊥` (task version: at startup, or any time). Executing `invoke` immediately followed
  by `sendPropose` is the atomic handler of Fig. 1, so this is an over-approximation.
* Line 6, object version: the red conjunct `initial_val ≠ ⊥ ⟹ v = initial_val` (`Accepts`).
* `cfg.fallbackVal` (default `false` = the paper) selects a fixed variant of lines 37–38 in which
  a leader with `initial_val = ⊥` proposes its own `val` if `≠ ⊥` (`leaderIv`). All safety
  results hold for both variants.
* Ghost data (not read by any handler): `Decide` messages carry the ballot `bal` of the sender at
  the moment of its decision (`0` = fast path, line 10 first disjunct), and each process records the
  argument of its `propose` invocation (`Loc.inv`), used to state Validity of the object version.
-/

namespace TwoStepConsensus.Fig1

/-- The two versions of Fig. 1: consensus *task* (black lines) and *object* (with red lines). -/
inductive Version
  | task
  | object
  deriving DecidableEq

/-- Parameters: version, the thresholds `e ≤ f`, the owner of each ballot, and (task version) the
inputs. -/
structure Config (P V : Type*) where
  ver : Version
  e : ℕ
  f : ℕ
  /-- The process that owns ballot `b` (the only one that may send `1A(b)` and `2A(b, ·)`). -/
  owner : ℕ → P
  /-- Inputs (task version; ignored by the object version). -/
  input : P → V
  /-- `false` (default): Fig. 1 as in the paper. `true`: the *fixed* lines 37–38, where a leader
  with `initial_val = ⊥` falls back to its own `val` (see `leaderIv`). -/
  fallbackVal : Bool := false

/-- Local state of a process (Fig. 1 variables plus the ghost `inv`). -/
structure Loc (P V : Type*) where
  bal : ℕ
  vbal : ℕ
  val : Option V
  proposer : Option P
  decided : Option V
  initVal : Option V
  /-- Ghost: the argument of this process's `propose` invocation (object version). -/
  inv : Option V

/-- The payload of a `1B` message: `(vbal, val, proposer, decided)` of the sender (line 20). -/
structure Snap (P V : Type*) where
  vbal : ℕ
  val : Option V
  proposer : Option P
  decided : Option V

/-- The `1B` payload reported by a process in local state `l`. -/
def Loc.snap {P V : Type*} (l : Loc P V) : Snap P V := ⟨l.vbal, l.val, l.proposer, l.decided⟩

/-- Messages. Destinations are implicit where they are determined: `Propose`, `Decide`, `1A`,
`2A` are broadcasts; `1B(b, …)` goes to `owner b`. `2B` records its destination. -/
inductive Msg (P V : Type*)
  /-- `Propose(v)` from `src` (line 4). -/
  | propose (src : P) (v : V)
  /-- `2B(b, v)` from `src` to `dst` (lines 8 and 43). -/
  | twoB (src dst : P) (b : ℕ) (v : V)
  /-- `Decide(v)` from `src` (line 13); `b` is a ghost: the sender's ballot when deciding. -/
  | decide (src : P) (b : ℕ) (v : V)
  /-- `1A(b)` (line 23), sent by `owner b`. -/
  | oneA (b : ℕ)
  /-- `1B(b, vbal, val, proposer, decided)` from `src` (line 20). -/
  | oneB (src : P) (b : ℕ) (d : Snap P V)
  /-- `2A(b, v)` (line 39), sent by `owner b`. -/
  | twoA (b : ℕ) (v : V)

/-- Global state: local states and the set of all messages ever sent. -/
structure State (P V : Type*) where
  loc : P → Loc P V
  msgs : Set (Msg P V)

/-- The names of the handlers of Fig. 1 (used to restrict executions, e.g. in `Fig1Liveness`). -/
inductive Kind
  | invoke | sendPropose | recvPropose | fastDecide | slowDecide | recvDecide
  | recv1A | start1A | send2A | recv2A
  deriving DecidableEq

variable {P V : Type*}

namespace State

/-- Replace the local state of `p`. -/
def set [DecidableEq P] (s : State P V) (p : P) (l : Loc P V) : State P V :=
  ⟨Function.update s.loc p l, s.msgs⟩

/-- Send (add) a message. -/
def send (s : State P V) (m : Msg P V) : State P V := ⟨s.loc, insert m s.msgs⟩

@[simp] theorem set_loc [DecidableEq P] (s : State P V) (p : P) (l : Loc P V) (q : P) :
    (s.set p l).loc q = if q = p then l else s.loc q := by
  simp [set, Function.update_apply]

@[simp] theorem set_msgs [DecidableEq P] (s : State P V) (p : P) (l : Loc P V) :
    (s.set p l).msgs = s.msgs := rfl

@[simp] theorem send_loc (s : State P V) (m : Msg P V) : (s.send m).loc = s.loc := rfl

@[simp] theorem mem_send_msgs (s : State P V) (m m' : Msg P V) :
    m' ∈ (s.send m).msgs ↔ m' = m ∨ m' ∈ s.msgs := Iff.rfl

end State

variable [Fintype P] [DecidableEq P] [LinearOrder V]

/-- Line 6, the condition on `initial_val`: `v ≥ initial_val`, and (object version, red)
`initial_val ≠ ⊥ ⟹ v = initial_val`. -/
def Accepts (ver : Version) (iv : Option V) (v : V) : Prop :=
  (∀ a, iv = some a → a ≤ v) ∧ (ver = .object → ∀ a, iv = some a → a = v)

/-- Line 28: `q ∈ R` iff `proposer_q ∉ Q` (`⊥ ∉ Q`). -/
def InR (Q : Finset P) (d : Snap P V) : Prop := ∀ p, d.proposer = some p → p ∉ Q

/-- `S ⊆ R` and every `q ∈ S` reported `v_q = w` (lines 33 and 35). -/
def VotersIn (Q : Finset P) (rep : P → Snap P V) (w : V) (S : Finset P) : Prop :=
  S ⊆ Q ∧ ∀ q ∈ S, InR Q (rep q) ∧ (rep q).val = some w

/-- The condition of line 33 for the value `w`. -/
def Cond33 (cfg : Config P V) (Q : Finset P) (rep : P → Snap P V) (w : V) : Prop :=
  ∃ S, VotersIn Q rep w S ∧ Fintype.card P - cfg.f - cfg.e < S.card

/-- The condition of line 35 for the value `w`. -/
def Cond35 (cfg : Config P V) (Q : Finset P) (rep : P → Snap P V) (w : V) : Prop :=
  ∃ S, VotersIn Q rep w S ∧ S.card = Fintype.card P - cfg.f - cfg.e

/-- Lines 26–38: `Select cfg Q rep iv w` holds iff the leader, having received the `1B` payloads
`rep q` from all `q ∈ Q` and having `initial_val = iv`, may end with `val = w ≠ ⊥`. -/
inductive Select (cfg : Config P V) (Q : Finset P) (rep : P → Snap P V) (iv : Option V) : V → Prop
  /-- Lines 29–30. -/
  | l30 {q : P} {w : V} : q ∈ Q → (rep q).decided = some w → Select cfg Q rep iv w
  /-- Lines 31–32: `b_max > 0`; `q` attains `b_max`. -/
  | l32 {q : P} {w : V} : (∀ q' ∈ Q, (rep q').decided = none) → q ∈ Q →
      (∀ q' ∈ Q, (rep q').vbal ≤ (rep q).vbal) → 0 < (rep q).vbal → (rep q).val = some w →
      Select cfg Q rep iv w
  /-- Lines 33–34 (`b_max = 0`). -/
  | l34 {w : V} : (∀ q' ∈ Q, (rep q').decided = none) → (∀ q' ∈ Q, (rep q').vbal = 0) →
      Cond33 cfg Q rep w → Select cfg Q rep iv w
  /-- Lines 35–36: `w` is the maximal value satisfying the condition at line 35. -/
  | l36 {w : V} : (∀ q' ∈ Q, (rep q').decided = none) → (∀ q' ∈ Q, (rep q').vbal = 0) →
      (∀ w', ¬ Cond33 cfg Q rep w') → Cond35 cfg Q rep w → (∀ w', Cond35 cfg Q rep w' → w' ≤ w) →
      Select cfg Q rep iv w
  /-- Lines 37–38. -/
  | l38 {w : V} : (∀ q' ∈ Q, (rep q').decided = none) → (∀ q' ∈ Q, (rep q').vbal = 0) →
      (∀ w', ¬ Cond33 cfg Q rep w') → (∀ w', ¬ Cond35 cfg Q rep w') → iv = some w →
      Select cfg Q rep iv w

/-- The value used by a leader with local state `l` at lines 37–38. Paper (`fallbackVal = false`):
`initial_val`. Fixed protocol (`fallbackVal = true`): "else if `initial_val ≠ ⊥` then `initial_val`,
else if `val ≠ ⊥` then `val`". In the task version `initial_val ≠ ⊥`, so both coincide. -/
def leaderIv (cfg : Config P V) (l : Loc P V) : Option V :=
  if cfg.fallbackVal then l.initVal.orElse fun _ => l.val else l.initVal

/-- The initial state. -/
def init (cfg : Config P V) : State P V where
  loc p := { bal := 0, vbal := 0, val := none, proposer := none, decided := none,
             initVal := if cfg.ver = .task then some (cfg.input p) else none, inv := none }
  msgs := ∅

/-- One atomic step of process `p` executing the handler `k` of Fig. 1. -/
inductive Step (cfg : Config P V) : P → Kind → State P V → State P V → Prop
  /-- Lines 1–3 (object version): invocation of `propose(v)`, at most once per process. -/
  | invoke {s : State P V} {p : P} (v : V) :
      cfg.ver = .object → (s.loc p).inv = none →
      Step cfg p .invoke s (s.set p { s.loc p with
        inv := some v,
        initVal := if (s.loc p).val = none then some v else (s.loc p).initVal })
  /-- Line 4: send `Propose(initial_val)`. -/
  | sendPropose {s : State P V} {p : P} {v : V} :
      (s.loc p).initVal = some v → Step cfg p .sendPropose s (s.send (.propose p v))
  /-- Lines 5–8. -/
  | recvPropose {s : State P V} {p q : P} {v : V} :
      .propose q v ∈ s.msgs → q ≠ p → (s.loc p).bal = 0 → (s.loc p).val = none →
      Accepts cfg.ver (s.loc p).initVal v →
      Step cfg p .recvPropose s
        ((s.set p { s.loc p with val := some v, proposer := some q }).send (.twoB p q 0 v))
  /-- Lines 9–13, first disjunct of line 10 (fast path). -/
  | fastDecide {s : State P V} {p : P} {v : V} (P' : Finset P) :
      P'.Nonempty → (∀ q ∈ P', .twoB q p 0 v ∈ s.msgs) →
      Fintype.card P - cfg.e ≤ (insert p P').card → (s.loc p).bal = 0 →
      ((s.loc p).val = none ∨ (s.loc p).val = some v) →
      Step cfg p .fastDecide s
        ((s.set p { s.loc p with val := some v, decided := some v }).send (.decide p 0 v))
  /-- Lines 9–13, second disjunct of line 10 (slow path). -/
  | slowDecide {s : State P V} {p : P} {v : V} (P' : Finset P) :
      P'.Nonempty → (∀ q ∈ P', .twoB q p (s.loc p).bal v ∈ s.msgs) →
      Fintype.card P - cfg.f ≤ P'.card → (s.loc p).bal ≠ 0 →
      Step cfg p .slowDecide s
        ((s.set p { s.loc p with val := some v, decided := some v }).send
          (.decide p (s.loc p).bal v))
  /-- Lines 14–16. -/
  | recvDecide {s : State P V} {p q : P} {b : ℕ} {v : V} :
      .decide q b v ∈ s.msgs →
      Step cfg p .recvDecide s (s.set p { s.loc p with val := some v, decided := some v })
  /-- Lines 17–20. -/
  | recv1A {s : State P V} {p : P} {b : ℕ} :
      .oneA b ∈ s.msgs → (s.loc p).bal < b →
      Step cfg p .recv1A s ((s.set p { s.loc p with bal := b }).send (.oneB p b (s.loc p).snap))
  /-- Lines 21–23 (any process may start any of its own ballots `b > bal`). -/
  | start1A {s : State P V} {p : P} {b : ℕ} :
      cfg.owner b = p → (s.loc p).bal < b → Step cfg p .start1A s (s.send (.oneA b))
  /-- Lines 24–39 (sending `2A(b, v)` when lines 26–38 end with `val = v ≠ ⊥`). -/
  | send2A {s : State P V} {p : P} {b : ℕ} {v : V} (Q : Finset P) (rep : P → Snap P V) :
      cfg.owner b = p → (∀ w, .twoA b w ∉ s.msgs) → Q.card = Fintype.card P - cfg.f →
      (∀ q ∈ Q, .oneB q b (rep q) ∈ s.msgs) → Select cfg Q rep (leaderIv cfg (s.loc p)) v →
      Step cfg p .send2A s (s.send (.twoA b v))
  /-- Lines 40–43. -/
  | recv2A {s : State P V} {p : P} {b : ℕ} {v : V} :
      .twoA b v ∈ s.msgs → (s.loc p).bal ≤ b →
      Step cfg p .recv2A s
        ((s.set p { s.loc p with val := some v, bal := b, vbal := b }).send
          (.twoB p (cfg.owner b) b v))

/-- Some process takes some step. -/
def Next (cfg : Config P V) (s s' : State P V) : Prop := ∃ p k, Step cfg p k s s'

/-- Reachable states. -/
def Reachable (cfg : Config P V) (s : State P V) : Prop :=
  Relation.ReflTransGen (Next cfg) (init cfg) s

end TwoStepConsensus.Fig1
