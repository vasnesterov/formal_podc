import Mathlib

/-!
# VABA (Abraham, Malkhi, Spiegelman, PODC 2019): the protocol as a transition system

We model Algorithms 1–7 of *Asymptotically Optimal Validated Asynchronous Byzantine Agreement*
(arXiv:1811.01332v1) as an interleaving transition system.

## Model

* `n = |P|` parties; the adversary corrupts parties **adaptively** (action `corrupt`), at most `f`
  of them in total. A corrupted party stops following the protocol and its local state is frozen.
* **Asynchrony.** Every honest step is an action the adversary may schedule in any order whenever
  its guard holds; there is no notion of time.
* **Ideal threshold signatures.** `tok p st` means that party `p` has produced a signature share on
  the statement `st`. A threshold signature (certificate, "QC") on `st` exists iff at least `Q`
  parties produced shares (`QC`); the paper uses `Q = 2f + 1` with `n = 3f + 1`, and we keep `Q`
  as a parameter. Corrupted parties may sign anything (`byzSign`), honest ones only what the
  protocol prescribes. Certificates cannot be forged, but anybody may forward an existing one.
* **Ideal common coin.** The leader of view `j` is `c j` for a coin sequence `c : ℕ → P`. It is
  *revealed* (`rev j`) when the first honest party invokes `elect` for view `j` (with the `f`
  shares of the corrupted parties, one honest share suffices to compute the coin); an honest party
  learns it (`lead`) when its `elect` returns, which needs the coin to be revealed.
* **f+1-Provable-Broadcast.** An honest party may deliver, in its current view and before
  abandoning it, a message of proposer `k` at stage `s ∈ {1,2,3,4}` if it passes the external
  validation (`ex-sbc-validation` / `ex-bc-validation`), the party has not delivered in that
  instance yet, and the message may have been sent (`SentBy`): a corrupted proposer may send
  anything, an honest one only its proposal of that view (stage `s ≥ 2` needs a stage-`(s-1)`
  certificate on it anyway). Delivering = sending the signature share. We do not model the
  proposer's collection of shares; the `done` messages are abstracted by "a stage-4 certificate
  exists" (`completed`), which over-approximates when they can be sent.
* **Keys** `⟨r, σ⟩`: `σ` is a stage-1 certificate of the leader of view `r`; `r = 0` is the empty key
  of view 1. (Algorithm 6 line 4 says `j ≠ 1`; it must be the key view `≠ 0`, see
  `differencies.md`.) Since certificates are ideal, a key is represented by its view `r` only.
* **View change.** View-change messages of view `j` are processed once the receiver knows the
  leader of view `j` (buffered until then). A message of an honest sender carries its deliveries
  `D_key, D_lock, D_commit` in the leader's broadcast (frozen, since the sender has abandoned it).
  A corrupted sender can send any combination of existing certificates; this is `recvQC`, which
  may also be used at any time for forwarded certificates.
* Ghost fields (not used by the protocol's decisions): `kv` (the key view used when delivering a
  stage-1 message), `exitR` (the senders of the view-change messages that let a party leave a
  view), `prop` (the key proposed at the start of each view).
-/

namespace VABA

open Finset

/-- Signed statements: `pb j k s v` is the share of stage `s ∈ {1,…,4}` of the 4-stage provable
broadcast of proposer `k` in view `j` on value `v` (the statement `⟨⟨⟨id,k,j⟩,s⟩,v⟩`); `skip j`
is the share on `⟨id, skip, j⟩`. -/
inductive Stmt (P V : Type*)
  | pb (j : ℕ) (k : P) (s : ℕ) (v : V)
  | skip (j : ℕ)

/-- Phases of a view: broadcast phase, waiting for the leader election, view-change phase. -/
inductive Phase
  | bc
  | electing
  | vc
  deriving DecidableEq

/-- Local state of a party. -/
structure Loc (P V : Type*) where
  /-- current view `j` -/
  view : ℕ
  /-- phase in the current view -/
  ph : Phase
  /-- `L[i]`: the leader of view `i`, once `elect` returned -/
  lead : ℕ → Option P
  /-- `d i k s`: the value delivered at stage `s` of proposer `k`'s broadcast of view `i`
  (`D_key, D_lock, D_commit` are stages 2, 3, 4) -/
  d : ℕ → P → ℕ → Option V
  /-- ghost: the key view of the stage-1 message delivered in `(i, k)` -/
  kv : ℕ → P → ℕ
  /-- `LOCK` -/
  lock : ℕ
  /-- `KEY` (view, value); the proof is the stage-1 certificate of that view's leader -/
  key : ℕ × V
  /-- decided values -/
  decs : Set V
  /-- senders of the view-change messages of view `i` received so far -/
  rcvd : ℕ → Finset P
  /-- ghost: `rcvd i` at the moment the party left view `i` -/
  exitR : ℕ → Finset P
  /-- ghost: the (key view, value) broadcast at the start of view `i` -/
  prop : ℕ → ℕ × V

/-- Global state. -/
structure Glob (P V : Type*) where
  /-- corrupted parties (adaptive adversary) -/
  corrupt : Finset P
  /-- signature shares produced so far -/
  tok : P → Stmt P V → Prop
  /-- revealed coins: `rev j = some (c j)` once the coin of view `j` is revealed -/
  rev : ℕ → Option P
  /-- local states -/
  loc : P → Loc P V

/-- Parameters of the protocol. -/
structure Cfg (P V : Type*) where
  /-- maximal number of corrupted parties -/
  f : ℕ
  /-- certificate / quorum size (the paper's `2f + 1`) -/
  Q : ℕ
  /-- the external validity predicate `ex-ba-validation` -/
  valid : V → Prop
  /-- inputs -/
  input : P → V

variable {P V : Type*} [Fintype P] [DecidableEq P]

/-- Parties that signed `st`. -/
noncomputable def signers (s : Glob P V) (st : Stmt P V) : Finset P := by
  classical exact univ.filter (fun p => s.tok p st)

omit [DecidableEq P] in
@[simp] lemma mem_signers {s : Glob P V} {st : Stmt P V} {p : P} :
    p ∈ signers s st ↔ s.tok p st := by
  classical simp [signers]

/-- A (threshold-signature) certificate on `st` exists. -/
def QC (Q : ℕ) (s : Glob P V) (st : Stmt P V) : Prop := Q ≤ (signers s st).card

/-- Proposers whose broadcast of view `j` has a stage-4 certificate ("completed" broadcasts, i.e.
those for which a `done` message with a valid proof can be sent). -/
noncomputable def completed (Q : ℕ) (s : Glob P V) (j : ℕ) : Finset P := by
  classical exact univ.filter (fun k => ∃ v, QC Q s (.pb j k 4 v))

/-- The party has sent its view-change message of view `i` (and abandoned the broadcasts of view
`i`): it is past view `i`, or in view `i` after `elect` returned. -/
def Past (L : Loc P V) (i : ℕ) : Prop := i < L.view ∨ (i = L.view ∧ L.ph = .vc)

/-- Processing one entry of a view-change message of view `j`: a stage-`s` certificate (`s = 1`:
key, `s = 2`: lock, `s = 3`: commit) on `o` (Algorithm 7, lines 24–31). -/
def proc (j s : ℕ) (o : Option V) (L : Loc P V) : Loc P V :=
  match o with
  | none => L
  | some v =>
    if s = 1 then (if L.key.1 < j then { L with key := (j, v) } else L)
    else if s = 2 then (if L.lock < j then { L with lock := j } else L)
    else if s = 3 then { L with decs := insert v L.decs }
    else L

/-- Processing the view-change message of view `j` of a party with local state `H` (its
deliveries in the broadcast of the leader `l`). -/
def procVC (j : ℕ) (l : P) (H : Loc P V) (L : Loc P V) : Loc P V :=
  proc j 3 (H.d j l 4) (proc j 2 (H.d j l 3) (proc j 1 (H.d j l 2) L))

/-- Actions. -/
inductive Act (P V : Type*)
  /-- honest `p` delivers (and signs) value `v` at stage `s` of proposer `k`'s broadcast of its
  current view; for `s = 1` the message carries a key of view `r` -/
  | deliver (p k : P) (s : ℕ) (v : V) (r : ℕ)
  /-- honest `p` sends a skip share for view `j` (after `Q` valid `done` messages) -/
  | skipShare (p : P) (j : ℕ)
  /-- honest `p` gets a skip certificate, abandons the broadcasts and invokes `elect` -/
  | invokeElect (p : P)
  /-- `elect` returns at honest `p`; `p` sends its view-change message -/
  | electReturn (p : P)
  /-- honest `p` receives the view-change message of view `j` from `q`; `b = true`: the message
  `q` sent while honest, `b = false`: a message of the corrupted `q` (its certificates are
  processed by `recvQC`) -/
  | recvVC (p q : P) (j : ℕ) (b : Bool)
  /-- honest `p` processes an existing stage-`s` certificate of the leader of view `j` contained
  in some view-change message (`s ∈ {1,2,3}`) -/
  | recvQC (p : P) (j s : ℕ) (v : V)
  /-- honest `p` has `Q` view-change messages and moves to the next view -/
  | exitView (p : P)
  /-- the adversary corrupts `p` -/
  | corrupt (p : P)
  /-- the corrupted `p` signs `st` -/
  | byzSign (p : P) (st : Stmt P V)

/-- The initial state. -/
def init (C : Cfg P V) : Glob P V where
  corrupt := ∅
  tok := fun _ _ => False
  rev := fun _ => none
  loc := fun p =>
    { view := 1, ph := .bc, lead := fun _ => none, d := fun _ _ _ => none, kv := fun _ _ => 0,
      lock := 0, key := (0, C.input p), decs := ∅, rcvd := fun _ => ∅, exitR := fun _ => ∅,
      prop := fun _ => (0, C.input p) }

/-- Replace the local state of `p`. -/
def Glob.upd (s : Glob P V) (p : P) (L : Loc P V) : Glob P V :=
  { s with loc := Function.update s.loc p L }

/-- Add the share of `p` on `st`. -/
def Glob.sign (s : Glob P V) (p : P) (st : Stmt P V) : Glob P V :=
  { s with tok := fun q x => s.tok q x ∨ (q = p ∧ x = st) }

/-- Validation of a stage-`s` message `(v, key view r)` of proposer `k` by a party with state `L`
in global state `s` (`ex-sbc-validation` and, for `s = 1`, `ex-bc-validation`). -/
def Valid (C : Cfg P V) (s : Glob P V) (L : Loc P V) (k : P) (st : ℕ) (v : V) (r : ℕ) : Prop :=
  if st = 1 then
    C.valid v ∧ L.lock ≤ r ∧ (r = 0 ∨ ∃ l, L.lead r = some l ∧ QC C.Q s (.pb r l 1 v))
  else QC C.Q s (.pb L.view k (st - 1) v)

/-- The stage-`st` message `(v, key view r)` of the broadcast of proposer `k` in view `j` may
have been sent: `k` is corrupted, or `k` is honest, has started view `j` and proposes there its
`KEY` from the end of view `j - 1` (`v_j, σ_j` of Algorithm 6). -/
def SentBy (s : Glob P V) (k : P) (j st : ℕ) (v : V) (r : ℕ) : Prop :=
  k ∈ s.corrupt ∨ (j ≤ (s.loc k).view ∧ v = ((s.loc k).prop j).2 ∧
    (st = 1 → r = ((s.loc k).prop j).1))

/-- Guards of the actions. -/
def Enabled (C : Cfg P V) : Act P V → Glob P V → Prop
  | .deliver p k st v r, s =>
    p ∉ s.corrupt ∧ (s.loc p).ph = .bc ∧ 1 ≤ st ∧ st ≤ 4 ∧
      (s.loc p).d (s.loc p).view k st = none ∧ Valid C s (s.loc p) k st v r ∧
      SentBy s k (s.loc p).view st v r
  | .skipShare p j, s => p ∉ s.corrupt ∧ C.Q ≤ (completed C.Q s j).card
  | .invokeElect p, s => p ∉ s.corrupt ∧ (s.loc p).ph = .bc ∧ QC C.Q s (.skip (s.loc p).view)
  | .electReturn p, s => p ∉ s.corrupt ∧ (s.loc p).ph = .electing ∧
      (s.rev (s.loc p).view).isSome
  | .recvVC p q j b, s => p ∉ s.corrupt ∧ ((s.loc p).lead j).isSome ∧
      (if b then Past (s.loc q) j else q ∈ s.corrupt)
  | .recvQC p j st v, s => p ∉ s.corrupt ∧ 1 ≤ st ∧ st ≤ 3 ∧
      ∃ l, (s.loc p).lead j = some l ∧ QC C.Q s (.pb j l st v)
  | .exitView p, s => p ∉ s.corrupt ∧ (s.loc p).ph = .vc ∧
      C.Q ≤ ((s.loc p).rcvd (s.loc p).view).card
  | .corrupt p, s => p ∉ s.corrupt ∧ s.corrupt.card < C.f
  | .byzSign p _, s => p ∈ s.corrupt

/-- Effects of the actions; the coin sequence `c` is used only when a coin is revealed. -/
def eff (c : ℕ → P) : Act P V → Glob P V → Glob P V
  | .deliver p k st v r, s =>
    let L := s.loc p
    let j := L.view
    (s.sign p (.pb j k st v)).upd p
      { L with
        d := fun j' k' s' => if j' = j ∧ k' = k ∧ s' = st then some v else L.d j' k' s'
        kv := fun j' k' => if j' = j ∧ k' = k ∧ st = 1 then r else L.kv j' k' }
  | .skipShare p j, s => s.sign p (.skip j)
  | .invokeElect p, s =>
    let L := s.loc p
    let j := L.view
    { s with
      rev := fun i => if i = j ∧ s.rev j = none then some (c j) else s.rev i
      loc := Function.update s.loc p { L with ph := .electing } }
  | .electReturn p, s =>
    let L := s.loc p
    let j := L.view
    s.upd p { L with ph := .vc, lead := Function.update L.lead j (s.rev j) }
  | .recvVC p q j b, s =>
    let L := s.loc p
    let L' := { L with rcvd := Function.update L.rcvd j (insert q (L.rcvd j)) }
    match L.lead j with
    | some l => s.upd p (if b then procVC j l (s.loc q) L' else L')
    | none => s
  | .recvQC p j st v, s => s.upd p (proc j st (some v) (s.loc p))
  | .exitView p, s =>
    let L := s.loc p
    let j := L.view
    s.upd p
      { L with
        view := j + 1, ph := .bc, exitR := Function.update L.exitR j (L.rcvd j)
        prop := Function.update L.prop (j + 1) L.key }
  | .corrupt p, s => { s with corrupt := insert p s.corrupt }
  | .byzSign p st, s => s.sign p st

/-- One step: the action takes effect if enabled, otherwise nothing happens. -/
noncomputable def step (C : Cfg P V) (c : ℕ → P) (a : Act P V) (s : Glob P V) : Glob P V := by
  classical exact if Enabled C a s then eff c a s else s

/-- Reachable states (for arbitrary coin sequences and schedules). -/
inductive Reach (C : Cfg P V) : Glob P V → Prop
  | init : Reach C (init C)
  | step {s : Glob P V} (c : ℕ → P) (a : Act P V) : Reach C s → Reach C (step C c a s)

end VABA
