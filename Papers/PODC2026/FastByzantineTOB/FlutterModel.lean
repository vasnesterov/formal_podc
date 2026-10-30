import Mathlib

set_option linter.unusedSectionVars false

/-!
# Flutter (Algorithms 2 and 3): the model

Monti, Camaioni, Roman. *Fast Byzantine Total Order Broadcast.* PODC 2026 (arXiv:2412.14061v2).

## Model

* Servers `P` (finite) and clients `C` are distinct nodes (`Node P C = P ⊕ C`). `F : Finset P` is the
  set of Byzantine servers, `G : Set C` the set of Byzantine clients (no bound on `G`).
* Asynchronous interleaving semantics: a run is a sequence of global states; each step is a stutter or
  one *action* of one correct node whose guard holds. Byzantine nodes have no state: their messages
  are arbitrary and can be delivered at any time.
* Authenticated FIFO links: for a correct sender `a` and any receiver `b`, `sent a b` is the list of
  all messages `a` sent to `b`, and `dlv a b` how many of them `b` has delivered; a delivery from a
  correct sender delivers the next message, `(sent a b)[dlv a b]`. Messages from Byzantine senders are
  arbitrary (but carry the true sender identity).
* Time: each correct node has a local clock in a linear order `T`; `tick` moves it forward
  (local clocks are non-decreasing, as the paper's proof of Lemma 15 assumes). Timing bounds
  (`Δ`, `Ψ`) are irrelevant for safety and not modelled.
* `beat()` may be executed at any time (the paper executes it "regularly" and at scheduled times;
  allowing more behaviours only strengthens safety results).
* The instances `con[x]` of Representative Binary Consensus are black boxes: `con[x].Decide v`
  reaches a correct server as an unconstrained environment action (`Action.decide`). Their
  specification is a hypothesis on whole runs (`ConRepValidity`, `ConAgreement` in
  `FlutterSafety.lean`).
* The lock-time quorum (`4f+1` in the paper) is a parameter `q`; `f` is used by clients (line 20).
* The order on `Θ × M × T` is Assumption 1: by bet, then client, then message (`Tag`).

History variables: `props` (proposals to `con`), `decs` (decisions of `con`), `procd` (processed
candidates with their decision), `orders` (sequence of calls to `order`), `dels` (sequence of
`tob.Deliver` events); `bcast` for clients (messages broadcast).
-/

namespace Podc.FastByzantineTOB.Flutter

/-- A client-issued message with its bet: `(θ, m, b)`. -/
structure Tag (C M T : Type*) where
  /-- The bet `b`. -/
  bet : T
  /-- The issuing client `θ`. -/
  client : C
  /-- The payload `m`. -/
  msg : M
  deriving DecidableEq

variable {C M T : Type*}

/-- Assumption 1: tags are compared by bet, then client, then message. -/
def Tag.toLex (x : Tag C M T) : T ×ₗ C ×ₗ M :=
  _root_.toLex (x.bet, _root_.toLex (x.client, x.msg))

lemma Tag.toLex_injective : Function.Injective (Tag.toLex : Tag C M T → _) := by
  rintro ⟨b, c, m⟩ ⟨b', c', m'⟩ h
  simp only [Tag.toLex, toLex_inj, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl, rfl⟩ := h
  rfl

variable [LinearOrder C] [LinearOrder M] [LinearOrder T]

instance : LinearOrder (Tag C M T) :=
  LinearOrder.lift' Tag.toLex Tag.toLex_injective

lemma Tag.le_def (x y : Tag C M T) : x ≤ y ↔ x.toLex ≤ y.toLex := Iff.rfl

lemma Tag.lt_def (x y : Tag C M T) : x < y ↔ x.toLex < y.toLex := Iff.rfl

lemma Tag.bet_le_of_le {x y : Tag C M T} (h : x ≤ y) : x.bet ≤ y.bet := by
  rw [Tag.le_def, Tag.toLex, Tag.toLex, Prod.Lex.toLex_le_toLex] at h
  rcases h with h | ⟨h, -⟩
  · exact h.le
  · exact h.le

lemma Tag.lt_of_bet_lt {x y : Tag C M T} (h : x.bet < y.bet) : x < y := by
  rw [Tag.lt_def, Tag.toLex, Tag.toLex, Prod.Lex.toLex_lt_toLex]
  exact Or.inl h

/-- Messages. -/
inductive Msg (C M T : Type*)
  /-- `[Time, t]` (server to server, line 16). -/
  | time (t : T)
  /-- `[Observe, θ, m, b]` (server to server, line 26). -/
  | observe (x : Tag C M T)
  /-- `[Message, m, b]` (client to server, Alg. 3 line 14). -/
  | message (m : M) (b : T)
  /-- `[Decision, m, b, v]` (server to client, line 41). -/
  | decision (m : M) (b : T) (v : Bool)
  deriving DecidableEq

/-- Nodes: servers and clients. -/
abbrev Node (P C : Type*) := P ⊕ C

/-- Local state of a server (Alg. 2, lines 6–13) with history variables. -/
structure SState (P C M T : Type*) where
  /-- Local clock. -/
  clock : T
  /-- `observed` (line 7). -/
  observed : Finset (Tag C M T)
  /-- `proposed` (line 8). -/
  proposed : Finset (Tag C M T)
  /-- `candidates` (line 9). -/
  cands : Finset (Tag C M T)
  /-- `delivered` (line 10). -/
  delivered : Finset (C × M)
  /-- `remote_times` (line 11); `⊥` is `-∞`. -/
  remote : P → WithBot T
  /-- `decisions` (line 12). -/
  decisions : Tag C M T → Option Bool
  /-- `last_processed` (line 13); `⊥` is `(⊥, ⊥, -∞)`. -/
  lp : WithBot (Tag C M T)
  /-- History: proposals to `con` (lines 35, 38). -/
  props : Finset (Tag C M T × Bool)
  /-- History: decisions of `con` (line 40). -/
  decs : Finset (Tag C M T × Bool)
  /-- History: processed candidates with their decision (line 43). -/
  procd : Finset (Tag C M T × Bool)
  /-- History: the sequence of calls to `order` (line 47). -/
  orders : List (Tag C M T)
  /-- History: the sequence of `tob.Deliver` events (line 49). -/
  dels : List (C × M)
  /-- History: the messages sent to every server (`Time`, line 16; `Observe`, line 26). -/
  obox : List (Msg C M T)

/-- Local state of a client (Alg. 3, lines 8–10) with a history variable. -/
structure CState (P C M T : Type*) where
  /-- Local clock. -/
  clock : T
  /-- `submissions` (line 9). -/
  subs : M → Option (ℕ × T)
  /-- `decisions` (line 10). -/
  decisions : M × T × P → Option Bool
  /-- History: messages broadcast (`tob.Broadcast`). -/
  bcast : Finset M
  /-- History: the messages sent to every server (`Message`, Alg. 3 line 14). -/
  cbox : List (Msg C M T)

/-- Global state. -/
structure State (P C M T : Type*) where
  /-- Server states. -/
  srv : P → SState P C M T
  /-- Client states. -/
  cli : C → CState P C M T
  /-- `sent a b`: all messages sent by `a` to `b` (meaningful for correct `a`). -/
  sent : Node P C → Node P C → List (Msg C M T)
  /-- `dlv a b`: number of messages of `sent a b` delivered to `b`. -/
  dlv : Node P C → Node P C → ℕ

variable {P : Type*} [Fintype P] [DecidableEq P] [DecidableEq C]

/-- Initial server state. -/
def SState.init (t0 : T) : SState P C M T :=
  ⟨t0, ∅, ∅, ∅, ∅, fun _ => ⊥, fun _ => none, ⊥, ∅, ∅, ∅, [], [], []⟩

/-- Initial client state. -/
def CState.init (t0 : T) : CState P C M T := ⟨t0, fun _ => none, fun _ => none, ∅, []⟩

/-- Initial global state, with arbitrary initial clocks. -/
def State.init (c0 : P → T) (d0 : C → T) : State P C M T :=
  ⟨fun p => SState.init (c0 p), fun θ => CState.init (d0 θ), fun _ _ => [], fun _ _ => 0⟩

/-- `lock_time()` (line 19): the largest value `t` such that at least `q` entries of
`remote_times` are `≥ t` (`⊥` if there is none). -/
def lockTime (q : ℕ) (rt : P → WithBot T) : WithBot T :=
  (Finset.univ.filter fun σ => q ≤ (Finset.univ.filter fun ρ => rt σ ≤ rt ρ).card).sup rt

/-- Parameters of a Flutter system. -/
structure Setup (P C T : Type*) where
  /-- Byzantine servers. -/
  F : Finset P
  /-- Byzantine clients. -/
  G : Set C
  /-- Membership in `G` is decidable. -/
  decG : DecidablePred (· ∈ G)
  /-- The fault bound `f` (used by clients, Alg. 3 line 20). -/
  f : ℕ
  /-- The lock-time quorum (`4f+1` in the paper). -/
  q : ℕ
  /-- Client's estimate `Δ̃` of the message delay. -/
  dEst : T
  /-- Bet margin `ε`. -/
  eps : T

attribute [instance] Setup.decG

/-- Actions. -/
inductive Action (P C M T : Type*)
  /-- A server's clock moves forward to `t`. -/
  | tick (p : P) (t : T)
  /-- `beat()` (line 14). -/
  | beat (p : P)
  /-- Server `p` delivers `msg` from server `σ` (lines 17, 29). -/
  | srvRecv (p σ : P) (msg : Msg C M T)
  /-- Server `p` delivers `msg` from client `θ` (line 31). -/
  | cliMsg (p : P) (θ : C) (msg : Msg C M T)
  /-- Line 37: propose `False` for an observed, unproposed tag whose bet is reached. -/
  | proposeFalse (p : P) (x : Tag C M T)
  /-- `con[x].Decide v` at server `p` (line 40), an environment event of the black box. -/
  | decide (p : P) (x : Tag C M T) (v : Bool)
  /-- Line 43: process the next candidate `x`, whose decision is `v`. -/
  | process (p : P) (x : Tag C M T) (v : Bool)
  /-- A client's clock moves forward to `t`. -/
  | cTick (θ : C) (t : T)
  /-- `tob.Broadcast m` at client `θ` (Alg. 3 line 16). -/
  | cBroadcast (θ : C) (m : M)
  /-- Client `θ` delivers `msg` from server `σ` (Alg. 3 line 18). -/
  | cRecv (θ : C) (σ : P) (msg : Msg C M T)
  /-- Alg. 3 line 20: resubmit `m` after `f + 1` rejections. -/
  | cRetry (θ : C) (m : M)

section Exec

variable (S : Setup P C T)

/-- The next message on the link from a correct `a` to `b`. -/
def State.next (s : State P C M T) (a b : Node P C) : Option (Msg C M T) :=
  (s.sent a b)[s.dlv a b]?

/-- Guard of an action: the actor is correct and the conditions of its `upon` clause hold. -/
def Enabled [AddCommMonoid T] (s : State P C M T) : Action P C M T → Prop
  | .tick p t => p ∉ S.F ∧ (s.srv p).clock ≤ t
  | .beat p => p ∉ S.F
  | .srvRecv p σ msg => p ∉ S.F ∧ (σ ∈ S.F ∨ s.next (.inl σ) (.inl p) = some msg)
  | .cliMsg p θ msg => p ∉ S.F ∧ (θ ∈ S.G ∨ s.next (.inr θ) (.inl p) = some msg)
  | .proposeFalse p x => p ∉ S.F ∧ x ∈ (s.srv p).observed ∧ x ∉ (s.srv p).proposed ∧
      x.bet ≤ (s.srv p).clock
  | .decide p _ _ => p ∉ S.F
  | .process p x v => p ∉ S.F ∧ x ∈ (s.srv p).cands ∧ (s.srv p).lp < x ∧
      (∀ z ∈ (s.srv p).cands, (s.srv p).lp < z → x ≤ z) ∧ (s.srv p).decisions x = some v ∧
      (x.bet : WithBot T) ≤ lockTime S.q (s.srv p).remote
  | .cTick θ t => θ ∉ S.G ∧ (s.cli θ).clock ≤ t
  | .cBroadcast θ m => θ ∉ S.G ∧ m ∉ (s.cli θ).bcast
  | .cRecv θ σ msg => θ ∉ S.G ∧ (σ ∈ S.F ∨ s.next (.inl σ) (.inr θ) = some msg)
  | .cRetry θ m => θ ∉ S.G ∧ match (s.cli θ).subs m with
      | some (_, b) =>
        S.f + 1 ≤ (Finset.univ.filter fun π => (s.cli θ).decisions (m, b, π) = some false).card
      | none => False

instance [AddCommMonoid T] (s : State P C M T) (a : Action P C M T) : Decidable (Enabled S s a) := by
  cases a with
  | cRetry θ m =>
    unfold Enabled
    have : Decidable (match (s.cli θ).subs m with
      | some (_, b) =>
        S.f + 1 ≤ (Finset.univ.filter fun π => (s.cli θ).decisions (m, b, π) = some false).card
      | none => False) := by split <;> infer_instance
    infer_instance
  | _ => unfold Enabled; infer_instance

/-- Send `msg` from `a` to every server. -/
def sendAll (sent : Node P C → Node P C → List (Msg C M T)) (a : Node P C) (msg : Msg C M T) :
    Node P C → Node P C → List (Msg C M T) :=
  fun x y => if x = a ∧ y.isLeft then sent x y ++ [msg] else sent x y

/-- Send `msg` from `a` to `b`. -/
def send1 (sent : Node P C → Node P C → List (Msg C M T)) (a b : Node P C) (msg : Msg C M T) :
    Node P C → Node P C → List (Msg C M T) :=
  Function.update sent a (Function.update (sent a) b (sent a b ++ [msg]))

/-- Update the state of server `p`. -/
def State.updSrv (s : State P C M T) (p : P) (f : SState P C M T → SState P C M T) :
    State P C M T :=
  { s with srv := Function.update s.srv p (f (s.srv p)) }

/-- Update the state of client `θ`. -/
def State.updCli (s : State P C M T) (θ : C) (f : CState P C M T → CState P C M T) :
    State P C M T :=
  { s with cli := Function.update s.cli θ (f (s.cli θ)) }

/-- Count one delivery on the link `a → b`. -/
def State.bump (s : State P C M T) (a b : Node P C) : State P C M T :=
  { s with dlv := Function.update s.dlv a (Function.update (s.dlv a) b (s.dlv a b + 1)) }

/-- Procedure `spot(θ, m, b)` (lines 21–28) at server `p`. -/
noncomputable def State.spot (s : State P C M T) (p : P) (x : Tag C M T) : State P C M T :=
  let s1 := if lockTime S.q (s.srv p).remote < (x.bet : WithBot T)
    then s.updSrv p fun l => { l with cands := insert x l.cands } else s
  if x ∈ (s.srv p).observed then s1
  else { s1.updSrv p (fun l => { l with
      observed := insert x l.observed
      obox := l.obox ++ [.observe x] }) with
    sent := sendAll s1.sent (.inl p) (.observe x) }

/-- Procedure `order(θ, m, b)` (lines 47–50). -/
noncomputable def SState.order (l : SState P C M T) (x : Tag C M T) : SState P C M T :=
  if (x.client, x.msg) ∈ l.delivered then { l with orders := l.orders ++ [x] }
  else { l with
    orders := l.orders ++ [x]
    dels := l.dels ++ [(x.client, x.msg)]
    delivered := insert (x.client, x.msg) l.delivered }

/-- Procedure `submit(m, r)` (Alg. 3, lines 11–15) at client `θ`. -/
def State.submit [AddCommMonoid T] (s : State P C M T) (θ : C) (m : M) (r : ℕ) : State P C M T :=
  let b := (s.cli θ).clock + 2 ^ r • S.dEst + S.eps
  { (s.updCli θ fun l => { l with
      subs := Function.update l.subs m (some (r, b))
      cbox := l.cbox ++ [.message m b] }) with
    sent := sendAll s.sent (.inr θ) (.message m b) }

/-- Byzantine nodes. -/
def Setup.Byz : Node P C → Prop
  | .inl σ => σ ∈ S.F
  | .inr θ => θ ∈ S.G

instance (a : Node P C) : Decidable (S.Byz a) := by
  cases a <;> unfold Setup.Byz <;> infer_instance

/-- Count a delivery on the link `a → b` (only links from correct senders are FIFO queues). -/
noncomputable def State.recv (s : State P C M T) (a b : Node P C) : State P C M T :=
  if S.Byz a then s else s.bump a b

/-- Handling of a message from server `σ` at server `p` (lines 17–18 and 29–30). -/
noncomputable def State.onSrv (s : State P C M T) (p σ : P) : Msg C M T → State P C M T
  | .time t => s.updSrv p fun l =>
      { l with remote := Function.update l.remote σ (max (l.remote σ) (t : WithBot T)) }
  | .observe x => s.spot S p x
  | _ => s

/-- Lines 32–36: spot `x` and, if `x` was not proposed yet, propose whether it is in time. -/
noncomputable def State.accept (s : State P C M T) (p : P) (x : Tag C M T) : State P C M T :=
  let s2 := s.spot S p x
  if x ∈ (s2.srv p).proposed then s2
  else s2.updSrv p fun l => { l with
    props := insert (x, decide ((l.clock : T) < x.bet)) l.props
    proposed := insert x l.proposed }

/-- Handling of a message from client `θ` at server `p` (line 31). -/
noncomputable def State.onCli (s : State P C M T) (p : P) (θ : C) : Msg C M T → State P C M T
  | .message m b => s.accept S p ⟨b, θ, m⟩
  | _ => s

/-- Handling of a message from server `σ` at client `θ` (Alg. 3 line 18). -/
def State.onDec (s : State P C M T) (θ : C) (σ : P) : Msg C M T → State P C M T
  | .decision m b v => s.updCli θ fun l =>
      { l with decisions := Function.update l.decisions (m, b, σ) (some v) }
  | _ => s

/-- Effect of an action. -/
noncomputable def exec [AddCommMonoid T] (s : State P C M T) : Action P C M T → State P C M T
  | .tick p t => s.updSrv p fun l => { l with clock := t }
  | .beat p => { (s.updSrv p fun l => { l with obox := l.obox ++ [.time l.clock] }) with
      sent := sendAll s.sent (.inl p) (.time (s.srv p).clock) }
  | .srvRecv p σ msg => (s.recv S (.inl σ) (.inl p)).onSrv S p σ msg
  | .cliMsg p θ msg => (s.recv S (.inr θ) (.inl p)).onCli S p θ msg
  | .proposeFalse p x => s.updSrv p fun l => { l with
      props := insert (x, false) l.props
      proposed := insert x l.proposed }
  | .decide p x v => { (s.updSrv p fun l => { l with
        decs := insert (x, v) l.decs
        decisions := Function.update l.decisions x (some v) }) with
      sent := send1 s.sent (.inl p) (.inr x.client) (.decision x.msg x.bet v) }
  | .process p x v => s.updSrv p fun l =>
      { (if v then l.order x else l) with
        lp := (x : WithBot (Tag C M T))
        procd := insert (x, v) l.procd }
  | .cTick θ t => s.updCli θ fun l => { l with clock := t }
  | .cBroadcast θ m =>
      (s.submit S θ m 0).updCli θ fun l => { l with bcast := insert m l.bcast }
  | .cRecv θ σ msg => (s.recv S (.inl σ) (.inr θ)).onDec θ σ msg
  | .cRetry θ m =>
    match (s.cli θ).subs m with
    | some (r, _) => s.submit S θ m (r + 1)
    | none => s

/-- One step: a stutter or one enabled action. -/
def Step [AddCommMonoid T] (s s' : State P C M T) : Prop :=
  s' = s ∨ ∃ a, Enabled S s a ∧ s' = exec S s a

/-- A run of Flutter. -/
structure Run [AddCommMonoid T] where
  /-- Global state at time `k`. -/
  st : ℕ → State P C M T
  init : ∃ c0 d0, st 0 = State.init c0 d0
  step : ∀ k, Step S (st k) (st (k + 1))

end Exec

end Podc.FastByzantineTOB.Flutter
