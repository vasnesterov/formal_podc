import Mathlib
import Cslib.Computability.Distributed.Byzantine.Certificate

/-!
# The fast Byzantine consensus protocol of Kuznetsov–Tonkikh–Zhang (generalized version)

Kuznetsov, Tonkikh, Zhang, *Revisiting Optimal Resilience of Fast Byzantine Consensus*, PODC 2021
(arXiv:2102.12825v3), Section 3 and Appendix A.

We model the *safety-relevant* part of the generalized protocol (parameters `f`, `t`,
`1 ≤ t ≤ f`, `n ≥ 3f + 2t − 1`) as an asynchronous, interleaving transition system with an
ideal signature scheme:

* Every signed statement (and every message sent over an authenticated channel) is a *token*
  `Tok P V` with a signer. The global state records the set `E` of all tokens emitted so far.
  Since signatures are unforgeable and channels authenticated, a message carrying a token can
  only be received after the token was emitted, so all enabling conditions of correct processes
  are stated in terms of `E` (this over-approximates "received"; safety for this more permissive
  system implies safety for the real protocol).
* Byzantine processes (`B`) may emit any token they sign, at any time.
* A correct process may take any of its enabled steps at any time (the view synchronizer, timers
  and message delays are abstracted by nondeterminism; safety must hold for all of them).

Votes carry, instead of the full certificates, the signed pair `(x, u)` of the latest
acknowledged proposal and the pair of the latest collected commit certificate; the attached
certificates (`σ`, `τ`, `cc`) are self-certifying, so a verifier checks their existence in `E`
(`ValidBallot`, `ValidCC`). Views start at `0` (the paper's view `1`).

Decisions are a predicate on `E` (`DecidedIn`): `n − t` `ack` tokens (fast path) or
`⌈(n+f+1)/2⌉` `commit` tokens (slow path) for the same value and view. A correct process decides
`x` exactly when it has received such a quorum, which is possible only if `DecidedIn E x v` holds
for the current `E`.
-/

namespace FastByzantineConsensus.Protocol

open Finset

/-- Signed statements (ideal signatures): the signer is the first argument. -/
inductive Tok (P V : Type*) where
  /-- `propose(x, v)` signed by the leader `p` of view `v` (the paper's `τ`). -/
  | propose (p : P) (x : V) (v : ℕ)
  /-- `ack(x, v)` sent by `p` (with the signature `φ_ack` of the generalized version). -/
  | ack (p : P) (x : V) (v : ℕ)
  /-- `CertAck(x, v)` signed by `p` (a share of a progress certificate). -/
  | certAck (p : P) (x : V) (v : ℕ)
  /-- `Commit(x, v, cc)` sent by `p` (slow path). -/
  | commit (p : P) (x : V) (v : ℕ)
  /-- `vote` of `p` for view `v`: the latest acknowledged proposal `(x, u)` (or `nil`) and the
  latest collected commit certificate `(x', u')` (or `nil`). -/
  | vote (p : P) (v : ℕ) (b : Option (V × ℕ)) (c : Option (V × ℕ))
  deriving DecidableEq

namespace Tok

variable {P V : Type*}

/-- The signer (sender) of a token. -/
def signer : Tok P V → P
  | propose p _ _ => p
  | ack p _ _ => p
  | certAck p _ _ => p
  | commit p _ _ => p
  | vote p _ _ _ => p

end Tok

/-- Parameters of the protocol: `f` (resilience), `t` (fast-path threshold), the leader map. -/
structure Params (P : Type*) where
  f : ℕ
  t : ℕ
  leader : ℕ → P

variable {P V : Type*} [Fintype P] [DecidableEq P]

namespace Params

variable (pr : Params P)

/-- Size of a commit certificate and of a slow-path quorum: `⌈(n + f + 1) / 2⌉`. -/
def qc : ℕ := (Fintype.card P + pr.f + 2) / 2

end Params

section Quorums

open Classical

variable (pr : Params P) (E : Set (Tok P V))

/-- Processes that acknowledged `(x, v)`. -/
noncomputable def ackers (x : V) (v : ℕ) : Finset P := univ.filter fun s => Tok.ack s x v ∈ E

/-- Processes that sent `Commit(x, v)`. -/
noncomputable def committers (x : V) (v : ℕ) : Finset P :=
  univ.filter fun s => Tok.commit s x v ∈ E

/-- Processes that signed `CertAck(x, v)`. -/
noncomputable def certAckers (x : V) (v : ℕ) : Finset P :=
  univ.filter fun s => Tok.certAck s x v ∈ E

/-- A valid progress certificate for `(x, v)`: `f + 1` `CertAck(x, v)` signatures (a threshold
certificate, `Cslib.Byzantine.Certified`). -/
def Certified (x : V) (v : ℕ) : Prop :=
  Cslib.Byzantine.Certified (fun s (xv : V × ℕ) => Tok.certAck s xv.1 xv.2 ∈ E) (pr.f + 1) (x, v)

/-- A valid commit certificate for `(x, v)`: `⌈(n+f+1)/2⌉` `ack(x, v)` signatures. -/
def HasCC (x : V) (v : ℕ) : Prop :=
  Cslib.Byzantine.Certified (fun s (xv : V × ℕ) => Tok.ack s xv.1 xv.2 ∈ E) pr.qc (x, v)

omit [DecidableEq P] in
theorem hasCC_iff {x : V} {v : ℕ} : HasCC pr E x v ↔ pr.qc ≤ (ackers E x v).card := Iff.rfl

/-- `x` is decided in view `v`: fast path (`n − t` acks) or slow path (`⌈(n+f+1)/2⌉` commits). -/
def DecidedIn (x : V) (v : ℕ) : Prop :=
  Fintype.card P - pr.t ≤ (ackers E x v).card ∨ pr.qc ≤ (committers E x v).card

/-- Some value is decided: `x` is decided in some view. -/
def Decided (x : V) : Prop := ∃ v, DecidedIn pr E x v

/-- Validity of the proposal part of a vote for view `v`: `nil`, or `(x, u)` with `u < v`, the
leader's signature on `propose(x, u)` and a progress certificate for `(x, u)` (none needed in the
first view). The condition `u < v` is not in the paper (see `differencies.md`). -/
def ValidBallot (v : ℕ) : Option (V × ℕ) → Prop
  | none => True
  | some (x, u) => u < v ∧ Tok.propose (pr.leader u) x u ∈ E ∧ (u = 0 ∨ Certified pr E x u)

/-- Validity of the commit-certificate part of a vote for view `v`. -/
def ValidCC (v : ℕ) : Option (V × ℕ) → Prop
  | none => True
  | some (x, u) => u < v ∧ HasCC pr E x u

/-- A set `S` of at least `n − f` valid votes for view `v` (one per voter; `bal s`, `cc s` is the
content of the vote of `s`). -/
def ValidVotes (v : ℕ) (S : Finset P) (bal cc : P → Option (V × ℕ)) : Prop :=
  Fintype.card P - pr.f ≤ S.card ∧
    ∀ s ∈ S, Tok.vote s v (bal s) (cc s) ∈ E ∧ ValidBallot pr E v (bal s) ∧ ValidCC pr E v (cc s)

/-- The selection algorithm (Section 3.2 and Appendix A.2): the values `x` that a correct
verifier accepts as the outcome of the selection on the vote set `S`.
* all votes `nil`: any value (the leader's input);
* otherwise let `w` be the highest view in a vote; if a single value `x` has a vote in view `w`,
  only `x`;
* otherwise `leader w` equivocated; with `S' = S \ {leader w}` (still at least `n − f` votes):
  (1) a value with a commit certificate for view `w` in `S'`; else (2) a value with `f + t` votes
  in view `w` in `S'`; else (3) any value. -/
def Selects (v : ℕ) (S : Finset P) (bal cc : P → Option (V × ℕ)) (x : V) : Prop :=
  (∀ s ∈ S, bal s = none) ∨
  ∃ w, (∃ s ∈ S, ∃ y, bal s = some (y, w)) ∧ (∀ s ∈ S, ∀ y u, bal s = some (y, u) → u ≤ w) ∧
    ((∀ s ∈ S, ∀ y, bal s = some (y, w) → y = x) ∨
     ((∃ s₁ ∈ S, ∃ s₂ ∈ S, ∃ y₁ y₂, bal s₁ = some (y₁, w) ∧ bal s₂ = some (y₂, w) ∧ y₁ ≠ y₂) ∧
      Fintype.card P - pr.f ≤ (S.erase (pr.leader w)).card ∧
      ((∃ s ∈ S.erase (pr.leader w), cc s = some (x, w)) ∨
       ((∀ s ∈ S.erase (pr.leader w), ∀ y, cc s ≠ some (y, w)) ∧
         pr.f + pr.t ≤ ((S.erase (pr.leader w)).filter fun s => bal s = some (x, w)).card) ∨
       ((∀ s ∈ S.erase (pr.leader w), ∀ y, cc s ≠ some (y, w)) ∧
         ∀ y, ((S.erase (pr.leader w)).filter fun s => bal s = some (y, w)).card < pr.f + pr.t))))

end Quorums

/-- Local state of a correct process. -/
structure Local (V : Type*) where
  /-- Current view (never decreases). -/
  view : ℕ
  /-- `vote_q`: the latest acknowledged proposal `(x, u)`. -/
  ballot : Option (V × ℕ)
  /-- The latest collected commit certificate `(x, u)`. -/
  cc : Option (V × ℕ)

/-- Global state: emitted tokens and local states of correct processes. -/
structure State (P V : Type*) where
  E : Set (Tok P V)
  loc : P → Local V

/-- Initial state. -/
def init : State P V where
  E := ∅
  loc _ := ⟨0, none, none⟩

variable (pr : Params P) (B : Finset P) (inp : P → V)

/-- One step of the system. `B`: Byzantine processes; `inp`: inputs. -/
inductive Step : State P V → State P V → Prop
  /-- A correct process `q` moves to a higher view `v` and sends its vote to `leader v`. -/
  | enterView (s : State P V) (q : P) (v : ℕ) (hq : q ∉ B) (hv : (s.loc q).view < v) :
      Step s ⟨insert (Tok.vote q v (s.loc q).ballot (s.loc q).cc) s.E,
        Function.update s.loc q { s.loc q with view := v }⟩
  /-- The correct leader `q` of its current view proposes `x` (its input in the first view,
  otherwise a value with a progress certificate), once per view. -/
  | propose (s : State P V) (q : P) (x : V) (hq : q ∉ B)
      (hl : pr.leader (s.loc q).view = q)
      (hfirst : ∀ y, Tok.propose q y (s.loc q).view ∉ s.E)
      (hx : ((s.loc q).view = 0 ∧ x = inp q) ∨ ((s.loc q).view ≠ 0 ∧ Certified pr s.E x (s.loc q).view)) :
      Step s ⟨insert (Tok.propose q x (s.loc q).view) s.E, s.loc⟩
  /-- A correct process acknowledges the (first) valid proposal of its current view and adopts
  it as its vote. -/
  | ack (s : State P V) (q : P) (x : V) (hq : q ∉ B)
      (hp : Tok.propose (pr.leader (s.loc q).view) x (s.loc q).view ∈ s.E)
      (hc : (s.loc q).view = 0 ∨ Certified pr s.E x (s.loc q).view)
      (hfirst : ∀ y, Tok.ack q y (s.loc q).view ∉ s.E) :
      Step s ⟨insert (Tok.ack q x (s.loc q).view) s.E,
        Function.update s.loc q { s.loc q with ballot := some (x, (s.loc q).view) }⟩
  /-- A correct process signs `CertAck(x, v)` after verifying a valid vote set for view `v` on
  which the selection algorithm may output `x`. -/
  | certAck (s : State P V) (q : P) (x : V) (v : ℕ) (hq : q ∉ B) (S : Finset P)
      (bal cc : P → Option (V × ℕ)) (hS : ValidVotes pr s.E v S bal cc)
      (hsel : Selects pr v S bal cc x) :
      Step s ⟨insert (Tok.certAck q x v) s.E, s.loc⟩
  /-- A correct process that collected a commit certificate for its current view sends
  `Commit` and records the certificate. -/
  | commit (s : State P V) (q : P) (x : V) (hq : q ∉ B) (hcc : HasCC pr s.E x (s.loc q).view) :
      Step s ⟨insert (Tok.commit q x (s.loc q).view) s.E,
        Function.update s.loc q { s.loc q with cc := some (x, (s.loc q).view) }⟩
  /-- A Byzantine process emits an arbitrary token signed by itself. -/
  | byz (s : State P V) (m : Tok P V) (hm : m.signer ∈ B) :
      Step s ⟨insert m s.E, s.loc⟩

/-- Reachable states. -/
def Reachable (s : State P V) : Prop := Relation.ReflTransGen (Step pr B inp) init s

end FastByzantineConsensus.Protocol
