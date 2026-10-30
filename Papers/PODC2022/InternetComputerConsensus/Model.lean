import Mathlib
import Cslib.Computability.Distributed.Byzantine.Certificate

/-!
# Protocol ICC0 (Internet Computer Consensus): the model

Camenisch, Drijvers, Hanke, Pignolet, Shoup, Williams. *Internet Computer Consensus.* PODC 2022.
Sections 3.4–3.5, Figures 1 and 2.

We model Protocol ICC0 (Tree Building Subprotocol, Figure 1, and Finalization Subprotocol,
Figure 2) as an asynchronous interleaving transition system with discrete global time and
idealized cryptography.

* **Parties.** A finite type `P` of `n = Fintype.card P` parties; a static set `F` of corrupt
  parties (chosen before the execution). Only honest parties (`p ∉ F`) take protocol steps;
  corrupt parties are modelled by what the adversary can inject into honest pools (`Avail`).
* **Blocks.** Collision resistance of `H` is idealized: a block contains its parent block itself
  (`Block.mk k α parent payload`), so "`phash = H(B_p)`" is "`parent = B_p`".
* **Signatures.** Idealized:
  - an authenticator for a block of party `α` can be injected by the adversary iff `α` is corrupt
    or an honest party has broadcast it;
  - a notarization (finalization) share of `q` iff `q` is corrupt or `q` has broadcast it;
  - a notarization (finalization) for `B` iff at least `n - t` parties have signed it, where
    corrupt parties count as having signed everything (the ideal `(t, n - t, n)`-threshold
    signature, `Cslib.Byzantine.Certified`);
  - a random-beacon share of `q` iff `q` is corrupt or `q` broadcast it. The beacon value is
    unique, so the permutation of round `k` is a fixed function `rank k : P → ℕ`.
* **Network.** Every broadcast message of an honest party is added to the global set `sent` and
  to the sender's own pool; the adversary delivers any available message to any honest pool at
  any time (asynchrony; eventual delivery and synchrony are properties of runs, see
  `Liveness.lean`). Pools only grow.
* **Time.** A global discrete clock `now`; each honest party records the start time `t0 k` of each
  round `k` it entered (the paper's `t₀ ← clock()`). A `tick` advances time. In `UStep` (used for
  liveness) a tick is allowed only when no honest party has an enabled clause: this is the
  paper's "wait for" semantics (a clause is executed as soon as its condition holds).
-/

namespace Podc.InternetComputerConsensus

open Finset Cslib.Byzantine

variable {P V : Type*}

/-- A block: the special `root`, or a round-`k` block `(block, k, α, phash, payload)` proposed by
party `α`, whose `phash` is idealized as the parent block itself. -/
inductive Block (P V : Type*) where
  | root : Block P V
  | mk (round : ℕ) (prop : P) (parent : Block P V) (payload : V) : Block P V

namespace Block

/-- The round number (= depth) of a block; the root has round `0`. -/
def round : Block P V → ℕ
  | root => 0
  | mk k _ _ _ => k

/-- The parent of a block (the root is its own parent). -/
def parent : Block P V → Block P V
  | root => root
  | mk _ _ par _ => par

/-- The rank of the proposer of a block in the block's round, according to `rank`. -/
def rk (rank : ℕ → P → ℕ) : Block P V → ℕ
  | root => 0
  | mk k α _ _ => rank k α

/-- The proposer of a block (`none` for the root). -/
def prop? : Block P V → Option P
  | root => none
  | mk _ α _ _ => some α

/-- The chain of blocks from round `1` to `B` (the root excluded), oldest first. -/
def chain : Block P V → List (Block P V)
  | root => []
  | b@(mk _ _ par _) => chain par ++ [b]

@[simp] theorem round_root : (root : Block P V).round = 0 := rfl
@[simp] theorem round_mk (k : ℕ) (α : P) (par : Block P V) (pl : V) :
    (mk k α par pl).round = k := rfl
@[simp] theorem parent_mk (k : ℕ) (α : P) (par : Block P V) (pl : V) :
    (mk k α par pl).parent = par := rfl
@[simp] theorem rk_mk (rank : ℕ → P → ℕ) (k : ℕ) (α : P) (par : Block P V) (pl : V) :
    (mk k α par pl).rk rank = rank k α := rfl
@[simp] theorem chain_root : (root : Block P V).chain = [] := rfl
@[simp] theorem chain_mk (k : ℕ) (α : P) (par : Block P V) (pl : V) :
    (mk k α par pl).chain = par.chain ++ [mk k α par pl] := rfl

end Block

/-- Messages. `block B` and `auth B` are the block and its authenticator, `notar B`/`final B`
the (combined) notarization/finalization, `notarShare B q`/`finalShare B q` the shares of `q`,
`beacon k q` the share of `q` of the round-`k` random beacon. -/
inductive Msg (P V : Type*) where
  | block (B : Block P V)
  | auth (B : Block P V)
  | notar (B : Block P V)
  | notarShare (B : Block P V) (q : P)
  | final (B : Block P V)
  | finalShare (B : Block P V) (q : P)
  | beacon (k : ℕ) (q : P)

/-- The round a message belongs to. -/
def Msg.round : Msg P V → ℕ
  | .block B => B.round
  | .auth B => B.round
  | .notar B => B.round
  | .notarShare B _ => B.round
  | .final B => B.round
  | .finalShare B _ => B.round
  | .beacon k _ => k

/-- Protocol parameters: the resilience `t`, the ranks given by the random beacon
(`rank k q` = rank of `q` in round `k`), and the delay functions `Δprop`, `Δntry`. -/
structure Params (P : Type*) where
  t : ℕ
  rank : ℕ → P → ℕ
  Δprop : ℕ → ℕ
  Δntry : ℕ → ℕ

variable [Fintype P] (π : Params P) (F : Finset P)

/-- Validity of a block for a party with pool `pool` (Section 3.4): authentic (block and
authenticator in the pool) and extending a notarized block of the previous round. The root is
valid. -/
def Valid (pool : Set (Msg P V)) : Block P V → Prop
  | .root => True
  | .mk k α par pl =>
      par.round + 1 = k ∧ Msg.block (.mk k α par pl) ∈ pool ∧ Msg.auth (.mk k α par pl) ∈ pool ∧
        Valid pool par ∧ (par = .root ∨ Msg.notar par ∈ pool)

/-- A block is notarized for a party: valid, with a notarization in its pool (the root is its own
notarization). -/
def Notarized (pool : Set (Msg P V)) (B : Block P V) : Prop :=
  Valid pool B ∧ (B = .root ∨ Msg.notar B ∈ pool)

/-- A block is finalized for a party: valid, with a finalization in its pool. -/
def Finalized (pool : Set (Msg P V)) (B : Block P V) : Prop :=
  Valid pool B ∧ Msg.final B ∈ pool

/-- A notarization on `B` can exist given the set `S` of messages broadcast by honest parties:
at least `n - t` parties signed it (corrupt parties sign anything). -/
def NotarCert (S : Set (Msg P V)) (B : Block P V) : Prop :=
  Certified (fun q B => q ∈ F ∨ Msg.notarShare B q ∈ S) (Fintype.card P - π.t) B

/-- A finalization on `B` can exist given the set `S` of honest messages. -/
def FinalCert (S : Set (Msg P V)) (B : Block P V) : Prop :=
  Certified (fun q B => q ∈ F ∨ Msg.finalShare B q ∈ S) (Fintype.card P - π.t) B

/-- Messages the adversary can make an honest party receive, given the set `S` of messages
broadcast by honest parties so far (idealized unforgeability). -/
def Avail (S : Set (Msg P V)) : Msg P V → Prop
  | .block _ => True
  | .auth B => (∃ k α par pl, B = .mk k α par pl ∧ α ∈ F) ∨ Msg.auth B ∈ S
  | .notar B => B = .root ∨ NotarCert π F S B
  | .notarShare B q => q ∈ F ∨ Msg.notarShare B q ∈ S
  | .final B => FinalCert π F S B
  | .finalShare B q => q ∈ F ∨ Msg.finalShare B q ∈ S
  | .beacon k q => q ∈ F ∨ Msg.beacon k q ∈ S

/-- The local state of a party running ICC0 (Figures 1 and 2).
`round` is the current round `k`; `active` says that the round-`k` beacon has been computed
(otherwise the party waits for `t + 1` beacon shares); `t0 k` is the start time of round `k`;
`N`, `D`, `proposed` are as in Figure 1; `kmax` as in Figure 2; `out` is the output (committed
blocks, oldest first; the payloads are output in this order). -/
structure LState (P V : Type*) where
  pool : Set (Msg P V)
  round : ℕ
  active : Bool
  t0 : ℕ → ℕ
  N : Set (Block P V)
  D : Set ℕ
  proposed : Bool
  kmax : ℕ
  out : List (Block P V)

/-- The global state: the clock, the local states, and all messages broadcast by honest
parties so far. -/
structure GState (P V : Type*) where
  now : ℕ
  loc : P → LState P V
  sent : Set (Msg P V)

/-- Start the current round at time `now`: `t₀ ← clock()`, `N ← ∅`, `D ← ∅`,
`proposed ← false`. -/
def LState.start (l : LState P V) (now : ℕ) : LState P V :=
  { l with active := true, t0 := Function.update l.t0 l.round now, N := ∅, D := ∅,
           proposed := false }

/-- Number of round-`k` beacon shares in a pool is at least `t + 1`. -/
def BeaconReady (pool : Set (Msg P V)) (k : ℕ) : Prop :=
  Certified (fun q k => Msg.beacon k q ∈ pool) (π.t + 1) k

/-- A full set of `n - t` notarization shares for `B` in a pool. -/
def NotarShares (pool : Set (Msg P V)) (B : Block P V) : Prop :=
  Certified (fun q B => Msg.notarShare B q ∈ pool) (Fintype.card P - π.t) B

/-- A full set of `n - t` finalization shares for `B` in a pool. -/
def FinalShares (pool : Set (Msg P V)) (B : Block P V) : Prop :=
  Certified (fun q B => Msg.finalShare B q ∈ pool) (Fintype.card P - π.t) B

/-- One clause of Figure 1 or Figure 2 executed by party `p` at time `now`: the local state
moves from `l` to `l'` and `p` broadcasts the messages `M`. -/
inductive LStep (now : ℕ) (p : P) : LState P V → LState P V → Set (Msg P V) → Prop
  /-- Wait for `t + 1` beacon shares of round `k`, compute the beacon, broadcast the share for
  round `k + 1` and start the round (`N ← ∅`, `D ← ∅`, `proposed ← false`, `t₀ ← clock()`). -/
  | beacon (l : LState P V) :
      l.active = false → BeaconReady π l.pool l.round →
      LStep now p l (l.start now) {Msg.beacon (l.round + 1) p}
  /-- Clause (a): a notarized round-`k` block, or a full set of notarization shares for a valid
  round-`k` block: broadcast the notarization, and a finalization share if `N ⊆ {B}`; the round
  ends. -/
  | finish (l : LState P V) (B : Block P V) :
      l.active = true → B.round = l.round → Valid l.pool B →
      (Msg.notar B ∈ l.pool ∨ NotarShares π l.pool B) →
      LStep now p l { l with round := l.round + 1, active := false }
        {m | m = Msg.notar B ∨ (l.N ⊆ {B} ∧ m = Msg.finalShare B p)}
  /-- Clause (b): after `Δprop(r_me)`, propose a block extending a notarized round-`(k-1)` block
  `Bp` with an arbitrary payload, and broadcast it with its authenticator and `Bp`'s
  notarization. -/
  | propose (l : LState P V) (Bp : Block P V) (pl : V) :
      l.active = true → l.proposed = false → l.t0 l.round + π.Δprop (π.rank l.round p) ≤ now →
      Bp.round + 1 = l.round → Notarized l.pool Bp →
      LStep now p l { l with proposed := true }
        {Msg.block (.mk l.round p Bp pl), Msg.auth (.mk l.round p Bp pl), Msg.notar Bp}
  /-- Clause (c), case "no block in `N` has rank `r`": echo `B` (unless it is our own) and
  broadcast a notarization share for it. -/
  | echoShare (l : LState P V) (B : Block P V) :
      l.active = true → B.round = l.round → Valid l.pool B → B ∉ l.N →
      B.rk π.rank ∉ l.D → l.t0 l.round + π.Δntry (B.rk π.rank) ≤ now →
      (∀ B', Valid l.pool B' → B'.round = l.round → B'.rk π.rank < B.rk π.rank →
        B'.rk π.rank ∈ l.D) →
      (¬ ∃ B' ∈ l.N, B'.rk π.rank = B.rk π.rank) →
      LStep now p l { l with N := insert B l.N }
        {m | (B.rk π.rank ≠ π.rank l.round p ∧
              (m = Msg.block B ∨ m = Msg.auth B ∨ m = Msg.notar B.parent)) ∨
            m = Msg.notarShare B p}
  /-- Clause (c), case "some block in `N` has rank `r`": echo `B` (unless it is our own) and
  disqualify the rank `r`. -/
  | echoDisq (l : LState P V) (B : Block P V) :
      l.active = true → B.round = l.round → Valid l.pool B → B ∉ l.N →
      B.rk π.rank ∉ l.D → l.t0 l.round + π.Δntry (B.rk π.rank) ≤ now →
      (∀ B', Valid l.pool B' → B'.round = l.round → B'.rk π.rank < B.rk π.rank →
        B'.rk π.rank ∈ l.D) →
      (∃ B' ∈ l.N, B'.rk π.rank = B.rk π.rank) →
      LStep now p l { l with D := insert (B.rk π.rank) l.D }
        {m | B.rk π.rank ≠ π.rank l.round p ∧
              (m = Msg.block B ∨ m = Msg.auth B ∨ m = Msg.notar B.parent)}
  /-- Figure 2: a finalized round-`k` block, or a full set of finalization shares for a valid
  round-`k` block, with `k > kmax`: broadcast the finalization, output the last `k - kmax`
  blocks of the chain ending at `B`, and set `kmax ← k`. -/
  | final (l : LState P V) (B : Block P V) :
      Valid l.pool B → l.kmax < B.round → (Msg.final B ∈ l.pool ∨ FinalShares π l.pool B) →
      LStep now p l { l with kmax := B.round, out := l.out ++ B.chain.drop l.kmax }
        {Msg.final B}

/-- The initial local state: round `1`, waiting for the round-`1` beacon, own beacon share in
the pool. -/
def LState.init (p : P) : LState P V where
  pool := {Msg.beacon 1 p}
  round := 1
  active := false
  t0 := fun _ => 0
  N := ∅
  D := ∅
  proposed := false
  kmax := 0
  out := []

/-- The initial global state: every honest party has broadcast its round-`1` beacon share. -/
def GState.init : GState P V where
  now := 0
  loc := LState.init
  sent := {m | ∃ p ∉ F, m = Msg.beacon 1 p}

variable [DecidableEq P]

/-- A step of the system: the adversary delivers an available message to an honest party, an
honest party executes an enabled clause (its broadcasts go to `sent` and to its own pool), or time
advances. -/
inductive Step : GState P V → GState P V → Prop
  | deliver (s : GState P V) (p : P) (m : Msg P V) :
      p ∉ F → Avail π F s.sent m →
      Step s { s with loc := Function.update s.loc p { s.loc p with pool := insert m (s.loc p).pool } }
  | act (s : GState P V) (p : P) (l : LState P V) (M : Set (Msg P V)) :
      p ∉ F → LStep π s.now p (s.loc p) l M →
      Step s { s with loc := Function.update s.loc p { l with pool := l.pool ∪ M },
                      sent := s.sent ∪ M }
  | tick (s : GState P V) : Step s { s with now := s.now + 1 }

/-- Party `p` has no enabled clause. -/
def Settled (s : GState P V) (p : P) : Prop :=
  ∀ l M, ¬ LStep (V := V) π s.now p (s.loc p) l M

/-- Steps with the "wait for" semantics: time advances only when every honest party is
settled. -/
inductive UStep : GState P V → GState P V → Prop
  | step (s s' : GState P V) : Step π F s s' → s'.now = s.now → UStep s s'
  | tick (s : GState P V) : (∀ p ∉ F, Settled π s p) → UStep s { s with now := s.now + 1 }

/-- Reachable states. -/
def Reachable (s : GState P V) : Prop :=
  Relation.ReflTransGen (Step π F) (GState.init F) s

end Podc.InternetComputerConsensus
