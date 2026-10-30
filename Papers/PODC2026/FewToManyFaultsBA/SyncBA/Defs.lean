import Mathlib
import Cslib.Computability.Distributed.Byzantine.LockStep.Sequential

/-!
# The synchronous protocol `SyncBA` (Appendix B.1–B.3): definitions

Formalization of the synchronous Byzantine agreement protocol `SyncBA` of
A. Constantinescu, M. Dufay, A. Paramonov, R. Wattenhofer,
*From Few to Many Faults: Optimal Adaptive Byzantine Agreement* (PODC 2026, arXiv 2505.19989),
behind Theorem 3.1: `ViewByzantineAgreement` (Appendix B.1) with the synchronous retrieval
protocol (`RetrievalLeaderSync` / `RetrievalPartySync`, Section 10.1), run for `n` views, followed by
the fallback detection of `SyncBA` (Appendix B.3) and a black-box quadratic fallback protocol.

## Model

CSLib's synchronous lock-step model `Cslib.Byzantine.LockStep` on the complete network of the
parties `Fin n` (one round = `Δ`), static Byzantine set, ideal signatures
(`Cslib.Byzantine.LockStep.Auth`). Threshold signatures are modelled as *sets of partial
signatures*: a token `(q, s) : Tok n` is `q`'s partial signature on the statement `s`, and a
`k`-certificate on `s` is a set of at least `k` tokens on `s` (`Valid`); since tokens are pairs,
the signers are distinct. (A real threshold signature is one word; we count messages, not bits.)

## The protocol

View `v < n` occupies rounds `11v, …, 11v+10` and has leader `v mod n` (round robin, so every
party leads exactly one view). Phases (`j = r mod 11`; `P` = party role, `L` = leader role; a
message from `p` to `q` carries the party-role component for `q` = leader and the leader-role
component for `p` = leader; the leader receives its own messages through *self-delivery*):

* `j = 0`: P sends `Complain` if it has no commit; L (without commit) sends `ReqSuggestion`.
* `j = 1`: P answers `ReqSuggestion` with its commit, else its key, else nothing; it is *active*
  in the view iff it has no commit. L with a commit (from before the view) answers complaints.
* `j = 2`: L (running the leader protocol) broadcasts a commit if it knows one; otherwise it
  proposes the highest key suggested (in phase 4); otherwise it broadcasts `RunRetrieval`.
* `j = 3`: active P answers `RunRetrieval` with a partial signature on its retrieval input (both
  values if the input was set to `⊥`). L combines a `(t+1)`-certificate for a value, or sets its
  own retrieval input to `⊥` and stays silent (`RetrievalLeaderSync`).
* `j = 4, 6, 8`: L sends `ProposeKey` / `ProposeLock` / `ProposeCommit`;
  `j = 5, 7, 9`: active P checks and answers with a partial signature (`CheckedKey`, …), updating
  its key (on `ProposeLock`) and lock (on `ProposeCommit`); the key phase checks the lock.
* `j = 10`: L broadcasts the commit (`SendCommit`).
* any round: a valid `SendCommit` sets the commit, which is the decision.

Then (rounds `11n`, `11n+1`, `11n+2`): `HELP` if no commit; `PROOF` replies and `FALLBACK`
certificates (`t+1` help signatures); `LOCK` broadcast by parties with a fallback certificate.
At round `R₀ = 11n+3` stage A ends with the record `Rec` (participate in the fallback?, value).
Stage B runs a black-box BA protocol `Afb` among the participants (others are silent); a party
without commit decides its output (or its value if it does not participate).
-/

namespace Podc.FewToManyFaultsBA.Sync

open Cslib.Byzantine.LockStep Finset

/-- The statements that get signed. -/
inductive Stmt where
  /-- retrieval: "`b` is a valid value" (`tsign(v_in)` in `RetrievalPartySync`) -/
  | inp (b : Bool)
  /-- `CheckedKey` in view `v` -/
  | key (b : Bool) (v : ℕ)
  /-- `CheckedLock` in view `v` -/
  | lock (b : Bool) (v : ℕ)
  /-- `CheckedCommit` in view `v` -/
  | commit (b : Bool) (v : ℕ)
  /-- `HELP` -/
  | help
  deriving DecidableEq

variable (n : ℕ)

/-- A partial signature: signer and statement. -/
abbrev Tok := Fin n × Stmt

/-- A set of partial signatures (a threshold certificate when valid). -/
abbrev Cert := Finset (Tok n)

/-- `c` is a `th`-certificate on `s`: at least `th` tokens, all on `s` (distinct signers). -/
def Valid (th : ℕ) (s : Stmt) (c : Cert n) : Prop := (∀ τ ∈ c, τ.2 = s) ∧ th ≤ c.card

instance (th : ℕ) (s : Stmt) (c : Cert n) : Decidable (Valid n th s c) := by
  unfold Valid; infer_instance

/-- A key / lock / commit proof: value, view, certificate. -/
abbrev Proof := Bool × ℕ × Cert n

/-- Suggestions (`Suggest`). -/
inductive Sugg where
  | none
  | key (c : Proof n)
  | commit (c : Proof n)
  deriving DecidableEq

/-- Justification of a key proposal (`prop`). -/
inductive Justif where
  | combine (c : Cert n)
  | key (v : ℕ) (c : Cert n)
  deriving DecidableEq

/-- Party-role messages (to the leader). -/
inductive PMsg where
  | complain
  | sugg (s : Sugg n)
  | retr (c : Cert n)
  | checked (τ : Tok n)
  deriving DecidableEq

/-- Leader-role messages. -/
inductive LMsg where
  | reqSugg
  | runRetr
  | sendCommit (c : Proof n)
  | proposeKey (b : Bool) (J : Justif n)
  | proposeLock (b : Bool) (c : Cert n)
  | proposeCommit (b : Bool) (c : Cert n)
  deriving DecidableEq

/-- Messages of stage A. -/
inductive Msg where
  | view (pm : Option (PMsg n)) (lm : Option (LMsg n))
  | help (τ : Tok n)
  | stage2 (pr : Option (Proof n)) (fb : Option (Cert n))
  | lock (c : Proof n)
  deriving DecidableEq

variable {n}

/-- Tokens of a suggestion. -/
def Sugg.toks : Sugg n → Cert n
  | .none => ∅
  | .key c => c.2.2
  | .commit c => c.2.2

/-- Tokens of a justification. -/
def Justif.toks : Justif n → Cert n
  | .combine c => c
  | .key _ c => c

/-- Tokens of a party-role message. -/
def PMsg.toks : PMsg n → Cert n
  | .complain => ∅
  | .sugg s => s.toks
  | .retr c => c
  | .checked τ => {τ}

/-- Tokens of a leader-role message. -/
def LMsg.toks : LMsg n → Cert n
  | .reqSugg => ∅
  | .runRetr => ∅
  | .sendCommit c => c.2.2
  | .proposeKey _ J => J.toks
  | .proposeLock _ c => c
  | .proposeCommit _ c => c

/-- Tokens of a message. -/
def Msg.toks : Msg n → Cert n
  | .view pm lm => (pm.map PMsg.toks).getD ∅ ∪ (lm.map LMsg.toks).getD ∅
  | .help τ => {τ}
  | .stage2 pr fb => (pr.map fun c => c.2.2).getD ∅ ∪ fb.getD ∅
  | .lock c => c.2.2

/-- The signature structure of stage A. -/
def auth : Cslib.Byzantine.Auth (Fin n) (Msg n) (Tok n) where
  signer τ := τ.1
  tokens m := ↑m.toks

/-- The leader's plan within a view. -/
inductive Plan (n : ℕ) where
  | idle
  | bcast (c : Proof n)
  | retr
  | propose (b : Bool) (J : Justif n)
  | keyC (b : Bool) (c : Cert n)
  | lockC (b : Bool) (c : Cert n)
  | fin (c : Proof n)
  | silent
  deriving DecidableEq

/-- Local state of a party in stage A. -/
structure St (n : ℕ) where
  /-- retrieval input (`none` = `⊥`) -/
  vin : Option Bool
  key : Option (Proof n)
  lock : Option (Proof n)
  /-- the commit; having one = having decided -/
  commit : Option (Proof n)
  /-- leader: runs the leader protocol in the current view -/
  lead : Bool
  /-- party: had no commit when suggesting in the current view -/
  active : Bool
  plan : Plan n
  /-- statement to sign in the next round -/
  sign : Option Stmt
  /-- the (self-delivery augmented) inbox of the previous round -/
  last : Fin n → Option (Msg n)
  /-- fallback certificate -/
  fb : Option (Cert n)

/-- Initial state with input `x`. -/
def St.init (x : Bool) : St n :=
  ⟨some x, none, none, none, false, false, .idle, none, fun _ => none, none⟩

/-- Parameters: `n` parties, resilience `t`, threshold `k = ⌈(n+t+1)/2⌉`. -/
structure Params (n : ℕ) where
  t : ℕ

/-- The threshold `k = ⌈(n+t+1)/2⌉`. -/
def Params.k (π : Params n) : ℕ := (n + π.t + 2) / 2

/-- Number of rounds of a view. -/
abbrev viewLen : ℕ := 11

variable [NeZero n]

/-- The leader of view `v` (round robin). -/
def leader (v : ℕ) : Fin n := ⟨v % n, Nat.mod_lt _ (NeZero.pos n)⟩

/-! ### Reading inboxes -/

/-- A valid commit carried by a message (`SendCommit` or `PROOF`). -/
def commitOf (k : ℕ) : Msg n → Option (Proof n)
  | .view _ (some (.sendCommit c)) => if Valid n k (.commit c.1 c.2.1) c.2.2 then some c else none
  | .stage2 (some c) _ => if Valid n k (.commit c.1 c.2.1) c.2.2 then some c else none
  | _ => none

/-- A valid commit in an inbox (the first sender in the order of `Fin n`). -/
def inboxCommit (k : ℕ) (ib : Fin n → Option (Msg n)) : Option (Proof n) :=
  (List.finRange n).findSome? fun q => (ib q).bind (commitOf k)

/-- A valid commit suggestion carried by a message. -/
def commitSugg (k : ℕ) : Option (Msg n) → Option (Proof n)
  | some (.view (some (.sugg (.commit c))) _) =>
      if Valid n k (.commit c.1 c.2.1) c.2.2 then some c else none
  | _ => none

/-- A valid key suggestion (from an earlier view `< v`) carried by a message. -/
def keySugg (k v : ℕ) : Option (Msg n) → Option (Proof n)
  | some (.view (some (.sugg (.key c))) _) =>
      if c.2.1 < v ∧ Valid n k (.key c.1 c.2.1) c.2.2 then some c else none
  | _ => none

/-- The valid key suggestions of an inbox. -/
def keyCands (k v : ℕ) (ib : Fin n → Option (Msg n)) : Finset (Proof n) :=
  univ.biUnion fun q => ((keySugg k v (ib q)).map singleton).getD ∅

open Classical in
/-- A valid key suggestion with the highest view (if any). -/
noncomputable def bestKey (k v : ℕ) (ib : Fin n → Option (Msg n)) : Option (Proof n) :=
  if h : (keyCands k v ib).Nonempty then
    some (Classical.choose (exists_max_image (keyCands k v ib) (fun c => c.2.1) h))
  else none

/-- The tokens on `s` in the `Retrieval` answers of an inbox. -/
def retrToks (s : Stmt) (ib : Fin n → Option (Msg n)) : Cert n :=
  univ.biUnion fun q => match ib q with
    | some (.view (some (.retr c)) _) => c.filter (·.2 = s)
    | _ => ∅

/-- The tokens on `s` in the `Checked` answers of an inbox. -/
def checkedToks (s : Stmt) (ib : Fin n → Option (Msg n)) : Cert n :=
  univ.biUnion fun q => match ib q with
    | some (.view (some (.checked τ)) _) => if τ.2 = s then {τ} else ∅
    | _ => ∅

/-- The `HELP` tokens of an inbox. -/
def helpToks (ib : Fin n → Option (Msg n)) : Cert n :=
  univ.biUnion fun q => match ib q with
    | some (.help τ) => if τ.2 = .help then {τ} else ∅
    | _ => ∅

/-- A valid `FALLBACK` certificate received. -/
def inboxFb (t : ℕ) (ib : Fin n → Option (Msg n)) : Option (Cert n) :=
  (List.finRange n).findSome? fun q => match ib q with
    | some (.stage2 _ (some c)) => if Valid n (t + 1) .help c then some c else none
    | _ => none

/-- The fallback certificate a party builds from the `HELP`s it received. -/
def ownFb (t : ℕ) (ib : Fin n → Option (Msg n)) : Option (Cert n) :=
  if t + 1 ≤ (helpToks ib).card then some (helpToks ib) else none

/-- A valid `LOCK` carried by a message. -/
def lockMsg (k : ℕ) : Option (Msg n) → Option (Proof n)
  | some (.lock c) => if Valid n k (.lock c.1 c.2.1) c.2.2 then some c else none
  | _ => none

/-- The valid `LOCK`s of an inbox. -/
def lockCands (k : ℕ) (ib : Fin n → Option (Msg n)) : Finset (Proof n) :=
  univ.biUnion fun q => ((lockMsg k (ib q)).map singleton).getD ∅

open Classical in
/-- A valid received lock with the highest view (if any). -/
noncomputable def bestLock (k : ℕ) (ib : Fin n → Option (Msg n)) : Option (Proof n) :=
  if h : (lockCands k ib).Nonempty then
    some (Classical.choose (exists_max_image (lockCands k ib) (fun c => c.2.1) h))
  else none

/-- The retrieval answer of a party: partial signatures on its retrieval input, on both values
if the input is `⊥`. -/
def retrAnswer (p : Fin n) (vin : Option Bool) : Cert n :=
  match vin with
  | some b => {(p, .inp b)}
  | none => {(p, .inp false), (p, .inp true)}

/-- The key-phase check of a party with lock `lk` (`ViewPartyProtocol`). -/
def lockOK (lk : Option (Proof n)) (J : Justif n) : Bool :=
  match lk, J with
  | none, _ => true
  | some _, .combine _ => false
  | some l, .key v' _ => decide (l.2.1 ≤ v')

/-- Validity of a key justification in view `v`. -/
def Justif.valid (π : Params n) (b : Bool) (v : ℕ) : Justif n → Prop
  | .combine c => Valid n (π.t + 1) (.inp b) c
  | .key v' c => v' < v ∧ Valid n π.k (.key b v') c

instance (π : Params n) (b : Bool) (v : ℕ) (J : Justif n) : Decidable (J.valid π b v) := by
  cases J <;> unfold Justif.valid <;> infer_instance

/-- The proposal received from the leader. -/
def proposalOf : Option (Msg n) → Option (Bool × Justif n)
  | some (.view _ (some (.proposeKey b J))) => some (b, J)
  | _ => none

/-- The `ProposeLock` received from the leader. -/
def proposeLockOf : Option (Msg n) → Option (Bool × Cert n)
  | some (.view _ (some (.proposeLock b c))) => some (b, c)
  | _ => none

/-- The `ProposeCommit` received from the leader. -/
def proposeCommitOf : Option (Msg n) → Option (Bool × Cert n)
  | some (.view _ (some (.proposeCommit b c))) => some (b, c)
  | _ => none

/-- Did the message carry `ReqSuggestion`? -/
def isReqSugg : Option (Msg n) → Bool
  | some (.view _ (some .reqSugg)) => true
  | _ => false

/-- Did the message carry `RunRetrieval`? -/
def isRunRetr : Option (Msg n) → Bool
  | some (.view _ (some .runRetr)) => true
  | _ => false

/-- Did the message carry `Complain`? -/
def isComplain : Option (Msg n) → Bool
  | some (.view (some .complain) _) => true
  | _ => false

/-- Was the message a `HELP`? -/
def isHelp : Option (Msg n) → Bool
  | some (.help _) => true
  | _ => false

/-! ### The local algorithm -/

variable (π : Params n)

open Classical in
/-- The leader's plan after the suggestion phase. -/
noncomputable def leaderPlan (v : ℕ) (st : St n) (ib : Fin n → Option (Msg n)) : Plan n :=
  match st.commit with
  | some c => .bcast c
  | none =>
    match (List.finRange n).findSome? fun q => commitSugg π.k (ib q) with
    | some c => .bcast c
    | none =>
      match bestKey π.k v ib with
      | some c => .propose c.1 (.key c.2.1 c.2.2)
      | none => .retr

/-- The suggestion of a party: its commit, else its key, else nothing. -/
def suggOf (st : St n) : Sugg n :=
  match st.commit, st.key with
  | some c, _ => .commit c
  | none, some c => .key c
  | none, none => .none

/-- The party-role message of `p` in phase `j` of view `v` (to the leader). -/
def partyOut (p : Fin n) (st : St n) (v j : ℕ) : Option (PMsg n) :=
  if j = 0 then (if st.commit.isNone then some .complain else none)
  else if j = 1 then
    (if isReqSugg (st.last (leader v)) then some (.sugg (suggOf st)) else none)
  else if j = 3 then
    (if st.active ∧ isRunRetr (st.last (leader v)) then some (.retr (retrAnswer p st.vin)) else none)
  else if j = 5 ∨ j = 7 ∨ j = 9 then
    (match st.sign with
     | some s => if st.active then some (.checked (p, s)) else none
     | none => none)
  else none

/-- The leader-role message of the leader in phase `j`, to `q`. -/
def leaderOut (st : St n) (j : ℕ) (q : Fin n) : Option (LMsg n) :=
  if j = 0 then (if st.commit.isNone then some .reqSugg else none)
  else if j = 1 then
    (match st.commit with
     | some c => if !st.lead ∧ isComplain (st.last q) then some (.sendCommit c) else none
     | none => none)
  else if j = 2 then
    (match st.plan with
     | .bcast c => some (.sendCommit c)
     | .retr => some .runRetr
     | _ => none)
  else if j = 4 then
    (match st.plan with
     | .propose b J => some (.proposeKey b J)
     | _ => none)
  else if j = 6 then
    (match st.plan with
     | .keyC b c => some (.proposeLock b c)
     | _ => none)
  else if j = 8 then
    (match st.plan with
     | .lockC b c => some (.proposeCommit b c)
     | _ => none)
  else if j = 10 then
    (match st.plan with
     | .fin c => some (.sendCommit c)
     | _ => none)
  else none

/-- Round of the first `HELP` round. -/
abbrev Rh (n : ℕ) : ℕ := 11 * n

/-- Number of rounds of stage A. -/
abbrev R0 (n : ℕ) : ℕ := 11 * n + 3

/-- The message `p` sends to `q` in round `r` of stage A. -/
def out (p : Fin n) (st : St n) (r : ℕ) (q : Fin n) : Option (Msg n) :=
  if r < Rh n then
    let v := r / 11
    let j := r % 11
    let pm := if q = leader v then partyOut p st v j else none
    let lm := if p = leader v then leaderOut st j q else none
    if pm.isNone ∧ lm.isNone then none else some (.view pm lm)
  else if r = Rh n then
    (if st.commit.isNone then some (.help (p, .help)) else none)
  else if r = Rh n + 1 then
    let pr := if isHelp (st.last q) then st.commit else none
    let fb := ownFb π.t st.last
    if pr.isNone ∧ fb.isNone then none else some (.stage2 pr fb)
  else if r = Rh n + 2 then
    (match st.lock with
     | some c => if st.fb.isSome then some (.lock c) else none
     | none => none)
  else none

/-- Phase 0: the leader decides whether it runs the leader protocol. -/
def ph0 (p : Fin n) (st : St n) (v : ℕ) : St n :=
  { st with lead := (decide (p = leader v) && st.commit.isNone), plan := .idle, sign := none }

/-- Phase 1: activity; the leader's plan after the suggestions. -/
noncomputable def ph1 (st : St n) (v : ℕ) (ib : Fin n → Option (Msg n)) : St n :=
  if st.lead then
    match leaderPlan π v st ib with
    | .bcast c =>
      { st with
        active := st.commit.isNone
        plan := .bcast c
        commit := st.commit.or (some c) }
    | pl => { st with active := st.commit.isNone, plan := pl }
  else { st with active := st.commit.isNone }

/-- Phase 3: the leader's retrieval (`RetrievalLeaderSync`). -/
def ph3 (st : St n) (ib : Fin n → Option (Msg n)) : St n :=
  if st.lead ∧ st.plan = .retr then
    (if π.t + 1 ≤ (retrToks (.inp false) ib).card then
      { st with plan := .propose false (.combine (retrToks (.inp false) ib)) }
    else if π.t + 1 ≤ (retrToks (.inp true) ib).card then
      { st with plan := .propose true (.combine (retrToks (.inp true) ib)) }
    else { st with plan := .silent, vin := none })
  else st

/-- The key-phase decision of a party (sign `CheckedKey` or not). -/
def keySign (st : St n) (v : ℕ) (m : Option (Msg n)) : Option Stmt :=
  match proposalOf m with
  | some (b, J) => if st.active ∧ J.valid π b v ∧ lockOK st.lock J then some (.key b v) else none
  | none => none

/-- Phase 4: parties check the key proposal. -/
def ph4 (st : St n) (v : ℕ) (ib : Fin n → Option (Msg n)) : St n :=
  { st with sign := keySign π st v (ib (leader v)) }

/-- Phases 5, 7, 9: the leader aggregates partial signatures. -/
def phAgg (st : St n) (v j : ℕ) (ib : Fin n → Option (Msg n)) : St n :=
  match j, st.plan with
  | 5, .propose b _ =>
      if st.lead then
        (if π.k ≤ (checkedToks (.key b v) ib).card then
          { st with plan := .keyC b (checkedToks (.key b v) ib) }
        else { st with plan := .silent })
      else st
  | 7, .keyC b _ =>
      if st.lead then
        (if π.k ≤ (checkedToks (.lock b v) ib).card then
          { st with plan := .lockC b (checkedToks (.lock b v) ib) }
        else { st with plan := .silent })
      else st
  | 9, .lockC b _ =>
      if st.lead then
        (if π.k ≤ (checkedToks (.commit b v) ib).card then
          { st with
            plan := .fin (b, v, checkedToks (.commit b v) ib)
            commit := st.commit.or (some (b, v, checkedToks (.commit b v) ib)) }
        else { st with plan := .silent })
      else st
  | _, _ => st

/-- Phase 6: parties check the lock proposal and update their key. -/
def ph6 (st : St n) (v : ℕ) (ib : Fin n → Option (Msg n)) : St n :=
  match proposeLockOf (ib (leader v)) with
  | some (b, c) =>
      if st.active ∧ Valid n π.k (.key b v) c then
        { st with key := some (b, v, c), sign := some (.lock b v) }
      else { st with sign := none }
  | none => { st with sign := none }

/-- Phase 8: parties check the commit proposal and update their lock. -/
def ph8 (st : St n) (v : ℕ) (ib : Fin n → Option (Msg n)) : St n :=
  match proposeCommitOf (ib (leader v)) with
  | some (b, c) =>
      if st.active ∧ Valid n π.k (.lock b v) c then
        { st with lock := some (b, v, c), sign := some (.commit b v) }
      else { st with sign := none }
  | none => { st with sign := none }

/-- View-phase transition of `p` on the (augmented) inbox `ib` of round `r = 11v + j`. -/
noncomputable def viewTrans (p : Fin n) (st : St n) (v j : ℕ) (ib : Fin n → Option (Msg n)) :
    St n :=
  match j with
  | 0 => ph0 p st v
  | 1 => ph1 π st v ib
  | 3 => ph3 π st ib
  | 4 => ph4 π st v ib
  | 5 => phAgg π st v 5 ib
  | 6 => ph6 π st v ib
  | 7 => phAgg π st v 7 ib
  | 8 => ph8 π st v ib
  | 9 => phAgg π st v 9 ib
  | _ => st

/-- Transition of `p` on the augmented inbox `ib` of round `r`: phase-specific update, then
acceptance of a valid commit (`SendCommit`/`PROOF`), then recording the inbox. -/
noncomputable def trans (p : Fin n) (st : St n) (r : ℕ) (ib : Fin n → Option (Msg n)) : St n :=
  let st₁ :=
    if r < Rh n then viewTrans π p st (r / 11) (r % 11) ib
    else if r = Rh n + 1 then { st with fb := (ownFb π.t st.last).or (inboxFb π.t ib) }
    else st
  let st₂ := if r < R0 n then { st₁ with commit := st₁.commit.or (inboxCommit π.k ib) } else st₁
  { st₂ with last := ib }

/-- One step: transition on the inbox augmented by the party's own message to itself. -/
noncomputable def step (p : Fin n) (st : St n) (r : ℕ) (ib : Fin n → Option (Msg n)) : St n :=
  trans π p st r (fun q => if q = p then out π p st r p else ib q)

/-- The state of `p` with input `x` after the history `h`. -/
noncomputable def stateOf (p : Fin n) (x : Bool) (h : History (Fin n) (Msg n)) : St n :=
  (h.foldl (fun (sr : St n × ℕ) ib => (step π p sr.1 sr.2 ib, sr.2 + 1)) (St.init x, 0)).1

/-- The record handed to stage B: participate in the fallback?, and the value. -/
structure Rec where
  part : Bool
  value : Bool

/-- The value of a party at the end of stage A (`SyncBA`, lines 25–31): its commit value, else
the highest valid lock received, else its input. -/
noncomputable def finalValue (st : St n) (x : Bool) : Bool :=
  match st.commit with
  | some c => c.1
  | none => match bestLock π.k st.last with
    | some c => c.1
    | none => x

/-- Stage A as a lock-step protocol; it "decides" its record at round `R₀`. -/
noncomputable def stageA : Protocol (Fin n) Bool (Msg n) Rec where
  send p x h q := if h.length < R0 n then out π p (stateOf π p x h) h.length q else none
  decide p x h := if h.length = R0 n then
    some ⟨(stateOf π p x h).fb.isSome, finalValue π (stateOf π p x h) x⟩ else none

/-- Stage B: the fallback protocol run by the participants (input `some v`); non-participants
(input `none`) are silent. -/
def stageB {Mf : Type} (Afb : Protocol (Fin n) Bool Mf Bool) :
    Protocol (Fin n) (Option Bool) Mf Bool where
  send p x h q := match x with
    | some v => Afb.send p v h q
    | none => none
  decide p x h := match x with
    | some v => Afb.decide p v h
    | none => none

/-- Input of stage B computed from the record. -/
def toB (_ : Fin n) (_ : Bool) : Option Rec → Option Bool
  | some r => if r.part then some r.value else none
  | none => none

/-- **`SyncBA`**: stage A for `R₀ = 11n+3` rounds, then the fallback `Afb` among the parties
holding a fallback certificate. A party decides its commit value as soon as it has a commit
(stage A); otherwise, at the end of stage A, the output of `Afb` if it participates, else its
value. -/
noncomputable def syncBA {Mf : Type} (Afb : Protocol (Fin n) Bool Mf Bool) :
    Protocol (Fin n) Bool (Msg n ⊕ Mf) Bool where
  send := ((stageA π).seq (R0 n) toB (stageB Afb)).send
  decide p x h :=
    let st := stateOf π p x (histL (h.take (R0 n)))
    match st.commit with
    | some c => some c.1
    | none =>
      if h.length < R0 n then none
      else if st.fb.isSome then Afb.decide p (finalValue π st x) (histR (h.drop (R0 n)))
      else some (finalValue π st x)

end Podc.FewToManyFaultsBA.Sync
