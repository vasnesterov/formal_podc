import Papers.PODC2022.AdaptiveBAFewerWords.Basic

/-!
# Algorithms 3 and 4 of [CKS22] (adaptive weak BA): an executable lock-step model

[CKS22] S. Cohen, I. Keidar, A. Spiegelman. *Make Every Word Count: Adaptive Byzantine Agreement
with Fewer Words.* PODC 2022; full version arXiv:2202.09123v2 (Algorithms 3, 4 and Appendix B).

**Processes and adversary.** Processes are `Fin n`; the phase-`j` leader is `p_{j mod n}`
(`leader n j`, index `j % n`). The adversary corrupts a set `F` (static: the protocol is
deterministic, so an adaptive adversary is simulated by corrupting the final faulty set from the
start and letting these processes follow the protocol until their "corruption"). Byzantine processes
send arbitrary messages, subject to unforgeability (`AdvValid`).

**Phases (Algorithm 4).** A phase has 5 lock-step rounds; all of its messages are leader-to-all or
all-to-leader, so the adversary's messages are given per phase and per correct counterpart:
`prop`, `com`, `fin` (a Byzantine leader's messages of rounds 1, 3, 5 to a correct process) and
`reply`, `dec` (a Byzantine process's messages of rounds 2 and 4 to a correct leader).
A commit certificate `QC_commit(v)` of level `ℓ` is the pair `⟨v, ℓ⟩ : Cert V` (its level is the
phase whose votes it batches, so "`level_commit` is valid according to `QC_commit(v)`" holds by
construction); the finalize certificate of phase `j` on `v` is `⟨v, j⟩` as well.

**Signatures** are ideal: a Byzantine process may send a certificate only if enough signatures on
its content are *available*, i.e. signed by a Byzantine process or sent by a correct process
(eavesdropping, rushing adversary): `q = ⌈(n+t+1)/2⌉` votes `⟨vote, v, ℓ⟩` for `QC_commit`,
`q` messages `⟨decide, v, j⟩` for `QC_finalized`, `t + 1` `help_req` signatures for `QC_fallback`.

**After the phases (Algorithm 3, lines 5–29)** we use one lock-step round per paper round:
undecided correct processes broadcast `help_req` (H1); decided ones answer, and every process that
receives `t + 1` help requests forms and broadcasts a fallback certificate (H2, lines 9–12; we call
it a *former*); undecided processes accept a valid `help` answer (H3). The fallback window and the
black box `A_fallback`: if a fallback certificate reaches a correct process, all correct processes
run `A_fallback` (Lemma 17, by the echo of line 22) on their `bu_decision`; its common output
`fbOut` is chosen by the adversary subject to the black-box specification *strong unanimity*
(`Admissible`). During the window an undecided process adopts a value carried with a valid proof by
a fallback message (`adoptOf`): from formers (line 11; `proof` is read as `decide_proof`) or from
Byzantine processes (possibly relayed by correct echoers). Correct echoers that never adopted carry
`bu_proof = ⊥`, so they add no proof. Among several adoptable values we take a fixed one (the
adversary would control the order; fixing it only restricts the adversary).

**Readings.** `Params.intendedBu`: `false` is the printed line 15 (`bu_decision ← decision`, i.e.
`undecided` for undecided processes); `true` is the reading of the proof of Lemma 22
(`bu_decision` stays the input `v_i` unless decided). `Params.guard`: `true` = a correct leader acts
in rounds 3 and 5 only if it proposed in round 1 (the text: "if the leader decides not to send the
initial message then no messages will be sent by correct processes in this phase"); `false` = the
printed pseudocode (lines 37 and 48 are unguarded). `Params.K` is the number of phases: `t + 1` in
the printed line 1, `n` in the text. `Params.voteOnce`: line 33 says a process votes for a proposal
"for the first time"; `false` reads it per phase (a process votes for the first proposal it gets in
the phase, as in the proof of Lemma 16), `true` as "at most one vote in the whole run".
-/

namespace Podc.AdaptiveBAFewerWords.WeakBA

open Finset

/-- A certificate: `QC_commit(val)` of level `lvl`, or `QC_finalized(val)` of phase `lvl`. -/
structure Cert (V : Type) where
  /-- The certified value. -/
  val : V
  /-- The level / phase of the certificate. -/
  lvl : ℕ
  deriving DecidableEq

/-- A round-2 answer to a proposal: a vote (line 34) or the current commit (line 36). -/
inductive Reply (V : Type) where
  /-- `⟨vote, v, j⟩`. -/
  | vote (v : V)
  /-- `⟨commit, commit, commit_proof, commit_level, j⟩`. -/
  | commit (c : Cert V)
  deriving DecidableEq

/-- Local state of a process between phases. -/
structure St (V : Type) where
  /-- The input `v_i`. -/
  inp : V
  /-- `decision` of Algorithm 3 (`none` = `undecided`). -/
  decision : Option V
  /-- `decide_proof` (overwritten by every received finalize certificate, line 54 and line 2). -/
  dproof : Option (Cert V)
  /-- `commit`, `commit_proof` and `commit_level` (the level of the certificate). -/
  commit : Option (Cert V)
  /-- Whether the process has ever voted (used only by the `voteOnce` reading of line 33). -/
  voted : Bool
  deriving DecidableEq

variable {n : ℕ} {V : Type} [DecidableEq V]

/-- `commit_level` (`0` if `commit = ⊥`). -/
def St.level (s : St V) : ℕ :=
  match s.commit with
  | some c => c.lvl
  | none => 0

/-- Protocol parameters. -/
structure Params (V : Type) where
  /-- The resilience `t` (`n = 2t + 1`). -/
  t : ℕ
  /-- The number of phases of line 1. -/
  K : ℕ
  /-- The external predicate `validate`. -/
  valid : V → Bool
  /-- `true`: `bu_decision` is the input unless decided (proof of Lemma 22); `false`: line 15. -/
  intendedBu : Bool
  /-- `true`: a correct leader acts in rounds 3 and 5 only if it proposed. -/
  guard : Bool
  /-- Reading of "for the first time" at line 33: `false` = the first proposal of the phase
  (a process may vote once per phase); `true` = a process votes at most once in the whole run. -/
  voteOnce : Bool

/-- The adversary: Byzantine set, inputs, and all messages of Byzantine processes to correct ones. -/
structure Adv (n : ℕ) (V : Type) where
  /-- Byzantine processes. -/
  F : Finset (Fin n)
  /-- Inputs. -/
  inp : Fin n → V
  /-- Round 1 of phase `j`: proposal of a Byzantine leader to `q`. -/
  prop : ℕ → Fin n → Option V
  /-- Round 3 of phase `j`: commit certificate of a Byzantine leader to `q`. -/
  com : ℕ → Fin n → Option (Cert V)
  /-- Round 5 of phase `j`: finalize certificate (on a value) of a Byzantine leader to `q`. -/
  fin : ℕ → Fin n → Option V
  /-- Round 2 of phase `j`: answer of Byzantine `b` to a correct leader. -/
  reply : ℕ → Fin n → Option (Reply V)
  /-- Round 4 of phase `j`: decide message of Byzantine `b` to a correct leader. -/
  dec : ℕ → Fin n → Option V
  /-- H1: Byzantine `b` sends `help_req` to `q`. -/
  helpReq : Fin n → Fin n → Bool
  /-- H2: Byzantine `b` answers `q` with `⟨help, c.val, c⟩` (`c` a finalize certificate). -/
  help : Fin n → Fin n → Option (Cert V)
  /-- Window: Byzantine `b` sends `q` a fallback message, with an optional decide proof. -/
  fbMsg : Fin n → Fin n → Option (Option (Cert V))
  /-- The common output of `A_fallback`. -/
  fbOut : Option V

variable (P : Params V) (A : Adv n V)

/-- The leader `p_{j mod n}` of phase `j`. -/
def leader (n : ℕ) [NeZero n] (j : ℕ) : Fin n := ⟨j % n, Nat.mod_lt _ (NeZero.pos n)⟩

/-- The certificate of maximal level in a list (the first one among equals). -/
def maxCert : List (Cert V) → Option (Cert V)
  | [] => none
  | c :: cs =>
    match maxCert cs with
    | none => some c
    | some d => if d.lvl ≤ c.lvl then some c else some d

section Phase

variable [NeZero n] (j : ℕ) (s : Fin n → St V)

/-- The correct leader proposes (line 31): it has not decided. -/
def proposes : Bool := (s (leader n j)).decision.isNone

/-- Round 1: the proposal received by `q`. -/
def propRcv (q : Fin n) : Option V :=
  if leader n j ∈ A.F then A.prop j q
  else if proposes j s then some (s (leader n j)).inp else none

/-- Round 2: the answer of a correct `q` (lines 33–36). -/
def replyOf (q : Fin n) : Option (Reply V) :=
  match propRcv A j s q with
  | none => none
  | some v =>
    match (s q).commit with
    | none =>
      if P.valid v ∧ (P.voteOnce = false ∨ (s q).voted = false) then some (.vote v) else none
    | some c => some (.commit c)

/-- Round 2: the answer of `p` as received by the leader. -/
def replyRcv (p : Fin n) : Option (Reply V) :=
  if p ∈ A.F then A.reply j p else replyOf P A j s p

/-- Commit messages received by the leader. -/
def commitsRcv : List (Cert V) :=
  (List.finRange n).filterMap fun p =>
    match replyRcv P A j s p with
    | some (.commit c) => some c
    | _ => none

/-- Votes received by the leader. -/
def votesRcv : List V :=
  (List.finRange n).filterMap fun p =>
    match replyRcv P A j s p with
    | some (.vote v) => some v
    | _ => none

/-- Round 3 of a correct leader (lines 37–42). -/
def leaderCert : Option (Cert V) :=
  if P.guard ∧ proposes j s = false then none else
  match maxCert (commitsRcv P A j s) with
  | some c => some c
  | none =>
    ((votesRcv P A j s).find? fun v => decide (quorum n P.t ≤ (votesRcv P A j s).count v)).map
      fun v => ⟨v, j⟩

/-- Round 3: the commit certificate received by `q`. -/
def comRcv (q : Fin n) : Option (Cert V) :=
  if leader n j ∈ A.F then A.com j q else leaderCert P A j s

/-- Round 4: the decide message of a correct `q` (line 43–44). -/
def decOf (q : Fin n) : Option V :=
  match comRcv P A j s q with
  | some c => if (s q).level ≤ c.lvl then some c.val else none
  | none => none

/-- Round 4: the decide message of `p` as received by the leader. -/
def decRcv (p : Fin n) : Option V :=
  if p ∈ A.F then A.dec j p else decOf P A j s p

/-- Decide messages received by the leader. -/
def decsRcv : List V := (List.finRange n).filterMap (decRcv P A j s)

/-- Round 5 of a correct leader (lines 48–51). -/
def leaderFin : Option V :=
  if P.guard ∧ proposes j s = false then none else
  (decsRcv P A j s).find? fun v => decide (quorum n P.t ≤ (decsRcv P A j s).count v)

/-- Round 5: the finalize certificate (value) received by `q`. -/
def finRcv (q : Fin n) : Option V :=
  if leader n j ∈ A.F then A.fin j q else leaderFin P A j s

/-- The state after phase `j` (Algorithm 4 and lines 2–4 of Algorithm 3). -/
def step (q : Fin n) : St V where
  inp := (s q).inp
  decision :=
    match (s q).decision with
    | some v => some v
    | none => finRcv P A j s q
  dproof :=
    match finRcv P A j s q with
    | some v => some ⟨v, j⟩
    | none => (s q).dproof
  commit :=
    match decOf P A j s q with
    | some _ => comRcv P A j s q
    | none => (s q).commit
  voted :=
    match replyOf P A j s q with
    | some (.vote _) => true
    | _ => (s q).voted

end Phase

variable [NeZero n]

/-- Initial states. -/
def init : Fin n → St V := fun q => ⟨A.inp q, none, none, none, false⟩

/-- States after `j` phases. -/
def stateAt : ℕ → Fin n → St V
  | 0 => init A
  | j + 1 => step P A (j + 1) (stateAt j)

/-- Processes that signed `⟨vote, v, j⟩`: Byzantine ones, and correct ones that voted for `v` in
phase `j`. -/
def voteSigners (j : ℕ) (v : V) : Finset (Fin n) :=
  univ.filter fun p => p ∈ A.F ∨ replyOf P A j (stateAt P A (j - 1)) p = some (.vote v)

/-- Processes that signed `⟨decide, v, j⟩`. -/
def decideSigners (j : ℕ) (v : V) : Finset (Fin n) :=
  univ.filter fun p => p ∈ A.F ∨ decOf P A j (stateAt P A (j - 1)) p = some v

/-- `QC_commit(c.val)` of level `c.lvl` can be formed by the adversary in phase `j`. -/
def CommitAvail (c : Cert V) (j : ℕ) : Prop :=
  1 ≤ c.lvl ∧ c.lvl ≤ j ∧ quorum n P.t ≤ (voteSigners P A c.lvl c.val).card

/-- `QC_finalized(c.val)` of phase `c.lvl` can be formed by the adversary in phase `j`. -/
def FinAvail (c : Cert V) (j : ℕ) : Prop :=
  1 ≤ c.lvl ∧ c.lvl ≤ j ∧ quorum n P.t ≤ (decideSigners P A c.lvl c.val).card

instance (c : Cert V) (j : ℕ) : Decidable (CommitAvail P A c j) := by
  unfold CommitAvail; infer_instance

instance (c : Cert V) (j : ℕ) : Decidable (FinAvail P A c j) := by
  unfold FinAvail; infer_instance

/-- States after all phases. -/
def phases : Fin n → St V := stateAt P A P.K

/-- Decision after the phases (line 4). -/
def dAfter (q : Fin n) : Option V := (phases P A q).decision

/-- H1: `p` sends `help_req` to `q` (line 6). -/
def helpReqFrom (p q : Fin n) : Bool := if p ∈ A.F then A.helpReq p q else (dAfter P A p).isNone

/-- Line 9: `q` receives `t + 1` help requests and forms a fallback certificate. -/
def Former (q : Fin n) : Prop := P.t + 1 ≤ (univ.filter fun p => helpReqFrom P A p q).card

instance (q : Fin n) : Decidable (Former P A q) := by unfold Former; infer_instance

/-- `QC_fallback` can be formed by the adversary. -/
def FbCertAvail : Prop := P.t + 1 ≤ (univ.filter fun p => p ∈ A.F ∨ (dAfter P A p).isNone).card

instance : Decidable (FbCertAvail P A) := by unfold FbCertAvail; infer_instance

/-- The help answer of a correct decided `p` (line 8) is valid (line 13): its proof is for its
decision. -/
def helpOk (p : Fin n) : Option V :=
  match dAfter P A p, (phases P A p).dproof with
  | some v, some c => if c.val = v then some v else none
  | _, _ => none

/-- H3: the values of valid help answers received by an undecided correct `q`. -/
def helpVals (q : Fin n) : List V :=
  ((List.finRange n).filterMap fun p =>
    if p ∈ A.F then (A.help p q).map Cert.val else helpOk P A p).filter fun v => P.valid v

/-- Decision after line 14. -/
def dH3 (q : Fin n) : Option V :=
  match dAfter P A q with
  | some v => some v
  | none => (helpVals P A q).head?

/-- Some correct process runs the fallback: it formed a certificate or received one. -/
def FbRuns : Prop :=
  (∃ q, q ∉ A.F ∧ Former P A q) ∨ ∃ b ∈ A.F, ∃ q, q ∉ A.F ∧ (A.fbMsg b q).isSome

instance : Decidable (FbRuns P A) := by unfold FbRuns; infer_instance

/-- Values carried with a valid proof by fallback messages: formers' decisions (line 11) and
Byzantine messages (relayed by echoers). -/
def adoptVals : List V :=
  ((List.finRange n).filterMap fun r =>
    if r ∈ A.F then none
    else if decide (Former P A r) then helpOk P A r else none) ++
  ((List.finRange n).flatMap fun b => (List.finRange n).filterMap fun r =>
    if b ∈ A.F ∧ r ∉ A.F then
      match A.fbMsg b r with
      | some (some c) => some c.val
      | _ => none
    else none)

/-- The value adopted during the window (lines 17–20) by an undecided process. -/
def adoptOf : Option V := ((adoptVals P A).filter fun v => P.valid v).head?

/-- `bu_decision` at the start of `A_fallback`. -/
def bu (q : Fin n) : Option V :=
  match dH3 P A q with
  | some v => some v
  | none =>
    match adoptOf P A with
    | some v => some v
    | none => if P.intendedBu then some (A.inp q) else none

/-- The outcome of Algorithm 3: `some d` = decided `d` (`d = none` is `⊥`), `none` = never decides. -/
def outcome (q : Fin n) : Option (Option V) :=
  match dH3 P A q with
  | some v => some (some v)
  | none =>
    if FbRuns P A then
      some (match A.fbOut with
        | some v => if P.valid v then some v else none
        | none => none)
    else none

/-- Unforgeability: Byzantine processes only send certificates they can form. -/
structure AdvValid : Prop where
  card_F : A.F.card ≤ P.t
  com : ∀ j, 1 ≤ j → j ≤ P.K → leader n j ∈ A.F → ∀ q c, A.com j q = some c → CommitAvail P A c j
  fin : ∀ j, 1 ≤ j → j ≤ P.K → leader n j ∈ A.F → ∀ q v, A.fin j q = some v → FinAvail P A ⟨v, j⟩ j
  reply : ∀ j, 1 ≤ j → j ≤ P.K → ∀ b c, A.reply j b = some (.commit c) → CommitAvail P A c j
  help : ∀ b q c, A.help b q = some c → FinAvail P A c P.K
  fbMsg : ∀ b q m, A.fbMsg b q = some m → FbCertAvail P A
  fbProof : ∀ b q c, A.fbMsg b q = some (some c) → FinAvail P A c P.K

/-- The black box `A_fallback` is a strong BA: if all correct processes run it with the same input,
that is the output. -/
def Admissible : Prop :=
  ∀ x, (∀ q, q ∉ A.F → bu P A q = x) → FbRuns P A → A.fbOut = x

end Podc.AdaptiveBAFewerWords.WeakBA
