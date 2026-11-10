import Papers.PODC2022.AdaptiveBAFewerWords.Basic

/-!
# Algorithms 1 and 2 of [CKS22]: Byzantine Broadcast from weak BA (executable model)

[CKS22] S. Cohen, I. Keidar, A. Spiegelman. *Make Every Word Count: Adaptive Byzantine Agreement with
Fewer Words.* PODC 2022; full version arXiv:2202.09123v2, Section 5 and Appendix A.

This file is an executable lock-step model of the first two parts of Algorithm 1 (round 1 and the
`n` "vetting" phases of Algorithm 2). The third part (the weak BA, line 9) is a black box, see
`BBCorrect.lean`.

## Model

* Processes `Fin n` (process `p_k` of the paper is `k`, so the leader `p_{j mod n}` of phase `j` is
  `j % n`, `ldr`), a designated `sender`, a static set `F` of Byzantine processes. Synchronous
  lock-step rounds; a message sent in a round is received in the same round; a broadcast includes
  the broadcaster itself.
* Adaptive corruption reduces to static corruption here: the protocol is deterministic, so an
  adaptive adversary can be simulated by corrupting its final faulty set from the start and letting
  these processes follow the protocol until the original corruption time. All theorems quantify
  over all Byzantine behaviours, so they cover this.
* Global round `0` is round 1 of Algorithm 1; phase `j ∈ [1, n]` occupies the global rounds
  `3j - 2, 3j - 1, 3j` (its rounds 1, 2, 3).
* Signatures and threshold signatures are ideal and *symbolic*: `Item.signed s v` is `⟨v⟩_s`,
  `Item.qc j` the idk certificate `QC_idk(j)` (a `(t+1, n)`-threshold signature on `⟨idk, j⟩`),
  `Msg.idk p j` the signature share `⟨idk, j⟩_p`. Every message is one word.
* Unforgeability is a validity condition on the adversary (`AdvValid`): a Byzantine process may send
  `⟨v⟩_s` of a correct `s` only if `s` is the sender and `v` its input (correct non-senders never
  sign values), `⟨idk, j⟩_p` of a correct `p` only if `p` has sent it (in this or an earlier round:
  rushing, eavesdropping adversary), and `QC_idk(j)` only if `t + 1` distinct `⟨idk, j⟩` shares are
  available in that sense.
* Correct processes run Algorithm 2 (`reqH`, `repH`, `relH`, `ret`); their states are computed from
  the Byzantine messages (`vPh j` = the vector of the values `v_i` after `j` phases). The paper's
  `BB_valid(v)` ("signed by the sender or by `t + 1` processes") is read as "a sender-signed value or
  an idk certificate" (`bbValid`).
* The leader's relay rule (line 23) is a parameter `Rule`: `printed` relays only a sender-signed
  value `v' = ⟨v⟩_sender` (as in the paper), `fixed` relays any `BB_valid` value.
* A correct leader executes round 3 (lines 22-27) only in a non-silent phase, i.e. if it has sent the
  help request (otherwise it would broadcast unsolicited values sent to it by Byzantine processes,
  contradicting "no messages will be sent by correct processes in this phase" of Section 5).
-/

namespace Podc.AdaptiveBAFewerWords.BB

/-- Signed values and certificates. -/
inductive Item (n : ℕ) (V : Type) where
  /-- `⟨v⟩_s`: the value `v` signed by `s`. -/
  | signed (s : Fin n) (v : V)
  /-- `QC_idk(j)`: the threshold signature of `t + 1` shares `⟨idk, j⟩`. -/
  | qc (j : ℕ)
  deriving DecidableEq

/-- Messages of Algorithms 1 and 2 (each is one word). -/
inductive Msg (n : ℕ) (V : Type) where
  /-- Round 1 of Algorithm 1: `⟨v_sender⟩_sender`. -/
  | init (x : Item n V)
  /-- `⟨help_req, j⟩_leader` (line 16). -/
  | helpReq (j : ℕ)
  /-- `⟨v_i, j⟩` (line 19). -/
  | reply (x : Item n V) (j : ℕ)
  /-- `⟨idk, j⟩_p` (line 21). -/
  | idk (p : Fin n) (j : ℕ)
  /-- `⟨v, j⟩` broadcast by the leader (lines 24, 27). -/
  | relay (x : Item n V) (j : ℕ)
  deriving DecidableEq

/-- The leader's relay rule at line 23. -/
inductive Rule where
  /-- As printed: relay a received `⟨v', j⟩` only if `v' = ⟨v⟩_sender`. -/
  | printed
  /-- Repaired: relay a received `⟨v', j⟩` if `BB_valid(v')`. -/
  | fixed
  deriving DecidableEq

/-- The adversary's data: Byzantine set, sender, sender's input, Byzantine messages
(`adv r b w` = messages sent by `b` to `w` in global round `r`). -/
structure Scenario (n : ℕ) (V : Type) where
  /-- The Byzantine processes. -/
  F : Finset (Fin n)
  /-- The designated sender. -/
  sender : Fin n
  /-- The sender's input `v_sender`. -/
  inp : V
  /-- Messages of Byzantine processes. -/
  adv : ℕ → Fin n → Fin n → List (Msg n V)

variable {n : ℕ} {V : Type} [DecidableEq V]

/-- `BB_valid(v)`: `v` is signed by the sender, or it is an idk certificate (signed by `t + 1`
processes). -/
def bbValid (sender : Fin n) : Item n V → Bool
  | .signed s _ => decide (s = sender)
  | .qc _ => true

/-- Which values a correct leader relays at line 23. -/
def relayable (rule : Rule) (sender : Fin n) (x : Item n V) : Bool :=
  match rule with
  | .printed => match x with
    | .signed s _ => decide (s = sender)
    | .qc _ => false
  | .fixed => bbValid sender x

/-- The BB decision at lines 10-13 from the weak BA decision: `⟨v⟩_sender ↦ v`, anything else
(including `⊥`) `↦ ⊥`. -/
def bbOut (sender : Fin n) : Option (Item n V) → Option V
  | some (.signed s v) => if s = sender then some v else none
  | _ => none

/-- Values `x` of messages `⟨x, j⟩` (line 19) with `relayable x`. -/
def replyVals (rule : Rule) (sender : Fin n) (j : ℕ) (ms : List (Msg n V)) : List (Item n V) :=
  ms.filterMap fun
    | .reply x j' => if j' = j ∧ relayable rule sender x = true then some x else none
    | _ => none

/-- Distinct signers of `⟨idk, j⟩` among `ms`. -/
def idkSigners (j : ℕ) (ms : List (Msg n V)) : List (Fin n) :=
  (ms.filterMap fun
    | .idk p j' => if j' = j then some p else none
    | _ => none).dedup

/-- Lines 23-27: what the leader broadcasts given the messages `ms` received in round 2 of
phase `j`. -/
def pick (t : ℕ) (rule : Rule) (sender : Fin n) (j : ℕ) (ms : List (Msg n V)) :
    Option (Item n V) :=
  match (replyVals rule sender j ms).head? with
  | some x => some x
  | none => if t + 1 ≤ (idkSigners j ms).length then some (.qc j) else none

/-- Line 28: the `BB_valid` values `v` of messages `⟨v, j⟩` among `ms`. -/
def relayVals (sender : Fin n) (j : ℕ) (ms : List (Msg n V)) : List (Item n V) :=
  ms.filterMap fun
    | .relay x j' => if j' = j ∧ bbValid sender x = true then some x else none
    | _ => none

/-- Line 3: the sender-signed values `⟨v⟩_sender` among `ms`. -/
def initVals (sender : Fin n) (ms : List (Msg n V)) : List (Item n V) :=
  ms.filterMap fun
    | .init (.signed s v) => if s = sender then some (.signed s v) else none
    | _ => none

section protocol
variable [NeZero n] (t : ℕ) (rule : Rule) (sc : Scenario n V)

/-- The leader `p_{j mod n}` of phase `j` (line 14). -/
def ldr (j : ℕ) : Fin n := ⟨j % n, Nat.mod_lt _ (NeZero.pos n)⟩

/-- Round 1 of Algorithm 1 (lines 1-2), correct process `u` to `w`. -/
def initH (u _w : Fin n) : List (Msg n V) :=
  if u = sc.sender then [.init (.signed sc.sender sc.inp)] else []

/-- Messages sent in round 1 of Algorithm 1. -/
def out0 (u w : Fin n) : List (Msg n V) :=
  if u ∈ sc.F then sc.adv 0 u w else initH sc u w

/-- The value `v_i` after round 1 (lines 3-4): the first `⟨v⟩_sender` received from the sender. -/
def v0 (w : Fin n) : Option (Item n V) :=
  (initVals sc.sender (out0 sc sc.sender w)).head?

/-- Round 1 of phase `j` (lines 15-16), correct `u` to `w`, given the phase-start values `v`. -/
def reqH (j : ℕ) (v : Fin n → Option (Item n V)) (u _w : Fin n) : List (Msg n V) :=
  if u = ldr j ∧ v u = none then [.helpReq j] else []

/-- Messages sent in round 1 of phase `j` (global round `3j - 2`). -/
def reqOut (j : ℕ) (v : Fin n → Option (Item n V)) (u w : Fin n) : List (Msg n V) :=
  if u ∈ sc.F then sc.adv (3 * j - 2) u w else reqH j v u w

/-- The answer of `u` to a help request (lines 18-21). -/
def answer (j : ℕ) (u : Fin n) : Option (Item n V) → Msg n V
  | some x => .reply x j
  | none => .idk u j

/-- Round 2 of phase `j` (lines 17-21), correct `u` to `w`. -/
def repH (j : ℕ) (v : Fin n → Option (Item n V)) (u w : Fin n) : List (Msg n V) :=
  if w = ldr j ∧ Msg.helpReq j ∈ reqOut sc j v (ldr j) u then [answer j u (v u)] else []

/-- Messages sent in round 2 of phase `j` (global round `3j - 1`). -/
def repOut (j : ℕ) (v : Fin n → Option (Item n V)) (u w : Fin n) : List (Msg n V) :=
  if u ∈ sc.F then sc.adv (3 * j - 1) u w else repH sc j v u w

/-- What the leader receives in round 2 of phase `j`. -/
def inboxRep (j : ℕ) (v : Fin n → Option (Item n V)) : List (Msg n V) :=
  (List.finRange n).flatMap fun s => repOut sc j v s (ldr j)

/-- Round 3 of phase `j` (lines 22-27), correct `u` to `w`; only the leader of a non-silent phase
sends. -/
def relH (j : ℕ) (v : Fin n → Option (Item n V)) (u _w : Fin n) : List (Msg n V) :=
  if u = ldr j ∧ v u = none then
    ((pick t rule sc.sender j (inboxRep sc j v)).map fun x => Msg.relay x j).toList
  else []

/-- Messages sent in round 3 of phase `j` (global round `3j`). -/
def relOut (j : ℕ) (v : Fin n → Option (Item n V)) (u w : Fin n) : List (Msg n V) :=
  if u ∈ sc.F then sc.adv (3 * j) u w else relH t rule sc j v u w

/-- The return value of `invokePhase(j, v_w)` (lines 28-31). -/
def ret (j : ℕ) (v : Fin n → Option (Item n V)) (w : Fin n) : Option (Item n V) :=
  (relayVals sc.sender j (relOut t rule sc j v (ldr j) w)).head?

/-- Lines 6-8: `v_w ← val` if `val ≠ ⊥`. -/
def step (j : ℕ) (v : Fin n → Option (Item n V)) (w : Fin n) : Option (Item n V) :=
  (ret t rule sc j v w).or (v w)

/-- The values `v_i` after round 1 and `j` phases. -/
def vPh : ℕ → Fin n → Option (Item n V)
  | 0 => v0 sc
  | j + 1 => step t rule sc (j + 1) (vPh j)

/-- The input of `w` to the weak BA (line 9). -/
def vEnd (w : Fin n) : Option (Item n V) := vPh t rule sc n w

/-- What correct `u` sends to `w` in global round `r`. -/
def honOut (r : ℕ) (u w : Fin n) : List (Msg n V) :=
  if r = 0 then initH sc u w
  else if n < (r + 2) / 3 then []
  else if (r + 2) % 3 = 0 then reqH ((r + 2) / 3) (vPh t rule sc ((r + 2) / 3 - 1)) u w
  else if (r + 2) % 3 = 1 then repH sc ((r + 2) / 3) (vPh t rule sc ((r + 2) / 3 - 1)) u w
  else relH t rule sc ((r + 2) / 3) (vPh t rule sc ((r + 2) / 3 - 1)) u w

/-- `m` was sent (to anybody) by a correct process in some round `≤ r`. -/
def SentByHonest (r : ℕ) (m : Msg n V) : Prop :=
  ∃ r' ≤ r, ∃ u w, u ∉ sc.F ∧ m ∈ honOut t rule sc r' u w

/-- `⟨idk, j⟩_p` is available to the adversary in round `r`. -/
def IdkAvail (r : ℕ) (p : Fin n) (j : ℕ) : Prop :=
  p ∈ sc.F ∨ SentByHonest t rule sc r (.idk p j)

/-- Items the adversary can produce in round `r` (unforgeability). -/
def ItemAvail (r : ℕ) : Item n V → Prop
  | .signed s v => s ∈ sc.F ∨ (s = sc.sender ∧ v = sc.inp)
  | .qc j => ∃ σ : Finset (Fin n), t + 1 ≤ σ.card ∧ ∀ p ∈ σ, IdkAvail t rule sc r p j

/-- Messages the adversary can produce in round `r`. -/
def MsgAvail (r : ℕ) : Msg n V → Prop
  | .init x => ItemAvail t rule sc r x
  | .helpReq _ => True
  | .reply x _ => ItemAvail t rule sc r x
  | .idk p j => IdkAvail t rule sc r p j
  | .relay x _ => ItemAvail t rule sc r x

/-- The adversary respects unforgeability: Byzantine messages to correct processes contain only
available signatures. -/
def AdvValid : Prop :=
  ∀ r b w m, b ∈ sc.F → w ∉ sc.F → m ∈ sc.adv r b w → MsgAvail t rule sc r m

/-- Phase `j` is non-silent: its leader is correct and broadcasts a help request, i.e. it starts the
phase with `v = ⊥`. (Phases with Byzantine leaders are not called silent or non-silent.) -/
def NonSilent (j : ℕ) : Prop :=
  ldr (n := n) j ∉ sc.F ∧ vPh t rule sc (j - 1) (ldr j) = none

instance (j : ℕ) : Decidable (NonSilent t rule sc j) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- Number of messages (= words) sent by correct processes in phase `j` (messages to oneself
included). -/
def phaseWords (j : ℕ) : ℕ :=
  ∑ u ∈ Finset.univ.filter (· ∉ sc.F), ∑ w : Fin n,
    ((reqH j (vPh t rule sc (j - 1)) u w).length +
     (repH sc j (vPh t rule sc (j - 1)) u w).length +
     (relH t rule sc j (vPh t rule sc (j - 1)) u w).length)

/-- Number of messages (= words) sent by correct processes in round 1 and the `n` phases of
Algorithm 1 (lines 1-8). -/
def words : ℕ :=
  ∑ u ∈ Finset.univ.filter (· ∉ sc.F), ∑ w : Fin n, (initH sc u w).length +
    ∑ j ∈ Finset.Icc 1 n, phaseWords t rule sc j

end protocol

end Podc.AdaptiveBAFewerWords.BB
