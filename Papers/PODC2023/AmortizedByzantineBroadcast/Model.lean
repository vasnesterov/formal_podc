import Mathlib

/-!
# Algorithm 4 of [WXMRS23]: linear-communication multi-shot Byzantine broadcast

[WXMRS23] J. Wan, Z. Xiang, A. Momose, L. Ren, E. Shi. *On the Amortized Communication Complexity
of Byzantine Broadcast.* PODC 2023.

This file is an executable lock-step model of Algorithm 4 (honest majority, `f ≤ (1/2 - ε) n`).

* `n` nodes `Fin n`, a static set `F` of Byzantine nodes; lock-step rounds: a message sent in round
  `r` is available to its recipient from round `r + 1` on. Messages to oneself are delivered as well
  (a multicast includes the sender).
* Slot `k ≥ 1` has `f + 2` epochs `0 ≤ i ≤ f + 1` of 11 rounds; epoch `i` of slot `k` starts at
  round `11((k-1)(f+2) + i)` (`roundOf`). The leader of epoch `0` is the slot's sender, the leader
  of epoch `i ≥ 1` is "node `i`", i.e. `Fin` index `i - 1` (`leader`).
* Signatures and threshold signatures are ideal. Items are *symbolic*: `Item.cert k i m` is the
  threshold signature `C_{k,i}(m) = thsig(vote,k,i,m)`, `Item.cproof k i m` the commit-proof
  `thsig(C_{k,i}(m))`, `Item.cpf v` the corrupt-proof `thsig(accuse, v)`, and the signed atoms carry
  their signer. Unforgeability is a validity condition on the adversary (`Scenario.AdvValid`,
  `availAt`): a Byzantine node may send a signed atom only if its signer is Byzantine or an honest
  node has sent that atom (in this or an earlier round: rushing, eavesdropping adversary), and a
  threshold signature only if `n - f` of its shares are available in that sense.
* Honest nodes run `act`, a transcription of the 11 steps and the four `(★)` rules of Algorithm 4.
  The states (`St`: everything received and everything sent, with round tags) are computed from the
  adversary's messages (`exec`).

The paper says that node `u` runs the 11 steps "if it has neither 1) committed in slot `k`, nor 2)
received the corrupt-proof `thsig(accuse, L_i)`", without saying *when* this is checked. Read at every
step, a node holding a commit-proof has committed and never answers queries, which defeats rounds
8–11; the intended reading is presumably that the conditions are evaluated at the start of the epoch.
We keep the three readings as a parameter `Skip` (`epochStart`, `everyStep`, `mixed`); the
consistency proof works for all three, the counterexamples are checked for the relevant ones.
-/

namespace Podc.AmortizedByzantineBroadcast

/-- Signed atoms, threshold signatures and other items exchanged by Algorithm 4. -/
inductive Item (n : ℕ) (V : Type) where
  /-- `⟨prop, k, i, m, C⟩_L`; `c = none` is `C = ⊥`, `c = some j` is `C = C_{k,j}(m)`. -/
  | prop (L : Fin n) (k i : ℕ) (m : V) (c : Option ℕ)
  /-- `⟨vote, k, i, m⟩_u` (a threshold-signature share). -/
  | vote (u : Fin n) (k i : ℕ) (m : V)
  /-- The certificate `C_{k,i}(m) = thsig(vote, k, i, m)`. -/
  | cert (k i : ℕ) (m : V)
  /-- `⟨C_{k,i}(m)⟩_u` (a share of the commit-proof). -/
  | cshare (u : Fin n) (k i : ℕ) (m : V)
  /-- The commit-proof `thsig(C_{k,i}(m))`. -/
  | cproof (k i : ℕ) (m : V)
  /-- `⟨accuse, v⟩_w`: `w` accuses `v`. -/
  | accuse (w v : Fin n)
  /-- The corrupt-proof `thsig(accuse, v)`. -/
  | cpf (v : Fin n)
  /-- `⟨query₁, k, i⟩_u`. -/
  | query1 (u : Fin n) (k i : ℕ)
  /-- `⟨query₂, k, i⟩_u`. -/
  | query2 (u : Fin n) (k i : ℕ)
  deriving DecidableEq

/-- When the skip condition of Algorithm 4 is evaluated. -/
inductive Skip where
  /-- Both conditions are evaluated at the start of the epoch. -/
  | epochStart
  /-- Both conditions are evaluated at every step (the literal reading). -/
  | everyStep
  /-- "Committed" is evaluated at the start of the epoch, the corrupt-proof at every step. -/
  | mixed
  deriving DecidableEq

/-- Protocol parameters: `f`, the expander `G_ε` (adjacency), the senders `S_k` and the
"arbitrary value" an honest leader of an epoch `i > 0` proposes when it holds no certificate. -/
structure Params (n : ℕ) (V : Type) where
  /-- The resilience parameter `f`. -/
  f : ℕ
  /-- The expander graph `G_ε` used in Propagate-1/2. -/
  G : Fin n → Fin n → Bool
  /-- The designated sender `S_k` of slot `k`. -/
  sender : ℕ → Fin n
  /-- The arbitrary value proposed by leader `u` in epoch `i > 0` of slot `k` without certificate. -/
  dflt : Fin n → ℕ → ℕ → V

/-- A local state: everything received (round sent, sender, item) and everything sent
(round, recipient, item). -/
structure St (n : ℕ) (V : Type) where
  /-- Received items with the round in which they were sent and their sender. -/
  rcv : List (ℕ × Fin n × Item n V)
  /-- Sent items with the round and the recipient. -/
  sent : List (ℕ × Fin n × Item n V)

variable {n : ℕ} {V : Type} [DecidableEq V]

section timing
variable (P : Params n V)

/-- Rounds per slot. -/
def slotLen : ℕ := 11 * (P.f + 2)

/-- The slot (`≥ 1`) of round `r`. -/
def slotOf (r : ℕ) : ℕ := r / slotLen P + 1

/-- The epoch of round `r` within its slot. -/
def epochOf (r : ℕ) : ℕ := r % slotLen P / 11

/-- The step (`0..10`, i.e. steps (1)–(11) of Algorithm 4) of round `r`. -/
def stepOf (r : ℕ) : ℕ := r % 11

/-- The first round of the epoch of round `r`. -/
def epochStart (r : ℕ) : ℕ := r - r % 11

/-- The round of step `s` (`0..10`) of epoch `i` of slot `k ≥ 1`. -/
def roundOf (k i s : ℕ) : ℕ := (k - 1) * slotLen P + 11 * i + s

/-- The leader `L_i` of epoch `i` of slot `k`: the sender for `i = 0`, node `i` (index `i - 1`)
otherwise. -/
def leader [NeZero n] (k i : ℕ) : Fin n :=
  if i = 0 then P.sender k else ⟨(i - 1) % n, Nat.mod_lt _ (NeZero.pos n)⟩

end timing

section helpers

/-- Items held at round `t` (sent to us before round `t`). -/
def held (st : St n V) (t : ℕ) : List (Item n V) :=
  (st.rcv.filter (fun e => decide (e.1 < t))).map (fun e => e.2.2)

/-- Items received in rounds `[a, b)`. -/
def heldIn (st : St n V) (a b : ℕ) : List (Item n V) :=
  (st.rcv.filter (fun e => decide (a ≤ e.1) && decide (e.1 < b))).map (fun e => e.2.2)

/-- The slot-`k` certificates `(j, m)` (for `C_{k,j}(m)`) among `xs`, including those carried
by proposals. -/
def certsOf (xs : List (Item n V)) (k : ℕ) : List (ℕ × V) :=
  xs.filterMap fun
    | .cert k' j m => if k' = k then some (j, m) else none
    | .prop _ k' _ m (some j) => if k' = k then some (j, m) else none
    | _ => none

/-- The freshest certificate in a list (the first one of maximal epoch). -/
def freshest (cs : List (ℕ × V)) : Option (ℕ × V) :=
  cs.foldl (fun acc c => match acc with
    | none => some c
    | some a => if a.1 < c.1 then some c else some a) none

/-- Freshness order on `Option ℕ` (`none` = `⊥` is the least). -/
def fle : Option ℕ → Option ℕ → Bool
  | none, _ => true
  | some _, none => false
  | some a, some b => decide (a ≤ b)

/-- Distinct signers of `vote(k,i,m)` among `xs`. -/
def voters (xs : List (Item n V)) (k i : ℕ) (m : V) : List (Fin n) :=
  (xs.filterMap fun
    | .vote u k' i' m' => if k' = k ∧ i' = i ∧ m' = m then some u else none
    | _ => none).dedup

/-- Distinct signers of `⟨C_{k,i}(m)⟩` among `xs`. -/
def sharers (xs : List (Item n V)) (k i : ℕ) (m : V) : List (Fin n) :=
  (xs.filterMap fun
    | .cshare u k' i' m' => if k' = k ∧ i' = i ∧ m' = m then some u else none
    | _ => none).dedup

/-- Distinct accusers of `v` among `xs`. -/
def accusers (xs : List (Item n V)) (v : Fin n) : List (Fin n) :=
  (xs.filterMap fun
    | .accuse w v' => if v' = v then some w else none
    | _ => none).dedup

/-- Values of proposals of `L` for `(k, i)` among `xs`. -/
def propVals (xs : List (Item n V)) (L : Fin n) (k i : ℕ) : List V :=
  (xs.filterMap fun
    | .prop L' k' i' m _ => if L' = L ∧ k' = k ∧ i' = i then some m else none
    | _ => none).dedup

/-- Values of votes for `(k, i)` among `xs`. -/
def voteVals (xs : List (Item n V)) (k i : ℕ) : List V :=
  (xs.filterMap fun
    | .vote _ k' i' m => if k' = k ∧ i' = i then some m else none
    | _ => none).dedup

/-- Values of commit-proof shares for `(k, i)` among `xs`. -/
def shareVals (xs : List (Item n V)) (k i : ℕ) : List V :=
  (xs.filterMap fun
    | .cshare _ k' i' m => if k' = k ∧ i' = i then some m else none
    | _ => none).dedup

/-- Values of commit-proofs for `(k, i)` among `xs`. -/
def cproofVals (xs : List (Item n V)) (k i : ℕ) : List V :=
  (xs.filterMap fun
    | .cproof k' i' m => if k' = k ∧ i' = i then some m else none
    | _ => none).dedup

/-- Some commit-proof of slot `k` is among `xs`. -/
def committedIn (xs : List (Item n V)) (k : ℕ) : Bool :=
  xs.any fun
    | .cproof k' _ _ => k' == k
    | _ => false

/-- `u` has accused `v` (has sent `⟨accuse, v⟩_u`). -/
def accusedBy (st : St n V) (u v : Fin n) : Bool :=
  st.sent.any fun e => e.2.2 == .accuse u v

end helpers

section protocol
variable [NeZero n] (P : Params n V)

/-- Is node `u` running the 11 steps in round `r` (the skip condition of Algorithm 4)? -/
def active (pol : Skip) (r : ℕ) (st : St n V) : Bool :=
  let k := slotOf P r
  let L := leader P k (epochOf P r)
  let old := held st (epochStart r)
  let cur := held st r
  match pol with
  | .epochStart => !(committedIn old k) && !(old.contains (.cpf L))
  | .everyStep => !(committedIn cur k) && !(cur.contains (.cpf L))
  | .mixed => !(committedIn old k) && !(cur.contains (.cpf L))

/-- Send to everybody (including oneself). -/
def mcast (x : Item n V) : List (Fin n × Item n V) := (List.finRange n).map fun w => (w, x)

/-- Send to the `G_ε`-neighbours of `u`. -/
def nbcast (u : Fin n) (x : Item n V) : List (Fin n × Item n V) :=
  ((List.finRange n).filter fun w => P.G u w).map fun w => (w, x)

/-- The 11 steps of Algorithm 4 for node `u` (with input `inp`, i.e. `bc_k = inp k`) in round `r`,
given its state `st` (without the skip condition). -/
def steps (r : ℕ) (u : Fin n) (inp : ℕ → V) (st : St n V) : List (Fin n × Item n V) :=
  let k := slotOf P r
  let i := epochOf P r
  let es := epochStart r
  let L := leader P k i
  let cur := held st r
  let ep := heldIn st es r
  let collectVal : Option ℕ := (freshest (certsOf (held st es) k)).map (·.1)
  let cp : Option V := (cproofVals cur k i).head?
  match stepOf r with
  | 0 => -- (1) Collect
    match freshest (certsOf cur k) with
    | some (j, m) => [(L, .cert k j m)]
    | none => []
  | 1 => -- (2) Propose
    if u = L then
      match freshest (certsOf cur k) with
      | some (j, m) => mcast (.prop u k i m (some j))
      | none => mcast (.prop u k i (if i = 0 then inp k else P.dflt u k i) none)
    else []
  | 2 => -- (3) Propagate-1
    ((ep.filter fun
      | .prop L' k' i' _ c => decide (L' = L ∧ k' = k ∧ i' = i) && fle collectVal c
      | _ => false).dedup).flatMap (nbcast P u)
  | 3 => -- (4) Vote
    if 2 ≤ (propVals cur L k i).length then
      (if accusedBy st u L then [] else mcast (.accuse u L))
    else
      ((st.sent.filterMap fun e =>
        if e.1 = es + 2 then
          (match e.2.2 with
            | .prop L' k' i' m _ => if L' = L ∧ k' = k ∧ i' = i then some m else none
            | _ => none)
        else none).dedup).map fun m => (L, .vote u k i m)
  | 4 => -- (5) Certificate
    if u = L then
      ((voteVals cur k i).filter fun m => decide (n - P.f ≤ (voters cur k i m).length)).flatMap
        fun m => mcast (.cert k i m)
    else []
  | 5 => -- (6) Propagate-2
    (((certsOf cur k).filterMap fun c => if c.1 = i then some c.2 else none).dedup).flatMap
      fun m => nbcast P u (.cert k i m) ++ [(L, .cshare u k i m)]
  | 6 => -- (7) Commit
    if u = L then
      ((shareVals cur k i).filter fun m => decide (n - P.f ≤ (sharers cur k i m).length)).flatMap
        fun m => mcast (.cproof k i m)
    else []
  | 7 => -- (8) Query-1
    if (cproofVals cur k i).isEmpty then
      (if accusedBy st u L then [] else mcast (.accuse u L)) ++
      (match (List.finRange n).find? (fun v => decide (v ≠ u) && !(accusedBy st u v || v == L) &&
          !(cur.contains (.accuse v L))) with
        | some v => [(v, .query1 u k i)]
        | none => [])
    else []
  | 8 => -- (9) Respond-1
    match cp with
    | some m =>
      ((ep.filterMap fun
        | .query1 v k' i' => if k' = k ∧ i' = i then some v else none
        | _ => none).dedup).filterMap fun v =>
          if cur.contains (.accuse v L) &&
              ((List.finRange n).find? (fun w => decide (w ≠ v) && !(cur.contains (.accuse v w))) ==
                some u)
          then some (v, .cproof k i m) else none
    | none => []
  | 9 => -- (10) Query-2
    match st.sent.find? (fun e => decide (e.1 = es + 7) && (match e.2.2 with
        | .query1 _ _ _ => true
        | _ => false)) with
    | some (_, v, _) =>
      if st.rcv.any (fun e => decide (es ≤ e.1) && e.2.1 == v && (match e.2.2 with
          | .cproof k' i' _ => k' == k && i' == i
          | _ => false)) then []
      else mcast (.accuse u v) ++ mcast (.query2 u k i)
    | none => []
  | 10 => -- (11) Respond-2
    match cp with
    | some m =>
      ((List.finRange n).filter fun v =>
        (List.finRange n).any (fun w => (st.rcv.any fun e => e.1 + 1 == r && e.2.2 == .accuse v w) &&
            !((held st (r - 1)).contains (.accuse v w))) &&
          ep.contains (.query2 v k i)).map fun v => (v, .cproof k i m)
    | none => []
  | _ => []

/-- The `(★)` rules of Algorithm 4 (executed at any point). -/
def star (r : ℕ) (u : Fin n) (st : St n V) : List (Fin n × Item n V) :=
  let cur := held st r
  let prev := held st (r - 1)
  let new := (st.rcv.filter fun e => e.1 + 1 == r).map (·.2.2)
  -- forward (newly received) accusations to the accused node (unless it is ourselves)
  ((new.filterMap fun x => match x with
    | .accuse _ v => if v ≠ u ∧ x ∉ prev then some (v, x) else none
    | _ => none).dedup) ++
  -- aggregate `n - f` accusations into a corrupt-proof
  ((List.finRange n).filter fun v =>
      decide (n - P.f ≤ (accusers cur v).length) && decide ((accusers prev v).length < n - P.f)).flatMap
    (fun v => mcast (.cpf v)) ++
  -- forward a newly received commit-proof if the epoch's leader has `n - f` accusations
  ((new.filter fun x => match x with
      | .cproof k j _ => !(prev.contains x) &&
          decide (n - P.f ≤ (accusers cur (leader P k j)).length)
      | _ => false).dedup).flatMap mcast

/-- The honest protocol of Algorithm 4: the 11 steps (subject to the skip condition) and the
`(★)` rules. -/
def act (pol : Skip) (r : ℕ) (u : Fin n) (inp : ℕ → V) (st : St n V) : List (Fin n × Item n V) :=
  (if active P pol r st then steps P r u inp st else []) ++ star P r u st

end protocol

/-- The adversary's data: the static Byzantine set, the inputs (`inp u k` is the value `u` would
broadcast as the sender of slot `k`) and the Byzantine messages (`adv r b` = list of
(recipient, item) sent by `b` in round `r`). -/
structure Scenario (n : ℕ) (V : Type) where
  /-- The Byzantine nodes. -/
  F : Finset (Fin n)
  /-- `inp u k`: the input `bc_k` of `u` (used only when `u = S_k`). -/
  inp : Fin n → ℕ → V
  /-- Messages of Byzantine nodes. -/
  adv : ℕ → Fin n → List (Fin n × Item n V)

section exec
variable [NeZero n] (P : Params n V) (pol : Skip) (sc : Scenario n V)

/-- What every node sends in round `r`, given the configuration `c`. -/
def outs (r : ℕ) (c : Fin n → St n V) (u : Fin n) : List (Fin n × Item n V) :=
  if u ∈ sc.F then sc.adv r u else act P pol r u (sc.inp u) (c u)

/-- What `w` receives in round `r`. -/
def deliver (os : Fin n → List (Fin n × Item n V)) (r : ℕ) (w : Fin n) :
    List (ℕ × Fin n × Item n V) :=
  (List.finRange n).flatMap fun u => (os u).filterMap fun e => if e.1 = w then some (r, u, e.2) else none

/-- One round on a materialized configuration (a list indexed by nodes). -/
def cfgStep (r : ℕ) (c : List (St n V)) : List (St n V) :=
  let get : Fin n → St n V := fun u => c.getD u ⟨[], []⟩
  let os : List (List (Fin n × Item n V)) := (List.finRange n).map (outs P pol sc r get)
  let getO : Fin n → List (Fin n × Item n V) := fun u => os.getD u []
  (List.finRange n).map fun w =>
    ⟨(get w).rcv ++ deliver getO r w, (get w).sent ++ ((getO w).map fun e => (r, e.1, e.2))⟩

/-- The materialized configuration at the start of round `r`. -/
def cfg : ℕ → List (St n V)
  | 0 => List.replicate n ⟨[], []⟩
  | r + 1 => cfgStep P pol sc r (cfg r)

/-- The state of `u` at the start of round `r`. -/
def exec (r : ℕ) (u : Fin n) : St n V := (cfg P pol sc r).getD u ⟨[], []⟩

/-- `x` was sent (to anybody) by an honest node in some round `≤ r`. -/
def sentByHonest (r : ℕ) (x : Item n V) : Prop :=
  ∃ r' ≤ r, ∃ u, u ∉ sc.F ∧ ∃ w, (w, x) ∈ outs P pol sc r' (exec P pol sc r') u

/-- The signer of a signed atom. -/
def Item.signer : Item n V → Option (Fin n)
  | .prop L _ _ _ _ => some L
  | .vote u _ _ _ => some u
  | .cshare u _ _ _ => some u
  | .accuse w _ => some w
  | .query1 u _ _ => some u
  | .query2 u _ _ => some u
  | _ => none

/-- A signed atom is available to the adversary in round `r`: Byzantine signer, or sent by an
honest node in a round `≤ r`. -/
def atomAvail (r : ℕ) (x : Item n V) : Prop :=
  (∃ s, x.signer = some s ∧ s ∈ sc.F) ∨ sentByHonest P pol sc r x

/-- What the adversary can produce in round `r` (ideal (threshold) signatures). -/
def availAt (r : ℕ) : Item n V → Prop
  | .prop L k i m c => atomAvail P pol sc r (.prop L k i m c) ∧
      ∀ j, c = some j → ∃ σ : Finset (Fin n), n - P.f ≤ σ.card ∧
        ∀ u ∈ σ, atomAvail P pol sc r (.vote u k j m)
  | .cert k i m => ∃ σ : Finset (Fin n), n - P.f ≤ σ.card ∧
      ∀ u ∈ σ, atomAvail P pol sc r (.vote u k i m)
  | .cproof k i m => ∃ σ : Finset (Fin n), n - P.f ≤ σ.card ∧
      ∀ u ∈ σ, atomAvail P pol sc r (.cshare u k i m)
  | .cpf v => ∃ σ : Finset (Fin n), n - P.f ≤ σ.card ∧
      ∀ u ∈ σ, atomAvail P pol sc r (.accuse u v)
  | x => atomAvail P pol sc r x

/-- The adversary respects unforgeability: Byzantine messages to honest nodes contain only
available items. -/
def Scenario.AdvValid : Prop :=
  ∀ r b w x, b ∈ sc.F → w ∉ sc.F → (w, x) ∈ sc.adv r b → availAt P pol sc r x

/-- Honest node `u` commits `m` at slot `k` in the run (it holds a commit-proof
`thsig(C_{k,j}(m))` for some epoch `j`, rule `(★)`). -/
def Commits (u : Fin n) (k : ℕ) (m : V) : Prop :=
  ∃ r j, Item.cproof k j m ∈ held (exec P pol sc r u) r

/-- `u` has committed at slot `k` before round `r`. -/
def committedBy (r : ℕ) (u : Fin n) (k : ℕ) : Bool :=
  committedIn (held (exec P pol sc r u) r) k

end exec

end Podc.AmortizedByzantineBroadcast
