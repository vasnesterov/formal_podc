import Mathlib
import Cslib.Foundations.Data.Finset.Quorum

/-!
# Forget-IT: messages, local state and the rules of Algorithms 1–3

Abraham, Das, Efron, Komatovic, *Forget-IT: Optimal Good-Case Latency For Information-Theoretic
BFT*, PODC 2026 (DOI 10.1145/3796701.3815965), Section 4.1, Algorithms 1–3.

This file transcribes the pseudocode as *guarded actions* on the local state of one process:
`En prm p a s` is the guard ("upon …") of rule `a` at process `p` in state `s`, and
`exec prm p a s` is the new local state together with the list of messages broadcast by the rule.

Conventions.
* Views are natural numbers; the protocol uses views `1, 2, …`. The pseudocode also touches
  views `V - 2` and `V - 1` when entering view `V`, i.e. the nonexistent views `-1` and `0` when
  entering view `1`; with truncated subtraction both are view `0` here (a dummy view).
* `GV Val` is `Value ∪ {SAFE}`; `⊥` is `none`.
* The guard field of a `vote-2` message has type `Option (GV Val)` (the pseudocode copies
  `guard_i[view_i]`, which is never `⊥` for a correct process, see `Safety.lean`).
* "Receipt of `k` messages" counts distinct senders (line 21). `cert` is line 117.
* The rules quantifying over a set `S` of accepted `vote-2` messages (lines 58, 61, 63) are
  stated with the largest admissible set, which is equivalent.
* The fields `clk`, `entered`, `active`, `out` are only used by the timed implementation
  (`Protocol.lean`): a local clock, the clock value at the last view entry, whether the current
  view was entered actively, and the outbox of the current tick.
-/

namespace Podc.ForgetIT

open Finset

/-- `Value ∪ {SAFE}`. -/
inductive GV (Val : Type) where
  | safe
  | val (v : Val)
  deriving DecidableEq

/-- Messages of Forget-IT. `echo k V x` is `⟨echo-(k+1), V, x⟩`. -/
inductive Msg (Val : Type) where
  | prepare (V : ℕ) (v : Val)
  | vote1 (V : ℕ) (v : Val)
  | vote2 (V : ℕ) (l : Option Val) (g : Option (GV Val))
  | echo (k : Fin 3) (V : ℕ) (x : GV Val)
  deriving DecidableEq

/-- Protocol parameters: resilience `f` (`n = 3f + 1`), the leader schedule, and the time unit
`Δ` (in ticks; only used by the timed implementation). -/
structure Params (P : Type) where
  f : ℕ
  leader : ℕ → P
  Δ : ℕ

/-- Local state of process `p_i` (lines 3–16), plus the volatile state: received messages
`rcv` and accepted `vote-2` messages `acc` (at most one per view and sender, line 25). -/
structure LS (P Val : Type) where
  prop : Val
  view : ℕ
  guard : ℕ → Option (GV Val)
  vtp : ℕ → Option Val
  lock : ℕ → Option Val
  vote1 : ℕ → Option Val
  vote2 : ℕ → Option (Option Val × Option (GV Val))
  pot : ℕ → Option Val
  alert : ℕ → Option Bool
  vc : ℕ → Bool
  /-- `val_echo(k+1)_i[V][1]`. -/
  echo : Fin 3 → ℕ → Option (GV Val)
  /-- whether `val_echo(k+1)_i[V][2]` (always `SAFE`) is set. -/
  echoS : Fin 3 → ℕ → Bool
  rcv : List (P × Msg Val)
  acc : ℕ → P → Option (Option Val × Option (GV Val))
  /-- the decision (view, value), if any. -/
  decided : Option (ℕ × Val)
  clk : ℕ
  entered : ℕ
  active : Bool
  out : List (Msg Val)

variable {P Val : Type} [Fintype P] [DecidableEq P] [DecidableEq Val]

/-- Distinct senders of received messages satisfying `b`. -/
def snd (rcv : List (P × Msg Val)) (b : Msg Val → Bool) : Finset P :=
  univ.filter fun q => ∃ e ∈ rcv, e.1 = q ∧ b e.2 = true

/-- `⟨vote-1, V, v⟩`. -/
def isVote1 (V : ℕ) (v : Val) : Msg Val → Bool
  | .vote1 V' v' => V' == V && v' == v
  | _ => false

/-- `⟨vote-2, V, v, ·⟩` with lock `v ≠ ⊥`. -/
def isVote2L (V : ℕ) (v : Val) : Msg Val → Bool
  | .vote2 V' (some v') _ => V' == V && v' == v
  | _ => false

/-- `⟨echo-(k+1), V, y⟩` with `y = x` or `y = SAFE` (`SAFE` counts for every value). -/
def isEcho (k : Fin 3) (V : ℕ) (x : GV Val) : Msg Val → Bool
  | .echo k' V' y => k' == k && V' == V && (y == x || y == .safe)
  | _ => false

/-- `cert(echo-(k+1), th, V, x)` (line 117). -/
def cert (s : LS P Val) (k : Fin 3) (th V : ℕ) (x : GV Val) : Prop :=
  th ≤ (snd s.rcv (isEcho k V x)).card

/-- `V ∈ {view_i − 2, view_i − 1, view_i}`. -/
def inW (s : LS P Val) (V : ℕ) : Prop := V ≤ s.view ∧ s.view ≤ V + 2

/-- Lock carried by an accepted `vote-2` entry. -/
def lockOf (o : Option (Option Val × Option (GV Val))) : Option Val := o.bind Prod.fst

/-- Guard carried by an accepted `vote-2` entry. -/
def guardOf (o : Option (Option Val × Option (GV Val))) : Option (GV Val) := o.bind Prod.snd

/-- Senders of accepted `vote-2` messages for view `V`. -/
def accAll (s : LS P Val) (V : ℕ) : Finset P := univ.filter fun q => s.acc V q ≠ none

/-- Senders of accepted `vote-2` messages for `V` carrying guard `G`. -/
def accG (s : LS P Val) (V : ℕ) (G : GV Val) : Finset P :=
  univ.filter fun q => guardOf (s.acc V q) = some G

/-- Senders of accepted `vote-2` messages for `V` whose lock is `⊥` or `ol`. -/
def lockSet (s : LS P Val) (V : ℕ) (ol : Option Val) : Finset P :=
  univ.filter fun q => s.acc V q ≠ none ∧ (lockOf (s.acc V q) = none ∨ lockOf (s.acc V q) = ol)

/-- Senders of accepted `vote-2` messages for `V` whose lock is `⊥` or differs from
`potential_decision_i[V]` (line 63). -/
def notPotSet (s : LS P Val) (V : ℕ) : Finset P :=
  univ.filter fun q => s.acc V q ≠ none ∧ (lockOf (s.acc V q) = none ∨ lockOf (s.acc V q) ≠ s.pot V)

/-- `divergent_guards(V)` (line 123): the number of accepted `vote-2` messages minus the number
of those carrying the most frequent guard is at least `f + 1`; equivalently, this holds for
every guard `G`. -/
def divergent (f : ℕ) (s : LS P Val) (V : ℕ) : Prop :=
  ∀ G : GV Val, f + 1 + (accG s V G).card ≤ (accAll s V).card

/-- The rules of Algorithms 1–3 (the guarded actions of a process). -/
inductive Act (P Val : Type) where
  /-- line 35: vote for the leader's proposal. -/
  | vote1 (w : Val)
  /-- line 39: lock and send `vote-2`. -/
  | lock (v : Val)
  /-- line 43: decide. -/
  | decide (v : Val)
  /-- line 45: timeout `vote-2`. -/
  | timeout2
  /-- line 50: clear the guard. -/
  | clearGuard (x : GV Val)
  /-- lines 23–25: accept a `vote-2` message. -/
  | accept (V : ℕ) (q : P) (l : Option Val) (g : Option (GV Val))
  /-- line 58 (`ol = some ℓ`: line 59, `ol = none`: line 60). -/
  | alertSet (V : ℕ) (ol : Option Val)
  /-- line 61. -/
  | alertClear1 (V : ℕ)
  /-- line 63. -/
  | alertClear2 (V : ℕ)
  /-- line 65: the view-change timer. -/
  | vcTimer
  /-- line 67. -/
  | echoLock (V : ℕ) (q : P) (x : Val)
  /-- line 69. -/
  | echoGuard (V : ℕ) (G : GV Val)
  /-- line 71. -/
  | echoDiv (V : ℕ)
  /-- line 73. -/
  | echo2 (V : ℕ) (x : GV Val)
  /-- line 75. -/
  | echo3 (V : ℕ) (x : GV Val)
  /-- line 77. -/
  | enter3 (V : ℕ) (x : GV Val)
  /-- line 80. -/
  | enter3L (V : ℕ) (x : GV Val)
  /-- line 85. -/
  | enterPrep (V : ℕ) (w : Val) (x : GV Val)
  /-- line 88. -/
  | passive (V : ℕ) (x : GV Val)
  /-- line 52: the recovery procedure. -/
  | recover

/-- Guards of the rules ("upon …"). Timing conditions (lines 45, 65) are dropped: the timers may
fire at any time. -/
def En (prm : Params P) (p : P) : Act P Val → LS P Val → Prop
  | .vote1 w, s => (prm.leader s.view, .prepare s.view w) ∈ s.rcv ∧
      (s.guard s.view = some .safe ∨ s.guard s.view = some (.val w)) ∧
      s.vote1 s.view = none ∧ s.vc s.view = false
  | .lock v, s => 2 * prm.f + 1 ≤ (snd s.rcv (isVote1 s.view v)).card ∧ s.vc s.view = false ∧
      s.vote2 s.view = none
  | .decide v, s => 2 * prm.f + 1 ≤ (snd s.rcv (isVote2L s.view v)).card
  | .timeout2, s => s.vote2 s.view = none
  | .clearGuard x, s => cert s 1 (prm.f + 1) (s.view - 1) x ∧ s.guard s.view ≠ some .safe ∧
      s.guard s.view ≠ some x
  | .accept V q l g, s => (q, .vote2 V l g) ∈ s.rcv ∧ s.acc V q = none ∧
      ∀ v ∈ l, prm.f + 1 ≤ (snd s.rcv (isVote1 V v)).card
  | .alertSet V ol, s => inW s V ∧ s.alert V = none ∧ 2 * prm.f + 1 ≤ (lockSet s V ol).card ∧
      ∀ ℓ ∈ ol, ∃ q, lockOf (s.acc V q) = some ℓ
  | .alertClear1 V, s => inW s V ∧ s.alert V = some true ∧
      2 * prm.f + 1 ≤ (lockSet s V none).card
  | .alertClear2 V, s => inW s V ∧ s.alert V = some true ∧ 2 * prm.f + 1 ≤ (notPotSet s V).card
  | .vcTimer, _ => True
  | .echoLock V q x, s => inW s V ∧ lockOf (s.acc V q) = some x ∧
      (s.pot V = some x ∨ s.alert V = some false) ∧ s.vc V = true
  | .echoGuard V G, s => inW s V ∧ prm.f + 1 ≤ (accG s V G).card ∧ s.alert V = some false ∧
      s.vc V = true
  | .echoDiv V, s => inW s V ∧ s.alert V = some false ∧ divergent prm.f s V ∧ s.vc V = true
  | .echo2 V x, s => inW s V ∧ cert s 0 (2 * prm.f + 1) V x
  | .echo3 V x, s => inW s V ∧ cert s 1 (2 * prm.f + 1) V x
  | .enter3 V x, s => cert s 2 (2 * prm.f + 1) V x ∧ s.view ≤ V ∧ p ≠ prm.leader (V + 1)
  | .enter3L V x, s => cert s 2 (prm.f + 1) V x ∧ s.view ≤ V ∧ p = prm.leader (V + 1)
  | .enterPrep V w x, s => (prm.leader V, .prepare V w) ∈ s.rcv ∧ s.view < V ∧
      cert s 1 (prm.f + 1) (V - 1) x
  | .passive V x, s => cert s 0 (prm.f + 1) V x ∧ s.view ≤ V
  | .recover, _ => True

/-- `ensure_view_change(V, g)` (line 99). -/
def ensureVC (V : ℕ) (g : Option (GV Val)) (s : LS P Val) : LS P Val × List (Msg Val) :=
  match s.vote2 V with
  | none => ({ s with vc := Function.update s.vc V true,
                      vote2 := Function.update s.vote2 V (some (none, g)) }, [.vote2 V none g])
  | some _ => ({ s with vc := Function.update s.vc V true }, [])

/-- `send_echo_one/two/three(V, x)` (lines 102–116). -/
def sendEcho (k : Fin 3) (V : ℕ) (x : GV Val) (s : LS P Val) : LS P Val × List (Msg Val) :=
  match s.echo k V with
  | none => ({ s with echo := Function.update s.echo k (Function.update (s.echo k) V (some x)) },
      [.echo k V x])
  | some y =>
    if s.echoS k V = false ∧ y ≠ .safe ∧ (x = .safe ∨ x ≠ y) then
      ({ s with echoS := Function.update s.echoS k (Function.update (s.echoS k) V true) },
        [.echo k V .safe])
    else (s, [])

/-- `upon entering view V` (lines 30–34), after `guard_i[V]` has been set (active entry). -/
def enterV (prm : Params P) (p : P) (V : ℕ) (s : LS P Val) : LS P Val × List (Msg Val) :=
  let s0 := { s with view := V, entered := s.clk, active := true }
  let r1 := ensureVC (V - 2) (s.guard V) s0
  let r2 := ensureVC (V - 1) (s.guard V) r1.1
  (r2.1, r1.2 ++ r2.2 ++
    (if p = prm.leader V then (match r2.1.vtp V with | some w => [.prepare V w] | none => [])
     else []))

/-- `upon passively entering view V` (lines 94–98), after `guard_i[V]` has been set. -/
def passiveV (V : ℕ) (s : LS P Val) : LS P Val × List (Msg Val) :=
  let s0 := { s with view := V, entered := s.clk, active := false }
  let r1 := ensureVC (V - 2) (s.guard V) s0
  let r2 := ensureVC (V - 1) (s.guard V) r1.1
  let r3 := ensureVC V (s.guard V) r2.1
  (r3.1, r1.2 ++ r2.2 ++ r3.2)

/-- Set `guard_i[V] ← x`. -/
def setGuard (V : ℕ) (x : GV Val) (s : LS P Val) : LS P Val :=
  { s with guard := Function.update s.guard V (some x) }

/-- `x` if it is a value, else `d` (line 82–83). -/
def gvOr (x : GV Val) (d : Val) : Val :=
  match x with
  | .safe => d
  | .val v => v

/-- Set `value_to_propose_i[V] ← w`. -/
def setVtp (V : ℕ) (w : Val) (s : LS P Val) : LS P Val :=
  { s with vtp := Function.update s.vtp V (some w) }

/-- Effect of a rule: new local state and broadcast messages. -/
def exec (prm : Params P) (p : P) : Act P Val → LS P Val → LS P Val × List (Msg Val)
  | .vote1 w, s => ({ s with vote1 := Function.update s.vote1 s.view (some w) },
      [.vote1 s.view w])
  | .lock v, s => ({ s with lock := Function.update s.lock s.view (some v),
                            vote2 := Function.update s.vote2 s.view (some (some v, s.guard s.view)) },
      [.vote2 s.view (some v) (s.guard s.view)])
  | .decide v, s => ({ s with decided := s.decided.or (some (s.view, v)) }, [])
  | .timeout2, s => ({ s with vote2 := Function.update s.vote2 s.view
                                (some (s.lock s.view, s.guard s.view)) },
      [.vote2 s.view (s.lock s.view) (s.guard s.view)])
  | .clearGuard _, s => (setGuard s.view .safe s, [])
  | .accept V q l g, s =>
      ({ s with acc := Function.update s.acc V (Function.update (s.acc V) q (some (l, g))) }, [])
  | .alertSet V ol, s => match ol with
      | none => ({ s with alert := Function.update s.alert V (some false) }, [])
      | some ℓ => ({ s with alert := Function.update s.alert V (some true),
                            pot := Function.update s.pot V (some ℓ) }, [])
  | .alertClear1 V, s => ({ s with alert := Function.update s.alert V (some false) }, [])
  | .alertClear2 V, s => ({ s with alert := Function.update s.alert V (some false) }, [])
  | .vcTimer, s => ({ s with vc := Function.update s.vc s.view true }, [])
  | .echoLock V _ x, s => sendEcho 0 V (.val x) s
  | .echoGuard V G, s => sendEcho 0 V G s
  | .echoDiv V, s => sendEcho 0 V .safe s
  | .echo2 V x, s => sendEcho 1 V x s
  | .echo3 V x, s => sendEcho 2 V x s
  | .enter3 V x, s => enterV prm p (V + 1) (setGuard (V + 1) x s)
  | .enter3L V x, s =>
      enterV prm p (V + 1) (setVtp (V + 1) (gvOr x s.prop) (setGuard (V + 1) x s))
  | .enterPrep V _ x, s => enterV prm p V (setGuard V x s)
  | .passive V x, s => if s.view < V then passiveV V (setGuard V x s) else ensureVC s.view (some x) s
  | .recover, s =>
      let s1 := { s with vc := fun W => if W = s.view ∨ W = s.view - 1 ∨ W = s.view - 2 then true
                                         else s.vc W }
      match s1.vote2 s.view with
      | none => ({ s1 with vote2 := Function.update s1.vote2 s.view
                                  (some (s.lock s.view, s.guard s.view)) },
                 [.vote2 s.view (s.lock s.view) (s.guard s.view)])
      | some _ => (s1, [])

/-- Local state right after `upon starting` (lines 26–28), before entering view 1. -/
def startLS (v : Val) : LS P Val where
  prop := v
  view := 0
  guard := Function.update (fun _ => none) 1 (some .safe)
  vtp := Function.update (fun _ => none) 1 (some v)
  lock := fun _ => none
  vote1 := fun _ => none
  vote2 := fun _ => none
  pot := fun _ => none
  alert := fun _ => none
  vc := fun _ => false
  echo := fun _ _ => none
  echoS := fun _ _ => false
  rcv := []
  acc := fun _ _ => none
  decided := none
  clk := 0
  entered := 0
  active := false
  out := []

/-- Initial local state (after `enter view 1`, line 29) and the messages it broadcasts. -/
def initR (prm : Params P) (p : P) (v : Val) : LS P Val × List (Msg Val) :=
  enterV prm p 1 (startLS v)

/-- Initial local state, with the initial broadcasts in the outbox. -/
def initLS (prm : Params P) (p : P) (v : Val) : LS P Val :=
  { (initR prm p v).1 with out := (initR prm p v).2 }

end Podc.ForgetIT
