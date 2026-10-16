import Papers.PODC2020.UnknownParticipantsBA.Consensus

/-!
# The "fill rule" of Algorithm 3 (full version) breaks agreement

Algorithm 3 of the full version (consensus) contains the rule: "If a node `u` receives a message
from another node `v` during initialization but not later inside the loop, then `u` assumes that
`v` sent the same message as sent by `u` in the previous round" (meant to cope with nodes that
have terminated). But correct nodes are also silent when they do not reach a threshold (they send
`prefer`/`strongprefer` only conditionally), and such silence is then counted as *support for the
receiver's own value*.

`fillExt` is our consensus algorithm `consExt` with this rule added: a node treats every node it
has heard of that sent it no consensus message in the round as having sent the consensus messages
the node itself broadcast in the previous round. With `n = 4`, `f = 1` (correct `1, 2, 3` with
inputs `0, 0, 1`; Byzantine `0`, which is the coordinator of phase 0):

* phase 0: only node `1` gets `3` copies of `input(0)` (`1, 2` and the Byzantine node) and sends
  `prefer(0)`; nodes `2, 3` are silent, so node `1` counts them as `prefer(0)` and then as
  `strongprefer(0)` and **decides `0`**; nodes `2, 3` see one `strongprefer(0)` and adopt the
  Byzantine coordinator's opinion `1`;
* phase 1: nodes `2, 3` (and the Byzantine node) send `input(1)`, `prefer(1)` — node `1` is silent
  in the `prefer` round and is counted as `prefer(1)` — and node `2` **decides `1`**.
-/

namespace UnknownBA

variable {I X : Type*} [DecidableEq I] [LinearOrder I] [LinearOrder X]

/-- Senders of consensus (application) messages. -/
def appSenders (B : Finset (I × Msg I (CMsg X))) : Finset I :=
  (B.filter fun e => e.2.appVal.isSome).image Prod.fst

/-- The fill rule: every node of `H` that sent no consensus message is assumed to have sent the
consensus messages `O` (those the receiver sent in the previous round). -/
def fillIn (H : Finset I) (O : Finset (CMsg X)) (B : Finset (I × Msg I (CMsg X))) :
    Finset (I × Msg I (CMsg X)) :=
  B ∪ (H.filter fun q => q ∉ appSenders B) ×ˢ O.image Msg.app

/-- Our consensus algorithm with Algorithm 3's fill rule. -/
def fillExt : Ext I X (CMsg X) (CState I X) :=
  { consExt with step := fun s c st B => consExt.step s c st (fillIn c.heard st.out B) }

/-- The protocol with the fill rule. -/
def fillCons : Protocol I X (Msg I (CMsg X)) (St I (CState I X)) := withRotor fillExt

namespace FillCex

/-- The Byzantine node `0`. -/
def adv : ℕ → ℕ → ℕ → Finset (Msg ℕ (CMsg ℕ))
  | 0, 0, _ => {.init}
  | 1, 0, v => if v = 1 then {.app (.input 0)} else {.app (.input 1)}
  | 2, 0, v => if v = 1 then {.app (.prefer 0)} else ∅
  | 3, 0, v => if v = 1 then {.app (.strong 0)} else {.app (.opinion 1)}
  | 4, 0, _ => {.app (.input 1)}
  | 5, 0, _ => {.app (.prefer 1)}
  | 6, 0, _ => {.app (.strong 1)}
  | _, _, _ => ∅

/-- Correct nodes `1, 2, 3` with inputs `0, 0, 1`; Byzantine node `0`. -/
def env : Env ℕ ℕ (Msg ℕ (CMsg ℕ)) where
  G := {1, 2, 3}
  F := {0}
  disj := by decide
  input v := if v = 3 then 1 else 0
  adv := adv

theorem resilience : 2 * env.F.card < env.G.card := by decide

/-- Node `1` decides `0` (in phase 0) ... -/
theorem dec_one : (run fillCons env 4 1).ext.dec = some 0 := by decide +kernel

/-- ... and node `2` decides `1` (in phase 1). -/
theorem dec_two : (run fillCons env 7 2).ext.dec = some 1 := by decide +kernel

/-- **Agreement fails** for the consensus algorithm with the fill rule of Algorithm 3, although
`n = 4 > 3f = 3`. -/
theorem fill_rule_breaks_agreement :
    ∃ v ∈ env.G, ∃ u ∈ env.G, ∃ s s' y y', (run fillCons env s v).ext.dec = some y ∧
      (run fillCons env s' u).ext.dec = some y' ∧ y ≠ y' :=
  ⟨1, by decide, 2, by decide, 4, 7, 0, 1, dec_one, dec_two, by decide⟩

/-- Sanity check: without the fill rule, the same adversary is harmless — all correct nodes decide
`1` (as guaranteed by `consensus_correct`). -/
theorem without_fill : ∀ v ∈ env.G, (run cons env 7 v).ext.dec = some 1 := by decide +kernel

end FillCex

end UnknownBA
