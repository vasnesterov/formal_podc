import Cslib.Computability.Distributed.Byzantine.LockStep.Agreement
import Cslib.Computability.Distributed.Byzantine.LockStep.Sequential
import Mathlib

/-!
# The SmallCouncil layer (Goren–Moses, PODC 2020, Figure 1)

Processes are `Fin n`; the Council is `{0, …, t}`. The model is CSLib's synchronous lock-step
Byzantine model `Cslib.Byzantine.LockStep` on the complete graph `⊤`: in round `r` (0-indexed,
so the paper's round `r + 1`, sent at the paper's time `r`) every process sends an `Option` message
to every other process; `none` is a *null message*. The history after `r` rounds is the local state
at time `r`.

Messages are `Bool ⊕ M₂`: layer messages carry one bit, `M₂` is the message type of the base
protocol `B`.

* round 0 (time 0, lines 01–03): `p` sends its input `x` to council member `j` iff `par j ≠ x`
  (silence encodes `x = par j`, where `par j = j mod 2`);
* round 1 (time 1, lines 04–07): council member `j` reconstructs the votes (`values`), computes
  `rec = MAJ(values)` and sends `rec` to `i` iff `values i ≠ rec` (silence encodes
  "`rec` = the value you reported");
* round 2 (time 2, lines 08–10): a process without a unanimous recommendation sends `err` to all;
* time 3 (line 11): a process that got no `err` decides its estimate `est`;
* round 3 (line 12): a process that got an `err` sends `help!` to all;
* rounds `≥ 4` (lines 13–15): a process that got a `help!` runs `B` with input `est`; if it has not
  decided at time 3, it decides `B`'s decision.

**Self-delivery.** Simple graphs have no loops, so a process does not receive its own broadcasts.
The paper's "send to all" includes the sender: a process that sends `err` (resp. `help!`) also
counts it as received. The flag `selfRcv` selects this convention (`true`, the paper's protocol)
or the literal "own messages are not received" reading (`false`), which is broken
(`SelfDelivery.lean`).
-/

namespace Podc.NullMessagesByzantine

open Cslib.Byzantine.LockStep

variable {n : ℕ} {M₂ : Type*}

/-- Messages of the composed protocol: one-bit layer messages or base-protocol messages. -/
abbrev Msg (M₂ : Type*) := Bool ⊕ M₂

/-- Membership in the Council `{0, …, t}`. -/
def council (t : ℕ) (j : Fin n) : Prop := j.val ≤ t

instance (t : ℕ) (j : Fin n) : Decidable (council t j) := inferInstanceAs (Decidable (j.val ≤ t))

/-- `j mod 2`, as a bit. -/
def par (j : Fin n) : Bool := j.val % 2 == 1

/-- The layer message (bit) received from `q` in round `k` of the history `h`. -/
def lmsg (h : History (Fin n) (Msg M₂)) (k : ℕ) (q : Fin n) : Option Bool :=
  (h[k]?.bind fun ib => ib q).bind Sum.getLeft?

/-- Round 0 (lines 01–03): `p` with input `x` sends `x` to `j` iff `j` is in the Council and
`j mod 2 ≠ x`. -/
def send0 (t : ℕ) (x : Bool) (j : Fin n) : Option Bool :=
  if council t j ∧ par j ≠ x then some x else none

/-- Line 04: council member `j` (input `x`) reconstructs the vote of `i` from round 0. -/
def values (j : Fin n) (x : Bool) (h : History (Fin n) (Msg M₂)) (i : Fin n) : Bool :=
  if i = j then x else if (lmsg h 0 i).isSome then !par j else par j

/-- `MAJ`: `true` iff a strict majority of the entries is `true`. -/
def maj (f : Fin n → Bool) : Bool := decide (n < 2 * (Finset.univ.filter fun i => f i = true).card)

/-- Line 05: the recommendation of council member `j`. -/
def recOf (j : Fin n) (x : Bool) (h : History (Fin n) (Msg M₂)) : Bool := maj (values j x h)

/-- Round 1 (lines 06–07): council member `j` sends `rec` to `i` iff `values i ≠ rec`. -/
def send1 (t : ℕ) (j : Fin n) (x : Bool) (h : History (Fin n) (Msg M₂)) (i : Fin n) :
    Option Bool :=
  if council t j ∧ values j x h i ≠ recOf j x h then some (recOf j x h) else none

/-- The recommendation `p` (input `x`) attributes to council member `j` at time 2: its own if
`p = j`; the bit received in round 1 if any; otherwise (null message) the value `p` reported,
i.e. `x`. -/
def recFrom (p : Fin n) (x : Bool) (h : History (Fin n) (Msg M₂)) (j : Fin n) : Bool :=
  if j = p then recOf p x h else (lmsg h 1 j).getD x

/-- Line 08: `p` received the unanimous recommendation `c` from the Council. -/
def Unanimous (t : ℕ) (p : Fin n) (x : Bool) (h : History (Fin n) (Msg M₂)) (c : Bool) : Prop :=
  ∀ j, council t j → recFrom p x h j = c

/-- Line 10: no unanimous recommendation (`p` sends `err`). -/
def Err (t : ℕ) (p : Fin n) (x : Bool) (h : History (Fin n) (Msg M₂)) : Prop :=
  ¬ Unanimous t p x h true ∧ ¬ Unanimous t p x h false

open Classical in
/-- Lines 08–10: the estimate. -/
noncomputable def est (t : ℕ) (p : Fin n) (x : Bool) (h : History (Fin n) (Msg M₂)) : Bool :=
  if Unanimous t p x h true then true else if Unanimous t p x h false then false else x

/-- Line 11: `p` got an `err` in round 2 (with `selfRcv`, its own `err` counts). -/
def GotErr (selfRcv : Bool) (t : ℕ) (p : Fin n) (x : Bool) (h : History (Fin n) (Msg M₂)) :
    Prop :=
  (selfRcv = true ∧ Err t p x h) ∨ ∃ q, (lmsg h 2 q).isSome

/-- Line 13: `p` got a `help!` in round 3 (with `selfRcv`, its own `help!` counts). -/
def Participates (selfRcv : Bool) (t : ℕ) (p : Fin n) (x : Bool)
    (h : History (Fin n) (Msg M₂)) : Prop :=
  (selfRcv = true ∧ GotErr selfRcv t p x h) ∨ ∃ q, (lmsg h 3 q).isSome

open Classical in
/-- **SmallCouncil composed with the base protocol `B`** (Figure 1), with the self-delivery
convention `selfRcv`. -/
noncomputable def smallCouncilGen (selfRcv : Bool) (t : ℕ) (B : Protocol (Fin n) Bool M₂ Bool) :
    Protocol (Fin n) Bool (Msg M₂) Bool where
  send p x h q :=
    if h.length = 0 then (send0 t x q).map Sum.inl
    else if h.length = 1 then (send1 t p x h q).map Sum.inl
    else if h.length = 2 then (if Err t p x h then some (Sum.inl true) else none)
    else if h.length = 3 then (if GotErr selfRcv t p x h then some (Sum.inl true) else none)
    else if Participates selfRcv t p x h then
      (B.send p (est t p x h) (histR (h.drop 4)) q).map Sum.inr
    else none
  decide p x h :=
    if h.length < 3 then none
    else if ¬ GotErr selfRcv t p x h then some (est t p x h)
    else if h.length < 4 then none
    else if Participates selfRcv t p x h then B.decide p (est t p x h) (histR (h.drop 4))
    else none

/-- **SmallCouncil composed with `B`** (Figure 1), with the paper's convention that a process
broadcasting `err` / `help!` also receives it. -/
noncomputable abbrev smallCouncil (t : ℕ) (B : Protocol (Fin n) Bool M₂ Bool) :
    Protocol (Fin n) Bool (Msg M₂) Bool :=
  smallCouncilGen true t B

end Podc.NullMessagesByzantine
