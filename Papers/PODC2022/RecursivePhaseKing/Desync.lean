import Cslib.Computability.Distributed.Byzantine.PartialSync.Rounds

/-!
# Synchronous rounds with off-by-one starts (Section 4 of [LS22])

In Section 4 of [LS22] correct nodes start (sub)routines "within one round of each other". We
model this with CSLib's `RoundAlgorithm` (local round numbers are passed to `send`/`trans`) run in
global lock-step rounds, where node `p` performs its local round `ℓ` in the global round
`σ p + ℓ`:

* `DRun A F inp`: such an execution. `rcv ℓ p q` is the message `p` receives from `q` in its local
  round `ℓ` (global round `σ p + ℓ`). For a correct sender `q` and a correct receiver `p` this is
  exactly the message `q` sends in that global round (its local round `σ p + ℓ - σ q`), or nothing
  if `q` has not started yet. Messages from faulty senders are arbitrary; what faulty receivers get
  is irrelevant. Messages sent to a node before it starts are lost (it is not running).
* `DRun.StartWithin1`: the correct nodes start in at most two consecutive global rounds.

States of faulty nodes are computed too (meaningless but harmless).
-/

-- CSLib candidate (desynchronized lock-step executions of round algorithms)
namespace RecursivePhaseKing

open Cslib.Byzantine.PartialSync

variable {P M S VI VO : Type*}

/-- An execution of the round algorithm `A` in which node `p` starts at global round `σ p`. -/
structure DRun (A : RoundAlgorithm P M S VI VO) (F : Finset P) (inp : P → VI) where
  /-- The global round in which `p` performs its local round `0`. -/
  σ : P → ℕ
  /-- `st ℓ p`: the state of `p` at the beginning of its local round `ℓ`. -/
  st : ℕ → P → S
  /-- `rcv ℓ p q`: the message received by `p` from `q` in `p`'s local round `ℓ`. -/
  rcv : ℕ → P → P → Option M
  st_zero : ∀ p, st 0 p = A.init p (inp p)
  st_succ : ∀ ℓ p, st (ℓ + 1) p = A.trans ℓ p (st ℓ p) (rcv ℓ p)
  /-- Messages between correct nodes are delivered in the global round in which they are sent. -/
  honest : ∀ ℓ p q, p ∉ F → q ∉ F → rcv ℓ p q =
    if σ q ≤ σ p + ℓ then A.send (σ p + ℓ - σ q) q (st (σ p + ℓ - σ q) q) p else none

/-- The correct nodes start within one round of each other. -/
def DRun.StartWithin1 {A : RoundAlgorithm P M S VI VO} {F : Finset P} {inp : P → VI}
    (E : DRun A F inp) : Prop :=
  ∀ p q, p ∉ F → q ∉ F → E.σ p ≤ E.σ q + 1

end RecursivePhaseKing
