import Papers.PODC2013.MessageAdversariesVsFD.Model

/-!
# Two three-process tasks used as counterexamples

Processes are `Fin 3`; the paper's `p₁, p₂, p₃` are `0, 1, 2`. In both tasks the output of `p₃`
(process `2`) is unconstrained: `p₃` only acts as a helper.

* `Tcons`: consensus between `p₁` and `p₂` (`p₁`, `p₂` output the same value, which is the input
  of `p₁` or of `p₂`).
* `Tseen`: each of `p₁`, `p₂` outputs either `alone` or the pair of the inputs of `p₁` and `p₂`,
  and at least one of them outputs the pair ("at least one of the two sees the other"). It is
  solved wait-free in the read/write model by "write your input, then read the other register".
-/

namespace Podc.MessageAdversariesVsFD

/-- Consensus between processes `0` and `1`; process `2` is a helper whose output is free. -/
def Tcons : Task (Fin 3) Bool Bool where
  inputs := Set.univ
  Δ x := {O | O 0 = O 1 ∧ (O 0 = x 0 ∨ O 0 = x 1)}

/-- Outputs of `Tseen`. -/
inductive Seen where
  /-- "I did not see the other process." -/
  | alone
  /-- The inputs of processes `0` and `1`. -/
  | pair (a b : Bool)
  deriving DecidableEq

/-- An output of `Tseen` that is correct for process `0` or `1` with input vector `x`. -/
def Seen.Ok (x : Fin 3 → Bool) : Seen → Prop
  | .alone => True
  | .pair a b => a = x 0 ∧ b = x 1

/-- At least one of processes `0`, `1` outputs the pair of their inputs; process `2` is a helper
whose output is free. -/
def Tseen : Task (Fin 3) Bool Seen where
  inputs := Set.univ
  Δ x := {O | Seen.Ok x (O 0) ∧ Seen.Ok x (O 1) ∧ (O 0 ≠ .alone ∨ O 1 ≠ .alone)}

end Podc.MessageAdversariesVsFD
