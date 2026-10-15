import Cslib.Computability.Distributed.SharedMemory.Task

/-!
# The `k`-bounded lattice-agreement task (§3 of Gafni–Losa–Raynal–Taubenfeld, PODC 2025)

Processes receive no input (`In = Unit`) and each participating process outputs a finite set of
process identifiers such that

* **Validity**: each participating process outputs a set of participating processes;
* **Self-inclusion**: each participating process outputs a set that contains itself;
* **Containment**: every two outputs of cardinality at most `k` are related by containment.

Since `Δ` is evaluated on finite (possibly partial) executions, "participating" means "has
invoked the task".
-/

namespace Cslib.SharedMemory.StrangerFree

open Cslib.SharedMemory

variable {P : Type}

/-- The `k`-bounded lattice-agreement task (Definition in §3 of the paper). -/
def boundedLA (P : Type) (k : ℕ) : Task P where
  In := Unit
  Out := Finset P
  Δ ins outs := ∀ p o, outs p = some o →
    (∀ q ∈ o, ins q ≠ none) ∧ p ∈ o ∧
    ∀ p' o', outs p' = some o' → o.card ≤ k → o'.card ≤ k → o ⊆ o' ∨ o' ⊆ o

instance (k : ℕ) : Inhabited (boundedLA P k).Out := inferInstanceAs (Inhabited (Finset P))

/-- The object specification of the `k`-bounded lattice-agreement task. -/
abbrev laObj (P : Type) : ObjSpec := taskObj Unit (Finset P)

end Cslib.SharedMemory.StrangerFree
