import Papers.PODC2025.UniqueIDsBoundedRegisters.Defs

/-!
# Algorithms 1 and 2: unique identifiers from `n + 1` bounded registers

Registers `R₀, R₁, …, Rₙ` (`Fin (n + 1)`), values in `Fin m`, initially `0`. Parameter `d`
with `n ≤ d` and `d ∣ m`:

```
get():
  repeat i ← R₀.FAI() mod d until i < n
  j ← R_{i+1}.FAI()
  return i · m + j
```

* `d = n` (`n ∣ m`) is Algorithm 1 of the paper (`k = n + 1 = 2^x + 1 ≤ 2^w + 1`): the loop
  always exits after one iteration.
* `d = 2^⌈log₂ n⌉` (`n ≤ m = 2^w`) is Algorithm 2 (`k' - 1 = d`).

Local states: `idle` (no pending operation), `start` (about to apply FAI to `R₀`), `got i`
(about to apply FAI to `R_{i+1}`), `done v` (about to return `v`).
-/

set_option linter.unusedSectionVars false

namespace Cslib.SharedMemory.UniqueIDs

open Cslib.SharedMemory

/-- Local states of the algorithm. -/
inductive St (n : ℕ) where
  | idle
  | start
  | got (i : Fin n)
  | done (v : ℕ)
  deriving DecidableEq

variable {P : Type} [DecidableEq P]

/-- Algorithm 2 with parameter `d` (Algorithm 1 for `d = n`). Anonymous: nothing depends on
the process. -/
def alg (n d m : ℕ) [NeZero m] : Impl uidObj (fun _ : Fin (n + 1) => bReg m) P (St n) where
  memInit _ := 0
  locInit _ := .idle
  invoke _ _ _ := .start
  act _ l := match l with
    | .idle => .ret 0 .idle
    | .start => .access 0 .fai
        (fun r => if h : r.val % d < n then .got ⟨r.val % d, h⟩ else .start)
    | .got i => .access i.succ .fai (fun j => .done (i.val * m + j.val))
    | .done v => .ret v .idle

lemma alg_anonymous (n d m : ℕ) [NeZero m] : Anonymous (alg (P := P) n d m) :=
  ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩

end Cslib.SharedMemory.UniqueIDs
