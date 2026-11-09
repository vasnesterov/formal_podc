import Papers.PODC2016.WeakCrashFailures.Failures
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Order.Fin.Basic

/-!
# The consensus algorithm of Fig. 1 (one crash (n−1)-failure)

G. Taubenfeld, *Computing in the presence of weak crash failures*, PODC 2016; full version
*Weak Failures: Definitions, Algorithms and Impossibility Results*, Fig. 1.

Model: `n` processes `Fin n`, asynchronous, atomic multi-writer registers `state[1..n]`
(values `0..3`), `input[1..n]` (initial values immaterial: an arbitrary parameter `inr₀`) and
`decision : Option ℕ` (`none` = ⊥). Inputs are natural numbers ("non-negative").

Every step of a process performs at most one shared-memory access (read or write) together with
the local computation that follows it. Program counters carry the local variables
(`round`, `j`, `counter`, `max`). Two reads of `decision` that follow each other without any other
access of the process (lines 13–14, lines 22–23) are merged into one read; the result of the second
read is determined by the first one (the register is never reset to ⊥), so this only removes
stuttering. A process that decided is in `done v`; its later steps are no-ops, so it counts as a
correct process in infinite schedules (see `Failures.lean`).

* `PC.start` – line 1 (write `input[i]`).
* `PC.scan r j cnt mx` – lines 4–6 of round `r`, about to read `state[j]` (`j < n`), or, for
  `j = n`, line 7 (`counter = n−1`: write `decision := max`, decide) or line 8
  (write `state[i] := r`).
* `PC.scanIn r j cnt mx` – line 6, about to read `input[j]`.
* `PC.wait r j cnt mx` – lines 10–12, about to read `state[j]`; for `j = n` lines 13–14: read
  `decision`; if `≠ ⊥` decide it, else if `counter ≥ n−1` leave the loop (next round, or after
  round 3 line 16), else repeat.
* `PC.chk j cnt mx` / `PC.chkIn j cnt mx` – lines 17–19; for `j = n` line 20.
* `PC.fin j mx` – line 22, about to read `state[j]`; for `j = n` line 25.
* `PC.finDec j mx b` – lines 22–23, about to read `decision` (`b`: `state[j] = 3` was read).
* `PC.finIn j mx` – line 24, about to read `input[j]`.
-/

namespace Podc.WeakCrashFailures.Fig1

/-- Program counters (with the local variables). -/
inductive PC
  | start
  | scan (r j cnt mx : ℕ)
  | scanIn (r j cnt mx : ℕ)
  | wait (r j cnt mx : ℕ)
  | chk (j cnt mx : ℕ)
  | chkIn (j cnt mx : ℕ)
  | fin (j mx : ℕ)
  | finDec (j mx : ℕ) (b : Bool)
  | finIn (j mx : ℕ)
  | done (v : ℕ)
  deriving DecidableEq

/-- Configurations: local states and the shared registers. -/
@[ext]
structure Cfg (n : ℕ) where
  pc : Fin n → PC
  st : Fin n → ℕ
  inr : Fin n → ℕ
  dec : Option ℕ

variable {n : ℕ}

/-- `state[j]` for `j : ℕ` (`0` out of range, never used). -/
def stAt (C : Cfg n) (j : ℕ) : ℕ := if h : j < n then C.st ⟨j, h⟩ else 0

/-- `input[j]` for `j : ℕ`. -/
def inAt (C : Cfg n) (j : ℕ) : ℕ := if h : j < n then C.inr ⟨j, h⟩ else 0

/-- Change the program counter of `i` only. -/
def setPc (i : Fin n) (c : PC) (C : Cfg n) : Cfg n := { C with pc := Function.update C.pc i c }

/-- One step of process `i` (inputs `x`). -/
def step (x : Fin n → ℕ) (i : Fin n) (C : Cfg n) : Cfg n :=
  match C.pc i with
  | .start => { C with inr := Function.update C.inr i (x i),
                       pc := Function.update C.pc i (.scan 1 0 0 0) }
  | .scan r j cnt mx =>
    if j < n then
      if r ≤ stAt C j then setPc i (.scanIn r j (cnt + 1) mx) C
      else setPc i (.scan r (j + 1) cnt mx) C
    else if cnt = n - 1 then { C with dec := some mx, pc := Function.update C.pc i (.done mx) }
    else { C with st := Function.update C.st i r, pc := Function.update C.pc i (.wait r 0 0 mx) }
  | .scanIn r j cnt mx => setPc i (.scan r (j + 1) cnt (max mx (inAt C j))) C
  | .wait r j cnt mx =>
    if j < n then setPc i (.wait r (j + 1) (if r ≤ stAt C j then cnt + 1 else cnt) mx) C
    else match C.dec with
      | some d => setPc i (.done d) C
      | none =>
        if n - 1 ≤ cnt then
          if r < 3 then setPc i (.scan (r + 1) 0 0 0) C
          else if cnt = n - 1 then setPc i (.chk 0 0 0) C
          else setPc i (.fin 0 mx) C
        else setPc i (.wait r 0 0 mx) C
  | .chk j cnt mx =>
    if j < n then
      if 2 ≤ stAt C j then setPc i (.chkIn j (cnt + 1) mx) C
      else setPc i (.chk (j + 1) cnt mx) C
    else if cnt = n - 1 then { C with dec := some mx, pc := Function.update C.pc i (.done mx) }
    else setPc i (.fin 0 mx) C
  | .chkIn j cnt mx => setPc i (.chk (j + 1) cnt (max mx (inAt C j))) C
  | .fin j mx =>
    if j < n then setPc i (.finDec j mx (decide (stAt C j = 3))) C
    else { C with dec := some mx, pc := Function.update C.pc i (.done mx) }
  | .finDec j mx b =>
    match C.dec with
    | some d => setPc i (.done d) C
    | none => if b then setPc i (.finIn j mx) C else setPc i (.fin j mx) C
  | .finIn j mx => setPc i (.fin (j + 1) (max mx (inAt C j))) C
  | .done _ => C

/-- The initial configuration (`inr₀`: the immaterial initial values of `input[]`). -/
def init (inr₀ : Fin n → ℕ) : Cfg n where
  pc _ := .start
  st _ := 0
  inr := inr₀
  dec := none

/-- The configuration after `t` steps of the schedule `σ`. -/
def exec (x inr₀ : Fin n → ℕ) (σ : ℕ → Fin n) : ℕ → Cfg n
  | 0 => init inr₀
  | t + 1 => step x (σ t) (exec x inr₀ σ t)

@[simp] lemma exec_zero (x inr₀ : Fin n → ℕ) (σ : ℕ → Fin n) : exec x inr₀ σ 0 = init inr₀ := rfl

lemma exec_succ (x inr₀ : Fin n → ℕ) (σ : ℕ → Fin n) (t : ℕ) :
    exec x inr₀ σ (t + 1) = step x (σ t) (exec x inr₀ σ t) := rfl

/-- `i` has decided `v`. -/
def Decided (C : Cfg n) (i : Fin n) (v : ℕ) : Prop := C.pc i = .done v

end Podc.WeakCrashFailures.Fig1
