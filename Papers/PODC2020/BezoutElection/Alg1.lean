import Papers.PODC2020.BezoutElection.Defs

/-!
# Algorithm 1: leader election with a single read/write register

Godard, Imbs, Raynal, Taubenfeld, PODC 2020, Section 3 (Algorithm 1).

```
init REG ← ⟨⊥, ∅, electing⟩
operation election(id_i):
  phase_i ← electing; discarded_i ← ∅; loser_i ← false; candidate_i ← true
(1) repeat
(2)   reg_i ← REG
(3)   if reg_i.phase = committing ∧ phase_i = electing then
(4)     phase_i ← committing; discarded_i ← ∅
(5)   else if |reg_i.discarded| = n − 1 ∧ reg_i.id ≠ ⊥ then
(6)     if reg_i.phase = committing then
(7)       return reg_i.id
(8)     else REG ← ⟨⊥, ∅, committing⟩
(10)  else if reg_i.id = ⊥ ∧ ¬loser_i ∧ candidate_i then
(11)    if reg_i.phase = phase_i then
(12)      discarded_i ← discarded_i ∪ reg_i.discarded
(14)    REG ← ⟨id_i, discarded_i, phase_i⟩
(15)  else if reg_i.id ∉ {⊥, id_i} ∧ id_i ∉ reg_i.discarded then
(16)    loser_i ← true; discarded_i ← reg_i.discarded ∪ {id_i}
(17)    REG ← ⟨⊥, discarded_i, phase_i⟩
(19) end repeat
```

Modelling choices:
* the memory is the anonymous memory of CSLib with `m = 1` register (`SymAlg … 1 …`); a single
  register is not anonymous, so the algorithm also works in a non-anonymous memory;
* every loop iteration is one atomic read (line 2) followed, if a write is decided, by one
  atomic write; the local computation is folded into the read (`afterRead`);
* `candidate_i` is always `true` for leader election and is omitted;
* the response is `out id_i ℓ` where `ℓ` is the elected identifier (line 7): `out _ ℓ = ℓ` gives
  the paper's leader election, `out a ℓ = decide (a = ℓ)` the bit output ("am I elected?").
-/

set_option linter.unusedSectionVars false

open Cslib.SharedMemory

namespace BezoutElection.Alg1

/-- The two phases of Algorithm 1. -/
inductive Phase
  | electing
  | committing
  deriving DecidableEq

/-- The value of the shared register `REG`: fields `id`, `discarded`, `phase`. -/
structure Reg (Id : Type) where
  id : Option Id
  disc : Finset Id
  phase : Phase
  deriving DecidableEq

/-- Program counter: `idle` (before the invocation), `read` (line 2), `write w` (a pending
write of `w` at line 8, 14 or 17), `ret ℓ` (line 7: return `ℓ`), `fin` (returned). -/
inductive PC (Id : Type)
  | idle
  | read
  | write (w : Reg Id)
  | ret (ℓ : Id)
  | fin
  deriving DecidableEq

/-- Local state of a process. -/
structure St (Id : Type) where
  me : Id
  pc : PC Id
  phase : Phase
  disc : Finset Id
  loser : Bool
  deriving DecidableEq

variable {Id : Type} [DecidableEq Id]

/-- The initial register value `⟨⊥, ∅, electing⟩`. -/
def Reg.init : Reg Id := ⟨none, ∅, .electing⟩

/-- Lines 3–18, executed after reading the value `r` of `REG` (line 2). -/
def afterRead (n : ℕ) (s : St Id) (r : Reg Id) : St Id :=
  if r.phase = .committing ∧ s.phase = .electing then
    { s with pc := .read, phase := .committing, disc := ∅ }
  else if r.disc.card = n - 1 ∧ r.id ≠ none then
    if r.phase = .committing then
      match r.id with
      | some ℓ => { s with pc := .ret ℓ }
      | none => { s with pc := .read }
    else { s with pc := .write ⟨none, ∅, .committing⟩ }
  else if r.id = none ∧ s.loser = false then
    let d := if r.phase = s.phase then s.disc ∪ r.disc else s.disc
    { s with pc := .write ⟨some s.me, d, s.phase⟩, disc := d }
  else if r.id ≠ none ∧ r.id ≠ some s.me ∧ s.me ∉ r.disc then
    { s with pc := .write ⟨none, insert s.me r.disc, s.phase⟩, loser := true,
             disc := insert s.me r.disc }
  else { s with pc := .read }

variable {R : Type} [Inhabited R]

/-- Algorithm 1 for `n` processes as a symmetric algorithm on one register, with output map
`out`. -/
def alg1 (Id : Type) [DecidableEq Id] (n : ℕ) (out : Id → Id → R) :
    SymAlg (elecObj R) Id 1 (Reg Id) (St Id) where
  bot := Reg.init
  init a := ⟨a, .idle, .electing, ∅, false⟩
  invoke s _ := match s.pc with
    | .idle => { s with pc := .read }
    | _ => s
  act s := match s.pc with
    | .read => .rmw 0 (fun v => v) (afterRead n s)
    | .write w => .rmw 0 (fun _ => w) (fun _ => { s with pc := .read })
    | .ret ℓ => .ret (out s.me ℓ) { s with pc := .fin }
    | _ => .ret default s

end BezoutElection.Alg1
