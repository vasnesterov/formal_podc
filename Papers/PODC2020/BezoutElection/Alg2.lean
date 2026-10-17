import Papers.PODC2020.BezoutElection.Alg1
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Lattice.Fold

/-!
# Algorithm 2: Bezout-based exact d-election with m anonymous read/write registers

Godard, Imbs, Raynal, Taubenfeld, PODC 2020, Section 5 (Algorithm 2).

Parameters: `n` processes, `m` anonymous registers, natural numbers `u, v, ℓ` with
`u m = v n + gcd(m, n)` (the paper takes the smallest such `u, v`), `d = gcd(m, n) ℓ`.
Each register hosts `U = u ℓ` successive competitions (its `level` field counts the solved ones);
each process first wins `W = v ℓ` competitions, and once `v n ℓ` competitions are solved every
process competes for one of the `d` remaining ones, whose winners are the leaders.

```
init REG[x] = ⟨⊥, ∅, electing, 0, ∅⟩ for all x
operation election(id_i):
  phase_i[1..m] ← electing; disc_i[1..m] ← ∅; loser_i[1..m] ← false; level_i[1..m] ← 0;
  cand_i[1..m] ← false; to_win_i ← v ℓ; finishing_i ← false
(1) repeat
(2)   reg_i ← REG_i.collect()                       -- m reads, in local order
N(1)  solved_i ← Σ_x reg_i[x].level
N(2)  leaders_i ← ∪_x reg_i[x].leaders
N(3)  if solved_i = u m ℓ then return leaders_i
N(4)  if solved_i ≥ v n ℓ ∧ ¬finishing_i then finishing_i ← true; to_win_i ← 1
N(5)  for each x ∈ {1..m} do                          -- local order
N(6)    if reg_i[x].level = level_i[x] ∧ reg_i[x].level < u ℓ then
(3)       if reg_i[x].phase = committing ∧ phase_i[x] = electing then
(4)         phase_i[x] ← committing; disc_i[x] ← ∅
(5)       else if |reg_i[x].disc| = n − 1 ∧ reg_i[x].id ≠ ⊥ then
(6)         if reg_i[x].phase = committing then
N(8)          if id_i ∉ reg_i[x].disc then
N(9)            to_win_i ← to_win_i − 1; cand_i[x] ← false
N(10)           if finishing_i then reg_i[x].leaders ← reg_i[x].leaders ∪ {id_i}
N(11)           REG_i[x] ← ⟨⊥, ∅, electing, reg_i[x].level + 1, reg_i[x].leaders⟩
(8)         else REG_i[x] ← ⟨⊥, ∅, committing, reg_i[x].level, reg_i[x].leaders⟩
M(10)     else if reg_i[x].id = ⊥ ∧ ¬loser_i[x] ∧ (∄ y ≠ x : cand_i[y]) ∧ to_win_i > 0 then
N(13)       cand_i[x] ← true
(11)        if reg_i[x].phase = phase_i[x] then disc_i[x] ← disc_i[x] ∪ reg_i[x].disc
(14)        REG_i[x] ← ⟨id_i, disc_i[x], phase_i[x], reg_i[x].level, reg_i[x].leaders⟩
(15)      else if reg_i[x].id ∉ {⊥, id_i} ∧ id_i ∉ reg_i[x].disc then
N(14)       cand_i[x] ← false
(16)        loser_i[x] ← true; disc_i[x] ← reg_i[x].disc ∪ {id_i}
(17)        REG_i[x] ← ⟨⊥, disc_i[x], phase_i[x], reg_i[x].level, reg_i[x].leaders⟩
N(15)   else if reg_i[x].level > level_i[x] then
N(17)     phase_i[x] ← electing; disc_i[x] ← ∅; loser_i[x] ← false; level_i[x] ← level_i[x] + 1
(19) end repeat
```

Modelling choices: every read of the collect and every write is one atomic step (the collect is
not atomic); the local computation is folded into the preceding access; the response is
`out id_i leaders_i` (`out _ L = L` gives the paper's output, `out a L = decide (a ∈ L)` the
bit "am I elected?").
-/

set_option linter.unusedSectionVars false

open Cslib.SharedMemory

namespace BezoutElection.Alg2

export BezoutElection.Alg1 (Phase)

/-- The value of an anonymous register. -/
structure Reg (Id : Type) where
  id : Option Id
  disc : Finset Id
  phase : Phase
  level : ℕ
  leaders : Finset Id
  deriving DecidableEq

/-- Program counter: `idle` (before the invocation), `collect k` (read local register `k`),
`write k w` (write `w` into local register `k`, then continue the for loop at `k + 1`),
`ret L` (return the leader set `L`), `fin` (returned). -/
inductive PC (Id : Type)
  | idle
  | collect (k : ℕ)
  | write (k : ℕ) (w : Reg Id)
  | ret (L : Finset Id)
  | fin
  deriving DecidableEq

/-- Local state; arrays are indexed by local register names. -/
structure St (Id : Type) (m : ℕ) where
  me : Id
  pc : PC Id
  regs : Fin m → Reg Id
  phase : Fin m → Phase
  disc : Fin m → Finset Id
  loser : Fin m → Bool
  level : Fin m → ℕ
  cand : Fin m → Bool
  toWin : ℕ
  finishing : Bool

/-- The parameters of Algorithm 2. -/
structure Params where
  /-- number of processes -/
  n : ℕ
  /-- competitions per register, `u ℓ` -/
  U : ℕ
  /-- competitions each process wins first, `v ℓ` -/
  W : ℕ

variable {Id : Type} [DecidableEq Id] {m : ℕ}

/-- The initial register value. -/
def Reg.init : Reg Id := ⟨none, ∅, .electing, 0, ∅⟩

/-- Lines N(6)–N(19) for local register `x` (with the copy `s.regs x`): the new local state and
the value to write, if any. -/
def procReg (p : Params) (s : St Id m) (x : Fin m) : St Id m × Option (Reg Id) :=
  let r := s.regs x
  if r.level = s.level x ∧ r.level < p.U then
    if r.phase = .committing ∧ s.phase x = .electing then
      ({ s with phase := Function.update s.phase x .committing,
                disc := Function.update s.disc x ∅ }, none)
    else if r.disc.card = p.n - 1 ∧ r.id ≠ none then
      if r.phase = .committing then
        if s.me ∉ r.disc then
          ({ s with toWin := s.toWin - 1, cand := Function.update s.cand x false },
           some ⟨none, ∅, .electing, r.level + 1,
             if s.finishing then insert s.me r.leaders else r.leaders⟩)
        else (s, none)
      else (s, some ⟨none, ∅, .committing, r.level, r.leaders⟩)
    else if r.id = none ∧ s.loser x = false ∧ (∀ y, y ≠ x → s.cand y = false) ∧ 0 < s.toWin then
      let d := if r.phase = s.phase x then s.disc x ∪ r.disc else s.disc x
      ({ s with cand := Function.update s.cand x true, disc := Function.update s.disc x d },
       some ⟨some s.me, d, s.phase x, r.level, r.leaders⟩)
    else if r.id ≠ none ∧ r.id ≠ some s.me ∧ s.me ∉ r.disc then
      ({ s with cand := Function.update s.cand x false, loser := Function.update s.loser x true,
                disc := Function.update s.disc x (insert s.me r.disc) },
       some ⟨none, insert s.me r.disc, s.phase x, r.level, r.leaders⟩)
    else (s, none)
  else if s.level x < r.level then
    ({ s with phase := Function.update s.phase x .electing, disc := Function.update s.disc x ∅,
              loser := Function.update s.loser x false,
              level := Function.update s.level x (s.level x + 1) }, none)
  else (s, none)

/-- The for loop of lines N(5)–N(20) from local index `k` on: stops at the first write
(`pc = write`), or starts a new collect when the loop is over. -/
def loopFrom (p : Params) (s : St Id m) (k : ℕ) : St Id m :=
  if h : k < m then
    match procReg p s ⟨k, h⟩ with
    | (s', some w) => { s' with pc := .write k w }
    | (s', none) => loopFrom p s' (k + 1)
  else { s with pc := .collect 0 }
termination_by m - k

/-- Lines N(1)–N(4) after the collect, then the for loop. -/
def afterCollect (p : Params) (s : St Id m) : St Id m :=
  let solved := ∑ x, (s.regs x).level
  let leaders := Finset.univ.sup (fun x => (s.regs x).leaders)
  if solved = p.U * m then { s with pc := .ret leaders }
  else
    let s := if p.W * p.n ≤ solved ∧ s.finishing = false then
      { s with finishing := true, toWin := 1 } else s
    loopFrom p s 0

variable {R : Type} [Inhabited R]

/-- Algorithm 2 as a symmetric algorithm on `m` anonymous registers, with output map `out`
(applied to the own identifier and the leader set). -/
def alg2 (Id : Type) [DecidableEq Id] (m : ℕ) (p : Params) (out : Id → Finset Id → R) :
    SymAlg (elecObj R) Id m (Reg Id) (St Id m) where
  bot := Reg.init
  init a := ⟨a, .idle, fun _ => Reg.init, fun _ => .electing, fun _ => ∅, fun _ => false,
    fun _ => 0, fun _ => false, p.W, false⟩
  invoke s _ := match s.pc with
    | .idle => { s with pc := .collect 0 }
    | _ => s
  act s := match s.pc with
    | .collect k =>
      if h : k < m then
        .rmw ⟨k, h⟩ (fun v => v) (fun v =>
          let s' := { s with regs := Function.update s.regs ⟨k, h⟩ v }
          if k + 1 < m then { s' with pc := .collect (k + 1) } else afterCollect p s')
      else .ret default s
    | .write k w =>
      if h : k < m then .rmw ⟨k, h⟩ (fun _ => w) (fun _ => loopFrom p s (k + 1))
      else .ret default s
    | .ret L => .ret (out s.me L) { s with pc := .fin }
    | _ => .ret default s

end BezoutElection.Alg2
