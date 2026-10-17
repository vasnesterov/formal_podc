import Papers.PODC2020.BezoutElection.Alg2

/-!
# Algorithm 2: the per-register abstraction

Godard, Imbs, Raynal, Taubenfeld, PODC 2020, Section 5.

Fix one physical register `x`. What happens at `x` is Algorithm 1 (with levels): every process
alternates between reading `x` (during a collect), *processing* its copy of `x` later in its for
loop (lines N(6)–N(19) for the local name of `x`), and possibly writing `x`. We abstract a
configuration to

* the value `reg` of `x`;
* for every process its local variables for `x` (`ph`, `D`, `lo`, `lv`, `ca`: `phase`,
  `discarded`, `loser`, `level`, `candidate` at the local name of `x`) and its *status* for `x`
  (`fresh`: it will read `x`; `copy v`: it read `v` and has not processed it yet; `pend w`: it
  will write `w`).

Abstract steps (`AStep`): `read`, `proc` (processing a copy; the global parts of the candidacy
predicate of line M(10) and the flag `finishing` are arbitrary oracles `ok`, `fin`) and `write`.
-/

set_option linter.unusedSectionVars false

namespace BezoutElection.Alg2

/-- The status of a process with respect to one register. -/
inductive AStatus (Id : Type)
  | fresh
  | copy (v : Reg Id)
  | pend (w : Reg Id)
  deriving DecidableEq

/-- The local variables of a process for one register, and its status. -/
structure ALoc (Id : Type) where
  ph : Phase
  D : Finset Id
  lo : Bool
  lv : ℕ
  ca : Bool
  st : AStatus Id

/-- The abstract per-register state. -/
structure AState (Id P : Type) where
  reg : Reg Id
  loc : P → ALoc Id

variable {Id : Type} [DecidableEq Id]

/-- Processing the copy `r` (lines N(6)–N(19) for one register): the new local variables (the
status is not updated) and the value to write. `ok` is the global part of the candidacy
predicate (`∄ y ≠ x : cand[y]` and `to_win > 0`), `fin` the flag `finishing`. -/
def procX (n U : ℕ) (me : Id) (l : ALoc Id) (r : Reg Id) (ok fin : Bool) :
    ALoc Id × Option (Reg Id) :=
  if r.level = l.lv ∧ r.level < U then
    if r.phase = .committing ∧ l.ph = .electing then
      ({ l with ph := .committing, D := ∅ }, none)
    else if r.disc.card = n - 1 ∧ r.id ≠ none then
      if r.phase = .committing then
        if me ∉ r.disc then
          ({ l with ca := false },
           some ⟨none, ∅, .electing, r.level + 1,
             if fin then insert me r.leaders else r.leaders⟩)
        else (l, none)
      else (l, some ⟨none, ∅, .committing, r.level, r.leaders⟩)
    else if r.id = none ∧ l.lo = false ∧ ok = true then
      ({ l with ca := true, D := if r.phase = l.ph then l.D ∪ r.disc else l.D },
       some ⟨some me, if r.phase = l.ph then l.D ∪ r.disc else l.D, l.ph, r.level, r.leaders⟩)
    else if r.id ≠ none ∧ r.id ≠ some me ∧ me ∉ r.disc then
      ({ l with ca := false, lo := true, D := insert me r.disc },
       some ⟨none, insert me r.disc, l.ph, r.level, r.leaders⟩)
    else (l, none)
  else if l.lv < r.level then
    ({ l with ph := .electing, D := ∅, lo := false, lv := l.lv + 1 }, none)
  else (l, none)

/-- The status after processing: a pending write or nothing. -/
def stOf : Option (Reg Id) → AStatus Id
  | some w => .pend w
  | none => .fresh

/-- The new local state after processing a copy (status updated). -/
def procL (n U : ℕ) (me : Id) (l : ALoc Id) (r : Reg Id) (ok fin : Bool) : ALoc Id :=
  { (procX n U me l r ok fin).1 with st := stOf (procX n U me l r ok fin).2 }

variable {P : Type} [DecidableEq P]

/-- Abstract steps of process `j`. -/
inductive AStep (n U : ℕ) (ids : P → Id) : AState Id P → AState Id P → Prop
  | read (A : AState Id P) (j : P) (h : (A.loc j).st = .fresh) :
      AStep n U ids A ⟨A.reg, Function.update A.loc j { A.loc j with st := .copy A.reg }⟩
  | proc (A : AState Id P) (j : P) (v : Reg Id) (ok fin : Bool) (h : (A.loc j).st = .copy v) :
      AStep n U ids A ⟨A.reg, Function.update A.loc j (procL n U (ids j) (A.loc j) v ok fin)⟩
  | write (A : AState Id P) (j : P) (w : Reg Id) (h : (A.loc j).st = .pend w) :
      AStep n U ids A ⟨w, Function.update A.loc j { A.loc j with st := .fresh }⟩

end BezoutElection.Alg2

/-! ### The per-register invariant -/

namespace BezoutElection.Alg2

variable {Id : Type} [DecidableEq Id] {P : Type} [DecidableEq P]
variable (n U : ℕ) (ids : P → Id)

namespace AState

/-- `u` is a value of the current competition at the register: its content, a pending write of
the current level, or a copy of the current level held by a process of the current level. -/
def Val (A : AState Id P) (u : Reg Id) : Prop :=
  u = A.reg ∨ (∃ j, (A.loc j).st = .pend u ∧ u.level = A.reg.level) ∨
    (∃ j, (A.loc j).st = .copy u ∧ u.level = A.reg.level ∧ (A.loc j).lv = A.reg.level)

/-- `a` is the identifier of a loser of the current competition. -/
def ActLoser (A : AState Id P) (a : Id) : Prop :=
  ∃ i, ids i = a ∧ (A.loc i).lv = A.reg.level ∧ (A.loc i).lo = true

/-- `j` holds a copy that will make it a loser (line 15). -/
def Threat (A : AState Id P) (j : P) : Prop :=
  ∃ v, (A.loc j).st = .copy v ∧ v.level = A.reg.level ∧ (A.loc j).lv = A.reg.level ∧
    v.id ≠ none ∧ v.id ≠ some (ids j) ∧ ids j ∉ v.disc

/-- `w` is the write of line N(11) by `j` (the competition is over). -/
def IsN11 (A : AState Id P) (j : P) (w : Reg Id) : Prop :=
  w.level = A.reg.level + 1 ∧ w.id = none ∧ w.disc = ∅ ∧ w.phase = .electing ∧
    A.reg.leaders ⊆ w.leaders ∧ w.leaders ⊆ insert (ids j) A.reg.leaders

/-- In the committing phase of the leader `ℓ`, `j` acknowledged it and will not write again. -/
def Quiet (A : AState Id P) (ℓ j : P) : Prop :=
  (A.loc j).ph = .committing ∧ (∀ w, (A.loc j).st ≠ .pend w) ∧
    (∀ v, (A.loc j).st = .copy v → v.level = A.reg.level →
      v.id = none ∨ (v.phase = .committing ∧ ids j ∈ v.disc)) ∧
    (A.reg.id = some (ids ℓ) → ids j ∈ A.reg.disc)

/-- No identifier has been written in the current competition yet. -/
def Pristine (A : AState Id P) : Prop :=
  (∀ j, (A.loc j).lv = A.reg.level → (A.loc j).lo = false) ∧ A.reg.id = none ∧
    (∀ j w, (A.loc j).st = .pend w → w.level = A.reg.level → w.id = none) ∧
    (∀ j v, (A.loc j).st = .copy v → v.level = A.reg.level → (A.loc j).lv = A.reg.level →
      v.id = none)

end AState

open AState

/-- Facts that hold in every phase of a competition. -/
structure Basic (A : AState Id P) : Prop where
  lvU : A.reg.level ≤ U
  lvLe : ∀ j, (A.loc j).lv ≤ A.reg.level
  copyLv : ∀ j v, (A.loc j).st = .copy v → (A.loc j).lv ≤ v.level ∧ v.level ≤ A.reg.level
  pendLv : ∀ j w, (A.loc j).st = .pend w → (A.loc j).lv = A.reg.level ∧ A.reg.level < U ∧
    ((w.level = A.reg.level ∧ w.leaders = A.reg.leaders) ∨ A.IsN11 ids j w)
  copyLead : ∀ j v, (A.loc j).st = .copy v → v.level = A.reg.level → v.leaders = A.reg.leaders
  dead : ∀ j v, (A.loc j).st = .copy v → v.level = (A.loc j).lv → (A.loc j).lv < A.reg.level →
    ∀ ok fin, (procX n U (ids j) (A.loc j) v ok fin).2 = none
  lagCa : ∀ j, (A.loc j).lv < A.reg.level → (A.loc j).ca = false
  disc : ∀ u, A.Val u → ∀ a ∈ u.disc, A.ActLoser ids a
  discLoc : ∀ j, (A.loc j).lv = A.reg.level → ∀ a ∈ (A.loc j).D, A.ActLoser ids a
  pendId : ∀ j w, (A.loc j).st = .pend w → w.level = A.reg.level → w.id ≠ none →
    w.id = some (ids j) ∧ w.disc = (A.loc j).D ∧ w.phase = (A.loc j).ph ∧
      (A.loc j).lo = false ∧ (A.loc j).ca = true
  nonloser : ∃ j, (A.loc j).lv < A.reg.level ∨ ((A.loc j).lo = false ∧ ¬A.Threat ids j)
  regId : ∀ a, A.reg.id = some a → ∃ c, ids c = a ∧ (A.loc c).lv = A.reg.level ∧
    (A.loc c).lo = false
  caAct : ∀ j, (A.loc j).ca = true → (A.loc j).lv = A.reg.level ∧ (A.loc j).lo = false
  copyOwn : ∀ j v, (A.loc j).st = .copy v → A.reg.id = some (ids j) → v = A.reg
  caU : ∀ j, (A.loc j).ca = true → A.reg.level < U
  regCa : ∀ a, A.reg.id = some a → ∃ c, ids c = a ∧ ((A.loc c).ca = true ∨
    ∃ w, (A.loc c).st = .pend w ∧ w.level = A.reg.level + 1)
  wit : A.Pristine ∨ (∃ c, (A.loc c).ca = true ∧ ¬A.Threat ids c) ∨
    (∃ c w, (A.loc c).st = .pend w ∧ w.level = A.reg.level + 1)

/-- No value `⟨id, D, ·⟩` with `|D| = n - 1` has been decided in the current competition. -/
structure NoLead (A : AState Id P) : Prop where
  valsEl : ∀ u, A.Val u → u.phase = .electing ∧ (u.id ≠ none → u.disc.card ≠ n - 1)
  phEl : ∀ j, (A.loc j).lv = A.reg.level → (A.loc j).ph = .electing
  noN11 : ∀ j w, (A.loc j).st = .pend w → w.level = A.reg.level
  strict : ∀ c, (A.loc c).lv = A.reg.level → (A.loc c).lo = false → (A.loc c).ca = true →
    (A.loc c).D.card ≠ n - 1

/-- The leader `ℓ` is electing. -/
structure ElPart (A : AState Id P) (ℓ : P) : Prop where
  card : (A.loc ℓ).D.card = n - 1
  ca : (A.loc ℓ).ca = true
  regL : A.reg.id = some (ids ℓ) → A.reg.phase = .electing ∧ A.reg.disc.card = n - 1
  copyL : ∀ j v, (A.loc j).st = .copy v → v.level = A.reg.level →
    (A.loc j).lv = A.reg.level → v.id = some (ids ℓ) → v.phase = .electing
  coVals : ∀ u, A.Val u → u.phase = .committing → u.id = none ∧ u.disc = ∅
  noN11 : ∀ j w, (A.loc j).st = .pend w → w.level = A.reg.level

/-- The leader `ℓ` is committing. -/
structure CoPart (A : AState Id P) (ℓ : P) : Prop where
  closing : ∀ w, (A.loc ℓ).st = .pend w → w.level = A.reg.level + 1 →
    (A.loc ℓ).D.card = n - 1 ∧ (A.loc ℓ).ca = false
  ca : (∀ w, (A.loc ℓ).st = .pend w → w.level = A.reg.level) → (A.loc ℓ).ca = true
  regL : A.reg.id = some (ids ℓ) → A.reg.phase = .committing ∧ A.reg.disc ⊆ (A.loc ℓ).D
  copyL : ∀ j v, (A.loc j).st = .copy v → v.level = A.reg.level →
    (A.loc j).lv = A.reg.level → v.id = some (ids ℓ) →
      (j = ℓ → v.phase = .committing) ∧ (v.phase = .committing → v.disc ⊆ (A.loc ℓ).D)
  regBot : A.reg.id = none → A.reg.phase = .committing → ∀ j, ids j ∈ A.reg.disc →
    ids j ∈ (A.loc ℓ).D ∨ A.Quiet ids ℓ j
  copyBot : ∀ v, (A.loc ℓ).st = .copy v → v.level = A.reg.level → v.id = none →
    v.phase = .committing → ∀ j, ids j ∈ v.disc → ids j ∈ (A.loc ℓ).D ∨ A.Quiet ids ℓ j
  copyBotReg : ∀ v, (A.loc ℓ).st = .copy v → v.level = A.reg.level → v.id = none →
    A.reg.id = none
  pendBot : ∀ k w, (A.loc k).st = .pend w → w.level = A.reg.level → w.id = none →
    w.phase = .committing → ∀ j, ids j ∈ w.disc →
      ids j ∈ (A.loc ℓ).D ∨ (j = k ∧ (A.loc k).ph = .committing)
  quiet : ∀ j, ids j ∈ (A.loc ℓ).D → A.Quiet ids ℓ j
  n11 : ∀ j w, (A.loc j).st = .pend w → w.level = A.reg.level + 1 → j = ℓ

/-- `ℓ` is the leader of the current competition. -/
structure Lead (A : AState Id P) (ℓ : P) : Prop where
  act : (A.loc ℓ).lv = A.reg.level ∧ (A.loc ℓ).lo = false
  others : ∀ j, j ≠ ℓ → (A.loc j).lv = A.reg.level ∧ (A.loc j).lo = true
  copyOther : ∀ j v, (A.loc j).st = .copy v → v.level = A.reg.level →
    (A.loc j).lv = A.reg.level → v.id ≠ none → v.id ≠ some (ids ℓ) →
      j ≠ ℓ ∧ (A.loc j).ph = .electing ∧ v.phase = .electing ∧ v.disc.card ≠ n - 1
  copyLE : ∀ j v, (A.loc j).st = .copy v → v.level = A.reg.level →
    (A.loc j).lv = A.reg.level → v.id = some (ids ℓ) → v.phase = .electing →
      v.disc.card ≠ n - 1 → (A.loc j).ph = .electing
  el : (A.loc ℓ).ph = .electing → ElPart n ids A ℓ
  co : (A.loc ℓ).ph = .committing → CoPart n ids A ℓ

/-- The per-register invariant. -/
def AInv (A : AState Id P) : Prop :=
  Basic n U ids A ∧ (NoLead n A ∨ ∃ ℓ, Lead n ids A ℓ)

end BezoutElection.Alg2
