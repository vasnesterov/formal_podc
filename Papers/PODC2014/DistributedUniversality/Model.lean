import Mathlib

/-!
# The model: Raynal–Stainer–Taubenfeld's (k, ℓ)-universal constructions

Raynal, Stainer, Taubenfeld. *Distributed Universality: Contention-Awareness; Wait-Freedom; Object
Progress, and Other Properties*, PODC 2014 (BA) / IRISA PI-2014 (full version).

We model, as one parametrised asynchronous shared-memory algorithm, the constructions of
* Figure 1 (basic non-blocking `(k,1)`-universal construction, `ca = false`, `help = false`, `ℓ = 1`),
* Figure 2 (contention-aware variant, `ca = true`),
* Section 4.2 (helping lines L1–L5 replacing lines 24 and 27, `help = true`),
* Section 4.3 (`(k, ℓ)`-simultaneous consensus objects instead of `k`-SC objects, general `ℓ`).

`n` processes `Fin n` implement `k` objects `Fin k`.  Operation `(i, s) : Op n` on object `m` is the
`s`-th operation of `my_listᵢ[m]` (operations are unique, as the paper assumes).

**Base objects** are black boxes given by their specifications (as in the paper):
* adopt-commit objects `AC[r][m]` (two instances per round: `ph = false` is `AC[2r-1][m]` of
  Figure 2 (line N1), `ph = true` is `AC[r][m]` of Figure 1 / `AC[2r][m]` of Figure 2), with
  invocation and response as two separate steps; the response chosen by the adversary must satisfy
  validity (the value has been proposed), agreement, and the *no-conflicting-values* property (`acOK`);
* `(k, ℓ)`-simultaneous consensus objects `SC[r]` (`scOK`), also with separate invocation/response.

Atomic registers `GSTATE[i]` (`gst i`) and `LAST_OP[i][m]` (`lastOp i m`).  Each step of a
process performs at most one access to a shared base object or reads one register, except that a
process' writes to its own `LAST_OP` registers are merged with the adjacent local step.

The state also carries *ghost* variables used only to state and prove the theorems (time, the
"global history" `G`, invocation/return times, linearization points, …); they do not influence the
behaviour of the algorithm.
-/

namespace Podc.DistributedUniversality

/-- An operation on one object: its issuing process and its index in that process' list. -/
abbrev Op (n : ℕ) := Fin n × ℕ

/-- The variant of the construction. -/
structure Mode where
  /-- number of objects returned by a `(k,ℓ)`-SC object (`ℓ = 1`: `k`-simultaneous consensus) -/
  ℓ : ℕ
  /-- contention-aware variant (Figure 2): first round of adopt-commit objects (line N1) -/
  ca : Bool
  /-- helping mechanism (lines L1–L5 replace lines 24 and 27) -/
  help : Bool
  /-- strong reading of the "no-conflicting values" property of adopt-commit objects -/
  strongAC : Bool := false
  /-- literal reading of line 4M in Section 4.3, which proposes `operᵢ[m]` instead of `ac_opᵢ[m]`
  (the text of Section 4.3; Figure 2 proposes `ac_opᵢ[m]`) -/
  typo4M : Bool := false

/-- Program counter of a process. -/
inductive PC
  /-- before the initialization line -/
  | init
  /-- line N1: invoke / await `AC[2r-1][m]` -/
  | n1Inv (m : ℕ) | n1Resp (m : ℕ)
  /-- line 2 / 2M: invoke / await `SC[r]` -/
  | scInv | scResp
  /-- lines 3–4 / 3M–4M: invoke / await the `j`-th adopt-commit object of the round -/
  | acInv (j : ℕ) | acResp (j : ℕ)
  /-- line 5: read `GSTATE[q]` -/
  | collect (q : ℕ)
  /-- lines 6–13 (local) -/
  | loc
  /-- lines 16–28 for object `m` -/
  | upd (m : ℕ)
  /-- lines 30–31 -/
  | write
  deriving DecidableEq, Repr

/-- Local state of a process. -/
structure Loc (n k : ℕ) where
  pc : PC
  /-- round number `rᵢ` -/
  r : ℕ
  oper : Fin k → Op n
  /-- `my_opᵢ[m] = (i, cnt m)` -/
  cnt : Fin k → ℕ
  /-- `ℓ_histᵢ` -/
  hist : Fin k → List (Op n)
  /-- `tagᵢ` (`true` = commit) -/
  tag : Fin k → Bool
  acop : Fin k → Op n
  /-- the decision of `SC[r]` (`some v` for the `ℓ` decided objects) -/
  scd : Fin k → Option (Op n)
  /-- order in which the adopt-commit objects of lines 3–4 are invoked: the decided objects first -/
  ord : List (Fin k)
  /-- `g_stateᵢ` -/
  gs : Fin n → Fin k → List (Op n)
  /-- results to return at line 31: object and index of the operation -/
  res : List (Fin k × ℕ)

/-- Global state (shared objects, local states, ghost variables). -/
structure St (n k : ℕ) where
  loc : Fin n → Loc n k
  /-- `GSTATE[i][m]` -/
  gst : Fin n → Fin k → List (Op n)
  /-- `LAST_OP[i][m]`: index of the last operation of `my_listᵢ[m]` invoked by `pᵢ` (`none` = ⊥) -/
  lastOp : Fin n → Fin k → Option ℕ
  /-- adopt-commit invocations: round, instance (`false` = line N1), object, process ↦ proposed value -/
  acI : ℕ → Bool → Fin k → Fin n → Option (Op n)
  /-- adopt-commit responses `(commit?, value)` -/
  acR : ℕ → Bool → Fin k → Fin n → Option (Bool × Op n)
  /-- ghost for the strong reading of no-conflict: some process returned before any conflicting
  invocation, with this value -/
  acFree : ℕ → Bool → Fin k → Option (Op n)
  /-- `SC[r]` invocations -/
  scI : ℕ → Fin n → Option (Fin k → Op n)
  /-- `SC[r]` responses -/
  scR : ℕ → Fin n → Option (Fin k → Option (Op n))
  /-- ghost: number of steps so far -/
  time : ℕ
  /-- ghost: the longest history of each object ever built -/
  G : Fin k → List (Op n)
  /-- ghost: the round in which each entry of `G` was appended -/
  born : Fin k → List ℕ
  /-- ghost: `operᵢ[m]` at the start of round `r` -/
  opRec : ℕ → Fin k → Fin n → Option (Op n)
  /-- ghost: time of the invocation (`next()`) of operation `(i, s)` on `m` -/
  invAt : Fin n → Fin k → ℕ → Option ℕ
  /-- ghost: the local history from which the output of `(i, s)` was computed -/
  retH : Fin n → Fin k → ℕ → Option (List (Op n))
  /-- ghost: the time at which `(i, s)` was returned to the upper layer -/
  retAt : Fin n → Fin k → ℕ → Option ℕ
  /-- ghost: the first time a `GSTATE` register contained the operation (linearization point) -/
  lin : Fin k → Op n → Option ℕ
  /-- ghost: the first process that finished its adopt-commit invocations on its `ℓ` decided
  objects in round `r` -/
  firstL : ℕ → Option (Fin n)
  /-- ghost: the final pair `(tagᵢ[m], ac_opᵢ[m])` of round `r` (recorded when `pᵢ` reaches line 5) -/
  finR : ℕ → Fin k → Fin n → Option (Bool × Op n)

/-- Actions: a local/invocation step, or a response chosen by the adversary. -/
inductive Act (n k : ℕ)
  | go (i : Fin n)
  | ac (i : Fin n) (t : Bool) (v : Op n)
  | sc (i : Fin n) (d : Fin k → Option (Op n))

variable {n k : ℕ}

/-- Initial local state of process `i`. -/
def initLoc (i : Fin n) : Loc n k where
  pc := .init
  r := 0
  oper := fun _ => (i, 0)
  cnt := fun _ => 0
  hist := fun _ => []
  tag := fun _ => false
  acop := fun _ => (i, 0)
  scd := fun _ => none
  ord := []
  gs := fun _ _ => []
  res := []

/-- The initial state. -/
def init : St n k where
  loc := initLoc
  gst := fun _ _ => []
  lastOp := fun _ _ => none
  acI := fun _ _ _ _ => none
  acR := fun _ _ _ _ => none
  acFree := fun _ _ _ => none
  scI := fun _ _ => none
  scR := fun _ _ => none
  time := 0
  G := fun _ => []
  born := fun _ => []
  opRec := fun _ _ _ => none
  invAt := fun _ _ _ => none
  retH := fun _ _ _ => none
  retAt := fun _ _ _ => none
  lin := fun _ _ => none
  firstL := fun _ => none
  finR := fun _ _ _ => none

/-- **Adopt-commit specification** (Section 2.1), checked when process `i` (which proposed `own`)
receives the response `(t, v)` (`t = true`: commit) from an object whose invocations so far are
`inv` and responses so far are `resp`:
* validity: `v` has been proposed;
* agreement: if some process returns `(commit, w)`, every returned pair carries `w`;
* no-conflicting values: if `i` returns before any other process invoked the object with a value
  `≠ own`, it returns `(commit, own)`;
* (strong reading, optional) once some process returned before any conflicting invocation, only
  `(commit, ·)` can be returned. -/
def acOK (strong : Bool) (inv : Fin n → Option (Op n)) (resp : Fin n → Option (Bool × Op n))
    (free : Option (Op n)) (i : Fin n) (own : Op n) (t : Bool) (v : Op n) : Prop :=
  (∃ q, inv q = some v) ∧
  (∀ q, ∀ bw ∈ resp q, bw.1 = true → bw.2 = v) ∧
  (t = true → ∀ q, ∀ bw ∈ resp q, bw.2 = v) ∧
  ((∀ q, q ≠ i → ∀ w ∈ inv q, w = own) → t = true ∧ v = own) ∧
  (strong = true → ∀ w ∈ free, t = true ∧ v = w)

instance (strong : Bool) (inv : Fin n → Option (Op n)) (resp : Fin n → Option (Bool × Op n))
    (free : Option (Op n)) (i : Fin n) (own : Op n) (t : Bool) (v : Op n) :
    Decidable (acOK strong inv resp free i own t v) := by
  unfold acOK; infer_instance

/-- **`(k, ℓ)`-simultaneous consensus specification** (Sections 2.1 and 4.3): the decision `d`
contains exactly `ℓ` pairs `(x, d x)`, each value was proposed in entry `x` before the decision
(validity), and two decided pairs with the same first component agree (agreement). -/
def scOK (ℓ : ℕ) (inv : Fin n → Option (Fin k → Op n))
    (resp : Fin n → Option (Fin k → Option (Op n))) (d : Fin k → Option (Op n)) : Prop :=
  (Finset.univ.filter (fun x => (d x).isSome)).card = ℓ ∧
  (∀ x, ∀ v ∈ d x, ∃ q, ∃ u ∈ inv q, u x = v) ∧
  (∀ q x, ∀ e ∈ resp q, ∀ v ∈ d x, ∀ w ∈ e x, w = v)

instance (ℓ : ℕ) (inv : Fin n → Option (Fin k → Op n))
    (resp : Fin n → Option (Fin k → Option (Op n))) (d : Fin k → Option (Op n)) :
    Decidable (scOK ℓ inv resp d) := by
  unfold scOK; infer_instance

/-- Line 7: the longest of the histories `cands q` that contain `h` (as a prefix). -/
def merge (cands : Fin n → List (Op n)) (h : List (Op n)) : List (Op n) :=
  (List.finRange n).foldl (fun acc q => if acc.isPrefixOf (cands q) then cands q else acc) h

/-- The new proposal `operᵢ[m]` after the operation proposed in the round has been dealt with
(line 24 / 27, or lines L1–L5 with helping), given the local history `h`, the index `c` of
`my_opᵢ[m]` and the registers `LAST_OP`. -/
def nextProp (M : Mode) (lastOp : Fin n → Fin k → Option ℕ) (i : Fin n) (m : Fin k)
    (h : List (Op n)) (c : ℕ) : Op n :=
  if M.help then
    let j : Fin n := ⟨h.length % n, Nat.mod_lt _ i.pos⟩
    match lastOp j m with
    | some t => if (j, t) ∈ h then (i, c) else (j, t)
    | none => (i, c)
  else (i, c)

/-- Where a process goes after line N1 (line N2). -/
def afterN1 (l : Loc n k) : PC :=
  if ∀ m, l.tag m = true then .collect 0 else .scInv

/-- The first line of a round. -/
def startPC (M : Mode) : PC :=
  if M.ca then .n1Inv 0 else .scInv

/-- The order of lines 3M/4M: the objects decided by `SC[r]` first, then the others. -/
def ordOf (d : Fin k → Option (Op n)) : List (Fin k) :=
  (List.finRange k).filter (fun x => (d x).isSome) ++
    (List.finRange k).filter (fun x => (d x).isNone)

/-- The value proposed at line 3M/4M (or 3/4) for object `x`. -/
def acVal (M : Mode) (l : Loc n k) (x : Fin k) : Op n :=
  (l.scd x).getD (if M.ca ∧ M.typo4M = false then l.acop x else l.oper x)

/-- Record the response of `i` to an adopt-commit object, and the "free" ghost. -/
def freeUpd (inv : Fin n → Option (Op n)) (free : Option (Op n)) (i : Fin n) (own : Op n) :
    Option (Op n) :=
  match free with
  | some w => some w
  | none => if ∀ q, q ≠ i → ∀ w ∈ inv q, w = own then some own else none

/-- One step. `none` if the action is not enabled. -/
def stepFn (M : Mode) (s : St n k) : Act n k → Option (St n k)
  | .go i =>
    let l := s.loc i
    match l.pc with
    | .init =>
      some { s with
        loc := Function.update s.loc i
          { l with pc := startPC M, r := 1, cnt := fun _ => 0, oper := fun _ => (i, 0) }
        lastOp := fun j m => if j = i then some 0 else s.lastOp j m
        invAt := fun j m t => if j = i ∧ t = 0 then some s.time else s.invAt j m t
        opRec := fun r m j => if r = 1 ∧ j = i then some (i, 0) else s.opRec r m j
        time := s.time + 1 }
    | .n1Inv m =>
      if h : m < k then
        let x : Fin k := ⟨m, h⟩
        some { s with
          loc := Function.update s.loc i { l with pc := .n1Resp m }
          acI := fun r b y j => if r = l.r ∧ b = false ∧ y = x ∧ j = i then some (l.oper x)
            else s.acI r b y j
          time := s.time + 1 }
      else none
    | .scInv =>
      some { s with
        loc := Function.update s.loc i { l with pc := .scResp }
        scI := fun r j => if r = l.r ∧ j = i then some (if M.ca then l.acop else l.oper)
          else s.scI r j
        time := s.time + 1 }
    | .acInv j =>
      match l.ord[j]? with
      | some x =>
        some { s with
          loc := Function.update s.loc i { l with pc := .acResp j }
          acI := fun r b y q => if r = l.r ∧ b = true ∧ y = x ∧ q = i then some (acVal M l x)
            else s.acI r b y q
          time := s.time + 1 }
      | none => none
    | .collect q =>
      if h : q < n then
        some { s with
          loc := Function.update s.loc i
            { l with pc := if q + 1 < n then .collect (q + 1) else .loc,
                     gs := Function.update l.gs ⟨q, h⟩ (s.gst ⟨q, h⟩) }
          time := s.time + 1 }
      else none
    | .loc =>
      let hist' : Fin k → List (Op n) := fun m => merge (fun q => l.gs q m) (l.hist m)
      let done : Fin k → Prop := fun m => (i, l.cnt m) ∈ hist' m
      some { s with
        loc := Function.update s.loc i
          { l with pc := if 0 < k then .upd 0 else .write, hist := hist',
                   cnt := fun m => if done m then l.cnt m + 1 else l.cnt m }
        lastOp := fun j m => if j = i ∧ done m then some (l.cnt m + 1) else s.lastOp j m
        invAt := fun j m t => if j = i ∧ done m ∧ t = l.cnt m + 1 then some s.time
          else s.invAt j m t
        retH := fun j m t => if j = i ∧ done m ∧ t = l.cnt m then some (hist' m)
          else s.retH j m t
        retAt := fun j m t => if j = i ∧ done m ∧ t = l.cnt m then some s.time
          else s.retAt j m t
        time := s.time + 1 }
    | .upd m =>
      if h : m < k then
        let x : Fin k := ⟨m, h⟩
        let pc' : PC := if m + 1 < k then .upd (m + 1) else .write
        let hx := l.hist x
        if l.acop x ∈ hx then
          some { s with
            loc := Function.update s.loc i
              { l with pc := pc',
                       oper := Function.update l.oper x
                         (nextProp M s.lastOp i x hx (l.cnt x)) }
            time := s.time + 1 }
        else if l.tag x = true then
          let hx' := hx ++ [l.acop x]
          let G' := if hx = s.G x then Function.update s.G x hx' else s.G
          let born' := if hx = s.G x then Function.update s.born x (s.born x ++ [l.r])
            else s.born
          if l.acop x = (i, l.cnt x) then
            let c' := l.cnt x + 1
            let lastOp' : Fin n → Fin k → Option ℕ :=
              fun j y => if j = i ∧ y = x then some c' else s.lastOp j y
            some { s with
              loc := Function.update s.loc i
                { l with pc := pc', hist := Function.update l.hist x hx',
                         cnt := Function.update l.cnt x c',
                         res := (x, l.cnt x) :: l.res,
                         oper := Function.update l.oper x (nextProp M lastOp' i x hx' c') }
              G := G'
              born := born'
              lastOp := lastOp'
              invAt := fun j y t => if j = i ∧ y = x ∧ t = c' then some s.time
                else s.invAt j y t
              retH := fun j y t => if j = i ∧ y = x ∧ t = l.cnt x then some hx'
                else s.retH j y t
              time := s.time + 1 }
          else
            some { s with
              loc := Function.update s.loc i
                { l with pc := pc', hist := Function.update l.hist x hx',
                         oper := Function.update l.oper x
                           (nextProp M s.lastOp i x hx' (l.cnt x)) }
              G := G'
              born := born'
              time := s.time + 1 }
        else
          some { s with
            loc := Function.update s.loc i
              { l with pc := pc', oper := Function.update l.oper x (l.acop x) }
            time := s.time + 1 }
      else none
    | .write =>
      some { s with
        loc := Function.update s.loc i
          { l with pc := startPC M, r := l.r + 1, res := [] }
        gst := Function.update s.gst i l.hist
        lin := fun m o => if (s.lin m o).isNone ∧ o ∈ l.hist m then some s.time else s.lin m o
        retAt := fun j m t => if j = i ∧ (m, t) ∈ l.res then some s.time else s.retAt j m t
        opRec := fun r m j => if r = l.r + 1 ∧ j = i then some (l.oper m) else s.opRec r m j
        time := s.time + 1 }
    | _ => none
  | .ac i t v =>
    let l := s.loc i
    match l.pc with
    | .n1Resp m =>
      if h : m < k then
        let x : Fin k := ⟨m, h⟩
        let own := l.oper x
        if acOK M.strongAC (s.acI l.r false x) (s.acR l.r false x) (s.acFree l.r false x)
            i own t v then
          let l' : Loc n k := { l with tag := Function.update l.tag x t,
                                       acop := Function.update l.acop x v }
          some { s with
            loc := Function.update s.loc i
              { l' with pc := if m + 1 < k then .n1Inv (m + 1) else afterN1 l' }
            acR := fun r b y j => if r = l.r ∧ b = false ∧ y = x ∧ j = i then some (t, v)
              else s.acR r b y j
            acFree := fun r b y => if r = l.r ∧ b = false ∧ y = x then
                freeUpd (s.acI l.r false x) (s.acFree l.r false x) i own
              else s.acFree r b y
            finR := fun r y j => if r = l.r ∧ j = i ∧ ¬ m + 1 < k ∧ (∀ z, l'.tag z = true) then
                some (l'.tag y, l'.acop y)
              else s.finR r y j
            time := s.time + 1 }
        else none
      else none
    | .acResp j =>
      match l.ord[j]? with
      | some x =>
        let own := acVal M l x
        if acOK M.strongAC (s.acI l.r true x) (s.acR l.r true x) (s.acFree l.r true x)
            i own t v then
          some { s with
            loc := Function.update s.loc i
              { l with tag := Function.update l.tag x t,
                       acop := Function.update l.acop x v,
                       pc := if j + 1 < l.ord.length then .acInv (j + 1) else .collect 0 }
            acR := fun r b y q => if r = l.r ∧ b = true ∧ y = x ∧ q = i then some (t, v)
              else s.acR r b y q
            acFree := fun r b y => if r = l.r ∧ b = true ∧ y = x then
                freeUpd (s.acI l.r true x) (s.acFree l.r true x) i own
              else s.acFree r b y
            firstL := fun r => if r = l.r ∧ j + 1 = M.ℓ ∧ s.firstL r = none then some i
              else s.firstL r
            finR := fun r y q => if r = l.r ∧ q = i ∧ ¬ j + 1 < l.ord.length then
                some (Function.update l.tag x t y, Function.update l.acop x v y)
              else s.finR r y q
            time := s.time + 1 }
        else none
      | none => none
    | _ => none
  | .sc i d =>
    let l := s.loc i
    match l.pc with
    | .scResp =>
      if scOK M.ℓ (s.scI l.r) (s.scR l.r) d then
        some { s with
          loc := Function.update s.loc i { l with pc := .acInv 0, scd := d, ord := ordOf d }
          scR := fun r j => if r = l.r ∧ j = i then some d else s.scR r j
          time := s.time + 1 }
      else none
    | _ => none

/-- The process taking an action. -/
def Act.proc : Act n k → Fin n
  | .go i => i
  | .ac i _ _ => i
  | .sc i _ => i

/-- One step of the system. -/
def Step (M : Mode) (s s' : St n k) : Prop := ∃ a, stepFn M s a = some s'

/-- Runs from a state: the list of actions executed. -/
def run (M : Mode) : St n k → List (Act n k) → Option (St n k)
  | s, [] => some s
  | s, a :: as => (stepFn M s a).bind (fun s' => run M s' as)

/-- Reachable states. -/
def Reachable (M : Mode) (s : St n k) : Prop := Relation.ReflTransGen (Step M) init s

/-- Process `i` skipped lines 2M–4M in round `r` (Figure 2, line N2: all its N1 tags are commit). -/
def skipped (M : Mode) (s : St n k) (r : ℕ) (i : Fin n) : Prop :=
  M.ca = true ∧ ∀ y, ∃ v, s.acR r false y i = some (true, v)

open Classical in
/-- The final pair `(tagᵢ[m], ac_opᵢ[m])` of process `i` in round `r`, the one used at lines 16–28:
the response of `AC[2r-1][m]` (line N1) if `i` skipped lines 2M–4M, otherwise the response of the
adopt-commit object of line 3/4 (3M/4M). -/
noncomputable def fin (M : Mode) (s : St n k) (r : ℕ) (m : Fin k) (i : Fin n) :
    Option (Bool × Op n) :=
  if skipped M s r i then s.acR r false m i else s.acR r true m i

/-- An infinite execution: states, actions, starting in `init`, each action enabled. -/
structure Exec (M : Mode) (n k : ℕ) where
  st : ℕ → St n k
  act : ℕ → Act n k
  start : st 0 = init
  step : ∀ t, stepFn M (st t) (act t) = some (st (t + 1))

/-- A correct process takes infinitely many steps (crashed processes stop taking steps). -/
def Exec.Correct {M : Mode} (e : Exec M n k) (i : Fin n) : Prop :=
  ∀ N, ∃ t, N ≤ t ∧ (e.act t).proc = i

end Podc.DistributedUniversality
