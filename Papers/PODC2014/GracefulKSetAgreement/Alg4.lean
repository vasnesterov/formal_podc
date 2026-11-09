import Papers.PODC2014.GracefulKSetAgreement.Model

/-!
# Algorithm 1 + Algorithm 4 (the `k`-uniform `k`-set agreement algorithm, Section 7.3)

This file implements, as a full-information algorithm `alg4 n D : Alg (Fin n) ℕ St` of the model of
`Model.lean`, the paper's Algorithm 4 run together with the network approximation Algorithm 1.
The implementation is computable (bitmasks and lists), so that concrete runs can be evaluated in
the kernel (`decide +kernel`); `Alg.run_eq_cconf` identifies `Alg.run` with the computable mirror
`cconf` for patterns given by a Boolean adjacency function.

Rounds: our round index `t` (graph `ρ t`) is the paper's round `t + 1`; inside the step function,
`r = round + 1` is the paper's current round number. In round `r` the Alg. 1 step is executed
before the Alg. 4 step, and Alg. 4 uses the Alg. 1 state at the end of round `r` (paper, Sec. 7.3).
Messages are the senders' full states at the beginning of the round (full-information form).

## Representation

* Process `j : Fin n` is the number `j.val`; a set of processes is a bitmask `R : ℕ`; the edge
  `(u → w)` (`w` received `u`'s message) is bit `u * n + w`.
* Alg. 1: `A : List ℕ` with `A.getD t 0` = bitmask of the edges whose label set `T` contains the
  round `t` (so `A_p|t` of line 13 is `A.getD t 0`).
* Alg. 4: a lock `(V(R), v, τ_create)` is `Lock`. The lock history `hist_i[j][r']` is stored as a
  list of pairs `(L, e)` with `e.getD j none = some r'` the *earliest* round `r'` such that
  `L ∈ hist_i[j][r']` (`none`: `L` in no entry of row `j`). Algorithm 4 only ever reads
  `⋃_{r'' ≤ r'} hist_i[j][r'']` (line 26), which is determined by these earliest rounds, and the
  updates of lines 13–15 and 20 translate into `min` (see I4).

## Interpretation choices

* **I1** `A_p|t` (Alg. 1, line 13) has vertex set `{p} ∪ {endpoints of edges labelled t}` (with the
  edge-induced graph only, a deaf singleton could never detect itself, contradicting Lemma 13).
* **I2** `C_p|t` (line 14) is the strongly connected component of `p` in `A_p|t` if no edge of
  `A_p|t` enters it from outside, and empty otherwise (sound and complete version of line 14;
  literally, "`A_p|t` if strongly connected", Lemma 13 and Corollary 2 fail as soon as processes
  outside the root report edges leaving it).
* **I3** `InStableRoot(I)` is empty if `I` contains a round `t < 1` (no graph exists there).
* **I4** Line 15 (`hist_i[i] := hist_i \ hist'_i`): every lock that newly appears in some entry
  `hist_i[x][r']` is added to `hist_i[i][r]`; since the own row always contains every lock of the
  other rows, this means: a lock not yet in row `i` gets earliest round `r` in row `i`. Lines 13–14
  copy all rows `x ≠ i` (pointwise `min` of earliest rounds).
* **I5** The multiset `S` of line 26: the multiplicity of `L` is the number of `j ∈ R` with
  `L ∈ ⋃_{r'' ≤ r'} hist_i[j][r'']` ("the number of members of `R` who got to know `L` by round
  `r − 2D`", p. 32).
* **I6** `mfrq_latest` exactly as line 27: `{x ∈ mfrq(S) | ∀ y ≠ x ∈ mfrq(S), x.τ > y.τ}`; the
  fallback of line 32 is the maximum value over *all* of `S`.
* **I7** `τ_create` of a new lock is the current round `r` (lines 30, 32); locks are compared as
  triples.
* **I8** Lines 8–9: if several decisions are received, the smallest one is adopted.
* **I9** The `else if` chain of lines 17/21/23 is evaluated once per round after the history
  update; `lock` is the value set in line 19.
* **I10–I14** concern the message adversary and are listed in `MajInf.lean`.

The variable `V_p` of Alg. 1 (line 8) is not used by `InStableRoot` under I1–I2 and is omitted.
-/

namespace Podc.GracefulKSetAgreement

open Cslib.HeardOf

/-! ### A computable mirror of `Alg.run` -/

section Mirror

variable {n : ℕ} {σ : Type}

/-- Messages received by `i` in the graph given by the Boolean adjacency `g` (`g j i`: `i`
receives `j`), decidable version of `Cslib.HeardOf.msgs`. -/
def cmsgs (g : Fin n → Fin n → Bool) (C : Fin n → σ) (i : Fin n) : Fin n → Option σ :=
  fun j => if j = i ∨ g j i = true then some (C j) else none

/-- Computable mirror of `Cslib.HeardOf.conf`. -/
def cconf (step : StepFn (Fin n) σ) (g : ℕ → Fin n → Fin n → Bool) (C : Fin n → σ) :
    ℕ → Fin n → σ
  | 0 => C
  | t + 1 => fun i => step i (cmsgs (g t) (cconf step g C t) i)

theorem conf_eq_cconf (step : StepFn (Fin n) σ) {ρ : ℕ → Graph (Fin n)}
    {g : ℕ → Fin n → Fin n → Bool} (hρ : ∀ t u v, ρ t u v ↔ g t u v = true) (C : Fin n → σ) :
    ∀ t, conf step C ρ t = cconf step g C t
  | 0 => rfl
  | t + 1 => by
    rw [conf_succ, conf_eq_cconf step hρ C t]
    funext i
    simp only [next, cconf]
    congr 1
    funext j
    simp only [msgs, cmsgs, Hears, hρ]

theorem Alg.run_eq_cconf {V : Type} (A : Alg (Fin n) V σ) {ρ : ℕ → Graph (Fin n)}
    {g : ℕ → Fin n → Fin n → Bool} (hρ : ∀ t u v, ρ t u v ↔ g t u v = true) (x : Fin n → V)
    (t : ℕ) : A.run x ρ t = cconf A.step g (A.initC x) t :=
  conf_eq_cconf A.step hρ _ t

end Mirror

namespace Alg4

/-! ### Bitmask helpers -/

/-- The singleton bitmask `{k}`. -/
def bit (k : ℕ) : ℕ := 2 ^ k

/-- Pointwise union of two lists of bitmasks (missing entries are `0`). -/
def orL : List ℕ → List ℕ → List ℕ
  | [], l => l
  | l, [] => l
  | a :: l, b :: l' => (a ||| b) :: orL l l'

/-- One forward step of the closure of `X` along the edges `E` (`n` processes). -/
def post (n E X : ℕ) : ℕ :=
  (List.range n).foldl (fun acc u =>
    if X.testBit u then
      (List.range n).foldl (fun acc w => if E.testBit (u * n + w) then acc ||| bit w else acc) acc
    else acc) X

/-- One backward step of the closure of `X` along the edges `E`. -/
def pre (n E X : ℕ) : ℕ :=
  (List.range n).foldl (fun acc w =>
    if X.testBit w then
      (List.range n).foldl (fun acc u => if E.testBit (u * n + w) then acc ||| bit u else acc) acc
    else acc) X

/-- `k`-fold iteration. -/
def iter (f : ℕ → ℕ) : ℕ → ℕ → ℕ
  | 0, X => X
  | k + 1, X => iter f k (f X)

/-- Some edge of `E` enters the set `c` from outside. -/
def entersFromOutside (n E c : ℕ) : Bool :=
  (List.range n).any fun u => (List.range n).any fun w =>
    E.testBit (u * n + w) && c.testBit w && !c.testBit u

/-- `C_p|t` of Alg. 1, line 14 (interpretation I1–I2): the strongly connected component of `p`
in the graph with edges `E` (and vertex `p`), if no edge enters it from outside; else `0` (∅). -/
def rootSCC (n E p : ℕ) : ℕ :=
  let c := iter (post n E) n (bit p) &&& iter (pre n E) n (bit p)
  if entersFromOutside n E c then 0 else c

/-- `InStableRoot([lo, hi])` of Alg. 1 (lines 12–18) at process `p` with approximation `A`:
the common non-empty vertex set of `C_p|t`, `t ∈ [lo, hi]`, or `0` (∅). Rounds `t < 1` are
not admissible (I3). -/
def inStableRoot (n : ℕ) (A : List ℕ) (p lo hi : ℕ) : ℕ :=
  if lo = 0 then 0 else
    let c := rootSCC n (A.getD lo 0) p
    if c ≠ 0 ∧ (List.range (hi + 1 - lo)).all (fun k => rootSCC n (A.getD (lo + k) 0) p == c)
    then c else 0

/-! ### Locks and lock histories -/

/-- A lock `(V(R), v, τ_create)`; `R` is a bitmask. -/
structure Lock where
  /-- The vertex set of the detected root component. -/
  R : ℕ
  /-- The proposal value. -/
  v : ℕ
  /-- The creation round. -/
  τ : ℕ
deriving DecidableEq, Repr, Inhabited

/-- Lock history: for each known lock, row `j` holds the earliest round `r'` with
`L ∈ hist[j][r']` (see the module docstring). -/
abbrev Hist := List (Lock × List (Option ℕ))

/-- Minimum of earliest rounds (`none` = never). -/
def omin : Option ℕ → Option ℕ → Option ℕ
  | none, b => b
  | a, none => a
  | some a, some b => some (min a b)

/-- Lines 13–14: copy the rows `x ≠ i` of a received lock entry. -/
def mergeRows (n i : ℕ) (e e' : List (Option ℕ)) : List (Option ℕ) :=
  (List.range n).map fun x => if x = i then e.getD x none else omin (e.getD x none) (e'.getD x none)

/-- Lines 13–14 for one received lock `L` with rows `e'`. -/
def mergeLock (n i : ℕ) (h : Hist) (L : Lock) (e' : List (Option ℕ)) : Hist :=
  if h.any (fun p => p.1 == L) then
    h.map fun p => if p.1 == L then (p.1, mergeRows n i p.2 e') else p
  else h ++ [(L, mergeRows n i (List.replicate n none) e')]

/-- Lines 11–14 for one received history `h'`. -/
def mergeHist (n i : ℕ) (h h' : Hist) : Hist :=
  h'.foldl (fun h p => mergeLock n i h p.1 p.2) h

/-- Line 15 (I4): locks newly learned in round `r` enter the own row with round `r`. -/
def learnNew (i r : ℕ) (h : Hist) : Hist :=
  h.map fun p =>
    if p.2.getD i none = none ∧ p.2.any Option.isSome then (p.1, p.2.set i (some r)) else p

/-- Line 20: a lock created in round `r` is put into `hist_i[i][r]`. -/
def addOwn (n i r : ℕ) (h : Hist) (L : Lock) : Hist :=
  let own : List (Option ℕ) := (List.range n).map fun x => if x = i then some r else none
  if h.any (fun p => p.1 == L) then
    h.map fun p => if p.1 == L then (p.1, p.2.set i (omin (p.2.getD i none) (some r))) else p
  else h ++ [(L, own)]

/-- Row `j` knows the lock by round `r'`. -/
def knowsBy (e : List (Option ℕ)) (j r' : ℕ) : Bool :=
  match e.getD j none with
  | some k => decide (k ≤ r')
  | none => false

/-- Multiplicity of a lock in the multiset `S` of line 26 (I5). -/
def mult (n R r' : ℕ) (e : List (Option ℕ)) : ℕ :=
  ((List.range n).filter fun j => R.testBit j && knowsBy e j r').length

/-- `GetLock(R, r')` (lines 25–33) called in round `r` (I5–I7). -/
def getLock (n : ℕ) (h : Hist) (R r' r : ℕ) : Lock :=
  let S : List (Lock × ℕ) := h.filterMap fun p =>
    let c := mult n R r' p.2
    if c = 0 then none else some (p.1, c)
  let m := S.foldl (fun a q => max a q.2) 0
  let mfrq := (S.filter fun q => q.2 == m).map Prod.fst
  let latest := mfrq.filter fun x => mfrq.all fun y => y == x || decide (y.τ < x.τ)
  match latest with
  | [L] => ⟨R, L.v, r⟩
  | _ => ⟨R, S.foldl (fun a q => max a q.1.v) 0, r⟩

/-! ### The algorithm -/

/-- Local state of Alg. 1 + Alg. 4. -/
structure St where
  /-- Number of completed rounds. -/
  round : ℕ
  /-- Network approximation `A_p` of Alg. 1 (labels per round as bitmasks). -/
  A : List ℕ
  /-- Lock history `hist` of Alg. 4. -/
  hist : Hist
  /-- `ℓ`, the most recent lock round (`none` = ⊥). -/
  ell : Option ℕ
  /-- The current lock (line 19). -/
  lock : Option Lock
  /-- `decision` (`none` = ⊥). -/
  decision : Option ℕ
deriving Inhabited

/-- Initial state (Alg. 4, lines 1–4; Alg. 1, line 1): the virtual lock `({p_i}, x_i, 0)`. -/
def init (n : ℕ) (i : Fin n) (x : ℕ) : St where
  round := 0
  A := []
  hist := [(⟨bit i.val, x, 0⟩, (List.range n).map fun j => if j = i.val then some 0 else none)]
  ell := none
  lock := none
  decision := none

/-- Round `r` computation of Alg. 4 (lines 7–24), after the history update, given the
network approximation `A` at the end of round `r`. -/
def core (n D i r : ℕ) (A : List ℕ) (s : St) (h : Hist) : St :=
  let s1 : St := { s with round := r, A := A, hist := h }
  let myRoot := inStableRoot n A i (r - 2 * D) (r - D)
  match s.ell with
  | none =>
    if myRoot ≠ 0 then
      let L := getLock n h myRoot (r - 2 * D) r
      { s1 with hist := addOwn n i r h L, ell := some (r - 2 * D), lock := some L }
    else s1
  | some l =>
    if myRoot = 0 then { s1 with ell := none }
    else if inStableRoot n A i l (l + 2 * D) ≠ 0 then { s1 with decision := s.lock.map Lock.v }
    else s1

/-- One round of Alg. 1 + Alg. 4 at process `i` (full-information form: `m j` is the state of
`j` at the beginning of the round if `i` hears `j`). -/
def step (n D : ℕ) : StepFn (Fin n) St := fun i m =>
  let s := (m i).getD default
  let r := s.round + 1
  let ids := (List.finRange n).filter fun j => j ≠ i ∧ (m j).isSome
  let nbrs : List St := ids.filterMap m
  -- Alg. 1, lines 3–11
  let newEdges := ids.foldl (fun acc j => acc ||| bit (j.val * n + i.val)) 0
  let A := orL (nbrs.foldl (fun acc s' => orL acc s'.A) s.A) (List.replicate r 0 ++ [newEdges])
  match s.decision with
  | some _ => { s with round := r, A := A }
  | none =>
    match (nbrs.filterMap St.decision).min? with
    | some d => { s with round := r, A := A, decision := some d }   -- lines 8–9
    | none =>
      let h := learnNew i.val r (nbrs.foldl (fun h s' => mergeHist n i.val h s'.hist) s.hist)
      core n D i.val r A s h

end Alg4

open Alg4 in
/-- **Algorithm 4 with Algorithm 1** (Section 7.3) for `n` processes and dynamic causal diameter
`D`, with inputs in `ℕ`. -/
def alg4 (n D : ℕ) : Alg (Fin n) ℕ St where
  init := init n
  step := step n D
  dec := St.decision
  dec_stable := by
    intro i m s v hm hv
    simp only [step, hm, Option.getD_some, hv]

end Podc.GracefulKSetAgreement
