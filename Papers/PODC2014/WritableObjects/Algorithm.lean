import Papers.PODC2014.WritableObjects.Defs
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Fin
import Mathlib.Algebra.BigOperators.Fin

/-!
# The wait-free algorithm of Figure 4.5

A transition-system model of the wait-free implementation of a writable object from
sequentially writable (`SW`) objects (Figure 4.5 of Aghazadeh's thesis = Section 3 of
[AGW14]).

## Model

* `n ≥ 1` processes `Fin n`. The array `A[0 … n(8n+9)-1]` is indexed by
  `Idx n = Fin n × Fin (8n+9)`; the owner of `(p, k)` is `p`. This is the paper's
  `I_p = {i | i mod n = p}` up to the relabelling `(p, k) ↦ k·n + p`.
* Shared registers: `Ptr` (`ptr`), `Annc[q]` (`annc q`), `H_p[q]` (`hH p q`), `H'_p[q]`
  (`hH' p q`) and `S_q` (`S q`). `⊥` is `none`; the initial value `-1` of `S_q` is the integer
  `-1`.
* Local variables: the four queues `usedQ, anncQ, hintQ, hint'Q` (`qs.q 0 … qs.q 3`), the
  counters `c_p` (`qs.cnt`), the set `free_p` (`qs.free`) and `ctr_p` (`ctr`). The paper's
  `ctr_p` is incremented modulo `n`; we keep the unbounded counter `ctr` and use it modulo `n`
  (`cq ctr`) wherever the paper uses `ctr_p`, which is equivalent. The unused local `lptr_p` of
  the figure is omitted.
* One step = one atomic access of a shared register (or an invocation/response), together with
  the local computation that follows it up to the next shared access; local lines are attached
  to the adjacent shared step as on p. 58–59 of the thesis: lines 25–28 form one step (the
  first atomic step of `recycle()`, reading `Annc[ctr_p]`), lines 29–30 and 31–32 one step
  each, line 17 belongs to line 16, lines 41–42 to line 40 and line 38 to line 39. Line 24
  (`ctr_p += 1`) belongs to line 21 resp. line 23.
* `free_p.remove()` returns an arbitrary element of `free_p` (nondeterminism); if `free_p` were
  empty the step would be disabled (Claim 4.14 says this never happens; the safety properties
  proved here do not need it).
* The `SW` objects are black boxes: invoking `A[i].SWrite(v)` / `A[i].Oper(o)` is one step that
  emits `swinv` / `opinv`, and its response is a separate step that emits `aret` with an
  *arbitrary* response chosen by the environment. Invocations of `Write(v)` / `Exec(o)` (with `o`
  not a write) are environment-chosen steps of idle processes.
* Line 38 computes `owner(i)` of the value `i` read from `Ptr`; if `Ptr = ⊥` this is undefined
  and the step is disabled. After the initial `Write(v0)` (see `Initialized`) `Ptr ≠ ⊥`, so this
  never happens in the executions considered by the paper.

## Ghost state

Some fields are *ghost* variables: they are written but never read by the algorithm (no guard
or written value depends on them), so they do not restrict the behaviour. They record history
used by the correctness proof (Lemma 4.8):

* `tr` — the transcript of the execution (the list of emitted events);
* `Loc.lc i` — the number (value of `ctr`) of the `Write` of the owner that last chose `i` as its
  write-index; `Loc.pp i` — the position in `tr` of the `Ptr.Write(i)` of that `Write`;
* `Loc.m` — the number of writes of `q` to `S_q` (the *epoch*); `Loc.τ35` — the length of the
  transcript at `q`'s latest write to `S_q`; `Loc.eq` — the position of `q`'s latest `Exec`
  invocation;
* hint entries carry the number `w` of the `Write` that wrote them and the epochs of `S_q`
  read/current during that `Write`; `H'` entries also carry the position `π` of the `Ptr.Write`;
* program-counter arguments `m14, m19, τ19, π, g, ts, t` and the values `olds, olds'` kept at
  line 18.
-/

namespace Podc.WritableObjects.WF

open Cslib.SharedMemory

/-- Indices of the array `A`: `(p, k)` is the `k`-th index owned by `p`. -/
abbrev Idx (n : ℕ) := Fin n × Fin (8 * n + 9)

/-- `owner(i)`. -/
abbrev owner {n : ℕ} (i : Idx n) : Fin n := i.1


/-- `k mod n` as a process identifier. -/
def cq {n : ℕ} [NeZero n] (k : ℕ) : Fin n := ⟨k % n, Nat.mod_lt _ (Nat.pos_of_neZero n)⟩

/-- The value of `S_q` after `m` writes to it (`-1` initially, then `0, 1, …, 2n-1, 0, …`). -/
def Sval (n m : ℕ) : ℤ := if m = 0 then -1 else (((m - 1) % (2 * n) : ℕ) : ℤ)

/-- An entry of `H_p[q]`: the pair `(f, s)` plus ghost data (the number `w` of the `Write` of `p`
that wrote it, the epoch `m14` of `S_q` read in line 14 and the epoch `m18` of `S_q` when line 18
was executed). -/
structure HE (n : ℕ) where
  f : Idx n
  s : ℤ
  w : ℕ
  m14 : ℕ
  m18 : ℕ

/-- An entry of `H'_p[q]`: the pair `(f, s')` plus ghost data (the number `w` of the `Write`
that wrote it, the epoch `m19` of `S_q` read in line 19 and the position `π` in the transcript
of the `Ptr.Write(f)` of line 20). -/
structure HE' (n : ℕ) where
  f : Idx n
  s : ℤ
  w : ℕ
  m19 : ℕ
  π : ℕ

/-- The four local queues (`0 = usedQ`, `1 = anncQ`, `2 = hintQ`, `3 = hint'Q`), the counters
`c_p` and the set `free_p`. -/
structure QS (n : ℕ) where
  q : Fin 4 → List (Option (Idx n))
  cnt : Idx n → ℕ
  free : Finset (Idx n)

/-- Lines 47–51 of `updateQ_p(qu, x)`: enqueue `x` if `p` owns it (and count it), else `⊥`. -/
def enq {n : ℕ} (p : Fin n) (o : Fin 4) (x : Option (Idx n)) (s : QS n) : QS n :=
  match x with
  | some y =>
    if y.1 = p then
      { s with q := Function.update s.q o (s.q o ++ [some y]),
               cnt := Function.update s.cnt y (s.cnt y + 1) }
    else { s with q := Function.update s.q o (s.q o ++ [none]) }
  | none => { s with q := Function.update s.q o (s.q o ++ [none]) }

/-- Lines 52–55 of `updateQ_p`: dequeue `y`; if `y ≠ ⊥`, decrement `c_p[y]` and add `y` to
`free_p` if the counter drops to `0`. -/
def deq {n : ℕ} (o : Fin 4) (s : QS n) : QS n :=
  match s.q o with
  | [] => s
  | none :: rest => { s with q := Function.update s.q o rest }
  | some y :: rest =>
    { q := Function.update s.q o rest,
      cnt := Function.update s.cnt y (s.cnt y - 1),
      free := if s.cnt y - 1 = 0 then insert y s.free else s.free }

/-- `updateQ_p(qu_o, x)` (lines 47–55). -/
def upd {n : ℕ} (p : Fin n) (o : Fin 4) (x : Option (Idx n)) (s : QS n) : QS n :=
  deq o (enq p o x s)

variable (n : ℕ) (T : ObjSpec)

/-- Program counters (with the local variables live at that point). -/
inductive PC where
  /-- no pending operation -/
  | idle
  /-- `Write(v)` invoked; next: lines 25–28 (`free.remove()`, `updateQ(usedQ)`, read
  `Annc[ctr]`, `updateQ(anncQ)`) -/
  | w27 (v : T.State)
  /-- next: lines 29–30 -/
  | w29 (v : T.State) (f : Idx n)
  /-- next: lines 31–32 -/
  | w31 (v : T.State) (f : Idx n)
  /-- next: line 13 (invoke `A[f].SWrite(v)`) -/
  | w13 (v : T.State) (f : Idx n)
  /-- `A[f].SWrite(v)` pending -/
  | wSW (v : T.State) (f : Idx n)
  /-- next: line 14 -/
  | w14 (v : T.State) (f : Idx n)
  /-- next: line 15 (`s` read in line 14; ghost `m14`) -/
  | w15 (v : T.State) (f : Idx n) (s : ℤ) (m14 : ℕ)
  /-- next: lines 16–17 -/
  | w16 (v : T.State) (f : Idx n) (s : ℤ) (m14 : ℕ) (olds : Option ℤ)
  /-- next: line 18 (`olds, olds'` kept as ghost values) -/
  | w18 (v : T.State) (f : Idx n) (s : ℤ) (m14 : ℕ) (olds olds' : Option ℤ)
  /-- next: line 19 -/
  | w19 (v : T.State) (f : Idx n)
  /-- next: line 20 (`s'` read in line 19; ghost `m19, τ19`) -/
  | w20 (v : T.State) (f : Idx n) (s' : ℤ) (m19 τ19 : ℕ)
  /-- next: lines 21 and 24 (ghost `π`: position of the `Ptr.Write`) -/
  | w21 (v : T.State) (f : Idx n) (s' : ℤ) (m19 τ19 π : ℕ)
  /-- next: lines 23 and 24 -/
  | w23 (v : T.State) (f : Idx n)
  /-- next: return from `Write(v)` -/
  | wRet (v : T.State)
  /-- `Exec(o)` invoked; next: line 34 -/
  | e34 (o : T.Op)
  /-- next: line 35 -/
  | e35 (o : T.Op) (x : ℕ)
  /-- next: line 36 -/
  | e36 (o : T.Op) (x : ℕ)
  /-- next: line 37 (`i` read from `Ptr`; ghost `g`, `ts`) -/
  | e37 (o : T.Op) (x : ℕ) (i : Option (Idx n)) (g ts : ℕ)
  /-- next: lines 38–39 -/
  | e39 (o : T.Op) (x : ℕ) (i : Option (Idx n)) (g ts : ℕ)
  /-- next: lines 40–42 (`hv = (j, s)` read in line 39) -/
  | e40 (o : T.Op) (x : ℕ) (i : Idx n) (g ts : ℕ) (hv : Option (HE n))
  /-- next: line 43 (invoke `A[i].Oper(o)`) -/
  | e43 (o : T.Op) (x : ℕ) (i : Idx n) (ts : ℕ)
  /-- `A[i].Oper(o)` pending (ghost `t`: position of its invocation) -/
  | eOp (x : ℕ) (i : Idx n) (ts t : ℕ)
  /-- next: line 44 -/
  | e44 (x : ℕ) (r : T.Resp)
  /-- next: line 45 -/
  | e45 (x : ℕ) (r : T.Resp)
  /-- next: return `r` (line 46) -/
  | eRet (r : T.Resp)

/-- The local state of a process. -/
structure Loc where
  pc : PC n T
  ctr : ℕ
  qs : QS n
  /-- ghost -/
  lc : Idx n → ℕ
  /-- ghost -/
  pp : Idx n → Option ℕ
  /-- ghost: number of writes to `S_q` so far -/
  m : ℕ
  /-- ghost -/
  τ35 : ℕ
  /-- ghost -/
  eq : ℕ

/-- A configuration. -/
structure Cfg where
  loc : Fin n → Loc n T
  ptr : Option (Idx n)
  annc : Fin n → Option (Idx n)
  /-- `hH p q` is `H_p[q]` -/
  hH : Fin n → Fin n → Option (HE n)
  /-- `hH' p q` is `H'_p[q]` -/
  hH' : Fin n → Fin n → Option (HE' n)
  S : Fin n → ℤ
  /-- ghost: the transcript so far -/
  tr : List (Ev (Fin n) (Idx n) T)

variable {n T}

/-- The initial queues (`2n+2` copies of `⊥`), counters and `free_p = I_p`. -/
def QS.init (p : Fin n) : QS n where
  q _ := List.replicate (2 * n + 2) none
  cnt _ := 0
  free := Finset.univ.filter fun i : Idx n => i.1 = p

/-- The initial local state. -/
def Loc.init (p : Fin n) : Loc n T where
  pc := .idle
  ctr := 0
  qs := QS.init p
  lc _ := 0
  pp _ := none
  m := 0
  τ35 := 0
  eq := 0

/-- The initial configuration depicted in Figure 4.5. -/
def Cfg.init : Cfg n T where
  loc := Loc.init
  ptr := none
  annc _ := none
  hH _ _ := none
  hH' _ _ := none
  S _ := -1
  tr := []

/-- Replace the local state of `p`. -/
abbrev Cfg.setLoc (c : Cfg n T) (p : Fin n) (l : Loc n T) : Cfg n T :=
  { c with loc := Function.update c.loc p l }

/-- Whether `Exec` uses the hint (line 41): `hv = (j, s)`, `hv' = (j', s')` and
`s = s' = x ∧ j = j'`. -/
def HintOK (x : ℕ) (hv : Option (HE n)) (hv' : Option (HE' n)) : Prop :=
  ∃ h h', hv = some h ∧ hv' = some h' ∧ h.s = x ∧ h'.s = x ∧ h.f = h'.f

variable [NeZero n]

/-- One step of the algorithm (Figure 4.5). -/
inductive Step (W : Writable T) : Cfg n T → Cfg n T → Prop
  /-- invocation of `Write(v)` -/
  | winv (c : Cfg n T) (p : Fin n) (v : T.State) (h : (c.loc p).pc = .idle) :
      Step W c { c.setLoc p { c.loc p with pc := .w27 v } with tr := c.tr ++ [.winv p v] }
  /-- lines 12, 25–28: `f := free.remove()`, `updateQ(usedQ, f)`, `a := Annc[ctr].Read()`,
  `updateQ(anncQ, a)` -/
  | rec27 (c : Cfg n T) (p : Fin n) (v : T.State) (f : Idx n) (h : (c.loc p).pc = .w27 v)
      (hf : f ∈ (c.loc p).qs.free) :
      Step W c (c.setLoc p { c.loc p with
        pc := .w29 v f
        qs := upd p 1 (c.annc (cq (c.loc p).ctr))
                (upd p 0 (some f) { (c.loc p).qs with free := (c.loc p).qs.free.erase f })
        lc := Function.update (c.loc p).lc f (c.loc p).ctr
        pp := Function.update (c.loc p).pp f none })
  /-- lines 29–30 -/
  | rec29 (c : Cfg n T) (p : Fin n) (v : T.State) (f : Idx n) (h : (c.loc p).pc = .w29 v f) :
      Step W c (c.setLoc p { c.loc p with
        pc := .w31 v f
        qs := upd p 2 ((c.hH p (cq (c.loc p).ctr)).map HE.f) (c.loc p).qs })
  /-- lines 31–33 -/
  | rec31 (c : Cfg n T) (p : Fin n) (v : T.State) (f : Idx n) (h : (c.loc p).pc = .w31 v f) :
      Step W c (c.setLoc p { c.loc p with
        pc := .w13 v f
        qs := upd p 3 ((c.hH' p (cq (c.loc p).ctr)).map HE'.f) (c.loc p).qs })
  /-- line 13: invoke `A[f].SWrite(v)` -/
  | swinv (c : Cfg n T) (p : Fin n) (v : T.State) (f : Idx n) (h : (c.loc p).pc = .w13 v f) :
      Step W c { c.setLoc p { c.loc p with pc := .wSW v f } with
        tr := c.tr ++ [.swinv p f v] }
  /-- response of `A[f].SWrite(v)` (arbitrary response `r`) -/
  | swret (c : Cfg n T) (p : Fin n) (v : T.State) (f : Idx n) (r : T.Resp)
      (h : (c.loc p).pc = .wSW v f) :
      Step W c { c.setLoc p { c.loc p with pc := .w14 v f } with
        tr := c.tr ++ [.aret p f r] }
  /-- line 14: `s := S_ctr.Read()` -/
  | l14 (c : Cfg n T) (p : Fin n) (v : T.State) (f : Idx n) (h : (c.loc p).pc = .w14 v f) :
      Step W c (c.setLoc p { c.loc p with
        pc := .w15 v f (c.S (cq (c.loc p).ctr)) (c.loc (cq (c.loc p).ctr)).m })
  /-- line 15: `(·, olds) := H_p[ctr].Read()` -/
  | l15 (c : Cfg n T) (p : Fin n) (v : T.State) (f : Idx n) (s : ℤ) (m14 : ℕ)
      (h : (c.loc p).pc = .w15 v f s m14) :
      Step W c (c.setLoc p { c.loc p with
        pc := .w16 v f s m14 ((c.hH p (cq (c.loc p).ctr)).map HE.s) })
  /-- lines 16–17, case `s ≠ olds ∨ s ≠ olds'` -/
  | l16w (c : Cfg n T) (p : Fin n) (v : T.State) (f : Idx n) (s : ℤ) (m14 : ℕ)
      (olds : Option ℤ) (h : (c.loc p).pc = .w16 v f s m14 olds)
      (hc : some s ≠ olds ∨ some s ≠ (c.hH' p (cq (c.loc p).ctr)).map HE'.s) :
      Step W c (c.setLoc p { c.loc p with
        pc := .w18 v f s m14 olds ((c.hH' p (cq (c.loc p).ctr)).map HE'.s) })
  /-- lines 16–17, case `s = olds = olds'` -/
  | l16s (c : Cfg n T) (p : Fin n) (v : T.State) (f : Idx n) (s : ℤ) (m14 : ℕ)
      (olds : Option ℤ) (h : (c.loc p).pc = .w16 v f s m14 olds)
      (hc : ¬ (some s ≠ olds ∨ some s ≠ (c.hH' p (cq (c.loc p).ctr)).map HE'.s)) :
      Step W c (c.setLoc p { c.loc p with pc := .w23 v f })
  /-- line 18: `H_p[ctr].Write(f, s)` -/
  | l18 (c : Cfg n T) (p : Fin n) (v : T.State) (f : Idx n) (s : ℤ) (m14 : ℕ)
      (olds olds' : Option ℤ) (h : (c.loc p).pc = .w18 v f s m14 olds olds') :
      Step W c { c.setLoc p { c.loc p with pc := .w19 v f } with
        hH := Function.update c.hH p (Function.update (c.hH p) (cq (c.loc p).ctr)
          (some ⟨f, s, (c.loc p).ctr, m14, (c.loc (cq (c.loc p).ctr)).m⟩)) }
  /-- line 19: `s' := S_ctr.Read()` -/
  | l19 (c : Cfg n T) (p : Fin n) (v : T.State) (f : Idx n) (h : (c.loc p).pc = .w19 v f) :
      Step W c (c.setLoc p { c.loc p with
        pc := .w20 v f (c.S (cq (c.loc p).ctr)) (c.loc (cq (c.loc p).ctr)).m c.tr.length })
  /-- line 20: `Ptr.Write(f)` -/
  | l20 (c : Cfg n T) (p : Fin n) (v : T.State) (f : Idx n) (s' : ℤ) (m19 τ19 : ℕ)
      (h : (c.loc p).pc = .w20 v f s' m19 τ19) :
      Step W c { c.setLoc p { c.loc p with
          pc := .w21 v f s' m19 τ19 c.tr.length
          pp := Function.update (c.loc p).pp f (some c.tr.length) } with
        ptr := some f
        tr := c.tr ++ [.ptr p f] }
  /-- lines 21 and 24: `H'_p[ctr].Write(f, s')`, `ctr := ctr + 1` -/
  | l21 (c : Cfg n T) (p : Fin n) (v : T.State) (f : Idx n) (s' : ℤ) (m19 τ19 π : ℕ)
      (h : (c.loc p).pc = .w21 v f s' m19 τ19 π) :
      Step W c { c.setLoc p { c.loc p with pc := .wRet v, ctr := (c.loc p).ctr + 1 } with
        hH' := Function.update c.hH' p (Function.update (c.hH' p) (cq (c.loc p).ctr)
          (some ⟨f, s', (c.loc p).ctr, m19, π⟩)) }
  /-- lines 23 and 24: `Ptr.Write(f)`, `ctr := ctr + 1` -/
  | l23 (c : Cfg n T) (p : Fin n) (v : T.State) (f : Idx n) (h : (c.loc p).pc = .w23 v f) :
      Step W c { c.setLoc p { c.loc p with
          pc := .wRet v
          ctr := (c.loc p).ctr + 1
          pp := Function.update (c.loc p).pp f (some c.tr.length) } with
        ptr := some f
        tr := c.tr ++ [.ptr p f] }
  /-- return from `Write(v)` -/
  | wret (c : Cfg n T) (p : Fin n) (v : T.State) (h : (c.loc p).pc = .wRet v) :
      Step W c { c.setLoc p { c.loc p with pc := .idle } with
        tr := c.tr ++ [.hret p (W.wresp v)] }
  /-- invocation of `Exec(o)` for a non-write operation `o` -/
  | einv (c : Cfg n T) (q : Fin n) (o : T.Op) (ho : ∀ v, o ≠ W.wr v)
      (h : (c.loc q).pc = .idle) :
      Step W c { c.setLoc q { c.loc q with pc := .e34 o, eq := c.tr.length } with
        tr := c.tr ++ [.einv q o] }
  /-- line 34: `x := (S_q.Read() + 1) mod 2n` -/
  | l34 (c : Cfg n T) (q : Fin n) (o : T.Op) (h : (c.loc q).pc = .e34 o) :
      Step W c (c.setLoc q { c.loc q with
        pc := .e35 o ((c.S q + 1) % (2 * n : ℤ)).toNat })
  /-- line 35: `S_q.Write(x)` -/
  | l35 (c : Cfg n T) (q : Fin n) (o : T.Op) (x : ℕ) (h : (c.loc q).pc = .e35 o x) :
      Step W c { c.setLoc q { c.loc q with
          pc := .e36 o x, m := (c.loc q).m + 1, τ35 := c.tr.length } with
        S := Function.update c.S q x }
  /-- line 36: `i := Ptr.Read()` -/
  | l36 (c : Cfg n T) (q : Fin n) (o : T.Op) (x : ℕ) (h : (c.loc q).pc = .e36 o x) :
      Step W c (c.setLoc q { c.loc q with
        pc := .e37 o x c.ptr ((c.ptr.map fun i => (c.loc i.1).ctr).getD 0) c.tr.length })
  /-- line 37: `Annc[q].Write(i)` -/
  | l37 (c : Cfg n T) (q : Fin n) (o : T.Op) (x : ℕ) (i : Option (Idx n)) (g ts : ℕ)
      (h : (c.loc q).pc = .e37 o x i g ts) :
      Step W c { c.setLoc q { c.loc q with pc := .e39 o x i g ts } with
        annc := Function.update c.annc q i }
  /-- lines 38–39: `p := owner(i)`, `(j, s) := H_p[q].Read()` -/
  | l39 (c : Cfg n T) (q : Fin n) (o : T.Op) (x : ℕ) (i : Idx n) (g ts : ℕ)
      (h : (c.loc q).pc = .e39 o x (some i) g ts) :
      Step W c (c.setLoc q { c.loc q with pc := .e40 o x i g ts (c.hH i.1 q) })
  /-- lines 40–42, the hint is used: `i := j` -/
  | l40h (c : Cfg n T) (q : Fin n) (o : T.Op) (x : ℕ) (i : Idx n) (g ts : ℕ) (hv : Option (HE n))
      (h : (c.loc q).pc = .e40 o x i g ts hv) (hb : HE n) (hb' : HE' n)
      (h1 : hv = some hb) (h2 : c.hH' i.1 q = some hb') (h3 : hb.s = x) (h4 : hb'.s = x)
      (h5 : hb.f = hb'.f) :
      Step W c (c.setLoc q { c.loc q with pc := .e43 o x hb.f (hb'.π + 1) })
  /-- lines 40–41, the hint is not used -/
  | l40d (c : Cfg n T) (q : Fin n) (o : T.Op) (x : ℕ) (i : Idx n) (g ts : ℕ) (hv : Option (HE n))
      (h : (c.loc q).pc = .e40 o x i g ts hv) (hn : ¬ HintOK x hv (c.hH' i.1 q)) :
      Step W c (c.setLoc q { c.loc q with pc := .e43 o x i ts })
  /-- line 43: invoke `A[i].Oper(o)` -/
  | opinv (c : Cfg n T) (q : Fin n) (o : T.Op) (x : ℕ) (i : Idx n) (ts : ℕ)
      (h : (c.loc q).pc = .e43 o x i ts) :
      Step W c { c.setLoc q { c.loc q with pc := .eOp x i ts c.tr.length } with
        tr := c.tr ++ [.opinv q i o] }
  /-- response of `A[i].Oper(o)` (arbitrary response `r`) -/
  | opret (c : Cfg n T) (q : Fin n) (x : ℕ) (i : Idx n) (ts t : ℕ) (r : T.Resp)
      (h : (c.loc q).pc = .eOp x i ts t) :
      Step W c { c.setLoc q { c.loc q with pc := .e44 x r } with
        tr := c.tr ++ [.aret q i r] }
  /-- line 44: `H_{x mod n}[q].Write(⊥, ⊥)` -/
  | l44 (c : Cfg n T) (q : Fin n) (x : ℕ) (r : T.Resp) (h : (c.loc q).pc = .e44 x r) :
      Step W c { c.setLoc q { c.loc q with pc := .e45 x r } with
        hH := Function.update c.hH (cq x) (Function.update (c.hH (cq x)) q none) }
  /-- line 45: `H'_{x mod n}[q].Write(⊥, ⊥)` -/
  | l45 (c : Cfg n T) (q : Fin n) (x : ℕ) (r : T.Resp) (h : (c.loc q).pc = .e45 x r) :
      Step W c { c.setLoc q { c.loc q with pc := .eRet r } with
        hH' := Function.update c.hH' (cq x) (Function.update (c.hH' (cq x)) q none) }
  /-- line 46: return `r` -/
  | eret (c : Cfg n T) (q : Fin n) (r : T.Resp) (h : (c.loc q).pc = .eRet r) :
      Step W c { c.setLoc q { c.loc q with pc := .idle } with
        tr := c.tr ++ [.hret q r] }

/-- Configurations reachable from `c₀`. -/
inductive ReachFrom (W : Writable T) (c₀ : Cfg n T) : Cfg n T → Prop
  | refl : ReachFrom W c₀ c₀
  | step {c c' : Cfg n T} : ReachFrom W c₀ c → Step W c c' → ReachFrom W c₀ c'

/-- Configurations reachable from the initial configuration of Figure 4.5. -/
abbrev Reach (W : Writable T) (c : Cfg n T) : Prop := ReachFrom W Cfg.init c

/-- The configurations obtained from the depicted initial configuration by a complete solo
`Write(v0)` of process `0`: the initial state of the object (p. 48 of the thesis). Its
transcript consists of the five events of that `Write`. -/
def Initialized (W : Writable T) (v0 : T.State) (c : Cfg n T) : Prop :=
  Reach W c ∧ (∀ p, (c.loc p).pc = .idle) ∧
    ∃ f r, c.tr = [.winv ⟨0, Nat.pos_of_neZero n⟩ v0, .swinv ⟨0, Nat.pos_of_neZero n⟩ f v0,
      .aret ⟨0, Nat.pos_of_neZero n⟩ f r, .ptr ⟨0, Nat.pos_of_neZero n⟩ f,
      .hret ⟨0, Nat.pos_of_neZero n⟩ (W.wresp v0)]

/-- An execution in the sense of the paper: the solo initial `Write(v0)` of process `0`,
followed by an arbitrary sequence of steps. -/
def IsExecution (W : Writable T) (v0 : T.State) (c : Cfg n T) : Prop :=
  ∃ c₁, Initialized W v0 c₁ ∧ ReachFrom W c₁ c

end Podc.WritableObjects.WF
