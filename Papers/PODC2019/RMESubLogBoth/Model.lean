import Mathlib

/-!
# The `k`-ported recoverable mutual exclusion algorithm of Jayanti, Jayanti and Joshi (PODC 2019)

Prasad Jayanti, Siddhartha Jayanti, Anup Joshi. *A Recoverable Mutex Algorithm with
Sub-logarithmic RMR on Both CC and DSM.* PODC 2019 (arXiv 1904.02124v2), Figures 3–4.

```
Shared: Tail (init &SpecialNode), Node[0..k-1] (init NIL);
        QNode = {Pred, NonNil_Signal, CS_Signal}; SpecialNode.Pred = &Exit, both signals 1.
Try:  10 if Node[p] = NIL then 11 mynode ← new QNode  12 Node[p] ← mynode
                               13 mypred ← FAS(Tail, mynode)  14 mynode.Pred ← mypred
                               15 mynode.NonNil_Signal.set()
      16 else 17 mynode ← Node[p]  18 if mynode.Pred = NIL then mynode.Pred ← &Crash
              19 mypred ← mynode.Pred  20 if mypred = &InCS then go to CS
              21 if mypred = &Exit then 22 execute lines 28–29 and go to line 10
              23 mynode.NonNil_Signal.set()  24 execute RLock
      25 mypred.CS_Signal.wait()  26 mynode.Pred ← &InCS
Exit: 27 mynode.Pred ← &Exit  28 mynode.CS_Signal.set()  29 Node[p] ← NIL
CS of RLock:
      30 if mypred ≠ &Crash then go to Exit section of RLock
      31 tail ← Tail; V ← ∅; E ← ∅; tailpath ← NIL; headpath ← NIL
      32 for i ← 0 to k-1: 33 cur ← Node[i]  34 if cur = NIL then continue
            35 cur.NonNil_Signal.wait()  36 curpred ← cur.Pred
            37 if curpred ∈ {&Crash,&InCS,&Exit} then V ← V ∪ {cur}
            38 else V ← V ∪ {cur, curpred}; E ← E ∪ {(cur, curpred)}
      39 Paths ← maximal paths of (V,E)   40 mypath ← the path containing mynode
      41 if tail ∈ V then tailpath ← the path containing tail
      42 for each σ ∈ Paths: 43 if end(σ).Pred ∈ {&InCS,&Exit} then
                              44 if start(σ).Pred ≠ &Exit then 45 headpath ← σ
      46 if tailpath = NIL ∨ end(tailpath).Pred ∈ {&InCS,&Exit} then
      47     mypred ← FAS(Tail, start(mypath))
      48 else if headpath ≠ NIL then mypred ← start(headpath) else mypred ← &SpecialNode
      49 mynode.Pred ← mypred
```

## Model

* `k` ports `Fin k`, one process per port. The paper has `n ≥ k` processes, at most one per port
  during a super-passage; a process only ever accesses `Node[p]` of its own port `p`, its local
  variables are wiped at every crash, and between two super-passages of a port it is in the
  remainder section, so the identity of the process using a port does not matter for the
  properties formalized here.
* Node references are natural numbers; `0` is `SpecialNode`; `nxt` is the next fresh address
  (`new QNode` returns `nxt`). The pseudo-nodes `&Crash`, `&InCS`, `&Exit` and `NIL` are the
  constructors of `PV` (the values of a `Pred` field).
* Signal objects are atomic bits: `set()` is one write, `wait()` busy-waits on the bit (one read
  per step). Theorem 1 (the implementation of Figure 2) is treated separately in `Signal.lean`.
* `RLock` is abstract: a lock variable `holder`. Line 24 acquires it when it is free or already
  held by the caller (critical-section re-entry after a crash); otherwise the step is a busy-wait.
  The exit of `RLock` frees it. This allows every order of entries, so the safety results hold
  for every mutual exclusion lock with critical-section re-entry; starvation freedom of `RLock`
  is a fairness assumption on runs.
* Every step performs at most one shared-memory access (or one `RLock` operation) together with
  the local computation that follows it. Lines 11–12 (allocation and the write of `Node[p]`)
  form one step; lines 16–17 are merged into line 10 (both read `Node[p]`, which only `p` writes).
* Lines 39–41 and the order of the loop at line 42 are nondeterministic (`Step` is a relation):
  every maximal path containing `mynode` (resp. `tail`) may be chosen, and the loop may visit the
  maximal paths in any order. Results are proved for all resolutions.
* A crash resets the local state: the program counter goes to line 10 (`l10`); the shared
  memory (NVM) and the `RLock` state are unaffected.
-/

namespace Podc.RMESubLogBoth

/-- Values of a `Pred` field (and of `mypred`): `NIL`, the three distinguished nodes, or a
reference to a `QNode`. -/
inductive PV where
  | nil
  | crash
  | incs
  | exit
  | node (a : ℕ)
  deriving DecidableEq

/-- Address of `SpecialNode`. -/
abbrev special : ℕ := 0

/-- Program counters with the local variables. `my` is `mynode`, `mp` is `mypred`. -/
inductive PC (k : ℕ) where
  /-- remainder section (line 10, idle) -/
  | rem
  /-- line 10 after a crash or after line 22 (the process must take steps) -/
  | l10
  /-- lines 11–12: allocate a node and write it to `Node[p]` -/
  | l11
  /-- line 13: `mypred ← FAS(Tail, mynode)` -/
  | l13 (my : ℕ)
  /-- line 14: `mynode.Pred ← mypred` -/
  | l14 (my mp : ℕ)
  /-- line 15: `mynode.NonNil_Signal.set()` -/
  | l15 (my mp : ℕ)
  /-- line 18: read `mynode.Pred` -/
  | l18 (my : ℕ)
  /-- line 18: `mynode.Pred ← &Crash` -/
  | l18w (my : ℕ)
  /-- line 19: `mypred ← mynode.Pred` (lines 20–21 are local) -/
  | l19 (my : ℕ)
  /-- line 22 (line 28): `mynode.CS_Signal.set()` -/
  | l22a (my : ℕ)
  /-- line 22 (line 29): `Node[p] ← NIL` -/
  | l22b
  /-- line 23: `mynode.NonNil_Signal.set()` -/
  | l23 (my : ℕ) (mp : PV)
  /-- line 24: acquire `RLock` -/
  | l24 (my : ℕ) (mp : PV)
  /-- line 30 (in the CS of `RLock`): test `mypred` -/
  | l30 (my : ℕ) (mp : PV)
  /-- line 31: `tail ← Tail` -/
  | l31 (my : ℕ)
  /-- line 33 (loop of line 32 at index `i`; `i = k` ends the loop) -/
  | l33 (my tl : ℕ) (V : Finset ℕ) (E : Finset (ℕ × ℕ)) (i : ℕ)
  /-- line 35: `cur.NonNil_Signal.wait()` -/
  | l35 (my tl : ℕ) (V : Finset ℕ) (E : Finset (ℕ × ℕ)) (i cur : ℕ)
  /-- line 36: `curpred ← cur.Pred` (lines 37–38 are local) -/
  | l36 (my tl : ℕ) (V : Finset ℕ) (E : Finset (ℕ × ℕ)) (i cur : ℕ)
  /-- lines 39–41 (local): choose `mypath` and `tailpath` -/
  | l39 (my tl : ℕ) (V : Finset ℕ) (E : Finset (ℕ × ℕ))
  /-- line 42: choose the next maximal path (`done`: the paths already visited) -/
  | l42 (my tl : ℕ) (V : Finset ℕ) (E : Finset (ℕ × ℕ)) (mpath : List ℕ)
      (tpath hpath : Option (List ℕ)) (done : List (List ℕ))
  /-- line 43: read `end(σ).Pred` -/
  | l43 (my tl : ℕ) (V : Finset ℕ) (E : Finset (ℕ × ℕ)) (mpath : List ℕ)
      (tpath hpath : Option (List ℕ)) (done : List (List ℕ)) (σ : List ℕ)
  /-- line 44: read `start(σ).Pred` -/
  | l44 (my tl : ℕ) (V : Finset ℕ) (E : Finset (ℕ × ℕ)) (mpath : List ℕ)
      (tpath hpath : Option (List ℕ)) (done : List (List ℕ)) (σ : List ℕ)
  /-- line 46: read `end(tailpath).Pred` (line 48 is local) -/
  | l46 (my tl : ℕ) (V : Finset ℕ) (E : Finset (ℕ × ℕ)) (mpath : List ℕ)
      (tpath hpath : Option (List ℕ))
  /-- line 47: `mypred ← FAS(Tail, start(mypath))` -/
  | l47 (my s : ℕ)
  /-- line 49: `mynode.Pred ← mypred` -/
  | l49 (my mp : ℕ)
  /-- exit section of `RLock` -/
  | rx (my : ℕ) (mp : PV)
  /-- line 25: `mypred.CS_Signal.wait()` -/
  | l25 (my : ℕ) (mp : PV)
  /-- line 26: `mynode.Pred ← &InCS` -/
  | l26 (my : ℕ)
  /-- critical section; its step is line 27: `mynode.Pred ← &Exit` -/
  | cs (my : ℕ)
  /-- line 28: `mynode.CS_Signal.set()` -/
  | l28 (my : ℕ)
  /-- line 29: `Node[p] ← NIL` -/
  | l29

/-- Configurations. -/
structure Cfg (k : ℕ) where
  /-- `Tail` -/
  tail : ℕ
  /-- `Node[0..k-1]` (`none` is `NIL`) -/
  node : Fin k → Option ℕ
  /-- `Pred` fields -/
  pred : ℕ → PV
  /-- `NonNil_Signal` states -/
  nn : ℕ → Bool
  /-- `CS_Signal` states -/
  csig : ℕ → Bool
  /-- next fresh address -/
  nxt : ℕ
  /-- the process holding `RLock` (in its critical section, possibly crashed there) -/
  holder : Option (Fin k)
  /-- program counters with local variables -/
  pc : Fin k → PC k

variable {k : ℕ}

/-- The initial configuration. -/
def Cfg.init : Cfg k where
  tail := special
  node _ := none
  pred a := if a = special then .exit else .nil
  nn a := a = special
  csig a := a = special
  nxt := 1
  holder := none
  pc _ := .rem

/-! ### Graphs and maximal paths (lines 37–48) -/

/-- `σ` is a path of the graph `(V, E)`: nonempty, all vertices in `V`, consecutive vertices
joined by an edge. A path is listed from its `start` to its `end`. -/
def IsPath (V : Finset ℕ) (E : Finset (ℕ × ℕ)) (σ : List ℕ) : Prop :=
  σ ≠ [] ∧ (∀ v ∈ σ, v ∈ V) ∧ σ.IsChain (fun u v => (u, v) ∈ E)

/-- `σ` is a maximal path: a path that cannot be extended at either end. -/
def IsMaxPath (V : Finset ℕ) (E : Finset (ℕ × ℕ)) (σ : List ℕ) : Prop :=
  IsPath V E σ ∧ (∀ u, (u, σ.headD 0) ∉ E) ∧ (∀ w, (σ.getLastD 0, w) ∉ E)

/-- `start(σ)` -/
def pstart (σ : List ℕ) : ℕ := σ.headD 0

/-- `end(σ)` -/
def pend (σ : List ℕ) : ℕ := σ.getLastD 0

/-- Line 48: `start(headpath)`, or `&SpecialNode` if `headpath = NIL`. -/
def hstart : Option (List ℕ) → ℕ
  | some σ => pstart σ
  | none => special

/-- Lines 37–38: the graph after reading `curpred` of `cur`. -/
def addV (V : Finset ℕ) (cur : ℕ) (v : PV) : Finset ℕ :=
  match v with
  | .node d => insert cur (insert d V)
  | _ => insert cur V

/-- Lines 37–38: the edges after reading `curpred` of `cur`. -/
def addE (E : Finset (ℕ × ℕ)) (cur : ℕ) (v : PV) : Finset (ℕ × ℕ) :=
  match v with
  | .node d => insert (cur, d) E
  | _ => E

/-- `v ∈ {&InCS, &Exit}` -/
def PV.isInOut : PV → Bool
  | .incs | .exit => true
  | _ => false

/-! ### Steps -/

/-- Update the program counter of `p`. -/
def Cfg.setPc (c : Cfg k) (p : Fin k) (q : PC k) : Cfg k := { c with pc := Function.update c.pc p q }

/-- One (normal) step of process `p`, as a relation (the only nondeterminism is at lines 39–42). -/
inductive Step : Cfg k → Fin k → Cfg k → Prop
  /-- line 10 (from the remainder section or after a crash), `Node[p] = NIL` -/
  | l10_nil (c : Cfg k) (p : Fin k) (h : c.pc p = .rem ∨ c.pc p = .l10) (hn : c.node p = none) :
      Step c p (c.setPc p .l11)
  /-- lines 10, 16–17: `Node[p] ≠ NIL` -/
  | l10_some (c : Cfg k) (p : Fin k) (h : c.pc p = .rem ∨ c.pc p = .l10) (x : ℕ)
      (hn : c.node p = some x) : Step c p (c.setPc p (.l18 x))
  /-- lines 11–12 -/
  | l11 (c : Cfg k) (p : Fin k) (h : c.pc p = .l11) :
      Step c p { c with node := Function.update c.node p (some c.nxt), nxt := c.nxt + 1,
                        pc := Function.update c.pc p (.l13 c.nxt) }
  /-- line 13 -/
  | l13 (c : Cfg k) (p : Fin k) (x : ℕ) (h : c.pc p = .l13 x) :
      Step c p { c with tail := x, pc := Function.update c.pc p (.l14 x c.tail) }
  /-- line 14 -/
  | l14 (c : Cfg k) (p : Fin k) (x m : ℕ) (h : c.pc p = .l14 x m) :
      Step c p { c with pred := Function.update c.pred x (.node m),
                        pc := Function.update c.pc p (.l15 x m) }
  /-- line 15 -/
  | l15 (c : Cfg k) (p : Fin k) (x m : ℕ) (h : c.pc p = .l15 x m) :
      Step c p { c with nn := Function.update c.nn x true,
                        pc := Function.update c.pc p (.l25 x (.node m)) }
  /-- line 18 (read) -/
  | l18 (c : Cfg k) (p : Fin k) (x : ℕ) (h : c.pc p = .l18 x) :
      Step c p (c.setPc p (if c.pred x = .nil then .l18w x else .l19 x))
  /-- line 18 (write) -/
  | l18w (c : Cfg k) (p : Fin k) (x : ℕ) (h : c.pc p = .l18w x) :
      Step c p { c with pred := Function.update c.pred x .crash,
                        pc := Function.update c.pc p (.l19 x) }
  /-- lines 19–21 -/
  | l19 (c : Cfg k) (p : Fin k) (x : ℕ) (h : c.pc p = .l19 x) :
      Step c p (c.setPc p (match c.pred x with
        | .incs => .cs x
        | .exit => .l22a x
        | v => .l23 x v))
  /-- line 22 (line 28) -/
  | l22a (c : Cfg k) (p : Fin k) (x : ℕ) (h : c.pc p = .l22a x) :
      Step c p { c with csig := Function.update c.csig x true,
                        pc := Function.update c.pc p .l22b }
  /-- line 22 (line 29), then go to line 10 -/
  | l22b (c : Cfg k) (p : Fin k) (h : c.pc p = .l22b) :
      Step c p { c with node := Function.update c.node p none, pc := Function.update c.pc p .l10 }
  /-- line 23 -/
  | l23 (c : Cfg k) (p : Fin k) (x : ℕ) (v : PV) (h : c.pc p = .l23 x v) :
      Step c p { c with nn := Function.update c.nn x true,
                        pc := Function.update c.pc p (.l24 x v) }
  /-- line 24: `RLock` is free or held by `p`: enter its CS -/
  | l24_acq (c : Cfg k) (p : Fin k) (x : ℕ) (v : PV) (h : c.pc p = .l24 x v)
      (hl : c.holder = none ∨ c.holder = some p) :
      Step c p { c with holder := some p, pc := Function.update c.pc p (.l30 x v) }
  /-- line 24: `RLock` is held by another process: busy-wait -/
  | l24_wait (c : Cfg k) (p : Fin k) (x : ℕ) (v : PV) (h : c.pc p = .l24 x v) (q : Fin k)
      (hl : c.holder = some q) (hq : q ≠ p) : Step c p c
  /-- line 30 -/
  | l30 (c : Cfg k) (p : Fin k) (x : ℕ) (v : PV) (h : c.pc p = .l30 x v) :
      Step c p (c.setPc p (if v = .crash then .l31 x else .rx x v))
  /-- line 31 -/
  | l31 (c : Cfg k) (p : Fin k) (x : ℕ) (h : c.pc p = .l31 x) :
      Step c p (c.setPc p (.l33 x c.tail ∅ ∅ 0))
  /-- lines 32–34: `i < k` -/
  | l33 (c : Cfg k) (p : Fin k) (x tl : ℕ) (V : Finset ℕ) (E : Finset (ℕ × ℕ)) (i : ℕ)
      (h : c.pc p = .l33 x tl V E i) (hi : i < k) :
      Step c p (c.setPc p (match c.node ⟨i, hi⟩ with
        | none => .l33 x tl V E (i + 1)
        | some a => .l35 x tl V E i a))
  /-- line 32: end of the loop -/
  | l33_end (c : Cfg k) (p : Fin k) (x tl : ℕ) (V : Finset ℕ) (E : Finset (ℕ × ℕ)) (i : ℕ)
      (h : c.pc p = .l33 x tl V E i) (hi : k ≤ i) : Step c p (c.setPc p (.l39 x tl V E))
  /-- line 35 -/
  | l35 (c : Cfg k) (p : Fin k) (x tl : ℕ) (V : Finset ℕ) (E : Finset (ℕ × ℕ)) (i a : ℕ)
      (h : c.pc p = .l35 x tl V E i a) :
      Step c p (c.setPc p (if c.nn a then .l36 x tl V E i a else .l35 x tl V E i a))
  /-- lines 36–38 -/
  | l36 (c : Cfg k) (p : Fin k) (x tl : ℕ) (V : Finset ℕ) (E : Finset (ℕ × ℕ)) (i a : ℕ)
      (h : c.pc p = .l36 x tl V E i a) :
      Step c p (c.setPc p (.l33 x tl (addV V a (c.pred a)) (addE E a (c.pred a)) (i + 1)))
  /-- lines 39–41 -/
  | l39 (c : Cfg k) (p : Fin k) (x tl : ℕ) (V : Finset ℕ) (E : Finset (ℕ × ℕ))
      (h : c.pc p = .l39 x tl V E) (mpath : List ℕ) (hm : IsMaxPath V E mpath ∧ x ∈ mpath)
      (tpath : Option (List ℕ))
      (ht : (tl ∈ V → ∃ τ, tpath = some τ ∧ IsMaxPath V E τ ∧ tl ∈ τ) ∧
        (tl ∉ V → tpath = none)) :
      Step c p (c.setPc p (.l42 x tl V E mpath tpath none []))
  /-- line 42: visit a maximal path not visited yet -/
  | l42_next (c : Cfg k) (p : Fin k) (x tl : ℕ) (V : Finset ℕ) (E : Finset (ℕ × ℕ))
      (mpath : List ℕ) (tpath hpath : Option (List ℕ)) (done : List (List ℕ))
      (h : c.pc p = .l42 x tl V E mpath tpath hpath done) (σ : List ℕ)
      (hσ : IsMaxPath V E σ) (hσd : σ ∉ done) :
      Step c p (c.setPc p (.l43 x tl V E mpath tpath hpath (σ :: done) σ))
  /-- line 42: all maximal paths visited -/
  | l42_end (c : Cfg k) (p : Fin k) (x tl : ℕ) (V : Finset ℕ) (E : Finset (ℕ × ℕ))
      (mpath : List ℕ) (tpath hpath : Option (List ℕ)) (done : List (List ℕ))
      (h : c.pc p = .l42 x tl V E mpath tpath hpath done)
      (hall : ∀ σ, IsMaxPath V E σ → σ ∈ done) :
      Step c p (c.setPc p (.l46 x tl V E mpath tpath hpath))
  /-- line 43 -/
  | l43 (c : Cfg k) (p : Fin k) (x tl : ℕ) (V : Finset ℕ) (E : Finset (ℕ × ℕ))
      (mpath : List ℕ) (tpath hpath : Option (List ℕ)) (done : List (List ℕ)) (σ : List ℕ)
      (h : c.pc p = .l43 x tl V E mpath tpath hpath done σ) :
      Step c p (c.setPc p (if (c.pred (pend σ)).isInOut then .l44 x tl V E mpath tpath hpath done σ
        else .l42 x tl V E mpath tpath hpath done))
  /-- lines 44–45 -/
  | l44 (c : Cfg k) (p : Fin k) (x tl : ℕ) (V : Finset ℕ) (E : Finset (ℕ × ℕ))
      (mpath : List ℕ) (tpath hpath : Option (List ℕ)) (done : List (List ℕ)) (σ : List ℕ)
      (h : c.pc p = .l44 x tl V E mpath tpath hpath done σ) :
      Step c p (c.setPc p (.l42 x tl V E mpath tpath
        (if c.pred (pstart σ) ≠ .exit then some σ else hpath) done))
  /-- line 46, first disjunct (`tailpath = NIL`) -/
  | l46_none (c : Cfg k) (p : Fin k) (x tl : ℕ) (V : Finset ℕ) (E : Finset (ℕ × ℕ))
      (mpath : List ℕ) (hpath : Option (List ℕ)) (h : c.pc p = .l46 x tl V E mpath none hpath) :
      Step c p (c.setPc p (.l47 x (pstart mpath)))
  /-- lines 46–48: read `end(tailpath).Pred` -/
  | l46_some (c : Cfg k) (p : Fin k) (x tl : ℕ) (V : Finset ℕ) (E : Finset (ℕ × ℕ))
      (mpath τ : List ℕ) (hpath : Option (List ℕ)) (h : c.pc p = .l46 x tl V E mpath (some τ) hpath) :
      Step c p (c.setPc p (if (c.pred (pend τ)).isInOut then .l47 x (pstart mpath)
        else .l49 x (hstart hpath)))
  /-- line 47 -/
  | l47 (c : Cfg k) (p : Fin k) (x s : ℕ) (h : c.pc p = .l47 x s) :
      Step c p { c with tail := s, pc := Function.update c.pc p (.l49 x c.tail) }
  /-- line 49 -/
  | l49 (c : Cfg k) (p : Fin k) (x m : ℕ) (h : c.pc p = .l49 x m) :
      Step c p { c with pred := Function.update c.pred x (.node m),
                        pc := Function.update c.pc p (.rx x (.node m)) }
  /-- exit section of `RLock` -/
  | rx (c : Cfg k) (p : Fin k) (x : ℕ) (v : PV) (h : c.pc p = .rx x v) :
      Step c p { c with holder := none, pc := Function.update c.pc p (.l25 x v) }
  /-- line 25 -/
  | l25 (c : Cfg k) (p : Fin k) (x : ℕ) (v : PV) (h : c.pc p = .l25 x v) :
      Step c p (c.setPc p (match v with
        | .node m => if c.csig m then .l26 x else .l25 x v
        | _ => .l25 x v))
  /-- line 26 -/
  | l26 (c : Cfg k) (p : Fin k) (x : ℕ) (h : c.pc p = .l26 x) :
      Step c p { c with pred := Function.update c.pred x .incs,
                        pc := Function.update c.pc p (.cs x) }
  /-- line 27 (the step of a process in the CS) -/
  | cs (c : Cfg k) (p : Fin k) (x : ℕ) (h : c.pc p = .cs x) :
      Step c p { c with pred := Function.update c.pred x .exit,
                        pc := Function.update c.pc p (.l28 x) }
  /-- line 28 -/
  | l28 (c : Cfg k) (p : Fin k) (x : ℕ) (h : c.pc p = .l28 x) :
      Step c p { c with csig := Function.update c.csig x true,
                        pc := Function.update c.pc p .l29 }
  /-- line 29 -/
  | l29 (c : Cfg k) (p : Fin k) (h : c.pc p = .l29) :
      Step c p { c with node := Function.update c.node p none, pc := Function.update c.pc p .rem }

/-- A crash of `p`: its local state is lost and its program counter is reset to line 10. -/
def Cfg.crash (c : Cfg k) (p : Fin k) : Cfg k := c.setPc p .l10

/-- Events. -/
inductive Ev (k : ℕ) where
  | step (p : Fin k)
  | crash (p : Fin k)
  deriving DecidableEq

/-- The transition relation for an event. -/
def Next (c : Cfg k) : Ev k → Cfg k → Prop
  | .step p, c' => Step c p c'
  | .crash p, c' => c' = c.crash p

/-- Reachable configurations. -/
inductive Reach : Cfg k → Prop
  | init : Reach Cfg.init
  | next {c c' : Cfg k} (e : Ev k) : Reach c → Next c e c' → Reach c'

/-- A run: an infinite sequence of configurations and events, starting in the initial
configuration. -/
structure Run (k : ℕ) where
  /-- configuration after `t` events -/
  cfg : ℕ → Cfg k
  /-- the `t`-th event -/
  ev : ℕ → Ev k
  init : cfg 0 = Cfg.init
  next : ∀ t, Next (cfg t) (ev t) (cfg (t + 1))

lemma Run.reach (r : Run k) (t : ℕ) : Reach (r.cfg t) := by
  induction t with
  | zero => rw [r.init]; exact .init
  | succ t ih => exact .next _ ih (r.next t)

/-! ### Sections -/

/-- `p` is in the critical section. -/
def Cfg.InCS (c : Cfg k) (p : Fin k) : Prop := ∃ x, c.pc p = .cs x

end Podc.RMESubLogBoth
