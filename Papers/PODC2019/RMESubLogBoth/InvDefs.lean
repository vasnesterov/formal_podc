import Papers.PODC2019.RMESubLogBoth.Graph

/-!
# The invariant (definitions)

Our own inductive invariant for the algorithm of Figures 3–4 (the paper's Lemma 9 invariant is
false as stated, see `PaperInv.lean`).

Central notions:
* `vp q`: the *virtual predecessor* of port `q`: `mypred` while `q` is between the `FAS` and the
  write of `Pred` (lines 14 and 49), otherwise `Node[q].Pred`.
* `Bh y z`: the node `y` of some port is behind `z` (`vp = z`).
* `Rel z`: `z` is released (`Pred = &Exit` and `CS_Signal = 1`).
* `InH y`: `y` holds the right to the CS: it is in the CS (`&InCS`), behind a released node, or
  exiting (`&Exit`, signal not yet set) with a successor (or as `Tail`). At most one node is in
  `InH` (`Glob.hUniq`), which gives mutual exclusion.
* The repairer (the process in the CS of `RLock`) keeps facts about its partial view `(V, E)`
  of the queue. They mention the ghost set `EA` of *early* nodes: nodes that existed and had
  executed their `FAS` when the repairer read `Tail` (line 31). Nodes outside `EA` are *late*:
  they all hang behind the node `tail` read at line 31.
-/

namespace Podc.RMESubLogBoth

variable {k : ℕ}

/-- `mypred` overrides `Node[q].Pred` at lines 14 and 49. -/
def PC.ovr : PC k → Option ℕ
  | .l14 _ m => some m
  | .l49 _ m => some m
  | _ => none

/-- The virtual predecessor of port `q`. -/
def Cfg.vp (c : Cfg k) (q : Fin k) : PV :=
  match (c.pc q).ovr with
  | some m => .node m
  | none => match c.node q with
    | some y => c.pred y
    | none => .nil

/-- `y` is the node of some port. -/
def Cfg.Act (c : Cfg k) (y : ℕ) : Prop := ∃ q, c.node q = some y

/-- The node `y` of some port has virtual predecessor `z`. -/
def Cfg.Bh (c : Cfg k) (y z : ℕ) : Prop := ∃ q, c.node q = some y ∧ c.vp q = .node z

/-- `z` is released. -/
def Cfg.Rel (c : Cfg k) (z : ℕ) : Prop := c.pred z = .exit ∧ c.csig z = true

/-- `y` holds the right to the critical section. -/
def Cfg.InH (c : Cfg k) (y : ℕ) : Prop :=
  c.Act y ∧ (c.pred y = .incs ∨ (∃ z, c.Bh y z ∧ c.Rel z) ∨
    (c.pred y = .exit ∧ c.csig y = false ∧ ((∃ w, c.Bh w y) ∨ c.tail = y)))

/-- Program counters inside the critical section of `RLock` (lines 30–49 and its exit). -/
def PC.InR : PC k → Prop
  | .l30 _ _ | .l31 _ | .l33 _ _ _ _ _ | .l35 _ _ _ _ _ _ | .l36 _ _ _ _ _ _ | .l39 _ _ _ _
  | .l42 _ _ _ _ _ _ _ _ | .l43 _ _ _ _ _ _ _ _ _ | .l44 _ _ _ _ _ _ _ _ _
  | .l46 _ _ _ _ _ _ _ | .l47 _ _ | .l49 _ _ | .rx _ _ => True
  | _ => False

/-- The repairer's view after line 46 decides for the attach branch (line 48). -/
def AttachBr (c : Cfg k) (tpath : Option (List ℕ)) : Prop :=
  ∃ τ, tpath = some τ ∧ (c.pred (pend τ)).isInOut = false

/-- Facts about the repairer `q` (node `x`) during the scan (`i` = indices scanned so far). -/
structure ScanInv (c : Cfg k) (own : ℕ → ℕ) (q : Fin k) (x tl : ℕ) (V : Finset ℕ)
    (E : Finset (ℕ × ℕ)) (i : ℕ) (EA : Set ℕ) : Prop where
  tlEA : tl ∈ EA
  xEA : x ∈ EA
  EAlt : ∀ a ∈ EA, a < c.nxt
  tail : c.tail = tl ∨ c.tail ∉ EA
  bhLate : ∀ a b, c.Bh a b → a ∉ EA → b = tl ∨ b ∉ EA
  bhEarly : ∀ a b, c.Bh a b → a ∈ EA → b ∈ EA
  lateIO : ∀ a, a ∉ EA → (c.pred a = .incs ∨ c.pred a = .exit) → c.pred tl = .exit
  l13Late : ∀ j a, c.pc j = .l13 a → a ∉ EA
  Vlt : ∀ v ∈ V, v < c.nxt
  Vl13 : ∀ v ∈ V, ∀ j, c.pc j ≠ .l13 v
  Esrc : ∀ u v, (u, v) ∈ E → u ∈ V
  Etgt : ∀ u v, (u, v) ∈ E → v ∈ V
  E1 : ∀ u v, (u, v) ∈ E →
    c.pred u = .node v ∨ ((c.pred u = .incs ∨ c.pred u = .exit) ∧ c.Rel v)
  E2 : ∀ u v w, (u, v) ∈ E → c.Bh w v → w = u
  Etail : ∀ u v, (u, v) ∈ E → v ≠ c.tail
  El13 : ∀ u v j, (u, v) ∈ E → c.pc j ≠ .l13 v
  Ein : ∀ u u' v, (u, v) ∈ E → (u', v) ∈ E → u = u'
  Eown : ∀ u v, (u, v) ∈ E → own u < i
  Eout : ∀ u v v', (u, v) ∈ E → (u, v') ∈ E → v = v'
  EEA : ∀ u v, (u, v) ∈ E → u ∈ EA → v ∈ EA
  Eacyc : ∀ u, ¬ Relation.TransGen (EdgeR E) u u
  scanned : ∀ j : Fin k, j.val < i → ∀ a, c.node j = some a →
    a ∉ EA ∨ (a ∈ V ∧ c.nn a = true ∧ ∀ v, c.vp j = .node v → (a, v) ∈ E)

/-- Facts after the scan, while the loop of lines 42–45 runs and at line 46.
`done'` are the visited paths whose test is complete. -/
structure PathInv (c : Cfg k) (x tl : ℕ) (V : Finset ℕ) (E : Finset (ℕ × ℕ)) (EA : Set ℕ)
    (mpath : List ℕ) (tpath hpath : Option (List ℕ)) (done' : List (List ℕ)) : Prop where
  mp : IsMaxPath V E mpath ∧ x ∈ mpath
  tpIn : tl ∈ V → ∃ τ, tpath = some τ ∧ IsMaxPath V E τ ∧ tl ∈ τ
  tpOut : tl ∉ V → tpath = none
  hp : ∀ σ, hpath = some σ → IsMaxPath V E σ ∧ (c.pred (pend σ)).isInOut = true ∧
    (AttachBr c tpath → c.pred (pstart σ) = .exit → ∀ y, ¬ c.InH y)
  visited : hpath = none → ∀ σ ∈ done', IsMaxPath V E σ → pend σ ∈ EA →
    (c.pred (pend σ)).isInOut = true → c.pred (pstart σ) = .exit

/-- Local invariant of port `q`, by program counter. -/
def LI (c : Cfg k) (own : ℕ → ℕ) (q : Fin k) : Prop :=
  match c.pc q with
  | .rem => c.node q = none
  | .l10 => True
  | .l11 => c.node q = none
  | .l13 y => c.node q = some y ∧ c.pred y = .nil ∧ c.nn y = false ∧ c.csig y = false ∧
      (∀ w, ¬ c.Bh w y) ∧ c.tail ≠ y
  | .l14 y _ => c.node q = some y ∧ c.pred y = .nil ∧ c.nn y = false ∧ c.csig y = false
  | .l15 y m => c.node q = some y ∧ c.pred y = .node m ∧ c.nn y = false ∧ c.csig y = false
  | .l18 y => c.node q = some y
  | .l18w y => c.node q = some y ∧ c.pred y = .nil
  | .l19 y => c.node q = some y ∧ c.pred y ≠ .nil
  | .l22a y => c.node q = some y ∧ c.pred y = .exit
  | .l22b => ∃ y, c.node q = some y ∧ c.Rel y
  | .l23 y v => c.node q = some y ∧ c.pred y = v ∧ (v = .crash ∨ ∃ m, v = .node m)
  | .l24 y v => c.node q = some y ∧ c.pred y = v ∧ (v = .crash ∨ ∃ m, v = .node m) ∧
      c.nn y = true
  | .l30 y v => c.node q = some y ∧ c.pred y = v ∧ (v = .crash ∨ ∃ m, v = .node m) ∧
      c.nn y = true
  | .l31 y => c.node q = some y ∧ c.pred y = .crash ∧ c.nn y = true
  | .l33 y tl V E i => c.node q = some y ∧ c.pred y = .crash ∧ c.nn y = true ∧ i ≤ k ∧
      ∃ EA, ScanInv c own q y tl V E i EA
  | .l35 y tl V E i a => c.node q = some y ∧ c.pred y = .crash ∧ c.nn y = true ∧ i < k ∧
      ∃ EA, ScanInv c own q y tl V E i EA ∧ own a = i ∧ a < c.nxt ∧
        ∀ b, (h : i < k) → c.node ⟨i, h⟩ = some b → b ∈ EA → b = a
  | .l36 y tl V E i a => c.node q = some y ∧ c.pred y = .crash ∧ c.nn y = true ∧ i < k ∧
      ∃ EA, ScanInv c own q y tl V E i EA ∧ own a = i ∧ a < c.nxt ∧ c.nn a = true ∧
        ∀ b, (h : i < k) → c.node ⟨i, h⟩ = some b → b ∈ EA → b = a
  | .l39 y tl V E => c.node q = some y ∧ c.pred y = .crash ∧ c.nn y = true ∧
      ∃ EA, ScanInv c own q y tl V E k EA
  | .l42 y tl V E mpath tpath hpath done => c.node q = some y ∧ c.pred y = .crash ∧
      c.nn y = true ∧ ∃ EA, ScanInv c own q y tl V E k EA ∧
        PathInv c y tl V E EA mpath tpath hpath done
  | .l43 y tl V E mpath tpath hpath done σ => c.node q = some y ∧ c.pred y = .crash ∧
      c.nn y = true ∧ ∃ EA, ScanInv c own q y tl V E k EA ∧
        PathInv c y tl V E EA mpath tpath hpath done.tail ∧ done.head? = some σ ∧
        IsMaxPath V E σ
  | .l44 y tl V E mpath tpath hpath done σ => c.node q = some y ∧ c.pred y = .crash ∧
      c.nn y = true ∧ ∃ EA, ScanInv c own q y tl V E k EA ∧
        PathInv c y tl V E EA mpath tpath hpath done.tail ∧ done.head? = some σ ∧
        IsMaxPath V E σ ∧ (c.pred (pend σ)).isInOut = true
  | .l46 y tl V E mpath tpath hpath => c.node q = some y ∧ c.pred y = .crash ∧
      c.nn y = true ∧ ∃ EA, ScanInv c own q y tl V E k EA ∧
        PathInv c y tl V E EA mpath tpath hpath [] ∧
        (AttachBr c tpath → hpath = none → ∀ w, ¬ c.InH w)
  | .l47 y s => c.node q = some y ∧ c.pred y = .crash ∧ c.nn y = true ∧
      (∀ w, ¬ c.Bh w s) ∧ c.tail ≠ s ∧ s < c.nxt ∧ (∀ j, c.pc j ≠ .l13 s) ∧
      ¬ Relation.ReflTransGen c.Bh c.tail y ∧
      Relation.ReflTransGen (fun a b => c.pred a = .node b) s y
  | .l49 y _ => c.node q = some y ∧ c.pred y = .crash ∧ c.nn y = true
  | .rx y v => c.node q = some y ∧ c.pred y = v ∧ (∃ m, v = .node m) ∧ c.nn y = true
  | .l25 y v => c.node q = some y ∧ c.pred y = v ∧ (∃ m, v = .node m) ∧ c.nn y = true
  | .l26 y => c.node q = some y ∧ (∃ m, c.pred y = .node m ∧ c.Rel m) ∧ c.nn y = true
  | .cs y => c.node q = some y ∧ c.pred y = .incs ∧ c.nn y = true
  | .l28 y => c.node q = some y ∧ c.pred y = .exit ∧ c.csig y = false ∧ c.nn y = true
  | .l29 => ∃ y, c.node q = some y ∧ c.Rel y

/-- Global invariant (with the ghost `own`: the port that allocated a node). -/
structure Glob (c : Cfg k) (own : ℕ → ℕ) : Prop where
  own : ∀ q a, c.node q = some a → own a = q.val
  nodeLt : ∀ q a, c.node q = some a → 0 < a ∧ a < c.nxt
  fresh : ∀ a, c.nxt ≤ a → c.pred a = .nil ∧ c.nn a = false ∧ c.csig a = false
  special : c.pred special = .exit ∧ c.csig special = true ∧ c.nn special = true
  nxtPos : 0 < c.nxt
  table : ∀ a, 0 < a → a < c.nxt → c.Act a ∨ c.Rel a
  nnPred : ∀ a, c.nn a = true → c.pred a ≠ .nil
  csigPred : ∀ a, c.csig a = true → c.pred a = .exit
  ioNN : ∀ a, (c.pred a = .incs ∨ c.pred a = .exit) → c.nn a = true
  tailLt : c.tail < c.nxt
  bhLt : ∀ y z, c.Bh y z → z < c.nxt
  bhInj : ∀ y y' z, c.Bh y z → c.Bh y' z → y = y'
  noBhTail : ∀ y, ¬ c.Bh y c.tail
  hUniq : ∀ y y', c.InH y → c.InH y' → y = y'
  relTail : c.Rel c.tail → ∀ y, ¬ c.InH y
  wf : WellFounded (flip c.Bh)
  holder : ∀ q, (c.pc q).InR → c.holder = some q

/-- The invariant. -/
def Inv (c : Cfg k) : Prop := ∃ own, Glob c own ∧ ∀ q, LI c own q

end Podc.RMESubLogBoth
