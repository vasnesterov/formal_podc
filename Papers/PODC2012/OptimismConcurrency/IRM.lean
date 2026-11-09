import Papers.PODC2012.OptimismConcurrency.Observable

/-!
# The optimistic implementation `I_RM` (Algorithm 1)

Every object `X_ℓ` (a location `ℓ`) has three base objects: `t-var[ℓ]` (the node), `r[ℓ]`
(marked for deletion) and `L[ℓ]` (version number and locked flag, with `read`, `write`, `cas`).
Process `p` keeps a rotating buffer `rbuf` of its last two successful reads (object, version).

The model (`RStep`) executes every shared-memory access of Algorithm 1 as one atomic step, in
any interleaving. To make the impossibility result below as strong as possible, the model
*over-approximates* `I_RM`:
* the client is arbitrary: any process without a pending read/write may invoke any high-level
  operation, any read, any write, or return anything (the real client runs `LL`);
* the initial content of `t-var` is arbitrary;
* when a `cas` of line 22/25/35 fails, the write may either return `⊥` (pseudocode) or retry the
  `cas` with the current version (the refinement described in the text of §6);
* a write of an `insert` to an object that is not in `rbuf` (the new node, whose allocation
  Algorithm 1 does not show) is a plain store followed by `ok`; a write of a `remove` to an object
  not in `rbuf`, or with no other object in `rbuf`, returns `⊥`.
Writes of `contains` (never issued by `LL`) are treated like writes of `insert`.

Ghost data (not influencing the behaviour): the read stage stores the deletion flag `g` of the
object at the invocation; the stages of a `remove` write store `ℓ'` (line 24).
-/

namespace Podc.OptimismConcurrency

/-- Stages of `read(X_ℓ)` (lines 11–18). -/
inductive RdSt
  /-- before line 11 -/
  | l11
  /-- before line 12, `ver₁` read -/
  | l12 (v1 : ℕ)
  /-- before line 13 -/
  | l13 (v1 : ℕ) (val : NodeV)
  /-- before line 14 -/
  | l14 (v1 : ℕ) (val : NodeV) (f : Bool)
  /-- about to return `res` (`none` = `⊥`) -/
  | fin (v1 : ℕ) (res : Option NodeV)

/-- Stages of `write(X_ℓ, v)` executed by `remove` (lines 20–31). -/
inductive RmSt
  /-- line 22, with the version of `X_ℓ` from `rbuf` -/
  | l22 (ver : ℕ)
  /-- line 25: `ℓ' = z` with version `vz` -/
  | l25 (ver : ℕ) (z : Loc) (vz : ℕ)
  | l27 (ver : ℕ) (z : Loc) (vz : ℕ)
  | l28 (ver : ℕ) (z : Loc) (vz : ℕ)
  | l29 (ver : ℕ) (z : Loc) (vz : ℕ)
  | l30 (ver : ℕ) (z : Loc) (vz : ℕ)
  /-- line 31: return `ok` -/
  | ok (z : Loc)
  /-- return `⊥` -/
  | fail

/-- Stages of `write(X_ℓ, v)` executed by `insert` (lines 33–39). -/
inductive InsSt
  | l35 (ver : ℕ)
  | l37 (ver : ℕ)
  | l38 (ver : ℕ)
  | ok
  | fail

/-- The pending implemented read or write of a process. -/
inductive RPc
  /-- `read(X_y)`; `g` is a ghost: `r[y]` at the invocation -/
  | rd (y : Loc) (g : Bool) (s : RdSt)
  /-- write of a `remove` -/
  | rm (y : Loc) (n : NodeV) (s : RmSt)
  /-- write of an `insert` -/
  | ins (y : Loc) (n : NodeV) (s : InsSt)
  /-- allocation of a new node (plain store, then `ok`) -/
  | alc (y : Loc) (n : NodeV) (stored : Bool)

/-- Local state of a process. -/
structure RLoc where
  /-- current high-level operation -/
  kind : Option SetOp
  /-- rotating buffer, newest first -/
  rbuf : List (Loc × ℕ)
  /-- pending read or write -/
  pc : Option RPc

/-- Configuration of `I_RM`. -/
structure RCfg where
  tvar : Loc → NodeV
  rf : Loc → Bool
  lk : Loc → ℕ × Bool
  loc : ℕ → RLoc

/-- Initial configuration (arbitrary initial `t-var`). -/
def rcfg0 (tv : Loc → NodeV) : RCfg := ⟨tv, fun _ => false, fun _ => (0, false), fun _ => ⟨none, [], none⟩⟩

/-- Replace the local state of `p`. -/
def RCfg.setLoc (c : RCfg) (p : ℕ) (l : RLoc) : RCfg := { c with loc := Function.update c.loc p l }

/-- Replace the pending operation of `p`. -/
def RCfg.setPc (c : RCfg) (p : ℕ) (q : Option RPc) : RCfg := c.setLoc p { c.loc p with pc := q }

/-- The first stage of an implemented write (lines 20–21, 33–34). -/
def wstart (l : RLoc) (y : Loc) (n : NodeV) : RPc :=
  match l.kind with
  | some (.remove _) =>
    match l.rbuf.lookup y with
    | some ver => .rm y n (.l22 ver)
    | none => .rm y n .fail
  | _ =>
    match l.rbuf.lookup y with
    | some ver => .ins y n (.l35 ver)
    | none => .alc y n false

/-- One step of `I_RM`: an event (`some e`) or an internal shared-memory access (`none`). -/
inductive RStep : RCfg → Option (LEv ℕ) → RCfg → Prop
  | inv (c : RCfg) (p : ℕ) (o : SetOp) (h : (c.loc p).pc = none) :
      RStep c (some (.inv p () o)) (c.setLoc p { c.loc p with kind := some o })
  | res (c : RCfg) (p : ℕ) (r : Bool) (h : (c.loc p).pc = none) :
      RStep c (some (.res p () r)) c
  | rinv (c : RCfg) (p : ℕ) (y : Loc) (h : (c.loc p).pc = none) :
      RStep c (some (.rinv p () y)) (c.setPc p (some (.rd y (c.rf y) .l11)))
  | winv (c : RCfg) (p : ℕ) (y : Loc) (n : NodeV) (h : (c.loc p).pc = none) :
      RStep c (some (.winv p () y n)) (c.setPc p (some (wstart (c.loc p) y n)))
  -- read (lines 11–18)
  | r11 (c : RCfg) (p : ℕ) (y : Loc) (g : Bool) (h : (c.loc p).pc = some (.rd y g .l11)) :
      RStep c none (c.setPc p (some (.rd y g (.l12 (c.lk y).1))))
  | r12 (c : RCfg) (p : ℕ) (y : Loc) (g : Bool) (v1 : ℕ)
      (h : (c.loc p).pc = some (.rd y g (.l12 v1))) :
      RStep c none (c.setPc p (some (.rd y g (.l13 v1 (c.tvar y)))))
  | r13 (c : RCfg) (p : ℕ) (y : Loc) (g : Bool) (v1 : ℕ) (val : NodeV)
      (h : (c.loc p).pc = some (.rd y g (.l13 v1 val))) :
      RStep c none (c.setPc p (some (.rd y g (.l14 v1 val (c.rf y)))))
  | r14 (c : RCfg) (p : ℕ) (y : Loc) (g : Bool) (v1 : ℕ) (val : NodeV) (f : Bool)
      (h : (c.loc p).pc = some (.rd y g (.l14 v1 val f))) :
      RStep c none (c.setPc p (some (.rd y g
        (.fin v1 (if v1 ≠ (c.lk y).1 ∨ f = true then none else some val)))))
  | rret (c : RCfg) (p : ℕ) (y : Loc) (g : Bool) (v1 : ℕ) (res : Option NodeV)
      (h : (c.loc p).pc = some (.rd y g (.fin v1 res))) :
      RStep c (some (.rres p () res)) (c.setLoc p { c.loc p with
        rbuf := if res.isSome then (y, v1) :: (c.loc p).rbuf.take 1 else (c.loc p).rbuf,
        pc := none })
  -- write of a remove (lines 20–31)
  | m22ok (c : RCfg) (p : ℕ) (y : Loc) (n : NodeV) (ver : ℕ) (z : Loc) (vz : ℕ)
      (h : (c.loc p).pc = some (.rm y n (.l22 ver))) (hl : c.lk y = (ver, false))
      (hz : (c.loc p).rbuf.find? (fun e => decide (e.1 ≠ y)) = some (z, vz)) :
      RStep c none ({ c with lk := Function.update c.lk y (ver, true) }.setPc p
        (some (.rm y n (.l25 ver z vz))))
  | m22noz (c : RCfg) (p : ℕ) (y : Loc) (n : NodeV) (ver : ℕ)
      (h : (c.loc p).pc = some (.rm y n (.l22 ver))) (hl : c.lk y = (ver, false))
      (hz : (c.loc p).rbuf.find? (fun e => decide (e.1 ≠ y)) = none) :
      RStep c none ({ c with lk := Function.update c.lk y (ver, true) }.setPc p
        (some (.rm y n .fail)))
  | m22fail (c : RCfg) (p : ℕ) (y : Loc) (n : NodeV) (ver : ℕ)
      (h : (c.loc p).pc = some (.rm y n (.l22 ver))) (hl : c.lk y ≠ (ver, false)) :
      RStep c none (c.setPc p (some (.rm y n .fail)))
  | m22retry (c : RCfg) (p : ℕ) (y : Loc) (n : NodeV) (ver : ℕ)
      (h : (c.loc p).pc = some (.rm y n (.l22 ver))) (hl : c.lk y ≠ (ver, false)) :
      RStep c none (c.setPc p (some (.rm y n (.l22 (c.lk y).1))))
  | m25ok (c : RCfg) (p : ℕ) (y : Loc) (n : NodeV) (ver : ℕ) (z : Loc) (vz : ℕ)
      (h : (c.loc p).pc = some (.rm y n (.l25 ver z vz))) (hl : c.lk z = (vz, false)) :
      RStep c none ({ c with lk := Function.update c.lk z (vz, true) }.setPc p
        (some (.rm y n (.l27 ver z vz))))
  | m25fail (c : RCfg) (p : ℕ) (y : Loc) (n : NodeV) (ver : ℕ) (z : Loc) (vz : ℕ)
      (h : (c.loc p).pc = some (.rm y n (.l25 ver z vz))) (hl : c.lk z ≠ (vz, false)) :
      RStep c none (c.setPc p (some (.rm y n .fail)))
  | m25retry (c : RCfg) (p : ℕ) (y : Loc) (n : NodeV) (ver : ℕ) (z : Loc) (vz : ℕ)
      (h : (c.loc p).pc = some (.rm y n (.l25 ver z vz))) (hl : c.lk z ≠ (vz, false)) :
      RStep c none (c.setPc p (some (.rm y n (.l25 ver z (c.lk z).1))))
  | m27 (c : RCfg) (p : ℕ) (y : Loc) (n : NodeV) (ver : ℕ) (z : Loc) (vz : ℕ)
      (h : (c.loc p).pc = some (.rm y n (.l27 ver z vz))) :
      RStep c none ({ c with rf := Function.update c.rf z true }.setPc p
        (some (.rm y n (.l28 ver z vz))))
  | m28 (c : RCfg) (p : ℕ) (y : Loc) (n : NodeV) (ver : ℕ) (z : Loc) (vz : ℕ)
      (h : (c.loc p).pc = some (.rm y n (.l28 ver z vz))) :
      RStep c none ({ c with tvar := Function.update c.tvar y n }.setPc p
        (some (.rm y n (.l29 ver z vz))))
  | m29 (c : RCfg) (p : ℕ) (y : Loc) (n : NodeV) (ver : ℕ) (z : Loc) (vz : ℕ)
      (h : (c.loc p).pc = some (.rm y n (.l29 ver z vz))) :
      RStep c none ({ c with lk := Function.update c.lk y (ver + 1, false) }.setPc p
        (some (.rm y n (.l30 ver z vz))))
  | m30 (c : RCfg) (p : ℕ) (y : Loc) (n : NodeV) (ver : ℕ) (z : Loc) (vz : ℕ)
      (h : (c.loc p).pc = some (.rm y n (.l30 ver z vz))) :
      RStep c none ({ c with lk := Function.update c.lk z (vz + 1, false) }.setPc p
        (some (.rm y n (.ok z))))
  | mok (c : RCfg) (p : ℕ) (y : Loc) (n : NodeV) (z : Loc)
      (h : (c.loc p).pc = some (.rm y n (.ok z))) :
      RStep c (some (.wres p () true)) (c.setPc p none)
  | mfail (c : RCfg) (p : ℕ) (y : Loc) (n : NodeV) (h : (c.loc p).pc = some (.rm y n .fail)) :
      RStep c (some (.wres p () false)) (c.setPc p none)
  -- write of an insert (lines 33–39)
  | i35ok (c : RCfg) (p : ℕ) (y : Loc) (n : NodeV) (ver : ℕ)
      (h : (c.loc p).pc = some (.ins y n (.l35 ver))) (hl : c.lk y = (ver, false)) :
      RStep c none ({ c with lk := Function.update c.lk y (ver, true) }.setPc p
        (some (.ins y n (.l37 ver))))
  | i35fail (c : RCfg) (p : ℕ) (y : Loc) (n : NodeV) (ver : ℕ)
      (h : (c.loc p).pc = some (.ins y n (.l35 ver))) (hl : c.lk y ≠ (ver, false)) :
      RStep c none (c.setPc p (some (.ins y n .fail)))
  | i35retry (c : RCfg) (p : ℕ) (y : Loc) (n : NodeV) (ver : ℕ)
      (h : (c.loc p).pc = some (.ins y n (.l35 ver))) (hl : c.lk y ≠ (ver, false)) :
      RStep c none (c.setPc p (some (.ins y n (.l35 (c.lk y).1))))
  | i37 (c : RCfg) (p : ℕ) (y : Loc) (n : NodeV) (ver : ℕ)
      (h : (c.loc p).pc = some (.ins y n (.l37 ver))) :
      RStep c none ({ c with tvar := Function.update c.tvar y n }.setPc p
        (some (.ins y n (.l38 ver))))
  | i38 (c : RCfg) (p : ℕ) (y : Loc) (n : NodeV) (ver : ℕ)
      (h : (c.loc p).pc = some (.ins y n (.l38 ver))) :
      RStep c none ({ c with lk := Function.update c.lk y (ver + 1, false) }.setPc p
        (some (.ins y n .ok)))
  | iok (c : RCfg) (p : ℕ) (y : Loc) (n : NodeV) (h : (c.loc p).pc = some (.ins y n .ok)) :
      RStep c (some (.wres p () true)) (c.setPc p none)
  | ifail (c : RCfg) (p : ℕ) (y : Loc) (n : NodeV) (h : (c.loc p).pc = some (.ins y n .fail)) :
      RStep c (some (.wres p () false)) (c.setPc p none)
  -- allocation of a new node
  | a1 (c : RCfg) (p : ℕ) (y : Loc) (n : NodeV) (h : (c.loc p).pc = some (.alc y n false)) :
      RStep c none ({ c with tvar := Function.update c.tvar y n }.setPc p (some (.alc y n true)))
  | aok (c : RCfg) (p : ℕ) (y : Loc) (n : NodeV) (h : (c.loc p).pc = some (.alc y n true)) :
      RStep c (some (.wres p () true)) (c.setPc p none)

/-- Executions of `I_RM` (labels in order). -/
inductive RRun (c₀ : RCfg) : List (Option (LEv ℕ)) → RCfg → Prop
  | nil : RRun c₀ [] c₀
  | snoc {c c' : RCfg} {L : List (Option (LEv ℕ))} {l : Option (LEv ℕ)} :
      RRun c₀ L c → RStep c l c' → RRun c₀ (L ++ [l]) c'

/-- **`I_RM`**: the set of histories exported by executions of Algorithm 1 (over-approximated as
explained in the module docstring). -/
def IRM : Set (LHist ℕ) :=
  {H | ∃ tv L c, RRun (rcfg0 tv) L c ∧ L.filterMap id = H}

end Podc.OptimismConcurrency
