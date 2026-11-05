import Papers.PODC2023.DuraCAS.AModel
import Papers.PODC2023.DuraCAS.ALin

/-!
# The local invariant of the A-level proof (Appendix A.3, Lemmas A.28–A.41)

The invariant is stated on small records:
* `KV` — the *view* of one DuraCAS object `k`: the EC objects `W = (k, W)` and `Z = (k, Z)`, and
  the ghost variables of `k`: `pw` (the id of the installed write that is not yet moved), `zAt`
  (`Z.seq` at the time of that install), `lm` (the last change of `Z` was a move, not an
  imprint), `sig` (the value of `k` in the ghost linearization);
* `PV` — a busy process: program counter, operation, orphan, `DETECT` value of its critical
  handle, the CAS/WRITE witness step `wit`, and whether its operation is linearized (`inL`).

`KV.Inv` is the per-object invariant (Corollary A.33: `W.bit ≠ Z.bit` iff an install is pending;
Lemma A.38; Lemma A.44.1 `O.val = Z.val`), `Loc p v x` the per-process invariant. The three kinds
of changes of an object (install, move, imprint — Lemma A.29) are the relations `Inst`, `Move`,
`Impr`; the frame lemmas `loc_inst`, `loc_move`, `loc_impr` show that `Loc` of every process is
preserved by such a change made by another process.
-/

namespace Podc.DuraCAS

set_option linter.unusedSectionVars false

variable {P K V : Type} [DecidableEq P] [DecidableEq K] [DecidableEq V]

variable (V) in
/-- The view of one DuraCAS object (EC objects `W`, `Z` and the ghost variables of the object). -/
structure KV where
  W : Cell V
  Z : Cell V
  pw : Option ℕ
  zAt : ℕ
  lm : Bool
  sig : V

/-- An install is pending (`W.bit ≠ Z.bit`). -/
def KV.pend (v : KV V) : Prop := v.W.2.2 ≠ v.Z.2.2

/-- Per-object invariant. -/
structure KV.Inv (v : KV V) : Prop where
  pend_iff : v.pend ↔ v.pw ≠ none
  a38 : v.pend → v.lm = true → v.W.2.1 ≠ v.Z.2.1
  zAt_le : v.zAt ≤ v.Z.1
  sig_eq : v.sig = v.Z.2.1

variable (P K V) in
/-- The local view of a busy process. -/
structure PV where
  pc : APc V
  r : OpRec K V
  orph : Option (Orph P K V)
  ls : ℕ
  wit : Option ℕ
  inL : Prop

/-- `c` is a snapshot of the current cell `cur` (sequence numbers grow at every change). -/
def Snap (c cur : Cell V) : Prop := c.1 ≤ cur.1 ∧ (c.1 = cur.1 → c = cur)

/-- Second `TRANSFER-WRITE` of `WRITE` or `RECOVER`. -/
def Ret.st2 : Ret V → Prop
  | .wr2 => True
  | .rec2 => True
  | _ => False

/-- The operation is a `WRITE`. -/
def IsWr (op : Op V) : Prop := ∃ u, op = .write u

/-- A running write still needs a move: it installed and was not moved, or it is a hitchhiker
that saw no move since its invocation. -/
def needW (v : KV V) (x : PV P K V) : Prop :=
  v.pw = some x.r.id ∨ (x.ls = x.r.d1 ∧ x.wit = none)

/-- A recovering operation still needs a move: it installed and was not moved. -/
def needR (v : KV V) (x : PV P K V) : Prop := v.pw = some x.r.id

/-- Generic clauses of `TRANSFER-WRITE` (Lemmas A.28.2, A.34.2, A.35.1). -/
def TwGen (v : KV V) : APc V → Prop
  | .at (.tw20 _ zh) => Snap zh v.Z
  | .at (.tw21 _ zh wh) => Snap zh v.Z ∧ wh.2.2 ≠ zh.2.2 ∧ (v.Z.1 = zh.1 → v.W = wh ∧ v.pend)
  | _ => True

/-- Progress of a write that needs a move through its two transfers (Lemma A.36). -/
def Stage (v : KV V) (need s2 : Prop) : APc V → Prop
  | .at (.tw19 _) => (need → v.pend) ∧ (s2 → need → v.zAt < v.Z.1)
  | .at (.tw20 _ zh) => (need → v.pend) ∧ (need → (s2 → v.zAt < zh.1 ∧ v.Z = zh) ∧ v.zAt ≤ zh.1)
  | .at (.tw21 _ zh _) => (need → v.pend) ∧ (need → (s2 → v.zAt < zh.1 ∧ v.Z = zh) ∧ v.zAt ≤ zh.1)
  | .aft (.tw21 _ _ _) _ => (s2 → ¬need) ∧ (need → v.pend ∧ v.zAt < v.Z.1)
  | _ => True

/-- A `CAS(old, new)` between its read of `z` at line 7 and its `ECSC` at line 10
(Lemma A.39: the iteration-2 `ECSC` can fail only after `Z.val ≠ old` at some time). -/
def CasMid (v : KV V) (x : PV P K V) (old new : V) (i : Bool) (z : Cell V) : Prop :=
  x.ls = x.r.d1 ∧ z.2.1 = old ∧ old ≠ new ∧ Snap z v.Z ∧
    (x.wit = none → if i then v.lm = true ∧ v.Z.1 = z.1 else (v.Z.1 ≠ z.1 → v.lm = true))

/-- Extra clauses of the transfer called by `CAS` with `z`. -/
def CasTw (v : KV V) (z : Cell V) : APc V → Prop
  | .at (.tw20 _ zh) => z.1 ≤ zh.1
  | .at (.tw21 _ zh _) => z.1 ≤ zh.1
  | .aft (.tw21 _ _ _) _ => z.1 < v.Z.1
  | _ => True

/-- Clauses of a process inside `TRANSFER-WRITE` with return address `r`. -/
def TwOK (v : KV V) (x : PV P K V) (r : Ret V) (pc : APc V) : Prop :=
  TwGen v pc ∧
  match r with
  | .casT i z => ∃ old new, x.r.op = .cas old new ∧ CasMid v x old new i z ∧ CasTw v z pc
  | .wr1 => IsWr x.r.op ∧ Stage v (needW v x) False pc
  | .wr2 => IsWr x.r.op ∧ Stage v (needW v x) True pc
  | .rec1 => Stage v (needR v x) False pc
  | .rec2 => Stage v (needR v x) True pc

/-- Per-program-counter clauses. -/
def PcOK (v : KV V) (x : PV P K V) : APc V → Prop
  | .at .read => x.r.op = .read ∧ x.ls = x.r.d1
  | .at (.cas7 i) => (∃ old new, x.r.op = .cas old new) ∧ x.ls = x.r.d1 ∧
      (i = true → x.wit = none → v.lm = true)
  | .at (.cas10 i z) => (∃ old new, x.r.op = .cas old new ∧ CasMid v x old new i z) ∧
      (v.Z.1 = z.1 → v.pend → v.zAt = z.1)
  | .aft (.cas10 i z) b => (∃ old new, x.r.op = .cas old new) ∧ (b = true → x.inL) ∧
      (b = false → x.ls = x.r.d1 ∧ z.1 < v.Z.1 ∧ (i = true → x.wit ≠ none) ∧
        (i = false → x.wit = none → v.lm = true))
  | .at .wr12 => IsWr x.r.op ∧ x.ls = x.r.d1
  | .at (.wr13 w) => IsWr x.r.op ∧ x.ls = x.r.d1 ∧ Snap w v.W ∧
      (x.wit = none → v.W.1 ≠ w.1 → v.pend)
  | .at (.wr15 w) => (∃ u, x.r.op = .write u ∧ (v.W.1 = w.1 → ¬v.pend ∧ (v.lm = true → v.Z.2.1 ≠ u))) ∧
      x.ls = x.r.d1 ∧ Snap w v.W ∧ (x.wit = none → v.W.1 ≠ w.1 → v.pend)
  | .aft (.wr15 _) b => IsWr x.r.op ∧ (b = true ↔ x.r.d1 < x.ls) ∧ (needW v x → v.pend)
  | .at (.tw19 r) => TwOK v x r (.at (.tw19 r))
  | .at (.tw20 r zh) => TwOK v x r (.at (.tw20 r zh))
  | .at (.tw21 r zh wh) => TwOK v x r (.at (.tw21 r zh wh))
  | .aft (.tw21 r zh wh) b => TwOK v x r (.aft (.tw21 r zh wh) b)
  | .at (.recv _) => needR v x → v.pend
  | _ => False

/-- Clauses of an orphan `ECSC` (a pending call of a crashed process). -/
def OrphOK (p : P) (v : KV V) (x : PV P K V) : Prop :=
  ∀ o, x.orph = some o →
    (x.pc = .at (.recv 0) ∨ (x.pc = .at (.recv 1) ∧ o.o = (x.r.k, .Z))) ∧
    ((o.o = (x.r.k, .W) ∧ o.h = (p, .crit) ∧ x.ls = x.r.d1 ∧ o.s ≤ v.W.1 ∧
        ∃ u, x.r.op = .write u ∧ o.v.1 = u ∧
          (v.W.1 = o.s → ¬v.pend ∧ (v.lm = true → v.Z.2.1 ≠ u) ∧ o.v.2 ≠ v.W.2.2)) ∨
     (o.o = (x.r.k, .Z) ∧ o.h = (p, .crit) ∧ x.ls = x.r.d1 ∧ o.s ≤ v.Z.1 ∧
        ∃ old new, x.r.op = .cas old new ∧ old ≠ new ∧ o.v.1 = new ∧
          (v.Z.1 = o.s → v.Z.2 = (old, o.v.2) ∧ (v.pend → v.zAt = o.s))) ∨
     (o.o = (x.r.k, .Z) ∧ o.h = (p, .cas) ∧ o.s ≤ v.Z.1 ∧ (v.Z.1 = o.s → v.W.2 = o.v ∧ v.pend)))

/-- The per-process invariant (Lemmas A.28–A.41 and the detectability bookkeeping of A.45). -/
structure Loc (p : P) (v : KV V) (x : PV P K V) : Prop where
  d1_le : x.r.d1 ≤ x.ls
  inL_lt : x.inL → x.r.d1 < x.ls
  lt_inL : x.r.d1 < x.ls → x.inL ∨ v.pw = some x.r.id
  not_both : ¬(x.inL ∧ v.pw = some x.r.id)
  pw_op : v.pw = some x.r.id → x.r.d1 < x.ls ∧ x.r.op = .write v.W.2.1
  wit_sig : ∀ old new, x.r.op = .cas old new → x.wit = none → v.sig = old
  orph : OrphOK p v x
  pc : PcOK v x x.pc

/-! ### The three changes of an object (Lemma A.29) -/

/-- An install (successful `ECSC` on `W`, Lemma A.28.1) by the write with id `id`. -/
structure Inst (v v' : KV V) (id : ℕ) : Prop where
  npend : ¬v.pend
  W1 : v.W.1 < v'.W.1
  Wb : v'.W.2.2 ≠ v.W.2.2
  Z : v'.Z = v.Z
  pw : v'.pw = some id
  zAt : v'.zAt = v.Z.1
  lm : v'.lm = v.lm
  sig : v'.sig = v.sig
  a38 : v.lm = true → v'.W.2.1 ≠ v.Z.2.1

/-- A move (successful `ECSC` on `Z` in `TRANSFER-WRITE`, Lemma A.28.2). -/
structure Move (v v' : KV V) : Prop where
  pend : v.pend
  W : v'.W = v.W
  Z1 : v.Z.1 < v'.Z.1
  Z2 : v'.Z.2 = v.W.2
  pw : v'.pw = none
  zAt : v'.zAt = v.zAt
  lm : v'.lm = true
  sig : v'.sig = v.W.2.1

/-- An imprint of `new` (successful `ECSC` on `Z` at line 10, Lemma A.28.3). -/
structure Impr (v v' : KV V) (new : V) : Prop where
  i4 : v.pend → v.zAt = v.Z.1
  W : v'.W = v.W
  Z1 : v.Z.1 < v'.Z.1
  Z2 : v'.Z.2 = (new, v.Z.2.2)
  ne : new ≠ v.Z.2.1
  pw : v'.pw = v.pw
  zAt : v'.zAt = v.zAt
  lm : v'.lm = false
  sig : v'.sig = new

/-- The witness step after a change of `Z` at step `t` that sets the value to `sig'`: a `CAS`
with argument `old ≠ sig'` gets the witness `t` (its earliest step with `Z.val ≠ old`), a `WRITE`
gets the witness `t` if the change is a move (the first move in its interval). -/
def massWit (x : PV P K V) (sig' : V) (mv : Bool) (t : ℕ) : Option ℕ :=
  match x.wit with
  | some w => some w
  | none =>
    match x.r.op with
    | .cas old _ => if sig' = old then none else some t
    | .write _ => if mv then some t else none
    | .read => none

theorem KV.Inv.inst {v v' : KV V} {id : ℕ} (hv : v.Inv) (h : Inst v v' id) : v'.Inv := by
  have hb : v.W.2.2 = v.Z.2.2 := not_not.1 h.npend
  have hp : v'.pend := by
    unfold KV.pend; rw [h.Z]; intro h'; exact h.Wb (h'.trans hb.symm)
  refine ⟨⟨fun _ => by simp [h.pw], fun _ => hp⟩, fun _ hl => ?_, ?_, ?_⟩
  · rw [h.Z]; rw [h.lm] at hl; exact h.a38 hl
  · rw [h.zAt, h.Z]
  · rw [h.sig, h.Z]; exact hv.sig_eq

theorem KV.Inv.move {v v' : KV V} (hv : v.Inv) (h : Move v v') : v'.Inv := by
  have hp : ¬v'.pend := by unfold KV.pend; rw [h.W, h.Z2]; simp
  refine ⟨⟨fun h' => absurd h' hp, fun h' => absurd h.pw h'⟩, fun h' => absurd h' hp, ?_, ?_⟩
  · rw [h.zAt]; exact (hv.zAt_le).trans h.Z1.le
  · rw [h.sig, h.Z2]

theorem KV.Inv.impr {v v' : KV V} {new : V} (hv : v.Inv) (h : Impr v v' new) : v'.Inv := by
  have hp : v'.pend ↔ v.pend := by unfold KV.pend; rw [h.W, h.Z2]
  refine ⟨⟨fun h' => by rw [h.pw]; exact hv.pend_iff.1 (hp.1 h'),
    fun h' => hp.2 (hv.pend_iff.2 (by rw [← h.pw]; exact h'))⟩, fun _ h' => by simp [h.lm] at h',
    ?_, ?_⟩
  · rw [h.zAt]; exact (hv.zAt_le).trans h.Z1.le
  · rw [h.sig, h.Z2]

end Podc.DuraCAS

