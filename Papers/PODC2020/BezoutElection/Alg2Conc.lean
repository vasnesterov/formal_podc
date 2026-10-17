import Papers.PODC2020.BezoutElection.Alg2AbsFacts

/-!
# Algorithm 2: from configurations to the per-register abstraction

A *virtual program counter* `VPC` extends the program counter by the positions `loop k` inside
the for loop (between two accesses), so that the for loop can be analysed one register at a
time. `absAt π mem loc vpc x` is the abstract state of the physical register `x`.
-/

set_option linter.unusedSectionVars false

open Cslib.SharedMemory

namespace BezoutElection.Alg2

variable {Id : Type} [DecidableEq Id] {P : Type} [DecidableEq P] {m : ℕ}

/-- Program counters, plus the positions inside the for loop. -/
inductive VPC (Id : Type)
  | pc (c : PC Id)
  | loop (k : ℕ)

/-- The status of a process for its local register `k`. After the final collect (`ret`, `fin`)
the copies are kept forever. -/
def vstatus (c : VPC Id) (s : St Id m) (k : Fin m) : AStatus Id :=
  match c with
  | .pc .idle => .fresh
  | .pc (.collect j) => if j ≤ k.val then .fresh else .copy (s.regs k)
  | .pc (.write j w) => if j < k.val then .copy (s.regs k) else if j = k.val then .pend w else .fresh
  | .pc (.ret _) => .copy (s.regs k)
  | .pc .fin => .copy (s.regs k)
  | .loop j => if j ≤ k.val then .copy (s.regs k) else .fresh

/-- The local variables of a process for its local register `k`. -/
def locX (s : St Id m) (k : Fin m) (st : AStatus Id) : ALoc Id :=
  ⟨s.phase k, s.disc k, s.loser k, s.level k, s.cand k, st⟩

/-- The abstract state of the physical register `x`. -/
def absAt (π : P → Equiv.Perm (Fin m)) (mem : Fin m → Reg Id) (loc : P → St Id m)
    (vpc : P → VPC Id) (x : Fin m) : AState Id P :=
  ⟨mem x, fun q => locX (loc q) ((π q).symm x) (vstatus (vpc q) (loc q) ((π q).symm x))⟩

/-- The global part of the candidacy predicate of line M(10). -/
def okOf (s : St Id m) (k : Fin m) : Bool :=
  decide ((∀ y, y ≠ k → s.cand y = false) ∧ 0 < s.toWin)

section ProcReg

variable (pp : Params) (s : St Id m) (k : Fin m)

/-- The abstract outcome of `procReg`. -/
abbrev oX : ALoc Id × Option (Reg Id) :=
  procX pp.n pp.U s.me (locX s k .fresh) (s.regs k) (okOf s k) s.finishing

theorem procReg_snd : (procReg pp s k).2 = (oX pp s k).2 := by
  unfold procReg oX procX locX okOf
  dsimp only
  simp only [decide_eq_true_eq]
  split_ifs <;> rfl

theorem procReg_locX (st : AStatus Id) :
    locX (procReg pp s k).1 k st = { (oX pp s k).1 with st := st } := by
  unfold procReg oX procX okOf
  simp only [locX, decide_eq_true_eq]
  split_ifs <;> simp [*]

theorem procReg_locX_ne (k' : Fin m) (hk : k' ≠ k) (st : AStatus Id) :
    locX (procReg pp s k).1 k' st = locX s k' st := by
  unfold procReg
  dsimp only
  split_ifs <;> simp [locX, Function.update_of_ne hk]

theorem procReg_fields : (procReg pp s k).1.me = s.me ∧ (procReg pp s k).1.pc = s.pc ∧
    (procReg pp s k).1.regs = s.regs ∧ (procReg pp s k).1.finishing = s.finishing := by
  unfold procReg
  dsimp only
  split_ifs <;> simp

theorem procReg_toWin_win (w : Reg Id) (hw : (oX pp s k).2 = some w)
    (hl : w.level = (s.regs k).level + 1) : (procReg pp s k).1.toWin = s.toWin - 1 := by
  revert hw hl
  unfold procReg oX procX locX okOf
  dsimp only
  simp only [decide_eq_true_eq]
  split_ifs <;> intro h1 h2 <;> simp only [Option.some.injEq, reduceCtorEq] at h1 <;>
    subst h1 <;> simp_all

theorem procReg_toWin_nowin (h : ∀ w, (oX pp s k).2 = some w → w.level ≠ (s.regs k).level + 1) :
    (procReg pp s k).1.toWin = s.toWin := by
  revert h
  unfold procReg oX procX locX okOf
  dsimp only
  simp only [decide_eq_true_eq]
  split_ifs <;> intro h <;> simp_all

end ProcReg

end BezoutElection.Alg2
