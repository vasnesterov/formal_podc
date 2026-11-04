import Papers.PODC2019.RecoverableHierarchy.Defs

/-!
# Figure 1 of Golab (PODC 2019): the algorithm and its abstract view

The transformation of Figure 1 turns a conventional 2-process consensus algorithm `C` into a
2-process recoverable consensus algorithm tolerating arbitrarily many *simultaneous*
crash-recovery failures (`SEv.crashAll`). We model `C` by an atomic consensus object
(`consObj Bool`); the registers `P[1]`, `P[2]` (here `P 0`, `P 1`) and `D` are read/write
registers over `Option Bool` (`none` = `⊥`).

```
Procedure Decide(v) for process p_i
 2 if P[i] = ⊥ ∧ P[other] = ⊥ then
 3     P[i] := v
 4     d := C.Decide(v)
 5     D := d
 6     return d
 7 else if D ≠ ⊥ then
 8     return D
 9 else if P[i] ≠ ⊥ ∧ P[other] = ⊥ then
10     return P[i]
11 else if P[i] = ⊥ ∧ P[other] ≠ ⊥ then
12     return P[other]
13 else
14     return P[1]
```

Every shared-memory access is one step; the conditions of lines 2, 9 and 11 read the two
registers separately (first `P[i]`, then `P[other]`), as written. Program counters: `PC`.

Main results (in `Fig1.lean`):
* `theorem1` (Theorem 1 = Theorem 11): `SolvesS alg` — agreement (all outputs of an execution,
  also of different incarnations of one process, are equal), validity and recoverable
  wait-freedom, with arbitrarily many simultaneous crash-recovery failures;
* `lemma8` (Lemma 8): in every execution each process accesses `C` at most once.

This file: the algorithm `alg`, the abstract view `St` of configurations (program counters,
register values, the state of `C`, inputs) and the abstract step `sstep`, with
`view (srun C α) = α.foldl sstep (view C)` (`wf_view_srun`).
-/

namespace Podc.RecoverableHierarchy.Fig1

open Cslib.SharedMemory Cslib.SharedMemory.Recoverable

/-! ## The algorithm -/

/-- Shared objects: the proposal registers `P k` (paper: `P[k+1]`), the decision register `D`,
and the consensus object `C`. -/
inductive Obj where
  | P (k : Fin 2)
  | D
  | C
  deriving DecidableEq

/-- Object types: `P k` and `D` are registers over `Option Bool` (initially `none` = `⊥`), `C` is
an atomic consensus object (modelling the conventional consensus algorithm `C`). -/
abbrev T : Obj → ObjSpec
  | .P _ => register (Option Bool) none
  | .D => register (Option Bool) none
  | .C => consObj Bool

/-- The other process. -/
def oth (k : Fin 2) : Fin 2 := 1 - k

@[simp] lemma oth_zero : oth 0 = 1 := rfl
@[simp] lemma oth_one : oth 1 = 0 := rfl
@[simp] lemma oth_oth (k : Fin 2) : oth (oth k) = k := by fin_cases k <;> rfl
lemma oth_ne (k : Fin 2) : oth k ≠ k := by fin_cases k <;> decide
lemma ne_oth (k : Fin 2) : k ≠ oth k := (oth_ne k).symm
lemma eq_oth_of_ne {k m : Fin 2} (h : k ≠ m) : k = oth m := by
  fin_cases k <;> fin_cases m <;> simp_all

/-- Program counters. `l2a`/`l2b a`: line 2 (read `P[i]`, then `P[other]`; `a` is the value read
for `P[i]`), `l3`–`l5 d`: lines 3–5, `l7`: line 7, `l9a`/`l9b a`: line 9, `l11a`/`l11b a`:
line 11, `l13`: lines 13–14 (read `P[1]`); `rK d`: returned `d` at line `K`. -/
inductive PC where
  | l2a
  | l2b (a : Option Bool)
  | l3
  | l4
  | l5 (d : Bool)
  | l7
  | l9a
  | l9b (a : Option Bool)
  | l11a
  | l11b (a : Option Bool)
  | l13
  | r6 (d : Bool)
  | r8 (d : Bool)
  | r10 (d : Bool)
  | r12 (d : Bool)
  | r14 (d : Bool)
  deriving DecidableEq

namespace PC

/-- Line 2 after reading `P[i] = a` and `P[other] = r`. -/
def k2 (a r : Option Bool) : PC := if a = none ∧ r = none then .l3 else .l7

/-- Line 7 after reading `D = r`. -/
def k7 (r : Option Bool) : PC := Option.elim r .l9a .r8

/-- Line 9 after reading `P[i] = a` and `P[other] = r`. -/
def k9 (a r : Option Bool) : PC := if r = none then Option.elim a .l11a .r10 else .l11a

/-- Line 11 after reading `P[i] = a` and `P[other] = r`. -/
def k11 (a r : Option Bool) : PC := if a = none then Option.elim r .l13 .r12 else .l13

/-- Lines 13–14 after reading `P[1] = r` (`r = none` is impossible, see `Inv`; we then return
the own proposal `v`). -/
def k13 (v : Bool) (r : Option Bool) : PC := .r14 (r.getD v)

/-- The returned value, if `pc` is a return state. -/
def ret : PC → Option Bool
  | r6 d | r8 d | r10 d | r12 d | r14 d => some d
  | _ => none

/-- Rank: an upper bound on the number of remaining steps. -/
def rank : PC → ℕ
  | l2a => 10
  | l2b _ => 9
  | l3 => 3
  | l4 => 2
  | l5 _ => 1
  | l7 => 8
  | l9a => 7
  | l9b _ => 6
  | l11a => 5
  | l11b _ => 4
  | l13 => 1
  | _ => 0

/-- Lines 3–5: the process has passed line 2 and may write. -/
def busy : PC → Prop
  | l3 | l4 | l5 _ => True
  | _ => False

/-- Not in lines 3–6 (i.e. not in the epoch-local "writing" phase). -/
def idle : PC → Prop
  | l3 | l4 | l5 _ | r6 _ => False
  | _ => True

end PC

open PC

/-- Local states: process identifier, proposal, program counter. -/
abbrev Loc := Fin 2 × Bool × PC

/-- The next action of a process in local state `(k, v, pc)` (pseudo-code of Figure 1). -/
def act : Loc → Act T Loc
  | (k, v, .l2a) => .access (.P k) RWOp.read fun r => (k, v, .l2b r)
  | (k, v, .l2b a) => .access (.P (oth k)) RWOp.read fun r => (k, v, k2 a r)
  | (k, v, .l3) => .access (.P k) (RWOp.write (some v)) fun _ => (k, v, .l4)
  | (k, v, .l4) => .access .C v fun d => (k, v, .l5 d)
  | (k, v, .l5 d) => .access .D (RWOp.write (some d)) fun _ => (k, v, .r6 d)
  | (k, v, .l7) => .access .D RWOp.read fun r => (k, v, k7 r)
  | (k, v, .l9a) => .access (.P k) RWOp.read fun r => (k, v, .l9b r)
  | (k, v, .l9b a) => .access (.P (oth k)) RWOp.read fun r => (k, v, k9 a r)
  | (k, v, .l11a) => .access (.P k) RWOp.read fun r => (k, v, .l11b r)
  | (k, v, .l11b a) => .access (.P (oth k)) RWOp.read fun r => (k, v, k11 a r)
  | (k, v, .l13) => .access (.P 0) RWOp.read fun r => (k, v, k13 v r)
  | (_, _, .r6 d) => .out d
  | (_, _, .r8 d) => .out d
  | (_, _, .r10 d) => .out d
  | (_, _, .r12 d) => .out d
  | (_, _, .r14 d) => .out d

/-- The algorithm of Figure 1. -/
abbrev alg : Alg 2 T where
  L := Loc
  init k v := (k, v, .l2a)
  act := act
  mem₀
    | .P _ => (none : Option Bool)
    | .D => (none : Option Bool)
    | .C => (none : Option Bool)

/-! ## Abstract view -/

/-- The abstract view of a configuration. -/
@[ext] structure St where
  /-- Program counters. -/
  pc : Fin 2 → PC
  /-- Values of `P[k]`. -/
  P : Fin 2 → Option Bool
  /-- Value of `D`. -/
  D : Option Bool
  /-- State of the consensus object `C`. -/
  C : Option Bool
  /-- Inputs. -/
  x : Fin 2 → Bool

/-- A step of process `m` in the abstract view. -/
def astep (s : St) (m : Fin 2) : St :=
  match s.pc m with
  | .l2a => { s with pc := Function.update s.pc m (.l2b (s.P m)) }
  | .l2b a => { s with pc := Function.update s.pc m (k2 a (s.P (oth m))) }
  | .l3 => { s with pc := Function.update s.pc m .l4, P := Function.update s.P m (some (s.x m)) }
  | .l4 => { s with pc := Function.update s.pc m (.l5 (s.C.getD (s.x m))),
                    C := some (s.C.getD (s.x m)) }
  | .l5 d => { s with pc := Function.update s.pc m (.r6 d), D := some d }
  | .l7 => { s with pc := Function.update s.pc m (k7 s.D) }
  | .l9a => { s with pc := Function.update s.pc m (.l9b (s.P m)) }
  | .l9b a => { s with pc := Function.update s.pc m (k9 a (s.P (oth m))) }
  | .l11a => { s with pc := Function.update s.pc m (.l11b (s.P m)) }
  | .l11b a => { s with pc := Function.update s.pc m (k11 a (s.P (oth m))) }
  | .l13 => { s with pc := Function.update s.pc m (k13 (s.x m) (s.P 0)) }
  | _ => s

/-- An event in the abstract view. -/
def sstep (s : St) : SEv 2 → St
  | .step m => astep s m
  | .crashAll => { s with pc := fun _ => .l2a }

/-- The abstract view of a configuration. -/
def view (C : Cfg alg) : St where
  pc k := (C.loc k).2.2
  P k := C.mem (.P k)
  D := C.mem .D
  C := C.mem .C
  x := C.inp

/-- Well-formed local states: process `k` knows its identifier and its input. -/
def WF (C : Cfg alg) : Prop := ∀ k, (C.loc k).1 = k ∧ (C.loc k).2.1 = C.inp k


lemma wf_init (x : Fin 2 → Bool) : WF (initCfg alg x) := fun _ => ⟨rfl, rfl⟩

lemma view_init (x : Fin 2 → Bool) :
    view (initCfg alg x) = ⟨fun _ => .l2a, fun _ => none, none, none, x⟩ := rfl

lemma loc_eq {C : Cfg alg} (hC : WF C) (m : Fin 2) :
    C.loc m = (m, C.inp m, (view C).pc m) :=
  Prod.ext (hC m).1 (Prod.ext (hC m).2 rfl)

lemma wf_stepP {C : Cfg alg} (hC : WF C) (m : Fin 2) : WF (C.stepP m) := by
  intro k
  rw [stepP_inp]
  by_cases hk : k = m
  · subst hk
    rcases hact : alg.act (C.loc k) with ⟨i, o, κ⟩ | v
    · rw [stepP_loc_self C hact]
      have := loc_eq hC k
      revert hact
      rw [this]
      cases (view C).pc k <;> intro hact <;> cases hact <;> exact ⟨rfl, rfl⟩
    · rw [stepP_of_out C hact]; exact hC k
  · rw [stepP_loc_other C hk]; exact hC k

lemma view_stepP {C : Cfg alg} (hC : WF C) (m : Fin 2) :
    view (C.stepP m) = astep (view C) m := by
  have hl := loc_eq hC m
  rcases hpc : (view C).pc m with _ | a | _ | _ | d | _ | _ | a | _ | a | _ | d | d | d | d | d
  case l2a =>
    have hact : alg.act (C.loc m) = .access (.P m) RWOp.read (fun r => (m, C.inp m, .l2b r)) := by
      rw [hl, hpc]; rfl
    rw [stepP_of_access C hact]
    simp only [astep, hpc]
    ext k <;> by_cases hk : k = m <;> simp [view, hk, Function.update_of_ne]
  case l2b =>
    have hact : alg.act (C.loc m) = .access (.P (oth m)) RWOp.read (fun r => (m, C.inp m, k2 a r)) := by
      rw [hl, hpc]; rfl
    rw [stepP_of_access C hact]
    simp only [astep, hpc]
    ext k <;> by_cases hk : k = m <;> simp [view, hk, Function.update_of_ne]
  case l3 =>
    have hact : alg.act (C.loc m) = .access (.P m) (RWOp.write (some (C.inp m))) (fun _ => (m, C.inp m, .l4)) := by
      rw [hl, hpc]; rfl
    rw [stepP_of_access C hact]
    simp only [astep, hpc]
    ext k <;> by_cases hk : k = m <;> simp [view, hk, Function.update_of_ne]
  case l4 =>
    have hact : alg.act (C.loc m) = .access .C (C.inp m) (fun d => (m, C.inp m, .l5 d)) := by
      rw [hl, hpc]; rfl
    rw [stepP_of_access C hact]
    simp only [astep, hpc]
    ext k <;> by_cases hk : k = m <;> simp [view, hk, Function.update_of_ne]
  case l5 =>
    have hact : alg.act (C.loc m) = .access .D (RWOp.write (some d)) (fun _ => (m, C.inp m, .r6 d)) := by
      rw [hl, hpc]; rfl
    rw [stepP_of_access C hact]
    simp only [astep, hpc]
    ext k <;> by_cases hk : k = m <;> simp [view, hk, Function.update_of_ne]
  case l7 =>
    have hact : alg.act (C.loc m) = .access .D RWOp.read (fun r => (m, C.inp m, k7 r)) := by
      rw [hl, hpc]; rfl
    rw [stepP_of_access C hact]
    simp only [astep, hpc]
    ext k <;> by_cases hk : k = m <;> simp [view, hk, Function.update_of_ne]
  case l9a =>
    have hact : alg.act (C.loc m) = .access (.P m) RWOp.read (fun r => (m, C.inp m, .l9b r)) := by
      rw [hl, hpc]; rfl
    rw [stepP_of_access C hact]
    simp only [astep, hpc]
    ext k <;> by_cases hk : k = m <;> simp [view, hk, Function.update_of_ne]
  case l9b =>
    have hact : alg.act (C.loc m) = .access (.P (oth m)) RWOp.read (fun r => (m, C.inp m, k9 a r)) := by
      rw [hl, hpc]; rfl
    rw [stepP_of_access C hact]
    simp only [astep, hpc]
    ext k <;> by_cases hk : k = m <;> simp [view, hk, Function.update_of_ne]
  case l11a =>
    have hact : alg.act (C.loc m) = .access (.P m) RWOp.read (fun r => (m, C.inp m, .l11b r)) := by
      rw [hl, hpc]; rfl
    rw [stepP_of_access C hact]
    simp only [astep, hpc]
    ext k <;> by_cases hk : k = m <;> simp [view, hk, Function.update_of_ne]
  case l11b =>
    have hact : alg.act (C.loc m) = .access (.P (oth m)) RWOp.read (fun r => (m, C.inp m, k11 a r)) := by
      rw [hl, hpc]; rfl
    rw [stepP_of_access C hact]
    simp only [astep, hpc]
    ext k <;> by_cases hk : k = m <;> simp [view, hk, Function.update_of_ne]
  case l13 =>
    have hact : alg.act (C.loc m) = .access (.P 0) RWOp.read (fun r => (m, C.inp m, k13 (C.inp m) r)) := by
      rw [hl, hpc]; rfl
    rw [stepP_of_access C hact]
    simp only [astep, hpc]
    ext k <;> by_cases hk : k = m <;> simp [view, hk, Function.update_of_ne]
  all_goals
    have hout : ∃ v, alg.act (C.loc m) = .out v := by rw [hl, hpc]; exact ⟨_, rfl⟩
    obtain ⟨v, hv⟩ := hout
    rw [stepP_of_out C hv]
    simp only [astep, hpc]


lemma wf_snext {C : Cfg alg} (hC : WF C) : ∀ e, WF (snext C e)
  | .step m => wf_stepP hC m
  | .crashAll => fun _ => ⟨rfl, rfl⟩

lemma view_snext {C : Cfg alg} (hC : WF C) : ∀ e, view (snext C e) = sstep (view C) e
  | .step m => view_stepP hC m
  | .crashAll => rfl

lemma wf_view_srun {C : Cfg alg} (hC : WF C) (α : List (SEv 2)) :
    WF (srun C α) ∧ view (srun C α) = α.foldl sstep (view C) := by
  induction α generalizing C with
  | nil => exact ⟨hC, rfl⟩
  | cons e α ih =>
    obtain ⟨h1, h2⟩ := ih (wf_snext hC e)
    refine ⟨h1, ?_⟩
    rw [srun_cons, h2, view_snext hC e]
    rfl

lemma act_eq_out (k : Fin 2) (v : Bool) (pc : PC) (d : Bool) :
    act (k, v, pc) = .out d ↔ pc.ret = some d := by
  cases pc <;> simp [act, PC.ret]

lemma out_iff {C : Cfg alg} (hC : WF C) (p : Fin 2) (d : Bool) :
    C.Out p d ↔ ((view C).pc p).ret = some d := by
  rw [Cfg.Out, loc_eq hC p]
  exact act_eq_out _ _ _ _

end Podc.RecoverableHierarchy.Fig1
