import Papers.PODC2026.ConflictFreedom.Alg1

/-!
# Algorithm 1: explicit description of the steps

The internal steps of `Alg1.impl` are described explicitly, phase by phase
(`Alg1.step_tau_cases`), together with the per-round GCA state `Alg1.gst C r` (the snapshot
objects of `GCA_r` and the local GCA states of its participants, current or recorded in the
ghost history).
-/

namespace Podc.ConflictFreedom

open Cslib.SharedMemory Cslib.Mazurkiewicz Classical

namespace Alg1

variable {A : ObjSpec} {n : ℕ}

/-- The local GCA state of a process at round `r` (current round, or recorded in the ghost
history). -/
def locAt (l : Loc A n) (r : ℕ) : Option (GCA.Loc n (Tr A n)) :=
  match l.phase with
  | .gca g => if r = l.r then some g else l.hist r
  | _ => l.hist r

/-- Configurations of Algorithm 1. -/
abbrev Cfg (A : ObjSpec) (n : ℕ) := Config A (base A n) (Fin n) (Loc A n)

/-- The global state of `GCA_r` in configuration `C`. -/
def gst (C : Cfg A n) (r : ℕ) : GCA.State n (Tr A n) :=
  ⟨C.mem (.A r), C.mem (.B r), fun i => locAt (C.loc i) r⟩

variable [Inhabited A.Resp] [Inhabited A.Op] [NeZero n]

/-- Replace the local state of `p`. -/
def setLoc (C : Cfg A n) (p : Fin n) (l : Loc A n) : Cfg A n :=
  { C with loc := Function.update C.loc p l }

/-- Replace the state of base object `o` and the local state of `p`. -/
def setMemLoc (C : Cfg A n) (o : Obj n) (v : (base A n o).State) (p : Fin n) (l : Loc A n) :
    Cfg A n :=
  { C with mem := Function.update C.mem o v, loc := Function.update C.loc p l }

/-- The local state after the last read of `S` (line 5) in phase `readS j best`. -/
noncomputable def Loc.afterRead (l : Loc A n) (b : ℕ × Tr A n) : Loc A n :=
  l.startRound b.1 b.2

/-- The explicit forms of an internal step of process `p` from `C` to `C'`. -/
inductive TauStep (C : Cfg A n) (p : Fin n) : Cfg A n → Prop
  | readS (j : ℕ) (best : ℕ × Tr A n) (hj : j < n) (hph : (C.loc p).phase = .readS j best)
      (hlt : j + 1 < n) :
      TauStep C p (setLoc C p
        { C.loc p with phase := .readS (j + 1) (better best (C.mem (.S ⟨j, hj⟩))) })
  | readLast (j : ℕ) (best : ℕ × Tr A n) (hj : j < n) (hph : (C.loc p).phase = .readS j best)
      (hlt : ¬ j + 1 < n) :
      TauStep C p (setLoc C p ((C.loc p).afterRead (better best (C.mem (.S ⟨j, hj⟩)))))
  | gca0 (g : GCA.Loc n (Tr A n)) (hph : (C.loc p).phase = .gca g) (hpc : g.pc = 0) :
      TauStep C p (setMemLoc C (.A (C.loc p).r)
        (Function.update (C.mem (.A (C.loc p).r)) p (some g.inp)) p
        { C.loc p with phase := .gca { g with pc := 1 } })
  | gca1 (g : GCA.Loc n (Tr A n)) (hph : (C.loc p).phase = .gca g) (hpc : g.pc = 1) :
      TauStep C p (setLoc C p
        { C.loc p with phase := .gca { g with pc := 2, av := C.mem (.A (C.loc p).r) } })
  | gca2 (g : GCA.Loc n (Tr A n)) (hph : (C.loc p).phase = .gca g) (hpc : g.pc = 2) :
      TauStep C p (setMemLoc C (.B (C.loc p).r)
        (Function.update (C.mem (.B (C.loc p).r)) p
          (some (GCA.candidate g.av, GCA.compatFlag g.av))) p
        { C.loc p with phase := .gca { g with pc := 3 } })
  | gca3 (g : GCA.Loc n (Tr A n)) (hph : (C.loc p).phase = .gca g)
      (hpc : g.pc ≠ 0 ∧ g.pc ≠ 1 ∧ g.pc ≠ 2) :
      TauStep C p (setLoc C p
        ((C.loc p).afterGCA { g with pc := 4, bv := C.mem (.B (C.loc p).r) }))
  | writeS (hph : (C.loc p).phase = .writeS) :
      TauStep C p (setMemLoc C (.S p) ((C.loc p).r, (C.loc p).s) p
        { C.loc p with phase := .done })

/-- Every internal step has one of the explicit forms of `TauStep`. -/
theorem step_tau_cases {C C' : Cfg A n} {p : Fin n} (h : (impl (A := A) (n := n)).step C (.tau p) = some C') :
    C.pend p ≠ none ∧ C'.pend = C.pend ∧ TauStep C p C' := by
  obtain ⟨hp, hpend, i, o, k, hact, hmem, hloc⟩ := Impl.step_tau h
  refine ⟨hp, hpend, ?_⟩
  have hC' : C' = { C with mem := C'.mem, loc := C'.loc } := by
    cases C'; simp only [Config.mk.injEq, and_true, true_and]; exact hpend
  rw [hC', hmem, hloc]
  change act p (C.loc p) = _ at hact
  unfold act at hact
  split at hact
  · cases hact
  · rename_i j best hph
    split at hact
    · rename_i hj
      cases hact
      by_cases hlt : j + 1 < n
      · have := TauStep.readS (C := C) j best hj hph hlt
        simpa [hlt, Function.update_eq_self, setLoc, setMemLoc, Loc.afterRead] using this
      · have := TauStep.readLast (C := C) j best hj hph hlt
        simpa [hlt, Function.update_eq_self, setLoc, setMemLoc, Loc.afterRead] using this
    · cases hact
  · rename_i g hph
    split at hact
    · rename_i hpc; cases hact; simpa [setLoc, setMemLoc] using TauStep.gca0 (C := C) g hph hpc
    · rename_i hpc; cases hact
      have := TauStep.gca1 (C := C) g hph hpc
      simpa [Function.update_eq_self, setLoc, setMemLoc, Loc.afterRead] using this
    · rename_i hpc; cases hact; simpa [setLoc, setMemLoc] using TauStep.gca2 (C := C) g hph hpc
    · rename_i hpc0 hpc1 hpc2; cases hact
      have := TauStep.gca3 (C := C) g hph ⟨hpc0, hpc1, hpc2⟩
      simpa [Function.update_eq_self, setLoc, setMemLoc, Loc.afterRead] using this
  · rename_i hph; cases hact; simpa [setLoc, setMemLoc] using TauStep.writeS (C := C) hph
  · cases hact

end Alg1

end Podc.ConflictFreedom
