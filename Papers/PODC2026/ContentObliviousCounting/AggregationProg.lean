import Papers.PODC2026.ContentObliviousCounting.AggregationMIS
import Cslib.Computability.Distributed.ContentOblivious.Staged
import Cslib.Computability.Distributed.ContentOblivious.VirtualRing
import Mathlib

/-!
# The aggregation algorithm of Theorem 1 as a staged program

Chalopin, Chang, Di Luna, Zhou, *Efficient Counting and Simulation in Content-Oblivious Rings*,
PODC 2026, proof of Theorem 1.

Every node runs a driver (`aggDriver`) whose stages are either a `ComputeOR` (procedure `OR`) or a
simulation (Theorem 14) of `misAlg` (Lemma 26 + one aggregation round) on the virtual ring of the
currently active nodes. The driver implements:
1. *λ-preprocessing*: `ComputeOR(size(ID) ≥ i)` for `i = 1, 2, …` until the outcome is false;
   then `lam = i - 1` is the maximal ID length;
2. *phases*: loneliness test `ComputeOR(active ∧ ¬leader)`; if true, simulate `misAlg` on the
   active nodes (MIS + aggregation); the MIS stays active;
3. *dissemination*: the leader broadcasts the bits of the final aggregate, one bit per
   `ComputeOR` (`ComputeOR(leader ∧ more bits)`, then `ComputeOR(leader ∧ bit)`).

`simStage` is the simulation procedure with the number of rounds computed from the initial state
(`Proc.precomp`), so that no stage returns at start-up.
-/

namespace Cslib.ContentOblivious

namespace Proc

variable {I I' R : Type*} (P : Proc I R) (g : I' → I)

/-- Precomposition of the input of a procedure with `g`. -/
def precomp : Proc I' R where
  State := P.State
  init a := P.init (g a)
  recv := P.recv
  ready := P.ready
  terminated := P.terminated
  result := P.result
  terminated_eq := P.terminated_eq

variable {P g} [Encodable I] [Inhabited I] [Encodable I'] [Inhabited I'] {V : Type*}
  [DecidableEq V] {W : Wiring V}

lemma precomp_step {c c' : Config V P.State} :
    (P.precomp g).Step W c c' ↔ P.Step W c c' := by
  constructor <;> rintro ⟨v, j, h⟩ <;> exact Step.mk _ v j h

lemma precomp_reach (x : V → I') (c : Config V P.State) :
    (P.precomp g).Reach W x c ↔ P.Reach W (fun v => g (x v)) c := by
  unfold Prog.Reach Reach
  rw [Prog.initCfg_eq, Prog.initCfg_eq]
  have e : (P.precomp g).toProg.initCfg x = P.initCfg (fun v => g (x v)) := rfl
  rw [e]
  have e2 : Step W (P.precomp g).toAlgo = Step W P.toAlgo := by
    funext c c'; exact propext precomp_step
  rw [e2]
  exact Iff.rfl

variable [Fintype V]

lemma precomp_totalSent {x : V → I'} {B : ℕ}
    (hB : ∀ c, P.Reach W (fun v => g (x v)) c → totalSent c ≤ B) :
    ∀ c, (P.precomp g).Reach W x c → totalSent c ≤ B :=
  fun c hc => hB c ((precomp_reach (P := P) (g := g) x c).1 hc)

lemma precomp_composable {x : V → I'} (h : P.Composable W (fun v => g (x v))) :
    (P.precomp g).Composable W x where
  bounded := by
    obtain ⟨B, hB⟩ := h.bounded
    exact ⟨B, precomp_totalSent hB⟩
  final c hc hfin := h.final c ((precomp_reach (P := P) (g := g) x c).1 hc) hfin
  clean c hc := h.clean c ((precomp_reach (P := P) (g := g) x c).1 hc)

omit [Fintype V] in
lemma precomp_returns {x : V → I'} {r : V → R} (h : P.Returns W (fun v => g (x v)) r) :
    (P.precomp g).Returns W x r :=
  fun c hc hfin => h c ((precomp_reach (P := P) (g := g) x c).1 hc) hfin

end Proc

end Cslib.ContentOblivious

namespace Podc.ContentOblivious

open Cslib.ContentOblivious

namespace Aggregation

open Simulation MsgExchange Finset

variable (OR : Proc (Bool × Bool) Bool) (CW CCW : Proc (Bool × Bool × Option Bool) (Option Bool))
  (op2 : List Bool → List Bool → List Bool)

/-- Inputs of a simulation stage before precomposition: leader flag, active flag, initial state
(the number of rounds is `rounds lam`). -/
def simInput (i : Bool × Bool × MState) : Bool × Bool × MState × ℕ :=
  (i.1, i.2.1, i.2.2, rounds i.2.2.lam)

/-- The simulation stage (Theorem 14 applied to `misAlg`). -/
abbrev simStage : Proc (Bool × Bool × MState) (SimSt MState) :=
  (simProg OR CW CCW (misAlg op2)).precomp simInput

/-- Stage inputs and results. -/
abbrev J := (Bool × Bool) ⊕ (Bool × Bool × MState)
abbrev R := Bool ⊕ SimSt MState

/-- The stage procedure: `ComputeOR` or a simulation. -/
abbrev stageProc : Proc J R := OR.sum (simStage OR CW CCW op2)

/-- Driver modes. -/
inductive Mode
  | pre (i : ℕ)
  | lonely
  | sim
  | more (k : ℕ)
  | bit (k : ℕ)
  | done

/-- Local state of the driver. -/
structure DSt where
  id : ℕ
  lead : Bool
  /-- Current (encoded) partial aggregate. -/
  w : List Bool
  mode : Mode
  lam : ℕ
  active : Bool
  /-- Bits of the final aggregate received so far. -/
  out : List Bool

variable {U : Type}

/-- The driver of the aggregation algorithm. Node input: `(ID, isLeader, x)`; `w0 x` is the
encoding of `f {x}`. -/
def aggDriver (w0 : U → List Bool) : Driver (ℕ × Bool × U) J R DSt where
  start i := (⟨i.1, i.2.1, w0 i.2.2, .pre 1, 0, true, []⟩,
    some (.inl (i.2.1, decide (1 ≤ Nat.size i.1))))
  next d r := match d.mode, r with
    | .pre i, .inl b =>
      if b then
        ({ d with mode := .pre (i + 1) }, some (.inl (d.lead, decide (i + 1 ≤ Nat.size d.id))))
      else ({ d with mode := .lonely, lam := i - 1 }, some (.inl (d.lead, d.active && !d.lead)))
    | .lonely, .inl b =>
      if b then
        ({ d with mode := .sim }, some (.inr (d.lead, d.active, initSt d.lam d.lead d.id d.w)))
      else ({ d with mode := .more 0 }, some (.inl (d.lead, d.lead && decide (0 < d.w.length))))
    | .sim, .inr st =>
      let a := d.active && st.s.mis
      let w' := if d.active then st.s.w else d.w
      ({ d with mode := .lonely, active := a, w := w' }, some (.inl (d.lead, a && !d.lead)))
    | .more k, .inl b =>
      if b then ({ d with mode := .bit k }, some (.inl (d.lead, d.lead && d.w.getD k false)))
      else ({ d with mode := .done }, none)
    | .bit k, .inl b =>
      ({ d with mode := .more (k + 1), out := d.out ++ [b] },
        some (.inl (d.lead, d.lead && decide (k + 1 < d.w.length))))
    | _, _ => (d, none)

/-- The aggregation program. -/
abbrev aggProg (w0 : U → List Bool) : Proc (ℕ × Bool × U) DSt :=
  (stageProc OR CW CCW op2).staged (aggDriver w0)

/-! ### The result oracle -/

variable {n : ℕ} [NeZero n]

/-- The `ComputeOR` input bit of a stage input. -/
def orBit : J → Bool
  | .inl (_, b) => b
  | .inr _ => false

/-- The active flag of a simulation stage input. -/
def simAct : J → Bool
  | .inl _ => false
  | .inr (_, a, _) => a

/-- The initial state of a simulation stage input. -/
def simS0 : J → MState
  | .inl _ => default
  | .inr (_, _, s) => s

/-- What every stage returns, as a function of all stage inputs. -/
def oracle (j : ZMod n → J) (v : ZMod n) : R :=
  match j v with
  | .inl _ => .inl (decide (∃ u, orBit (j u) = true))
  | .inr (l, a, s) =>
    .inr ⟨l, a, stateAt (misAlg op2) (fun u => simAct (j u)) (vnext fun u => simAct (j u))
      (vprev fun u => simAct (j u)) (fun u => simS0 (j u)) (rounds s.lam) v,
      rounds s.lam, rounds s.lam⟩

end Aggregation

end Podc.ContentOblivious
