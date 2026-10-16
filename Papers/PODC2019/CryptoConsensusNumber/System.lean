import Papers.PODC2019.CryptoConsensusNumber.Valency
import Papers.PODC2025.TwoShotConsensusObjects.Model

/-!
# Consensus from registers and asset-transfer objects: the system

Model for the consensus-number statements (Section 2.1 and Section 4 of the paper), on top of
CSLib's asynchronous shared-memory model `Cslib.SharedMemory.Recoverable` used without crashes:

* `n` deterministic processes `Fin n` starting with binary inputs; a process decides by entering
  an output state; asynchronous scheduling; executions are lists of events;
* wait-free binary consensus `WFConsensus` (agreement, validity, and: every process taking
  infinitely many steps decides). Crash-stop failures are processes that stop taking steps;
* shared objects (`atSys R μ`): read/write objects `R j` (`IsRW`: every operation is read-only or a
  blind write; registers are an instance), and asset-transfer objects `j : ιS`, each with its own
  owner map `μ j : Acct → Finset (Fin n)`. Any number of objects (`ιR`, `ιS` arbitrary); initial
  balances and register values are chosen by the algorithm (`Alg.mem₀`; `ObjSpec.init` is
  ignored by the model);
* `Honest A`: processes invoke `transfer` only under their own identity (the caller is an
  argument of the operation since CSLib's object specifications do not see the caller).

`ATSolvable n k`: there is a wait-free consensus algorithm for `n` processes using read/write
objects and asset-transfer objects in which every account has at most `k` owners. The paper's
"consensus number of `k`-shared asset transfer is `k`" is `ATSolvable k k ∧ ∀ n > k, ¬ ATSolvable n k`
(`Main.lean`).
-/

namespace CryptoCons

open Cslib.SharedMemory Cslib.SharedMemory.Recoverable TwoShotCons

variable {n : ℕ} {ιR ιS : Type} [DecidableEq ιR] [DecidableEq ιS] (R : ιR → ObjSpec)
  {Acct : Type} [DecidableEq Acct] (μ : ιS → Acct → Finset (Fin n))

/-- The objects: read/write objects `R j` and asset-transfer objects with owner maps `μ j`. -/
abbrev atSys : ιR ⊕ ιS → ObjSpec
  | .inl j => R j
  | .inr j => atSpec (Fin n) Acct (μ j) (fun _ => 0)

/-- Processes invoke `transfer` only under their own identity, in every reachable
configuration. -/
def Honest (A : Alg n (atSys R μ)) : Prop :=
  ∀ x α, CrashFree α → ∀ (p : Fin n) (j : ιS) (q : Fin n) (a b : Acct) (y : ℕ)
    (κ : (Bool ⊕ ℕ) → A.L),
    A.act ((run (initCfg A x) α).loc p) = .access (.inr j) (ATOp.transfer q a b y) κ → q = p

/-- **Consensus from `k`-shared asset transfer.** There is a wait-free binary consensus algorithm
for `n` processes using read/write objects and asset-transfer objects in which every account has
at most `k` owners (and processes transfer only under their own identity). -/
def ATSolvable (n k : ℕ) : Prop :=
  ∃ (ιR ιS Acct : Type) (_ : DecidableEq ιR) (_ : DecidableEq ιS) (_ : DecidableEq Acct)
    (R : ιR → ObjSpec) (_ : ∀ j, IsRW (R j)) (μ : ιS → Acct → Finset (Fin n))
    (_ : ∀ j, KShared (μ j) k) (A : Alg n (atSys R μ)), WFConsensus A ∧ Honest R μ A

end CryptoCons
