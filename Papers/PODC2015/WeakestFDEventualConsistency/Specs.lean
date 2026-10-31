import Podc.Computability.Distributed.MessagePassing.FailureDetectors.Model

/-!
# Eventual consensus, eventual total order broadcast, eventual irrevocable consensus

Specifications of §3 and Appendix A.1 of Dubois, Guerraoui, Kuznetsov, Petit, Sens, *The Weakest
Failure Detector for Eventual Consistency* (PODC 2015, arXiv:1505.03469v1), stated on abstract
histories (so that they can be used both as conclusions, for algorithms, and as hypotheses, for
black boxes used by transformations).

* `ECHist`: invocations `inv p j v t` ("`p` invokes `proposeEC_j(v)` at time `t`") and responses
  `resp p j v t`. Instances are numbered from `0` (the paper numbers EC instances from `1` and
  EIC instances from `0`).
* `TOBHist`: broadcasts `bcast p m t` and the output variable `d p t` (the sequence delivered by
  `p` at time `t`).

"No two processes" in the agreement properties is read literally, i.e. *uniformly* (faulty
processes included), as in the consensus abstraction `C` the paper recalls (and in CHT). For EIC
we also give the non-uniform variant (`EICAgreementCorrect`).
-/

namespace Podc.WeakestFDEventualConsistency

open Cslib.FailureDetectors

/-! ### Eventual consensus -/

/-- Invocation/response history of a (multivalued) consensus-like abstraction with instances
`ℕ` and values `V`. -/
structure ECHist (P V : Type*) where
  /-- `p` invokes instance `j` with value `v` at time `t`. -/
  inv : P → ℕ → V → ℕ → Prop
  /-- `p` receives the response `v` to instance `j` at time `t`. -/
  resp : P → ℕ → V → ℕ → Prop

variable {P V M : Type*}

/-- The usage assumption of EC: every process invokes each instance at most once, invokes
`j + 1` exactly when (in the same step as) it receives its response to `j`, and only then. -/
structure ECHist.ProperUse (h : ECHist P V) : Prop where
  inv_once : ∀ p j v v' t t', h.inv p j v t → h.inv p j v' t' → t = t' ∧ v = v'
  inv_succ : ∀ p j v t, h.inv p (j + 1) v t → ∃ v', h.resp p j v' t
  resp_inv : ∀ p j v t, h.resp p j v t → ∃ v', h.inv p (j + 1) v' t

/-- Well-formedness of a black box: a response to instance `j` at `p` comes (strictly) after an
invocation of `j` at `p`. -/
def ECHist.RespAfterInv (h : ECHist P V) : Prop :=
  ∀ p j v t, h.resp p j v t → ∃ v' t', t' < t ∧ h.inv p j v' t'

/-- EC-Termination: every correct process eventually returns a response to every instance. -/
def ECTermination (F : FailurePattern P) (h : ECHist P V) : Prop :=
  ∀ p, F.Correct p → ∀ j, ∃ v t, h.resp p j v t

/-- EC-Integrity: no process responds twice to the same instance. -/
def ECIntegrity (h : ECHist P V) : Prop :=
  ∀ p j v v' t t', h.resp p j v t → h.resp p j v' t' → t = t' ∧ v = v'

/-- EC-Validity: every value returned to instance `j` was previously proposed to `j`. -/
def ECValidity (h : ECHist P V) : Prop :=
  ∀ p j v t, h.resp p j v t → ∃ q t', t' ≤ t ∧ h.inv q j v t'

/-- EC-Agreement from instance `k` on: no two processes return different values. -/
def ECAgreementFrom (h : ECHist P V) (k : ℕ) : Prop :=
  ∀ j, k ≤ j → ∀ p q v v' t t', h.resp p j v t → h.resp q j v' t' → v = v'

/-- **Eventual consensus** (§3): in the run there is `k` such that termination, integrity,
validity hold and agreement holds for all instances `j ≥ k`. -/
def EC (F : FailurePattern P) (h : ECHist P V) : Prop :=
  ECTermination F h ∧ ECIntegrity h ∧ ECValidity h ∧ ∃ k, ECAgreementFrom h k

/-! ### Eventual total order broadcast -/

/-- History of a total-order-broadcast-like abstraction. -/
structure TOBHist (P M : Type*) where
  /-- `p` broadcasts `m` at time `t`. -/
  bcast : P → M → ℕ → Prop
  /-- The output variable `d_p` at time `t`. -/
  d : P → ℕ → List M

/-- The usage assumption: broadcast messages are distinct. -/
def TOBHist.Distinct (h : TOBHist P M) : Prop :=
  ∀ p q m t t', h.bcast p m t → h.bcast q m t' → p = q ∧ t = t'

/-- `p` eventually stably delivers `m`: from some time on, `m ∈ d_p` forever. -/
def TOBHist.StablyDelivers (h : TOBHist P M) (p : P) (m : M) : Prop :=
  ∃ t, ∀ t' ≥ t, m ∈ h.d p t'

/-- `m₁` appears before `m₂` in `l`. -/
def Before (m₁ m₂ : M) (l : List M) : Prop := List.Sublist [m₁, m₂] l

/-- TOB-Validity. -/
def TOBValidity (F : FailurePattern P) (h : TOBHist P M) : Prop :=
  ∀ p m t, F.Correct p → h.bcast p m t → ∃ t' > t, ∀ t'' ≥ t', m ∈ h.d p t''

/-- TOB-No-creation. -/
def TOBNoCreation (h : TOBHist P M) : Prop :=
  ∀ p t m, m ∈ h.d p t → ∃ q t', t' < t ∧ h.bcast q m t'

/-- TOB-No-duplication. -/
def TOBNoDup (h : TOBHist P M) : Prop := ∀ p t, (h.d p t).Nodup

/-- TOB-Agreement. -/
def TOBAgreement (F : FailurePattern P) (h : TOBHist P M) : Prop :=
  ∀ p q m, F.Correct p → F.Correct q → h.StablyDelivers p m → h.StablyDelivers q m

/-- ETOB-Stability from time `τ` on (TOB-Stability is `ETOBStability F h 0`). -/
def ETOBStability (F : FailurePattern P) (h : TOBHist P M) (τ : ℕ) : Prop :=
  ∀ p, F.Correct p → ∀ t₁ t₂, τ ≤ t₁ → t₁ ≤ t₂ → h.d p t₁ <+: h.d p t₂

/-- ETOB-Total-order from time `τ` on. -/
def ETOBTotalOrder (F : FailurePattern P) (h : TOBHist P M) (τ : ℕ) : Prop :=
  ∀ p q, F.Correct p → F.Correct q → ∀ t, τ ≤ t → ∀ m₁ m₂,
    m₁ ∈ h.d q t → m₂ ∈ h.d q t → Before m₁ m₂ (h.d p t) → Before m₁ m₂ (h.d q t)

/-- **Eventual total order broadcast** (§3). -/
def ETOB (F : FailurePattern P) (h : TOBHist P M) : Prop :=
  TOBValidity F h ∧ TOBNoCreation h ∧ TOBNoDup h ∧ TOBAgreement F h ∧
    ∃ τ, ETOBStability F h τ ∧ ETOBTotalOrder F h τ

/-! ### Eventual irrevocable consensus (Appendix A.1) -/

/-- At time `t`, the current response of `p` to instance `j` is `v`: `v` is the last response of
`p` to `j` strictly before `t`. -/
def ECHist.Current (h : ECHist P V) (p : P) (j : ℕ) (v : V) (t : ℕ) : Prop :=
  ∃ t₀ < t, h.resp p j v t₀ ∧ ∀ t₁ v₁, t₀ < t₁ → t₁ < t → ¬ h.resp p j v₁ t₁

/-- `p` and `q` return "infinitely different" values to instance `j`: at infinitely many times
their current responses differ. -/
def ECHist.InfDiff (h : ECHist P V) (p q : P) (j : ℕ) : Prop :=
  ∀ T, ∃ t ≥ T, ∃ v v', v ≠ v' ∧ h.Current p j v t ∧ h.Current q j v' t

/-- EIC-Integrity from instance `k` on. -/
def EICIntegrityFrom (h : ECHist P V) (k : ℕ) : Prop :=
  ∀ j, k ≤ j → ∀ p v v' t t', h.resp p j v t → h.resp p j v' t' → t = t' ∧ v = v'

/-- EIC-Agreement, literal (uniform) reading: no two processes return infinitely different
values. -/
def EICAgreement (h : ECHist P V) : Prop := ∀ p q j, ¬ h.InfDiff p q j

/-- EIC-Agreement restricted to correct processes. -/
def EICAgreementCorrect (F : FailurePattern P) (h : ECHist P V) : Prop :=
  ∀ p q j, F.Correct p → F.Correct q → ¬ h.InfDiff p q j

/-- The usage assumption of EIC: instance `j + 1` is invoked exactly when the *first* response to
`j` is returned. -/
structure ECHist.ProperUseEIC (h : ECHist P V) : Prop where
  inv_once : ∀ p j v v' t t', h.inv p j v t → h.inv p j v' t' → t = t' ∧ v = v'
  inv_succ : ∀ p j v t, h.inv p (j + 1) v t → ∃ v', h.resp p j v' t ∧
    ∀ t' v'', t' < t → ¬ h.resp p j v'' t'
  resp_inv : ∀ p j v t, h.resp p j v t → (∀ t' v'', t' < t → ¬ h.resp p j v'' t') →
    ∃ v', h.inv p (j + 1) v' t

/-- **Eventual irrevocable consensus** (Appendix A.1), literal reading. -/
def EIC (F : FailurePattern P) (h : ECHist P V) : Prop :=
  ECTermination F h ∧ (∃ k, EICIntegrityFrom h k) ∧ EICAgreement h ∧ ECValidity h

/-- Eventual irrevocable consensus with agreement among correct processes only. -/
def EICCorrect (F : FailurePattern P) (h : ECHist P V) : Prop :=
  ECTermination F h ∧ (∃ k, EICIntegrityFrom h k) ∧ EICAgreementCorrect F h ∧ ECValidity h

end Podc.WeakestFDEventualConsistency
