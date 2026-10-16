import Mathlib
import Cslib.Computability.Distributed.Byzantine.PartialSync.ICSync
import Cslib.Computability.Distributed.Byzantine.PartialSync.FLM
import Cslib.Computability.Distributed.Byzantine.PartialSync.Constructions
import Papers.PODC2013.ByzantineVectorConsensus.Gamma

/-!
# Byzantine vector consensus: specifications

The execution model is CSLib's Byzantine message-passing model
`Cslib.Byzantine.PartialSync` (complete network of `n = |P|` processes, at most `t` Byzantine,
deterministic state machines, adversary = faulty set + inputs + Byzantine messages + delivery
times). *Synchronous* runs are the runs with `gst = 0` (`Cslib.Byzantine.PartialSync.Sync`);
*asynchronous* behaviour is modelled by runs with an arbitrary (finite, adversarial) `gst`, i.e.
the partially synchronous model. Since the latter has fewer runs than the asynchronous model and
its processes have synchronized clocks, impossibility results proved for it imply the
asynchronous ones.

* `bvcValidity P d`: the decision lies in the convex hull of the inputs of the correct processes.
* Exact BVC in synchrony: `SolvesConsensusSync t δ A (bvcValidity P d)` (CSLib's consensus
  specification: termination, agreement, validity).
* `SolvesApproxBVC t δ ε K A` / `SolvesApproxBVCSync t δ ε K A`: approximate BVC (termination,
  `ε`-agreement on every coordinate, validity) in all runs (resp. all synchronous runs) whose
  correct inputs lie in the input domain `K` (`K = Set.univ` in the paper's lower bounds, a box
  `[ν, U]^d` for its algorithm).
-/

open Cslib.Byzantine.PartialSync Finset

namespace ByzantineVectorConsensus

set_option linter.unusedSectionVars false

/-- Points of `ℝ^d`. -/
abbrev Vec (d : ℕ) := Fin d → ℝ

variable {P M S : Type*} [Fintype P] [DecidableEq P] {d : ℕ}

/-- **Validity** of BVC: the decision lies in the convex hull of the inputs of the correct
processes (the processes in `π(c)`). -/
def bvcValidity (P : Type*) (d : ℕ) : ValidityProperty P (Vec d) (Vec d) :=
  fun c => convexHull ℝ {v | ∃ p, c p = some v}

/-- `ε`-agreement of two decision vectors: every coordinate differs by at most `ε`. -/
def Close (ε : ℝ) (v w : Vec d) : Prop := ∀ l, |v l - w l| ≤ ε

/-- The inputs of all correct processes lie in `K`. -/
def InputsIn (K : Set (Vec d)) (R : Run P M (Vec d)) : Prop := ∀ p ∉ R.faulty, R.inp p ∈ K

/-- `A` solves **approximate BVC** with parameter `ε` and input domain `K`, with at most `t`
Byzantine processes, in every (partially synchronous / asynchronous) run. -/
structure SolvesApproxBVC (t δ : ℕ) (ε : ℝ) (K : Set (Vec d))
    (A : Algorithm P M S (Vec d) (Vec d)) : Prop where
  termination : ∀ R : Run P M (Vec d), R.Valid t δ → InputsIn K R →
    ∀ p ∉ R.faulty, ∃ v, R.Decides A p v
  agreement : ∀ R : Run P M (Vec d), R.Valid t δ → InputsIn K R →
    ∀ p ∉ R.faulty, ∀ q ∉ R.faulty, ∀ v w, R.Decides A p v → R.Decides A q w → Close ε v w
  validity : ∀ R : Run P M (Vec d), R.Valid t δ → InputsIn K R →
    ∀ p ∉ R.faulty, ∀ v, R.Decides A p v → v ∈ bvcValidity P d R.inputConf

/-- `A` solves approximate BVC in every **synchronous** run (`gst = 0`). -/
structure SolvesApproxBVCSync (t δ : ℕ) (ε : ℝ) (K : Set (Vec d))
    (A : Algorithm P M S (Vec d) (Vec d)) : Prop where
  termination : ∀ R : Run P M (Vec d), R.Valid t δ → R.gst = 0 → InputsIn K R →
    ∀ p ∉ R.faulty, ∃ v, R.Decides A p v
  agreement : ∀ R : Run P M (Vec d), R.Valid t δ → R.gst = 0 → InputsIn K R →
    ∀ p ∉ R.faulty, ∀ q ∉ R.faulty, ∀ v w, R.Decides A p v → R.Decides A q w → Close ε v w
  validity : ∀ R : Run P M (Vec d), R.Valid t δ → R.gst = 0 → InputsIn K R →
    ∀ p ∉ R.faulty, ∀ v, R.Decides A p v → v ∈ bvcValidity P d R.inputConf

variable {t δ : ℕ} {ε : ℝ} {K : Set (Vec d)} {A : Algorithm P M S (Vec d) (Vec d)}

/-- An asynchronous solution is a synchronous one. -/
theorem SolvesApproxBVC.sync (h : SolvesApproxBVC t δ ε K A) : SolvesApproxBVCSync t δ ε K A :=
  ⟨fun R hR _ hK => h.termination R hR hK, fun R hR _ hK => h.agreement R hR hK,
    fun R hR _ hK => h.validity R hR hK⟩

/-- An exact solution is an approximate one, for every `ε ≥ 0` and every input domain. -/
theorem approx_of_exact (h : SolvesConsensusSync t δ A (bvcValidity P d))
    (hε : 0 ≤ ε) : SolvesApproxBVCSync t δ ε K A := by
  refine ⟨fun R hR h0 _ => h.termination R hR (R.authValid_none A) h0,
    fun R hR h0 _ p hp q hq v w hv hw => ?_,
    fun R hR h0 _ => h.validity R hR (R.authValid_none A) h0⟩
  obtain rfl := h.agreement R hR (R.authValid_none A) h0 p hp q hq v w hv hw
  intro l; simpa using hε

end ByzantineVectorConsensus
