import Podc.Computability.Distributed.SelfStabilization.EdgeFair

/-!
# Stable computation (Section 3 of Czerner, *Population Protocols Decide Double-exponential
Thresholds*)

The paper defines stable computation once for an arbitrary left-total relation `→` on a set of
configurations in which *some* configurations carry an output `b ∈ {true, false}`:

* a *run* is a sequence `C₀ → C₁ → ⋯` (CSLib's `Cslib.TransitionSystem.Run`);
* a run *stabilises to `b`* if from some index on every configuration has output `b`;
* a run is *fair* if the set of configurations occurring infinitely often is closed under `→`
  (CSLib's global fairness `Run.GloballyFair`).

The definition is reused for population protocols, population programs and population machines.

## Main statements

* `Run.GloballyFair.stabilisesTo_of_reach`: if finitely many configurations are reachable and from
  every reachable configuration one can reach a configuration all of whose successors (reflexively,
  transitively) have output `b`, every fair run stabilises to `b`.
* `reach_stable_of_forall_fair`: the converse for systems with finitely many reachable
  configurations.
* `forall_fair_iff_reach`: both together.
-/

namespace Podc.PPDoubleExpThresholds

open Cslib.TransitionSystem Filter

variable {X : Type*} {R : X → X → Prop}

/-- A run stabilises to `b` (w.r.t. a partial output map `out`) if from some index on every
configuration has output `b`. -/
def StabilisesTo (out : X → Option Bool) (E : Run R) (b : Bool) : Prop :=
  ∃ i, ∀ j ≥ i, out (E.st j) = some b

/-- `x` is *stable with output `b`*: every configuration reachable from `x` has output `b`. -/
def StableOut (R : X → X → Prop) (out : X → Option Bool) (b : Bool) (x : X) : Prop :=
  ∀ y, Reach R x y → out y = some b

theorem StableOut.reach {out : X → Option Bool} {b : Bool} {x y : X} (h : StableOut R out b x)
    (hxy : Reach R x y) : StableOut R out b y := fun z hz => h z (hxy.trans hz)

/-- Under global fairness, if only finitely many configurations are reachable from the start and
from every reachable configuration a `b`-stable configuration is reachable, the run stabilises to
`b`. -/
theorem Run.GloballyFair.stabilisesTo_of_reach {E : Run R} (hE : E.GloballyFair)
    {out : X → Option Bool} {b : Bool} (hfin : {x | Reach R (E.st 0) x}.Finite)
    (h : ∀ x, Reach R (E.st 0) x → ∃ y, Reach R x y ∧ StableOut R out b y) :
    StabilisesTo out E b := by
  obtain ⟨x, hx⟩ := E.exists_frequently_eq_of_finite hfin
  obtain ⟨t₀, -, ht₀⟩ := frequently_atTop.1 hx 0
  obtain ⟨y, hxy, hy⟩ := h x (ht₀ ▸ E.reach t₀)
  obtain ⟨t, ht⟩ := (hE.frequently_of_reach hx hxy).exists
  exact ⟨t, fun j hj => hy _ (ht ▸ E.reach_of_le hj)⟩

theorem frequently_shift {p : ℕ → Prop} (k : ℕ) :
    (∃ᶠ t in atTop, p (t + k)) ↔ ∃ᶠ t in atTop, p t := by
  simp only [frequently_atTop]
  constructor
  · intro h T
    obtain ⟨t, ht, hp⟩ := h T
    exact ⟨t + k, by omega, hp⟩
  · intro h T
    obtain ⟨t, ht, hp⟩ := h (T + k)
    exact ⟨t - k, by omega, by rwa [Nat.sub_add_cancel (by omega)]⟩

/-- Shifting a run does not affect global fairness. -/
theorem Run.globallyFair_of_shift {E E' : Run R} {k : ℕ}
    (h : ∀ t, E'.st (t + k) = E.st t) (hE : E.GloballyFair) : E'.GloballyFair := by
  intro x y hxy hx
  have hx' : ∃ᶠ t in atTop, E.st t = x := by
    rw [← frequently_shift k] at hx; simpa only [h] using hx
  have := hE x y hxy hx'
  rw [← frequently_shift k]; simpa only [h] using this

/-- Prepending a finite path to a run. -/
theorem Run.exists_prefix {x y : X} (hxy : Reach R x y) (E : Run R) (hE : E.st 0 = y) :
    ∃ (E' : Run R) (k : ℕ), E'.st 0 = x ∧ ∀ t, E'.st (t + k) = E.st t := by
  induction hxy using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨E, 0, hE, fun _ => rfl⟩
  | @head a b hab _ ih =>
    obtain ⟨E', k, h0, hk⟩ := ih
    refine ⟨⟨fun t => Nat.casesOn t a E'.st, fun t => ?_⟩, k + 1, rfl, fun t => ?_⟩
    · cases t with
      | zero => show R a (E'.st 0); exact h0 ▸ hab
      | succ t => exact E'.step t
    · show E'.st (t + k) = _
      exact hk t

/-- Converse of `stabilisesTo_of_reach`: if finitely many configurations are reachable from `x₀`,
every configuration reachable from `x₀` has a successor, and every fair run from `x₀` stabilises
to `b`, then from every configuration reachable from `x₀` a `b`-stable configuration is
reachable. -/
theorem reach_stable_of_forall_fair {x₀ : X} (hfin : {x | Reach R x₀ x}.Finite)
    (htot : ∀ x, Reach R x₀ x → ∃ y, R x y) {out : X → Option Bool} {b : Bool}
    (h : ∀ E : Run R, E.st 0 = x₀ → E.GloballyFair → StabilisesTo out E b) :
    ∀ x, Reach R x₀ x → ∃ y, Reach R x y ∧ StableOut R out b y := by
  intro x hx
  have hfinx : {y | Reach R x y}.Finite := hfin.subset fun y hy => hx.trans hy
  obtain ⟨E, hE0, hE⟩ := exists_edgeFair hfinx (fun y hy => htot y (hx.trans hy))
  have hEf := hE.globallyFair
  obtain ⟨E', k, hE'0, hk⟩ := Run.exists_prefix hx E hE0
  obtain ⟨i, hi⟩ := h E' hE'0 (Run.globallyFair_of_shift hk hEf)
  obtain ⟨y, hy⟩ := E.exists_frequently_eq_of_finite (hE0 ▸ hfinx)
  obtain ⟨t₁, -, ht₁⟩ := frequently_atTop.1 hy 0
  refine ⟨y, hE0 ▸ ht₁ ▸ E.reach t₁, fun z hz => ?_⟩
  obtain ⟨t, ht, htz⟩ := frequently_atTop.1 (hEf.frequently_of_reach hy hz) i
  rw [← htz, ← hk t]
  exact hi _ (by omega)

/-- **Reachability characterization of stable computation** (finitely many reachable
configurations, no deadlocks): every fair run from `x₀` stabilises to `b` iff every
configuration reachable from `x₀` can reach a `b`-stable configuration. -/
theorem forall_fair_iff_reach {x₀ : X} (hfin : {x | Reach R x₀ x}.Finite)
    (htot : ∀ x, Reach R x₀ x → ∃ y, R x y) {out : X → Option Bool} {b : Bool} :
    (∀ E : Run R, E.st 0 = x₀ → E.GloballyFair → StabilisesTo out E b) ↔
      ∀ x, Reach R x₀ x → ∃ y, Reach R x y ∧ StableOut R out b y :=
  ⟨reach_stable_of_forall_fair hfin htot, fun h E hE0 hE =>
    Run.GloballyFair.stabilisesTo_of_reach hE (hE0 ▸ hfin) (hE0 ▸ h)⟩

end Podc.PPDoubleExpThresholds
