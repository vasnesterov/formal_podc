import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.EMetricSpace.BoundedVariation
import Mathlib.Algebra.Ring.Periodic

-- CSLib candidate: Cslib/Computability/Distributed/MobileRobots/Model.lean

/-!
# Oblivious mobile robots in the plane under centralized schedulers

A model of the standard OBLOT robots (Suzuki–Yamashita; Flocchini–Prencipe–Santoro), restricted to
*centralized* (sequential) schedulers, which activate exactly one robot per step; the Round-Robin
scheduler is the main example.

* The plane is `ℂ`. A configuration of `n` robots is `Config n := Fin n → ℂ`.
* **Frames.** Upon each activation the adversary picks a local coordinate system (`Frame`) of the
  activated robot, centred at the robot: a similarity `v ↦ a * v` or `v ↦ a * conj v` (`a ≠ 0`).
  The modulus of `a` is the inverse of the perceived unit length, its argument the rotation, and
  `mirror` the handedness. Restricting the frames (`frameOK`) gives the usual consistency
  assumptions: `Frame.UnitLength` (consistent unit length), `Frame.Chiral` (common chirality), …
  Choosing frames afresh at each activation is *variable disorientation*.
* **Views.** The robot sees the *set* (`Finset`) of robot positions in its frame
  (`view`): no multiplicity detection, not even for its own location, which is always the origin.
* **Algorithms.** Robots are oblivious, anonymous and uniform: one `Algorithm` maps the view to a
  trajectory `ℝ → ℂ` in local coordinates (parametrized by `[0, 1]`; the target is the value at 1).
* **Movement.** The adversary also picks a stopping parameter `s`; a `Movement` model says which
  ones are admissible, always including `s = 1` (the robot reaches its target). `Movement.rigid`
  allows only `s = 1`; `Movement.nonrigid δ` also allows stopping once the robot has travelled
  (arc length, `eVariationOn`) at least `δ`.
* **Executions.** `run A act adv P₀` is the execution from `P₀` where robot `act t` is activated at
  step `t` and the adaptive adversary `adv` picks frames and stops. `Legal` says the adversary's
  choices along the run are allowed.
* `Solves n A sched frameOK M init`: under every schedule allowed by `sched`, from every initial
  configuration satisfying `init`, against every legal adversary, the robots eventually stay
  gathered forever. Gathering: `init = fun _ => True`; Distinct Gathering: `init = Injective`.
-/

noncomputable section

namespace Cslib.MobileRobots

open ComplexConjugate

/-! ### Frames -/

/-- A local coordinate system centred at the observing robot: global vectors `v` are seen as
`coef * v` (or `coef * conj v` if `mirror`). -/
structure Frame where
  /-- Rotation and scaling of the frame. -/
  coef : ℂ
  coef_ne_zero : coef ≠ 0
  /-- Whether the frame has the opposite handedness. -/
  mirror : Bool

namespace Frame

/-- Global vector → local coordinates. -/
def toLocal (f : Frame) (v : ℂ) : ℂ := f.coef * (if f.mirror then conj v else v)

/-- Local coordinates → global vector. -/
def toGlobal (f : Frame) (w : ℂ) : ℂ := if f.mirror then conj (w / f.coef) else w / f.coef

@[simp] lemma toGlobal_toLocal (f : Frame) (v : ℂ) : f.toGlobal (f.toLocal v) = v := by
  have := f.coef_ne_zero
  cases h : f.mirror <;> simp [toGlobal, toLocal, h, mul_div_cancel_left₀ _ this]

@[simp] lemma toLocal_toGlobal (f : Frame) (w : ℂ) : f.toLocal (f.toGlobal w) = w := by
  have := f.coef_ne_zero
  cases h : f.mirror <;> simp [toGlobal, toLocal, h, mul_div_cancel₀ _ this]

lemma toLocal_injective (f : Frame) : Function.Injective f.toLocal :=
  Function.LeftInverse.injective f.toGlobal_toLocal

@[simp] lemma toLocal_zero (f : Frame) : f.toLocal 0 = 0 := by simp [toLocal]

@[simp] lemma toGlobal_zero (f : Frame) : f.toGlobal 0 = 0 := by simp [toGlobal]

@[simp] lemma toLocal_eq_zero_iff (f : Frame) (v : ℂ) : f.toLocal v = 0 ↔ v = 0 :=
  ⟨fun h => f.toLocal_injective (h.trans f.toLocal_zero.symm), fun h => h ▸ f.toLocal_zero⟩

lemma toGlobal_smul (f : Frame) (r : ℝ) (w : ℂ) : f.toGlobal ((r : ℂ) * w) = r * f.toGlobal w := by
  cases h : f.mirror <;> simp [toGlobal, h, mul_div_assoc]

/-- The orientation-preserving frame `v ↦ a * v`. -/
def ofCoef (a : ℂ) (ha : a ≠ 0) : Frame := ⟨a, ha, false⟩

@[simp] lemma ofCoef_toLocal (a : ℂ) (ha : a ≠ 0) (v : ℂ) : (ofCoef a ha).toLocal v = a * v := by
  simp [ofCoef, toLocal]

@[simp] lemma ofCoef_toGlobal (a : ℂ) (ha : a ≠ 0) (w : ℂ) : (ofCoef a ha).toGlobal w = w / a := by
  simp [ofCoef, toGlobal]

/-- The global frame itself. -/
def id : Frame := ofCoef 1 one_ne_zero

/-- The frame perceives the true unit length (consistent unit length). -/
def UnitLength (f : Frame) : Prop := ‖f.coef‖ = 1

/-- The frame has the global handedness (common chirality). -/
def Chiral (f : Frame) : Prop := f.mirror = false

end Frame

/-! ### Configurations, views, algorithms -/

/-- Positions of `n` robots in the plane. -/
abbrev Config (n : ℕ) := Fin n → ℂ

variable {n : ℕ}

/-- All robots are at the same point. -/
def Gathered (P : Config n) : Prop := ∀ i j, P i = P j

/-- The snapshot taken by robot `r` in configuration `P` with frame `f`: the set of all robot
positions in local coordinates (so it contains `0`, and multiplicities are invisible). -/
def view (P : Config n) (r : Fin n) (f : Frame) : Finset ℂ :=
  Finset.univ.image fun j => f.toLocal (P j - P r)

/-- A trajectory in local coordinates, parametrized by `[0, 1]`; its target is the value at `1`. -/
abbrev Trajectory := ℝ → ℂ

/-- An algorithm of oblivious, anonymous, uniform robots: the trajectory as a function of the
snapshot. -/
abbrev Algorithm := Finset ℂ → Trajectory

/-- A movement model: the stopping parameters the adversary may choose for a global trajectory.
Reaching the target (`s = 1`) is always allowed. -/
structure Movement where
  /-- `Admissible Γ s`: the robot following the global trajectory `Γ` may be stopped at `Γ s`. -/
  Admissible : (ℝ → ℂ) → ℝ → Prop
  admissible_one : ∀ Γ, Admissible Γ 1

/-- Rigid movement: every robot reaches its target. -/
def Movement.rigid : Movement := ⟨fun _ s => s = 1, fun _ => rfl⟩

/-- Non-rigid movement with minimum movement distance `δ`: the robot may be stopped at any point
of its trajectory once it has travelled a distance of at least `δ`. -/
def Movement.nonrigid (δ : ℝ) : Movement :=
  ⟨fun Γ s => s = 1 ∨ (0 ≤ s ∧ s ≤ 1 ∧ ENNReal.ofReal δ ≤ eVariationOn Γ (Set.Icc 0 s)),
    fun _ => Or.inl rfl⟩

/-- The global trajectory of robot `r` in `P` that follows the local trajectory `γ` in frame `f`. -/
def globalTraj (P : Config n) (r : Fin n) (f : Frame) (γ : Trajectory) : ℝ → ℂ :=
  fun s => P r + f.toGlobal (γ s)

/-- One Look-Compute-Move cycle of robot `r` with frame `f`, stopped at parameter `s`. -/
def step (A : Algorithm) (P : Config n) (r : Fin n) (f : Frame) (s : ℝ) : Config n :=
  Function.update P r (globalTraj P r f (A (view P r f)) s)

/-- An adaptive adversary: given the step number and the current configuration, it chooses the
frame of the activated robot and where to stop it. -/
structure Adversary (n : ℕ) where
  /-- Frame of the robot activated at step `t` in configuration `P`. -/
  frame : ℕ → Config n → Frame
  /-- Stopping parameter at step `t` in configuration `P`. -/
  stop : ℕ → Config n → ℝ

/-- The rigid adversary using the frames `F`. -/
def Adversary.rigidOf (F : ℕ → Config n → Frame) : Adversary n := ⟨F, fun _ _ => 1⟩

/-- The execution: robot `act t` performs a cycle at step `t`. -/
def run (A : Algorithm) (act : ℕ → Fin n) (adv : Adversary n) (P₀ : Config n) : ℕ → Config n
  | 0 => P₀
  | t + 1 => let P := run A act adv P₀ t
      step A P (act t) (adv.frame t P) (adv.stop t P)

@[simp] lemma run_zero (A : Algorithm) (act : ℕ → Fin n) (adv : Adversary n) (P₀ : Config n) :
    run A act adv P₀ 0 = P₀ := rfl

lemma run_succ (A : Algorithm) (act : ℕ → Fin n) (adv : Adversary n) (P₀ : Config n) (t : ℕ) :
    run A act adv P₀ (t + 1) = step A (run A act adv P₀ t) (act t)
      (adv.frame t (run A act adv P₀ t)) (adv.stop t (run A act adv P₀ t)) := rfl

/-- The adversary only uses allowed frames and admissible stops along the execution. -/
def Legal (A : Algorithm) (act : ℕ → Fin n) (adv : Adversary n) (P₀ : Config n)
    (frameOK : Frame → Prop) (M : Movement) : Prop :=
  ∀ t, let P := run A act adv P₀ t
    frameOK (adv.frame t P) ∧
      M.Admissible (globalTraj P (act t) (adv.frame t P) (A (view P (act t) (adv.frame t P))))
        (adv.stop t P)

lemma legal_rigidOf (A : Algorithm) (act : ℕ → Fin n) (F : ℕ → Config n → Frame) (P₀ : Config n)
    {frameOK : Frame → Prop} (M : Movement) (hF : ∀ t P, frameOK (F t P)) :
    Legal A act (Adversary.rigidOf F) P₀ frameOK M :=
  fun _ => ⟨hF _ _, M.admissible_one _⟩

/-! ### Schedulers and the problem -/

/-- The Round-Robin scheduler: the robots are activated one at a time in a fixed order, repeated
forever. -/
def IsRoundRobin (act : ℕ → Fin n) : Prop :=
  Function.Periodic act n ∧ ∀ i j, i < n → j < n → act i = act j → i = j

/-- `A` solves the gathering problem under the scheduler `sched`, frame restriction `frameOK`,
movement model `M`, for initial configurations satisfying `init`: every legal execution eventually
stays gathered forever. -/
def Solves (n : ℕ) (A : Algorithm) (sched : (ℕ → Fin n) → Prop) (frameOK : Frame → Prop)
    (M : Movement) (init : Config n → Prop) : Prop :=
  ∀ act, sched act → ∀ P₀, init P₀ → ∀ adv : Adversary n, Legal A act adv P₀ frameOK M →
    ∃ T, ∀ t, T ≤ t → Gathered (run A act adv P₀ t)

/-- Solvability is monotone: fewer frames, schedules, stops or initial configurations make the
problem easier. -/
lemma Solves.mono {A : Algorithm} {sched sched' : (ℕ → Fin n) → Prop}
    {frameOK frameOK' : Frame → Prop} {M M' : Movement} {init init' : Config n → Prop}
    (h : Solves n A sched frameOK M init) (hs : ∀ a, sched' a → sched a)
    (hf : ∀ f, frameOK' f → frameOK f)
    (hM : ∀ Γ s, M'.Admissible Γ s → M.Admissible Γ s) (hi : ∀ P, init' P → init P) :
    Solves n A sched' frameOK' M' init' := by
  intro act hact P₀ hP₀ adv hadv
  exact h act (hs _ hact) P₀ (hi _ hP₀) adv fun t => ⟨hf _ (hadv t).1, hM _ _ (hadv t).2⟩

/-! ### Basic facts -/

lemma view_mem_zero (P : Config n) (r : Fin n) (f : Frame) : (0 : ℂ) ∈ view P r f :=
  Finset.mem_image.2 ⟨r, Finset.mem_univ _, by simp⟩

lemma step_apply_self (A : Algorithm) (P : Config n) (r : Fin n) (f : Frame) (s : ℝ) :
    step A P r f s r = P r + f.toGlobal (A (view P r f) s) := by
  simp [step, globalTraj]

lemma step_apply_ne (A : Algorithm) (P : Config n) {r j : Fin n} (f : Frame) (s : ℝ) (h : j ≠ r) :
    step A P r f s j = P j := by
  simp [step, h]

/-- **First gathering step.** If a single move turns a non-gathered configuration into a gathered
one, then before the move all robots except the mover were at one point `P j` and the mover lands
exactly there. -/
lemma first_gather (A : Algorithm) {P : Config n} {r : Fin n} {f : Frame} {s : ℝ}
    (hP : ¬ Gathered P) (hQ : Gathered (step A P r f s)) :
    (∀ i j, i ≠ r → j ≠ r → P i = P j) ∧ ∀ j, j ≠ r → step A P r f s r = P j ∧ P r ≠ P j := by
  have key : ∀ i, i ≠ r → step A P r f s i = P i := fun i hi => step_apply_ne A P f s hi
  refine ⟨fun i j hi hj => by rw [← key i hi, ← key j hj]; exact hQ i j, fun j hj => ⟨?_, ?_⟩⟩
  · rw [← key j hj]; exact hQ r j
  · intro hrj
    apply hP
    intro a b
    have h1 : ∀ c, P c = P j := by
      intro c
      by_cases hc : c = r
      · rw [hc, hrj]
      · rw [← key c hc, ← key j hj]; exact hQ c j
    rw [h1 a, h1 b]

end Cslib.MobileRobots

end
