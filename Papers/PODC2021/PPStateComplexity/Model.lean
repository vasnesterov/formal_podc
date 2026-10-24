import Podc.Computability.Distributed.PopulationProtocols.Multiset.PotentialReach

/-!
# Population protocols with leaders deciding `x ≥ η` (Section 2 of Czerner–Esparza–Leroux)

The model of Section 2.2: a protocol `P = (Q, T, L, {x}, I, O)` with a single input variable `x`
(we store the input state `I(x)` as `P.x`), a *leader multiset* `L`, transitions `T ⊆ Q² × Q²`
(total: every pair of states has a transition) and outputs `O : Q → Bool`. Configurations are
multisets of states (CSLib/Podc multiset model `Cslib.PopulationProtocol`). The initial
configuration of input `i` is `IC(i) = L + i · x`; inputs have at least two agents (`2 ≤ i`).

An execution is fair if every configuration reachable infinitely often is visited infinitely
often: this is CSLib's *global fairness* `Cslib.TransitionSystem.Run.GloballyFair`. The protocol
computes `x ≥ η` (`Protocol.ComputesGe`) if every fair execution from `IC(i)`, `i ≥ 2`, eventually
stays in consensus `decide (η ≤ i)`.

## Main statements

* `Protocol.computesGe_iff`: the reachability characterization stated after Definition 2:
  `P` computes `x ≥ η` iff every configuration reachable from `IC(i)` can reach a
  `decide (η ≤ i)`-stable configuration.
* Monotonicity of reachability (`MReach.add_right`, `MReach.add`, `MReach.nsmul`).
-/

namespace Podc.PPStateComplexity

open Cslib Cslib.PopulationProtocol Cslib.TransitionSystem Filter

variable {Q : Type*} [DecidableEq Q]

/-! ### Monotonicity -/

-- CSLib candidate (Multiset population protocols: monotonicity)
theorem Transition.Fires.add_right {t : Transition Q} {C C' : Multiset Q} (h : t.Fires C C')
    (D : Multiset Q) : t.Fires (C + D) (C' + D) := by
  refine ⟨h.1.trans (Multiset.le_add_right _ _), ?_⟩
  rw [h.2]
  ext q
  have := Multiset.count_le_of_le q h.1
  simp only [Multiset.count_add, Multiset.count_sub]
  omega

-- CSLib candidate
/-- **Monotonicity**: adding agents preserves reachability. -/
theorem MReach.add_right {T : Set (Transition Q)} {C C' : Multiset Q} (h : MReach T C C')
    (D : Multiset Q) : MReach T (C + D) (C' + D) := by
  induction h with
  | refl => exact .refl
  | tail _ hs ih =>
    obtain ⟨t, ht, hf⟩ := hs
    exact ih.tail ⟨t, ht, Transition.Fires.add_right hf D⟩

-- CSLib candidate
theorem MReach.add_left {T : Set (Transition Q)} {C C' : Multiset Q} (h : MReach T C C')
    (D : Multiset Q) : MReach T (D + C) (D + C') := by
  simpa only [add_comm D] using MReach.add_right h D

-- CSLib candidate
theorem MReach.add {T : Set (Transition Q)} {C C' D D' : Multiset Q} (h₁ : MReach T C C')
    (h₂ : MReach T D D') : MReach T (C + D) (C' + D') :=
  (MReach.add_right h₁ D).trans (MReach.add_left h₂ C')

-- CSLib candidate
theorem MReach.nsmul {T : Set (Transition Q)} {C C' : Multiset Q} (h : MReach T C C') (k : ℕ) :
    MReach T (k • C) (k • C') := by
  induction k with
  | zero => simpa using (Relation.ReflTransGen.refl : MReach T 0 0)
  | succ k ih => simpa only [succ_nsmul] using MReach.add ih h

/-! ### Protocols -/

/-- A population protocol `(Q, T, L, {x}, I, O)` with one input variable and leaders
(Section 2.2). The input state `I(x)` is `x`. -/
structure Protocol (Q : Type*) where
  /-- The transitions `p, q ↦ p', q'`. -/
  T : Set (Transition Q)
  /-- For every pair of states there is at least one transition. -/
  total : ∀ p q, ∃ p' q', (⟨p, q, p', q'⟩ : Transition Q) ∈ T
  /-- The leader multiset `L`. -/
  L : Multiset Q
  /-- The input state `I(x)`. -/
  x : Q
  /-- The output map `O`. -/
  O : Q → Bool

namespace Protocol

variable (P : Protocol Q)

/-- The underlying multiset protocol (no leaders, input alphabet `Unit`). -/
def toM : MProtocol Q Unit := ⟨P.T, P.total, fun _ => P.x, P.O⟩

/-- One step `C → C'`. -/
abbrev Step : Multiset Q → Multiset Q → Prop := MStep P.T

/-- Reachability `C →* C'`. -/
abbrev Reach : Multiset Q → Multiset Q → Prop := MReach P.T

/-- The initial configuration `IC(i) = L + i · x`. -/
def IC (i : ℕ) : Multiset Q := P.L + Multiset.replicate i P.x

/-- `P` is leaderless. -/
def Leaderless : Prop := P.L = 0

/-- `C` is a consensus with output `b`: all agents output `b` (`O(C) = b`). -/
abbrev Out (C : Multiset Q) (b : Bool) : Prop := IsConsensus P.O C b

/-- **Computing `x ≥ η`** (Section 2.2): every fair execution from an input `i ≥ 2` has output
`[η ≤ i]`, i.e. eventually all its configurations are consensus configurations with that output. -/
def ComputesGe (η : ℕ) : Prop :=
  ∀ i, 2 ≤ i → ∀ E : Run P.Step, E.st 0 = P.IC i → E.GloballyFair →
    ∀ᶠ t in atTop, P.Out (E.st t) (decide (η ≤ i))

/-- **Definition 2.** `C` is `b`-stable: every configuration reachable from `C` has output `b`.
(`SC_b`; we write `SC` for `SC_0 ∪ SC_1`, `Protocol.SC`.) -/
def Stable (b : Bool) (C : Multiset Q) : Prop := ∀ C', P.Reach C C' → P.Out C' b

/-- The set `SC = SC_0 ∪ SC_1` of stable configurations. -/
def SC (C : Multiset Q) : Prop := P.Stable false C ∨ P.Stable true C

variable {P}

theorem IC_add (i j : ℕ) : P.IC (i + j) = P.IC i + Multiset.replicate j P.x := by
  simp [IC, Multiset.replicate_add, add_assoc]

theorem IC_leaderless (hL : P.Leaderless) (i : ℕ) : P.IC i = Multiset.replicate i P.x := by
  rw [IC, show P.L = 0 from hL, zero_add]

theorem card_IC (i : ℕ) : Multiset.card (P.IC i) = Multiset.card P.L + i := by
  simp [IC]

theorem Stable.out {b : Bool} {C : Multiset Q} (h : P.Stable b C) : P.Out C b := h C .refl

theorem Stable.reach {b : Bool} {C C' : Multiset Q} (h : P.Stable b C) (hC : P.Reach C C') :
    P.Stable b C' := fun _ h' => h _ (hC.trans h')

/-- A nonempty configuration has at most one output. -/
theorem Out.eq {C : Multiset Q} {b b' : Bool} (h : P.Out C b) (h' : P.Out C b') (hC : C ≠ 0) :
    b = b' := by
  obtain ⟨q, hq⟩ := Multiset.exists_mem_of_ne_zero hC
  exact (h q hq).symm.trans (h' q hq)

theorem Reach.card_eq {C C' : Multiset Q} (h : P.Reach C C') :
    Multiset.card C' = Multiset.card C := MReach.card_eq h

/-- Every configuration with at least two agents has a successor. -/
theorem exists_step {C : Multiset Q} (hC : 2 ≤ Multiset.card C) : ∃ C', P.Step C C' :=
  MProtocol.exists_step (P := P.toM) hC

/-! ### Fair runs through a given configuration -/

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

theorem eventually_shift {p : ℕ → Prop} (k : ℕ) :
    (∀ᶠ t in atTop, p (t + k)) ↔ ∀ᶠ t in atTop, p t := by
  have := frequently_shift (p := fun t => ¬ p t) k
  rw [← not_iff_not]
  simpa only [not_eventually] using this

/-- Global fairness only depends on a suffix. -/
theorem globallyFair_of_shift {X : Type*} {R : X → X → Prop} {E E' : Run R} {k : ℕ}
    (h : ∀ t, E'.st (t + k) = E.st t) (hE : E.GloballyFair) : E'.GloballyFair := by
  intro x y hxy hx
  have hx' : ∃ᶠ t in atTop, E.st t = x := by
    rw [← frequently_shift k] at hx; simpa only [h] using hx
  have := hE x y hxy hx'
  rw [← frequently_shift k]; simpa only [h] using this

/-- Prepending a finite path to a run. -/
theorem exists_run_prefix {X : Type*} {R : X → X → Prop} {x y : X}
    (hxy : Relation.ReflTransGen R x y) (E : Run R) (hE : E.st 0 = y) :
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

variable [Fintype Q]

/-- From every configuration with at least two agents there is a globally fair run. -/
theorem exists_fair_run {C : Multiset Q} (hC : 2 ≤ Multiset.card C) :
    ∃ E : Run P.Step, E.st 0 = C ∧ E.GloballyFair := by
  obtain ⟨E, h0, hE⟩ := exists_edgeFair (R := P.Step) (MReach.finite C)
    (fun C' hC' => exists_step (by rw [MReach.card_eq hC']; exact hC))
  exact ⟨E, h0, hE.globallyFair⟩

/-- In a globally fair run that eventually has output `b`, some configuration reachable from the
start is `b`-stable. -/
theorem exists_stable_of_eventually {E : Run P.Step} (hE : E.GloballyFair) {b : Bool}
    (hb : ∀ᶠ t in atTop, P.Out (E.st t) b) : ∃ C, P.Reach (E.st 0) C ∧ P.Stable b C := by
  obtain ⟨x, hx⟩ := E.exists_frequently_eq_of_finite (MReach.finite _)
  obtain ⟨t₀, ht₀⟩ := eventually_atTop.1 hb
  obtain ⟨t₁, -, ht₁⟩ := frequently_atTop.1 hx 0
  refine ⟨x, ht₁ ▸ E.reach t₁, fun y hy => ?_⟩
  obtain ⟨t, ht, hty⟩ := frequently_atTop.1 (hE.frequently_of_reach hx hy) t₀
  exact hty ▸ ht₀ t ht

/-- **Reachability characterization** (after Definition 2): `P` computes `x ≥ η` iff for every
input `i ≥ 2` every configuration reachable from `IC(i)` can reach a `[η ≤ i]`-stable
configuration. -/
theorem computesGe_iff {η : ℕ} : P.ComputesGe η ↔
    ∀ i, 2 ≤ i → ∀ C, P.Reach (P.IC i) C → ∃ C', P.Reach C C' ∧ P.Stable (decide (η ≤ i)) C' := by
  constructor
  · intro h i hi C hC
    have hcard : 2 ≤ Multiset.card C := by rw [hC.card_eq, card_IC]; omega
    obtain ⟨E, hE0, hE⟩ := exists_fair_run (P := P) hcard
    obtain ⟨E', k, hE'0, hk⟩ := exists_run_prefix hC E hE0
    have hev := h i hi E' hE'0 (globallyFair_of_shift hk hE)
    rw [← eventually_shift k] at hev
    simp only [hk] at hev
    obtain ⟨C', h1, h2⟩ := exists_stable_of_eventually hE hev
    exact ⟨C', hE0 ▸ h1, h2⟩
  · intro h i hi E hE0 hE
    have hS : IsTrap P.Step {C | P.Stable (decide (η ≤ i)) C} :=
      fun _ _ hx hxy => hx.reach (.single hxy)
    have := hE.eventually_mem_of_finite (MReach.finite _) hS (fun C hC => by
      obtain ⟨C', h1, h2⟩ := h i hi C (hE0 ▸ hC)
      exact ⟨C', h2, h1⟩)
    exact this.mono fun t ht => Stable.out ht

/-- If `P` computes `x ≥ η`, every configuration reachable from an input `i ≥ 2` that is
`b`-stable has `b = [η ≤ i]`. -/
theorem ComputesGe.stable_eq {η : ℕ} (h : P.ComputesGe η) {i : ℕ} (hi : 2 ≤ i) {C : Multiset Q}
    (hC : P.Reach (P.IC i) C) {b : Bool} (hb : P.Stable b C) : b = decide (η ≤ i) := by
  obtain ⟨C', h1, h2⟩ := computesGe_iff.1 h i hi C hC
  have hne : C' ≠ 0 := by
    intro h0
    have := MReach.card_eq (hC.trans h1)
    rw [h0, card_IC] at this
    simp at this; omega
  exact (hb C' h1).eq h2.out hne

/-- If `P` computes `x ≥ η`, every configuration reachable from an input `i ≥ 2` reaches `SC`. -/
theorem ComputesGe.exists_SC {η : ℕ} (h : P.ComputesGe η) {i : ℕ} (hi : 2 ≤ i) {C : Multiset Q}
    (hC : P.Reach (P.IC i) C) : ∃ C', P.Reach C C' ∧ P.SC C' := by
  obtain ⟨C', h1, h2⟩ := computesGe_iff.1 h i hi C hC
  refine ⟨C', h1, ?_⟩
  cases hd : decide (η ≤ i)
  · exact .inl (hd ▸ h2)
  · exact .inr (hd ▸ h2)

end Protocol

end Podc.PPStateComplexity
