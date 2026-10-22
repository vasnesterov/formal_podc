/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
-- CSLib candidate: Cslib/Computability/Distributed/SelfStabilization/EdgeFair.lean
import Cslib.Computability.Distributed.SelfStabilization.TransitionSystem

/-!
# Edge fairness, silent runs and termination

For a transition relation `R : X → X → Prop` (on a possibly infinite configuration space, but with
finitely many configurations reachable from each one):

* `Run.EdgeFair E`: *edge (strong global) fairness*: every transition `x → y` from a configuration
  occurring infinitely often is *taken* infinitely often (`E.st t = x ∧ E.st (t+1) = y`). This is
  the notion of fairness of Esparza et al. for population protocols; it implies CSLib's state-based
  `Run.GloballyFair` (`Run.EdgeFair.globallyFair`).
* `Run.Silent E`: the run is eventually constant.

## Main statements

* `exists_edgeFair`: edge-fair runs exist from every configuration, provided finitely many
  configurations are reachable and every reachable configuration has a successor.
* `Run.GloballyFair.eventually_mem_of_finite`: CSLib's `GloballyFair.eventually_mem` with "finitely
  many reachable configurations" instead of `[Finite X]`.
* `forall_edgeFair_silent_iff`: every edge-fair run is silent iff from every configuration a
  silent (terminal) configuration is reachable (*silence = termination*).
* `exists_run_of_reach_isSilent`: a path to a silent configuration with a self-loop extends to an
  edge-fair run that stays there forever.
-/

namespace Cslib.TransitionSystem

open Filter

variable {X : Type*} {R : X → X → Prop}

/-- *Edge fairness*: if `x` occurs infinitely often and `x → y`, then the transition `x → y` is
taken infinitely often. -/
def Run.EdgeFair (E : Run R) : Prop :=
  ∀ x y, R x y → (∃ᶠ t in atTop, E.st t = x) → ∃ᶠ t in atTop, E.st t = x ∧ E.st (t + 1) = y

/-- A run is *silent* if it is eventually constant. -/
def Run.Silent (E : Run R) : Prop := ∃ n, ∀ t ≥ n, E.st t = E.st n

/-- Edge fairness implies (state-based) global fairness. -/
theorem Run.EdgeFair.globallyFair {E : Run R} (hE : E.EdgeFair) : E.GloballyFair := by
  intro x y hxy hx
  have h := hE x y hxy hx
  rw [frequently_atTop] at h ⊢
  intro T
  obtain ⟨t, ht, -, hy⟩ := h T
  exact ⟨t + 1, by omega, hy⟩

/-- Pigeonhole for frequently: if `P` holds frequently and `f` takes values in a finite set along
the times where `P` holds, then frequently `P t ∧ f t = a` for some `a`. -/
theorem exists_frequently_and_eq {α : Type*} {P : ℕ → Prop} {f : ℕ → α} {S : Set α}
    (hS : S.Finite) (hfS : ∀ t, P t → f t ∈ S) (hP : ∃ᶠ t in atTop, P t) :
    ∃ a ∈ S, ∃ᶠ t in atTop, P t ∧ f t = a := by
  by_contra hcon
  have : ∀ᶠ t in atTop, ∀ a ∈ S, ¬ (P t ∧ f t = a) := by
    rw [hS.eventually_all]
    intro a ha
    exact not_frequently.1 fun h => hcon ⟨a, ha, h⟩
  apply hP
  filter_upwards [this] with t ht hPt
  exact ht _ (hfS t hPt) ⟨hPt, rfl⟩

/-- Along a run, all configurations are reachable from the start. -/
theorem Run.mem_reach (E : Run R) (t : ℕ) : E.st t ∈ {y | Reach R (E.st 0) y} := E.reach t

/-- If finitely many configurations are reachable from the start, some configuration occurs
infinitely often. -/
theorem Run.exists_frequently_eq_of_finite (E : Run R) (hfin : {y | Reach R (E.st 0) y}.Finite) :
    ∃ x, ∃ᶠ t in atTop, E.st t = x := by
  obtain ⟨a, -, ha⟩ := exists_frequently_and_eq (P := fun _ => True) hfin
    (fun t _ => E.mem_reach t) (frequently_atTop.2 fun T => ⟨T, le_rfl, trivial⟩)
  exact ⟨a, ha.mono fun _ h => h.2⟩

/-- CSLib's `GloballyFair.eventually_mem` with finitely many reachable configurations instead of
finitely many configurations. -/
theorem Run.GloballyFair.eventually_mem_of_finite {E : Run R} (hE : E.GloballyFair) {S : Set X}
    (hfin : {y | Reach R (E.st 0) y}.Finite) (hS : IsTrap R S)
    (h : ∀ x, Reach R (E.st 0) x → ∃ y ∈ S, Reach R x y) : ∀ᶠ t in atTop, E.st t ∈ S := by
  obtain ⟨x, hx⟩ := E.exists_frequently_eq_of_finite hfin
  obtain ⟨t₀, -, ht₀⟩ := frequently_atTop.1 hx 0
  obtain ⟨y, hyS, hxy⟩ := h x (ht₀ ▸ E.reach t₀)
  obtain ⟨t, ht⟩ := (hE.frequently_of_reach hx hxy).exists
  exact eventually_atTop.2 ⟨t, fun s hs => hS.reach (ht ▸ hyS) (E.reach_of_le hs)⟩

/-! ### Existence of edge-fair runs -/

section Exists

variable (R) in
/-- The *edge system*: states are the transitions of `R` among configurations reachable from
`x₀`, and a transition `(x, y)` is followed by any transition `(y, z)`. -/
private def EdgeRel (x₀ : X) (e e' : {p : X × X // Reach R x₀ p.1 ∧ R p.1 p.2}) : Prop :=
  e.1.2 = e'.1.1

/-- **Edge-fair runs exist** from `x₀` if finitely many configurations are reachable from `x₀`
and each of them has a successor. -/
theorem exists_edgeFair {x₀ : X} (hfin : {y | Reach R x₀ y}.Finite)
    (htot : ∀ x, Reach R x₀ x → ∃ y, R x y) : ∃ E : Run R, E.st 0 = x₀ ∧ E.EdgeFair := by
  classical
  let Y := {p : X × X // Reach R x₀ p.1 ∧ R p.1 p.2}
  have hfinY : Finite Y := by
    have : ({p : X × X | Reach R x₀ p.1 ∧ R p.1 p.2} : Set (X × X)).Finite :=
      (hfin.prod hfin).subset fun p hp => ⟨hp.1, hp.1.tail hp.2⟩
    exact this.to_subtype
  have htotY : ∀ e : Y, ∃ e', EdgeRel R x₀ e e' := by
    intro e
    obtain ⟨z, hz⟩ := htot e.1.2 (e.2.1.tail e.2.2)
    exact ⟨⟨(e.1.2, z), e.2.1.tail e.2.2, hz⟩, rfl⟩
  obtain ⟨y₀, hy₀⟩ := htot x₀ .refl
  let e₀ : Y := ⟨(x₀, y₀), .refl, hy₀⟩
  obtain ⟨F, hF0, hF⟩ := exists_globallyFair htotY e₀
  let E : Run R :=
    { st := fun t => (F.st t).1.1
      step := fun t => by
        have h1 := (F.st t).2.2
        have h2 : (F.st t).1.2 = (F.st (t + 1)).1.1 := F.step t
        exact h2 ▸ h1 }
  refine ⟨E, by simp [E, hF0, e₀], ?_⟩
  intro x y hxy hx
  -- `x` occurs at infinitely many times `t + 1`, entered through some edge `(w, x)`
  have hx' : ∃ᶠ t in atTop, (F.st t).1.2 = x := by
    rw [frequently_atTop] at hx ⊢
    intro T
    obtain ⟨t, ht, hxt⟩ := hx (T + 1)
    obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
    refine ⟨s, by omega, ?_⟩
    have h2 : (F.st s).1.2 = (F.st (s + 1)).1.1 := F.step s
    rw [h2]; exact hxt
  obtain ⟨e, -, he⟩ := exists_frequently_and_eq (f := F.st) (S := (Set.univ : Set Y)) Set.finite_univ
    (fun _ _ => Set.mem_univ _) hx'
  obtain ⟨t₁, ht₁x, ht₁e⟩ := he.exists
  have hxreach : Reach R x₀ x := ht₁x ▸ (F.st t₁).2.1.tail (F.st t₁).2.2
  have hex : e.1.2 = x := ht₁e ▸ ht₁x
  let exy : Y := ⟨(x, y), hxreach, hxy⟩
  have hfreq : ∃ᶠ t in atTop, F.st t = exy :=
    hF e exy hex (he.mono fun _ h => h.2)
  refine hfreq.mono fun t ht => ⟨by simp [E, ht, exy], ?_⟩
  show (F.st (t + 1)).1.1 = y
  have h2 : (F.st t).1.2 = (F.st (t + 1)).1.1 := F.step t
  rw [← h2, ht]

end Exists

/-! ### Silence and termination -/

/-- An edge-fair (even globally fair) run that is eventually constant ends in a silent
configuration. -/
theorem Run.GloballyFair.isSilent_of_silent {E : Run R} (hE : E.GloballyFair) {n : ℕ}
    (hn : ∀ t ≥ n, E.st t = E.st n) : IsSilent R (E.st n) := by
  intro y hy
  have hfreq : ∃ᶠ t in atTop, E.st t = E.st n :=
    frequently_atTop.2 fun T => ⟨max T n, le_max_left _ _, hn _ (le_max_right _ _)⟩
  obtain ⟨t, ht, hty⟩ := frequently_atTop.1 (hE _ _ hy hfreq) n
  rw [← hty, hn t ht]

/-- A globally fair run in a system where a silent configuration is reachable from every
configuration reachable from the start (finitely many) is silent. -/
theorem Run.GloballyFair.silent {E : Run R} (hE : E.GloballyFair)
    (hfin : {y | Reach R (E.st 0) y}.Finite)
    (h : ∀ x, Reach R (E.st 0) x → ∃ y, Reach R x y ∧ IsSilent R y) : E.Silent := by
  have hS : IsTrap R {y | IsSilent R y} := fun y z hy hyz => by
    rw [Set.mem_ofPred_eq, hy z hyz]; exact hy
  obtain ⟨n, hn⟩ := eventually_atTop.1 (hE.eventually_mem_of_finite hfin hS
    fun x hx => (h x hx).elim fun y hy => ⟨y, hy.2, hy.1⟩)
  refine ⟨n, fun t ht => ?_⟩
  induction t, ht using Nat.le_induction with
  | base => rfl
  | succ t ht ih => rw [hn t ht (E.st (t + 1)) (E.step t), ih]

/-- **Silence = termination.** If finitely many configurations are reachable from each
configuration and every target of a transition has a successor, then every edge-fair run is
silent iff from every configuration some silent configuration is reachable. -/
theorem forall_edgeFair_silent_iff (hfin : ∀ x, {y | Reach R x y}.Finite)
    (htot : ∀ x y, R x y → ∃ z, R y z) :
    (∀ E : Run R, E.EdgeFair → E.Silent) ↔ ∀ x, ∃ y, Reach R x y ∧ IsSilent R y := by
  constructor
  · intro h x
    by_cases hx : ∃ y, R x y
    · have htot' : ∀ z, Reach R x z → ∃ w, R z w := by
        intro z hz
        rcases Relation.ReflTransGen.cases_tail hz with h | ⟨w, -, hwz⟩
        · exact h ▸ hx
        · exact htot w z hwz
      obtain ⟨E, hE0, hE⟩ := exists_edgeFair (hfin x) htot'
      obtain ⟨n, hn⟩ := h E hE
      exact ⟨E.st n, hE0 ▸ E.reach n, hE.globallyFair.isSilent_of_silent hn⟩
    · push Not at hx
      exact ⟨x, .refl, fun y hy => absurd hy (hx y)⟩
  · intro h E hE
    exact hE.globallyFair.silent (hfin _) fun x _ => h x

/-- Prepend a configuration to a run. -/
def Run.cons (x : X) (E : Run R) (h : R x (E.st 0)) : Run R where
  st t := Nat.casesOn t x fun t => E.st t
  step t := by cases t with
    | zero => exact h
    | succ t => exact E.step t

/-- A run that eventually stays in a silent configuration is edge fair. -/
theorem Run.edgeFair_of_eventually_eq {E : Run R} {y : X} (hy : IsSilent R y)
    (hE : ∀ᶠ t in atTop, E.st t = y) : E.EdgeFair := by
  intro a b hab ha
  obtain ⟨t, hty, hta⟩ := (hE.and_frequently ha).exists
  have hay : a = y := hta ▸ hty
  have hb : b = y := hy b (hay ▸ hab)
  rw [hay, hb]
  exact (Filter.Eventually.and hE ((tendsto_add_atTop_nat 1).eventually hE)).frequently

/-- A path to a silent configuration `y` with a self-loop extends to an edge-fair run that stays
in `y` forever. -/
theorem exists_run_of_reach_isSilent {x y : X} (h : Reach R x y) (hy : IsSilent R y)
    (hyy : R y y) : ∃ E : Run R, E.st 0 = x ∧ E.EdgeFair ∧ ∀ᶠ t in atTop, E.st t = y := by
  suffices ∃ E : Run R, E.st 0 = x ∧ ∀ᶠ t in atTop, E.st t = y from
    this.elim fun E hE => ⟨E, hE.1, Run.edgeFair_of_eventually_eq hy hE.2, hE.2⟩
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨⟨fun _ => y, fun _ => hyy⟩, rfl, Eventually.of_forall fun _ => rfl⟩
  | head hxz _ ih =>
    obtain ⟨E, hE0, hE⟩ := ih
    refine ⟨Run.cons _ E (hE0 ▸ hxz), rfl, ?_⟩
    obtain ⟨n, hn⟩ := eventually_atTop.1 hE
    exact eventually_atTop.2 ⟨n + 1, fun t ht => by
      obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
      exact hn s (by omega)⟩

/-! ### Constructing runs -/

/-- If every configuration satisfying `P` has a successor satisfying `P`, there is a run from any
configuration satisfying `P` that stays in `P`. -/
theorem exists_run_of_forall_exists {P : X → Prop} (h : ∀ y, P y → ∃ z, P z ∧ R y z) {x : X}
    (hx : P x) : ∃ E : Run R, E.st 0 = x ∧ ∀ t, P (E.st t) := by
  choose f hfP hfR using h
  let g : ℕ → {y // P y} := fun n => Nat.rec ⟨x, hx⟩ (fun _ y => ⟨f y.1 y.2, hfP y.1 y.2⟩) n
  exact ⟨⟨fun n => (g n).1, fun n => hfR (g n).1 (g n).2⟩, rfl, fun n => (g n).2⟩

/-- A run in which every step changes the configuration is not silent. -/
theorem Run.not_silent_of_ne {E : Run R} (h : ∀ t, E.st (t + 1) ≠ E.st t) : ¬ E.Silent :=
  fun ⟨n, hn⟩ => h n (hn (n + 1) (by omega))

/-- If every run is silent, a silent configuration is reachable from every configuration. -/
theorem exists_reach_isSilent_of_forall_silent (h : ∀ E : Run R, E.Silent) (x : X) :
    ∃ y, Reach R x y ∧ IsSilent R y := by
  by_contra hcon
  push Not at hcon
  have hstep : ∀ y, Reach R x y → ∃ z, Reach R x z ∧ (fun a b => R a b ∧ b ≠ a) y z := by
    intro y hy
    have := hcon y hy
    simp only [IsSilent, not_forall] at this
    obtain ⟨z, hz, hne⟩ := this
    exact ⟨z, hy.tail hz, hz, hne⟩
  obtain ⟨E, -, -⟩ := exists_run_of_forall_exists hstep (x := x) .refl
  exact Run.not_silent_of_ne (E := ⟨E.st, fun t => (E.step t).1⟩) (fun t => (E.step t).2)
    (h _)

/-- A cycle `x →⁺ x` of configuration-changing steps yields a non-silent run from `x`. -/
theorem exists_not_silent_of_cycle {x : X} (h : Relation.TransGen (fun a b => R a b ∧ b ≠ a) x x) :
    ∃ E : Run R, E.st 0 = x ∧ ¬ E.Silent := by
  have hstep : ∀ y, Relation.TransGen (fun a b => R a b ∧ b ≠ a) y x →
      ∃ z, Relation.TransGen (fun a b => R a b ∧ b ≠ a) z x ∧ (fun a b => R a b ∧ b ≠ a) y z := by
    intro y hy
    rcases Relation.TransGen.head'_iff.1 hy with ⟨z, hyz, hzx⟩
    rcases Relation.ReflTransGen.cases_head hzx with rfl | ⟨w, hzw, hwx⟩
    · exact ⟨z, h, hyz⟩
    · exact ⟨z, Relation.TransGen.head' hzw hwx, hyz⟩
  obtain ⟨E, hE0, -⟩ := exists_run_of_forall_exists hstep h
  exact ⟨⟨E.st, fun t => (E.step t).1⟩, hE0,
    Run.not_silent_of_ne (E := ⟨E.st, fun t => (E.step t).1⟩) fun t => (E.step t).2⟩

/-- A run along which every configuration change decreases a well-founded relation is silent
(ranking-function argument). -/
theorem Run.silent_of_wellFounded {r : X → X → Prop} (hr : WellFounded r) (E : Run R)
    (h : ∀ t, E.st (t + 1) ≠ E.st t → r (E.st (t + 1)) (E.st t)) : E.Silent := by
  suffices ∀ x s, E.st s = x → E.Silent from this _ 0 rfl
  intro x
  induction x using hr.induction with
  | _ x ih =>
    intro s hs
    by_cases hc : ∀ t ≥ s, E.st t = x
    · exact ⟨s, fun t ht => (hc t ht).trans hs.symm⟩
    · push Not at hc
      classical
      have hex : ∃ t, E.st (s + t) ≠ x := by
        obtain ⟨t, ht, hne⟩ := hc
        exact ⟨t - s, by rwa [show s + (t - s) = t by omega]⟩
      let k := Nat.find hex
      have hk : E.st (s + k) ≠ x := Nat.find_spec hex
      have hk0 : k ≠ 0 := fun h0 => hk (by rw [show k = 0 from h0, add_zero]; exact hs)
      obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hk0
      have hprev : E.st (s + j) = x := by
        by_contra hne; exact Nat.find_min hex (show j < k by omega) hne
      have hsucc : E.st (s + j + 1) = E.st (s + k) := by rw [hj]; rfl
      refine ih (E.st (s + k)) ?_ (s + k) rfl
      rw [← hsucc, ← hprev]
      exact h _ (by rw [hsucc, hprev]; exact hk)

end Cslib.TransitionSystem
