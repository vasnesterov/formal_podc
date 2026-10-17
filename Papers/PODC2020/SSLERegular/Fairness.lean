import Mathlib.Logic.Relation
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Pi
import Cslib.Probability.Markov.Absorption

/-!
# Global fairness and random schedulers for finite transition systems

Generic facts about a transition relation `R : X → X → Prop` on a *finite* set of configurations
`X`, used to give the self-stabilization claims of Chen–Chen (PODC 2020) a precise meaning.

* `TS.Run R`: an infinite run; `Run.GloballyFair` is global fairness in the sense of Angluin et
  al. (if `x` occurs infinitely often and `R x y`, then `y` occurs infinitely often).
* `TS.exists_globallyFair`: every finite total transition system has a globally fair run from any
  initial configuration (round-robin over the successors of each configuration). This is the
  non-vacuity fact needed to *refute* fairness-based correctness claims.
* `TS.eventually_of_reach`, `TS.fair_iff_reach`: for a closed set `S`, "every globally fair run
  eventually enters `S`" is equivalent to "`S` is reachable from every configuration".
* `TS.tendsto_compl_of_reach`, `TS.prob_eq_zero_of_not_reach`: the same reachability condition is
  equivalent to "a random scheduler reaches `S` with probability `1`" for every Markov kernel whose
  positive-probability moves are exactly the transitions (via `Cslib.Probability.Markov`).
-/

open Finset

namespace SSLERegular

namespace TS

set_option linter.unusedSectionVars false

variable {X : Type*} (R : X → X → Prop)

/-- Reachability (reflexive–transitive closure). -/
abbrev Reach : X → X → Prop := Relation.ReflTransGen R

/-- An infinite run of the transition system. -/
structure Run where
  /-- The configuration at time `t`. -/
  st : ℕ → X
  /-- Consecutive configurations are related by a transition. -/
  step : ∀ t, R (st t) (st (t + 1))

/-- `x` occurs infinitely often in `f`. -/
def IO (f : ℕ → X) (x : X) : Prop := ∀ T, ∃ t ≥ T, f t = x

variable {R}

-- CSLib candidate
/-- Global fairness: every transition enabled from a configuration occurring infinitely often is
taken (its target occurs infinitely often). -/
def Run.GloballyFair (E : Run R) : Prop := ∀ x y, R x y → IO E.st x → IO E.st y

/-- A set of configurations closed under transitions. -/
def Closed (R : X → X → Prop) (S : X → Prop) : Prop := ∀ x y, S x → R x y → S y

lemma Closed.reach {S : X → Prop} (hS : Closed R S) {x y : X} (hx : S x) (h : Reach R x y) :
    S y := by
  induction h with
  | refl => exact hx
  | tail _ hst ih => exact hS _ _ ih hst

lemma Run.reach_of_le (E : Run R) {s t : ℕ} (h : s ≤ t) : Reach R (E.st s) (E.st t) := by
  induction t, h using Nat.le_induction with
  | base => exact Relation.ReflTransGen.refl
  | succ t _ ih => exact ih.tail (E.step t)

lemma exists_io [Finite X] (f : ℕ → X) : ∃ x, IO f x := by
  by_contra h
  push Not at h
  have := Fintype.ofFinite X
  choose T hT using fun x => by simpa [IO] using h x
  exact hT (f (Finset.univ.sup T)) _ (Finset.le_sup (Finset.mem_univ _)) rfl

lemma Run.GloballyFair.io_of_reach {E : Run R} (hE : E.GloballyFair) {x y : X} (hx : IO E.st x)
    (h : Reach R x y) : IO E.st y := by
  induction h with
  | refl => exact hx
  | tail _ hst ih => exact hE _ _ hst ih

-- CSLib candidate
/-- Under global fairness (finitely many configurations): if from every configuration reachable
from the start some configuration of a closed set `S` is reachable, the run eventually enters `S`
and stays there. -/
theorem Run.GloballyFair.eventually [Finite X] {E : Run R} (hE : E.GloballyFair)
    {S : X → Prop} (hS : Closed R S) (h : ∀ x, Reach R (E.st 0) x → ∃ y, S y ∧ Reach R x y) :
    ∃ T, ∀ t ≥ T, S (E.st t) := by
  obtain ⟨x, hx⟩ := exists_io E.st
  obtain ⟨t0, -, ht0⟩ := hx 0
  obtain ⟨y, hyS, hxy⟩ := h x (ht0 ▸ E.reach_of_le (Nat.zero_le _))
  obtain ⟨t, -, ht⟩ := hE.io_of_reach hx hxy 0
  exact ⟨t, fun s hs => hS.reach (ht ▸ hyS) (E.reach_of_le hs)⟩

/-! ### Existence of globally fair runs -/

section Construction

variable [Fintype X] [DecidableEq X] [DecidableRel R]

/-- The successors of `x`, as a list. -/
noncomputable def succList (R : X → X → Prop) [DecidableRel R] (x : X) : List X :=
  (Finset.univ.filter (R x)).toList

lemma mem_succList {x y : X} : y ∈ succList R x ↔ R x y := by
  simp [succList]

/-- Round-robin choice: the `m`-th visit of `x` moves to the `(m mod #succ)`-th successor. -/
noncomputable def rr (htot : ∀ x, ∃ y, R x y) (x : X) (m : ℕ) : X :=
  (succList R x).get ⟨m % (succList R x).length, Nat.mod_lt _ (by
    obtain ⟨y, hy⟩ := htot x
    exact List.length_pos_of_mem (mem_succList.2 hy))⟩

/-- The run with visit counters. -/
noncomputable def rrAux (htot : ∀ x, ∃ y, R x y) (x0 : X) : ℕ → X × (X → ℕ)
  | 0 => (x0, fun _ => 0)
  | t + 1 =>
    let p := rrAux htot x0 t
    (rr htot p.1 (p.2 p.1), Function.update p.2 p.1 (p.2 p.1 + 1))

variable (htot : ∀ x, ∃ y, R x y) (x0 : X)

/-- Number of visits to `y` before time `t`. -/
noncomputable def cnt (t : ℕ) (y : X) : ℕ :=
  ((Finset.range t).filter fun s => (rrAux htot x0 s).1 = y).card

lemma rrAux_snd (t : ℕ) : (rrAux htot x0 t).2 = cnt htot x0 t := by
  induction t with
  | zero => funext y; simp [rrAux, cnt]
  | succ t ih =>
    funext y
    simp only [rrAux, cnt, Finset.range_add_one, Finset.filter_insert]
    rw [ih]
    by_cases hy : (rrAux htot x0 t).1 = y
    · subst hy
      rw [if_pos rfl, Finset.card_insert_of_notMem (by simp)]
      simp [cnt]
    · rw [if_neg hy, Function.update_of_ne (Ne.symm hy)]
      rfl

lemma cnt_succ (t : ℕ) (y : X) :
    cnt htot x0 (t + 1) y = cnt htot x0 t y + if (rrAux htot x0 t).1 = y then 1 else 0 := by
  simp only [cnt, Finset.range_add_one, Finset.filter_insert]
  split_ifs with h
  · rw [Finset.card_insert_of_notMem (by simp)]
  · simp

lemma cnt_mono {s t : ℕ} (h : s ≤ t) (y : X) : cnt htot x0 s y ≤ cnt htot x0 t y := by
  induction t, h using Nat.le_induction with
  | base => exact le_rfl
  | succ t _ ih => rw [cnt_succ]; omega

lemma rrAux_step (t : ℕ) : R (rrAux htot x0 t).1 (rrAux htot x0 (t + 1)).1 := by
  simp only [rrAux]
  exact mem_succList.1 (List.get_mem _ _)

/-- The round-robin run. -/
noncomputable def rrRun : Run R where
  st t := (rrAux htot x0 t).1
  step t := rrAux_step htot x0 t

-- CSLib candidate
/-- **Globally fair runs exist.** A finite transition system in which every configuration has a
successor has a globally fair run from every configuration. -/
theorem rrRun_globallyFair : (rrRun htot x0).GloballyFair := by
  intro x y hxy hx T
  -- the visit counter of `x` is unbounded
  have hunb : ∀ M, ∃ t, M ≤ cnt htot x0 t x := by
    intro M
    induction M with
    | zero => exact ⟨0, Nat.zero_le _⟩
    | succ M ih =>
      obtain ⟨t, ht⟩ := ih
      obtain ⟨s, hs, hsx⟩ := hx t
      refine ⟨s + 1, ?_⟩
      have hsx' : (rrAux htot x0 s).1 = x := hsx
      rw [cnt_succ, if_pos hsx']
      have := cnt_mono htot x0 hs x
      omega
  -- every value of the counter is attained at a visit
  have hvisit : ∀ m, ∃ t, (rrAux htot x0 t).1 = x ∧ cnt htot x0 t x = m := by
    intro m
    have hex : ∃ t, m < cnt htot x0 t x := by
      obtain ⟨t, ht⟩ := hunb (m + 1); exact ⟨t, by omega⟩
    classical
    let t := Nat.find hex
    have ht : m < cnt htot x0 t x := Nat.find_spec hex
    have ht0 : t ≠ 0 := by
      intro h0
      rw [show t = 0 from h0] at ht
      simp [cnt] at ht
    obtain ⟨t', ht'⟩ := Nat.exists_eq_succ_of_ne_zero ht0
    have hle : cnt htot x0 t' x ≤ m := by
      have := Nat.find_min hex (show t' < t by omega)
      omega
    rw [ht', cnt_succ] at ht
    refine ⟨t', ?_, ?_⟩
    · by_contra hne; rw [if_neg hne] at ht; omega
    · split_ifs at ht <;> omega
  -- position of `y` in the successor list
  obtain ⟨j, hj⟩ := List.get_of_mem (mem_succList.2 hxy)
  have hjl : (j : ℕ) < (succList R x).length := j.2
  obtain ⟨t, htx, htm⟩ := hvisit (cnt htot x0 T x * (succList R x).length + j)
  refine ⟨t + 1, ?_, ?_⟩
  · by_contra hlt
    push Not at hlt
    have h1 : cnt htot x0 (t + 1) x ≤ cnt htot x0 T x := cnt_mono htot x0 (by omega) x
    rw [cnt_succ, if_pos htx, htm] at h1
    nlinarith
  · show (rrAux htot x0 (t + 1)).1 = y
    simp only [rrAux]
    rw [rrAux_snd, htx, htm, ← hj]
    simp only [rr]
    congr 1
    ext
    simp only
    rw [Nat.add_mod, Nat.mul_mod_left, zero_add, Nat.mod_mod, Nat.mod_eq_of_lt hjl]

end Construction

/-- **Globally fair runs exist** (statement without decidability instances). -/
theorem exists_globallyFair [Finite X] (htot : ∀ x, ∃ y, R x y) (x0 : X) :
    ∃ E : Run R, E.st 0 = x0 ∧ E.GloballyFair := by
  classical
  have := Fintype.ofFinite X
  exact ⟨rrRun htot x0, rfl, rrRun_globallyFair htot x0⟩

-- CSLib candidate
/-- For a closed set `S` in a finite total transition system: every globally fair run (from any
configuration) eventually enters `S` iff `S` is reachable from every configuration. -/
theorem fair_iff_reach [Finite X] (htot : ∀ x, ∃ y, R x y) {S : X → Prop} (hS : Closed R S) :
    (∀ E : Run R, E.GloballyFair → ∃ T, S (E.st T)) ↔ ∀ x, ∃ y, S y ∧ Reach R x y := by
  constructor
  · intro h x
    obtain ⟨E, hE0, hE⟩ := exists_globallyFair htot x
    obtain ⟨T, hT⟩ := h E hE
    exact ⟨E.st T, hT, hE0 ▸ E.reach_of_le (Nat.zero_le T)⟩
  · intro h E hE
    obtain ⟨T, hT⟩ := hE.eventually hS (fun x _ => h x)
    exact ⟨T, hT T le_rfl⟩

/-! ### Random schedulers -/

section Markov

open Cslib.Probability.Markov Matrix Filter Topology

variable [Fintype X] [DecidableEq X]

/-- `S` as a finset. -/
noncomputable def setOf (S : X → Prop) : Finset X := by
  classical exact Finset.univ.filter S

lemma mem_setOf {S : X → Prop} {x : X} : x ∈ setOf S ↔ S x := by
  classical simp [setOf]

lemma reflTransGen_pos {T : Matrix X X ℝ} (hpos : ∀ x y, R x y → 0 < T x y) {x y : X}
    (h : Reach R x y) : Relation.ReflTransGen (fun a b => 0 < T a b) x y := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hst ih => exact ih.tail (hpos _ _ hst)

-- CSLib candidate
/-- **Reachability ⇒ probability 1.** For any Markov kernel whose positive-probability moves are
exactly the transitions, if a closed set `S` is reachable from everywhere then the probability of
being outside `S` after `t` steps tends to `0`. -/
theorem tendsto_compl_of_reach {S : X → Prop} (hS : Closed R S) {T : Matrix X X ℝ}
    (hT : T ∈ rowStochastic ℝ X) (hstep : ∀ x y, 0 < T x y → R x y)
    (hpos : ∀ x y, R x y → 0 < T x y) (h : ∀ x, ∃ y, S y ∧ Reach R x y) (x : X) :
    Tendsto (fun t => ∑ y ∈ (setOf S)ᶜ, (T ^ t) x y) atTop (𝓝 0) := by
  refine tendsto_sum_compl_of_absorbing hT ?_ ?_ x
  · intro a ha b hb
    by_contra hne
    have : 0 < T a b := lt_of_le_of_ne (nonneg_of_mem_rowStochastic hT) (Ne.symm hne)
    exact (by simpa using hb : b ∉ setOf S) (mem_setOf.2 (hS a b (mem_setOf.1 ha) (hstep _ _ this)))
  · intro a
    obtain ⟨y, hy, hr⟩ := h a
    exact ⟨y, mem_setOf.2 hy, reflTransGen_pos hpos hr⟩

-- CSLib candidate
/-- **Unreachability ⇒ probability 0.** If no configuration of `S` is reachable from `x`, the
probability of being in `S` is `0` at every time. -/
theorem prob_eq_zero_of_not_reach {S : X → Prop} {T : Matrix X X ℝ}
    (hT : T ∈ rowStochastic ℝ X) (hstep : ∀ x y, 0 < T x y → R x y) {x : X}
    (hx : ∀ y, Reach R x y → ¬ S y) (t : ℕ) : ∑ y ∈ setOf S, (T ^ t) x y = 0 := by
  refine Finset.sum_eq_zero fun y hy => ?_
  refine pow_eq_zero_of_closed hT (fun z => Reach R x z) ?_ Relation.ReflTransGen.refl t
    (fun h => hx y h (mem_setOf.1 hy))
  intro a b ha hab
  exact ha.tail (hstep _ _ hab)

end Markov

end TS

end SSLERegular
