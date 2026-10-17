import Mathlib
import Podc.Foundations.Data.Nat.Log
import Cslib.Computability.Distributed.Byzantine.Specs

/-!
# Byzantine Agreement with Predictions — the guess-and-double wrapper (Sections 5 and 9)

Algorithm 1 of [BDEG25] composes, in each phase `φ` (here 0-indexed, `φ < Φ` with
`Φ = ⌈log₂ t⌉ + 1`), five sub-protocols run by all honest processes:
`graded-consensus` (GC₁), `ba-early-stopping` (ES, time limit `T_φ`), GC₂,
`ba-with-classification` (CL, at most `2^φ` misclassifications, time limit `T_φ`), GC₃.

The sub-protocols are cited (graded consensus [14]/[37], early stopping [32]) or proved
elsewhere (Theorems 5 and 6, files `Unauth*.lean`, `Auth*.lean`). Here we verify the **logic of the
wrapper** (Lemmas 28–32) on *abstract phase traces*: the outputs of every sub-protocol instance are
arbitrary, subject only to the sub-protocols' specifications:

* graded consensus: Strong Unanimity and Coherence (`GCSpec`), always;
* ES and CL: Agreement and Strong Unanimity (`BASpec`) in the phases where their preconditions
  hold (`PreEs φ`, `PreCl φ`; e.g. `T_φ` is at least the early-stopping time for the actual number
  of faults, resp. `2^φ` bounds the number of misclassified processes and `n - t` is large enough).

As in the paper, a process *decides* in the first phase in which GC₃ returns grade `1` and
returns one phase later (or at the last phase).

**Modelling simplification.** In the abstract trace all honest processes take part in all phases;
in Algorithm 1 a process stops after returning. Every argument below only inspects phases up to
one phase after the first decision, in which no honest process has returned yet, so this does not
matter.

* `lemma28`: Strong Unanimity (validity).
* `lemma29`: after the first decision (phase `φ`), all honest processes hold `v` from phase `φ + 1`
  on and decide `v` by phase `φ + 1`.
* `lemma30_32`: if `PreEs φ ∨ PreCl φ`, all honest processes have decided by the end of phase `φ`
  (Lemmas 30 and 32).
* `lemma31`: Agreement (if the precondition of ES holds in the last phase).
* `rounds_le`: the number of rounds until the end of phase `ψ` is
  `1 + (ψ + 1) · 3G + 2 α (2^(ψ+1) - 1)`, i.e. `O(2^ψ)` (Lemma 33).
* `theorem11_rounds`: the round-complexity statement of Theorems 11/12: if `k = 2^ψ` makes the
  classification precondition true (or `α 2^ψ` exceeds the early-stopping time), all honest
  processes return within `1 + (ψ+2)·3G + 2α(2^(ψ+2) - 1)` rounds; with `2^ψ < 2 max(k_A, 1)` this
  is `O(k_A + 1) = O(B/n + 1)` by Lemma 1.
-/

namespace BAWithPredictions.Wrapper

open Finset

variable {P V : Type*}

/-- Specification of graded consensus (Section 5): Strong Unanimity and Coherence. This is the
shared binary graded consensus `Problem.GradedConsensus`; `gcSpec_iff` states it in the paper's
form, whose two clauses are `GCSpec.unanimity` and `GCSpec.coherence`. -/
abbrev GCSpec (H : Set P) (inp : P → V) (out : P → V × Bool) : Prop :=
  Cslib.Byzantine.Problem.GradedConsensus inp H out

/-- Agreement and Strong Unanimity of a (conditional) Byzantine agreement sub-protocol: the shared
`Problem.Consensus` (fields `agreement`, `unanimity`; `baSpec_iff`). -/
abbrev BASpec (H : Set P) (inp out : P → V) : Prop :=
  Cslib.Byzantine.Problem.Consensus inp H out

section Specs

variable {H : Set P}

/-- The specification of graded consensus in the paper's form (Strong Unanimity, Coherence). -/
theorem gcSpec_iff {inp : P → V} {out : P → V × Bool} : GCSpec H inp out ↔
    (∀ v, (∀ i ∈ H, inp i = v) → ∀ i ∈ H, out i = (v, true)) ∧
      ∀ i ∈ H, ∀ v, out i = (v, true) → ∀ j ∈ H, (out j).1 = v := by
  refine Cslib.Byzantine.Problem.gradedConsensus_iff.trans <| and_congr
    (forall₂_congr fun _ _ => forall₂_congr fun _ _ => by rw [Prod.ext_iff])
    ⟨fun h i hi v hv j hj => ?_, fun h i hi hg j hj => h i hi _ (Prod.ext rfl hg) j hj⟩
  rw [h i hi (by rw [hv]) j hj, hv]

/-- Strong Unanimity of graded consensus. -/
theorem GCSpec.unanimity {inp : P → V} {out : P → V × Bool} (h : GCSpec H inp out) :
    ∀ v, (∀ i ∈ H, inp i = v) → ∀ i ∈ H, out i = (v, true) :=
  (gcSpec_iff.1 h).1

/-- Coherence of graded consensus. -/
theorem GCSpec.coherence {inp : P → V} {out : P → V × Bool} (h : GCSpec H inp out) :
    ∀ i ∈ H, ∀ v, out i = (v, true) → ∀ j ∈ H, (out j).1 = v :=
  (gcSpec_iff.1 h).2

/-- The specification of the BA sub-protocols in explicit form (Agreement, Strong Unanimity). -/
theorem baSpec_iff {inp out : P → V} : BASpec H inp out ↔
    (∀ i ∈ H, ∀ j ∈ H, out i = out j) ∧ ∀ v, (∀ i ∈ H, inp i = v) → ∀ i ∈ H, out i = v :=
  ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.1, h.2⟩⟩

end Specs

/-- An abstract execution of Algorithm 1: inputs and the outputs of all sub-protocol instances
(`gc₁ φ i` = output of process `i` from GC₁ in phase `φ`, etc.). -/
structure Trace (P V : Type*) where
  x : P → V
  gc₁ : ℕ → P → V × Bool
  es : ℕ → P → V
  gc₂ : ℕ → P → V × Bool
  cl : ℕ → P → V
  gc₃ : ℕ → P → V × Bool

namespace Trace

variable (τ : Trace P V)

/-- `v_i` at the beginning of phase `φ`. -/
def start : ℕ → P → V
  | 0, i => τ.x i
  | φ + 1, i => (τ.gc₃ φ i).1

/-- `v_i` after Line 8 (input of GC₂). -/
def w (φ : ℕ) (i : P) : V := if (τ.gc₁ φ i).2 then (τ.gc₁ φ i).1 else τ.es φ i

/-- `v_i` after Line 11 (input of GC₃). -/
def y (φ : ℕ) (i : P) : V := if (τ.gc₂ φ i).2 then (τ.gc₂ φ i).1 else τ.cl φ i

/-- `i` has decided `v` by the end of phase `φ`: GC₃ returned `(v, 1)` in some phase `≤ φ` and
grade `0` before. -/
def DecidedBy (φ : ℕ) (i : P) (v : V) : Prop :=
  ∃ φ' ≤ φ, τ.gc₃ φ' i = (v, true) ∧ ∀ φ'' < φ', (τ.gc₃ φ'' i).2 = false

/-- The trace respects the specifications of the sub-protocols; `PreEs φ`/`PreCl φ` are the
phases in which the preconditions of the early-stopping, resp. classification-based, agreement
hold. -/
structure Valid (H : Set P) (PreEs PreCl : ℕ → Prop) : Prop where
  gc₁ : ∀ φ, GCSpec H (τ.start φ) (τ.gc₁ φ)
  es : ∀ φ, PreEs φ → BASpec H (fun i => (τ.gc₁ φ i).1) (τ.es φ)
  gc₂ : ∀ φ, GCSpec H (τ.w φ) (τ.gc₂ φ)
  cl : ∀ φ, PreCl φ → BASpec H (fun i => (τ.gc₂ φ i).1) (τ.cl φ)
  gc₃ : ∀ φ, GCSpec H (τ.y φ) (τ.gc₃ φ)

variable {τ} {H : Set P} {PreEs PreCl : ℕ → Prop}

theorem decidedBy_mono {φ φ' : ℕ} (h : φ ≤ φ') {i : P} {v : V} (hd : τ.DecidedBy φ i v) :
    τ.DecidedBy φ' i v := by
  obtain ⟨ψ, hψ, h1, h2⟩ := hd
  exact ⟨ψ, hψ.trans h, h1, h2⟩

theorem decidedBy_unique {φ φ' : ℕ} {i : P} {v v' : V} (h : τ.DecidedBy φ i v)
    (h' : τ.DecidedBy φ' i v') : v = v' := by
  obtain ⟨ψ, -, h1, h2⟩ := h
  obtain ⟨ψ', -, h1', h2'⟩ := h'
  rcases lt_trichotomy ψ ψ' with hl | rfl | hl
  · have := h2' ψ hl; rw [h1] at this; exact absurd this (by simp)
  · rw [h1] at h1'; exact (Prod.mk.inj h1').1
  · have := h2 ψ' hl; rw [h1'] at this; exact absurd this (by simp)

/-- If all honest processes start phase `φ` with `v`, they all keep `v` and get grade `1` from
all three graded consensus instances of phase `φ`. -/
theorem phase_unanimous (hτ : τ.Valid H PreEs PreCl) {φ : ℕ} {v : V}
    (h : ∀ i ∈ H, τ.start φ i = v) : ∀ i ∈ H, τ.gc₃ φ i = (v, true) := by
  have h1 := (hτ.gc₁ φ).unanimity v h
  have h2 := (hτ.gc₂ φ).unanimity v fun i hi => by simp [w, h1 i hi]
  exact (hτ.gc₃ φ).unanimity v fun i hi => by simp [y, h2 i hi]

/-- If all honest processes start phase `φ` with `v`, then every honest process has decided `v`
by the end of phase `φ` (a process that decided earlier decided `v` as well). -/
theorem decided_of_start (hτ : τ.Valid H PreEs PreCl) {φ : ℕ} {v : V}
    (h : ∀ i ∈ H, τ.start φ i = v)
    (hprev : ∀ i ∈ H, ∀ u, τ.DecidedBy φ i u → u = v) : ∀ i ∈ H, τ.DecidedBy φ i v := by
  classical
  intro i hi
  have h3 := phase_unanimous hτ h i hi
  by_cases hex : ∃ φ' ≤ φ, (τ.gc₃ φ' i).2 = true
  · obtain ⟨hφ₀, h0⟩ := Nat.find_spec hex
    have hmin : ∀ ψ < Nat.find hex, ¬ (ψ ≤ φ ∧ (τ.gc₃ ψ i).2 = true) :=
      fun ψ hψ => Nat.find_min hex hψ
    obtain ⟨u, hu⟩ : ∃ u, τ.gc₃ (Nat.find hex) i = (u, true) := ⟨_, Prod.ext rfl h0⟩
    have hd : τ.DecidedBy φ i u := ⟨Nat.find hex, hφ₀, hu, fun ψ hψ => by
      have := hmin ψ hψ
      exact Bool.eq_false_iff.mpr (fun h => this ⟨hψ.le.trans hφ₀, h⟩)⟩
    rwa [hprev i hi u hd] at hd
  · push Not at hex
    exact ⟨φ, le_rfl, h3, fun ψ hψ => Bool.eq_false_iff.mpr (hex ψ hψ.le)⟩

/-- **Lemma 28 (Strong Unanimity).** If all honest inputs are `v`, every honest process decides
`v` in the first phase. -/
theorem lemma28 (hτ : τ.Valid H PreEs PreCl) {v : V} (h : ∀ i ∈ H, τ.x i = v) :
    ∀ i ∈ H, τ.DecidedBy 0 i v := by
  refine decided_of_start hτ h fun i _ u hu => ?_
  obtain ⟨ψ, hψ, h1, -⟩ := hu
  obtain rfl : ψ = 0 := by omega
  have := phase_unanimous hτ (φ := 0) h i ‹_›
  rw [h1] at this; exact (Prod.mk.inj this).1

/-- No honest process has decided before phase `φ` (i.e. by the end of phase `φ - 1`). -/
def NoneBefore (τ : Trace P V) (H : Set P) (φ : ℕ) : Prop :=
  ∀ i ∈ H, ∀ ψ < φ, (τ.gc₃ ψ i).2 = false

/-- **Lemma 29.** If some honest process decides `v` in phase `φ` and nobody decided earlier,
then all honest processes start phase `φ + 1` with `v` and all have decided `v` by the end of phase
`φ + 1`. -/
theorem lemma29 (hτ : τ.Valid H PreEs PreCl) {φ : ℕ} {i : P} (hi : i ∈ H) {v : V}
    (hd : τ.gc₃ φ i = (v, true)) (hnone : NoneBefore τ H φ) :
    (∀ j ∈ H, τ.start (φ + 1) j = v) ∧ ∀ j ∈ H, τ.DecidedBy (φ + 1) j v := by
  have hst : ∀ j ∈ H, τ.start (φ + 1) j = v := fun j hj => (hτ.gc₃ φ).coherence i hi v hd j hj
  refine ⟨hst, decided_of_start hτ hst fun j hj u hu => ?_⟩
  obtain ⟨ψ, hψ, h1, -⟩ := hu
  rcases Nat.lt_or_ge ψ φ with hlt | hge
  · have := hnone j hj ψ hlt; rw [h1] at this; exact absurd this (by simp)
  · rcases (by omega : ψ = φ ∨ ψ = φ + 1) with rfl | rfl
    · have := (hτ.gc₃ ψ).coherence i hi v hd j hj; rw [h1] at this; exact this
    · have := phase_unanimous hτ hst j hj; rw [h1] at this; exact (Prod.mk.inj this).1

/-- If no honest process decided before phase `φ` and all honest processes enter GC₃ of phase
`φ` with the same value, they all decide it in phase `φ`. -/
theorem decide_of_y (hτ : τ.Valid H PreEs PreCl) {φ : ℕ} (hnone : NoneBefore τ H φ) {v : V}
    (hy : ∀ i ∈ H, τ.y φ i = v) : ∀ i ∈ H, τ.DecidedBy φ i v := by
  intro i hi
  have := (hτ.gc₃ φ).unanimity v hy i hi
  exact ⟨φ, le_rfl, this, fun ψ hψ => hnone i hi ψ hψ⟩

/-- If no honest process decided before phase `φ` and all honest processes enter GC₂ of phase
`φ` with the same value, they all decide it in phase `φ`. -/
theorem decide_of_w (hτ : τ.Valid H PreEs PreCl) {φ : ℕ} (hnone : NoneBefore τ H φ) {v : V}
    (hw : ∀ i ∈ H, τ.w φ i = v) : ∀ i ∈ H, τ.DecidedBy φ i v := by
  have h2 := (hτ.gc₂ φ).unanimity v hw
  exact decide_of_y hτ hnone fun i hi => by simp [y, h2 i hi]

/-- Common value after a sub-protocol with Agreement and Strong Unanimity, protected by a
graded consensus (the argument of Lemmas 30 and 32). -/
theorem common_after {gc : P → V × Bool} {sub : P → V} (hgc : ∀ i ∈ H, ∀ v, gc i = (v, true) →
    ∀ j ∈ H, (gc j).1 = v) (hsub : BASpec H (fun i => (gc i).1) sub) {i₀ : P} (hi₀ : i₀ ∈ H) :
    ∃ v, ∀ i ∈ H, (if (gc i).2 then (gc i).1 else sub i) = v := by
  by_cases h : ∃ j ∈ H, (gc j).2 = true
  · obtain ⟨j, hj, hg⟩ := h
    have hc : ∀ i ∈ H, (gc i).1 = (gc j).1 := hgc j hj _ (Prod.ext rfl hg)
    refine ⟨(gc j).1, fun i hi => ?_⟩
    split_ifs
    · exact hc i hi
    · exact hsub.unanimity _ hc i hi
  · push Not at h
    refine ⟨sub i₀, fun i hi => ?_⟩
    have hg : (gc i).2 = false := by simpa using h i hi
    simp only [hg, Bool.false_eq_true, ↓reduceIte]
    exact hsub.agreement i hi i₀ hi₀

/-- **Lemmas 30 and 32.** If the precondition of ES or of CL holds in phase `φ`, then all honest
processes have decided by the end of phase `φ`, and on the same value (given at least one honest
process). -/
theorem lemma30_32 (hτ : τ.Valid H PreEs PreCl) {i₀ : P} (hi₀ : i₀ ∈ H) {φ : ℕ}
    (hpre : PreEs φ ∨ PreCl φ) : ∃ v, ∀ i ∈ H, τ.DecidedBy φ i v := by
  classical
  by_cases hnone : NoneBefore τ H φ
  · rcases hpre with hes | hcl
    · obtain ⟨v, hv⟩ := common_after (hτ.gc₁ φ).coherence (hτ.es φ hes) hi₀
      exact ⟨v, decide_of_w hτ hnone fun i hi => hv i hi⟩
    · obtain ⟨v, hv⟩ := common_after (hτ.gc₂ φ).coherence (hτ.cl φ hcl) hi₀
      exact ⟨v, decide_of_y hτ hnone fun i hi => hv i hi⟩
  · -- some honest process decided earlier: take the first such phase
    have hex : ∃ ψ, ∃ i ∈ H, (τ.gc₃ ψ i).2 = true ∧ ψ < φ := by
      unfold NoneBefore at hnone; push Not at hnone
      obtain ⟨i, hi, ψ, hψ, h⟩ := hnone
      exact ⟨ψ, i, hi, by simpa using h, hψ⟩
    obtain ⟨i, hi, hg, hlt⟩ := Nat.find_spec hex
    have hmin : NoneBefore τ H (Nat.find hex) := by
      intro j hj ψ hψ
      by_contra hc
      exact Nat.find_min hex hψ ⟨j, hj, by simpa using hc, by omega⟩
    obtain ⟨v, hv⟩ : ∃ v, τ.gc₃ (Nat.find hex) i = (v, true) := ⟨_, Prod.ext rfl hg⟩
    obtain ⟨-, h2⟩ := lemma29 hτ hi hv hmin
    exact ⟨v, fun j hj => decidedBy_mono (by omega) (h2 j hj)⟩

/-- **Lemma 31 (Agreement).** If the precondition of the early-stopping agreement holds in the
last phase `Φ - 1` (time limit `α t` suffices for at most `t` faults), all honest processes decide,
and on the same value. -/
theorem lemma31 (hτ : τ.Valid H PreEs PreCl) {i₀ : P} (hi₀ : i₀ ∈ H) {Φ : ℕ}
    (hlast : PreEs (Φ - 1)) : ∃ v, ∀ i ∈ H, τ.DecidedBy (Φ - 1) i v :=
  lemma30_32 hτ hi₀ (Or.inl hlast)

/-- Two honest processes never decide differently (whenever both decide). -/
theorem agreement (hτ : τ.Valid H PreEs PreCl) {i j : P} (hi : i ∈ H) (hj : j ∈ H) {φ φ' : ℕ}
    {v v' : V} (hd : τ.DecidedBy φ i v) (hd' : τ.DecidedBy φ' j v') : v = v' := by
  classical
  have hex : ∃ ψ, ∃ k ∈ H, (τ.gc₃ ψ k).2 = true := by
    obtain ⟨ψ, -, h1, -⟩ := hd; exact ⟨ψ, i, hi, by rw [h1]⟩
  obtain ⟨k, hk, hg⟩ := Nat.find_spec hex
  have hmin : NoneBefore τ H (Nat.find hex) := by
    intro l hl ψ hψ
    by_contra hc
    exact Nat.find_min hex hψ ⟨l, hl, by simpa using hc⟩
  obtain ⟨u, hu⟩ : ∃ u, τ.gc₃ (Nat.find hex) k = (u, true) := ⟨_, Prod.ext rfl hg⟩
  obtain ⟨-, h2⟩ := lemma29 hτ hk hu hmin
  have e1 := decidedBy_unique hd (h2 i hi)
  have e2 := decidedBy_unique hd' (h2 j hj)
  rw [e1, e2]

/-! ### Rounds (Lemma 33) -/

/-- Rounds of Algorithm 1 up to the end of phase `ψ` (0-indexed phases): one round of
classification, then in phase `φ` three graded consensus instances of `G` rounds and two
sub-protocols of `T_φ = α 2^φ` rounds. -/
def roundsUpTo (G α ψ : ℕ) : ℕ := 1 + ∑ φ ∈ range (ψ + 1), (3 * G + 2 * (α * 2 ^ φ))

theorem sum_pow_two (ψ : ℕ) : ∑ φ ∈ range (ψ + 1), 2 ^ φ + 1 = 2 ^ (ψ + 1) := by
  induction ψ with
  | zero => simp
  | succ ψ ih => rw [sum_range_succ, pow_succ]; omega

/-- **Lemma 33 (rounds).** `roundsUpTo G α ψ = 1 + 3G(ψ+1) + 2α(2^(ψ+1) - 1)`. -/
theorem rounds_le (G α ψ : ℕ) :
    roundsUpTo G α ψ + 2 * α = 1 + 3 * G * (ψ + 1) + 2 * α * 2 ^ (ψ + 1) := by
  unfold roundsUpTo
  rw [sum_add_distrib, sum_const, card_range, smul_eq_mul, ← mul_sum, ← mul_sum,
    ← sum_pow_two ψ]
  ring

/-- **Round complexity of Algorithm 1 (Theorems 11 and 12).** If the precondition of ES or of CL
holds in phase `ψ` (for CL with `k = 2^ψ`: `k_A ≤ 2^ψ` and the size condition; for ES:
`α 2^ψ` exceeds the early-stopping time for the actual number of faults), then every honest
process has decided by the end of phase `ψ` and returns by the end of phase `ψ + 1`, i.e. within
`roundsUpTo G α (ψ + 1) ≤ 1 + 3G(ψ+2) + 2α 2^(ψ+2)` rounds. Choosing the least such `ψ`,
`2^ψ ≤ 2 max (k_A, 1)` (resp. `O(f + 1)`), which gives `O(min(B/n, f) + 1)` rounds via Lemma 1. -/
theorem theorem11_rounds (hτ : τ.Valid H PreEs PreCl) {i₀ : P} (hi₀ : i₀ ∈ H) {ψ : ℕ}
    (hpre : PreEs ψ ∨ PreCl ψ) (G α : ℕ) :
    (∃ v, ∀ i ∈ H, τ.DecidedBy ψ i v) ∧
      roundsUpTo G α (ψ + 1) + 2 * α = 1 + 3 * G * (ψ + 2) + 2 * α * 2 ^ (ψ + 2) :=
  ⟨lemma30_32 hτ hi₀ hpre, rounds_le G α (ψ + 1)⟩

/-- The doubling step: for every `k ≥ 1` there is a phase `ψ` with `k ≤ 2^ψ < 2k`. -/
theorem exists_pow_two_between {k : ℕ} (hk : 1 ≤ k) : ∃ ψ, k ≤ 2 ^ ψ ∧ 2 ^ ψ < 2 * k :=
  ⟨Nat.clog 2 k, Nat.le_pow_clog one_lt_two k, Nat.pow_clog_lt_mul one_lt_two (by omega)⟩

end Trace

end BAWithPredictions.Wrapper
