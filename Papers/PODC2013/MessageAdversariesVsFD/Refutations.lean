import Papers.PODC2013.MessageAdversariesVsFD.Counterexample
import Papers.PODC2013.MessageAdversariesVsFD.SigmaSeen
import Papers.PODC2013.MessageAdversariesVsFD.AsyncLocal
import Papers.PODC2013.MessageAdversariesVsFD.Theorem1
import Papers.PODC2013.MessageAdversariesVsFD.ArwOmegaCons
import Papers.PODC2013.MessageAdversariesVsFD.TourVariants

/-!
# The paper's theorems, as stated: what holds and what fails

Solvability in `SMP_n[adv : AD]` is the paper's (Section 2.4): every process computes an output
(`Solvable`); asynchronous solvability is `SolvableAMP` (`Async.lean`).

* `theorem1`: **Theorem 1 holds**: `SMP_n[adv : ∞] ≃_T AMP_{n,n-1}[fd : ∅]` (both are the local
  tasks).
* `lemma6_false`, `theorem4_false`: `Tseen` (`n = 3`) is solvable in `AMP_{3,2}[fd : Σ]` but not
  in `SMP_3[adv : QUORUM]`: **Lemma 6 and Theorem 4 are false.**
* `theorem2_false`, `corollary1_false`: `Tcons` (`n = 3`) is solvable in `ARW_{3,2}[fd : Ω]` but
  not in `SMP_3[adv : SOURCE, TOUR]`, nor (by Theorem 6) in `SMP_3[adv : SOURCE_tp, TP]` or
  `SMP_3[adv : SOURCE_pairs, PAIRS]`: **Lemma 2, Theorem 2 and Corollary 1 are false.**
* `theorem5_false`: `Tseen` is solvable in `AMP_{3,2}[fd : Σ, Ω]` but not in
  `SMP_3[adv : SOURCE, QUORUM]`: **Theorem 5 is false.**
* The arrows of Figure 1 `SMP_n[adv : QUORUM] → SMP_n[adv : TOUR]` and
  `SMP_n[adv : SOURCE, QUORUM] → SMP_n[adv : SOURCE, TOUR]` are false (`Counterexample.lean`).

To pass from `Σ` to the pair `(Σ, Ω)` we use that an algorithm for a failure detector `D` runs
unchanged with any failure detector from which `D` can be read off (`SolvableAMP.of_map`).
-/

namespace Podc.MessageAdversariesVsFD

open Cslib.FailureDetectors

variable {P R R' M X Y S : Type} [DecidableEq P]

/-- The pair of failure detectors `(Σ, Ω)`: a history of pairs whose first components form a
history of `Σ` and whose second components form a history of `Ω`. -/
def SigmaOmegaFD (P : Type) : FailureDetector P (Set P × P) := fun F =>
  {H | (fun p t => (H p t).1) ∈ SigmaFD P F ∧ (fun p t => (H p t).2) ∈ Omega P F}

namespace AlgAMP

/-- Run `A` with a failure detector whose value `d` is read as `f d`. -/
def comap (A : AlgAMP P R M X Y S) (f : R' → R) : AlgAMP P R' M X Y S :=
  ⟨A.init, fun p d s e => A.step p (f d) s e⟩

/-- The run seen through `f`. -/
def mapRun (f : R' → R) (r : Run P R' Empty) : Run P R Empty := ⟨r.F, fun p t => f (r.H p t), r.σ⟩

theorem cfg_comap (A : AlgAMP P R M X Y S) (f : R' → R) (x : P → X) (r : Run P R' Empty) (t : ℕ) :
    ((A.comap f).toAlg x).cfg r t = (A.toAlg x).cfg (mapRun f r) t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    simp only [Algorithm.cfg_succ, ih]
    rfl

theorem outAt_comap (A : AlgAMP P R M X Y S) (f : R' → R) (x : P → X) (r : Run P R' Empty)
    (t : ℕ) : ((A.comap f).toAlg x).outAt r t = (A.toAlg x).outAt (mapRun f r) t := by
  unfold Algorithm.outAt
  rw [cfg_comap]
  rfl

theorem out_comap (A : AlgAMP P R M X Y S) (f : R' → R) (x : P → X) (r : Run P R' Empty)
    (p : P) (y : Y) (t : ℕ) :
    ((A.comap f).toAlg x).Out r p y t ↔ (A.toAlg x).Out (mapRun f r) p y t := by
  unfold Algorithm.Out
  rw [outAt_comap]
  rfl

theorem output_comap (A : AlgAMP P R M X Y S) (f : R' → R) (x : P → X) (r : Run P R' Empty) :
    (A.comap f).output x r = A.output x (mapRun f r) := by
  classical
  funext p
  have hiff : (∃ t, ∃ y, ((A.comap f).toAlg x).Out r p y t) ↔
      ∃ t, ∃ y, (A.toAlg x).Out (mapRun f r) p y t := by
    simp only [out_comap]
  unfold output
  by_cases h : ∃ t, ∃ y, ((A.comap f).toAlg x).Out r p y t
  · have h' := hiff.1 h
    have heq : Nat.find h = Nat.find h' := by
      apply le_antisymm
      · exact Nat.find_min' h (by simpa only [out_comap] using Nat.find_spec h')
      · exact Nat.find_min' h' (by simpa only [out_comap] using Nat.find_spec h)
    rw [dite_eq_left_of_eq_true (eq_true h), dite_eq_left_of_eq_true (eq_true h'), outAt_comap,
      heq]
  · have h' : ¬ ∃ t, ∃ y, (A.toAlg x).Out (mapRun f r) p y t := fun h' => h (hiff.2 h')
    simp only [h, h', dite_false]

theorem admissible_comap (A : AlgAMP P R M X Y S) (f : R' → R) (x : P → X) (r : Run P R' Empty)
    (h : ((A.comap f).toAlg x).Admissible r) : (A.toAlg x).Admissible (mapRun f r) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨h1, fun t p q s hσ => ?_, h3, h4, fun p hp t s q m hm => ?_⟩
  · obtain ⟨hs, m, hm⟩ := h2 t p q s hσ
    exact ⟨hs, m, by rw [← cfg_comap]; exact hm⟩
  · exact h5 p hp t s q m (by rw [cfg_comap]; exact hm)

end AlgAMP

/-- An algorithm for `D` runs unchanged with a failure detector `D'` from which `D` can be read
off through `f`. -/
theorem SolvableAMP.of_map {D : FailureDetector P R} {D' : FailureDetector P R'} (f : R' → R)
    (hf : ∀ F H, H ∈ D' F → (fun p t => f (H p t)) ∈ D F) {T : Task P X Y}
    (h : SolvableAMP D T) : SolvableAMP D' T := by
  obtain ⟨M, S, A, hA⟩ := h
  refine ⟨M, S, A.comap f, fun x hx r hc hH hadm => ?_⟩
  obtain ⟨hdec, hval⟩ := hA x hx (AlgAMP.mapRun f r) hc (hf _ _ hH)
    (A.admissible_comap f x r hadm)
  refine ⟨fun p hp => ?_, by rw [A.output_comap]; exact hval⟩
  obtain ⟨t, y, hy⟩ := hdec p hp
  exact ⟨t, y, (A.out_comap f x r p y t).2 hy⟩

/-- Non-vacuity of `SolvableAMP`: for every algorithm, input vector and failure-detector value
`d`, there is an admissible failure-free run in which the failure detector constantly outputs
`d`. -/
theorem AlgAMP.exists_admissible_const [Fintype P] [Nonempty P] (A : AlgAMP P R M X Y S)
    (x : P → X) (d : R) :
    ∃ r : Run P R Empty, (∀ p, r.F.Correct p) ∧ r.H = (fun _ _ => d) ∧
      (A.toAlg x).Admissible r := by
  let r₀ := AsyncLocal.schedRun ((A.comap fun _ : Unit => d).toAlg x) (some 0) Set.univ
  have h₀ : ((A.comap fun _ : Unit => d).toAlg x).Admissible r₀ :=
    AsyncLocal.schedRun_admissible _ (some 0) Set.univ (by simp)
  refine ⟨AlgAMP.mapRun (fun _ => d) r₀, fun p t h => ?_, rfl, A.admissible_comap _ x r₀ h₀⟩
  simp [AlgAMP.mapRun, r₀, AsyncLocal.schedRun, Podc.WeakestFDEventualConsistency.policyRun,
    AsyncLocal.patternOf] at h

/-- Non-vacuity of `tseen_solvable_amp_sigma`: the algorithm has admissible runs with a valid
history of `Σ`. -/
theorem tseen_amp_sigma_nonvacuous (x : Fin 3 → Bool) : ∃ r : Run (Fin 3) (Set (Fin 3)) Empty,
    r.H ∈ SigmaFD (Fin 3) r.F ∧ (SigmaSeen.alg.toAlg x).Admissible r := by
  obtain ⟨r, hc, hH, hA⟩ := SigmaSeen.alg.exists_admissible_const x {0}
  exact ⟨r, hH ▸ const_mem_SigmaFD r.F 0 (hc 0), hA⟩

/-- **Theorem 1 of [Raynal–Stainer] holds**: a task is solvable in `SMP_n[adv : ∞]` iff it is
solvable in `AMP_{n,n-1}[fd : ∅]` (both iff the task is local). -/
theorem theorem1 [Fintype P] [Nonempty P] (T : Task P X Y) :
    Solvable (advInf : Adversary P) T ↔ SolvableAMP (trivialFD P) T :=
  (solvable_inf_iff_local T).trans (amp_solvable_iff_local T).symm

/-- `Tseen` is solvable in `AMP_{3,2}[fd : Σ, Ω]`. -/
theorem tseen_solvable_amp_sigma_omega : SolvableAMP (SigmaOmegaFD (Fin 3)) Tseen :=
  SolvableAMP.of_map Prod.fst (fun _ _ hH => hH.1) tseen_solvable_amp_sigma

/-- `Tseen` is not solvable in `SMP_3[adv : QUORUM]`. -/
theorem tseen_not_solvable_quorum : ¬ Solvable (QUORUM : Adversary (Fin 3)) Tseen :=
  fun h => tseen_not_solvable (Solvable.mono Set.inter_subset_right h)

/-- **Lemma 6 of [Raynal–Stainer] is false** ("if a task can be solved in `AMP_{n,n-1}[fd : Σ]`,
it can be solved in `SMP_n[adv : QUORUM]`", here without the undefined property FAIR): `Tseen`
is a counterexample for `n = 3`. -/
theorem lemma6_false :
    SolvableAMP (SigmaFD (Fin 3)) Tseen ∧ ¬ Solvable (QUORUM : Adversary (Fin 3)) Tseen :=
  ⟨tseen_solvable_amp_sigma, tseen_not_solvable_quorum⟩

/-- **Theorem 4 of [Raynal–Stainer] is false**: `SMP_n[adv : QUORUM]` and `AMP_{n,n-1}[fd : Σ]`
do not solve the same tasks (`n = 3`). -/
theorem theorem4_false :
    ¬ ∀ T : Task (Fin 3) Bool Seen, Solvable QUORUM T ↔ SolvableAMP (SigmaFD (Fin 3)) T :=
  fun h => tseen_not_solvable_quorum ((h Tseen).2 tseen_solvable_amp_sigma)

/-- **Theorem 5 of [Raynal–Stainer] is false**: `SMP_n[adv : SOURCE, QUORUM]` and
`AMP_{n,n-1}[fd : Σ, Ω]` do not solve the same tasks (`n = 3`). -/
theorem theorem5_false :
    ¬ ∀ T : Task (Fin 3) Bool Seen,
      Solvable (SOURCE ∩ QUORUM) T ↔ SolvableAMP (SigmaOmegaFD (Fin 3)) T :=
  fun h => tseen_not_solvable ((h Tseen).2 tseen_solvable_amp_sigma_omega)

/-- **Theorem 2 of [Raynal–Stainer] is false**: `SMP_n[adv : SOURCE, TOUR]` and
`ARW_{n,n-1}[fd : Ω]` do not solve the same tasks (`n = 3`, task `Tcons`). -/
theorem theorem2_false :
    ¬ ∀ T : Task (Fin 3) Bool Bool, Solvable (SOURCE ∩ TOUR) T ↔ SolvableARWOmega T :=
  fun h => tcons_not_solvable (((h Tcons).2 tcons_solvable_arw_omega).mono Set.inter_subset_left)

/-- **Corollary 1 of [Raynal–Stainer] is false**: `Tcons` is solvable in `ARW_{3,2}[fd : Ω]` but
in none of `SMP_3[adv : SOURCE, TOUR]`, `SMP_3[adv : SOURCE_tp, TP]`,
`SMP_3[adv : SOURCE_pairs, PAIRS]` (for the paper's PAIRS schedule `σ`). -/
theorem corollary1_false {C : ℕ} [NeZero C] (σ : Fin C ≃ {e : Sym2 (Fin 3) // ¬ e.IsDiag}) :
    SolvableARWOmega Tcons ∧ ¬ Solvable (SOURCE ∩ TOUR : Adversary (Fin 3)) Tcons ∧
      ¬ Solvable (SOURCEtp ∩ TP : Adversary (Fin 3)) Tcons ∧
      ¬ Solvable (SOURCEpairs (paperPair σ) ∩ PAIRS (paperPair σ) : Adversary (Fin 3)) Tcons := by
  have h1 : ¬ Solvable (SOURCE ∩ TOUR : Adversary (Fin 3)) Tcons :=
    fun h => tcons_not_solvable (h.mono Set.inter_subset_left)
  have h6 := theorem6 (P := Fin 3) (by simp) σ Tcons
  exact ⟨tcons_solvable_arw_omega, h1, fun h => h1 (h6.1.2 h), fun h => h1 (h6.2.1.2 h)⟩

end Podc.MessageAdversariesVsFD
