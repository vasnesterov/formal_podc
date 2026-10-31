import Papers.PODC2019.FastReadsRegisterSim.Theorem41
import Cslib.Computability.Distributed.SharedMemory.Atomic

/-!
# Non-vacuity: the trivial simulation of a binary register

For `k = 2` (`m = 1`) a binary register is simulated by one binary register (CSLib's
`atomicImpl`): every operation applies itself to the base register in one step. It is
wait-free, atomic (hence regular and safe), and every read takes one step. So

* the hypotheses of Theorems 3.1/3.2 and Corollary 3.5 are satisfiable (`trivialSim_hyps`);
* the definitions `Sim.Atomic` and `Sim.ReadStepsLE` are not contradictory, and the hypothesis
  `k > 2` of Theorem 4.1 is necessary (`theorem_4_1_needs_k_gt_two`).
-/

set_option linter.unusedSectionVars false

namespace Podc.FastReadsRegisterSim

open Cslib.SharedMemory

variable {P : Type} [DecidableEq P]

variable (P) in
/-- The trivial simulation of a binary register (initial value `false`) by one binary register. -/
def trivialSim : Sim Bool false Unit P (AtomicLoc (register Bool false)) :=
  atomicImpl (register Bool false) false P

lemma trivialSim_atomic (w : P) : (trivialSim P).Atomic w := by
  intro α hα _
  obtain ⟨h, hh⟩ := Atomic.exists_linFun (A := register Bool false) (P := P) (r₀ := false)
  obtain ⟨C, hC⟩ := hα
  exact ⟨h α, (hh α C hC).lin⟩

lemma trivialSim_waitFree : (trivialSim P).WaitFree := Atomic.waitFree

/-- Remaining steps of an operation of the trivial simulation. -/
def phi : AtomicLoc (register Bool false) → ℕ
  | .apply _ => 1
  | _ => 0

lemma numSteps_accessOf_ne (D : Config (register Bool false) (BinRegs Unit) P
    (AtomicLoc (register Bool false))) {ℓ : Label P (register Bool false)} {r : P}
    (hℓ : ℓ.proc ≠ r) : numSteps r ((trivialSim P).accessOf D ℓ) = 0 := by
  cases ℓ with
  | tau q =>
    simp only [Label.proc] at hℓ
    simp only [Sim.accessOf]
    split <;> simp [numSteps, hℓ]
  | inv q o => simp [Sim.accessOf, numSteps]
  | ret q v => simp [Sim.accessOf, numSteps]

lemma numSteps_le_phi (r : P) :
    ∀ (α : List (Label P (register Bool false)))
      (D : Config (register Bool false) (BinRegs Unit) P (AtomicLoc (register Bool false))),
      D.pend r ≠ none → (∀ v, Label.ret r v ∉ α) → ((trivialSim P).runFrom D α).isSome →
      numSteps r ((trivialSim P).accesses D α) ≤ phi (D.loc r) := by
  intro α
  induction α with
  | nil => intro D _ _ _; simp [Sim.accesses, numSteps]
  | cons ℓ α ih =>
    intro D hD hret hsome
    simp only [Impl.runFrom_cons] at hsome
    cases hs : (trivialSim P).step D ℓ with
    | none => simp [hs] at hsome
    | some D' =>
      simp only [hs, Option.bind_some] at hsome
      have hret' : ∀ v, Label.ret r v ∉ α := fun v hv => hret v (List.mem_cons_of_mem _ hv)
      simp only [Sim.accesses, hs, Option.getD_some]
      have hc : numSteps r ((trivialSim P).accessOf D ℓ ++ (trivialSim P).accesses D' α) =
          numSteps r ((trivialSim P).accessOf D ℓ) + numSteps r ((trivialSim P).accesses D' α) := by
        simp [numSteps, List.countP_append]
      rw [hc]
      by_cases hp : ℓ.proc = r
      · cases ℓ with
        | inv q o =>
          simp only [Label.proc] at hp; subst hp
          exact absurd (Impl.step_inv hs).1 hD
        | ret q v =>
          simp only [Label.proc] at hp; subst hp
          exact absurd (List.mem_cons_self) (hret v)
        | tau q =>
          simp only [Label.proc] at hp; subst hp
          obtain ⟨-, hpend, i, o, k, hact, -, hloc⟩ := Impl.step_tau hs
          cases hl : D.loc q with
          | idle => simp [trivialSim, atomicImpl, hl] at hact
          | done x => simp [trivialSim, atomicImpl, hl] at hact
          | apply o' =>
            have hD'l : phi (D'.loc q) = 0 := by
              rw [hloc]; simp only [Function.update_self]
              simp only [trivialSim, atomicImpl, hl, Action.access.injEq] at hact
              obtain ⟨-, -, hk⟩ := hact
              rw [← eq_of_heq hk]; rfl
            have := ih D' (by rw [hpend]; exact hD) hret' hsome
            rw [hD'l] at this
            have h1 : numSteps q ((trivialSim P).accessOf D (.tau q)) = 1 := by
              simp [Sim.accessOf, hl, trivialSim, atomicImpl, numSteps]
            rw [h1]; simp only [phi]; omega
      · rw [numSteps_accessOf_ne D hp, zero_add]
        have hoth := Impl.step_other hs hp
        have := ih D' (by rw [hoth.2]; exact hD) hret' hsome
        rwa [hoth.1] at this

/-- Every read of the trivial simulation takes one step. -/
lemma trivialSim_readSteps (r : P) : (trivialSim P).ReadStepsLE r 1 := by
  intro α₁ α₂ C hC hval hret
  obtain ⟨C', hC'⟩ := hval
  rw [Impl.run, Impl.runFrom_append, show Impl.runFrom _ _ α₁ = (trivialSim P).run α₁ from rfl,
    hC, Option.bind_some, Impl.runFrom_cons] at hC'
  cases hs : (trivialSim P).step C (.inv r .read) with
  | none => simp [hs] at hC'
  | some D =>
    simp only [hs, Option.bind_some] at hC'
    obtain ⟨-, -, hpend, hloc, -⟩ := Impl.step_inv hs
    simp only [Sim.accesses, Sim.accessOf, hs, Option.getD_some, List.nil_append]
    have := numSteps_le_phi r α₂ D (by rw [hpend]; simp) hret (by rw [hC']; rfl)
    rw [hloc] at this
    simpa [trivialSim, atomicImpl, phi] using this

lemma numReads_le_numSteps {ι : Type} (p : P) (as : List (P × ι × RWOp Bool)) :
    numReads p as ≤ numSteps p as :=
  List.countP_mono_left (fun a _ h => by simp at h ⊢; exact h.1)

lemma trivialSim_readReads (r : P) : (trivialSim P).ReadReadsLE r 1 :=
  fun α₁ α₂ C hC hval hret =>
    (numReads_le_numSteps r _).trans (trivialSim_readSteps r α₁ α₂ C hC hval hret)

/-- **Non-vacuity of Theorems 3.1/3.2 and Corollary 3.5**: for `k = 2 = 2 ^ 1` the trivial
simulation is wait-free, safe, regular and atomic, and its reads read one register. -/
theorem trivialSim_hyps (w r : P) :
    (trivialSim P).WaitFree ∧ (trivialSim P).Safe w ∧ (trivialSim P).Regular w ∧
      (trivialSim P).Atomic w ∧ (∀ v, (trivialSim P).allowed w (.write v)) ∧
      (trivialSim P).allowed r .read ∧ Fintype.card Bool = 2 ^ 1 ∧
      (trivialSim P).ReadReadsLE r 1 ∧ (trivialSim P).ReadStepsLE r 1 :=
  ⟨trivialSim_waitFree, (trivialSim_atomic w).regular.safe, (trivialSim_atomic w).regular,
    trivialSim_atomic w, fun _ => trivial, trivial, rfl, trivialSim_readReads r,
    trivialSim_readSteps r⟩

/-- **The hypothesis `k > 2` of Theorem 4.1 is necessary**: for `k = 2` there is a wait-free
atomic simulation in which the reads of every reader take `log₂ k = 1` step. -/
theorem theorem_4_1_needs_k_gt_two :
    ∃ I : Sim Bool false Unit (Fin 3) (AtomicLoc (register Bool false)),
      I.WaitFree ∧ I.Atomic 0 ∧ (∀ v, I.allowed 0 (.write v)) ∧ I.allowed 1 .read ∧
      I.allowed 2 .read ∧ Fintype.card Bool = 2 ^ 1 ∧ I.ReadStepsLE 1 1 ∧ I.ReadStepsLE 2 1 :=
  ⟨trivialSim (Fin 3), trivialSim_waitFree, trivialSim_atomic 0, fun _ => trivial, trivial,
    trivial, rfl, trivialSim_readSteps 1, trivialSim_readSteps 2⟩

end Podc.FastReadsRegisterSim
