import Papers.PODC2023.PPDoubleExpThresholds.ProgramToMachineSim
import Papers.PODC2023.PPDoubleExpThresholds.ProgramToMachineSize
import Papers.PODC2023.PPDoubleExpThresholds.Decide

/-!
# Proposition 14: from population programs to population machines

`proposition_14`: if a well-formed population program over a nonempty set of registers `R`
decides `φ`, then the population machine of Appendix B.2 (`ProgramToMachine.machine`), with the
same registers, decides `φ`, and its size is at most `20 λ + 20` where `λ` is the size of the
program. All pointer domains are nonempty, and every register configuration is the register part
of an initial configuration (so `Machine.Decides` is not vacuous).

## Proof

Both systems have finitely many configurations reachable from an initial one, so stable
computation is equivalent to "from every reachable configuration a `b`-stable one is reachable"
(`forall_fair_iff_reach`). We relate machine and program configurations by `Abs`:

* machine steps are simulated by program paths (`exec_abs`, so `reach_abs`), and outputs agree;
* from every related configuration a *clean* one is reachable (`to_clean`), and program steps from
  configurations related to clean ones are simulated by machine paths (`clean_sim`).
-/

set_option linter.unusedSectionVars false

namespace Podc.PPDoubleExpThresholds.ProgramToMachine

open Finset Cslib.TransitionSystem

variable {R P : Type} [Fintype R] [DecidableEq R] [DecidableEq P] [Nonempty R]
variable {prog : Program R P}

theorem reach_abs (hwf : prog.WellFormed) {m m' : MCfg prog} {s : Cfg R P} (h : Abs prog m s)
    (hm : Reach (machine prog hwf).Step m m') : ∃ s', Abs prog m' s' ∧ Reach prog.Step s s' := by
  induction hm with
  | refl => exact ⟨s, h, .refl⟩
  | tail _ hstep ih =>
    obtain ⟨s₁, h₁, hs₁⟩ := ih
    rcases hstep with hex | ⟨rfl, -⟩
    · obtain ⟨s₂, h₂, hs₂⟩ := exec_abs hwf h₁ hex
      exact ⟨s₂, h₂, hs₁.trans hs₂⟩
    · exact ⟨s₁, h₁, hs₁⟩

theorem creach_sim (hwf : prog.WellFormed) {m : MCfg prog} {s s' : Cfg R P} (h : CAbs prog m s)
    (hs : Reach prog.Step s s') : ∃ m', Reach (machine prog hwf).Step m m' ∧ CAbs prog m' s' := by
  induction hs with
  | refl => exact ⟨m, .refl, h⟩
  | tail _ hstep ih =>
    obtain ⟨m₁, hm₁, h₁⟩ := ih
    obtain ⟨m₂, hm₂, h₂⟩ := clean_sim hwf h₁ hstep
    exact ⟨m₂, hm₁.trans hm₂, h₂⟩

theorem prog_step_total (s : Cfg R P) : ∃ s', prog.Step s s' := by
  by_cases h : ∃ s', prog.Step₀ s s' ∨ prog.RestartStep s s'
  · obtain ⟨s', h | h⟩ := h
    · exact ⟨s', .inl h⟩
    · exact ⟨s', .inr (.inl h)⟩
  · simp only [not_exists, not_or] at h
    exact ⟨s, .inr (.inr ⟨rfl, fun s'' => h s''⟩)⟩

/-- An initial machine configuration is related to an initial program configuration. -/
theorem abs_init (hwf : prog.WellFormed) {m : MCfg prog} (hm : (machine prog hwf).IsInitial m)
    {OF : Bool} (hOF : m.ptr .OF = .bool OF) : Abs prog m (prog.init m.reg OF) := by
  obtain ⟨hIP, hV, hd⟩ := hm
  have hvm : vm m = id := by funext x; simp [vm, show m.ptr (.V (some x)) = .reg x from hV x]
  exact ⟨hd, hOF, .base 0, .pre1 hIP (by rw [hvm]; rfl) (by rw [hvm]; exact Function.injective_id)⟩

/-- The machine decides what the program decides. -/
theorem machine_decides (hwf : prog.WellFormed) {φ : ℕ → Bool} (h : prog.Decides φ) :
    (machine prog hwf).Decides φ := by
  intro E hE0 hfair
  set m₀ := E.st 0 with hm₀
  have hd₀ : DomOK m₀ := hE0.2.2
  obtain ⟨OF₀, hOF₀⟩ := bool_of_dom_OF hd₀
  set s₀ := prog.init m₀.reg OF₀
  have habs₀ : Abs prog m₀ s₀ := abs_init hwf hE0 hOF₀
  set b := φ (Machine.total m₀)
  have hprog : ∀ s, Reach prog.Step s₀ s → ∃ y, Reach prog.Step s y ∧
      StableOut prog.Step Program.out b y :=
    reach_stable_of_forall_fair (Program.finite_reach hwf _ _) (fun s _ => prog_step_total s)
      (fun E' h0 hf => by
        have := h E' (by rw [h0]; rfl) hf
        rwa [h0] at this)
  refine Run.GloballyFair.stabilisesTo_of_reach hfair (finite_reach_machine (lastJump hwf) hd₀) ?_
  intro m hm
  obtain ⟨s, habs, hs⟩ := reach_abs hwf habs₀ hm
  obtain ⟨m₁, s₁, hm₁, hs₁, hc⟩ := to_clean hwf habs
  obtain ⟨y, hy, hst⟩ := hprog s₁ (hs.trans hs₁)
  obtain ⟨m₂, hm₂, hc₂⟩ := creach_sim hwf hc hy
  refine ⟨m₂, hm₁.trans hm₂, fun m₃ hm₃ => ?_⟩
  obtain ⟨s₃, habs₃, hs₃⟩ := reach_abs hwf hc₂.abs hm₃
  rw [habs₃.out hwf]
  exact hst s₃ hs₃

/-- Every register configuration is the register part of an initial configuration. -/
theorem exists_initial (hwf : prog.WellFormed) (C : R → ℕ) :
    ∃ m, (machine prog hwf).IsInitial m ∧ m.reg = C := by
  let ptr : PtrT prog → Val R
    | .OF => .bool false
    | .CF => .bool false
    | .IP => .nat 1
    | .V (some x) => .reg x
    | .V none => .reg x0
    | .ret _ => .nat 3
  refine ⟨⟨C, ptr⟩, ⟨rfl, fun x => rfl, fun X => ?_⟩, rfl⟩
  rcases X with _ | _ | _ | (_ | x) | ⟨q, hq⟩
  · simp [ptr, dom]
  · simp [ptr, dom]
  · exact (mem_dom_IP prog).2 (valid_one prog)
  · simp [ptr, dom]
  · exact mem_image_of_mem _ (self_mem_cl x)
  · simp [ptr, dom, retDom]

theorem dom_nonempty (hwf : prog.WellFormed) (X : PtrT prog) :
    ((machine prog hwf).dom X).Nonempty := by
  obtain ⟨m, hm, -⟩ := exists_initial hwf (fun _ => 0)
  exact ⟨_, hm.2.2 X⟩

end ProgramToMachine

/-- **Proposition 14** of [Czerner, *Population Protocols Decide Double-exponential Thresholds*]:
if a (well-formed) population program of size `λ` over a nonempty set of registers decides `φ`,
then there is a population machine with the same registers deciding `φ`, of size
`≤ 20 λ + 20` (the paper: `O(λ)`). Moreover all pointer domains of the machine are nonempty and
every register configuration extends to an initial configuration (non-vacuity). -/
theorem proposition_14 {R P : Type} [Fintype R] [DecidableEq R] [DecidableEq P] [Nonempty R]
    (prog : Program R P) (hwf : prog.WellFormed) {φ : ℕ → Bool} (h : prog.Decides φ) :
    ∃ (F : Type) (_ : Fintype F) (_ : DecidableEq F) (A : Machine R F),
      A.Decides φ ∧ A.size ≤ 20 * prog.size + 20 ∧ (∀ X, (A.dom X).Nonempty) ∧
        ∀ C : R → ℕ, ∃ m, A.IsInitial m ∧ m.reg = C :=
  ⟨_, inferInstance, inferInstance, ProgramToMachine.machine prog hwf,
    ProgramToMachine.machine_decides hwf h, ProgramToMachine.size_machine_le hwf,
    ProgramToMachine.dom_nonempty hwf, ProgramToMachine.exists_initial hwf⟩

end Podc.PPDoubleExpThresholds
