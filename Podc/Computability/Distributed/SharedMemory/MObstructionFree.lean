import Cslib.Computability.Distributed.SharedMemory.Progress
import Mathlib.Data.Set.Card

-- CSLib candidate: Cslib/Computability/Distributed/SharedMemory/MObstructionFree.lean

/-!
# `m`-obstruction-freedom

Taubenfeld's `m`-obstruction-freedom (contention-sensitive progress, DISC 2009): in every infinite
execution in which at most `m` processes take infinitely many steps, every correct process
completes each of its operations. It interpolates between obstruction-freedom (`m = 1`) and
wait-freedom (`m` = number of processes).

In CSLib's model (`Cslib.SharedMemory.Impl`), a process *takes infinitely many steps* in an
infinite execution `e` if infinitely many labels of `e` belong to it (invocations included, as in
the usual "a step is an invocation, an access, local computation or a response"). A process that
is idle from some point on is correct and has completed its operations, so the condition says:
a process whose operation stays pending forever takes only finitely many internal steps
(it has crashed).

## Main definitions and results

* `Impl.InfExec.infSteppers e`: the processes with infinitely many labels in `e`;
* `Impl.MObstructionFreeOn m E`: `m`-obstruction-freedom for the infinite executions all of whose
  prefixes lie in `E` (e.g. one-shot executions);
* `Impl.MObstructionFreeOn.mono`: monotonicity in `m` and `E`;
* `Impl.WaitFreeOn.mObstructionFreeOn`: wait-freedom implies `m`-obstruction-freedom;
* `Impl.not_mObstructionFreeOn_of_solo`: a reachable configuration (in `E`) from which a pending
  process never returns when running solo refutes `m`-obstruction-freedom for every `m ≥ 1`
  (the solo continuation has a single process taking infinitely many steps);
* `Impl.MObstructionFreeOn.obstructionFreeOn`: for `m ≥ 1`, `m`-obstruction-freedom implies
  obstruction-freedom (solo termination) on sets of executions closed under prefixes and internal
  steps.
-/

namespace Cslib.SharedMemory

variable {A : ObjSpec} {ι : Type} {B : ι → ObjSpec} {P L : Type} [DecidableEq P] [DecidableEq ι]

namespace Impl

variable {I : Impl A B P L}

/-- The processes that take infinitely many steps (have infinitely many labels) in `e`. -/
def InfExec.infSteppers (e : I.InfExec) : Set P := {p | ∀ N, ∃ t ≥ N, (e.lbl t).proc = p}

variable (I) in
/-- **`m`-obstruction-freedom** (Taubenfeld) on the infinite executions whose prefixes all lie in
`E`: if at most `m` processes take infinitely many steps, then a process whose operation stays
pending forever takes only finitely many internal steps. -/
def MObstructionFreeOn (m : ℕ) (E : List (Label P A) → Prop) : Prop :=
  ∀ e : I.InfExec, (∀ t, E (e.pre t)) → e.infSteppers.encard ≤ m → ∀ (p : P) (n : ℕ),
    (∀ t ≥ n, (e.cfg t).pend p ≠ none) → ∃ N, ∀ t ≥ N, e.lbl t ≠ .tau p

lemma MObstructionFreeOn.mono {m m' : ℕ} {E E' : List (Label P A) → Prop}
    (h : I.MObstructionFreeOn m E) (hm : m' ≤ m) (hE : ∀ α, E' α → E α) :
    I.MObstructionFreeOn m' E' :=
  fun e he hc => h e (fun t => hE _ (he t)) (hc.trans (by exact_mod_cast hm))

/-- Wait-freedom implies `m`-obstruction-freedom for every `m`. -/
lemma WaitFreeOn.mObstructionFreeOn {E : List (Label P A) → Prop} (h : I.WaitFreeOn E) (m : ℕ) :
    I.MObstructionFreeOn m E :=
  fun e he _ => h e he

/-- Every process of `P` takes infinitely many steps in `e` if `P` is finite and has at most
`m` elements; hence, for `m ≥ |P|`, `m`-obstruction-freedom is wait-freedom. -/
lemma mObstructionFreeOn_iff_waitFreeOn [Fintype P] {E : List (Label P A) → Prop} {m : ℕ}
    (hm : Fintype.card P ≤ m) : I.MObstructionFreeOn m E ↔ I.WaitFreeOn E := by
  refine ⟨fun h e he => h e he ?_, fun h => h.mObstructionFreeOn m⟩
  calc e.infSteppers.encard ≤ (Set.univ : Set P).encard := Set.encard_le_encard (Set.subset_univ _)
    _ = Fintype.card P := by rw [Set.encard_univ, ENat.card_eq_coe_fintype_card]
    _ ≤ m := by exact_mod_cast hm

omit [DecidableEq P] in
private lemma pre_mem_of_solo' {E : List (Label P A) → Prop} (hE : PrefixClosed E)
    (htau : ∀ α p, E α → E (α ++ [.tau p])) {α : List (Label P A)} (hα : E α) (p : P) (t : ℕ) :
    E (α.take t ++ List.replicate (t - α.length) (.tau p)) := by
  induction t with
  | zero => simpa using hE.of_prefix (List.nil_prefix) hα
  | succ t ih =>
    by_cases ht : t < α.length
    · rw [show t + 1 - α.length = 0 by omega, List.replicate_zero, List.append_nil]
      exact hE.of_prefix (List.take_prefix _ _) hα
    · rw [List.take_of_length_le (by omega)] at ih ⊢
      rw [show t + 1 - α.length = (t - α.length) + 1 by omega, List.replicate_succ',
        ← List.append_assoc]
      exact htau _ p ih

/-- **Solo livelock refutes `m`-obstruction-freedom.** If, from a configuration reached by an
execution `α ∈ E`, a pending process `p` never returns when running solo, then the algorithm is
not `m`-obstruction-free on `E` for any `m ≥ 1`: the solo continuation is an infinite execution in
which only `p` takes infinitely many steps, and `p`'s operation stays pending forever. -/
theorem not_mObstructionFreeOn_of_solo {E : List (Label P A) → Prop} (hE : PrefixClosed E)
    (htau : ∀ α p, E α → E (α ++ [.tau p])) {α : List (Label P A)} {C : Config A B P L}
    (hα : I.run α = some C) (hEα : E α) {p : P}
    (hp : ∀ k, ((I.soloStep p)^[k] C).pend p ≠ none) {m : ℕ} (hm : 1 ≤ m) :
    ¬ I.MObstructionFreeOn m E := by
  intro h
  obtain ⟨e, hpre, he, hpend⟩ := exists_infExec_solo hα hp
  have hsub : e.infSteppers ⊆ {p} := by
    intro q hq
    obtain ⟨t, ht, hq⟩ := hq α.length
    rw [he t ht] at hq
    exact hq.symm
  have hcard : e.infSteppers.encard ≤ m :=
    (Set.encard_le_encard hsub).trans (by rw [Set.encard_singleton]; exact_mod_cast hm)
  obtain ⟨N, hN⟩ := h e (fun t => hpre t ▸ pre_mem_of_solo' hE htau hEα p t) hcard p _ hpend
  exact hN (max N α.length) (le_max_left _ _) (he _ (le_max_right _ _))

/-- For `m ≥ 1`, `m`-obstruction-freedom implies obstruction-freedom (solo termination) on a set
of executions closed under prefixes and internal steps. -/
theorem MObstructionFreeOn.obstructionFreeOn {E : List (Label P A) → Prop} {m : ℕ}
    (h : I.MObstructionFreeOn m E) (hm : 1 ≤ m) (hE : PrefixClosed E)
    (htau : ∀ α p, E α → E (α ++ [.tau p])) : I.ObstructionFreeOn E := by
  intro α C p hα hEα hp
  by_contra hcon
  push Not at hcon
  exact not_mObstructionFreeOn_of_solo hE htau hα hEα hcon hm h

end Impl

end Cslib.SharedMemory
