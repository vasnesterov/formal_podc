import Cslib.Computability.Distributed.SelfStabilization.StoneAge
import Mathlib

/-!
# Corollary 1.2 of [EK21] fails for arbitrary (non-static) tasks

Corollary 1.2 claims that *every* task with a synchronous self-stabilizing SA algorithm on
`D`-bounded diameter graphs has an asynchronous one. Counterexample for `D = 1` (complete graphs),
task "all nodes output the same value at all times, and the outputs change infinitely often":

* `toggle_sync`: the synchronous algorithm `δ(b, S) = ¬(true ∈ S)` solves it on every complete graph
  (after one round all nodes agree, then they toggle together). (It does not work on, e.g., `P₃`;
  the counterexample only needs the class of complete graphs, i.e. `D = 1`.)
* `no_async_alg`: on `K₂`, under any schedule activating at most one node per step (e.g. the fair
  round-robin schedule, `no_async_alg_roundRobin`), no deterministic SA algorithm solves it: the
  first output change after the outputs agree makes them disagree.

The synchronizer of Section 4 is correct for static tasks (`Synchronizer.lean`).
-/

namespace ThinUnison

open Cslib.StoneAge

theorem signal_top {V Q : Type*} (C : V → Q) (v : V) :
    signal (⊤ : SimpleGraph V) C v = Set.range C := by
  ext q
  simp only [mem_signal, SimpleGraph.top_adj, Set.mem_range]
  constructor
  · rintro ⟨u, -, rfl⟩; exact ⟨u, rfl⟩
  · rintro ⟨u, rfl⟩
    refine ⟨u, ?_, rfl⟩
    by_cases h : u = v
    · exact Or.inl h
    · exact Or.inr fun h' => h h'.symm

open Classical in
/-- The synchronous toggling algorithm: output `¬(true is sensed)`. -/
noncomputable def toggle : Algorithm Bool := ⟨fun _ S => !(decide (true ∈ S))⟩

/-- On every complete graph, the synchronous execution of `toggle` has all outputs equal from
round 1 on, and every output changes at every later step. -/
theorem toggle_sync {V : Type*} (C0 : V → Bool) {t : ℕ} (ht : 1 ≤ t) :
    (∀ u v, run ⊤ toggle C0 sync t u = run ⊤ toggle C0 sync t v) ∧
      ∀ v, run ⊤ toggle C0 sync (t + 1) v ≠ run ⊤ toggle C0 sync t v := by
  classical
  have hstep : ∀ s v, run ⊤ toggle C0 sync (s + 1) v =
      !(decide (true ∈ Set.range (run ⊤ toggle C0 sync s))) := by
    intro s v
    rw [(isRun_run ⊤ toggle C0 sync).succ_of_mem (Set.mem_univ v), signal_top]
    rfl
  obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
  refine ⟨fun u v => by rw [hstep, hstep], fun v => ?_⟩
  rw [hstep (s + 1) v]
  have hall : ∀ u, run ⊤ toggle C0 sync (s + 1) u = run ⊤ toggle C0 sync (s + 1) v := fun u => by
    rw [hstep, hstep]
  cases h : run ⊤ toggle C0 sync (s + 1) v
  · have : true ∉ Set.range (run ⊤ toggle C0 sync (s + 1)) := by
      rintro ⟨u, hu⟩; rw [hall u, h] at hu; exact Bool.false_ne_true hu
    simp [this]
  · have : true ∈ Set.range (run ⊤ toggle C0 sync (s + 1)) := ⟨v, h⟩
    simp [this]

/-- On `K₂`, under any schedule that never activates both nodes at once, no deterministic SA
algorithm has outputs that are eventually always equal and change infinitely often. -/
theorem no_async_alg {Q O : Type*} (P : Algorithm Q) (out : Q → O) (C0 : Fin 2 → Q)
    {A : ℕ → Set (Fin 2)} (hA : ∀ s, ¬ (0 ∈ A s ∧ 1 ∈ A s)) :
    ¬ ∃ T, (∀ t, T ≤ t → out (run ⊤ P C0 A t 0) = out (run ⊤ P C0 A t 1)) ∧
      ∀ t, T ≤ t → ∃ s, t ≤ s ∧ out (run ⊤ P C0 A (s + 1) 0) ≠ out (run ⊤ P C0 A s 0) := by
  rintro ⟨T, heq, hchg⟩
  obtain ⟨s, hs, hne⟩ := hchg T le_rfl
  have hC := isRun_run ⊤ P C0 A
  have h0 : (0 : Fin 2) ∈ A s := by
    by_contra h; exact hne (by rw [hC.succ_of_not_mem h])
  have h1 : (1 : Fin 2) ∉ A s := fun h => hA s ⟨h0, h⟩
  apply hne
  rw [heq (s + 1) (by omega), hC.succ_of_not_mem h1, heq s hs]

/-- The round-robin schedule on `K₂` is fair and activates one node at a time, so the task above
has no asynchronous solution although it has a synchronous one (`toggle_sync`): Corollary 1.2 of
[EK21] is false for arbitrary tasks (already for `D = 1`). -/
theorem no_async_alg_roundRobin {Q O : Type*} (P : Algorithm Q) (out : Q → O) (C0 : Fin 2 → Q) :
    Fair (roundRobin (Equiv.refl (Fin 2))) ∧
    ¬ ∃ T, (∀ t, T ≤ t → out (run ⊤ P C0 (roundRobin (Equiv.refl _)) t 0) =
        out (run ⊤ P C0 (roundRobin (Equiv.refl _)) t 1)) ∧
      ∀ t, T ≤ t → ∃ s, t ≤ s ∧ out (run ⊤ P C0 (roundRobin (Equiv.refl _)) (s + 1) 0) ≠
        out (run ⊤ P C0 (roundRobin (Equiv.refl _)) s 0) := by
  refine ⟨fair_roundRobin _, no_async_alg P out C0 fun s h => ?_⟩
  simp only [roundRobin, Equiv.refl_apply, Set.mem_ofPred_eq, Fin.val_zero, Fin.val_one] at h
  omega

end ThinUnison
