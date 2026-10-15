import Papers.PODC2025.StrangerFreeTasks.StrangerFree
import Papers.PODC2025.StrangerFreeTasks.BoundedLA

/-!
# `k`-bounded lattice agreement for `k + 1` processes is stranger-free (§3.2)

The paper argues: for `k + 1` processes, containment and self-inclusion give that for any two
outputting processes one output contains the other process, "and thus" the task is
stranger-free. The missing step — *if `j` is in `i`'s output then `j` appears in `i`'s view* —
is validity plus a causal-erasure argument (`Impl.fullInfo_exists_erase`): if `j` did not appear
in `i`'s view, erasing the causal future of `j` gives an execution in which `j` does not
participate but `i` outputs the same set, violating validity.

## Main results

* `boundedLA_strangerFree`: for `|P| = k + 1`, `boundedLA P k` is stranger-free for every
  progress condition (even the strongest variant, quantifying over obstruction-free algorithms).
* `boundedLA_lowerBound` (lower bound of Theorem 3.1): every obstruction-free (in particular every
  wait-free) algorithm solving `k`-bounded lattice agreement for `k + 1` processes uses at least
  `k + 1` registers.
-/

set_option linter.unusedSectionVars false

namespace Cslib.SharedMemory.StrangerFree

open Cslib.SharedMemory Impl

variable {P : Type} [DecidableEq P]

/-- If `j` belongs to the output of `i` in an execution of the full-information version of an
algorithm solving bounded lattice agreement, then `j` appears in `i`'s view. -/
theorem mentions_of_mem_output {k : ℕ} {ι V L : Type} [DecidableEq ι] {v₀ : V}
    {I : Impl (laObj P) (RegFamily ι V v₀) P L} (hI : I.Solves (boundedLA P k))
    {α : List (Label P (laObj P))} {C : FIConfig (laObj P) ι V P L v₀}
    (hα : I.fullInfo.run α = some C) (h1 : OneShot α) {i j : P} {o : Finset P}
    (ho : outputs α i = some o) (hj : j ∈ o) : (C.loc i).2.Mentions j := by
  by_contra hm
  obtain ⟨α', hα', hj', hsame, hsub⟩ := I.fullInfo_exists_erase j hα
  have h1' : OneShot α' := fun y => (hsub y).length_le.trans (h1 y)
  have hΔ := (I.fullInfo_solves (T := boundedLA P k) hI) α' hα' h1'
  have ho' : outputs α' i = some o := by
    simp only [outputs] at ho ⊢; rw [(hsame i hm).2]; exact ho
  exact (hΔ i o ho').1 j hj (congrArg List.head? hj')

/-- **`k`-bounded lattice agreement for `k + 1` processes is stranger-free** (§3.2), with respect to
any progress condition. -/
theorem boundedLA_strangerFree [Fintype P] {k : ℕ} (hk : Fintype.card P = k + 1)
    (prog : Progress) : (boundedLA P k).StrangerFree prog := by
  intro ι V L _ v₀ I hI _ _ α C hα h1 i j hi hj
  by_cases hij : i = j
  · subst hij; exact Or.inl (I.fullInfo_run_mentions_self hα i)
  by_contra hcon
  push Not at hcon
  obtain ⟨hmi, hmj⟩ := hcon
  obtain ⟨oi, hoi⟩ : ∃ o : Finset P, outputs α i = some o := by
    cases h : respsOf α i with
    | nil => exact absurd h hi
    | cons o _ => exact ⟨o, by simp only [outputs, h, List.head?_cons]; rfl⟩
  obtain ⟨oj, hoj⟩ : ∃ o : Finset P, outputs α j = some o := by
    cases h : respsOf α j with
    | nil => exact absurd h hj
    | cons o _ => exact ⟨o, by simp only [outputs, h, List.head?_cons]; rfl⟩
  have hΔ := (I.fullInfo_solves hI) α ⟨C, hα⟩ h1
  have hji : j ∉ oi := fun h => hmi (mentions_of_mem_output hI hα h1 hoi h)
  have hij' : i ∉ oj := fun h => hmj (mentions_of_mem_output hI hα h1 hoj h)
  have hcard : ∀ (o : Finset P) (z : P), z ∉ o → o.card ≤ k := by
    intro o z hz
    have : o ⊆ Finset.univ.erase z := fun y hy => Finset.mem_erase.2 ⟨fun h => hz (h ▸ hy), by simp⟩
    have := Finset.card_le_card this
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, hk] at this
    omega
  rcases (hΔ i oi hoi).2.2 j oj hoj (hcard oi j hji) (hcard oj i hij') with h | h
  · exact hij' (h (hΔ i oi hoi).2.1)
  · exact hji (h (hΔ j oj hoj).2.1)

/-- **Lower bound of Theorem 3.1.** For `k ≥ 1`, every obstruction-free (a fortiori every
wait-free) read/write algorithm solving `k`-bounded lattice agreement for `k + 1` processes, in
which every process may participate, uses at least `k + 1` registers. -/
theorem boundedLA_lowerBound [Fintype P] {k : ℕ} (hk1 : 1 ≤ k) (hk : Fintype.card P = k + 1)
    {ι V L : Type} [DecidableEq ι] [Fintype ι] {v₀ : V}
    (I : Impl (laObj P) (RegFamily ι V v₀) P L) (hI : I.Solves (boundedLA P k))
    (hof : I.ObstructionFree) (hin : ∀ p, I.allowed p ()) : k + 1 ≤ Fintype.card ι := by
  haveI : Nonempty (boundedLA P k).In := ⟨()⟩
  have := theorem_2_1_obstructionFree (T := boundedLA P k) I (by omega)
    (boundedLA_strangerFree hk .obstructionFree) hI hof (fun p _ => hin p)
  omega

/-- The wait-free version of the lower bound of Theorem 3.1. -/
theorem boundedLA_lowerBound_waitFree [Fintype P] {k : ℕ} (hk1 : 1 ≤ k)
    (hk : Fintype.card P = k + 1) {ι V L : Type} [DecidableEq ι] [Fintype ι] {v₀ : V}
    (I : Impl (laObj P) (RegFamily ι V v₀) P L) (hI : I.Solves (boundedLA P k))
    (hwf : I.WaitFree) (hin : ∀ p, I.allowed p ()) : k + 1 ≤ Fintype.card ι :=
  boundedLA_lowerBound hk1 hk I hI (WaitFree.obstructionFree I hwf) hin

end Cslib.SharedMemory.StrangerFree
