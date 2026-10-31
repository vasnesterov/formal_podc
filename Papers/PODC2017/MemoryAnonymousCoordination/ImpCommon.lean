import Podc.Computability.Distributed.SharedMemory.UnnamedCovering
import Cslib.Computability.Distributed.SharedMemory.Solo
import Cslib.Computability.Distributed.SharedMemory.Consensus
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Card

/-!
# Common lemmas for the impossibility results of Section 6

Taubenfeld, *Coordination Without Prior Agreement*, PODC 2017, Section 6.

* `solo_from`: one-shot obstruction-freedom lets a process finish solo from any configuration
  reached by a one-shot execution.
* `exists_ps_of_infinite`, `exists_ps_of_card_lt`: enough fresh processes to cover any finite set
  of registers, when the number of processes is unbounded, resp. when there are fewer registers
  than processes.
-/

open Cslib.SharedMemory

namespace Podc.MemoryAnonymousCoordination

variable {A : ObjSpec} {ι V P L : Type} {v₀ : V} [DecidableEq P] [DecidableEq ι]

/-- Under one-shot obstruction-freedom, a process finishes solo (no invocations) from any
configuration reached by a one-shot execution. -/
lemma solo_from {J : Impl A (RegFamily ι V v₀) P L} (hof : J.OneShotOF) {α : List (Label P A)}
    {F : Config A (RegFamily ι V v₀) P L} (hα : J.run α = some F) (hos : OneShot α) (p : P) :
    ∃ γ F', (∀ ℓ ∈ γ, ℓ.proc = p) ∧ (∀ r, opsOf γ r = []) ∧ J.runFrom F γ = some F' ∧
      F'.pend p = none := by
  obtain ⟨γ, F', hγ, hops, hr, hfin, -⟩ := J.exists_finish (E := OneShot) hof
    (fun _ _ h h' => h.append_of_opsOf_nil h') [p] hα hos
  exact ⟨γ, F', fun ℓ hℓ => by simpa using hγ ℓ hℓ, hops, hr, hfin p (by simp)⟩

omit [DecidableEq P] [DecidableEq ι] in
/-- An unbounded supply of processes: every finite set of registers can be matched by as many
fresh processes. -/
lemma exists_ps_of_infinite [Infinite P] (q : P) (W : Finset ι) :
    ∃ ps : List P, ps.Nodup ∧ q ∉ ps ∧ ps.length = W.card := by
  obtain ⟨t, ht, hcard⟩ := ((Set.finite_singleton q).infinite_compl :
    ({q}ᶜ : Set P).Infinite).exists_subset_card_eq W.card
  refine ⟨t.toList, t.nodup_toList, fun h => ?_, by simp [hcard]⟩
  exact ht (Finset.mem_toList.1 h) rfl

omit [DecidableEq ι] in
/-- Fewer registers than processes: every set of registers can be matched by as many processes
other than `q`. -/
lemma exists_ps_of_card_lt [Fintype P] [Fintype ι] (h : Fintype.card ι < Fintype.card P) (q : P)
    (W : Finset ι) : ∃ ps : List P, ps.Nodup ∧ q ∉ ps ∧ ps.length = W.card := by
  have hW : W.card ≤ (Finset.univ.erase q).card := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ q), Finset.card_univ]
    have := W.card_le_univ
    omega
  obtain ⟨t, ht, hcard⟩ := Finset.exists_subset_card_eq hW
  refine ⟨t.toList, t.nodup_toList, fun h => ?_, by simp [hcard]⟩
  exact (Finset.mem_erase.1 (ht (Finset.mem_toList.1 h))).1 rfl

end Podc.MemoryAnonymousCoordination
