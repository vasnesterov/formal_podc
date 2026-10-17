import Papers.PODC2020.BezoutElection.Defs
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.Basic

/-!
# Generic liveness lemmas for infinite executions

Small tools for proving progress properties of `Impl.InfExec` under fairness
(`Impl.InfExec.IsFair`), on top of `Podc.SharedMemory.Progress` (`InfExec.first_act`,
`InfExec.cfg_add_of_proc_ne`) and `Podc.Order.NatDescent`:

* `InfExec.acts`: under fairness a process that is pending forever acts infinitely often;
* `InfExec.descent`: a measure that never increases and strictly decreases at every action of a
  process that is pending forever gives a contradiction;
* `ev_forever`, `ev_forall_fin`: "eventually forever" properties;
* `stab_nat`, `stab_finset`: a monotone, bounded sequence of numbers / finite sets is eventually
  constant.

CSLib candidates (generic for all shared-memory implementations).
-/

set_option linter.unusedSectionVars false

open Cslib.SharedMemory

namespace BezoutElection

section Generic

variable {A : ObjSpec} {ι : Type} [DecidableEq ι] {B : ι → ObjSpec} {P L : Type} [DecidableEq P]
  {I : Impl A B P L}

-- CSLib candidate
/-- Under fairness, a process that is pending forever acts infinitely often. -/
lemma InfExec.acts (e : I.InfExec) (hfair : e.IsFair) {q : P} {T : ℕ}
    (hp : ∀ t ≥ T, (e.cfg t).pend q ≠ none) (t : ℕ) (ht : T ≤ t) :
    ∃ t' ≥ t, (e.lbl t').proc = q := by
  obtain ⟨t', h1, h2, -⟩ := e.first_act hfair (hp t ht)
  exact ⟨t', h1, h2⟩

-- CSLib candidate
/-- A measure that never increases and strictly decreases at every action of a process that is
pending forever gives a contradiction (under fairness). -/
lemma InfExec.descent (e : I.InfExec) (hfair : e.IsFair) (q : P) (t₀ : ℕ) (μ : ℕ → ℕ)
    (hp : ∀ t ≥ t₀, (e.cfg t).pend q ≠ none)
    (hle : ∀ t ≥ t₀, (e.lbl t).proc ≠ q → μ (t + 1) ≤ μ t)
    (hlt : ∀ t ≥ t₀, (e.lbl t).proc = q → μ (t + 1) < μ t) : False := by
  have hmono : ∀ t ≥ t₀, μ (t + 1) ≤ μ t := fun t ht => by
    by_cases h : (e.lbl t).proc = q
    · exact (hlt t ht h).le
    · exact hle t ht h
  obtain ⟨T, hT, hc⟩ := Nat.eventually_not_of_succ_le hmono hlt
  obtain ⟨t', ht', hq⟩ := InfExec.acts e hfair hp T hT
  exact hc t' ht' hq

end Generic

-- CSLib candidate
/-- A property that is preserved from `t₀` on and holds at some time `≥ t₀` holds eventually
forever. -/
lemma ev_forever (Q : ℕ → Prop) (t₀ : ℕ) (hpres : ∀ t ≥ t₀, Q t → Q (t + 1))
    (hex : ∃ t ≥ t₀, Q t) : ∃ T ≥ t₀, ∀ t ≥ T, Q t := by
  obtain ⟨T, hT, hQ⟩ := hex
  refine ⟨T, hT, fun t ht => ?_⟩
  induction t, ht using Nat.le_induction with
  | base => exact hQ
  | succ t ht ih => exact hpres t (by omega) ih

-- CSLib candidate
/-- Finitely many "eventually forever" properties hold eventually forever simultaneously. -/
lemma ev_forall_fin {P : Type} [Fintype P] (Q : P → ℕ → Prop)
    (h : ∀ p, ∃ T, ∀ t ≥ T, Q p t) (t₀ : ℕ) : ∃ T ≥ t₀, ∀ t ≥ T, ∀ p, Q p t := by
  classical
  choose T hT using h
  refine ⟨max t₀ (Finset.univ.sup T), le_max_left _ _, fun t ht p => hT p t ?_⟩
  have : T p ≤ Finset.univ.sup T := Finset.le_sup (Finset.mem_univ p)
  omega

-- CSLib candidate
/-- A monotone bounded sequence of natural numbers is eventually constant. -/
lemma stab_nat (g : ℕ → ℕ) (t₀ N : ℕ) (hmono : ∀ t ≥ t₀, g t ≤ g (t + 1))
    (hbd : ∀ t, g t ≤ N) : ∃ T ≥ t₀, ∀ t ≥ T, g t = g T := by
  obtain ⟨T, hT, hc⟩ := Nat.eventually_const_of_succ_le (f := fun t => N - g t) (N := t₀)
    fun t ht => by have := hmono t ht; omega
  exact ⟨T, hT, fun t ht => by have := hc t ht; have := hbd t; have := hbd T; omega⟩

-- CSLib candidate
/-- A monotone sequence of finite sets of bounded cardinality is eventually constant. -/
lemma stab_finset {α : Type} (f : ℕ → Finset α) (t₀ N : ℕ)
    (hmono : ∀ t ≥ t₀, f t ⊆ f (t + 1)) (hbd : ∀ t, (f t).card ≤ N) :
    ∃ T ≥ t₀, ∀ t ≥ T, f t = f T := by
  have hmono' : ∀ t ≥ t₀, ∀ k, f t ⊆ f (t + k) := by
    intro t ht k
    induction k with
    | zero => exact Finset.Subset.refl _
    | succ k ih => exact ih.trans (hmono (t + k) (by omega))
  obtain ⟨T, hT, hc⟩ := stab_nat (fun t => (f t).card) t₀ N
    (fun t ht => Finset.card_le_card (hmono t ht)) hbd
  refine ⟨T, hT, fun t ht => ?_⟩
  have hsub := hmono' T hT (t - T)
  rw [Nat.add_sub_cancel' ht] at hsub
  exact (Finset.eq_of_subset_of_card_le hsub (by rw [hc t ht])).symm

end BezoutElection
