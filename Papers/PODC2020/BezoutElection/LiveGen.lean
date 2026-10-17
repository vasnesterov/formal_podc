import Papers.PODC2020.BezoutElection.Defs
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.Basic

/-!
# Generic liveness lemmas for infinite executions

Small tools for proving progress properties of `Impl.InfExec` under fairness (`IsFair`):

* `InfExec.other`, `InfExec.first_act`: a process that does not act keeps its local state; under
  fairness a pending process eventually acts, and its first action happens in its current
  local state;
* `ev_forever`, `ev_forall_fin`: "eventually forever" properties;
* `stab_finset`: a monotone, bounded sequence of finite sets is eventually constant;
* `InfExec.descent`: a measure that never increases and strictly decreases at every action of a
  process that is pending forever gives a contradiction.

CSLib candidates (generic for all shared-memory implementations).
-/

set_option linter.unusedSectionVars false

open Cslib.SharedMemory

namespace BezoutElection

section Generic

variable {A : ObjSpec} {ι : Type} [DecidableEq ι] {B : ι → ObjSpec} {P L : Type} [DecidableEq P]
  {I : Impl A B P L}

-- CSLib candidate
/-- A step of another process does not change the local state and pending operation of `q`. -/
lemma InfExec.other (e : I.InfExec) {t : ℕ} {q : P} (h : (e.lbl t).proc ≠ q) :
    (e.cfg (t + 1)).loc q = (e.cfg t).loc q ∧ (e.cfg (t + 1)).pend q = (e.cfg t).pend q :=
  Impl.step_other (e.step_eq t) h

-- CSLib candidate
lemma InfExec.other_iter (e : I.InfExec) {t k : ℕ} {q : P}
    (h : ∀ j < k, (e.lbl (t + j)).proc ≠ q) :
    (e.cfg (t + k)).loc q = (e.cfg t).loc q ∧ (e.cfg (t + k)).pend q = (e.cfg t).pend q := by
  induction k with
  | zero => exact ⟨rfl, rfl⟩
  | succ k ih =>
    have h1 := ih (fun j hj => h j (by omega))
    have h2 := InfExec.other e (t := t + k) (h k (by omega))
    rw [← Nat.add_assoc, h2.1, h2.2]
    exact h1

-- CSLib candidate
/-- Under fairness, a pending process eventually acts; its first action happens in its current
local state. -/
lemma InfExec.first_act (e : I.InfExec) (hfair : IsFair e) {q : P} {t : ℕ}
    (hp : (e.cfg t).pend q ≠ none) :
    ∃ t' ≥ t, (e.lbl t').proc = q ∧ (e.cfg t').loc q = (e.cfg t).loc q ∧
      (e.cfg t').pend q = (e.cfg t).pend q := by
  classical
  obtain ⟨t₁, ht₁, hq, -⟩ := hfair q t hp
  have hex : ∃ k, (e.lbl (t + k)).proc = q := ⟨t₁ - t, by rw [Nat.add_sub_cancel' ht₁]; exact hq⟩
  refine ⟨t + Nat.find hex, by omega, Nat.find_spec hex, ?_⟩
  exact InfExec.other_iter e (fun j hj => Nat.find_min hex hj)

-- CSLib candidate
/-- Under fairness, a process that is pending forever acts infinitely often. -/
lemma InfExec.acts (e : I.InfExec) (hfair : IsFair e) {q : P} {T : ℕ}
    (hp : ∀ t ≥ T, (e.cfg t).pend q ≠ none) (t : ℕ) (ht : T ≤ t) :
    ∃ t' ≥ t, (e.lbl t').proc = q := by
  obtain ⟨t', h1, h2, -⟩ := InfExec.first_act e hfair (hp t ht)
  exact ⟨t', h1, h2⟩

-- CSLib candidate
/-- A measure that never increases and strictly decreases at every action of a process that is
pending forever gives a contradiction (under fairness). -/
lemma InfExec.descent (e : I.InfExec) (hfair : IsFair e) (q : P) (t₀ : ℕ) (μ : ℕ → ℕ)
    (hp : ∀ t ≥ t₀, (e.cfg t).pend q ≠ none)
    (hle : ∀ t ≥ t₀, (e.lbl t).proc ≠ q → μ (t + 1) ≤ μ t)
    (hlt : ∀ t ≥ t₀, (e.lbl t).proc = q → μ (t + 1) < μ t) : False := by
  have hmono : ∀ t ≥ t₀, μ (t + 1) ≤ μ t := by
    intro t ht
    by_cases h : (e.lbl t).proc = q
    · exact (hlt t ht h).le
    · exact hle t ht h
  have hanti : ∀ t ≥ t₀, ∀ k, μ (t + k) ≤ μ t := by
    intro t ht k
    induction k with
    | zero => exact le_rfl
    | succ k ih => exact (hmono (t + k) (by omega)).trans ih
  have key : ∀ k, ∃ t ≥ t₀, μ t + k ≤ μ t₀ := by
    intro k
    induction k with
    | zero => exact ⟨t₀, le_rfl, by simp⟩
    | succ k ih =>
      obtain ⟨t, ht, hμ⟩ := ih
      obtain ⟨t', ht', hq⟩ := InfExec.acts e hfair hp t ht
      have h1 := hanti t ht (t' - t)
      rw [Nat.add_sub_cancel' ht'] at h1
      have h2 := hlt t' (by omega) hq
      exact ⟨t' + 1, by omega, by omega⟩
  obtain ⟨t, -, ht⟩ := key (μ t₀ + 1)
  omega

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
  have hmono' : ∀ t ≥ t₀, ∀ k, g t ≤ g (t + k) := by
    intro t ht k
    induction k with
    | zero => exact le_rfl
    | succ k ih => exact ih.trans (hmono (t + k) (by omega))
  have key : ∀ m, ∀ t₁ ≥ t₀, N - g t₁ ≤ m → ∃ T ≥ t₁, ∀ t ≥ T, g t = g T := by
    intro m
    induction m with
    | zero =>
      intro t₁ ht₁ hm
      refine ⟨t₁, le_rfl, fun t ht => ?_⟩
      have h1 := hmono' t₁ ht₁ (t - t₁)
      rw [Nat.add_sub_cancel' ht] at h1
      have := hbd t
      omega
    | succ m ih =>
      intro t₁ ht₁ hm
      by_cases hc : ∀ t ≥ t₁, g t = g t₁
      · exact ⟨t₁, le_rfl, hc⟩
      · push Not at hc
        obtain ⟨t₂, ht₂, hne⟩ := hc
        have h1 := hmono' t₁ ht₁ (t₂ - t₁)
        rw [Nat.add_sub_cancel' ht₂] at h1
        obtain ⟨T, hT, hT'⟩ := ih t₂ (by omega) (by have := hbd t₂; omega)
        exact ⟨T, by omega, hT'⟩
  obtain ⟨T, hT, hT'⟩ := key (N - g t₀) t₀ le_rfl le_rfl
  exact ⟨T, hT, hT'⟩

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
