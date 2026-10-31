import Papers.PODC2015.HelpFreeWaitFree.Defs

/-!
# Starvation along a chain of executions contradicts wait-freedom

A generic tool for adversarial constructions that build an infinite execution as the limit of a
chain of finite executions (Figure 4.1 of [CPT15]): if along the chain a process `p` takes
unboundedly many base-object steps but never returns, the implementation is not wait-free.
-/

-- CSLib candidate: Cslib/Computability/Distributed/SharedMemory/Progress.lean

set_option linter.unusedSectionVars false

namespace Podc.HelpFreeWaitFree

open Cslib.SharedMemory

variable {A : ObjSpec} {ι : Type} [DecidableEq ι] {B : ι → ObjSpec} {P L : Type} [DecidableEq P]

lemma exists_ge_of_lt_countP {α : Type} (q : α → Bool) {l : List α} {N : ℕ}
    (h : N < l.countP q) : ∃ j, N ≤ j ∧ ∃ hj : j < l.length, q l[j] = true := by
  have hsplit : l.countP q = (l.take N).countP q + (l.drop N).countP q := by
    rw [← List.countP_append, List.take_append_drop]
  have htake : (l.take N).countP q ≤ N :=
    (List.countP_le_length).trans (by simp)
  have hpos : 0 < (l.drop N).countP q := by omega
  obtain ⟨x, hx, hqx⟩ := List.countP_pos_iff.1 hpos
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hx
  simp only [List.length_drop] at hi
  refine ⟨N + i, by omega, by omega, ?_⟩
  rw [List.getElem_drop] at hqx; exact hqx

/-- **Starvation contradicts wait-freedom.** Let `E` be a chain of finite executions of unbounded
length. If process `p` never returns along the chain (after `E 0`) but takes unboundedly many
base-object steps, then `I` is not wait-free. -/
theorem false_of_starving_chain {I : Impl A B P L} (hwf : I.WaitFree) (E : ℕ → List (Label P A))
    (hmono : ∀ k, E k <+: E (k + 1)) (hlen : ∀ k, k ≤ (E k).length) (hval : ∀ k, I.Valid (E k))
    (p : P) (hresp : ∀ k, (respsOf (E k) p).length = (respsOf (E 0) p).length)
    (htau : ∀ N, ∃ k, N ≤ (E k).countP (Label.isTauOf p)) : False := by
  obtain ⟨e, hlbl, -⟩ := I.exists_infExec_of_chain E hmono hlen hval
  have hmono' : ∀ k m, k ≤ m → E k <+: E m := by
    intro k m hkm
    induction m, hkm using Nat.le_induction with
    | base => exact List.prefix_refl _
    | succ m _ ih => exact ih.trans (hmono m)
  -- no response of `p` after `E 0`
  have hnoret : ∀ m, (E 0).length ≤ m → ∀ r, e.lbl m ≠ .ret p r := by
    intro m hm r hr
    have hk : m < (E (m + 1)).length := by have := hlen (m + 1); omega
    rw [hlbl (m + 1) m hk] at hr
    have h0 : E 0 <+: (E (m + 1)).take m := by
      rw [List.prefix_take_iff]; exact ⟨hmono' 0 (m + 1) (by omega), hm⟩
    have h1 := (respsOf_prefix h0 p).length_le
    have h2 : (E (m + 1)).take (m + 1) = (E (m + 1)).take m ++ [.ret p r] := by
      rw [List.take_succ_eq_append_getElem hk, hr]
    have h3 := (respsOf_prefix (List.take_prefix (m + 1) (E (m + 1))) p).length_le
    rw [h2, respsOf_append] at h3
    simp only [respsOf_cons, Label.retOf_ret, ↓reduceIte, Option.toList_some, respsOf_nil,
      List.append_nil, List.length_append, List.length_singleton] at h3
    have := hresp (m + 1)
    omega
  -- infinitely many steps of `p`
  have hinf : ∀ N, ∃ m, N ≤ m ∧ e.lbl m = .tau p := by
    intro N
    obtain ⟨k, hk⟩ := htau (N + 1)
    obtain ⟨j, hj, hjl, hq⟩ := exists_ge_of_lt_countP (Label.isTauOf p) (l := E k) (by omega : N < _)
    refine ⟨j, hj, ?_⟩
    rw [hlbl k j hjl]; exact (Label.isTauOf_eq_true_iff).1 hq
  obtain ⟨m₀, hm₀, hlm₀⟩ := hinf (E 0).length
  -- `p` is pending from `m₀` on
  have hpend : ∀ m, m₀ ≤ m → (e.cfg m).pend p ≠ none := by
    intro m hm
    induction m, hm using Nat.le_induction with
    | base => have := e.step_eq m₀; rw [hlm₀] at this; exact (Impl.step_tau this).1
    | succ m hm ih =>
      have hs := e.step_eq m
      by_cases hq : (e.lbl m).proc = p
      · cases hl : e.lbl m with
        | inv q o =>
          rw [hl] at hs hq; simp only [Label.proc] at hq; subst hq
          exact absurd (Impl.step_inv hs).1 ih
        | tau q =>
          rw [hl] at hs hq; simp only [Label.proc] at hq; subst hq
          rw [(Impl.step_tau hs).2.1]; exact ih
        | ret q r =>
          rw [hl] at hq; simp only [Label.proc] at hq; subst hq
          exact absurd hl (hnoret m (by omega) r)
      · rw [(Impl.step_other hs hq).2]; exact ih
  obtain ⟨N, hN⟩ := hwf e p m₀ hpend
  obtain ⟨m, hm, hlm⟩ := hinf N
  exact hN m hm hlm

end Podc.HelpFreeWaitFree
