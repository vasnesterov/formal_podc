import Papers.PODC2011.UnboundedConcurrency.Lemma15
import Papers.PODC2011.UnboundedConcurrency.Alg2

/-!
# Lemma 14 and Theorem 11: the iterator stack

Afek–Morrison–Wertheim, PODC 2011, Section 5.3.

* `lemma_14`: in a critical execution (Definition 2; `lemma_13`), the next operations `o_P`,
  `o_Q` of `P` and `Q` are writes to the same iterator stack (for algorithms using read/write-like
  objects, e.g. registers, and iterator stacks);
* `no_consensus_iterator_stack`: no algorithm using read/write-like objects and iterator stacks
  solves binary consensus (agreement, weak validity, wait-freedom) in the unbounded concurrency
  model (Lemmas 13, 14, 15);
* `theorem_11`: the iterator stack has infinite consensus number (Algorithm 2 with registers and
  one iterator stack solves `n`-process consensus for every `n`; even bounded-concurrency
  consensus, `Alg2.theorem_12`) but cannot solve consensus in the unbounded concurrency model.
-/

namespace Podc.UnboundedConcurrency

open Cslib.SharedMemory Cslib.SharedMemory.Arrival

set_option linter.unusedSectionVars false

variable {R S : Type} [DecidableEq R] [DecidableEq S] {B : R → ObjSpec} {W : S → Type}
  {A : Alg (ST B W) ℕ Bool Bool}

/-- **Lemma 14** of [AMW11]. Let `α` be critical (Definition 2): after `α P` only `v` and after
`α Q P` only `¬v` can be decided. Then `P ≠ Q` and both are poised to write to the same iterator
stack. -/
theorem lemma_14 (hrw : ∀ r, (B r).RWLike) (hwf : WaitFree A (fun s => (Set.range s).Finite))
    {x : ℕ → Bool} {α : List ℕ} {pp qq : ℕ} {v : Bool}
    (hP : Uni A x (α ++ [pp]) v) (hQ : Uni A x (α ++ [qq, pp]) (!v)) :
    pp ≠ qq ∧ ∃ s va vb ka kb,
      A.act ((A.exec x α).loc pp) = .access (.inr s) (ISOp.write va) ka ∧
      A.act ((A.exec x α).loc qq) = .access (.inr s) (ISOp.write vb) kb := by
  have hPQ : Uni A x (α ++ [pp, qq]) v := by
    simpa [List.append_assoc] using hP.append [qq]
  have hne : pp ≠ qq := by
    rintro rfl
    exact not_uni_both hwf hPQ hQ
  refine ⟨hne, ?_⟩
  set C := A.exec x α with hC
  have ePQ : A.exec x (α ++ [pp, qq]) = (C.step pp).step qq := by
    rw [show α ++ [pp, qq] = α ++ [pp] ++ [qq] by simp, Alg.exec_concat, Alg.exec_concat]
  have eQP : A.exec x (α ++ [qq, pp]) = (C.step qq).step pp := by
    rw [show α ++ [qq, pp] = α ++ [qq] ++ [pp] by simp, Alg.exec_concat, Alg.exec_concat]
  have eP : A.exec x (α ++ [pp]) = C.step pp := Alg.exec_concat _ _ _
  -- equal memories after `P Q` and `Q P` are impossible
  have hcomm : ((C.step pp).step qq).mem ≠ ((C.step qq).step pp).mem := fun h =>
    false_of_mem_eq hwf hPQ hQ (by rw [ePQ, eQP]; exact h)
  rcases Arrival.Cfg.out_or_poised C pp with ⟨w, hw⟩ | ⟨i, o, k, hactP⟩
  · exfalso; apply hcomm
    rw [Arrival.Cfg.step_of_out hw, Arrival.Cfg.step_of_out (hw.step qq)]
  rcases Arrival.Cfg.out_or_poised C qq with ⟨w, hw⟩ | ⟨j, o', k', hactQ⟩
  · exfalso; apply hcomm
    rw [Arrival.Cfg.step_of_out hw, Arrival.Cfg.step_of_out (hw.step pp)]
  by_cases hij : i = j
  swap
  · exfalso; apply hcomm
    rw [Arrival.Cfg.step_comm C ⟨o, k, hactP⟩ ⟨o', k', hactQ⟩ hne hij]
  subst hij
  rcases i with r | s
  · -- a read/write-like object: Herlihy's argument
    exfalso
    rcases hrw r o with hro | hov
    · exact hcomm (Cfg.mem_step_step_comm C hactP hactQ hne (by
        change ((B r).δ ((B r).δ (C.mem (.inl r)) o).1 o').1 =
          ((B r).δ ((B r).δ (C.mem (.inl r)) o').1 o).1
        rw [hro, hro]))
    rcases hrw r o' with hro' | hov'
    · exact hcomm (Cfg.mem_step_step_comm C hactP hactQ hne (by
        change ((B r).δ ((B r).δ (C.mem (.inl r)) o).1 o').1 =
          ((B r).δ ((B r).δ (C.mem (.inl r)) o').1 o).1
        rw [hro', hro']))
    · have h := Cfg.step_step_agreeOn_of_overwrites C hactP hov ⟨o', k', hactQ⟩ hne
      exact false_of_mem_eq hwf hP hQ (by rw [eP, eQP]; exact h.1.symm)
  · -- an iterator stack
    cases o with
    | write va =>
      cases o' with
      | write vb => exact ⟨s, va, vb, k, k', hactP, hactQ⟩
      | read kq =>
        exfalso
        by_cases hk : kq = (stk C s).its.length
        · subst hk
          exact write_read_next_false hwf hPQ hQ hne hactP hactQ
        · exact hcomm (Cfg.mem_step_step_comm C hactP hactQ hne
            (ISState.write_read_comm (stk C s) va hk))
    | read kp =>
      exfalso
      cases o' with
      | write vb =>
        by_cases hk : kp = (stk C s).its.length
        · subst hk
          exact write_read_next_false hwf hQ (by simpa using hPQ) hne.symm hactQ hactP
        · exact hcomm (Cfg.mem_step_step_comm C hactP hactQ hne
            (ISState.write_read_comm (stk C s) vb hk).symm)
      | read kq =>
        exact hcomm (Cfg.mem_step_step_comm C hactP hactQ hne
          (ISState.read_read_comm (stk C s) kp kq))

/-- **Theorem 11, impossibility part** (Lemmas 13–15 of [AMW11]). No algorithm using
read/write-like objects (e.g. registers) and iterator stacks — any number of each, initialized
arbitrarily — solves binary consensus (agreement, weak validity, wait-freedom) in the unbounded
concurrency model. -/
theorem no_consensus_iterator_stack (hrw : ∀ r, (B r).RWLike)
    (hag : Agreement A anySched) (hval : WeakValidity A anySched)
    (hwf : WaitFree A infArrival) : False := by
  classical
  have hag' : Agreement A (fun _ => True) := hag
  have hwf' : WaitFree A (fun s => (Set.range s).Finite) := fun x s _ => hwf x s trivial
  -- inputs: `p₀` proposes `false`, every other process `true`
  let x : ℕ → Bool := fun p => decide (p ≠ 0)
  have hsolo : ∀ p, CanDec A Set.univ x [] (x p) := by
    intro p
    obtain ⟨m, v, hout⟩ := exists_solo_out hwf' x [] p
    let x' : ℕ → Bool := fun _ => x p
    have hag0 : AgreeOn {p} (A.initCfg x) (A.initCfg x') :=
      Alg.initCfg_agreeOn (fun q hq => by simp at hq; subst hq; rfl)
    have hrep : ∀ s ∈ List.replicate (m + 1) p, s ∈ ({p} : Set ℕ) := fun s hs => by
      rw [List.eq_of_mem_replicate hs]; rfl
    have h2 := Alg.run_agreeOn hag0 hrep
    have hout' : (A.exec x' ([] ++ List.replicate (m + 1) p)).Out p v :=
      (h2.out_iff (by rfl) v).1 hout
    have hv : v = x p := hval (x p) x' _ trivial (fun _ => rfl) p (by simp) v hout'
    subst hv
    exact ⟨List.replicate (m + 1) p, fun _ _ => trivial, p, by simp, hout⟩
  have hbiv : Biv A Set.univ x [] := ⟨by simpa [x] using hsolo 0, by simpa [x] using hsolo 1⟩
  obtain ⟨α, pp, qq, v, hP, hQ⟩ := lemma_13 hag' hwf hbiv
  obtain ⟨hne, s, va, vb, ka, kb, hpw, hqw⟩ := lemma_14 hrw hwf' hP hQ
  have hPQ : Uni A x (α ++ [pp, qq]) v := by
    simpa [List.append_assoc] using hP.append [qq]
  exact lemma_15 hwf hPQ hQ hne hpw hqw

/-- **Theorem 11** of [AMW11]. There is an object with infinite consensus number that cannot
solve consensus wait-free in the unbounded concurrency model: the iterator stack. With read/write
registers and one iterator stack, Algorithm 2 solves `n`-process consensus for every `n` (it is
even a wait-free bounded-concurrency consensus algorithm, `Alg2.theorem_12`), while no algorithm
using registers (more generally, read/write-like objects) and iterator stacks solves binary
consensus wait-free under unbounded concurrency. -/
theorem theorem_11 :
    (∀ (V : Type) (n : ℕ), SolvesCons (Alg2.alg2 V) anySched (boundedBy n)) ∧
    ∀ (R S : Type) [DecidableEq R] [DecidableEq S] (B : R → ObjSpec) (W : S → Type)
      (A : Alg (ST B W) ℕ Bool Bool), (∀ r, (B r).RWLike) →
      Agreement A anySched → WeakValidity A anySched → ¬ WaitFree A infArrival :=
  ⟨fun _ n => Alg2.solvesCons_boundedBy n,
    fun _ _ _ _ _ _ _ hrw hag hval hwf => no_consensus_iterator_stack hrw hag hval hwf⟩

end Podc.UnboundedConcurrency
