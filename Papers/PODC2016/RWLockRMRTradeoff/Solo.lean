import Papers.PODC2016.RWLockRMRTradeoff.Regions
import Cslib.Computability.Distributed.SharedMemory.Progress

/-!
# Solo runs of lock operations

* `regFold_soloLabels`: a pending `lock()` run solo moves its process from `trying` to the CS
  once it returns.
* `soloLabels_tau`: as long as a solo run does not return, all its labels are internal steps.
* `solo_returns_of_deadlockFree`: with deadlock freedom, from a configuration in which nobody is
  in the CS and only `p` has a pending operation, `p` returns when it runs solo
  (-- CSLib candidate: `Cslib/Computability/Distributed/SharedMemory/Mutex.lean`).
-/

namespace Podc.RWLockRMRTradeoff

open Cslib.SharedMemory

variable {ι : Type} [DecidableEq ι] {B : ι → ObjSpec} {P L : Type} [DecidableEq P]
variable (I : Impl mutexObj B P L)

lemma soloStep_iterate_of_idle {p : P} {C : Config mutexObj B P L} (hC : C.pend p = none)
    (k : ℕ) : (I.soloStep p)^[k] C = C := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', ih]; simp [Impl.soloStep, hC]

lemma soloLabels_of_idle {p : P} {C : Config mutexObj B P L} (hC : C.pend p = none) (k : ℕ) :
    I.soloLabels p C k = [] := by
  cases k <;> simp [Impl.soloLabels, hC]

/-- A pending operation run solo: internal steps until the response. -/
lemma regFold_soloLabels (p : P) (r r' : Region) (hr : ∀ x, Region.next r (.ret p x) = some r')
    (hτ : Region.next r (.tau p) = some r) :
    ∀ (k : ℕ) (C : Config mutexObj B P L), C.pend p ≠ none →
      regFold (some r) (I.soloLabels p C k) p =
        some (if ((I.soloStep p)^[k] C).pend p = none then r' else r) := by
  intro k
  induction k with
  | zero => intro C hC; simp [Impl.soloLabels, hC]
  | succ k ih =>
    intro C hC
    rw [Impl.soloLabels_succ, if_neg hC, Function.iterate_succ_apply]
    obtain ⟨C', hC'⟩ := Option.isSome_iff_exists.1 (I.step_nextLabel_isSome C p hC)
    have hstep : I.soloStep p C = C' := by simp [Impl.soloStep, hC, hC']
    rw [hstep]
    unfold Impl.nextLabel at hC' ⊢
    split at hC'
    · rename_i i o k' hact
      have hp' : C'.pend p ≠ none := by rw [(Impl.step_tau hC').2.1]; exact hC
      rw [regFold_cons]
      simp only [Label.proc, ite_true, Option.bind_some, hτ]
      exact ih C' hp'
    · rename_i x l hact
      have hp' : C'.pend p = none := by simp [(Impl.step_ret hC').2.1]
      rw [regFold_cons]
      simp only [Label.proc, ite_true, Option.bind_some, hr, soloLabels_of_idle I hp',
        soloStep_iterate_of_idle I hp', hp', regFold_nil, if_true]

/-- Solo runs contain no invocations. -/
lemma soloLabels_not_inv (p : P) :
    ∀ (k : ℕ) (C : Config mutexObj B P L), ∀ ℓ ∈ I.soloLabels p C k, ∀ q o, ℓ ≠ .inv q o := by
  intro k
  induction k with
  | zero => intro C; simp [Impl.soloLabels]
  | succ k ih =>
    intro C ℓ hℓ q o
    rw [Impl.soloLabels_succ] at hℓ
    split_ifs at hℓ
    · simp at hℓ
    · rcases List.mem_cons.1 hℓ with rfl | hℓ
      · unfold Impl.nextLabel; split <;> exact fun h => by cases h
      · exact ih _ ℓ hℓ q o

/-- Labels of a solo run that has not returned are internal steps. -/
lemma soloLabels_tau (p : P) :
    ∀ (k : ℕ) (C : Config mutexObj B P L), ((I.soloStep p)^[k] C).pend p ≠ none →
      ∀ ℓ ∈ I.soloLabels p C k, ℓ = .tau p := by
  intro k
  induction k with
  | zero => intro C _; simp [Impl.soloLabels]
  | succ k ih =>
    intro C hk
    have hC : C.pend p ≠ none := by
      intro h; apply hk; rw [soloStep_iterate_of_idle I h]; exact h
    rw [Impl.soloLabels_succ, if_neg hC]
    rw [Function.iterate_succ_apply] at hk
    obtain ⟨C', hC'⟩ := Option.isSome_iff_exists.1 (I.step_nextLabel_isSome C p hC)
    have hstep : I.soloStep p C = C' := by simp [Impl.soloStep, hC, hC']
    rw [hstep] at hk ⊢
    intro ℓ hℓ
    rcases List.mem_cons.1 hℓ with rfl | hℓ
    · unfold Impl.nextLabel at hC' ⊢
      split at hC'
      · rfl
      · exfalso
        have hp' : C'.pend p = none := by simp [(Impl.step_ret hC').2.1]
        exact hk (by rw [soloStep_iterate_of_idle I hp']; exact hp')
    · exact ih C' hk ℓ hℓ

/-- If every solo run of `p` from `C` that has not returned has at most `b` internal steps, then
`p` returns within `b + 1` solo steps. -/
lemma exists_solo_return {p : P} {C : Config mutexObj B P L} (b : ℕ)
    (hb : ∀ k, ((I.soloStep p)^[k] C).pend p ≠ none →
      tauCount p (I.soloLabels p C k) ≤ b) :
    ∃ k, ((I.soloStep p)^[k] C).pend p = none := by
  by_contra hcon
  push Not at hcon
  have h1 := hb (b + 1) (hcon _)
  have hlen := I.soloLabels_length p C (b + 1) (fun i _ => hcon i)
  have hall := soloLabels_tau I p (b + 1) C (hcon _)
  have : tauCount p (I.soloLabels p C (b + 1)) = b + 1 := by
    unfold tauCount
    rw [List.countP_eq_length.2 (fun ℓ hℓ => by rw [hall ℓ hℓ]; simp [isTauOf]), hlen]
  omega

-- CSLib candidate: Cslib/Computability/Distributed/SharedMemory/Mutex.lean
/-- **Deadlock freedom gives solo termination.** If nobody is in the CS after `α`, only `p` has a
pending operation, then `p` running solo returns. -/
theorem solo_returns_of_deadlockFree (hDF : I.DeadlockFree) {α : List (Label P mutexObj)}
    {C : Config mutexObj B P L} (hα : I.run α = some C) (hwf : ClientWF α)
    (hcs : ∀ q, ¬ InCS α q) {p : P} (hp : C.pend p ≠ none) (hidle : ∀ q, q ≠ p → C.pend q = none) :
    ∃ k, ((I.soloStep p)^[k] C).pend p = none := by
  classical
  by_contra hcon
  push Not at hcon
  let E : ℕ → List (Label P mutexObj) := fun k => α ++ I.soloLabels p C k
  have hE : ∀ k, I.run (E k) = some ((I.soloStep p)^[k] C) := fun k => by
    simp only [E]; rw [Impl.run_append_of_eq I hα, Impl.runFrom_soloLabels]
  have hElen : ∀ k, (E k).length = α.length + k := fun k => by
    simp only [E, List.length_append, I.soloLabels_length p C k (fun i _ => hcon i)]
  obtain ⟨e, hlbl, hcfg⟩ := I.exists_infExec_of_chain E
    (fun k => (List.prefix_append_right_inj α).2 (I.soloLabels_prefix p C k))
    (fun k => by rw [hElen]; omega) (fun k => ⟨_, hE k⟩)
  -- labels after `α` are internal steps of `p`
  have hlate : ∀ t ≥ α.length, e.lbl t = .tau p := by
    intro t ht
    rw [hlbl (t - α.length + 1) t (by rw [hElen]; omega)]
    simp only [E]
    rw [List.getElem_append_right (by omega)]
    exact soloLabels_tau I p _ C (hcon _) _ (List.getElem_mem _)
  have hearly : ∀ t (ht : t < α.length), e.lbl t = α[t] := by
    intro t ht
    rw [hlbl 0 t (by rw [hElen]; omega)]
    simp only [E]
    rw [List.getElem_append_left ht]
  have hpreα : e.pre α.length = α := by
    apply List.ext_getElem (by simp)
    intro t h1 h2
    simp only [Impl.InfExec.pre, List.getElem_map, List.getElem_range]
    exact hearly t h2
  have hcfgα : e.cfg α.length = C := by
    have := e.run_pre α.length; rw [hpreα, hα] at this; exact (Option.some.inj this).symm
  -- regions
  have hpre_late : ∀ t, α.length ≤ t →
      e.pre t = α ++ List.replicate (t - α.length) (.tau p) := by
    intro t ht
    induction t, ht using Nat.le_induction with
    | base => simp [hpreα]
    | succ t ht ih =>
      rw [Impl.InfExec.pre_succ, ih, hlate t ht, show t + 1 - α.length = (t - α.length) + 1 by
        omega, List.replicate_succ', List.append_assoc]
  have hwf' : ∀ t, ClientWF (e.pre t) := by
    intro t q
    by_cases ht : t ≤ α.length
    · have hpfx : e.pre t <+: α := by
        rw [← hpreα]
        have : e.pre t = (e.pre α.length).take t := by
          simp only [Impl.InfExec.pre]; rw [← List.map_take, List.take_range, min_eq_left ht]
        rw [this]; exact List.take_prefix _ _
      rw [regionOf_eq_regFold]
      exact regFold_ne_none_of_prefix hpfx (hwf q)
    · rw [hpre_late t (by omega), regionOf_append, regFold_taus]
      · exact hwf q
      · intro ℓ hℓ _; rw [List.eq_of_mem_replicate hℓ]; exact ⟨p, rfl⟩
  -- fairness
  have hfair : e.Fair := by
    intro q t hq
    by_cases hqp : q = p
    · subst hqp
      exact ⟨max t α.length, le_max_left _ _, by rw [hlate _ (le_max_right _ _)]; rfl,
        by rw [hlate _ (le_max_right _ _)]; trivial⟩
    · -- `q` is idle at time `|α|` and after, so it is pending only before `|α|` and steps
      have hidle' : ∀ s ≥ α.length, (e.cfg s).pend q = none := by
        intro s hs
        have := e.cfg_add_of_proc_ne (t := α.length) (k := s - α.length) (q := q)
          (fun j _ => by rw [hlate _ (by omega)]; exact fun h => hqp h.symm)
        rw [show α.length + (s - α.length) = s by omega] at this
        rw [this.2, hcfgα]; exact hidle q hqp
      have ht : t < α.length := by
        by_contra h; exact hq (hidle' t (by omega))
      have hex : ∃ j, (e.lbl (t + j)).proc = q := by
        by_contra hno
        push Not at hno
        have := e.cfg_add_of_proc_ne (t := t) (k := α.length - t) (q := q) (fun j _ => hno j)
        rw [show t + (α.length - t) = α.length by omega] at this
        exact hq (this.2 ▸ hidle' α.length le_rfl)
      have hc := e.cfg_add_of_proc_ne fun j hj => Nat.find_min hex hj
      refine ⟨t + Nat.find hex, by omega, Nat.find_spec hex, ?_⟩
      have hs := e.step_eq (t + Nat.find hex)
      have hq' := Nat.find_spec hex
      cases hl : e.lbl (t + Nat.find hex) with
      | inv q' o =>
        rw [hl] at hs hq'; simp only [Label.proc] at hq'; subst hq'
        exact absurd (Impl.step_inv hs).1 (hc.2 ▸ hq)
      | ret _ _ => trivial
      | tau _ => trivial
  obtain ⟨t', ht', q, r, hret⟩ := hDF e hwf' hfair α.length ⟨p, by rw [hcfgα]; exact hp⟩
    (fun q => by rw [hpreα]; exact hcs q)
  rw [hlate t' ht'] at hret
  cases hret

end Podc.RWLockRMRTradeoff
