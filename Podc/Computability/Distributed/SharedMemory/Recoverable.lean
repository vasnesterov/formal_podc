import Cslib.Computability.Distributed.SharedMemory.Recoverable
import Cslib.Computability.Distributed.SharedMemory.ObjClasses

-- CSLib candidate: Cslib/Computability/Distributed/SharedMemory/Recoverable.lean (append to the
-- existing file)

/-!
# Crash-recovery model: single steps and the critical-configuration contradictions

Additions to `Cslib/Computability/Distributed/SharedMemory/Recoverable.lean`.

At a critical execution `α` all processes are poised on one object `i` (`Crit.poised`), and there
are processes `p`, `q` on opposite teams (`Crit.teams`). The standard case analysis of
Herlihy-style valency proofs then derives a contradiction from properties of the two pending
operations `o` (of `p`) and `o'` (of `q`) at the current state `s` of `i`:

* *absorption* (`Team.false_of_absorb`): `o'` behaves the same after `o` as alone
  (`δ (δ s o).1 o' = δ s o'`; e.g. `o` is read-only, or `o'` is a blind write) — then `q`
  cannot distinguish `C α p q` from `C α q`;
* *commutation* (`Team.false_of_commute`): `o` and `o'` commute at `s` (`ObjSpec.CommuteAt`) and
  `p` gets the same response in both orders — then `p` cannot distinguish `C α p q` from
  `C α q p`;
* read/write-like objects (`Team.false_of_rwLike`, `Crit.not_forall_poised_of_rwLike`): the
  processes of a critical execution are never all poised on a read/write-like object.

The statements are for an arbitrary crash budget `z` and admissibility predicate `Adm`, so they
apply both to recoverable consensus and (with `z = 0`, `Adm = CrashFree`) to wait-free consensus.

## Main statements

* `Cfg.next_step`, `stepP_inp`, `stepP_mem_of_access`, `stepP_loc_self`, `stepP_mem_self`,
  `stepP_mem_other`, `stepP_stepP_mem`, `stepP_stepP_loc`: the effect of one or two steps of
  processes poised on an object.
* `agreeOn_stepP_stepP_of_absorb`, `agreeOn_stepP_stepP_of_commute`: indistinguishability after
  two steps on the same object.
* `Reach.run_true`: with all crash patterns admissible, reachability is closed under events.
* `Team.ne`, `Team.false_of_absorb`, `Team.false_of_commute`, `Team.false_of_rwLike`,
  `Crit.not_forall_poised_of_rwLike`.
-/

namespace Cslib.SharedMemory.Recoverable

open Cslib.SharedMemory

variable {ι : Type} [DecidableEq ι] {T : ι → ObjSpec} {n : ℕ} {A : Alg n T}

/-! ### Single steps -/

/-- A step event is a step of its process. -/
lemma Cfg.next_step (C : Cfg A) (p : Fin n) : C.next (.step p) = C.stepP p := rfl

/-- Steps do not change the inputs. -/
@[simp] lemma stepP_inp (C : Cfg A) (p : Fin n) : (C.stepP p).inp = C.inp := next_inp C (.step p)

section Access

variable {p : Fin n} {i : ι} {o : (T i).Op} {k : (T i).Resp → A.L}

/-- The object values after a step of a process poised to apply `o` to `i`. -/
lemma stepP_mem_of_access (C : Cfg A) (h : A.act (C.loc p) = .access i o k) :
    (C.stepP p).mem = Function.update C.mem i ((T i).δ (C.mem i) o).1 := by
  rw [stepP_of_access C h]

/-- The local state of a process after its step applying `o` to `i`. -/
lemma stepP_loc_self (C : Cfg A) (h : A.act (C.loc p) = .access i o k) :
    (C.stepP p).loc p = k ((T i).δ (C.mem i) o).2 := by
  rw [stepP_of_access C h]; exact Function.update_self _ _ _

/-- The value of object `i` after a step applying `o` to `i`. -/
lemma stepP_mem_self (C : Cfg A) (h : A.act (C.loc p) = .access i o k) :
    (C.stepP p).mem i = ((T i).δ (C.mem i) o).1 := by
  rw [stepP_mem_of_access C h]; exact Function.update_self _ _ _

/-- A step applying an operation to `i` does not change the other objects. -/
lemma stepP_mem_other (C : Cfg A) (h : A.act (C.loc p) = .access i o k) {j : ι} (hj : j ≠ i) :
    (C.stepP p).mem j = C.mem j := by
  rw [stepP_mem_of_access C h]; exact Function.update_of_ne hj _ _

variable {q : Fin n} {o' : (T i).Op} {k' : (T i).Resp → A.L}

/-- The object values after steps of `p` and then `q`, both poised on `i`. -/
lemma stepP_stepP_mem (C : Cfg A) (hpq : p ≠ q) (hp : A.act (C.loc p) = .access i o k)
    (hq : A.act (C.loc q) = .access i o' k') :
    ((C.stepP p).stepP q).mem =
      Function.update C.mem i ((T i).δ ((T i).δ (C.mem i) o).1 o').1 := by
  have hq' : A.act ((C.stepP p).loc q) = .access i o' k' := by
    rw [stepP_loc_other C (Ne.symm hpq)]; exact hq
  rw [stepP_mem_of_access _ hq', stepP_mem_self C hp, stepP_mem_of_access C hp,
    Function.update_idem]

/-- The local state of `q` after steps of `p` and then `q`, both poised on `i`. -/
lemma stepP_stepP_loc (C : Cfg A) (hpq : p ≠ q) (hp : A.act (C.loc p) = .access i o k)
    (hq : A.act (C.loc q) = .access i o' k') :
    ((C.stepP p).stepP q).loc q = k' ((T i).δ ((T i).δ (C.mem i) o).1 o').2 := by
  have hq' : A.act ((C.stepP p).loc q) = .access i o' k' := by
    rw [stepP_loc_other C (Ne.symm hpq)]; exact hq
  rw [stepP_loc_self _ hq', stepP_mem_self C hp]

/-- **Absorption.** If the operation `o'` of `q` on `i` behaves the same (new value and
response) after the operation `o` of `p` on `i` as alone, then `C p q` and `C q` are
indistinguishable to `q`. -/
lemma agreeOn_stepP_stepP_of_absorb (C : Cfg A) (hpq : p ≠ q)
    (hp : A.act (C.loc p) = .access i o k) (hq : A.act (C.loc q) = .access i o' k')
    (h : (T i).δ ((T i).δ (C.mem i) o).1 o' = (T i).δ (C.mem i) o') :
    AgreeOn {q} ((C.stepP p).stepP q) (C.stepP q) := by
  refine ⟨by rw [stepP_stepP_mem C hpq hp hq, stepP_mem_of_access C hq, h], fun r hr => ?_⟩
  rw [Set.mem_singleton_iff] at hr
  subst hr
  exact ⟨by rw [stepP_stepP_loc C hpq hp hq, stepP_loc_self C hq, h], by simp⟩

/-- **Commutation.** If the operations `o` of `p` and `o'` of `q` on `i` commute at the current
value of `i`, and `p` gets the same response in both orders, then `C p q` and `C q p` are
indistinguishable to `p`. -/
lemma agreeOn_stepP_stepP_of_commute (C : Cfg A) (hpq : p ≠ q)
    (hp : A.act (C.loc p) = .access i o k) (hq : A.act (C.loc q) = .access i o' k')
    (hst : (T i).CommuteAt (C.mem i) o o')
    (hresp : ((T i).δ (C.mem i) o).2 = ((T i).δ ((T i).δ (C.mem i) o').1 o).2) :
    AgreeOn {p} ((C.stepP p).stepP q) ((C.stepP q).stepP p) := by
  refine ⟨?_, fun r hr => ?_⟩
  · rw [stepP_stepP_mem C hpq hp hq, stepP_stepP_mem C (Ne.symm hpq) hq hp]
    exact congrArg (Function.update C.mem i) hst
  rw [Set.mem_singleton_iff] at hr
  subst hr
  refine ⟨?_, by simp⟩
  rw [stepP_stepP_loc C (Ne.symm hpq) hq hp, stepP_loc_other _ hpq, stepP_loc_self C hp, hresp]

end Access

/-- With all event sequences admissible (recoverable consensus), reachability is preserved by
arbitrary events. -/
lemma Reach.run_true {C : Cfg A} (hC : Reach A (fun _ => True) C) (β : List (Ev n)) :
    Reach A (fun _ => True) (Recoverable.run C β) := by
  obtain ⟨x, γ, -, rfl⟩ := hC
  exact ⟨x, γ ++ β, trivial, by rw [run_append]⟩

/-! ### Contradictions at critical executions -/

section Crit

variable {Adm : List (Ev n) → Prop} {z : ℕ} {C : Cfg A} {α : List (Ev n)} {p q : Fin n}
  {v w : Bool}

/-- Processes on different teams are different. -/
lemma Team.ne (hA : Solves A Adm) (hAdm : AdmOK Adm z) (hC : Reach A Adm C)
    (hp : Team z C α p v) (hq : Team z C α q w) (hvw : v ≠ w) : p ≠ q := by
  rintro rfl
  exact hvw (hp.unique hA hAdm hC hq)

/-- **Absorption contradiction.** If `p` and `q` are on different teams at `α` and the operation
of `q` behaves the same after the operation of `p` on the same object as alone, we get a
contradiction (`q` cannot distinguish `α p q` from `α q`). -/
theorem Team.false_of_absorb (hA : Solves A Adm) (hAdm : AdmOK Adm z) (hC : Reach A Adm C)
    (hα : InEs z α) (hp : Team z C α p v) (hq : Team z C α q w) (hvw : v ≠ w) {i : ι}
    {o o' : (T i).Op} {k k' : (T i).Resp → A.L}
    (hpa : A.act ((run C α).loc p) = .access i o k)
    (hqa : A.act ((run C α).loc q) = .access i o' k')
    (h : (T i).δ ((T i).δ ((run C α).mem i) o).1 o' = (T i).δ ((run C α).mem i) o') : False := by
  have hpq := hp.ne hA hAdm hC hq hvw
  obtain rfl : w = !v := by cases v <;> cases w <;> simp_all
  refine team_contra hA hAdm hC hp hq (r := q) (β := [.step q]) (β' := [])
    (by rw [List.append_assoc]; exact hα.append_crashFree (crashFree_steps [p, q]))
    (by rw [List.append_nil]; exact hα.append_crashFree (crashFree_steps [q])) ?_
  simp only [List.append_nil, run_append, run_cons, run_nil, Cfg.next]
  exact agreeOn_stepP_stepP_of_absorb _ hpq hpa hqa h

/-- **Commutation contradiction.** If `p` and `q` are on different teams at `α`, their
operations on the same object commute at its current value, and `p` gets the same response in
both orders, we get a contradiction (`p` cannot distinguish `α p q` from `α q p`). -/
theorem Team.false_of_commute (hA : Solves A Adm) (hAdm : AdmOK Adm z) (hC : Reach A Adm C)
    (hα : InEs z α) (hp : Team z C α p v) (hq : Team z C α q w) (hvw : v ≠ w) {i : ι}
    {o o' : (T i).Op} {k k' : (T i).Resp → A.L}
    (hpa : A.act ((run C α).loc p) = .access i o k)
    (hqa : A.act ((run C α).loc q) = .access i o' k')
    (hst : (T i).CommuteAt ((run C α).mem i) o o')
    (hresp : ((T i).δ ((run C α).mem i) o).2 =
      ((T i).δ ((T i).δ ((run C α).mem i) o').1 o).2) : False := by
  have hpq := hp.ne hA hAdm hC hq hvw
  obtain rfl : w = !v := by cases v <;> cases w <;> simp_all
  refine team_contra hA hAdm hC hp hq (r := p) (β := [.step q]) (β' := [.step p])
    (by rw [List.append_assoc]; exact hα.append_crashFree (crashFree_steps [p, q]))
    (by rw [List.append_assoc]; exact hα.append_crashFree (crashFree_steps [q, p])) ?_
  simp only [run_append, run_cons, run_nil, Cfg.next]
  exact agreeOn_stepP_stepP_of_commute _ hpq hpa hqa hst hresp

/-- Two processes on different teams at `α` cannot both be poised on the same read/write-like
object (the "standard argument": a read is absorbed by anything, a blind write absorbs
anything). -/
theorem Team.false_of_rwLike (hA : Solves A Adm) (hAdm : AdmOK Adm z) (hC : Reach A Adm C)
    (hα : InEs z α) (hp : Team z C α p v) (hq : Team z C α q w) (hvw : v ≠ w) {i : ι}
    (hRW : (T i).RWLike) (hpi : (run C α).Poised p i) (hqi : (run C α).Poised q i) : False := by
  obtain ⟨o, k, hpa⟩ := hpi
  obtain ⟨o', k', hqa⟩ := hqi
  rcases hRW o with h | h
  · exact hp.false_of_absorb hA hAdm hC hα hq hvw hpa hqa (by rw [h])
  · rcases hRW o' with h' | h'
    · exact hq.false_of_absorb hA hAdm hC hα hp hvw.symm hqa hpa (by rw [h'])
    · exact hp.false_of_absorb hA hAdm hC hα hq hvw hpa hqa (h' _ _)

/-- At a critical execution, the processes are not all poised on a read/write-like object. -/
theorem Crit.not_forall_poised_of_rwLike (hA : Solves A Adm) (hAdm : AdmOK Adm z)
    (hC : Reach A Adm C) (hn : 0 < n) (hc : Crit z C α) {i : ι} (hRW : (T i).RWLike) :
    ¬ ∀ p, (run C α).Poised p i := by
  intro hpo
  obtain ⟨⟨p, hp⟩, ⟨q, hq⟩⟩ := hc.teams hA hAdm hC hn
  exact hp.false_of_rwLike hA hAdm hC hc.1 hq (by simp) hRW (hpo p) (hpo q)

end Crit

end Cslib.SharedMemory.Recoverable
