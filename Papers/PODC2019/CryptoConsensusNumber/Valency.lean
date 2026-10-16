import Papers.PODC2019.CryptoConsensusNumber.Defs
import Cslib.Computability.Distributed.SharedMemory.Recoverable

/-!
# Critical configurations: the two standard contradictions

Object-agnostic consequences of CSLib's valency theory (`Cslib.SharedMemory.Recoverable`, used
without crashes: `WFConsensus` = wait-free binary consensus in the crash-stop model). At a
critical execution `α` (from a reachable configuration `C`) all processes are poised on one object
`i` (`Crit.poised`); let `p` be on team `v` and `q` on the other team, with pending operations
`o` and `o'` on `i` in state `s`. Then

* `crit_overwrite`: `o'` cannot *overwrite* `o` (`δ (δ s o).1 o' = δ s o'`): otherwise `q` cannot
  distinguish `C α p q` from `C α q`. This covers "`o` does not change the state" (reads, failed
  operations) and "`o'` is a blind write";
* `crit_commute`: `o` and `o'` cannot *commute for `p`* (same final state either way and the same
  response to `p`): otherwise `p` cannot distinguish `C α p q` from `C α q p`.
-/

namespace CryptoCons

open Cslib.SharedMemory Cslib.SharedMemory.Recoverable

section Generic

variable {ι : Type} [DecidableEq ι] {T : ι → ObjSpec} {n : ℕ} {A : Alg n T}

-- CSLib candidate
/-- Two consecutive steps of different processes poised on the same object. -/
lemma stepP_stepP_same (E : Cfg A) {p q : Fin n} (hpq : p ≠ q) {i : ι} {o o' : (T i).Op}
    {κ κ' : (T i).Resp → A.L} (hp : A.act (E.loc p) = .access i o κ)
    (hq : A.act (E.loc q) = .access i o' κ') :
    ((E.stepP p).stepP q).mem = Function.update E.mem i ((T i).δ ((T i).δ (E.mem i) o).1 o').1 ∧
    ((E.stepP p).stepP q).loc q = κ' ((T i).δ ((T i).δ (E.mem i) o).1 o').2 ∧
    ((E.stepP p).stepP q).loc p = κ ((T i).δ (E.mem i) o).2 := by
  have hq' : A.act ((E.stepP p).loc q) = .access i o' κ' := by
    rw [stepP_loc_other E (Ne.symm hpq)]; exact hq
  rw [stepP_of_access _ hq', stepP_of_access E hp]
  simp [Function.update_of_ne hpq]

-- CSLib candidate
lemma stepP_same (E : Cfg A) {q : Fin n} {i : ι} {o' : (T i).Op} {κ' : (T i).Resp → A.L}
    (hq : A.act (E.loc q) = .access i o' κ') :
    (E.stepP q).mem = Function.update E.mem i ((T i).δ (E.mem i) o').1 ∧
    (E.stepP q).loc q = κ' ((T i).δ (E.mem i) o').2 := by
  rw [stepP_of_access E hq]
  simp

variable {C : Cfg A} {α : List (Ev n)}

lemma team_ne {p q : Fin n} {v w : Bool} (hA : WFConsensus A) (hC : Reach A CrashFree C)
    (hp : Team 0 C α p v) (hq : Team 0 C α q w) (hvw : w ≠ v) : p ≠ q := by
  rintro rfl
  exact hvw (hq.unique hA admOK_crashFree hC hp)

lemma inEs_two (hc : Crit 0 C α) (p q : Fin n) : InEs 0 (α ++ [.step p] ++ [.step q]) := by
  rw [List.append_assoc]; exact hc.1.append_crashFree (crashFree_steps [p, q])

lemma inEs_one (hc : Crit 0 C α) (p : Fin n) : InEs 0 (α ++ [.step p] ++ []) := by
  rw [List.append_nil]; exact hc.1.append_crashFree (crashFree_steps [p])

lemma run_two (C : Cfg A) (α : List (Ev n)) (p q : Fin n) :
    run C (α ++ [.step p] ++ [.step q]) = ((run C α).stepP p).stepP q := by
  simp [run_append, Cfg.next]

lemma run_one (C : Cfg A) (α : List (Ev n)) (p : Fin n) :
    run C (α ++ [.step p] ++ []) = (run C α).stepP p := by
  simp [run_append, Cfg.next]

/-- **Overwriting contradiction.** At a critical execution, if `p` (team `v`) and `q` (team
`w ≠ v`) are poised on the same object with operations `o`, `o'` such that `o'` applied after
`o` behaves exactly as `o'` alone (same new state, same response), we get a contradiction. -/
theorem crit_overwrite (hA : WFConsensus A) (hC : Reach A CrashFree C) (hc : Crit 0 C α)
    {p q : Fin n} {v w : Bool} (hp : Team 0 C α p v) (hq : Team 0 C α q w) (hvw : w ≠ v)
    {i : ι} {o o' : (T i).Op} {κ κ' : (T i).Resp → A.L}
    (hpa : A.act ((run C α).loc p) = .access i o κ)
    (hqa : A.act ((run C α).loc q) = .access i o' κ')
    (how : (T i).δ ((T i).δ ((run C α).mem i) o).1 o' = (T i).δ ((run C α).mem i) o') :
    False := by
  have hpq := team_ne hA hC hp hq hvw
  have hw : w = !v := by cases v <;> cases w <;> simp_all
  subst hw
  refine team_contra hA admOK_crashFree hC hp hq (r := q) (inEs_two hc p q) (inEs_one hc q) ?_
  have e1 := run_two C α p q
  have e2 := run_one C α q
  obtain ⟨m1, l1, -⟩ := stepP_stepP_same _ hpq hpa hqa
  obtain ⟨m2, l2⟩ := stepP_same _ hqa
  refine ⟨by rw [e1, e2, m1, m2, how], fun r hr => ?_⟩
  simp only [Set.mem_singleton_iff] at hr; subst hr
  exact ⟨by rw [e1, e2, l1, l2, how], by simp only [run_inp]⟩

/-- **Commuting contradiction.** At a critical execution, if `p` (team `v`) and `q` (team
`w ≠ v`) are poised on the same object with operations `o`, `o'` that lead to the same state in
both orders, and `p` gets the same response in both orders, we get a contradiction. -/
theorem crit_commute (hA : WFConsensus A) (hC : Reach A CrashFree C) (hc : Crit 0 C α)
    {p q : Fin n} {v w : Bool} (hp : Team 0 C α p v) (hq : Team 0 C α q w) (hvw : w ≠ v)
    {i : ι} {o o' : (T i).Op} {κ κ' : (T i).Resp → A.L}
    (hpa : A.act ((run C α).loc p) = .access i o κ)
    (hqa : A.act ((run C α).loc q) = .access i o' κ')
    (hst : ((T i).δ ((T i).δ ((run C α).mem i) o).1 o').1 =
      ((T i).δ ((T i).δ ((run C α).mem i) o').1 o).1)
    (hresp : ((T i).δ ((run C α).mem i) o).2 = ((T i).δ ((T i).δ ((run C α).mem i) o').1 o).2) :
    False := by
  have hpq := team_ne hA hC hp hq hvw
  have hw : w = !v := by cases v <;> cases w <;> simp_all
  subst hw
  refine team_contra hA admOK_crashFree hC hp hq (r := p) (inEs_two hc p q) (inEs_two hc q p) ?_
  have e1 := run_two C α p q
  have e2 := run_two C α q p
  obtain ⟨m1, -, l1⟩ := stepP_stepP_same _ hpq hpa hqa
  obtain ⟨m2, l2, -⟩ := stepP_stepP_same _ (Ne.symm hpq) hqa hpa
  refine ⟨by rw [e1, e2, m1, m2, hst], fun r hr => ?_⟩
  simp only [Set.mem_singleton_iff] at hr; subst hr
  exact ⟨by rw [e1, e2, l1, l2, hresp], by simp only [run_inp]⟩

end Generic

end CryptoCons
