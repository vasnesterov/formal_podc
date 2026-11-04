import Papers.PODC2011.AtMostOnceEffectiveness.Algorithm

/-!
# Step lemmas for `KK_β`

`step_inv`: the eleven kinds of transitions of a process, with the resulting configuration.
-/

set_option linter.unusedSectionVars false

namespace Podc.AtMostOnceEffectiveness

open Function

variable {m n β : ℕ} {C C' : Config m Reg ℕ LState} {p q : Fin m}

/-- The kinds of transitions of `KK_β` (with `s = C.loc p`). -/
inductive KStep (m n β : ℕ) (C : Config m Reg ℕ LState) (p : Fin m) :
    Config m Reg ℕ LState → Prop
  | compNext (h : (C.loc p).status = .compNext)
      (hb : β ≤ (free n (C.loc p) \ (C.loc p).tryS).card) :
      KStep m n β C p { C with loc := update C.loc p ({ (C.loc p) with
          status := .setNext
          q := 0
          tryS := ∅
          nxt := rank (free n (C.loc p) \ (C.loc p).tryS) (kIdx m p (free n (C.loc p)).card) }) }
  | finish (h : (C.loc p).status = .compNext)
      (hb : ¬ β ≤ (free n (C.loc p) \ (C.loc p).tryS).card) :
      KStep m n β C p { C with loc := update C.loc p { (C.loc p) with status := .finished } }
  | setNext (h : (C.loc p).status = .setNext) :
      KStep m n β C p { C with
          mem := update C.mem (.next p) (C.loc p).nxt
          loc := update C.loc p { (C.loc p) with status := .gatherTry } }
  | tryRead (h : (C.loc p).status = .gatherTry) (hq : (C.loc p).q ≠ p.val) :
      KStep m n β C p { C with loc := update C.loc p (({ (C.loc p) with
          tryS := addTry (C.mem (.next (C.loc p).q)) (C.loc p).tryS }).adv m .gatherDone) }
  | trySkip (h : (C.loc p).status = .gatherTry) (hq : (C.loc p).q = p.val) :
      KStep m n β C p { C with loc := update C.loc p ((C.loc p).adv m .gatherDone) }
  | doneRead (h : (C.loc p).status = .gatherDone) (hq : (C.loc p).q ≠ p.val)
      (hpos : (C.loc p).pos (C.loc p).q ≤ n)
      (hv : 0 < C.mem (.done (C.loc p).q ((C.loc p).pos (C.loc p).q))) :
      KStep m n β C p { C with loc := update C.loc p ({ (C.loc p) with
          doneS := insert (C.mem (.done (C.loc p).q ((C.loc p).pos (C.loc p).q))) (C.loc p).doneS
          pos := update (C.loc p).pos (C.loc p).q ((C.loc p).pos (C.loc p).q + 1) }) }
  | doneAdv (h : (C.loc p).status = .gatherDone)
      (hq : (C.loc p).q = p.val ∨
        ¬ ((C.loc p).pos (C.loc p).q ≤ n ∧ 0 < C.mem (.done (C.loc p).q ((C.loc p).pos (C.loc p).q)))) :
      KStep m n β C p { C with loc := update C.loc p ((C.loc p).adv m .check) }
  | checkOk (h : (C.loc p).status = .check) (h1 : (C.loc p).nxt ∉ (C.loc p).tryS)
      (h2 : (C.loc p).nxt ∉ (C.loc p).doneS) :
      KStep m n β C p { C with loc := update C.loc p { (C.loc p) with status := .doIt } }
  | checkFail (h : (C.loc p).status = .check)
      (h1 : (C.loc p).nxt ∈ (C.loc p).tryS ∨ (C.loc p).nxt ∈ (C.loc p).doneS) :
      KStep m n β C p { C with loc := update C.loc p { (C.loc p) with status := .compNext } }
  | perform (h : (C.loc p).status = .doIt) :
      KStep m n β C p { C with
          loc := update C.loc p { (C.loc p) with status := .done }
          log := C.log ++ [(p, (C.loc p).nxt)] }
  | writeDone (h : (C.loc p).status = .done) :
      KStep m n β C p { C with
          mem := update C.mem (.done p ((C.loc p).pos p)) (C.loc p).nxt
          loc := update C.loc p ({ (C.loc p) with
            doneS := insert (C.loc p).nxt (C.loc p).doneS
            pos := update (C.loc p).pos p ((C.loc p).pos p + 1)
            status := .compNext }) }

/-- Inversion of a step of `KK_β`. -/
theorem step_inv (hs : (kk m n β).step C p = some C') : KStep m n β C p C' := by
  cases h : (C.loc p).status <;>
    simp only [Alg.step, kk, kkNext, h, Option.some.injEq, reduceCtorEq] at hs
  · split_ifs at hs with hb
    · simp only [Option.some.injEq] at hs; subst hs; exact .compNext h hb
    · simp only [Option.some.injEq] at hs; subst hs; exact .finish h hb
  · subst hs; exact .setNext h
  · split_ifs at hs with hq
    · simp only [Option.some.injEq] at hs; subst hs
      convert KStep.tryRead (n := n) (β := β) h hq using 5; simp [h]
    · simp only [Option.some.injEq] at hs; subst hs; exact .trySkip h (not_not.mp hq)
  · split_ifs at hs with hq
    · simp only [Option.some.injEq] at hs
      by_cases hc : (C.loc p).pos (C.loc p).q ≤ n ∧
          0 < C.mem (.done (C.loc p).q ((C.loc p).pos (C.loc p).q))
      · rw [if_pos hc] at hs; subst hs
        convert KStep.doneRead (β := β) h hq hc.1 hc.2 using 4; simp [h]
      · rw [if_neg hc] at hs; subst hs; exact .doneAdv h (Or.inr hc)
    · simp only [Option.some.injEq] at hs; subst hs; exact .doneAdv h (Or.inl (not_not.mp hq))
  · split_ifs at hs with hc
    · subst hs; exact .checkOk h hc.1 hc.2
    · subst hs
      refine .checkFail h ?_
      by_contra hn; push Not at hn; exact hc ⟨hn.1, hn.2⟩
  · subst hs; exact .perform h
  · subst hs; exact .writeDone h

/-- Conversely, every transition kind is a step. -/
theorem KStep.step (hs : KStep m n β C p C') : (kk m n β).step C p = some C' := by
  cases hs with
  | compNext h hb => simp [Alg.step, kk, kkNext, h, hb]
  | finish h hb => simp [Alg.step, kk, kkNext, h, hb]
  | setNext h => simp [Alg.step, kk, kkNext, h]
  | tryRead h hq => simp [Alg.step, kk, kkNext, h, hq]
  | trySkip h hq => simp [Alg.step, kk, kkNext, h, hq]
  | doneRead h hq hpos hv => simp [Alg.step, kk, kkNext, h, hq, hpos, hv]
  | doneAdv h hq =>
    rcases hq with hq | hq
    · simp [Alg.step, kk, kkNext, h, hq]
    · by_cases hq' : (C.loc p).q = p.val
      · simp [Alg.step, kk, kkNext, h, hq']
      · simp only [Alg.step, kk, kkNext, h, ne_eq, hq', not_false_eq_true, ite_true]
        rw [if_neg hq]
  | checkOk h h1 h2 => simp [Alg.step, kk, kkNext, h, h1, h2]
  | checkFail h h1 =>
    have : ¬ ((C.loc p).nxt ∉ (C.loc p).tryS ∧ (C.loc p).nxt ∉ (C.loc p).doneS) := by tauto
    simp only [Alg.step, kk, kkNext, h]
    rw [if_neg this]
  | perform h => simp [Alg.step, kk, kkNext, h]
  | writeDone h => simp [Alg.step, kk, kkNext, h]

/-! ## `adv` -/

@[simp] lemma adv_doneS (s : LState) (st : Status) : (s.adv m st).doneS = s.doneS := by
  unfold LState.adv; split_ifs <;> rfl
@[simp] lemma adv_tryS (s : LState) (st : Status) : (s.adv m st).tryS = s.tryS := by
  unfold LState.adv; split_ifs <;> rfl
@[simp] lemma adv_pos (s : LState) (st : Status) : (s.adv m st).pos = s.pos := by
  unfold LState.adv; split_ifs <;> rfl
@[simp] lemma adv_nxt (s : LState) (st : Status) : (s.adv m st).nxt = s.nxt := by
  unfold LState.adv; split_ifs <;> rfl
lemma adv_status (s : LState) (st : Status) :
    (s.adv m st).status = if s.q + 1 < m then s.status else st := by
  unfold LState.adv; split_ifs <;> rfl
lemma adv_q (s : LState) (st : Status) :
    (s.adv m st).q = if s.q + 1 < m then s.q + 1 else 0 := by
  unfold LState.adv; split_ifs <;> rfl

/-! ## Frame lemmas -/

lemma KStep.loc_ne (hs : KStep m n β C p C') (hq : q ≠ p) : C'.loc q = C.loc q := by
  cases hs <;> simp [update_of_ne hq]

lemma KStep.log_eq (hs : KStep m n β C p C') (h : (C.loc p).status ≠ .doIt) : C'.log = C.log := by
  cases hs <;> simp_all

lemma KStep.mem_next_ne (hs : KStep m n β C p C') (r : ℕ) (hr : r ≠ p.val) :
    C'.mem (.next r) = C.mem (.next r) := by
  cases hs <;> simp [update_of_ne, hr]

lemma KStep.mem_done_ne (hs : KStep m n β C p C') (r j : ℕ) (hr : r ≠ p.val) :
    C'.mem (.done r j) = C.mem (.done r j) := by
  cases hs <;> simp [update_of_ne, hr]

end Podc.AtMostOnceEffectiveness
