import Papers.PODC2015.WeakestFDEventualConsistency.ECtoETOB

/-!
# Theorem 1, direction EC → ETOB: the black box must be well-formed

A run of `T_{EC→ETOB}` showing that the unconditional well-formedness hypothesis `ECIntegrity`
of `etob_of_ec` cannot be dropped when the black box is only assumed to satisfy
`RespAfterInv` and `ProperUse → EC` (the assume-guarantee form is circular: a black box that
misbehaves makes the usage improper and is then unconstrained).
-/
namespace Podc.WeakestFDEventualConsistency.ECtoETOB
open Cslib.FailureDetectors

/-! ### The well-formedness hypothesis `ECIntegrity` cannot be dropped -/

/-- Schedule of the counterexample (one process): a time-out (invoking instance `0`), the black
box answers instance `0` twice, then answers instance `2` with `[5]`; time-outs afterwards. -/
def cexSched : ℕ → Option (Unit × Choice Unit (Input ℕ))
  | 1 => some ((), .input (.ecResp 0 []))
  | 2 => some ((), .input (.ecResp 0 []))
  | 3 => some ((), .input (.ecResp 2 [5]))
  | _ => some ((), .tick)

/-- The counterexample run (no crashes). -/
def cexRun : Run Unit Unit (Input ℕ) := ⟨FailurePattern.noCrash, fun _ _ => (), cexSched⟩

lemma cexSched_cases (t : ℕ) :
    cexSched t = some ((), .tick) ∨ (t = 1 ∧ cexSched t = some ((), .input (.ecResp 0 []))) ∨
      (t = 2 ∧ cexSched t = some ((), .input (.ecResp 0 []))) ∨
      (t = 3 ∧ cexSched t = some ((), .input (.ecResp 2 [5]))) := by
  unfold cexSched
  split <;> simp

lemma cexSched_ne_recv (t : ℕ) (q : Unit) (s : ℕ) : cexSched t ≠ some ((), .recv q s) := by
  rcases cexSched_cases t with h | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ <;> rw [h] <;> simp

lemma cexSched_ne_bcast (t : ℕ) (m : ℕ) : cexSched t ≠ some ((), .input (.bcast m)) := by
  rcases cexSched_cases t with h | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ <;> rw [h] <;> simp

lemma cex_msg (t s : ℕ) : ((alg (R := Unit)).cfg cexRun t).msg s = none := by
  by_contra hc
  obtain ⟨⟨q, m⟩, hm⟩ := Option.ne_none_iff_exists'.mp hc
  obtain ⟨c, e, hσ, he, hb⟩ := Algorithm.msg_spec cexRun hm
  obtain ⟨m', -, rfl⟩ := step_msg _ _ _ _ hb
  rw [event_eq_input he] at hσ
  exact cexSched_ne_bcast s m' hσ

lemma cex_admissible : (alg (R := Unit)).Admissible cexRun where
  alive _ _ _ _ h := h
  recv_valid t p q s h := absurd h (cexSched_ne_recv t q s)
  recv_once t _ p q s h := absurd h (cexSched_ne_recv t q s)
  ticks p _ T := ⟨T + 4, by omega, by
    rcases cexSched_cases (T + 4) with h | ⟨h', -⟩ | ⟨h', -⟩ | ⟨h', -⟩
    · exact h
    all_goals omega⟩
  delivery p _ t s q m h := by rw [cex_msg] at h; simp at h

lemma cex_respAfterInv : (ecHist cexRun).RespAfterInv := by
  rintro ⟨⟩ j l t h
  change cexSched t = _ at h
  rcases cexSched_cases t with h' | ⟨rfl, h'⟩ | ⟨rfl, h'⟩ | ⟨rfl, h'⟩ <;> rw [h'] at h <;>
    simp only [Option.some.injEq, Prod.mk.injEq, Choice.input.injEq, Input.ecResp.injEq,
      reduceCtorEq, and_false, true_and] at h
  · obtain ⟨rfl, rfl⟩ := h
    exact ⟨_, 0, by omega, inv_iff.mpr ⟨by decide, by decide, rfl⟩⟩
  · obtain ⟨rfl, rfl⟩ := h
    exact ⟨_, 0, by omega, inv_iff.mpr ⟨by decide, by decide, rfl⟩⟩
  · obtain ⟨rfl, rfl⟩ := h
    exact ⟨_, 2, by omega, inv_iff.mpr ⟨by decide, by decide, rfl⟩⟩

lemma cex_not_properUse : ¬ (ecHist cexRun).ProperUse := by
  intro h
  obtain ⟨v, hv⟩ := h.resp_inv () 0 [] 2 rfl
  have := (inv_iff.mp hv).1
  revert this
  decide

/-- **The hypothesis `ECIntegrity` of `etob_of_ec` cannot be dropped.** In this admissible run
the black box answers only invoked instances (`RespAfterInv`), but answers instance `0` twice:
`T_{EC→ETOB}` then invokes instance `2` instead of `1`, so the usage is improper and the black box
is unconstrained (`ProperUse → EC` holds vacuously); it answers `[5]`, a message nobody
broadcast, violating TOB-No-creation. -/
theorem etob_of_ec_needs_integrity :
    (alg (R := Unit)).Admissible cexRun ∧ (ecHist cexRun).RespAfterInv ∧
      ((ecHist cexRun).ProperUse → EC cexRun.F (ecHist cexRun)) ∧ (tobHist cexRun).Distinct ∧
      ¬ ETOB cexRun.F (tobHist cexRun) := by
  refine ⟨cex_admissible, cex_respAfterInv, fun h => absurd h cex_not_properUse,
    fun p q m t t' h _ => absurd (show cexSched t = _ from h) (cexSched_ne_bcast t m), ?_⟩
  rintro ⟨-, hnc, -⟩
  obtain ⟨q, t, -, hb⟩ := hnc () 4 5 (by decide)
  exact cexSched_ne_bcast t 5 hb

end Podc.WeakestFDEventualConsistency.ECtoETOB
