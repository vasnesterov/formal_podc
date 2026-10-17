import Papers.PODC2020.BezoutElection.Alg2Prog3

/-!
# Algorithm 2, progress: stabilization

In an execution where no competition is solved any more (`PCtx`), the candidate flags, `to_win`
and `finishing` of all processes eventually stop changing (`Stab`); from then on, every open
register satisfies the hypotheses `LCtx` of the liveness of a competition (`Q.lctx`).
-/

set_option linter.unusedSectionVars false
set_option linter.deprecated false

open Cslib.SharedMemory Finset

namespace BezoutElection.Alg2

variable {Id : Type} [DecidableEq Id] {m : ℕ} {P : Type} [DecidableEq P] [Fintype P]
  {π : P → Equiv.Perm (Fin m)} {pp : Params} {ids : P → Id} {R : Type} [Inhabited R]
  {out : Id → Finset Id → R}

lemma okOf_congr {s s' : St Id m} (k : Fin m) (hc : s.cand = s'.cand) (ht : s.toWin = s'.toWin) :
    okOf s k = okOf s' k := by
  simp only [okOf, hc, ht]

namespace PCtx

variable {e : ((alg2 Id m pp out).impl ids π).InfExec} (Q : PCtx e)
include Q

lemma run_ca (x : Fin m) (i : ℕ) (q : P) :
    (((Q.run x).A i).loc q).ca = ((e.cfg (Q.T + i)).loc q).cand ((π q).symm x) := rfl

lemma cand_eq_ca {τ : ℕ} (hτ : Q.T ≤ τ) (q : P) (k : Fin m) :
    ((e.cfg τ).loc q).cand k = (((Q.run (π q k)).A (τ - Q.T)).loc q).ca := by
  rw [run_ca, Nat.add_sub_cancel' hτ, Equiv.symm_apply_apply]

/-- The candidate flags eventually stabilize. -/
lemma cand_stab : ∃ Tc ≥ Q.T, ∀ τ ≥ Tc, ∀ q, ((e.cfg (τ + 1)).loc q).cand = ((e.cfg τ).loc q).cand := by
  obtain ⟨I, -, hI⟩ := Nat.eventually_forall_of_finite
    (p := fun x i => ∀ q, (((Q.run x).A (i + 1)).loc q).ca = (((Q.run x).A i).loc q).ca) (fun x => by
      by_cases hx : ((e.cfg Q.t0).mem () x).level < pp.U
      · exact (Q.lctx0 x hx).ca_stab
      · refine ⟨0, fun i _ q => ?_⟩
        have hclosed : ∀ i, (((Q.run x).A i).loc q).ca = false := by
          intro i
          by_contra hne
          have := ((Q.run x).inv i).1.caU q (by simpa using hne)
          rw [run_reg, Q.lev_eq (by have := Q.t0_le_T; omega)] at this
          exact hx this
        rw [hclosed, hclosed]) 0
  refine ⟨Q.T + I, by omega, fun τ hτ q => funext fun k => ?_⟩
  rw [Q.cand_eq_ca (by omega), Q.cand_eq_ca (by omega),
    show τ + 1 - Q.T = τ - Q.T + 1 by omega]
  exact hI (τ - Q.T) (by omega) (π q k) q

/-- `finishing` and `to_win` eventually stabilize. -/
lemma fin_stab : ∃ Tf, ∀ τ ≥ Tf, ∀ q,
    ((e.cfg (τ + 1)).loc q).finishing = ((e.cfg τ).loc q).finishing ∧
      ((e.cfg (τ + 1)).loc q).toWin = ((e.cfg τ).loc q).toWin := by
  obtain ⟨Tf, -, h⟩ := Nat.eventually_forall_of_finite (p := fun q τ =>
    ((e.cfg (τ + 1)).loc q).finishing = ((e.cfg τ).loc q).finishing ∧
      ((e.cfg (τ + 1)).loc q).toWin = ((e.cfg τ).loc q).toWin) (fun q => by
    have hsf := fun τ => step_fin (Q.rinv τ) (e.step_eq τ) q
    obtain ⟨T1, -, hf⟩ := WellFoundedGT.eventually_const_of_le_succ
      (f := fun τ => ((e.cfg τ).loc q).finishing) (N := 0) fun τ _ => Bool.le_iff_imp.2 (hsf τ).1
    obtain ⟨T2, hT2, h2⟩ := Nat.eventually_const_of_succ_le
      (f := fun τ => ((e.cfg τ).loc q).toWin) (N := T1)
      (fun τ hτ => (hsf τ).2 (by rw [hf τ hτ, hf (τ + 1) (by omega)]))
    refine ⟨T2, fun τ hτ => ⟨?_, ?_⟩⟩
    · rw [hf τ (by omega), hf (τ + 1) (by omega)]
    · have := h2 τ hτ; have := h2 (τ + 1) (by omega); omega) 0
  exact ⟨Tf, h⟩

end PCtx

/-- A time from which candidate flags, `to_win` and `finishing` no longer change. -/
structure Stab {e : ((alg2 Id m pp out).impl ids π).InfExec} (Q : PCtx e) where
  Ts : ℕ
  hT : Q.T ≤ Ts
  cand : ∀ τ ≥ Ts, ∀ q, ((e.cfg τ).loc q).cand = ((e.cfg Ts).loc q).cand
  fin : ∀ τ ≥ Ts, ∀ q, ((e.cfg τ).loc q).finishing = ((e.cfg Ts).loc q).finishing
  tw : ∀ τ ≥ Ts, ∀ q, ((e.cfg τ).loc q).toWin = ((e.cfg Ts).loc q).toWin

namespace PCtx

variable {e : ((alg2 Id m pp out).impl ids π).InfExec} (Q : PCtx e)
include Q

lemma stab_ex : Nonempty (Stab Q) := by
  obtain ⟨Tc, hTc, hc⟩ := Q.cand_stab
  obtain ⟨Tf, hf⟩ := Q.fin_stab
  have key : ∀ τ ≥ max Tc Tf, ∀ q, ((e.cfg τ).loc q).cand = ((e.cfg (max Tc Tf)).loc q).cand ∧
      ((e.cfg τ).loc q).finishing = ((e.cfg (max Tc Tf)).loc q).finishing ∧
      ((e.cfg τ).loc q).toWin = ((e.cfg (max Tc Tf)).loc q).toWin := by
    intro τ hτ q
    induction τ, hτ using Nat.le_induction with
    | base => exact ⟨rfl, rfl, rfl⟩
    | succ τ hτ ih =>
      obtain ⟨a, b, c⟩ := ih
      obtain ⟨b', c'⟩ := hf τ (by omega) q
      exact ⟨(hc τ (by omega) q).trans a, b'.trans b, c'.trans c⟩
  exact ⟨⟨max Tc Tf, by omega, fun τ hτ q => (key τ hτ q).1, fun τ hτ q => (key τ hτ q).2.1,
    fun τ hτ q => (key τ hτ q).2.2⟩⟩

end PCtx

end BezoutElection.Alg2
