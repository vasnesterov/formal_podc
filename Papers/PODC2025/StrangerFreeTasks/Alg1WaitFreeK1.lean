import Papers.PODC2025.StrangerFreeTasks.Alg1WaitFreeK1Doomed
import Mathlib.Data.Set.Finite.Lattice

/-!
# Algorithm 1 is wait-free for `k = 1`

For `k = 1` (two registers), Algorithm 1 *is* wait-free, for any set of processes (finite or
infinite). Contrast with `alg1_not_waitFree` (`Alg1Livelock.lean`): for `k ≥ 2` it is not.

Proof (by contradiction). Suppose process `p` takes infinitely many steps in an infinite
execution.

1. `p` never decides: a decided process is stuck (its only action is to return).
2. No configuration is `Doomed` for `p`: from a doomed configuration `p` decides within a
   bounded number of its own steps (`doomed_step`, potential `pot`).
3. Hence a process `x ≠ p` never writes `A[1]` twice (`IA`: in its odd iterations after its
   third write it sees another process and outputs), and it writes `A[1]` at all only if its
   first collect read the initial value of `A[1]` (`PROV`), i.e. if it took a step before the
   first write to `A[1]`. So only finitely many writes to `A[1]` by processes other than `p`
   happen.
4. After the last of them, the next odd iteration of `p` (in which it writes `A[0]`) sees an
   unchanged `A[1]`, and `A[0]` can only change to a non-`p` value, which would make the
   configuration doomed; so the snapshot succeeds and `p` outputs (`QP`, `qp_final`) —
   contradicting 1. The progress measure `prog` makes "the next odd iteration" precise.
-/

namespace Cslib.SharedMemory.StrangerFree

open Cslib.SharedMemory

variable {P : Type} [DecidableEq P]

/-- A sequence of naturals that never increases after `t0` cannot decrease infinitely often. -/
lemma no_descent (f : ℕ → ℕ) (t0 : ℕ) (hmono : ∀ t, t0 ≤ t → f (t + 1) ≤ f t)
    (hstrict : ∀ N, ∃ m, N ≤ m ∧ f (m + 1) < f m) : False := by
  have anti : ∀ a b, t0 ≤ a → a ≤ b → f b ≤ f a := by
    intro a b ha hab
    induction b, hab using Nat.le_induction with
    | base => exact le_rfl
    | succ b hb ih => exact (hmono b (ha.trans hb)).trans ih
  have key : ∀ c, ∃ t, t0 ≤ t ∧ f t + c ≤ f t0 := by
    intro c
    induction c with
    | zero => exact ⟨t0, le_rfl, le_rfl⟩
    | succ c ih =>
      obtain ⟨t, ht, hc⟩ := ih
      obtain ⟨m, hm, hlt⟩ := hstrict t
      exact ⟨m + 1, by omega, by have := anti t m ht hm; omega⟩
  obtain ⟨t, -, ht⟩ := key (f t0 + 1)
  omega

/-- The configurations of an infinite execution are reachable. -/
lemma run_range_alg1 (e : (alg1 (P := P) 1).InfExec) (t : ℕ) :
    (alg1 1).run ((List.range t).map e.lbl) = some (e.cfg t) := by
  induction t with
  | zero => simp [e.cfg_zero]
  | succ t ih =>
    rw [List.range_succ, List.map_append, List.map_singleton, Impl.run_append_of_eq _ ih,
      Impl.runFrom_singleton]
    exact e.step_eq t

/-- In every infinite execution of Algorithm 1 with `k = 1`, every process takes only finitely
many steps. -/
theorem alg1_one_finite_steps (e : (alg1 (P := P) 1).InfExec) (p : P) :
    ∃ N, ∀ m ≥ N, e.lbl m ≠ .tau p := by
  by_contra hcon
  push Not at hcon
  have hinf : ∀ N, ∃ m, N ≤ m ∧ e.lbl m = .tau p := fun N => by
    obtain ⟨m, hm, h⟩ := hcon N; exact ⟨m, hm, h⟩
  have hB : ∀ t, BInv ((List.range t).map e.lbl) (e.cfg t) :=
    fun t => bInv_of_run (run_range_alg1 e t)
  have hS : ∀ t, SInvK1 (e.cfg t) := fun t => sInvK1_of_run (run_range_alg1 e t)
  have hst := e.step_eq
  -- 1. `p` never decides
  have hND : ∀ t, ((e.cfg t).loc p).phase ≠ .done := by
    intro t hd
    have hdone : ∀ m, t ≤ m → ((e.cfg m).loc p).phase = .done := by
      intro m hm
      induction m, hm using Nat.le_induction with
      | base => exact hd
      | succ m _ ih => rw [step_loc_done (hst m) ih]; exact ih
    obtain ⟨m, hm, hl⟩ := hinf t
    have h' := hst m
    rw [hl] at h'
    rcases step_tau_phase h' with h'' | h'' | h'' <;> rw [hdone m hm] at h'' <;> cases h''
  -- 2. no configuration is doomed
  have hNDm : ∀ t, ¬ Doomed p (e.cfg t) := by
    intro t0 hD
    have hall : ∀ t, t0 ≤ t → Doomed p (e.cfg t) := by
      intro t ht
      induction t, ht using Nat.le_induction with
      | base => exact hD
      | succ t _ ih => exact (doomed_step (hB t) ih (hst t) (hND (t + 1))).1
    apply no_descent (fun t => pot p (e.cfg t)) t0
    · intro t ht; exact (doomed_step (hB t) (hall t ht) (hst t) (hND (t + 1))).2.1
    · intro N
      obtain ⟨m, hm, hl⟩ := hinf (max N t0)
      exact ⟨m, le_of_max_le_left hm,
        (doomed_step (hB m) (hall m (le_of_max_le_right hm)) (hst m) (hND (m + 1))).2.2 hl⟩
  -- progress of `p`
  have hpr := fun t => prog_step (p := p) (hS t) (hst t) (hND (t + 1))
  have hmono : ∀ a b, a ≤ b → prog p (e.cfg a) ≤ prog p (e.cfg b) := by
    intro a b hab
    induction b, hab using Nat.le_induction with
    | base => exact le_rfl
    | succ b _ ih => exact ih.trans (hpr b).1
  have hunb : ∀ V, ∃ t, V < prog p (e.cfg t) := by
    intro V
    by_contra hc
    push Not at hc
    apply no_descent (fun t => V - prog p (e.cfg t)) 0
    · intro t _; have := (hpr t).1; omega
    · intro N
      obtain ⟨m, hm, hl⟩ := hinf N
      refine ⟨m, hm, ?_⟩
      have h1 := (hpr m).2.1 hl
      have h2 := hc (m + 1)
      omega
  -- 3. finitely many writes to `A[1]` by other processes
  obtain ⟨T₁, hT₁⟩ : ∃ T₁, ((e.cfg T₁).mem 1).id ≠ none := by
    obtain ⟨t, ht⟩ := hunb 13
    have := prog_le p (e.cfg t)
    exact ⟨t, (hS t).mem1 p (by omega)⟩
  have hmem1 : ∀ t, T₁ ≤ t → ((e.cfg t).mem 1).id ≠ none := by
    intro t ht
    induction t, ht using Nat.le_induction with
    | base => exact hT₁
    | succ t _ ih => exact step_mem_id (hst t) 1 ih
  let XF : Finset P := (Finset.range T₁).image (fun m => (e.lbl m).proc)
  have hProv : ∀ t, PROV (XF : Set P) (e.cfg t) := by
    intro t
    induction t with
    | zero => rw [e.cfg_zero]; exact prov_init _
    | succ t ih =>
      refine prov_step (hS t) (hst t) (fun h0 => ?_) ih
      have : t < T₁ := by
        by_contra h'; exact hmem1 t (by omega) h0
      simp only [XF, Finset.coe_image, Finset.coe_range, Set.mem_image, Set.mem_Iio]
      exact ⟨t, this, rfl⟩
  have hIA : ∀ t, IA p (e.cfg t) := by
    intro t
    induction t with
    | zero => rw [e.cfg_zero]; exact ia_init p
    | succ t ih => exact ia_step (hB t) (hS t) (hNDm t) (hND t) (hst t) ih
  have hFW1 : ∀ t y, y ≠ p → e.lbl t = .tau y → ((e.cfg t).loc y).phase = .wr →
      ((e.cfg t).loc y).i = 1 → ((e.cfg t).loc y).seq = 1 ∧ y ∈ XF := by
    intro t y hyp hl hph hi
    have hpar := (hS t).i_par y
    rw [hi] at hpar
    have hodd : ((e.cfg t).loc y).seq % 2 = 1 := by rw [← hpar]; rfl
    have hseq : ((e.cfg t).loc y).seq = 1 := by
      by_contra hne
      exact ((hIA t) y hyp hodd (by omega)).2.2 hph
    refine ⟨hseq, ?_⟩
    have hc : (((e.cfg t).loc y).collect 1).id = none := by
      by_contra hne
      obtain ⟨w, hw⟩ := Option.ne_none_iff_exists'.1 hne
      have hw2 := (hS t).col_sub y 1 ((hS t).col_self y 1 w hw)
      have hwy : w = y := Finset.card_le_one.1 ((hS t).wr_card y hph) w hw2 y ((hB t).self y)
      subst hwy
      have hf := (hB t).fresh_col w 1 w hw
      have hp := (hS t).col_par w 1 w hw
      rw [hseq] at hf
      have h0 : (((e.cfg t).loc w).collect 1).seq = 0 := by omega
      rw [h0] at hp
      exact absurd hp (by decide)
    exact hProv t y (Or.inr hph) hseq hc
  let FW : Set ℕ := {t | ∃ y, y ≠ p ∧ e.lbl t = .tau y ∧ ((e.cfg t).loc y).phase = .wr ∧
    ((e.cfg t).loc y).i = 1}
  have hseq_mono : ∀ y a b, a ≤ b → ((e.cfg a).loc y).seq ≤ ((e.cfg b).loc y).seq := by
    intro y a b hab
    induction b, hab using Nat.le_induction with
    | base => exact le_rfl
    | succ b _ ih => exact ih.trans (step_seq_le (hst b) y)
  have key : ∀ y a b, a < b → e.lbl a = .tau y → ((e.cfg a).loc y).phase = .wr →
      ((e.cfg a).loc y).seq = 1 → ((e.cfg b).loc y).seq = 1 → False := by
    intro y a b hab hla hpa hsa hsb
    have h' := hst a
    rw [hla] at h'
    have h1 := step_write_seq h' hpa
    have h2 := hseq_mono y (a + 1) b hab
    omega
  have hFin : FW.Finite := by
    refine Set.Finite.of_injOn (f := fun t => (e.lbl t).proc) (t := (XF : Set P)) ?_ ?_
      XF.finite_toSet
    · rintro t ⟨y, hyp, hl, hph, hi⟩
      simp only [hl, Label.proc, Finset.mem_coe]
      exact (hFW1 t y hyp hl hph hi).2
    · rintro t ⟨y, hyp, hl, hph, hi⟩ t' ⟨y', hyp', hl', hph', hi'⟩ heq
      simp only [hl, hl', Label.proc] at heq
      subst heq
      by_contra hne
      rcases lt_or_gt_of_ne hne with h | h
      · exact key y t t' h hl hph (hFW1 t y hyp hl hph hi).1 (hFW1 t' y hyp' hl' hph' hi').1
      · exact key y t' t h hl' hph' (hFW1 t' y hyp' hl' hph' hi').1 (hFW1 t y hyp hl hph hi).1
  obtain ⟨B, hBd⟩ := hFin.bddAbove
  have hnoFW : ∀ t, B + 1 ≤ t → t ∉ FW := fun t ht hmem => by
    have := hBd hmem; omega
  -- 4. after the last such write, `p` outputs in its next odd iteration
  obtain ⟨sT, hsT⟩ : ∃ s, ((e.cfg (B + 1)).loc p).seq = s := ⟨_, rfl⟩
  have hQ : ∀ t, B + 1 ≤ t → QP p sT (e.cfg t) := by
    intro t ht
    induction t, ht using Nat.le_induction with
    | base => intro h; rw [hsT] at h; exact absurd h (lt_irrefl _)
    | succ t ht ih =>
      refine qp_step (hB t) (hS t) (hNDm t) (hND t) ?_ (hst t) ih
      intro y hl hyp hph hi
      exact hnoFW t ht ⟨y, hyp, hl, hph, hi⟩
  have hR : ∀ t, B + 1 ≤ t → prog p (e.cfg t) ≤ 5 * (2 * sT + 3) + 3 := by
    intro t ht
    induction t, ht using Nat.le_induction with
    | base => have := prog_le p (e.cfg (B + 1)); omega
    | succ t ht ih =>
      by_cases hl : e.lbl t = .tau p
      · have h1 := (hpr t).2.1 hl
        rcases Nat.lt_or_ge (prog p (e.cfg t)) (5 * (2 * sT + 3) + 3) with h2 | h2
        · omega
        · exfalso
          obtain ⟨hph, hj, hseq⟩ := prog_decode (show prog p (e.cfg t) = 5 * (2 * sT + 3) + 3 by
            omega)
          have hst' := hst t
          rw [hl] at hst'
          exact hND (t + 1) (qp_final (hB t) (hS t) (hNDm t) (hND t) (hQ t ht) (by omega)
            (by omega) (by omega) hph hj hst')
      · rcases (hpr t).2.2 hl with h1 | h1 <;> omega
  obtain ⟨t, ht⟩ := hunb (5 * (2 * sT + 3) + 3)
  have h1 := hmono t (max t (B + 1)) (le_max_left _ _)
  have h2 := hR (max t (B + 1)) (le_max_right _ _)
  omega

/-- **Algorithm 1 is wait-free for `k = 1`**, for any set of processes (finite or infinite). -/
theorem alg1_waitFree_one {P : Type} [DecidableEq P] : (alg1 (P := P) 1).WaitFree :=
  fun e p _ _ => alg1_one_finite_steps e p

end Cslib.SharedMemory.StrangerFree
