import Papers.PODC2026.ContentObliviousCounting.AnonCountingProbe

/-!
# Anonymous counting: steps of the leadership-transfer stage

Every enabled delivery in the transfer stage `xfer j x y` leads to another stage (the next transfer
configuration, or the first probe of phase `j + 1`).
-/

namespace Podc.ContentOblivious.AnonCounting

open Cslib.ContentOblivious Finset

set_option linter.unusedSectionVars false
set_option linter.deprecated false

lemma relF_succ' (j p : ℕ) : relF (j + 1) (tri j + j) p = relF j (tri j + j) p := relF_succ j p
lemma mphF_succ' (j p : ℕ) : mphF (j + 1) (tri j + j) p = mphF j (tri j + j) p := mphF_succ j p

lemma xfer_en {n j x y q : ℕ} {b : Bool} (h : (absXfer n j x y).En n q b) :
    (b = true ∧ x ≤ n ∧ (if q = tri j then n else ccwD n (tri j) q) = x) ∨
    (b = false ∧ 1 ≤ y ∧ (if q = tri (j + 1) then n else cwD n (tri (j + 1)) q) = y) := by
  obtain ⟨-, h, -⟩ := h
  simp only [absXfer] at h
  cases b
  · right; refine ⟨rfl, ?_⟩
    by_contra hc
    simp only [Bool.false_eq_true, ite_false, if_neg hc] at h
    simp at h
  · left; refine ⟨rfl, ?_⟩
    by_contra hc
    simp only [ite_true, if_neg hc] at h
    simp at h

/-- The new leader is the only node satisfying the condition of line 14 of Algorithm 1. -/
lemma not_lead_cond {j p : ℕ} (hj : 1 ≤ j) (hp : p ≠ tri j + j) :
    ¬ (mphF j (tri j + j) p = some j ∧ relF j (tri j + j) p + 0 = 0) := by
  rintro ⟨h1, h2⟩
  by_cases h0 : p = 0
  · simp [mphF_zero' h0] at h1
  by_cases ha : p ≤ tri j
  · rw [mphF_le (by omega) ha] at h1
    have := phaseOf_lt (by omega) ha
    simp at h1; omega
  by_cases hb : p ≤ tri j + j
  · rw [relF_mid (by omega) hb] at h2; omega
  · rw [mphF_gt (by omega) (by omega)] at h1; simp at h1

/-- Region split used in the agreement proofs of the transfer stage. -/
macro "ac_xregions" p:term "," L:term "," R:term : tactic => `(tactic|
  (rcases Nat.lt_or_ge $L $p with _ | _ <;> rcases Nat.lt_or_ge $p $R with _ | _ <;>
    (try simp (disch := omega) only [ccwD_le, ccwD_gt, cwD_ge, cwD_lt] at *) <;>
    (try (exfalso; omega))))

lemma xfer_tL {n j y : ℕ} (hok : (Stage.xfer j n y).Ok n) :
    ∃ s' : Stage, s'.Ok n ∧ Agree n ((Stage.abs n (.xfer j n y)).step n (tri j) true) (s'.abs n) := by
  obtain ⟨hj, hR, hx1, hxn, hyn, hy1, hy2⟩ := hok
  simp only [tri_succ] at hR
  have hq : (Stage.abs n (.xfer j n y)).st (tri j) = lst .tr1 j j (tri j + j) (tri j) j := by
    simp only [Stage.abs, absXfer, tri_succ, ite_true, le_refl]
  refine ⟨.xfer j (n + 1) y, ⟨hj, by simp only [tri_succ]; omega, by omega, le_rfl, hyn,
    by omega, fun _ => rfl⟩, ?_⟩
  refine agree_of (by rw [hq, recv_tr1]) ?_ ?_ ?_ ?_
  · intro p hp hpq
    simp only [Stage.abs, absXfer, tri_succ]
    ac_xregions p, tri j, tri j + j
    all_goals split_ifs <;> ac_st_close
  · simp only [Stage.abs, absXfer, tri_succ, ite_true]
    split_ifs <;> ac_st_close
  · intro p hp b
    cases b
    · simp [Stage.abs, absXfer]
    · simp only [Stage.abs, absXfer, tri_succ, nxt, prv, out_true, out_false]
      simp only [Bool.true_eq_false, false_and, ite_false, and_true, true_and, ite_true, add_zero]
      ac_xregions p, tri j, tri j + j
      all_goals split_ifs <;> omega
  · simp only [Stage.abs, absXfer, out_false, out_true]
    rw [min_eq_left le_rfl, min_eq_right (by omega)]; omega

lemma xfer_tR {n j x : ℕ} (hok : (Stage.xfer j x 0).Ok n) (hx : x ≤ n)
    (hqx : ccwD n (tri j) (tri j + j) = x) :
    ∃ s' : Stage, s'.Ok n ∧
      Agree n ((Stage.abs n (.xfer j x 0)).step n (tri j + j) true) (s'.abs n) := by
  obtain ⟨hj, hR, hx1, hxn, hyn, hy1, hy2⟩ := hok
  simp only [tri_succ] at hR
  rw [ccwD_gt (by omega)] at hqx
  have hq : (Stage.abs n (.xfer j x 0)).st (tri j + j) = nst .main j j (tri j + j) (tri j + j) 0 := by
    simp only [Stage.abs, absXfer, tri_succ]
    simp (disch := omega) only [if_pos, if_neg, ite_true]
  have hlc : mphF j (tri j + j) (tri j + j) = some j ∧ relF j (tri j + j) (tri j + j) + 0 = 0 := by
    rw [mphF_mid (by omega) le_rfl, relF_mid (by omega) le_rfl]; simp
  refine ⟨.xfer j (x + 1) 1, ⟨hj, by simp only [tri_succ]; omega, by omega, by omega, by omega,
    by omega, by omega⟩, ?_⟩
  refine agree_of (by rw [hq, recv_main_lead hlc]) ?_ ?_ ?_ ?_
  · intro p hp hpq
    simp only [Stage.abs, absXfer, tri_succ]
    ac_xregions p, tri j, tri j + j
    all_goals split_ifs <;> ac_st_close
  · simp only [Stage.abs, absXfer, tri_succ]
    split_ifs <;> ac_st_close
  · intro p hp b
    cases b
    · simp only [Stage.abs, absXfer, tri_succ, nxt, prv, out_true, out_false]
      simp only [Bool.false_eq_true, false_and, ite_false, and_false, true_and, and_true, add_zero]
      ac_xregions p, tri j, tri j + j
      all_goals split_ifs <;> omega
    · simp only [Stage.abs, absXfer, tri_succ, nxt, prv, out_true, out_false]
      simp only [Bool.true_eq_false, false_and, ite_false, and_true, true_and, ite_true, add_zero]
      ac_xregions p, tri j, tri j + j
      all_goals split_ifs <;> omega
  · simp only [Stage.abs, absXfer, out_false, out_true]
    rw [min_eq_left (by omega), min_eq_left (by omega)]; omega

lemma xfer_tM {n j x y q : ℕ} (hok : (Stage.xfer j x y).Ok n) (hqn : q < n) (hx : x ≤ n)
    (hqL : q ≠ tri j) (hqR : q ≠ tri j + j) (hqx : ccwD n (tri j) q = x) :
    ∃ s' : Stage, s'.Ok n ∧ Agree n ((Stage.abs n (.xfer j x y)).step n q true) (s'.abs n) := by
  obtain ⟨hj, hR, hx1, hxn, hyn, hy1, hy2⟩ := hok
  simp only [tri_succ] at hR
  have hq : (Stage.abs n (.xfer j x y)).st q = nst .main j j (tri j + j) q 0 := by
    simp only [Stage.abs, absXfer, tri_succ]
    rcases Nat.lt_or_ge (tri j) q with h | h <;>
      simp (disch := omega) only [ccwD_gt, ccwD_le] at hqx ⊢ <;>
      simp (disch := omega) only [if_pos, if_neg]
  have hxq : x < n ∧ (x < n - j ∨ n - j < x) := by
    rcases Nat.lt_or_ge (tri j) q with h | h
    · rw [ccwD_gt h] at hqx; omega
    · rw [ccwD_le h] at hqx; omega
  refine ⟨.xfer j (x + 1) y, ⟨hj, by simp only [tri_succ]; omega, by omega, by omega, hyn,
    by omega, by omega⟩, ?_⟩
  refine agree_of (by rw [hq, recv_main_wait (not_lead_cond hj hqR)]) ?_ ?_ ?_ ?_
  · intro p hp hpq
    simp only [Stage.abs, absXfer, tri_succ]
    rcases Nat.lt_or_ge (tri j) q with _ | _ <;>
    ac_xregions p, tri j, tri j + j
    all_goals split_ifs <;> ac_st_close
  · simp only [Stage.abs, absXfer, tri_succ]
    ac_xregions q, tri j, tri j + j
    all_goals split_ifs <;> ac_st_close
  · intro p hp b
    cases b
    · simp [Stage.abs, absXfer]
    · simp only [Stage.abs, absXfer, tri_succ, nxt, prv, out_true, out_false]
      simp only [Bool.true_eq_false, false_and, ite_false, and_true, true_and, ite_true, add_zero]
      rcases Nat.lt_or_ge (tri j) q with _ | _ <;>
      ac_xregions p, tri j, tri j + j
      all_goals split_ifs <;> omega
  · simp only [Stage.abs, absXfer, out_false, out_true]
    rw [min_eq_left (by omega), min_eq_left (by omega)]; omega

lemma xfer_cL {n j x y : ℕ} (hok : (Stage.xfer j x y).Ok n) (hy : 1 ≤ y)
    (hqy : cwD n (tri j + j) (tri j) = y)
    (hrd : ready ((Stage.abs n (.xfer j x y)).st (tri j)) false = true) :
    ∃ s' : Stage, s'.Ok n ∧ Agree n ((Stage.abs n (.xfer j x y)).step n (tri j) false) (s'.abs n) := by
  obtain ⟨hj, hR, hx1, hxn, hyn, hy1, hy2⟩ := hok
  simp only [tri_succ] at hR
  rw [cwD_lt (by omega)] at hqy
  have hx : x = n + 1 := by
    by_contra hc
    simp only [Stage.abs, absXfer, ite_true, show x ≤ n by omega] at hrd
    simp [lst, nst, ready] at hrd
  subst hx
  have hq : (Stage.abs n (.xfer j (n + 1) y)).st (tri j) = lst .tr2 j j (tri j + j) (tri j) j := by
    simp only [Stage.abs, absXfer, tri_succ, ite_true]
    simp (disch := omega) only [if_pos, if_neg]
  refine ⟨.xfer j (n + 1) (y + 1), ⟨hj, by simp only [tri_succ]; omega, by omega, le_rfl, by omega,
    by omega, fun _ => rfl⟩, ?_⟩
  refine agree_of (by rw [hq, recv_tr2 false (by omega)]) ?_ ?_ ?_ ?_
  · intro p hp hpq
    simp only [Stage.abs, absXfer, tri_succ]
    ac_xregions p, tri j, tri j + j
    all_goals split_ifs <;> ac_st_close
  · simp only [Stage.abs, absXfer, tri_succ, ite_true]
    split_ifs <;> ac_st_close
  · intro p hp b
    cases b
    · simp only [Stage.abs, absXfer, tri_succ, nxt, prv, out_true, out_false]
      simp only [Bool.false_eq_true, false_and, ite_false, and_false, true_and, and_true, add_zero]
      ac_xregions p, tri j, tri j + j
      all_goals split_ifs <;> omega
    · simp [Stage.abs, absXfer]
  · simp only [Stage.abs, absXfer, out_false, out_true]; omega

set_option maxHeartbeats 1000000 in
lemma xfer_cM {n j x y q : ℕ} (hok : (Stage.xfer j x y).Ok n) (hqn : q < n) (hy : 1 ≤ y)
    (hqL : q ≠ tri j) (hqR : q ≠ tri j + j) (hqy : cwD n (tri j + j) q = y) :
    ∃ s' : Stage, s'.Ok n ∧ Agree n ((Stage.abs n (.xfer j x y)).step n q false) (s'.abs n) := by
  obtain ⟨hj, hR, hx1, hxn, hyn, hy1, hy2⟩ := hok
  simp only [tri_succ] at hR
  have hq : (Stage.abs n (.xfer j x y)).st q = nst .wait2 j j (tri j + j) q 0 := by
    simp only [Stage.abs, absXfer, tri_succ]
    ac_xregions q, tri j, tri j + j
    all_goals simp (disch := omega) only [if_pos, if_neg]
  have hyq : y < n ∧ y ≠ n - j := by
    ac_xregions q, tri j, tri j + j
    all_goals omega
  have key : ∀ p < n, p ≠ q → p ≠ tri j + j → cwD n (tri j + j) p ≠ y := by
    intro p hp hpq hpR h
    apply hpq
    ac_xregions p, tri j, tri j + j
    all_goals ac_xregions q, tri j, tri j + j
    all_goals omega
  refine ⟨.xfer j x (y + 1), ⟨hj, by simp only [tri_succ]; omega, hx1, hxn, by omega,
    by omega, by omega⟩, ?_⟩
  refine agree_of (by rw [hq, recv_wait_false]) ?_ ?_ ?_ ?_
  · intro p hp hpq
    have k := key p hp hpq
    simp only [Stage.abs, absXfer, tri_succ]
    ac_xregions p, tri j, tri j + j
    all_goals split_ifs <;> ac_st_close
  · simp only [Stage.abs, absXfer, tri_succ]
    ac_xregions q, tri j, tri j + j
    all_goals split_ifs <;> ac_st_close
  · intro p hp b
    cases b
    · by_cases hpq : p = q
      · subst hpq
        simp only [Stage.abs, absXfer, tri_succ, nxt, prv, out_true, out_false]
        simp only [Bool.false_eq_true, false_and, ite_false, and_false, true_and, and_true,
          add_zero]
        ac_xregions p, tri j, tri j + j
        all_goals split_ifs <;> omega
      have k := key p hp hpq
      simp only [Stage.abs, absXfer, tri_succ, nxt, prv, out_true, out_false]
      simp only [Bool.false_eq_true, false_and, ite_false, and_false, true_and, and_true, add_zero]
      ac_xregions p, tri j, tri j + j
      all_goals ac_xregions q, tri j, tri j + j
      all_goals split_ifs <;> omega
    · simp [Stage.abs, absXfer]
  · simp only [Stage.abs, absXfer, out_false, out_true]; omega

lemma phasesCost_succ {n j : ℕ} (hj : 1 ≤ j) :
    phasesCost n (j + 1) = phasesCost n j + j * (j + 1) + 2 * n := by
  simp [phasesCost, show j ≠ 0 by omega, add_assoc]

lemma xfer_cR {n j x : ℕ} (hok : (Stage.xfer j x n).Ok n)
    (hrd : ready ((Stage.abs n (.xfer j x n)).st (tri j + j)) false = true) :
    ∃ s' : Stage, s'.Ok n ∧
      Agree n ((Stage.abs n (.xfer j x n)).step n (tri j + j) false) (s'.abs n) := by
  obtain ⟨hj, hR, hx1, hxn, hyn, hy1, hy2⟩ := hok
  simp only [tri_succ] at hR
  have hx : x = n + 1 := hy2 (by omega)
  subst hx
  have hq : (Stage.abs n (.xfer j (n + 1) n)).st (tri j + j) =
      nst .newLeader j j (tri j + j) (tri j + j) 0 := by
    simp only [Stage.abs, absXfer, tri_succ]
    simp (disch := omega) only [if_pos, if_neg, ite_true]
  have hpc := phasesCost_succ (n := n) hj
  by_cases hlast : tri j + j + 1 < n
  · refine ⟨.out (j + 1) 1 1, ⟨by omega, le_rfl, by omega, by simp only [tri_succ]; omega, le_rfl,
      le_rfl⟩, ?_⟩
    refine agree_of (by rw [hq, recv_newLeader]) ?_ ?_ ?_ ?_
    · intro p hp hpq
      simp only [Stage.abs, absXfer, absOut, tri_succ, Nat.add_sub_cancel]
      ac_xregions p, tri j, tri j + j
      all_goals split_ifs <;>
        (try simp only [nst_eq_iff, lst_eq_iff, relF_succ', mphF_succ', true_and, and_true]) <;>
        ac_st_close
    · simp only [Stage.abs, absOut, tri_succ, Nat.add_sub_cancel, ite_true]
      simp only [lst_eq_iff, relF_succ', mphF_succ']
      simp
    · intro p hp b
      cases b
      · simp only [Stage.abs, absXfer, absOut, tri_succ, nxt, prv, out_true, out_false]
        simp only [Bool.false_eq_true, false_and, ite_false, and_false, true_and, and_true,
          add_zero]
        ac_xregions p, tri j, tri j + j
        all_goals split_ifs <;> omega
      · simp [Stage.abs, absXfer, absOut]
    · simp only [Stage.abs, absXfer, absOut, out_false, out_true, hpc]
      rw [min_eq_right (by omega)]; omega
  · have hI : lastPhase n = j + 1 :=
      lastPhase_eq (by simp only [tri_succ]; omega) (by simp only [tri_succ]; omega)
    have hL : lead n = tri j + j := by simp [lead, hI]
    have hC : lastCount n = 0 := by simp [lastCount, hI]; omega
    have hn1 : n - 1 = tri j + j := by omega
    refine ⟨.pipe .comp (fun _ => 0) 0, ⟨trivial, by simp [Kind.K], fun p _ _ => by simp [Kind.K],
      by simp⟩, ?_⟩
    refine agree_of (by rw [hq, recv_newLeader]) ?_ ?_ ?_ ?_
    · intro p hp hpq
      simp only [Stage.abs, absXfer, absPipe, hL, Kind.f, hI, hn1, ite_true, tri_succ]
      ac_xregions p, tri j, tri j + j
      all_goals split_ifs <;>
        (try simp only [nst_eq_iff, lst_eq_iff, relF_succ', mphF_succ', true_and, and_true]) <;>
        ac_st_close
    · simp only [Stage.abs, absPipe, hL, ite_true, Kind.g, gst_nil, hI, hC, hn1]
      simp only [lst_eq_iff, relF_succ', mphF_succ']
      simp
    · intro p hp b
      cases b
      · simp only [Stage.abs, absXfer, absPipe, pipeTr, src, Kind.K, Kind.cw, hL, nxt, prv,
          out_true, out_false, tri_succ]
        simp only [Bool.false_eq_true, false_and, ite_false, and_false, true_and, and_true,
          add_zero, Bool.not_true, ite_true]
        ac_xregions p, tri j, tri j + j
        all_goals split_ifs <;> omega
      · simp [Stage.abs, absXfer, absPipe, pipeTr, Kind.cw]
    · simp only [Stage.abs, absXfer, absPipe, Kind.base, lastBase, hI, hC, out_false, out_true,
        Finset.sum_const_zero, hpc]
      rw [min_eq_right (by omega)]; omega

theorem stepOk_xfer {n j x y : ℕ} (hok : (Stage.xfer j x y).Ok n) : StepOk n (.xfer j x y) := by
  intro q b hen
  have hqn : q < n := hen.1
  have hen' := xfer_en hen
  simp only [tri_succ] at hen'
  rcases hen' with ⟨rfl, hx, hqx⟩ | ⟨rfl, hy, hqy⟩
  · by_cases hqL : q = tri j
    · subst hqL
      simp only [ite_true] at hqx
      subst hqx
      exact xfer_tL hok
    simp only [hqL, ite_false] at hqx
    by_cases hqR : q = tri j + j
    · subst hqR
      have hy0 : y = 0 := by
        obtain ⟨hj, hR, -, -, -, hy1, -⟩ := hok
        simp only [tri_succ] at hR
        rw [ccwD_gt (by omega)] at hqx; omega
      subst hy0
      exact xfer_tR hok hx hqx
    · exact xfer_tM hok hqn hx hqL hqR hqx
  · by_cases hqR : q = tri j + j
    · subst hqR
      simp only [ite_true] at hqy
      subst hqy
      exact xfer_cR hok hen.2.2.1
    simp only [hqR, ite_false] at hqy
    by_cases hqL : q = tri j
    · subst hqL
      exact xfer_cL hok hy hqy hen.2.2.1
    · exact xfer_cM hok hqn hy hqL hqR hqy

end Podc.ContentOblivious.AnonCounting
