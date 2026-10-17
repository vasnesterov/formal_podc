import Papers.PODC2026.ContentObliviousCounting.AnonCountingStages

/-!
# Anonymous counting: steps of the probing stages

Every enabled delivery in a probing stage (`out`, `back`) leads to another stage.
-/

namespace Podc.ContentOblivious.AnonCounting

open Cslib.ContentOblivious Finset

set_option linter.unusedSectionVars false
set_option linter.deprecated false

/-! ## Reactions of canonical states -/

lemma recv_main_cnt {ph j F p x : ℕ} (h : p ≤ F) :
    recv (nst .main ph j F p x) false = (nst .relay ph j F p (x + 1), out 0 1) := by
  simp [recv, nst, h, add_assoc]

lemma recv_main_new {ph j F p x : ℕ} (h : F < p) :
    recv (nst .main ph j F p x) false =
      ({ nst .main ph j F p x with counted := true, myPhase := some ph }, out 1 0) := by
  simp [recv, nst, show ¬ p ≤ F by omega]

lemma recv_main_lead {ph j F p x : ℕ} (h : mphF j F p = some ph ∧ relF j F p + x = 0) :
    recv (nst .main ph j F p x) true = (nst .newLeader ph j F p x, out 1 1) := by
  simp [recv, nst, h]

lemma recv_main_wait {ph j F p x : ℕ} (h : ¬ (mphF j F p = some ph ∧ relF j F p + x = 0)) :
    recv (nst .main ph j F p x) true = (nst .wait2 ph j F p x, out 1 0) := by
  simp only [recv, nst]
  exact if_neg h

lemma recv_relay {ph j F p x : ℕ} (q : Bool) :
    recv (nst .relay ph j F p x) q = (nst .main ph j F p x, out 1 0) := by
  simp [recv, nst]

lemma recv_newLeader {ph j F p : ℕ} (q : Bool) :
    recv (nst .newLeader ph j F p 0) q = (lst .probe (ph + 1) j F p 0, out 0 1) := by
  simp [recv, nst, lst]

lemma recv_wait_false {ph j F p x : ℕ} :
    recv (nst .wait2 ph j F p x) false = (nst .main (ph + 1) j F p x, out 0 1) := by
  simp [recv, nst]

lemma recv_wait_true {ph j F p x : ℕ} :
    recv (nst .wait2 ph j F p x) true = (nst .rcvQ ph j F p x, out 1 0) := by
  simp [recv, nst]

lemma recv_probe_tr {ph j F p c : ℕ} (h : c + 1 = ph) :
    recv (lst .probe ph j F p c) true = (lst .tr1 ph j F p (c + 1), out 1 0) := by
  simp [recv, lst, nst, h]

lemma recv_probe_next {ph j F p c : ℕ} (h : c + 1 ≠ ph) :
    recv (lst .probe ph j F p c) true = (lst .probe ph j F p (c + 1), out 0 1) := by
  simp [recv, lst, nst, h]

lemma recv_probe_fin {ph j F p c : ℕ} :
    recv (lst .probe ph j F p c) false = (lst (.fin 0) ph j F p c, out 3 0) := by
  simp [recv, lst, nst]

lemma recv_tr1 {ph j F p c : ℕ} (q : Bool) :
    recv (lst .tr1 ph j F p c) q = (lst .tr2 ph j F p c, out 0 0) := by
  simp [recv, lst, nst]

lemma recv_tr2 {j F : ℕ} (q : Bool) (h : tri j ≤ F) :
    recv (lst .tr2 j j F (tri j) j) q = (nst .main (j + 1) j F (tri j) 0, out 0 1) := by
  simp [recv, lst, nst, relF_lead, h]

/-! ## A helper for agreement proofs -/

lemma agree_of {n : ℕ} {A B : Abs} {q : ℕ} {j : Bool} {s : St} {o : Bool → ℕ}
    (hrecv : recv (A.st q) j = (s, o))
    (hst : ∀ p < n, p ≠ q → A.st p = B.st p) (hsq : s = B.st q)
    (htr : ∀ p < n, ∀ b, A.tr p b - (if p = q ∧ b = j then 1 else 0) +
      (if b = false ∧ p = nxt n q then o true else 0) +
      (if b = true ∧ p = prv n q then o false else 0) = B.tr p b)
    (htot : A.tot + o false + o true = B.tot) : Agree n (A.step n q j) B := by
  refine ⟨fun p hp => ?_, fun p hp b => ?_, ?_⟩
  · simp only [Abs.step, hrecv]
    split_ifs with h
    · subst h; exact hsq
    · exact hst p hp h
  · simp only [Abs.step, hrecv]; exact htr p hp b
  · simp only [Abs.step, hrecv]; exact htot

/-- Closing tactic for equalities of canonical states. -/
macro "ac_st_close" : tactic => `(tactic| first
  | rfl
  | (exfalso; omega)
  | (simp (disch := omega) only [nst_eq_iff, lst_eq_iff, relF_le0, relF_mid, relF_gt,
      mphF_le0, mphF_mid, mphF_gt, true_and, and_true, Option.some.injEq, reduceCtorEq]
     try (first | omega | (split_ifs <;> omega))))

/-! ## The `out` stage -/

lemma out_en {n j m t q : ℕ} {b : Bool} (h : (absOut n j m t).En n q b) :
    q = tri j + t ∧ b = false := by
  obtain ⟨-, h, -⟩ := h
  simp only [absOut] at h
  split_ifs at h with h1
  · exact h1
  · simp at h

theorem stepOk_out {n j m t : ℕ} (hok : (Stage.out j m t).Ok n) : StepOk n (.out j m t) := by
  intro q b hen
  obtain ⟨rfl, rfl⟩ := out_en hen
  obtain ⟨hj, hm1, hmj, hmn, ht1, htm⟩ := hok
  have hq : (Stage.abs n (.out j m t)).st (tri j + t) =
      nst .main j j (tri j + m - 1) (tri j + t) 0 := by
    simp only [Stage.abs, absOut]; rw [if_neg (by omega), if_neg (by omega)]
  by_cases ht : t < m
  · refine ⟨.out j m (t + 1), ⟨hj, hm1, hmj, hmn, by omega, by omega⟩, ?_⟩
    refine agree_of (by rw [hq, recv_main_cnt (by omega)]) ?_ ?_ ?_ ?_
    · intro p hp hpq
      simp only [Stage.abs, absOut]
      rcases Nat.lt_or_ge (tri j) p with hreg | hreg <;> split_ifs <;> ac_st_close
    · simp only [Stage.abs, absOut]
      split_ifs <;> ac_st_close
    · intro p hp b
      simp only [Stage.abs, absOut, nxt, prv]
      cases b <;> (try simp) <;> split_ifs <;> omega
    · simp only [Stage.abs, absOut, out_false, out_true]; omega
  · refine ⟨.back j m (m - 1), ⟨hj, hm1, hmj, hmn, by omega⟩, ?_⟩
    refine agree_of (by rw [hq, recv_main_new (by omega)]) ?_ ?_ ?_ ?_
    · intro p hp hpq
      simp only [Stage.abs, absOut, absBack]
      rcases Nat.lt_or_ge (tri j) p with hreg | hreg <;> split_ifs <;> ac_st_close
    · simp only [Stage.abs, absBack]
      rw [if_neg (by omega), if_neg (by omega)]
      simp (disch := omega) only [nst, relF_mid, relF_gt, mphF_mid, St.mk.injEq]
      simp; omega
    · intro p hp b
      simp only [Stage.abs, absOut, absBack, nxt, prv]
      cases b <;> simp <;> split_ifs <;> try omega
    · simp only [Stage.abs, absOut, absBack, out_false, out_true]; omega

/-! ## The `back` stage -/

lemma mul_pred_add (m : ℕ) : m * (m - 1) + 2 * m = m * (m + 1) := by
  rcases m with _ | m
  · rfl
  · simp only [Nat.add_sub_cancel]; ring

lemma lastPhase_eq {n j : ℕ} (h1 : tri j < n) (h2 : n ≤ tri (j + 1)) : lastPhase n = j :=
  phaseOf_eq h1 h2

lemma back_en {n j m t q : ℕ} {b : Bool} (h : (absBack n j m t).En n q b) :
    q = tri j + t ∧ b = true := by
  obtain ⟨-, h, -⟩ := h
  simp only [absBack] at h
  split_ifs at h with h1
  · exact h1
  · simp at h

theorem stepOk_back {n j m t : ℕ} (hok : (Stage.back j m t).Ok n) : StepOk n (.back j m t) := by
  intro q b hen
  obtain ⟨rfl, rfl⟩ := back_en hen
  obtain ⟨hj, hm1, hmj, hmn, htm⟩ := hok
  by_cases ht : 1 ≤ t
  · -- relaying the probe back
    have hq : (Stage.abs n (.back j m t)).st (tri j + t) = nst .relay j j (tri j + m) (tri j + t) 0 := by
      simp only [Stage.abs, absBack]; rw [if_neg (by omega), if_pos (by omega)]
    refine ⟨.back j m (t - 1), ⟨hj, hm1, hmj, hmn, by omega⟩, ?_⟩
    refine agree_of (by rw [hq, recv_relay]) ?_ ?_ ?_ ?_
    · intro p hp hpq
      simp only [Stage.abs, absBack]
      rcases Nat.lt_or_ge (tri j) p with hreg | hreg <;> split_ifs <;> ac_st_close
    · simp only [Stage.abs, absBack]
      split_ifs <;> ac_st_close
    · intro p hp b
      simp only [Stage.abs, absBack, nxt, prv]
      cases b <;> (try simp) <;> split_ifs <;> omega
    · simp only [Stage.abs, absBack, out_false, out_true]; omega
  have ht0 : t = 0 := by omega
  subst ht0
  simp only [Nat.add_zero]
  have hq : (Stage.abs n (.back j m 0)).st (tri j) = lst .probe j j (tri j + m) (tri j) (m - 1) := by
    simp only [Stage.abs, absBack, ite_true]
  by_cases hmj' : m = j
  · -- end of the probing part of phase `j`: start the transfer
    subst hmj'
    refine ⟨.xfer m 1 0, ⟨hj, by simp only [tri_succ]; omega, le_rfl, by omega, by omega,
      by omega, by omega⟩, ?_⟩
    refine agree_of (by rw [hq, recv_probe_tr (by omega)]) ?_ ?_ ?_ ?_
    · intro p hp hpq
      simp only [Stage.abs, absBack, absXfer, tri_succ]
      rcases Nat.lt_or_ge (tri m) p with hreg | hreg <;>
        rcases Nat.lt_or_ge p (tri m + m) with hreg' | hreg' <;>
        (try simp (disch := omega) only [ccwD_le, ccwD_gt, cwD_ge, cwD_lt]) <;> split_ifs <;> ac_st_close
    · simp only [Stage.abs, absXfer, tri_succ]
      split_ifs <;> ac_st_close
    · intro p hp b
      simp only [Stage.abs, absBack, absXfer, nxt, prv, tri_succ]
      rcases Nat.lt_or_ge (tri m) p with hreg | hreg <;>
        (try simp (disch := omega) only [ccwD_le, ccwD_gt]) <;>
        cases b <;> (try simp) <;> split_ifs <;> omega
    · simp only [Stage.abs, absBack, absXfer, out_false, out_true]
      have := mul_pred_add m
      rw [min_eq_left (by omega)]; omega
  by_cases hlast : tri j + m + 1 < n
  · -- next probe
    refine ⟨.out j (m + 1) 1, ⟨hj, by omega, by omega, by omega, le_rfl, by omega⟩, ?_⟩
    refine agree_of (by rw [hq, recv_probe_next (by omega)]) ?_ ?_ ?_ ?_
    · intro p hp hpq
      simp only [Stage.abs, absBack, absOut]
      rcases Nat.lt_or_ge (tri j) p with hreg | hreg <;> split_ifs <;> ac_st_close
    · simp only [Stage.abs, absOut]
      split_ifs <;> ac_st_close
    · intro p hp b
      simp only [Stage.abs, absBack, absOut, nxt, prv]
      cases b <;> (try simp) <;> split_ifs <;> omega
    · simp only [Stage.abs, absBack, absOut, out_false, out_true]
      have := mul_pred_add m
      have : (m + 1) * (m + 1 - 1) = m * (m + 1) := by simp [mul_comm]
      omega
  · -- every node has been probed: the completion probe of the last phase
    have hI : lastPhase n = j := lastPhase_eq (by omega) (by simp only [tri_succ]; omega)
    have hL : lead n = tri j := by simp [lead, hI]
    have hC : lastCount n = m := by simp [lastCount, hI]; omega
    refine ⟨.pipe .comp (fun _ => 0) 0, ⟨trivial, by simp [Kind.K], fun p _ _ => by simp [Kind.K],
      by simp⟩, ?_⟩
    refine agree_of (by rw [hq, recv_probe_next (by omega)]) ?_ ?_ ?_ ?_
    · intro p hp hpq
      simp only [Stage.abs, absBack, absPipe, hL, Kind.f, hI, ite_true]
      rcases Nat.lt_or_ge (tri j) p with hreg | hreg <;> split_ifs <;> ac_st_close
    · simp only [Stage.abs, absPipe, hL, ite_true, Kind.g, gst_nil, hI, hC]
      ac_st_close
    · intro p hp b
      simp only [Stage.abs, absBack, absPipe, pipeTr, src, Kind.K, Kind.cw, hL, nxt, prv]
      cases b <;> (try simp) <;> split_ifs <;> omega
    · simp only [Stage.abs, absBack, absPipe, Kind.base, lastBase, hI, hC, out_false, out_true,
        Finset.sum_const_zero]
      have := mul_pred_add m
      omega

end Podc.ContentOblivious.AnonCounting
