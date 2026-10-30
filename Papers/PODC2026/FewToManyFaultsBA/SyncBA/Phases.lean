import Papers.PODC2026.FewToManyFaultsBA.SyncBA.Run

/-!
# Phase-by-phase behaviour of the local algorithm

Field-wise descriptions of `viewTrans`, `trans` and `out` at each phase of a view and in the
rounds after the views.
-/

namespace Podc.FewToManyFaultsBA.Sync

open Cslib.Byzantine.LockStep Finset

variable {n : ℕ} [NeZero n] (π : Params n)

/-! ### Round arithmetic -/

lemma view_lt_Rh {v j : ℕ} (hv : v < n) (hj : j < 11) : 11 * v + j < Rh n := by
  unfold Rh; omega

lemma view_div {v j : ℕ} (hj : j < 11) : (11 * v + j) / 11 = v := by omega

lemma view_mod {v j : ℕ} (hj : j < 11) : (11 * v + j) % 11 = j := by omega

lemma leader_of_lt {v : ℕ} (hv : v < n) : (leader v : Fin n) = ⟨v, hv⟩ := by
  simp [leader, Nat.mod_eq_of_lt hv]

lemma leader_injOn {v w : ℕ} (hv : v < n) (hw : w < n) (h : (leader v : Fin n) = leader w) :
    v = w := by
  rw [leader_of_lt hv, leader_of_lt hw] at h
  exact congrArg Fin.val h

/-! ### `trans` in the view rounds -/

variable {π}

lemma trans_view (p : Fin n) (st : St n) {v j : ℕ} (hv : v < n) (hj : j < 11)
    (ib : Fin n → Option (Msg n)) :
    trans π p st (11 * v + j) ib =
      { viewTrans π p st v j ib with
        commit := (viewTrans π p st v j ib).commit.or (inboxCommit π.k ib)
        last := ib } := by
  have h1 := view_lt_Rh (n := n) hv hj
  have h2 : 11 * v + j < R0 n := by unfold R0; unfold Rh at h1; omega
  simp only [trans, h1, h2, ite_true, view_div hj, view_mod hj]

lemma trans_ge_R0 (p : Fin n) (st : St n) {r : ℕ} (hr : R0 n ≤ r)
    (ib : Fin n → Option (Msg n)) : trans π p st r ib = { st with last := ib } := by
  have h1 : ¬ r < Rh n := by unfold R0 at hr; unfold Rh; omega
  have h2 : r ≠ Rh n + 1 := by unfold R0 at hr; unfold Rh; omega
  simp only [trans, h1, h2, ite_false, not_lt.2 hr]

lemma trans_Rh (p : Fin n) (st : St n) (ib : Fin n → Option (Msg n)) :
    trans π p st (Rh n) ib = { st with commit := st.commit.or (inboxCommit π.k ib), last := ib } := by
  have h2 : Rh n < R0 n := by unfold R0 Rh; omega
  simp [trans, h2]

lemma trans_Rh1 (p : Fin n) (st : St n) (ib : Fin n → Option (Msg n)) :
    trans π p st (Rh n + 1) ib = { st with
      fb := (ownFb π.t st.last).or (inboxFb π.t ib)
      commit := st.commit.or (inboxCommit π.k ib), last := ib } := by
  have h2 : Rh n + 1 < R0 n := by unfold R0 Rh; omega
  simp [trans, h2]

lemma trans_Rh2 (p : Fin n) (st : St n) (ib : Fin n → Option (Msg n)) :
    trans π p st (Rh n + 2) ib = { st with commit := st.commit.or (inboxCommit π.k ib), last := ib } := by
  have h2 : Rh n + 2 < R0 n := by unfold R0 Rh; omega
  simp [trans, h2]

/-! ### Fields of `viewTrans` -/

section Fields

variable (p : Fin n) (st : St n) (v : ℕ) (ib : Fin n → Option (Msg n))

/-- Tactic for field lemmas of `viewTrans`. -/
macro "vt_field" : tactic => `(tactic| (
  unfold viewTrans
  split <;> (try simp only [ph0, ph1, ph3, ph4, ph6, ph8, phAgg] at *) <;>
    (repeat' (first | split | split_ifs)) <;> simp_all))

lemma viewTrans_key {j : ℕ} (hj : j ≠ 6) : (viewTrans π p st v j ib).key = st.key := by
  vt_field

lemma viewTrans_lock {j : ℕ} (hj : j ≠ 8) : (viewTrans π p st v j ib).lock = st.lock := by
  vt_field

lemma viewTrans_vin {j : ℕ} (hj : j ≠ 3) : (viewTrans π p st v j ib).vin = st.vin := by
  vt_field

lemma viewTrans_lead {j : ℕ} (hj : j ≠ 0) : (viewTrans π p st v j ib).lead = st.lead := by
  vt_field

lemma viewTrans_active {j : ℕ} (hj : j ≠ 1) : (viewTrans π p st v j ib).active = st.active := by
  vt_field

lemma viewTrans_sign {j : ℕ} (h0 : j ≠ 0) (h4 : j ≠ 4) (h6 : j ≠ 6) (h8 : j ≠ 8) :
    (viewTrans π p st v j ib).sign = st.sign := by
  vt_field

lemma viewTrans_commit {j : ℕ} (h1 : j ≠ 1) (h9 : j ≠ 9) :
    (viewTrans π p st v j ib).commit = st.commit := by
  vt_field

lemma viewTrans_fb (j : ℕ) : (viewTrans π p st v j ib).fb = st.fb := by
  vt_field

lemma viewTrans_last (j : ℕ) : (viewTrans π p st v j ib).last = st.last := by
  vt_field

end Fields

end Podc.FewToManyFaultsBA.Sync
