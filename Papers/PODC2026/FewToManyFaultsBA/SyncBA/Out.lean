import Papers.PODC2026.FewToManyFaultsBA.SyncBA.Safety

/-!
# Messages of the view rounds and the leader's state

Shapes of the messages `out` sends in the view rounds (`out_party`, `out_leader`, `out_none`),
what the inbox readers return on them, and the evolution of the leader-only fields `lead` and
`plan` within a view.
-/

namespace Podc.FewToManyFaultsBA.Sync

open Cslib.Byzantine.LockStep Finset

variable {n : ℕ} [NeZero n] {π : Params n} {s : Scenario (Fin n) Bool (Msg n)}

/-! ### Shapes of view messages -/

lemma out_view {p : Fin n} {st : St n} {v j : ℕ} (hv : v < n) (hj : j < 11) (q : Fin n) :
    out π p st (11 * v + j) q =
      if (if q = leader v then partyOut p st v j else none).isNone ∧
          (if p = leader v then leaderOut st j q else none).isNone then none
      else some (.view (if q = leader v then partyOut p st v j else none)
        (if p = leader v then leaderOut st j q else none)) := by
  simp only [out, view_lt_Rh hv hj, ite_true, view_div hj, view_mod hj]

lemma out_party {p : Fin n} {st : St n} {v j : ℕ} (hv : v < n) (hj : j < 11) {pm : PMsg n}
    (hpm : partyOut p st v j = some pm) :
    ∃ lm, out π p st (11 * v + j) (leader v) = some (.view (some pm) lm) := by
  rw [out_view hv hj]; simp [hpm]

lemma out_leader {st : St n} {v j : ℕ} (hv : v < n) (hj : j < 11) {q : Fin n} {lm : LMsg n}
    (hlm : leaderOut st j q = some lm) :
    ∃ pm, out π (leader v) st (11 * v + j) q = some (.view pm (some lm)) := by
  rw [out_view hv hj]; simp [hlm]

lemma out_none {p : Fin n} {st : St n} {v j : ℕ} (hv : v < n) (hj : j < 11) {q : Fin n}
    (hp : p ≠ leader v) (hq : q ≠ leader v) : out π p st (11 * v + j) q = none := by
  rw [out_view hv hj]; simp [hp, hq]

/-! ### The leader's fields within a view -/

lemma S_lead1 {w : ℕ} (hw : w < n) (p : Fin n) :
    (S π s (11 * w + 1) p).lead = (decide (p = leader w) && (S π s (11 * w) p).commit.isNone) := by
  rw [S_view (11 * w) w 0 hw (by norm_num) (by omega)]
  simp [viewTrans, ph0]

lemma S_lead {w j : ℕ} (hw : w < n) (hj1 : 1 ≤ j) (hj2 : j ≤ 11) (p : Fin n) :
    (S π s (11 * w + j) p).lead = (S π s (11 * w + 1) p).lead := by
  induction j, hj1 using Nat.le_induction with
  | base => rfl
  | succ j hj ih =>
    rw [show 11 * w + (j + 1) = 11 * w + j + 1 by omega,
      S_view (11 * w + j) w j hw (by omega) rfl]
    simp only
    rw [viewTrans_lead _ _ _ _ (by omega)]
    exact ih (by omega)

lemma lead_spec {w j : ℕ} (hw : w < n) (hj1 : 1 ≤ j) (hj2 : j ≤ 11) {p : Fin n}
    (h : (S π s (11 * w + j) p).lead = true) :
    p = leader w ∧ (S π s (11 * w) p).commit = none := by
  rw [S_lead hw hj1 hj2, S_lead1 hw] at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, Option.isNone_iff_eq_none] at h
  exact h

lemma S_plan1 {w : ℕ} (hw : w < n) (p : Fin n) : (S π s (11 * w + 1) p).plan = .idle := by
  rw [S_view (11 * w) w 0 hw (by norm_num) (by omega)]
  simp [viewTrans, ph0]

lemma S_plan2 {w : ℕ} (hw : w < n) (p : Fin n) :
    (S π s (11 * w + 2) p).plan = if (S π s (11 * w + 1) p).lead then
      leaderPlan π w (S π s (11 * w + 1) p) (aib π s (11 * w + 1) p) else .idle := by
  rw [show 11 * w + 2 = 11 * w + 1 + 1 by omega, S_view (11 * w + 1) w 1 hw (by norm_num) rfl]
  simp only [viewTrans]
  rw [ph1_plan, S_plan1 hw]

lemma S_plan3 {w : ℕ} (hw : w < n) (p : Fin n) :
    (S π s (11 * w + 3) p).plan = (S π s (11 * w + 2) p).plan := by
  rw [show 11 * w + 3 = 11 * w + 2 + 1 by omega, S_view (11 * w + 2) w 2 hw (by norm_num) rfl]
  simp [viewTrans]

lemma S_vin_none : ∀ r (p : Fin n), (S π s r p).vin = none →
    ∃ w < n, 11 * w + 3 < r ∧ (S π s (11 * w + 3) p).lead = true ∧
      (S π s (11 * w + 3) p).plan = .retr ∧
      (retrToks (.inp false) (aib π s (11 * w + 3) p)).card < π.t + 1 ∧
      (retrToks (.inp true) (aib π s (11 * w + 3) p)).card < π.t + 1 := by
  intro r
  induction r with
  | zero => intro p h; simp [St.init] at h
  | succ r ih =>
    intro p h
    by_cases hprev : (S π s r p).vin = none
    · obtain ⟨w, hw, hr, rest⟩ := ih p hprev
      exact ⟨w, hw, by omega, rest⟩
    rw [S_succ, trans_vin] at h
    split_ifs at h with hr
    · by_cases h3 : r % 11 = 3
      · rw [h3] at h
        simp only [viewTrans, ph3] at h
        have hw : r / 11 < n := by unfold Rh at hr; omega
        have hr' : r = 11 * (r / 11) + 3 := by omega
        split_ifs at h with hc h1 h2
        · exact absurd h hprev
        · exact absurd h hprev
        · refine ⟨r / 11, hw, by omega, ?_⟩
          rw [← hr']
          exact ⟨hc.1, hc.2, by omega, by omega⟩
        · exact absurd h hprev
      · rw [viewTrans_vin _ _ _ _ h3] at h; exact absurd h hprev
    · exact absurd h hprev

end Podc.FewToManyFaultsBA.Sync
