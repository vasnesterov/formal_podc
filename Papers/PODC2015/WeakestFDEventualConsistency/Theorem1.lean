import Papers.PODC2015.WeakestFDEventualConsistency.ECtoETOB
import Papers.PODC2015.WeakestFDEventualConsistency.ETOBtoEC

/-!
# Theorem 1 of [DGKPS15]: EC and ETOB are equivalent

Both transformations (`ECtoETOB.etob_of_ec`, `ETOBtoEC.ec_of_etob`) in one statement, and
non-vacuity witnesses: admissible runs in which all hypotheses of the two directions hold.
-/

namespace Podc.WeakestFDEventualConsistency

open Cslib.FailureDetectors

/-- **Theorem 1 of [DGKPS15]** (EC and ETOB are equivalent), as the conjunction of the two
transformations: `T_{EC→ETOB}` implements ETOB from a (well-formed) EC black box, and
`T_{ETOB→EC}` (with distinct broadcasts) implements EC from an ETOB black box. Neither
transformation uses a failure detector (it is generic in the range `R` and ignores it), so the
equivalence holds in every environment. -/
theorem theorem1 :
    (∀ {P R M : Type} [DecidableEq P] [DecidableEq M] [Finite P] (r : Run P R (ECtoETOB.Input M)),
      (ECtoETOB.alg (R := R)).Admissible r → (ECtoETOB.ecHist r).RespAfterInv →
      ECIntegrity (ECtoETOB.ecHist r) →
      ((ECtoETOB.ecHist r).ProperUse → EC r.F (ECtoETOB.ecHist r)) →
      ETOB r.F (ECtoETOB.tobHist r)) ∧
    (∀ {P R V : Type} [DecidableEq P] [Finite P] (inp : P → ℕ → V)
      (r : Run P R (ETOBtoEC.Input P V)),
      (ETOBtoEC.alg (R := R) inp).Admissible r →
      ((ETOBtoEC.tobHist inp r).Distinct → ETOB r.F (ETOBtoEC.tobHist inp r)) →
      EC r.F (ETOBtoEC.ecHist inp r)) :=
  ⟨fun _ hA hwf hint hbb => ECtoETOB.etob_of_ec hA hwf hint hbb,
    fun _ _ hA hbb => ETOBtoEC.ec_of_etob hA hbb⟩

/-! ### Non-vacuity, direction EC → ETOB

One process, no broadcasts; the EC black box answers instance `j` with `[]` at time `2j + 1`;
time-outs at even times. -/

namespace ECtoETOB

/-- The schedule of the witness. -/
def wSched (t : ℕ) : Option (Unit × Choice Unit (Input ℕ)) :=
  if t % 2 = 1 then some ((), .input (.ecResp (t / 2) [])) else some ((), .tick)

/-- The witness run. -/
def wRun : Run Unit Unit (Input ℕ) := ⟨FailurePattern.noCrash, fun _ _ => (), wSched⟩

/-- Number of instances invoked before time `t`. -/
def wf (t : ℕ) : ℕ := if t = 0 then 0 else t / 2 + 1

lemma w_st (t : ℕ) : (alg (R := Unit)).st wRun () t = ⟨[], [], wf t⟩ := by
  induction t with
  | zero => rfl
  | succ t ih =>
    by_cases ht : t % 2 = 1
    · have hσ : wRun.σ t = some ((), .input (.ecResp (t / 2) [])) := by simp [wRun, wSched, ht]
      rw [(Algorithm.cfg_succ_of_event wRun t () _ _ hσ (Algorithm.event_input _ _)).1, ih]
      simp only [alg, proposal, newBatch, State.mk.injEq, true_and]
      simp only [wf]
      split_ifs <;> omega
    · have hσ : wRun.σ t = some ((), .tick) := by simp [wRun, wSched, ht]
      rw [(Algorithm.cfg_succ_of_event wRun t () _ _ hσ (Algorithm.event_tick _)).1, ih]
      simp only [alg, wf]
      split_ifs <;> simp <;> omega

lemma w_cnt (t : ℕ) : cnt wRun () t = wf t := by simp [cnt, w_st]

lemma w_resp {j : ℕ} {l : List ℕ} {t : ℕ} :
    (ecHist wRun).resp () j l t ↔ t % 2 = 1 ∧ j = t / 2 ∧ l = [] := by
  change wSched t = _ ↔ _
  unfold wSched
  split_ifs with h
  · simp only [Option.some.injEq, Prod.mk.injEq, Choice.input.injEq, Input.ecResp.injEq,
      true_and]
    constructor
    · rintro ⟨rfl, rfl⟩; exact ⟨h, rfl, rfl⟩
    · rintro ⟨-, rfl, rfl⟩; exact ⟨rfl, rfl⟩
  · simp [h]

lemma w_inv {j : ℕ} {t : ℕ} (h1 : wf t = j) (h2 : wf (t + 1) = j + 1) :
    (ecHist wRun).inv () j [] t :=
  inv_iff.mpr ⟨by rw [w_cnt, h1], by rw [w_cnt, h2], by simp [tobHist, td, w_st, proposal, newBatch]⟩

lemma w_inv_of_resp {j : ℕ} {l : List ℕ} {t : ℕ} (h : (ecHist wRun).resp () j l t) :
    l = [] ∧ ∃ t' < t, (ecHist wRun).inv () j [] t' := by
  obtain ⟨ht, rfl, rfl⟩ := w_resp.mp h
  refine ⟨rfl, ?_⟩
  by_cases h0 : t / 2 = 0
  · exact ⟨0, by omega, w_inv (by simp [wf, h0]) (by simp [wf]; omega)⟩
  · exact ⟨t - 2, by omega, w_inv (by simp only [wf]; split_ifs <;> omega)
      (by simp only [wf]; split_ifs <;> omega)⟩

/-- All hypotheses of `etob_of_ec` hold in the witness run (with a black box satisfying EC
unconditionally). -/
theorem etob_of_ec_nonvacuous :
    (alg (R := Unit)).Admissible wRun ∧ (ecHist wRun).RespAfterInv ∧ ECIntegrity (ecHist wRun) ∧
      EC wRun.F (ecHist wRun) := by
  have hnone : ∀ t q s, wRun.σ t ≠ some ((), .recv q s) := by
    intro t q s; simp only [wRun, wSched]; split_ifs <;> simp
  refine ⟨⟨fun _ _ _ _ h => h, fun t p q s h => absurd h (hnone t q s),
    fun t _ p q s h => absurd h (hnone t q s), fun p _ T => ⟨2 * T + 2, by omega, ?_⟩, ?_⟩,
    fun p j l t h => ?_, ?_, ?_⟩
  · simp only [wRun, wSched]; split_ifs <;> first | rfl | omega
  · intro p _ t s q m h
    exfalso
    obtain ⟨c, e, hσ, he, hb⟩ := Algorithm.msg_spec wRun h
    obtain ⟨m', -, rfl⟩ := step_msg _ _ _ _ hb
    rw [event_eq_input he] at hσ
    revert hσ; simp only [wRun, wSched]; split_ifs <;> simp
  · obtain ⟨-, t', ht', hi⟩ := w_inv_of_resp h
    exact ⟨[], t', ht', hi⟩
  · intro p j l l' t t' h h'
    obtain ⟨h1, rfl, rfl⟩ := w_resp.mp h
    obtain ⟨h1', h2', rfl⟩ := w_resp.mp h'
    exact ⟨by omega, rfl⟩
  · refine ⟨fun p _ j => ⟨[], 2 * j + 1, w_resp.mpr ⟨by omega, by omega, rfl⟩⟩, ?_, ?_,
      0, fun j _ p q l l' t t' h h' => by rw [(w_resp.mp h).2.2, (w_resp.mp h').2.2]⟩
    · intro p j l l' t t' h h'
      obtain ⟨h1, rfl, rfl⟩ := w_resp.mp h
      obtain ⟨h1', h2', rfl⟩ := w_resp.mp h'
      exact ⟨by omega, rfl⟩
    · intro p j l t h
      obtain ⟨rfl, t', ht', hi⟩ := w_inv_of_resp h
      exact ⟨(), t', ht'.le, hi⟩

example : ETOB wRun.F (tobHist wRun) :=
  have h := etob_of_ec_nonvacuous
  etob_of_ec h.1 h.2.1 h.2.2.1 (fun _ => h.2.2.2)

end ECtoETOB

/-! ### Non-vacuity, direction ETOB → EC

One process proposing `()` to every instance; at time `2j + 1` the ETOB black box delivers the
sequence of the messages broadcast for instances `0, …, j`; time-outs at even times. -/

namespace ETOBtoEC

/-- The messages broadcast for instances `0, …, j`. -/
def wL (j : ℕ) : List (Unit × ℕ × Unit) := (List.range (j + 1)).map fun i => ((), i, ())

/-- The schedule of the witness. -/
def wSched (t : ℕ) : Option (Unit × Choice Unit (Input Unit Unit)) :=
  if t % 2 = 1 then some ((), .input (.tobDeliver (wL (t / 2)))) else some ((), .tick)

/-- The witness run. -/
def wRun : Run Unit Unit (Input Unit Unit) := ⟨FailurePattern.noCrash, fun _ _ => (), wSched⟩

/-- The proposals. -/
def wInp : Unit → ℕ → Unit := fun _ _ => ()

/-- The black box's output variable before time `t`. -/
def wD (t : ℕ) : List (Unit × ℕ × Unit) := if t < 2 then [] else wL ((t - 2) / 2)

lemma wD_of_ge {t : ℕ} (h : 2 ≤ t) : wD t = wL ((t - 2) / 2) := by
  unfold wD
  split_ifs
  · omega
  · rfl

lemma mem_wL {i j : ℕ} : ((), i, ()) ∈ wL j ↔ i ≤ j := by
  simp [wL]

lemma wL_prefix {a b : ℕ} (h : a ≤ b) : wL a <+: wL b := by
  unfold wL
  have : List.range (b + 1) =
      List.range (a + 1) ++ List.map (fun x => a + 1 + x) (List.range (b - a)) := by
    rw [← List.range_add]; congr 1; omega
  rw [this, List.map_append]
  exact List.prefix_append _ _

lemma w_st (t : ℕ) : (alg (R := Unit) wInp).st wRun () t = ⟨(t + 1) / 2, wD t⟩ := by
  induction t with
  | zero => rfl
  | succ t ih =>
    by_cases ht : t % 2 = 1
    · have hσ : wRun.σ t = some ((), .input (.tobDeliver (wL (t / 2)))) := by
        simp [wRun, wSched, ht]
      rw [(Algorithm.cfg_succ_of_event wRun t () _ _ hσ (Algorithm.event_input _ _)).1, ih]
      simp only [alg, State.mk.injEq]
      refine ⟨by omega, ?_⟩
      rw [wD_of_ge (by omega)]
      congr 1
      omega
    · have hσ : wRun.σ t = some ((), .tick) := by simp [wRun, wSched, ht]
      rw [(Algorithm.cfg_succ_of_event wRun t () _ _ hσ (Algorithm.event_tick _)).1, ih]
      rcases Nat.eq_zero_or_pos t with rfl | hpos
      · rfl
      · obtain ⟨j, hj⟩ : ∃ j, t = 2 * j + 2 := ⟨(t - 2) / 2, by omega⟩
        subst hj
        have hn : (2 * j + 2 + 1) / 2 = j + 1 := by omega
        have hd : wD (2 * j + 2) = wL j := by rw [wD_of_ge (by omega)]; congr 1; omega
        obtain ⟨v, hv⟩ := first_isSome_of_mem (mem_wL.mpr (le_refl j))
        have h3 : wD (2 * j + 2 + 1) = wL j := by
          rw [wD_of_ge (by omega)]; congr 1; omega
        rw [hn, hd, h3, show (2 * j + 2 + 1 + 1) / 2 = j + 2 by omega]
        simp [alg, hv]

lemma w_nxt (t : ℕ) : nxt wInp wRun () t = (t + 1) / 2 := by simp [nxt, w_st]

lemma w_d (t : ℕ) : (tobHist wInp wRun).d () t = wD t := by simp [tobHist, w_st]

lemma w_bcast {i t : ℕ} (h : t = 2 * i) : (tobHist wInp wRun).bcast () ((), i, ()) t :=
  bcast_iff.mpr ⟨i, rfl, inv_iff.mpr ⟨by rw [w_nxt]; omega, by rw [w_nxt]; omega, rfl⟩⟩

/-- All hypotheses of `ec_of_etob` hold in the witness run (with a black box satisfying ETOB
unconditionally). -/
theorem ec_of_etob_nonvacuous :
    (alg (R := Unit) wInp).Admissible wRun ∧ ETOB wRun.F (tobHist wInp wRun) := by
  have hnone : ∀ t q s, wRun.σ t ≠ some ((), .recv q s) := by
    intro t q s; simp only [wRun, wSched]; split_ifs <;> simp
  refine ⟨⟨fun _ _ _ _ h => h, fun t p q s h => absurd h (hnone t q s),
    fun t _ p q s h => absurd h (hnone t q s), fun p _ T => ⟨2 * T + 2, by omega, ?_⟩,
    fun _ _ _ _ _ m => m.elim⟩, ?_, ?_, ?_, ?_, 0, ?_, ?_⟩
  · simp only [wRun, wSched]; split_ifs <;> first | rfl | omega
  · -- TOB-Validity
    rintro ⟨⟩ m t - hb
    obtain ⟨j, rfl, hi⟩ := bcast_iff.mp hb
    obtain ⟨h1, -, -⟩ := inv_iff.mp hi
    rw [w_nxt] at h1
    refine ⟨2 * j + 2, by omega, fun t'' ht'' => ?_⟩
    rw [w_d, wD_of_ge (by omega)]
    exact mem_wL.mpr (by omega)
  · -- TOB-No-creation
    rintro ⟨⟩ t ⟨⟨⟩, i, ⟨⟩⟩ hm
    rw [w_d, wD] at hm
    split_ifs at hm with h
    · simp at hm
    · exact ⟨(), 2 * i, by have := mem_wL.mp hm; omega, w_bcast rfl⟩
  · -- TOB-No-duplication
    rintro ⟨⟩ t
    rw [w_d, wD]
    split_ifs
    · exact List.nodup_nil
    · exact (List.nodup_range).map fun a b h => by simpa using h
  · -- TOB-Agreement
    rintro ⟨⟩ ⟨⟩ m - - h
    exact h
  · -- Stability
    rintro ⟨⟩ - t₁ t₂ - h
    rw [w_d, w_d, wD, wD]
    split_ifs with h1 h2
    · exact List.nil_prefix
    · exact List.nil_prefix
    · omega
    · exact wL_prefix (by omega)
  · -- Total order
    rintro ⟨⟩ ⟨⟩ - - t - m₁ m₂ - - hb
    exact hb

example : EC wRun.F (ecHist wInp wRun) :=
  ec_of_etob ec_of_etob_nonvacuous.1 fun _ => ec_of_etob_nonvacuous.2

end ETOBtoEC

end Podc.WeakestFDEventualConsistency
