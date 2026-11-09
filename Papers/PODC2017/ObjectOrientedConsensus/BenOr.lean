import Mathlib
import Cslib.Foundations.Data.Finset.Quorum
import Papers.PODC2017.ObjectOrientedConsensus.Template

/-!
# Ben-Or as vacillate-adopt-commit + reconciliator (Section 4.2 of [AACV])

Asynchronous message passing, `n = Fintype.card P` processes, at most `t` crashes, `2t < n`.

One round of Algorithm 5 (the VAC) is described by the *views* of the processes (`Round`): `I` are the
processes that sent their exchange-1 message `⟨1, val q⟩`, `I2 ⊆ I` those that completed the first wait
and sent an exchange-2 message, `O ⊆ I2` those that completed the second wait and returned. `S1 p`, `S2 p`
are the `n − t` messages `p` waited for (any `n − t` senders: the scheduler, crashes and message delays are
arbitrary). Messages are computed from the senders' states. Every asynchronous execution of a round
yields such views, so the safety properties below hold for all executions.

* Lemma 5 (Algorithm 5 is a VAC): `lemma5`.
* The waits can complete iff at least `n − t` processes send (`wait_completes_iff`).
* With the template's "decide, then halt" (Algorithm 1), Ben-Or **does not terminate**: with `n = 3`,
  `t = 1` and no crash, two processes commit in round 1 and halt, the third adopts and waits forever in
  round 2 (`halting_blocks`). If decided processes keep participating, every round has the `n − t`
  correct invokers and the template is correct (`toExec1`, `agreement`).
* Lemma 4 (the coin is a reconciliator), deterministic part: the adopt/commit value of a round is the
  strict-majority value of the round's inputs, so it is fixed before any coin is flipped, and coins equal
  to it end the protocol in the next round (`lemma4_good_coins`, `adopted_value_majority`).
-/

namespace Podc.ObjectOrientedConsensus.BenOr

open Finset

variable {P V : Type*} [Fintype P] [DecidableEq P] [DecidableEq V]

/-- One asynchronous round of Algorithm 5, given by the processes' views. -/
structure Round (P V : Type*) [Fintype P] (t : ℕ) where
  /-- Processes that sent `⟨1, val p⟩` (invokers). -/
  I : Finset P
  /-- Processes that completed the first wait and sent an exchange-2 message. -/
  I2 : Finset P
  /-- Processes that completed the second wait and returned. -/
  O : Finset P
  /-- Inputs (preferences) of the invokers. -/
  val : P → V
  /-- The `n − t` exchange-1 messages `p` waited for (their senders). -/
  S1 : P → Finset P
  /-- The `n − t` exchange-2 messages `p` waited for (their senders). -/
  S2 : P → Finset P
  I2_sub : I2 ⊆ I
  O_sub : O ⊆ I2
  S1_spec : ∀ p ∈ I2, S1 p ⊆ I ∧ #(S1 p) = Fintype.card P - t
  S2_spec : ∀ p ∈ O, S2 p ⊆ I2 ∧ #(S2 p) = Fintype.card P - t

namespace Round

variable {t : ℕ} (R : Round P V t)

/-- The exchange-2 message of `q`: `some v` (`⟨2, v, ratify⟩`) if more than `n/2` of the exchange-1
messages `q` received carry `v`, `none` (`⟨2, ?⟩`) otherwise. -/
noncomputable def rat (q : P) : Option V :=
  (R.S1 q).threshold? (fun r => some (R.val r)) (Fintype.card P / 2 + 1)

/-- The output of `p` (Algorithm 5): commit `v` if more than `t` received ratify messages carry `v`;
otherwise adopt `v` if some received ratify message carries `v`; otherwise vacillate with the own value. -/
noncomputable def out (p : P) : Conf × V :=
  match (R.S2 p).threshold? R.rat (t + 1) with
  | some v => (.commit, v)
  | none =>
    match (R.S2 p).threshold? R.rat 1 with
    | some v => (.adopt, v)
    | none => (.vacillate, R.val p)

omit [DecidableEq P] in
lemma countEq_le_univ (s : Finset P) (v : V) :
    s.countEq (fun r => some (R.val r)) (some v) ≤ (univ : Finset P).countEq R.val v := by
  simp only [countEq_def, Option.some_inj]
  exact card_le_card (filter_subset_filter _ (subset_univ _))

omit [DecidableEq P] in
/-- Ratify messages carry a unique value. -/
lemma rat_unique {q q' : P} {v w : V} (hq : R.rat q = some v) (hq' : R.rat q' = some w) : v = w := by
  have h1 := le_countEq_of_threshold?_eq_some hq
  have h2 := le_countEq_of_threshold?_eq_some hq'
  have h1' := (R.countEq_le_univ (R.S1 q) v)
  have h2' := (R.countEq_le_univ (R.S1 q') w)
  by_contra hvw
  have := countEq_add_countEq_le (s := (univ : Finset P)) (f := R.val) hvw
  rw [card_univ] at this
  omega

omit [DecidableEq P] in
/-- A ratified value is the input of a process `q` heard from. -/
lemma rat_valid {q : P} {v : V} (hq : R.rat q = some v) : ∃ r ∈ R.S1 q, R.val r = v := by
  obtain ⟨r, hr, h⟩ := exists_mem_of_threshold?_eq_some (Nat.succ_pos _) hq
  exact ⟨r, hr, Option.some_injective _ h⟩

omit [DecidableEq P] in
/-- A ratified value is a strict majority of `q`'s view. -/
lemma rat_majority {q : P} {v : V} (hq : R.rat q = some v) :
    Fintype.card P < 2 * #{r ∈ R.S1 q | R.val r = v} := by
  have := le_countEq_of_threshold?_eq_some hq
  simp only [countEq_def, Option.some_inj] at this
  omega

omit [DecidableEq P] in
/-- A non-vacillate output carries the value of a ratify message received. -/
lemma out_ratified {p : P} (h : (R.out p).1 ≠ .vacillate) : ∃ q ∈ R.S2 p, R.rat q = some (R.out p).2 := by
  unfold out at h ⊢
  split
  next v hv => exact exists_mem_of_threshold?_eq_some (Nat.succ_pos _) hv
  next hv =>
    split
    next v hv' => exact exists_mem_of_threshold?_eq_some Nat.one_pos hv'
    next hv' => rw [hv, hv'] at h; exact absurd rfl h

omit [DecidableEq P] in
lemma out_vacillate {p : P} (h : (R.out p).1 = .vacillate) : (R.out p).2 = R.val p := by
  unfold out at h ⊢
  split
  next v hv => rw [hv] at h; cases h
  next hv =>
    split
    next v hv' => rw [hv, hv'] at h; cases h
    next => rfl

omit [DecidableEq P] in
lemma out_commit {p : P} (h : (R.out p).1 = .commit) :
    t + 1 ≤ (R.S2 p).countEq R.rat (some (R.out p).2) := by
  unfold out at h ⊢
  split
  next v hv => exact le_countEq_of_threshold?_eq_some hv
  next hv =>
    split
    next v hv' => rw [hv, hv'] at h; cases h
    next hv' => rw [hv, hv'] at h; cases h

omit [DecidableEq P] in
/-- Receiving a ratify message rules out vacillation. -/
lemma out_ne_vacillate {p : P} {v : V} (h : 1 ≤ (R.S2 p).countEq R.rat (some v)) :
    (R.out p).1 ≠ .vacillate := by
  unfold out
  split
  · simp
  · split
    · simp
    next hv' => exact absurd h (not_le.2 (threshold?_eq_none_iff.1 hv' v))

/-- **Lemma 5 of [AACV].** Algorithm 5 is a vacillate-adopt-commit object (validity, convergence,
coherence over adopt & commit, coherence over vacillate & adopt), for `2t < n`. -/
theorem lemma5 (ht : 2 * t < Fintype.card P) : IsVAC (↑R.I : Set P) ↑R.O R.val R.out where
  sub := fun p hp => R.I2_sub (R.O_sub hp)
  validity p hp := by
    by_cases hv : (R.out p).1 = .vacillate
    · exact ⟨p, R.I2_sub (R.O_sub hp), R.out_vacillate hv⟩
    · obtain ⟨q, hq, hqv⟩ := R.out_ratified hv
      obtain ⟨r, hr, hrv⟩ := R.rat_valid hqv
      have hqI2 := (R.S2_spec p hp).1 hq
      exact ⟨r, (R.S1_spec q hqI2).1 hr, hrv.symm⟩
  convergence v hv p hp := by
    have hrat : ∀ q ∈ R.I2, R.rat q = some v := by
      intro q hq
      obtain ⟨hsub, hcard⟩ := R.S1_spec q hq
      have hall : (R.S1 q).countEq (fun r => some (R.val r)) (some v) = #(R.S1 q) := by
        rw [countEq_def, filter_true_of_mem]
        intro r hr; rw [hv r (hsub hr)]
      have hle : #(R.S1 q) ≤ Fintype.card P := card_le_univ _
      exact threshold?_eq_some (by omega) (by omega)
    obtain ⟨hsub, hcard⟩ := R.S2_spec p hp
    have hall : (R.S2 p).countEq R.rat (some v) = #(R.S2 p) := by
      rw [countEq_def, filter_true_of_mem]
      intro q hq; exact hrat q (hsub hq)
    have hth : (R.S2 p).threshold? R.rat (t + 1) = some v := by
      refine threshold?_eq_some_of_forall (by omega) fun c hc => ?_
      have := countEq_add_countEq_le (s := R.S2 p) (f := R.rat) (b := some v) (c := some c)
        (by simpa [eq_comm] using hc)
      omega
    simp only [out, hth]
  coh_ac p hp hc q hq := by
    set w := (R.out p).2
    have hpw := R.out_commit hc
    -- the ratifiers of `w` among the senders of exchange-2 messages
    have hRw : t + 1 ≤ #{r ∈ R.I2 | R.rat r = some w} := by
      refine hpw.trans (card_le_card ?_)
      exact filter_subset_filter _ (R.S2_spec p hp).1
    obtain ⟨hsub, hcard⟩ := R.S2_spec q hq
    have hint := card_add_card_le_card_inter_add_card_univ (R.S2 q) {r ∈ R.I2 | R.rat r = some w}
    have hq1 : 1 ≤ (R.S2 q).countEq R.rat (some w) := by
      have : R.S2 q ∩ {r ∈ R.I2 | R.rat r = some w} ⊆ {r ∈ R.S2 q | R.rat r = some w} := by
        intro r; simp only [mem_inter, mem_filter]; tauto
      have := card_le_card this
      rw [countEq_def]
      omega
    have hnv := R.out_ne_vacillate hq1
    refine ⟨hnv, ?_⟩
    obtain ⟨r, -, hr⟩ := R.out_ratified hnv
    obtain ⟨r', -, hr'⟩ := R.out_ratified (show (R.out p).1 ≠ .vacillate by rw [hc]; simp)
    exact R.rat_unique hr hr'
  coh_va _ p _ hpa q _ := by
    by_cases hqv : (R.out q).1 = .vacillate
    · exact Or.inl hqv
    · right
      obtain ⟨r, -, hr⟩ := R.out_ratified hqv
      obtain ⟨r', -, hr'⟩ := R.out_ratified (show (R.out p).1 ≠ .vacillate by rw [hpa]; simp)
      exact R.rat_unique hr hr'

/-- The adopt/commit value of a round is the strict-majority value among the inputs of the round's
invokers, hence determined before any process flips its coin. -/
theorem adopted_value_majority {p : P} (hp : p ∈ R.O) (h : (R.out p).1 ≠ .vacillate) :
    Fintype.card P < 2 * #{q ∈ R.I | R.val q = (R.out p).2} := by
  obtain ⟨q, hq, hqv⟩ := R.out_ratified h
  have hqI2 := (R.S2_spec p hp).1 hq
  have := R.rat_majority hqv
  have hsub := (R.S1_spec q hqI2).1
  have := card_le_card (filter_subset_filter (fun r => R.val r = (R.out p).2) hsub)
  omega

/-- **Lemma 4 of [AACV] (deterministic part).** If every vacillating process's coin equals `u`, and `u`
is the strict-majority value of the round's inputs whenever there is one, then all processes leave the
round with `u` (the reconciliator's weak agreement), so all commit `u` in the next round
(`Exec1.lemma1_termination`). -/
theorem lemma4_good_coins (coin : P → V) (u : V)
    (hu : ∀ v, Fintype.card P < 2 * #{q ∈ R.I | R.val q = v} → u = v)
    (hc : ∀ p ∈ R.O, (R.out p).1 = .vacillate → coin p = u) :
    ∀ p ∈ R.O, next1 (R.out p) (coin p) = u := by
  intro p hp
  unfold next1
  split_ifs with hv
  · exact hc p hp hv
  · exact (hu _ (R.adopted_value_majority hp hv)).symm

end Round

/-- The waits of Algorithm 5 ("wait to receive `n − t` messages") can complete iff at least `n − t`
processes send. -/
theorem wait_completes_iff {t : ℕ} (M : Finset P) :
    (∃ S ⊆ M, #S = Fintype.card P - t) ↔ Fintype.card P - t ≤ #M :=
  ⟨fun ⟨_, hS, hc⟩ => hc ▸ card_le_card hS, fun h => exists_subset_card_eq h⟩

/-- An execution of Ben-Or decomposed as in Algorithm 1: rounds `R m`, the invokers of round `m + 1`
returned from round `m` and carry `next1` of their output and coin. -/
noncomputable def toExec1 {t : ℕ} (ht : 2 * t < Fintype.card P) (R : ℕ → Round P V t)
    (coin : ℕ → P → V)
    (hI : ∀ m, (R (m + 1)).I ⊆ (R m).O)
    (hval : ∀ m, ∀ p ∈ (R (m + 1)).I, (R (m + 1)).val p = next1 ((R m).out p) (coin m p)) :
    Exec1 P V where
  inp := (R 0).val
  I m := ↑(R m).I
  O m := ↑(R m).O
  val m := (R m).val
  out m := (R m).out
  recon := coin
  val_zero _ _ := rfl
  I_succ m := by intro p hp; exact hI m hp
  val_succ m p hp := hval m p hp
  vac m := (R m).lemma5 ht

/-- **Agreement of Ben-Or decomposed by Algorithm 1** (with or without halting). -/
theorem agreement {t : ℕ} (ht : 2 * t < Fintype.card P) (R : ℕ → Round P V t) (coin : ℕ → P → V)
    (hI : ∀ m, (R (m + 1)).I ⊆ (R m).O)
    (hval : ∀ m, ∀ p ∈ (R (m + 1)).I, (R (m + 1)).val p = next1 ((R m).out p) (coin m p))
    {m m' : ℕ} {p q : P} {v w : V} (hp : p ∈ (R m).O) (hpv : (R m).out p = (.commit, v))
    (hq : q ∈ (R m').O) (hqw : (R m').out q = (.commit, w)) : v = w :=
  (toExec1 ht R coin hI hval).lemma1_agreement ⟨m, hp, hpv⟩ ⟨m', hq, hqw⟩

/-! ### Counterexample: "decide, then halt" blocks Ben-Or -/

/-- Round 1 of the counterexample: `n = 3`, `t = 1`, no crash, inputs `0, 0, 1`; processes 0 and 1
hear `{0, 1}` in both exchanges, process 2 hears `{0, 2}`. -/
def cxRound : Round (Fin 3) (Fin 2) 1 where
  I := univ
  I2 := univ
  O := univ
  val := ![0, 0, 1]
  S1 := ![{0, 1}, {0, 1}, {0, 2}]
  S2 := ![{0, 1}, {0, 1}, {0, 2}]
  I2_sub := subset_rfl
  O_sub := subset_rfl
  S1_spec := by decide
  S2_spec := by decide

lemma cxRound_rat : cxRound.rat = ![some 0, some 0, none] := by
  funext q
  fin_cases q
  · exact threshold?_eq_some (by decide) (by decide)
  · exact threshold?_eq_some (by decide) (by decide)
  · exact threshold?_eq_none_iff.2 (by decide)

/-- **Ben-Or with the template's halting rule does not terminate.** In round 1 of `cxRound` (no
crash, `n = 3`, `t = 1`) processes 0 and 1 commit `0` and halt, process 2 adopts `0`. In round 2 only
process 2 invokes the VAC, and no round with invokers `⊆ {2}` lets anybody complete the first wait:
process 2 never decides, although it never crashes. -/
theorem halting_blocks :
    cxRound.out 0 = (.commit, 0) ∧ cxRound.out 1 = (.commit, 0) ∧ cxRound.out 2 = (.adopt, 0) ∧
    ∀ R₂ : Round (Fin 3) (Fin 2) 1, R₂.I ⊆ {2} → R₂.I2 = ∅ := by
  have h01 : ∀ p : Fin 3, p ≠ 2 → cxRound.out p = (.commit, 0) := by
    intro p hp
    have hth : (cxRound.S2 p).threshold? cxRound.rat (1 + 1) = some 0 := by
      rw [cxRound_rat]
      fin_cases p
      · exact threshold?_eq_some (by decide) (by decide)
      · exact threshold?_eq_some (by decide) (by decide)
      · exact absurd rfl hp
    simp only [Round.out, hth]
  refine ⟨h01 0 (by decide), h01 1 (by decide), ?_, ?_⟩
  · have hth : (cxRound.S2 2).threshold? cxRound.rat (1 + 1) = none := by
      rw [cxRound_rat]; exact threshold?_eq_none_iff.2 (by decide)
    have hth' : (cxRound.S2 2).threshold? cxRound.rat 1 = some 0 := by
      rw [cxRound_rat]
      exact threshold?_eq_some_of_forall (by decide) (by decide)
    simp only [Round.out, hth, hth']
  · intro R₂ hI
    rw [eq_empty_iff_forall_notMem]
    intro p hp
    obtain ⟨hsub, hcard⟩ := R₂.S1_spec p hp
    have := card_le_card (hsub.trans hI)
    simp at hcard this
    omega

end Podc.ObjectOrientedConsensus.BenOr
