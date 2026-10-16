import Papers.PODC2026.ContentObliviousCounting.AnonCountingXfer
import Papers.PODC2026.ContentObliviousCounting.AnonCountingPipe

/-!
# Anonymous counting with a leader: main results (Theorem 4, Lemma 12, Theorem 13)

Chalopin, Chang, Di Luna, Zhou, *Efficient Counting and Simulation in Content-Oblivious Rings*,
PODC 2026, Section 5.

Model: oriented ring `oriented n`, `n ≥ 1`, asynchronous adversarial scheduler, content-oblivious
channels, no failures, deterministic anonymous nodes whose only input is the leader flag
(`leaderInput ℓ`: exactly the node `ℓ` is the leader). The algorithm is `anonCount`
(Algorithms 1–4, see `AnonCounting.lean`).

* `reach_inv`: every reachable configuration is described by a stage (`Stage.abs`).
* `anonCount_totalSent_le`: every execution sends at most `totalPulses n` pulses.
* `anonCount_final` (**Theorem 4**): every final configuration is quiescent, every node has
  terminated and outputs the ring size `n` and its clockwise distance from the leader (with the
  *corrected* distance formula `corrDist`).
* `anonCount_terminates`: every execution is finite, and every reachable configuration extends to a
  final one.
* `totalPulses_le` (**Theorem 13**): `totalPulses n ≤ 6 n ⌊√(2n)⌋ + 8n`.
-/

namespace Podc.ContentOblivious.AnonCounting

open Podc.ContentOblivious Finset

set_option linter.unusedSectionVars false
set_option linter.deprecated false

/-! ## All stages step to stages -/

theorem stepOk_all {n : ℕ} (hn : 0 < n) {s : Stage} (hok : s.Ok n) : StepOk n s := by
  cases s with
  | out j m t => exact stepOk_out hok
  | back j m t => exact stepOk_back hok
  | xfer j x y => exact stepOk_xfer hok
  | pipe κ a b => exact stepOk_pipe hn hok
  | final =>
    intro q j hen
    exact absurd hen.2.1 (by simp [Stage.abs, absFinal])

/-- The initial stage. -/
def initStage (n : ℕ) : Stage := if 1 < n then .out 1 1 1 else .pipe .comp (fun _ => 0) 0

lemma lastPhase_one : lastPhase 1 = 1 := lastPhase_eq (by decide) (by decide)

theorem init_ok {n : ℕ} (hn : 0 < n) :
    (initStage n).Ok n ∧ Agree n (absInit n) ((initStage n).abs n) := by
  unfold initStage
  split_ifs with h
  · refine ⟨⟨le_rfl, le_rfl, le_rfl, by simp [tri]; omega, le_rfl, le_rfl⟩, ?_, ?_, ?_⟩
    · intro p hp
      simp only [absInit, Stage.abs, absOut]
      by_cases hp0 : p = 0
      · subst hp0; simp [lst, nst, leaderInit, relF, mphF, tri]
      · simp [hp0, tri, nst, nonLeaderInit, relF, mphF]
    · intro p hp b
      simp only [absInit, Stage.abs, absOut, nxt, tri]
      have : ¬ (1 = n) := by omega
      cases b <;> simp [this]
    · simp [absInit, Stage.abs, absOut, phasesCost]
  · have h1 : n = 1 := by omega
    subst h1
    have hL : lead 1 = 0 := by simp [lead, lastPhase_one, tri]
    refine ⟨⟨trivial, pipeOk_zero (by simp [Kind.K])⟩, ?_, ?_, ?_⟩
    · intro p hp
      obtain rfl : p = 0 := by omega
      simp [absInit, Stage.abs, absPipe, hL, Kind.g, gst_nil, lst, nst, leaderInit, lastPhase_one,
        lastCount, relF, mphF]
    · intro p hp b
      obtain rfl : p = 0 := by omega
      simp only [absInit, Stage.abs, absPipe, hL, Kind.K, Kind.cw]
      rw [pipeTr_start true (by omega) hp b]
      cases b <;> simp [nxt, prv]
    · simp [absInit, Stage.abs, absPipe, Kind.base, lastBase, lastPhase_one, lastCount, phasesCost,
        hL]

/-- **The invariant**: every reachable configuration is described by a stage. -/
theorem reach_inv {n : ℕ} [NeZero n] {ℓ : ZMod n} {c : Cfg n}
    (h : anonCount.Reach (oriented n) (leaderInput ℓ) c) :
    ∃ s : Stage, s.Ok n ∧ Matches ℓ c (s.abs n) := by
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  refine Prog.Reach.induction ?_ ?_ h
  · obtain ⟨hok, hag⟩ := init_ok hn
    exact ⟨initStage n, hok, matches_init.agree hag⟩
  · intro c c' _ hs ih
    obtain ⟨s, hok, hm⟩ := ih
    obtain ⟨q, j, hen, hm'⟩ := matches_step hm hs
    obtain ⟨s', hok', hag⟩ := stepOk_all hn hok q j hen
    exact ⟨s', hok', hm'.agree hag⟩

/-! ## The pulse count -/

lemma phasesCost_mono {n j j' : ℕ} (h : j ≤ j') : phasesCost n j ≤ phasesCost n j' := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => simp only [phasesCost]; omega

lemma lt_tri_lastPhase_succ {n : ℕ} : n ≤ tri (lastPhase n + 1) := le_tri_phaseOf n

lemma tri_lastPhase_lt {n : ℕ} (hn : 0 < n) : tri (lastPhase n) < n := tri_phaseOf_lt hn

lemma one_le_lastPhase {n : ℕ} (hn : 0 < n) : 1 ≤ lastPhase n := one_le_phaseOf hn

/-- A phase `j` in which some position `tri j + m` (`m ≥ 1`) still exists is at most the last
phase. -/
lemma le_lastPhase {n j : ℕ} (h : tri j < n) : j ≤ lastPhase n := by
  by_contra hc
  have := tri_mono (show lastPhase n + 1 ≤ j by omega)
  have := @lt_tri_lastPhase_succ n
  omega

lemma probe_cost_le {n j m : ℕ} (hn : 0 < n) (hj : 1 ≤ j) (hmj : m ≤ j) (hmn : tri j + m < n) :
    phasesCost n j + m * (m + 1) ≤ totalPulses n := by
  have hjI := le_lastPhase (n := n) (j := j) (by omega)
  unfold totalPulses lastCount
  rcases Nat.lt_or_ge j (lastPhase n) with h | h
  · have h1 := phasesCost_mono (n := n) (show j + 1 ≤ lastPhase n by omega)
    have h2 : phasesCost n (j + 1) = phasesCost n j + j * (j + 1) + 2 * n := by
      simp [phasesCost, show j ≠ 0 by omega, add_assoc]
    have h3 : m * (m + 1) ≤ j * (j + 1) := Nat.mul_le_mul hmj (by omega)
    omega
  · have hjI' : j = lastPhase n := by omega
    subst hjI'
    have h3 : m * (m + 1) ≤ (n - 1 - tri (lastPhase n)) * (n - 1 - tri (lastPhase n) + 1) :=
      Nat.mul_le_mul (by omega) (by omega)
    omega

lemma sum_le_of_le {n L K : ℕ} {a : ℕ → ℕ} (hL : L < n) (h : ∀ p < n, p ≠ L → a p ≤ K) :
    ∑ p ∈ (range n).erase L, a p ≤ (n - 1) * K := by
  have := Finset.sum_le_card_nsmul ((range n).erase L) a K
    (fun p hp => h p (by simp at hp; omega) (by simp at hp; omega))
  rw [Finset.card_erase_of_mem (by simp [hL]), Finset.card_range, smul_eq_mul] at this
  exact this

/-- Every reachable configuration has sent at most `totalPulses n` pulses. -/
theorem stage_tot_le {n : ℕ} (hn : 0 < n) {s : Stage} (hok : s.Ok n) :
    (s.abs n).tot ≤ totalPulses n := by
  cases s with
  | out j m t =>
    obtain ⟨hj, hm1, hmj, hmn, ht1, htm⟩ := hok
    have := probe_cost_le hn hj hmj hmn
    have : m * (m - 1) + 2 * m = m * (m + 1) := mul_pred_add m
    simp only [Stage.abs, absOut]; omega
  | back j m t =>
    obtain ⟨hj, hm1, hmj, hmn, htm⟩ := hok
    have := probe_cost_le hn hj hmj hmn
    have : m * (m - 1) + 2 * m = m * (m + 1) := mul_pred_add m
    simp only [Stage.abs, absBack]; omega
  | xfer j x y =>
    obtain ⟨hj, hR, hx1, hxn, hyn, -, -⟩ := hok
    have hjI := le_lastPhase (n := n) (j := j + 1) hR
    have h1 := phasesCost_mono (n := n) hjI
    have h2 : phasesCost n (j + 1) = phasesCost n j + j * (j + 1) + 2 * n := by
      simp [phasesCost, show j ≠ 0 by omega, add_assoc]
    have h3 := min_le_right x n
    simp only [Stage.abs, absXfer]
    unfold totalPulses
    omega
  | pipe κ a b =>
    obtain ⟨hκ, hpo⟩ := hok
    have hL := lead_lt hn
    have hs := sum_le_of_le (a := a) (K := κ.K) hL (fun p hp hpL => (hpo.2.1 p hp hpL).1)
    simp only [Stage.abs, absPipe]
    unfold totalPulses
    have hn1 : (n - 1) + 1 = n := by omega
    cases κ with
    | comp => simp only [Kind.base, Kind.K, lastBase] at hs ⊢; nlinarith
    | fin3 => simp only [Kind.base, Kind.K, lastBase] at hs ⊢; nlinarith
    | bit i =>
      simp only [Kind.Ok] at hκ
      simp only [Kind.base, Kind.K, lastBase, D] at hs hκ ⊢
      have : 2 * n * i + 2 * n ≤ 2 * n * (Nat.digits 2 (lastCount n)).length := by
        have := Nat.mul_le_mul_left (2 * n) (show i + 1 ≤ _ from hκ); nlinarith
      nlinarith
    | end1 => simp only [Kind.base, Kind.K, lastBase, D] at hs ⊢; nlinarith
    | end2 => simp only [Kind.base, Kind.K, lastBase, D] at hs ⊢; nlinarith
  | final => simp [Stage.abs, absFinal]

/-! ## Final configurations -/

lemma kind_f_ready {n : ℕ} {κ : Kind} {p k : ℕ} (hk : k < κ.K) :
    ready (κ.f n p k) (!κ.cw n) = true ∧ terminated (κ.f n p k) = false := by
  cases κ <;> simp only [Kind.K] at hk <;> interval_cases k <;>
    simp [Kind.f, Kind.cw, fst, nst, ready, terminated]

lemma kind_g_ready {n : ℕ} {κ : Kind} (hκ : κ.Ok n) {b : ℕ} (hb : b < κ.K) :
    ready (κ.g n b) (!κ.cw n) = true ∧ terminated (κ.g n b) = false := by
  cases κ with
  | bit i =>
    simp only [Kind.Ok] at hκ
    have h2 := D_getD_lt n i
    simp only [Kind.g, Kind.cw, gst, lst, nst, ready, terminated, D_drop hκ, List.head?_cons]
    rcases (show (D n).getD i 0 = 0 ∨ (D n).getD i 0 = 1 by omega) with h | h <;>
      simp only [List.getD_eq_getElem?_getD] at h <;> simp [h]
  | _ => simp [Kind.g, Kind.cw, gst, lst, nst, ready, terminated]

/-- Simplification of the transfer stage at a given position. -/
macro "ac_xsimp" : tactic => `(tactic| simp (disch := omega) only [Stage.abs, absXfer, tri_succ,
  ccwD_le, ccwD_gt, cwD_ge, cwD_lt, if_pos, if_neg, ite_true, ite_false, and_true, true_and,
  and_self, Nat.lt_irrefl, le_refl, Nat.one_pos, Nat.zero_lt_one])

/-- In every stage except `final`, some delivery is enabled. -/
theorem exists_en {n : ℕ} (hn : 0 < n) {s : Stage} (hok : s.Ok n) (hs : s ≠ .final) :
    ∃ q j, (s.abs n).En n q j := by
  cases s with
  | out j m t =>
    obtain ⟨hj, hm1, hmj, hmn, ht1, htm⟩ := hok
    refine ⟨tri j + t, false, by omega, by simp [Stage.abs, absOut], ?_⟩
    simp only [Stage.abs, absOut]
    simp (disch := omega) only [if_pos, if_neg]
    simp [nst, ready, terminated]
  | back j m t =>
    obtain ⟨hj, hm1, hmj, hmn, htm⟩ := hok
    refine ⟨tri j + t, true, by omega, by simp [Stage.abs, absBack], ?_⟩
    simp only [Stage.abs, absBack]
    rcases Nat.eq_zero_or_pos t with rfl | ht
    · simp [lst, nst, ready, terminated]
    · simp (disch := omega) only [if_pos, if_neg]
      simp [nst, ready, terminated]
  | xfer j x y =>
    obtain ⟨hj, hR, hx1, hxn, hyn, hy1, hy2⟩ := hok
    simp only [tri_succ] at hR
    by_cases hx : x ≤ n
    · by_cases hxn' : x = n
      · subst hxn'
        refine ⟨tri j, true, by omega, ?_, ?_⟩ <;> ac_xsimp <;> simp [lst, nst, ready, terminated]
      by_cases hxL : x ≤ tri j
      · refine ⟨tri j - x, true, by omega, ?_, ?_⟩ <;> ac_xsimp <;>
          simp [nst, ready, terminated]
      · refine ⟨tri j + n - x, true, by omega, ?_, ?_⟩ <;> ac_xsimp <;>
          (try split_ifs) <;> (try contradiction) <;> simp [nst, ready, terminated]
    · have hy : 1 ≤ y := hy1.2 (by omega)
      have hx' : x = n + 1 := by omega
      subst hx'
      by_cases hyn' : y = n
      · subst hyn'
        refine ⟨tri j + j, false, by omega, ?_, ?_⟩ <;> ac_xsimp <;>
          simp [nst, ready, terminated]
      by_cases hw : tri j + j + y < n
      · refine ⟨tri j + j + y, false, by omega, ?_, ?_⟩ <;> ac_xsimp <;>
          simp [nst, ready, terminated]
      by_cases hL : tri j + j + y - n = tri j
      · refine ⟨tri j + j + y - n, false, by omega, ?_, ?_⟩ <;> ac_xsimp <;>
          simp [lst, nst, ready, terminated]
      · refine ⟨tri j + j + y - n, false, by omega, ?_, ?_⟩ <;> ac_xsimp <;>
          (try split_ifs) <;> (try contradiction) <;> simp [nst, ready, terminated]
  | pipe κ a b =>
    obtain ⟨hκ, hpo⟩ := hok
    have hL := lead_lt hn
    obtain ⟨p, hp, hpos⟩ := pipe_exists hL hpo
    refine ⟨p, !κ.cw n, hp, hpos, ?_⟩
    have hlt : (if p = lead n then b else a p) < κ.K := by
      rw [pipeTr_eq, if_pos rfl] at hpos
      have := pipeOk_srcCnt_le hpo (src_lt (κ.cw n) hp)
      omega
    simp only [Stage.abs, absPipe]
    split_ifs with h
    · rw [if_pos h] at hlt; exact kind_g_ready hκ hlt
    · rw [if_neg h] at hlt; exact kind_f_ready hlt
  | final => exact absurd rfl hs

lemma Matches.enabled {n : ℕ} [NeZero n] {ℓ : ZMod n} {c : Cfg n} {A : Abs}
    (h : Matches ℓ c A) {q : ℕ} {j : Bool} (hen : A.En n q j) :
    Enabled (oriented n) anonCount.toAlgo c (ℓ + (q : ZMod n)) j := by
  have hp := pos_natCast ℓ hen.1
  refine ⟨?_, ?_, ?_⟩
  · rw [h.1, hp]; exact hen.2.2.2
  · rw [h.1, hp]; exact hen.2.2.1
  · have := h.2.1 (ℓ + (q : ZMod n)) j; rw [hp] at this; have := hen.2.1; omega

/-- A final configuration is the configuration of the stage `final`. -/
theorem final_matches {n : ℕ} [NeZero n] {ℓ : ZMod n} {c : Cfg n}
    (hc : anonCount.Reach (oriented n) (leaderInput ℓ) c) (hf : anonCount.Final (oriented n) c) :
    Matches ℓ c (absFinal n) := by
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  obtain ⟨s, hok, hm⟩ := reach_inv hc
  by_cases hs : s = .final
  · subst hs; exact hm
  · obtain ⟨q, j, hen⟩ := exists_en hn hok hs
    exact absurd (hm.enabled hen) (hf _ _)

/-! ## Outputs -/

lemma lastCount_add {n : ℕ} (hn : 0 < n) : tri (lastPhase n) + lastCount n + 1 = n := by
  have := tri_lastPhase_lt hn; unfold lastCount; omega

lemma ringSize_last {n : ℕ} (hn : 0 < n) : ringSize (lastPhase n) (lastCount n) = n := by
  unfold ringSize; rw [← tri_eq]; exact lastCount_add hn

lemma D_ofDigits (n : ℕ) : Nat.ofDigits 2 (D n) = lastCount n := Nat.ofDigits_digits 2 _

/-- The state of every node in the final configuration. -/
lemma result_final {n : ℕ} (hn : 0 < n) {p : ℕ} (hp : p < n) :
    result ((absFinal n).st p) = some (n, p) := by
  have hI1 := one_le_lastPhase hn
  have htri := tri_lastPhase_lt hn
  have hsucc := @lt_tri_lastPhase_succ n
  simp only [tri_succ] at hsucc
  by_cases hpL : p = lead n
  · subst hpL
    simp only [absFinal, ite_true, gst_nil, result, lst, nst, terminated, countOf, kOf, ite_true,
      ringSize_last hn, relF_lead, add_zero, Option.some.injEq, Prod.mk.injEq, true_and]
    simp only [lead]
    by_cases h0 : tri (lastPhase n) = 0
    · rw [mphF_zero' h0, h0]; rfl
    · have hI2 : 2 ≤ lastPhase n := by
        by_contra hc; obtain h | h : lastPhase n = 0 ∨ lastPhase n = 1 := by omega
        · rw [h] at h0; exact h0 rfl
        · rw [h] at h0; exact h0 rfl
      have hφ : phaseOf (tri (lastPhase n)) = lastPhase n - 1 := by
        apply phaseOf_eq
        · exact tri_lt_tri (by omega) (by omega)
        · rw [show lastPhase n - 1 + 1 = lastPhase n by omega]
      rw [mphF_le (by omega) le_rfl, hφ, relF_lead]
      simp only [corrDist, show lastPhase n - 1 < lastPhase n by omega, ite_true, Nat.sub_zero]
      rw [← tri_succ_eq, show lastPhase n - 1 + 1 = lastPhase n by omega]
  · simp only [absFinal, if_neg hpL, fst, nst, result, terminated, countOf, kOf, D_ofDigits,
      ringSize_last hn, Option.some.injEq, Prod.mk.injEq, true_and, ite_true]
    simp only [show (PC.doneN = PC.doneL) = False by simp, ite_false, Nat.add_sub_cancel,
      D_ofDigits, ringSize_last hn, true_and]
    by_cases h0 : p = 0
    · rw [mphF_zero' h0, h0]; rfl
    by_cases h1 : p ≤ tri (lastPhase n)
    · have hlt := phaseOf_lt (by omega) h1
      have hle := le_tri_phaseOf p
      rw [mphF_le (by omega) h1, relF_le (by omega) h1]
      simp only [corrDist, hlt, ite_true]
      rw [← tri_succ_eq]; omega
    · rw [mphF_mid (by omega) (by omega), relF_mid (by omega) (by omega)]
      simp only [corrDist, lt_irrefl, ite_false]
      omega

/-! ## Main theorems -/

/-- The pulse count of every execution is at most `totalPulses n`. -/
theorem anonCount_totalSent_le {n : ℕ} [NeZero n] (ℓ : ZMod n) (c : Cfg n)
    (hc : anonCount.Reach (oriented n) (leaderInput ℓ) c) : totalSent c ≤ totalPulses n := by
  obtain ⟨s, hok, hm⟩ := reach_inv hc
  rw [hm.2.2]
  exact stage_tot_le (Nat.pos_of_ne_zero (NeZero.ne n)) hok

/-- **Theorem 4** (counting with anonymity, with the corrected distance formula): in every final
configuration of the counting algorithm on an oriented ring of size `n ≥ 1` with a unique leader
`ℓ`, no pulse is in transit, every node has terminated, and every node `v` outputs the ring size `n`
and its clockwise distance `(v - ℓ).val` from the leader. Moreover exactly `totalPulses n` pulses
have been sent. -/
theorem anonCount_final {n : ℕ} [NeZero n] (ℓ : ZMod n) (c : Cfg n)
    (hc : anonCount.Reach (oriented n) (leaderInput ℓ) c) (hf : anonCount.Final (oriented n) c) :
    anonCount.Quiescent (oriented n) c ∧ (∀ v, anonCount.result (c.st v) = some (n, (v - ℓ).val)) ∧
      totalSent c = totalPulses n := by
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hm := final_matches hc hf
  refine ⟨fun p => ?_, fun v => ?_, hm.2.2⟩
  · have := hm.2.1 p.1 p.2
    simp only [absFinal, add_zero] at this
    exact this.symm
  · show result (c.st v) = _
    rw [hm.1 v]
    exact result_final hn (pos_lt ℓ v)

/-- Termination: there is no infinite execution, and every reachable configuration can be
extended to a final configuration. -/
theorem anonCount_terminates {n : ℕ} [NeZero n] (ℓ : ZMod n) :
    (¬ ∃ f : ℕ → Cfg n, f 0 = anonCount.initCfg (leaderInput ℓ) ∧
        ∀ k, anonCount.Step (oriented n) (f k) (f (k + 1))) ∧
    ∀ c : Cfg n, anonCount.Reach (oriented n) (leaderInput ℓ) c →
      ∃ c', Relation.ReflTransGen (anonCount.Step (oriented n)) c c' ∧
        anonCount.Final (oriented n) c' := by
  have hB : ∀ c, Podc.ContentOblivious.Reach (oriented n) anonCount.toAlgo
      (fun v => Encodable.encode (leaderInput ℓ v)) c → totalSent c ≤ totalPulses n :=
    fun c hc => anonCount_totalSent_le ℓ c hc
  refine ⟨?_, fun c hc => exists_final hB hc⟩
  rintro ⟨f, h0, hf⟩
  refine no_infinite_execution hB ⟨f, ?_, hf⟩
  rw [h0, ← Prog.initCfg_eq]

/-- The counting procedure returns `(n, clockwise distance from ℓ)` at every node. -/
theorem anonCount_returns {n : ℕ} [NeZero n] (ℓ : ZMod n) :
    anonCount.Returns (oriented n) (leaderInput ℓ) (fun v => (n, (v - ℓ).val)) :=
  fun c hc hf v => (anonCount_final ℓ c hc hf).2.1 v

end Podc.ContentOblivious.AnonCounting
