import Papers.PODC2022.WearLeveling.Safety
import Papers.PODC2022.WearLeveling.LockFree

/-!
# Theorem 4.3: endurance of the counter

Words of persistent memory wear out after `T` write-backs (`Wear`): later write-backs of a word
store an arbitrary value (`junk`).

* `wear_le`, `exec_eq_ideal`: in every execution with at most `k·T` invocations, every word is
  written back at most `T` times, so the execution is the same as in the ideal model, and the
  counter is strictly linearizable and lock-free (`theorem_4_3`). This is the paper's argument.
* `hist_eq_ideal_succ`: even with `k·T + 1` invocations the *history* is the same as in the ideal
  model: the `(T+1)`-st write-back of `A[0]` can only happen after all `k·T + 1` operations
  performed their successful CAS, and afterwards nobody reads the memory again. So the counter
  maintains safety and liveness in all executions with `k·T + 1` FAIs (`guarantees_kT_succ`).
-/

namespace Podc.WearLeveling

set_option linter.unusedSectionVars false

open Cslib.SharedMemory Cslib.SharedMemory.Persistent Alg

variable {k : ℕ} [NeZero k] {P : Type} [DecidableEq P]

/-- The ids of `L` are distinct numbers below `cnt`, so `|L| ≤ cnt`. -/
lemma GInv.length_le_cnt {C : Cfg (counter k) P} {h L m} (hG : GInv C h L m) :
    L.length ≤ C.cnt := by
  have hsub : (L.map Prod.fst).toFinset ⊆ Finset.range C.cnt := by
    intro b hb; simpa using hG.ids_lt b (by simpa using hb)
  have := Finset.card_le_card hsub
  rw [List.toFinset_card_of_nodup hG.lin.nodup] at this
  simpa using this

/-- A pending operation that is not in `L` leaves room: `|L| + 1 ≤ cnt`. -/
lemma GInv.length_succ_le_cnt {C : Cfg (counter k) P} {h L m} (hG : GInv C h L m) {a : ℕ}
    (ha : a ∉ L.map Prod.fst) (hlt : a < C.cnt) : L.length + 1 ≤ C.cnt := by
  have hsub : (a :: L.map Prod.fst).toFinset ⊆ Finset.range C.cnt := by
    intro b hb
    simp only [List.toFinset_cons, Finset.mem_insert, List.mem_toFinset] at hb
    rcases hb with rfl | hb
    · simpa using hlt
    · simpa using hG.ids_lt b hb
  have := Finset.card_le_card hsub
  rw [List.toFinset_card_of_nodup (List.nodup_cons.2 ⟨ha, hG.lin.nodup⟩)] at this
  simpa using this

/-- Under the invariant, a dirty word `i` has been written back fewer times than the number of
invocations divided by `k`: precisely, `wear i * k + i + 1 ≤ cnt`. -/
lemma GInv.dirty_wear {C : Cfg (counter k) P} {h L m} (hG : GInv C h L m) {i : Fin k}
    (hi : C.dirty i = true) : C.wear i * k + i.val + 1 ≤ C.cnt ∧ C.wear i * k + i.val + 1 = L.length
    := by
  obtain ⟨hL, it, hm⟩ := (hG.dirty_iff i).1 hi
  have hw : C.wear i = it := by rw [hG.wear_eq, hm, stair_pos_self]
  have := hG.length_le_cnt
  rw [hw]; omega

/-- Two wear models agree on a configuration where no dirty word is worn out. -/
lemma step1_wear_congr {W W' : Wear k ℕ} {C : Cfg (counter k) P}
    (hC : ∀ i, C.dirty i = true → (C.wear i : ℕ∞) < W.T ∧ (C.wear i : ℕ∞) < W'.T)
    (e : Ev k P Unit) : step1 W C e = step1 W' C e := by
  have hwb : ∀ i, writeBack W C i = writeBack W' C i := by
    intro i
    unfold writeBack
    by_cases hd : C.dirty i = true
    · simp [hd, (hC i hd).1, (hC i hd).2]
    · simp [hd]
  cases e with
  | inv p o => rfl
  | evict i => simp [step1, hwb]
  | crash => rfl
  | step p =>
    cases hp : C.ts p with
    | idle => simp [step1, hp]
    | run a o l =>
      cases l with
      | cas it idx => by_cases hc : C.cache idx = it <;> simp [step1, hp, hc]
      | _ => simp [step1, hp, hwb]

/-- Executions with at most `k·T` invocations are executions of the ideal model. -/
theorem exec_eq_ideal (T : ℕ) (junk : Fin k → ℕ → ℕ → ℕ → ℕ) (es : List (Ev k P Unit))
    (hes : (exec ⟨T, junk⟩ (initCfg (counter k) P) es).1.cnt ≤ k * T) :
    exec ⟨T, junk⟩ (initCfg (counter k) P) es = exec (W₀ k) (initCfg (counter k) P) es := by
  induction es using List.reverseRecOn with
  | nil => rfl
  | append_singleton es e ih =>
    rw [exec_concat, exec_concat]
    rw [exec_concat] at hes
    dsimp only at hes
    have hle : (exec ⟨T, junk⟩ (initCfg (counter k) P) es).1.cnt ≤ k * T := by
      have := cnt_step1 ⟨T, junk⟩ (exec ⟨T, junk⟩ (initCfg (counter k) P) es).1 e; omega
    have heq := ih hle
    rw [heq]
    rw [heq] at hle
    obtain ⟨L, m, hC⟩ := cInv_exec (k := k) (P := P) es
    have hcongr : step1 ⟨T, junk⟩ (exec (W₀ k) (initCfg (counter k) P) es).1 e =
        step1 (W₀ k) (exec (W₀ k) (initCfg (counter k) P) es).1 e := by
      apply step1_wear_congr
      intro i hi
      obtain ⟨h1, -⟩ := hC.1.dirty_wear hi
      refine ⟨?_, by simp [Wear.ideal]⟩
      show (_ : ℕ∞) < (T : ℕ∞)
      rw [Nat.cast_lt]
      by_contra hT
      push Not at hT
      have := Nat.mul_le_mul_right k hT
      rw [Nat.mul_comm T k] at this
      omega
    rw [hcongr]

/-- In the ideal model, every word is written back at most `⌈cnt / k⌉` times; with at most `k·T`
invocations, at most `T` times. -/
theorem wear_le (T : ℕ) (es : List (Ev k P Unit))
    (hes : (exec (W₀ k) (initCfg (counter k) P) es).1.cnt ≤ k * T) (i : Fin k) :
    (exec (W₀ k) (initCfg (counter k) P) es).1.wear i ≤ T := by
  obtain ⟨L, m, hC⟩ := cInv_exec (k := k) (P := P) es
  have hG := hC.1
  rw [hG.wear_eq, stair_le_iff]
  have := hG.length_le_cnt
  have := hG.m_le
  have : T * k = k * T := Nat.mul_comm _ _
  omega

/-! ### `k·T + 1` invocations -/

/-- Local states before the successful CAS (lines 1–5 and 9–13). -/
def PreCAS : TS Unit (CL k) → Prop
  | .run _ _ .rd => True
  | .run _ _ (.fl _) => True
  | .run _ _ (.cas _ _) => True
  | .run _ _ (.flF _ _) => True
  | _ => False

/-- The faulty and the ideal run have diverged (only in persistent memory, wear and, after a
crash, the cache): all `k·T + 1` operations have been invoked and have performed their
successful CAS. -/
structure Diverged (T : ℕ) (D C : Cfg (counter k) P) : Prop where
  ts : D.ts = C.ts
  cnt : D.cnt = C.cnt
  dirty : D.dirty = C.dirty
  full : C.cnt = k * T + 1
  noPre : ∀ p, ¬ PreCAS (C.ts p)

lemma Diverged.step1 {T : ℕ} {W : Wear k ℕ} {D C : Cfg (counter k) P} (hD : Diverged T D C)
    (e : Ev k P Unit) (hcnt : (step1 W D e).1.cnt ≤ k * T + 1) :
    Diverged T (step1 W D e).1 (step1 (W₀ k) C e).1 ∧ (step1 W D e).2 = (step1 (W₀ k) C e).2 := by
  have hts := hD.ts
  cases e with
  | inv p o =>
    cases hp : C.ts p with
    | idle =>
      have hp' : D.ts p = .idle := by rw [hts, hp]
      simp [Alg.step1, hp'] at hcnt
      have := hD.cnt; have := hD.full; omega
    | run a o' l =>
      have hp' : D.ts p = .run a o' l := by rw [hts, hp]
      simpa [Alg.step1, hp, hp'] using hD
  | evict i =>
    refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, rfl⟩
    · simp [Alg.step1, writeBack_ts, hts]
    · simp [Alg.step1, writeBack_cnt, hD.cnt]
    · simp [Alg.step1, writeBack_dirty, hD.dirty]
    · simp [Alg.step1, writeBack_cnt, hD.full]
    · simpa [Alg.step1, writeBack_ts] using hD.noPre
  | crash =>
    exact ⟨⟨by simp [Alg.step1], by simp [Alg.step1, hD.cnt], by simp [Alg.step1],
      by simp [Alg.step1, hD.full], by simp [Alg.step1, PreCAS]⟩, rfl⟩
  | step p =>
    cases hp : C.ts p with
    | idle =>
      have hp' : D.ts p = .idle := by rw [hts, hp]
      simpa [Alg.step1, hp, hp'] using hD
    | run a o l =>
      have hp' : D.ts p = .run a o l := by rw [hts, hp]
      have hnp := hD.noPre p
      rw [hp] at hnp
      cases l with
      | rd => exact absurd trivial hnp
      | fl _ => exact absurd trivial hnp
      | cas _ _ => exact absurd trivial hnp
      | flF _ _ => exact absurd trivial hnp
      | flS it idx =>
        refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
        · simp [Alg.step1, hp, hp', counter, hts]
        · rw [step_flS W hp', step_flS _ hp]; simp only; rw [writeBack_cnt, writeBack_cnt, hD.cnt]
        · rw [step_flS W hp', step_flS _ hp]; simp only
          rw [writeBack_dirty, writeBack_dirty, hD.dirty]
        · rw [step_flS _ hp]; simp only; rw [writeBack_cnt, hD.full]
        · intro q
          simp only [Alg.step1, hp, counter]
          by_cases hqp : q = p
          · subst hqp; simp [PreCAS]
          · simpa [Function.update_of_ne hqp] using hD.noPre q
        · simp [Alg.step1, hp, hp', counter]
      | ret it idx =>
        refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
        · simp [Alg.step1, hp, hp', counter, hts]
        · simp [Alg.step1, hp, hp', counter, hD.cnt]
        · simp [Alg.step1, hp, hp', counter, hD.dirty]
        · simp [Alg.step1, hp, hp', counter, hD.full]
        · intro q
          simp only [Alg.step1, hp, counter]
          by_cases hqp : q = p
          · subst hqp; simp [PreCAS]
          · simpa [Function.update_of_ne hqp] using hD.noPre q
        · simp [Alg.step1, hp, hp', counter]

/-- If a worn-out dirty word is written back in an execution with at most `k·T + 1`
invocations, then all operations have been invoked and have done their successful CAS. -/
lemma diverged_of_worn {T : ℕ} {C : Cfg (counter k) P} {h L m} (hC : CInv C h L m)
    (hcnt : C.cnt ≤ k * T + 1) {i : Fin k} (hi : C.dirty i = true) (hw : T ≤ C.wear i) :
    Diverged T C C := by
  have hG := hC.1
  obtain ⟨-, h2⟩ := hG.dirty_wear hi
  have h3 := hG.length_le_cnt
  have h4 := Nat.mul_le_mul_right k hw
  rw [Nat.mul_comm T k] at h4
  have hfull : C.cnt = k * T + 1 := by omega
  refine ⟨rfl, rfl, rfl, hfull, fun p hp => ?_⟩
  cases hq : C.ts p with
  | idle => rw [hq] at hp; exact hp
  | run a o l =>
    have hl := hC.2 p a o l hq
    have hlt := hG.hinv.run_lt hq
    have hnot : a ∉ L.map Prod.fst := by
      rw [hq] at hp
      cases l with
      | rd => exact hl
      | fl _ => exact hl.1
      | cas _ _ => exact hl.1
      | flF _ _ => exact hl.1
      | flS _ _ => exact hp.elim
      | ret _ _ => exact hp.elim
    have := hG.length_succ_le_cnt hnot hlt
    omega

/-- The faulty run simulates the ideal run as long as at most `k·T + 1` operations are
invoked: the configurations are equal or have `Diverged`, and the histories are equal. -/
theorem sim_exec (T : ℕ) (junk : Fin k → ℕ → ℕ → ℕ → ℕ) (es : List (Ev k P Unit))
    (hes : (exec ⟨T, junk⟩ (initCfg (counter k) P) es).1.cnt ≤ k * T + 1) :
    ((exec ⟨T, junk⟩ (initCfg (counter k) P) es).1 = (exec (W₀ k) (initCfg (counter k) P) es).1 ∨
      Diverged T (exec ⟨T, junk⟩ (initCfg (counter k) P) es).1
        (exec (W₀ k) (initCfg (counter k) P) es).1) ∧
    (exec ⟨T, junk⟩ (initCfg (counter k) P) es).2 = (exec (W₀ k) (initCfg (counter k) P) es).2 := by
  induction es using List.reverseRecOn with
  | nil => exact ⟨Or.inl rfl, rfl⟩
  | append_singleton es e ih =>
    rw [exec_concat, exec_concat]
    rw [exec_concat] at hes
    dsimp only at hes ⊢
    set D := (exec ⟨T, junk⟩ (initCfg (counter k) P) es).1
    set C := (exec (W₀ k) (initCfg (counter k) P) es).1
    have hle : D.cnt ≤ k * T + 1 := by
      have := cnt_step1 ⟨T, junk⟩ D e; omega
    obtain ⟨hR, hH⟩ := ih hle
    rw [hH]
    obtain ⟨L, m, hC⟩ := cInv_exec (k := k) (P := P) es
    rcases hR with hDC | hDiv
    · rw [hDC] at hes hle ⊢
      by_cases hworn : ∃ i, C.dirty i = true ∧ T ≤ C.wear i
      · obtain ⟨i, hi, hw⟩ := hworn
        have hDv := diverged_of_worn hC hle hi hw
        obtain ⟨h1, h2⟩ := hDv.step1 (W := ⟨T, junk⟩) e hes
        exact ⟨Or.inr h1, by rw [h2]⟩
      · push Not at hworn
        have hcongr : step1 ⟨T, junk⟩ C e = step1 (W₀ k) C e := by
          apply step1_wear_congr
          intro i hi
          refine ⟨?_, by simp [Wear.ideal]⟩
          show (_ : ℕ∞) < (T : ℕ∞)
          exact Nat.cast_lt.2 (hworn i hi)
        rw [hcongr]
        exact ⟨Or.inl rfl, rfl⟩
    · obtain ⟨h1, h2⟩ := hDiv.step1 (W := ⟨T, junk⟩) e hes
      exact ⟨Or.inr h1, by rw [h2]⟩

/-- With at most `k·T + 1` invocations, the history is the same as in the ideal model. -/
theorem hist_eq_ideal_succ (T : ℕ) (junk : Fin k → ℕ → ℕ → ℕ → ℕ) (es : List (Ev k P Unit))
    (hes : invCount (hist (counter k) P ⟨T, junk⟩ es) ≤ k * T + 1) :
    hist (counter k) P ⟨T, junk⟩ es = hist (counter k) P (W₀ k) es := by
  rw [invCount_hist] at hes
  exact (sim_exec T junk es hes).2

/-- Lock-freedom (Theorem 4.2) holds in every wear model, so liveness is never lost. -/
lemma liveUpTo [Finite P] (W : Wear k ℕ) (N : ℕ∞) : LiveUpTo (counter k) P W N :=
  fun e _ => theorem_4_2 W e trivial

/-- **Theorem 4.3** of [Liu–Golab, PODC'22] (first half, the paper's claim): if every word
survives `T` write-backs, the counter remains strictly linearizable and lock-free in all
executions with at most `k·T` FAI invocations; in these executions no word is written back
more than `T` times (`wear_le`), so they are executions of the ideal model (`exec_eq_ideal`). -/
theorem theorem_4_3 [Finite P] (T : ℕ) : GuaranteesUpTo (counter k) P T (k * T : ℕ) := by
  intro junk
  refine ⟨fun es hes => ?_, liveUpTo _ _⟩
  have hes' : invCount (hist (counter k) P ⟨T, junk⟩ es) ≤ k * T := by exact_mod_cast hes
  rw [invCount_hist] at hes'
  have := exec_eq_ideal T junk es hes'
  unfold hist; rw [this]
  exact theorem_4_1 es

/-- **The counter even tolerates `k·T + 1` FAIs**: if every word survives `T` write-backs
(whatever worn-out words store), all executions with at most `k·T + 1` FAI invocations are
strictly linearizable and lock-free. Hence the second half of Definition 2.1 ("but not in some
execution with `k·T + 1` updates") fails for `k·T`. -/
theorem guarantees_kT_succ [Finite P] (T : ℕ) :
    GuaranteesUpTo (counter k) P T (k * T + 1 : ℕ) := by
  intro junk
  refine ⟨fun es hes => ?_, liveUpTo _ _⟩
  have hes' : invCount (hist (counter k) P ⟨T, junk⟩ es) ≤ k * T + 1 := by exact_mod_cast hes
  rw [hist_eq_ideal_succ T junk es hes']
  exact theorem_4_1 es

end Podc.WearLeveling
