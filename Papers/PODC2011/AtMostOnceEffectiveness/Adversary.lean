import Papers.PODC2011.AtMostOnceEffectiveness.Progress

/-!
# The adversary of Theorem 4.4: `KK_β` may perform only `n − (β + m − 2)` jobs

For `m ≥ 1` processes, `β ≥ m` and `n ≥ β + m − 1`, we construct a fair run of `KK_β` with
`m − 1` crashes in which at most `n − (β + m − 2)` jobs are performed (the upper-bound half of
Theorem 4.4 of the paper). We write the number of processes as `m + 1`; the survivor is the
last process `s = m` (`Fin.last m`), the others `0, …, m − 1` crash.

1. **Phase 1** (times `0, …, 2m − 1`): each process `i < m` takes two steps, `compNext` and
   `setNext`. Since `FREE_i = {1, …, n}` and `TRY_i = ∅`, it announces the job
   `k_i = kIdx (m + 1) i n` (`kj`), the element of rank `k_i` of `{1, …, n}`. It is then never
   scheduled again (it crashes in status `gatherTry`).
2. **Phase 2** (times `≥ 2m`): the survivor is scheduled whenever it has not terminated.

Because `n ≥ 2m + 1`, `i ↦ k_i` is strictly increasing on `0, …, m`, so `STUCK = {k_i | i < m}`
has `m` elements and does not contain the survivor's first choice `k_m`. In every iteration of
the survivor, `TRY_s = STUCK` is gathered, the `done` lines of the crashed processes are empty,
and the survivor's job lies outside `STUCK`. A job is chosen only while
`|FREE_s \ TRY_s| ≥ β` (or as the first job), so the survivor's jobs never exceed
`n − m − (β − 1)` (invariant `Solo`). The run is fair with crash set `{0, …, m − 1}`, since at
every time of phase 2 the survivor either steps or has terminated.

Wait-freedom (termination) is not needed for the upper bound; with it, the run performs exactly
`n − (β + m − 2)` jobs (`exists_fair_run_do_eq`, by Lemma 4.2).
-/

set_option linter.unusedSectionVars false

namespace Podc.AtMostOnceEffectiveness

/-! ## Runs from a fixed schedule -/

section Greedy

variable {m : ℕ} {R V L : Type} [DecidableEq R] (A : Alg m R V L) (σ : ℕ → Fin m)

open Classical in
/-- Configurations of the run that schedules `σ k` at time `k` unless it has terminated. -/
noncomputable def adv4GreedyCfg : ℕ → Config m R V L
  | 0 => A.init
  | k + 1 => if A.Halted (adv4GreedyCfg k) (σ k) then adv4GreedyCfg k
      else (A.step (adv4GreedyCfg k) (σ k)).getD (adv4GreedyCfg k)

open Classical in
/-- The run that schedules `σ k` at time `k` unless it has terminated (then it stutters). -/
noncomputable def adv4GreedyRun : A.Run where
  cfg := adv4GreedyCfg A σ
  ev k := if A.Halted (adv4GreedyCfg A σ k) (σ k) then none else some (σ k)
  cfg_zero := rfl
  cfg_succ k := by
    rw [adv4GreedyCfg.eq_2]
    split_ifs with h
    · rfl
    · obtain ⟨C', hC'⟩ := Alg.step_isSome_of_not_halted h
      simp [Alg.stepO, hC']

lemma adv4GreedyRun_ev_of_halted {k : ℕ} (h : A.Halted ((adv4GreedyRun A σ).cfg k) (σ k)) :
    (adv4GreedyRun A σ).ev k = none := by
  change A.Halted (adv4GreedyCfg A σ k) (σ k) at h
  simp [adv4GreedyRun, h]

lemma adv4GreedyRun_ev_of_not_halted {k : ℕ}
    (h : ¬ A.Halted ((adv4GreedyRun A σ).cfg k) (σ k)) :
    (adv4GreedyRun A σ).ev k = some (σ k) := by
  change ¬ A.Halted (adv4GreedyCfg A σ k) (σ k) at h
  simp [adv4GreedyRun, h]

end Greedy

namespace Adversary

open Function Finset

variable {m n β : ℕ}

/-- The job announced by process `i` when `FREE = {1, …, n}` (`m + 1` processes). -/
def kj (m n i : ℕ) : ℕ := kIdx (m + 1) i n

/-- The jobs announced by the crashed processes `0, …, m − 1`. -/
def stuck (m n : ℕ) : Finset ℕ := (range m).image (kj m n)

lemma kj_eq (hn : 2 * m + 1 ≤ n) (i : ℕ) : kj m n i = i * (n - m) / (m + 1) + 1 := by
  unfold kj kIdx
  split_ifs with h
  · simp
  · omega

lemma kj_strictMono (hn : 2 * m + 1 ≤ n) : StrictMono (kj m n) := by
  apply strictMono_nat_of_lt_succ
  intro i
  rw [kj_eq hn, kj_eq hn]
  have h1 : (i * (n - m) + (m + 1)) / (m + 1) ≤ (i + 1) * (n - m) / (m + 1) :=
    Nat.div_le_div_right (by rw [add_mul, one_mul]; omega)
  rw [Nat.add_div_right _ (by omega)] at h1
  omega

lemma kj_mem (hn : 2 * m + 1 ≤ n) {i : ℕ} (hi : i ≤ m) : kj m n i ∈ Icc 1 n := by
  rw [kj_eq hn, mem_Icc]
  refine ⟨Nat.le_add_left _ _, ?_⟩
  have : i * (n - m) / (m + 1) < n - m := by
    rw [Nat.div_lt_iff_lt_mul (by omega)]
    have h1 : i * (n - m) ≤ m * (n - m) := Nat.mul_le_mul_right _ hi
    have h2 : 0 < n - m := by omega
    nlinarith
  omega

lemma stuck_subset (hn : 2 * m + 1 ≤ n) : stuck m n ⊆ Icc 1 n := by
  intro x hx
  simp only [stuck, mem_image, mem_range] at hx
  obtain ⟨i, hi, rfl⟩ := hx
  exact kj_mem hn hi.le

lemma card_stuck (hn : 2 * m + 1 ≤ n) : (stuck m n).card = m := by
  unfold stuck
  rw [card_image_of_injective _ (kj_strictMono hn).injective, card_range]

lemma kj_not_mem_stuck (hn : 2 * m + 1 ≤ n) : kj m n m ∉ stuck m n := by
  simp only [stuck, mem_image, mem_range, not_exists, not_and]
  intro i hi h
  exact absurd ((kj_strictMono hn).injective h) (by omega)

lemma card_Icc_sdiff_stuck (hn : 2 * m + 1 ≤ n) : (Icc 1 n \ stuck m n).card = n - m := by
  rw [card_sdiff_of_subset (stuck_subset hn), card_stuck hn, Nat.card_Icc]; omega

lemma rank_Icc {k : ℕ} (hk : k ∈ Icc 1 n) : rank (Icc 1 n) k = k := by
  rw [mem_Icc] at hk
  refine rank_eq_of_below (mem_Icc.mpr hk) hk.1 ?_
  unfold below
  have : (Icc 1 n).filter (· < k) = Ico 1 k := by ext x; simp; omega
  rw [this, Nat.card_Ico]

/-! ## Phase 1: the crashed processes announce their jobs -/

/-- Process `i` after its `compNext` step of phase 1. -/
def setLoc (m n i : ℕ) : LState := ⟨.setNext, ∅, ∅, fun _ => 1, kj m n i, 0⟩

/-- Process `i` after phase 1 (crashed in status `gatherTry`). -/
def stuckLoc (m n i : ℕ) : LState := ⟨.gatherTry, ∅, ∅, fun _ => 1, kj m n i, 0⟩

/-- The local state of process `i` at time `t ≤ 2m` of phase 1. -/
def phLoc (m n t i : ℕ) : LState :=
  if 2 * i + 2 ≤ t then stuckLoc m n i
  else if 2 * i + 1 = t then setLoc m n i
  else LState.init

lemma phLoc_eq_init {t i : ℕ} (h : t ≤ 2 * i) : phLoc m n t i = LState.init := by
  unfold phLoc; split_ifs <;> first | rfl | omega

lemma phLoc_eq_set {i : ℕ} : phLoc m n (2 * i + 1) i = setLoc m n i := by
  unfold phLoc; split_ifs <;> first | rfl | omega

/-- The invariant of phase 1 at time `t`. -/
structure Phase1 (m n t : ℕ) (C : Config (m + 1) Reg ℕ LState) : Prop where
  log : C.log = []
  loc : ∀ p : Fin (m + 1), C.loc p = phLoc m n t p.val
  nxtM : ∀ i, C.mem (.next i) = if 2 * i + 2 ≤ t then kj m n i else 0
  doneM : ∀ q j, C.mem (.done q j) = 0

@[simp] lemma free_init : free n LState.init = Icc 1 n := by simp [free, LState.init]

lemma phase1_zero : Phase1 m n 0 (kk (m + 1) n β).init where
  log := rfl
  loc p := by simp [phLoc, Alg.init, kk]
  nxtM i := by simp [Alg.init, kk]
  doneM q j := rfl

lemma phase1_step (hβ : m + 1 ≤ β) (hn : β + m ≤ n) {t : ℕ} (ht : t < 2 * m)
    {C C' : Config (m + 1) Reg ℕ LState} (hC : Phase1 m n t C) (p : Fin (m + 1))
    (hp : p.val = t / 2) (hs : KStep (m + 1) n β C p C') : Phase1 m n (t + 1) C' := by
  have hn2 : 2 * m + 1 ≤ n := by omega
  have hlp := hC.loc p
  have hother : ∀ q : Fin (m + 1), q ≠ p → phLoc m n t q.val = phLoc m n (t + 1) q.val := by
    intro q hq
    have : q.val ≠ p.val := fun e => hq (Fin.ext e)
    simp only [phLoc]; split_ifs <;> first | rfl | omega
  rcases Nat.even_or_odd' t with ⟨j, rfl | rfl⟩
  · have hj : p.val = j := by omega
    have hl : C.loc p = LState.init := by rw [hlp, hj, phLoc_eq_init (by omega)]
    cases hs with
    | compNext h hb =>
      refine ⟨hC.log, fun q => ?_, fun i => ?_, hC.doneM⟩
      · by_cases hq : q = p
        · subst hq
          have hk := kj_mem (m := m) (i := j) hn2 (by omega)
          rw [hj, phLoc_eq_set]
          simp only [update_self, hl, free_init]
          rw [Nat.card_Icc, Nat.add_sub_cancel, show kIdx (m + 1) j n = kj m n j from rfl,
            show LState.init.tryS = ∅ from rfl, sdiff_empty, rank_Icc hk]
          rfl
        · simp only [update_of_ne hq, hC.loc q, hother q hq]
      · simp only [hC.nxtM i]; split_ifs <;> first | rfl | omega
    | finish h hb =>
      simp only [hl, free_init] at hb
      simp [LState.init] at hb; omega
    | _ => exact absurd ‹(C.loc p).status = _› (by simp [hl, LState.init])
  · have hj : p.val = j := by omega
    have hl : C.loc p = setLoc m n j := by rw [hlp, hj, phLoc_eq_set]
    cases hs with
    | setNext h =>
      refine ⟨hC.log, fun q => ?_, fun i => ?_, fun q i => ?_⟩
      · by_cases hq : q = p
        · subst hq
          simp only [update_self, hl, hj, phLoc, setLoc, stuckLoc]
          split_ifs <;> first | rfl | omega
        · simp only [update_of_ne hq, hC.loc q, hother q hq]
      · dsimp only
        by_cases hi : i = j
        · subst hi; simp [hj, hl, setLoc]
        · rw [update_of_ne (by simp [hj]; omega), hC.nxtM i]
          split_ifs <;> first | rfl | omega
      · dsimp only
        rw [update_of_ne (by simp), hC.doneM]
    | _ => exact absurd ‹(C.loc p).status = _› (by simp [hl, setLoc])

/-! ## Phase 2: the survivor runs solo -/

/-- The survivor has chosen its job `NEXT_s` in the current iteration: the job lies outside
`STUCK`, and the jobs recorded so far plus this one stay within the bound. -/
def Act (m n β : ℕ) (σ : LState) : Prop :=
  σ.doneS.card + 1 ≤ n - (β + m - 1) ∧ σ.nxt ∈ Icc 1 n ∧ σ.nxt ∉ stuck m n

/-- The survivor's local invariant, by status. -/
def SOK (m n β : ℕ) (σ : LState) : Prop :=
  match σ.status with
  | .compNext => (σ.tryS = stuck m n ∨ (σ.tryS = ∅ ∧ σ.doneS = ∅)) ∧
      σ.doneS.card ≤ n - (β + m - 1)
  | .finished => σ.doneS.card ≤ n - (β + m - 1)
  | .setNext => σ.q = 0 ∧ σ.tryS = ∅ ∧ Act m n β σ
  | .gatherTry => σ.q < m + 1 ∧ σ.tryS = (range (min σ.q m)).image (kj m n) ∧ Act m n β σ
  | _ => σ.tryS = stuck m n ∧ Act m n β σ

/-- The invariant of phase 2 (the survivor is `Fin.last m`). -/
structure Solo (m n β : ℕ) (C : Config (m + 1) Reg ℕ LState) : Prop where
  nxtM : ∀ i < m, C.mem (.next i) = kj m n i
  doneM : ∀ q j, q ≠ m → C.mem (.done q j) = 0
  log : ∀ x ∈ C.log.map Prod.snd, x ∈ (C.loc (Fin.last m)).doneS ∨
    ((C.loc (Fin.last m)).status = .done ∧ x = (C.loc (Fin.last m)).nxt)
  sub : (C.loc (Fin.last m)).doneS ⊆ Icc 1 n \ stuck m n
  sok : SOK m n β (C.loc (Fin.last m))

lemma SOK.card_le {σ : LState} (h : SOK m n β σ) : σ.doneS.card ≤ n - (β + m - 1) := by
  unfold SOK Act at h
  split at h
  · exact h.2
  · exact h
  · omega
  · omega
  · omega

lemma solo_of_phase1 {C : Config (m + 1) Reg ℕ LState}
    (hC : Phase1 m n (2 * m) C) : Solo m n β C := by
  have hl : C.loc (Fin.last m) = LState.init := by
    rw [hC.loc, Fin.val_last, phLoc_eq_init le_rfl]
  refine ⟨fun i hi => ?_, fun q j _ => hC.doneM q j, fun x hx => ?_, ?_, ?_⟩
  · rw [hC.nxtM]; simp [show 2 * i + 2 ≤ 2 * m by omega]
  · simp [hC.log] at hx
  · rw [hl]; simp [LState.init]
  · rw [hl]; simp [SOK, LState.init]

lemma solo_step (hβ : m + 1 ≤ β) (hn : β + m ≤ n) {C C' : Config (m + 1) Reg ℕ LState}
    (hC : Solo m n β C) (hs : KStep (m + 1) n β C (Fin.last m) C') : Solo m n β C' := by
  have hn2 : 2 * m + 1 ≤ n := by omega
  have hσ := hC.sok
  have hlog := hC.log
  have hsub := hC.sub
  cases hs with
  | compNext h hb =>
    simp only [SOK, h] at hσ
    refine ⟨hC.nxtM, hC.doneM, fun x hx => ?_, by simpa using hsub, ?_⟩
    · rcases hlog x hx with h' | ⟨h', _⟩
      · left; simpa using h'
      · simp [h] at h'
    · simp only [update_self, SOK, Act, Fin.val_last, true_and]
      rcases hσ.1 with ht | ⟨ht, hd⟩
      · rw [ht] at hb ⊢
        have heq : free n (C.loc (Fin.last m)) \ stuck m n =
            (Icc 1 n \ stuck m n) \ (C.loc (Fin.last m)).doneS := by
          unfold free; exact sdiff_right_comm _ _ _
        have hc : (free n (C.loc (Fin.last m)) \ stuck m n).card =
            n - m - (C.loc (Fin.last m)).doneS.card := by
          rw [heq, card_sdiff_of_subset hsub, card_Icc_sdiff_stuck hn2]
        have hne : (free n (C.loc (Fin.last m)) \ stuck m n).Nonempty := by
          rw [← card_pos]; omega
        have hmem := rank_mem hne (kIdx (m + 1) m (free n (C.loc (Fin.last m))).card)
        have key : ∀ x ∈ free n (C.loc (Fin.last m)) \ stuck m n, x ∈ Icc 1 n ∧ x ∉ stuck m n := by
          intro x hx; simp only [free, mem_sdiff] at hx; exact ⟨hx.1.1, hx.2⟩
        exact ⟨by omega, key _ hmem⟩
      · have hk := kj_mem (m := m) (i := m) hn2 le_rfl
        simp only [ht, hd, free, sdiff_empty, card_empty, Nat.card_Icc, Nat.add_sub_cancel]
        rw [show kIdx (m + 1) m n = kj m n m from rfl, rank_Icc hk]
        exact ⟨by omega, hk, kj_not_mem_stuck hn2⟩
  | finish h hb =>
    simp only [SOK, h] at hσ
    refine ⟨hC.nxtM, hC.doneM, fun x hx => ?_, by simpa using hsub, ?_⟩
    · rcases hlog x hx with h' | ⟨h', _⟩
      · left; simpa using h'
      · simp [h] at h'
    · simp only [update_self, SOK]; exact hσ.2
  | setNext h =>
    simp only [SOK, h] at hσ
    refine ⟨fun i hi => ?_, fun q j hq => ?_, fun x hx => ?_, by simpa using hsub, ?_⟩
    · dsimp only; rw [update_of_ne (by simp; omega)]; exact hC.nxtM i hi
    · dsimp only; rw [update_of_ne (by simp)]; exact hC.doneM q j hq
    · rcases hlog x hx with h' | ⟨h', _⟩
      · left; simpa using h'
      · simp [h] at h'
    · simp only [update_self, SOK, hσ.1, hσ.2.1]
      exact ⟨by omega, by simp, hσ.2.2⟩
  | tryRead h hq =>
    simp only [SOK, h] at hσ
    obtain ⟨hq1, ht, hact⟩ := hσ
    have hqm : (C.loc (Fin.last m)).q < m := by simp at hq; omega
    have hk1 : 0 < kj m n (C.loc (Fin.last m)).q := by rw [kj_eq hn2]; exact Nat.succ_pos _
    refine ⟨hC.nxtM, hC.doneM, fun x hx => ?_, by simpa using hsub, ?_⟩
    · rcases hlog x hx with h' | ⟨h', _⟩
      · left; simpa using h'
      · simp [h] at h'
    · have hq2 : (C.loc (Fin.last m)).q + 1 < m + 1 := by omega
      simp only [update_self, SOK, adv_status, adv_q, adv_tryS, hq2, h, hC.nxtM _ hqm, addTry,
        hk1, ↓reduceIte]
      refine ⟨trivial, ?_, by simpa [Act] using hact⟩
      rw [ht, min_eq_left hqm.le, min_eq_left (show (C.loc (Fin.last m)).q + 1 ≤ m by omega),
        range_add_one, image_insert]
  | trySkip h hq =>
    simp only [SOK, h] at hσ
    obtain ⟨hq1, ht, hact⟩ := hσ
    have hqm : (C.loc (Fin.last m)).q = m := by simpa using hq
    refine ⟨hC.nxtM, hC.doneM, fun x hx => ?_, by simpa using hsub, ?_⟩
    · rcases hlog x hx with h' | ⟨h', _⟩
      · left; simpa using h'
      · simp [h] at h'
    · simp only [update_self, SOK, adv_status, adv_tryS, hqm, lt_irrefl, ↓reduceIte]
      refine ⟨?_, by simpa [Act] using hact⟩
      rw [ht, hqm, min_self]; rfl
  | doneRead h hq hpos hv =>
    rw [hC.doneM _ _ (by simpa using hq)] at hv
    exact absurd hv (lt_irrefl 0)
  | doneAdv h hq =>
    simp only [SOK, h] at hσ
    refine ⟨hC.nxtM, hC.doneM, fun x hx => ?_, by simpa using hsub, ?_⟩
    · rcases hlog x hx with h' | ⟨h', _⟩
      · left; simpa using h'
      · simp [h] at h'
    · simp only [update_self, SOK, adv_status]
      split_ifs
      · simp only [h, adv_tryS]; exact ⟨hσ.1, by simpa [Act] using hσ.2⟩
      · simp only [adv_tryS]; exact ⟨hσ.1, by simpa [Act] using hσ.2⟩
  | checkOk h h1 h2 =>
    simp only [SOK, h] at hσ
    refine ⟨hC.nxtM, hC.doneM, fun x hx => ?_, by simpa using hsub, ?_⟩
    · rcases hlog x hx with h' | ⟨h', _⟩
      · left; simpa using h'
      · simp [h] at h'
    · simp only [update_self, SOK]; exact hσ
  | checkFail h h1 =>
    simp only [SOK, h] at hσ
    refine ⟨hC.nxtM, hC.doneM, fun x hx => ?_, by simpa using hsub, ?_⟩
    · rcases hlog x hx with h' | ⟨h', _⟩
      · left; simpa using h'
      · simp [h] at h'
    · simp only [update_self, SOK]; exact ⟨Or.inl hσ.1, by have := hσ.2.1; omega⟩
  | perform h =>
    simp only [SOK, h] at hσ
    refine ⟨hC.nxtM, hC.doneM, fun x hx => ?_, by simpa using hsub, ?_⟩
    · simp only [List.map_append, List.mem_append, List.map_cons, List.map_nil,
        List.mem_singleton] at hx
      rcases hx with hx | hx
      · rcases hlog x hx with h' | ⟨h', _⟩
        · left; simpa using h'
        · simp [h] at h'
      · right; simp [hx]
    · simp only [update_self, SOK]; exact hσ
  | writeDone h =>
    simp only [SOK, h] at hσ
    obtain ⟨ht, hact⟩ := hσ
    refine ⟨fun i hi => ?_, fun q j hq => ?_, fun x hx => ?_, ?_, ?_⟩
    · dsimp only; rw [update_of_ne (by simp)]; exact hC.nxtM i hi
    · dsimp only; rw [update_of_ne (by simp; omega)]; exact hC.doneM q j hq
    · left
      simp only [update_self, mem_insert]
      rcases hlog x hx with h' | ⟨_, h'⟩
      · exact Or.inr h'
      · exact Or.inl h'
    · simp only [update_self]
      exact insert_subset (mem_sdiff.mpr ⟨hact.2.1, hact.2.2⟩) hsub
    · simp only [update_self, SOK]
      exact ⟨Or.inl ht, (card_insert_le _ _).trans hact.1⟩

lemma Solo.do_le {C : Config (m + 1) Reg ℕ LState} (hC : Solo m n β C) :
    Alg.Do n C ≤ n - (β + m - 1) := by
  have hsok := hC.sok
  have hcard := hC.sok.card_le
  unfold Alg.Do
  by_cases hd : (C.loc (Fin.last m)).status = .done
  · simp only [SOK, hd] at hsok
    have hsub : Alg.jobs n C ⊆ insert (C.loc (Fin.last m)).nxt (C.loc (Fin.last m)).doneS := by
      intro x hx
      simp only [Alg.jobs, mem_filter] at hx
      rcases hC.log x hx.2 with h | ⟨_, h⟩
      · exact mem_insert_of_mem h
      · rw [h]; exact mem_insert_self _ _
    exact (card_le_card hsub).trans ((card_insert_le _ _).trans hsok.2.1)
  · have hsub : Alg.jobs n C ⊆ (C.loc (Fin.last m)).doneS := by
      intro x hx
      simp only [Alg.jobs, mem_filter] at hx
      rcases hC.log x hx.2 with h | ⟨h, _⟩
      · exact h
      · exact absurd h hd
    exact (card_le_card hsub).trans hcard

/-! ## The adversarial run -/

/-- The adversary's schedule: `0, 0, 1, 1, …, m − 1, m − 1`, then the survivor `m` forever. -/
def sched (m k : ℕ) : Fin (m + 1) := if h : k < 2 * m then ⟨k / 2, by omega⟩ else Fin.last m

/-- The adversarial run (the survivor is never scheduled after it has terminated). -/
noncomputable def advRun (m n β : ℕ) : (kk (m + 1) n β).Run :=
  adv4GreedyRun (kk (m + 1) n β) (sched m)

lemma advRun_phase1 (hβ : m + 1 ≤ β) (hn : β + m ≤ n) :
    ∀ t ≤ 2 * m, Phase1 m n t ((advRun m n β).cfg t) := by
  intro t
  induction t with
  | zero => intro _; rw [(advRun m n β).cfg_zero]; exact phase1_zero
  | succ t ih =>
    intro ht
    have hC := ih (by omega)
    have hst : sched m t = ⟨t / 2, by omega⟩ := by simp [sched, show t < 2 * m by omega]
    have hnh : ¬ (kk (m + 1) n β).Halted ((advRun m n β).cfg t) (sched m t) := by
      rw [halted_iff, hC.loc, hst]
      unfold phLoc; split_ifs <;> simp [stuckLoc, setLoc, LState.init]
    have hs := (advRun m n β).cfg_succ t
    rw [advRun, adv4GreedyRun_ev_of_not_halted _ _ hnh] at hs
    rw [hst] at hs
    exact phase1_step hβ hn (by omega) hC _ rfl (step_inv hs)

lemma advRun_solo (hβ : m + 1 ≤ β) (hn : β + m ≤ n) :
    ∀ t, Solo m n β ((advRun m n β).cfg (2 * m + t)) := by
  intro t
  induction t with
  | zero => exact solo_of_phase1 (advRun_phase1 hβ hn _ le_rfl)
  | succ t ih =>
    have hst : sched m (2 * m + t) = Fin.last m := by simp [sched]
    have hs := (advRun m n β).cfg_succ (2 * m + t)
    rw [← add_assoc]
    by_cases hh : (kk (m + 1) n β).Halted ((advRun m n β).cfg (2 * m + t)) (sched m (2 * m + t))
    · rw [advRun, adv4GreedyRun_ev_of_halted _ _ hh] at hs
      simp only [Alg.stepO, Option.some.injEq] at hs
      rw [advRun, ← hs]; exact ih
    · rw [advRun, adv4GreedyRun_ev_of_not_halted _ _ hh, hst] at hs
      exact solo_step hβ hn ih (step_inv hs)

lemma advRun_do_cfg_le (hβ : m + 1 ≤ β) (hn : β + m ≤ n) (k : ℕ) :
    Alg.Do n ((advRun m n β).cfg k) ≤ n - (β + m - 1) := by
  rcases le_or_gt k (2 * m) with hk | hk
  · have := (advRun_phase1 hβ hn k hk).log
    simp [Alg.Do, Alg.jobs, this]
  · obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hk.le
    exact (advRun_solo hβ hn t).do_le

lemma advRun_fair : (advRun m n β).Fair (univ.erase (Fin.last m)) := by
  intro p hp k
  simp only [mem_erase, ne_eq, mem_univ, and_true, not_not] at hp
  subst hp
  refine ⟨k + 2 * m, by omega, ?_⟩
  have hst : sched m (k + 2 * m) = Fin.last m := by simp [sched]
  by_cases hh : (kk (m + 1) n β).Halted ((advRun m n β).cfg (k + 2 * m)) (sched m (k + 2 * m))
  · right; rwa [hst] at hh
  · left; rw [advRun, adv4GreedyRun_ev_of_not_halted _ _ hh, hst]

end Adversary

end Podc.AtMostOnceEffectiveness

namespace Podc.AtMostOnceEffectiveness

open Adversary

/-- **The adversary in the proof of Theorem 4.4** of [Kentros–Kiayias] (upper bound on the
effectiveness of `KK_β`): for `m ≥ 1` processes, `β ≥ m` and `n ≥ β + m − 1`, there is a run of
`KK_β` that is fair with respect to a crash set of `m − 1` processes and performs at most
`n − (β + m − 2)` jobs. (No termination assumption is needed: the surviving process is scheduled
whenever it has not terminated.) -/
theorem exists_fair_run_do_le {m n β : ℕ} (hm : 1 ≤ m) (hβ : m ≤ β) (hn : β + m - 1 ≤ n) :
    ∃ (F : Finset (Fin m)) (r : (kk m n β).Run), F.card = m - 1 ∧ r.Fair F ∧
      r.Do n ≤ n - (β + m - 2) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hm
  refine ⟨Finset.univ.erase (Fin.last m), advRun m n β, ?_, advRun_fair, ?_⟩
  · simp
  · have h := (advRun m n β).do_le_of_forall n _
      (advRun_do_cfg_le (m := m) (by omega) (by omega))
    rwa [show β + m - 1 = β + (m + 1) - 2 by omega] at h

/-- **Theorem 4.4, upper bound, exact form**: assuming termination (wait-freedom, Lemma 4.3), the
adversarial run of `exists_fair_run_do_le` performs exactly `n − (β + m − 2)` jobs (the lower
bound comes from Lemma 4.2). -/
theorem exists_fair_run_do_eq {m n β : ℕ} (hm : 1 ≤ m) (hβ : m ≤ β) (hn : β + m - 1 ≤ n)
    (hwf : ∀ r : (kk m n β).Run, ∃ K, ∀ k ≥ K, r.ev k = none) :
    ∃ (F : Finset (Fin m)) (r : (kk m n β).Run), F.card = m - 1 ∧ r.Fair F ∧
      r.Do n = n - (β + m - 2) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hm
  refine ⟨Finset.univ.erase (Fin.last m), advRun m n β, by simp, advRun_fair, ?_⟩
  have hle := (advRun m n β).do_le_of_forall n _
    (advRun_do_cfg_le (m := m) (by omega) (by omega))
  obtain ⟨K, hK⟩ := hwf (advRun m n β)
  have hev := hK (K + 2 * m) (by omega)
  have hst : sched m (K + 2 * m) = Fin.last m := by simp [sched]
  have hh : (kk (m + 1) n β).Halted ((advRun m n β).cfg (K + 2 * m)) (Fin.last m) := by
    by_contra hh
    rw [← hst] at hh
    rw [advRun, adv4GreedyRun_ev_of_not_halted _ _ hh] at hev
    exact absurd hev (by simp)
  obtain ⟨hI, hI2⟩ := inv_of_reachable (by omega : 1 ≤ β) ((advRun m n β).reachable (K + 2 * m))
  have hge := do_ge_of_halted hI hI2 hh
  have hcfg := (advRun m n β).do_cfg_le n (K + 2 * m)
  omega

end Podc.AtMostOnceEffectiveness
