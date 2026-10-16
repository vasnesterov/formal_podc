import Papers.PODC2022.ConsensusFromSwap.Alg1Defs

/-!
# Algorithm 1, k-agreement: basic invariants (Observations 1–3)

We fix inputs `x` and an infinite schedule `σ : ℕ → P` and consider the configurations
`cfg x σ t` reached after the first `t` steps (every finite execution is a prefix of such a
schedule, see `run_eq_cfg`). We prove:

* the step semantics of Algorithm 1 (`cfg_succ_*`);
* `me = q` for every process (`st_me`); lap counters are nondecreasing (Observation 3,
  `st_U_mono`); decisions are permanent and the local state of a decided process is frozen;
* the shape of a deciding step (`decStep`);
* Observation 2 (`obs2`): if `q` completes a conflict-free iteration at time `τ` with lap
  counter `V`, then there is a `⟨V, q⟩`-total configuration at some time `s ≤ τ` and no process
  swaps the last object during `[s, τ)`;
* Observation 1 (`obs1`): a lap counter component `y` reaches `ℓ ≥ 2` only after some process
  completed a lap with counter `V`, `lead V = y`, `V y + 1 = ℓ`.
-/

namespace ConsensusFromSwap.Alg1.Agree

open ConsensusFromSwap

set_option linter.unusedSectionVars false

variable {P : Type} [DecidableEq P] {m N : ℕ} [NeZero m] [NeZero N]

/-- The local state of `q` in `C`. -/
def ls (C : Cfg (alg P m N)) (q : P) : LState P m N := C.loc q

lemma act_loc (C : Cfg (alg P m N)) (q : P) : (alg P m N).act (C.loc q) =
    match (ls C q).dec with
    | some v => .out v
    | none => .access (ls C q).idx ((ls C q).U, some (ls C q).me) (fun r => after (ls C q) r) :=
  rfl

lemma out_iff (C : Cfg (alg P m N)) (p : P) (v : Fin m) :
    C.Out p v ↔ (ls C p).dec = some v := by
  unfold Cfg.Out
  rw [act_loc]
  cases (ls C p).dec <;> simp

lemma step_of_dec' (C : Cfg (alg P m N)) {q : P} (h : (ls C q).dec ≠ none) : C.step q = C := by
  obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.1 h
  exact C.step_of_out ((out_iff C q v).2 hv)

lemma act_of_none (C : Cfg (alg P m N)) {q : P} (h : (ls C q).dec = none) :
    (alg P m N).act (C.loc q) = .access (ls C q).idx ((ls C q).U, some (ls C q).me)
      (fun r => after (ls C q) r) := by
  rw [act_loc]
  split
  · rename_i v hv; rw [h] at hv; cases hv
  · rfl

lemma step_ls_self (C : Cfg (alg P m N)) {q : P} (h : (ls C q).dec = none) :
    ls (C.step q) q = after (ls C q) (C.mem (ls C q).idx) := by
  rw [C.step_of_access (act_of_none C h)]
  exact Function.update_self _ _ _

lemma step_ls_ne (C : Cfg (alg P m N)) {q q' : P} (h : q' ≠ q) :
    ls (C.step q) q' = ls C q' :=
  C.step_loc_other h

lemma step_mem (C : Cfg (alg P m N)) {q : P} (h : (ls C q).dec = none) (i : Fin N) :
    (C.step q).mem i =
      if i = (ls C q).idx then ((ls C q).U, some (ls C q).me) else C.mem i := by
  rw [C.step_of_access (act_of_none C h)]
  by_cases hi : i = (ls C q).idx
  · subst hi; simp
  · simp [hi]


/-! ### The local computation (lines 8–20) -/

section After

variable (s : LState P m N) (r : Val P m)

lemma after_of_lt (h : s.idx.val + 1 < N) :
    after s r = ⟨s.me, fun j => max (s.U j) (r.1 j), ⟨s.idx.val + 1, h⟩,
      s.conf || decide (r ≠ (s.U, some s.me)), none⟩ := by
  simp [after, h]

lemma after_of_conf (h : ¬ s.idx.val + 1 < N)
    (hc : (s.conf || decide (r ≠ (s.U, some s.me))) = true) :
    after s r = ⟨s.me, fun j => max (s.U j) (r.1 j), 0, false, none⟩ := by
  simp only [after, h, dite_false]
  rw [ite_eq_left_iff.2 (fun h' => absurd hc h')]

lemma after_of_lap (h : ¬ s.idx.val + 1 < N) (hc : s.conf = false)
    (hr : r = (s.U, some s.me)) : after s r = lap s.me s.U := by
  have : (fun j => max (s.U j) (r.1 j)) = s.U := by funext j; simp [hr]
  simp [after, h, hc, hr]

lemma lap_me (me : P) (U : Lap m) : (lap (N := N) me U).me = me := by
  unfold lap; split_ifs <;> rfl

lemma lap_idx (me : P) (U : Lap m) : (lap (N := N) me U).idx = 0 := by
  unfold lap; split_ifs <;> rfl

lemma after_me : (after s r).me = s.me := by
  by_cases h : s.idx.val + 1 < N
  · rw [after_of_lt s r h]
  by_cases hc : (s.conf || decide (r ≠ (s.U, some s.me))) = true
  · rw [after_of_conf s r h hc]
  · simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, not_not, Bool.not_eq_true] at hc
    rw [after_of_lap s r h hc.1 hc.2, lap_me]

lemma after_idx_of_not_lt (h : ¬ s.idx.val + 1 < N) : (after s r).idx = 0 := by
  by_cases hc : (s.conf || decide (r ≠ (s.U, some s.me))) = true
  · rw [after_of_conf s r h hc]
  · simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, not_not, Bool.not_eq_true] at hc
    rw [after_of_lap s r h hc.1 hc.2, lap_idx]

lemma lap_U_ge (me : P) (U : Lap m) : U ≤ (lap (N := N) me U).U := by
  unfold lap
  split_ifs
  · exact le_rfl
  · intro j
    by_cases hj : j = lead U
    · subst hj; simp
    · simp [Function.update_of_ne hj]

lemma lap_dec {me : P} {U : Lap m} {v : Fin m} (h : (lap (N := N) me U).dec = some v) :
    v = lead U ∧ (∀ j, j ≠ lead U → U j + 2 ≤ U (lead U)) ∧ (lap (N := N) me U).U = U := by
  unfold lap at h ⊢
  split_ifs at h ⊢ with hc
  · simp only [Option.some.injEq] at h
    exact ⟨h.symm, hc, rfl⟩

lemma lap_U (me : P) (U : Lap m) (y : Fin m) :
    (lap (N := N) me U).U y = U y ∨ (y = lead U ∧ (lap (N := N) me U).U y = U y + 1) := by
  unfold lap
  split_ifs
  · exact Or.inl rfl
  · by_cases hy : y = lead U
    · subst hy; simp
    · simp [Function.update_of_ne hy]

/-- Lap counters only grow (part of Observation 3). -/
lemma U_le_after : s.U ≤ (after s r).U := by
  intro j
  by_cases h : s.idx.val + 1 < N
  · rw [after_of_lt s r h]; exact le_max_left _ _
  by_cases hc : (s.conf || decide (r ≠ (s.U, some s.me))) = true
  · rw [after_of_conf s r h hc]; exact le_max_left _ _
  · simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, not_not, Bool.not_eq_true] at hc
    rw [after_of_lap s r h hc.1 hc.2]
    exact lap_U_ge _ _ j

/-- The new lap counter dominates the response. -/
lemma resp_le_after : r.1 ≤ (after s r).U := by
  intro j
  by_cases h : s.idx.val + 1 < N
  · rw [after_of_lt s r h]; exact le_max_right _ _
  by_cases hc : (s.conf || decide (r ≠ (s.U, some s.me))) = true
  · rw [after_of_conf s r h hc]; exact le_max_right _ _
  · simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, not_not, Bool.not_eq_true] at hc
    rw [after_of_lap s r h hc.1 hc.2, hc.2]
    exact lap_U_ge _ _ j

/-- A component of the lap counter grows beyond the maximum of the old counter and the response
only by the increment on line 20 after a conflict-free iteration. -/
lemma after_U (y : Fin m) :
    (after s r).U y ≤ max (s.U y) (r.1 y) ∨
      (¬ s.idx.val + 1 < N ∧ s.conf = false ∧ r = (s.U, some s.me) ∧ y = lead s.U ∧
        (after s r).U y = s.U y + 1) := by
  by_cases h : s.idx.val + 1 < N
  · rw [after_of_lt s r h]; exact Or.inl le_rfl
  by_cases hc : (s.conf || decide (r ≠ (s.U, some s.me))) = true
  · rw [after_of_conf s r h hc]; exact Or.inl le_rfl
  · simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, not_not, Bool.not_eq_true] at hc
    rw [after_of_lap s r h hc.1 hc.2]
    rcases lap_U (N := N) s.me s.U y with h' | h'
    · exact Or.inl (h' ▸ le_max_left _ _)
    · exact Or.inr ⟨h, hc.1, hc.2, h'⟩

/-- A step decides only after a conflict-free iteration (lines 13–17). -/
lemma after_dec {v : Fin m} (hv : (after s r).dec = some v) :
    ¬ s.idx.val + 1 < N ∧ s.conf = false ∧ r = (s.U, some s.me) ∧ v = lead s.U ∧
      (∀ j, j ≠ lead s.U → s.U j + 2 ≤ s.U (lead s.U)) ∧ (after s r).U = s.U := by
  by_cases h : s.idx.val + 1 < N
  · rw [after_of_lt s r h] at hv; cases hv
  by_cases hc : (s.conf || decide (r ≠ (s.U, some s.me))) = true
  · rw [after_of_conf s r h hc] at hv; cases hv
  · simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, not_not, Bool.not_eq_true] at hc
    rw [after_of_lap s r h hc.1 hc.2] at hv ⊢
    exact ⟨h, hc.1, hc.2, lap_dec hv⟩

end After


/-! ### Executions as time-indexed sequences of configurations -/

/-- An infinite execution of Algorithm 1 with `N` objects: inputs `x` and a schedule `σ`
(`σ t` takes step `t`). -/
structure Sched (P : Type) (m N : ℕ) : Type where
  /-- The inputs. -/
  x : P → Fin m
  /-- The schedule. -/
  σ : ℕ → P

namespace Sched

variable (E : Sched P m N)

/-- The configuration after the first `t` steps. -/
def cfg : ℕ → Cfg (alg P m N)
  | 0 => initCfg (alg P m N) E.x
  | t + 1 => (cfg t).step (E.σ t)

/-- The local state of `q` after the first `t` steps. -/
def st (t : ℕ) (q : P) : LState P m N := ls (E.cfg t) q

/-- Step `t` is a `Swap` on object `i` (by the undecided process `σ t`). -/
def Wr (t : ℕ) (i : Fin N) : Prop :=
  (E.st t (E.σ t)).dec = none ∧ (E.st t (E.σ t)).idx = i

/-- Configuration `cfg s` is `⟨V, p⟩`-total: every object stores `⟨V, p⟩` and `p`'s lap counter
is `V`. -/
def Total (s : ℕ) (V : Lap m) (p : P) : Prop :=
  (∀ i, (E.cfg s).mem i = (V, some p)) ∧ (E.st s p).U = V

/-- At step `t`, process `q` swaps the last object at the end of a conflict-free iteration of
the loop on lines 4–20 (and completes a lap, line 13). -/
def CompLap (t : ℕ) (q : P) : Prop :=
  E.σ t = q ∧ (E.st t q).dec = none ∧ (E.st t q).idx.val + 1 = N ∧ (E.st t q).conf = false ∧
    (E.cfg t).mem (E.st t q).idx = ((E.st t q).U, some q)

lemma cfg_succ (t : ℕ) : E.cfg (t + 1) = (E.cfg t).step (E.σ t) := rfl

lemma st_zero (q : P) : E.st 0 q = ⟨q, initU (E.x q), 0, false, none⟩ := rfl

lemma cfg_zero_mem (i : Fin N) : (E.cfg 0).mem i = (0, none) := rfl

lemma cfg_succ_of_dec {t : ℕ} (h : (E.st t (E.σ t)).dec ≠ none) : E.cfg (t + 1) = E.cfg t :=
  step_of_dec' _ h

lemma st_succ_self {t : ℕ} {q : P} (hq : E.σ t = q) (h : (E.st t q).dec = none) :
    E.st (t + 1) q = after (E.st t q) ((E.cfg t).mem (E.st t q).idx) := by
  subst hq
  exact step_ls_self _ h

lemma st_succ_ne {t : ℕ} {q : P} (hq : q ≠ E.σ t) : E.st (t + 1) q = E.st t q :=
  step_ls_ne _ hq

lemma st_me (t : ℕ) (q : P) : (E.st t q).me = q := by
  induction t with
  | zero => rfl
  | succ t ih =>
    by_cases hq : q = E.σ t
    · by_cases hd : (E.st t q).dec = none
      · rw [E.st_succ_self hq.symm hd, after_me, ih]
      · subst hq
        simp only [st, E.cfg_succ_of_dec hd]
        exact ih
    · rw [E.st_succ_ne hq, ih]

lemma mem_succ_of_wr {t : ℕ} {i : Fin N} (h : E.Wr t i) :
    (E.cfg (t + 1)).mem i = ((E.st t (E.σ t)).U, some (E.σ t)) := by
  obtain ⟨h1, h2⟩ := h
  have hme := E.st_me t (E.σ t)
  simp only [st] at h1 h2 hme ⊢
  rw [cfg_succ, step_mem _ h1]
  simp [h2, hme]

lemma mem_succ_of_not_wr {t : ℕ} {i : Fin N} (h : ¬ E.Wr t i) :
    (E.cfg (t + 1)).mem i = (E.cfg t).mem i := by
  by_cases hd : (E.st t (E.σ t)).dec = none
  · rw [cfg_succ, step_mem _ hd]
    have : ¬ i = (ls (E.cfg t) (E.σ t)).idx := fun h' => h ⟨hd, h'.symm⟩
    simp [this]
  · rw [E.cfg_succ_of_dec hd]

/-- Objects not swapped during `[s, t)` keep their values. -/
lemma mem_eq_of_noWr {s t : ℕ} {i : Fin N} (hst : s ≤ t)
    (h : ∀ t', s ≤ t' → t' < t → ¬ E.Wr t' i) : (E.cfg t).mem i = (E.cfg s).mem i := by
  induction t, hst using Nat.le_induction with
  | base => rfl
  | succ t hst ih =>
    rw [E.mem_succ_of_not_wr (h t hst (Nat.lt_succ_self t)),
      ih (fun t' h1 h2 => h t' h1 (Nat.lt_succ_of_lt h2))]

/-- Decided processes are frozen. -/
lemma st_succ_of_dec {t : ℕ} {q : P} (h : (E.st t q).dec ≠ none) : E.st (t + 1) q = E.st t q := by
  by_cases hq : q = E.σ t
  · subst hq; simp only [st, E.cfg_succ_of_dec h]
  · exact E.st_succ_ne hq

lemma st_eq_of_dec {t t' : ℕ} {q : P} (htt' : t ≤ t') (h : (E.st t q).dec ≠ none) :
    E.st t' q = E.st t q := by
  induction t', htt' using Nat.le_induction with
  | base => rfl
  | succ t' _ ih => rw [E.st_succ_of_dec (ih ▸ h), ih]

lemma dec_none_of_le {t t' : ℕ} {q : P} (htt' : t ≤ t') (h : (E.st t' q).dec = none) :
    (E.st t q).dec = none := by
  by_contra h'
  rw [E.st_eq_of_dec htt' h'] at h
  exact h' h

/-- Observation 3 (one step). -/
lemma st_U_succ (t : ℕ) (q : P) : (E.st t q).U ≤ (E.st (t + 1) q).U := by
  by_cases hq : q = E.σ t
  · by_cases hd : (E.st t q).dec = none
    · rw [E.st_succ_self hq.symm hd]; exact U_le_after _ _
    · rw [E.st_succ_of_dec hd]
  · rw [E.st_succ_ne hq]

/-- Observation 3: lap counters are nondecreasing. -/
lemma st_U_mono {t t' : ℕ} (htt' : t ≤ t') (q : P) : (E.st t q).U ≤ (E.st t' q).U := by
  induction t', htt' using Nat.le_induction with
  | base => exact le_rfl
  | succ t' _ ih => exact ih.trans (E.st_U_succ t' q)

/-- The shape of a deciding step. -/
lemma decStep {t : ℕ} {q : P} {v : Fin m} (h : (E.st t q).dec = none)
    (h' : (E.st (t + 1) q).dec = some v) :
    E.CompLap t q ∧ v = lead (E.st t q).U ∧
      (∀ j, j ≠ lead (E.st t q).U → (E.st t q).U j + 2 ≤ (E.st t q).U (lead (E.st t q).U)) ∧
      (E.st (t + 1) q).U = (E.st t q).U := by
  by_cases hq : q = E.σ t
  · rw [E.st_succ_self hq.symm h] at h' ⊢
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := after_dec _ _ h'
    refine ⟨⟨hq.symm, h, by have := (E.st t q).idx.isLt; omega, h2, ?_⟩, h4, h5, h6⟩
    rw [h3, E.st_me]
  · rw [E.st_succ_ne hq, h] at h'
    cases h'

lemma st_succ_of_not_active {t : ℕ} {q : P} (h : ¬ (q = E.σ t ∧ (E.st t q).dec = none)) :
    E.st (t + 1) q = E.st t q := by
  by_cases hq : q = E.σ t
  · exact E.st_succ_of_dec (fun h' => h ⟨hq, h'⟩)
  · exact E.st_succ_ne hq

/-! ### Observation 2 -/

/-- The invariant behind Observation 2: during a conflict-free (so far) iteration of `p` with
lap counter `U` that started at time `s`, all objects already swapped by `p` stored `⟨U, p⟩` at
time `s`, and every object not yet swapped by `p` was either not swapped by anybody since `s`
or does not store `p`'s identifier now. -/
def IterInv (t : ℕ) (p : P) : Prop :=
  (E.st t p).dec = none → (E.st t p).conf = false →
    ∃ s ≤ t, (E.st s p).U = (E.st t p).U ∧
      (∀ i : Fin N, i < (E.st t p).idx → (E.cfg s).mem i = ((E.st t p).U, some p)) ∧
      (∀ i : Fin N, (E.st t p).idx ≤ i →
        (∀ t', s ≤ t' → t' < t → ¬ E.Wr t' i) ∨ ((E.cfg t).mem i).2 ≠ some p)

lemma noWr_extend {s t : ℕ} {i : Fin N} {p : P}
    (h : (∀ t', s ≤ t' → t' < t → ¬ E.Wr t' i) ∨ ((E.cfg t).mem i).2 ≠ some p)
    (hw : E.Wr t i → E.σ t ≠ p) :
    (∀ t', s ≤ t' → t' < t + 1 → ¬ E.Wr t' i) ∨ ((E.cfg (t + 1)).mem i).2 ≠ some p := by
  by_cases hW : E.Wr t i
  · right
    rw [E.mem_succ_of_wr hW]
    simpa using hw hW
  · rw [E.mem_succ_of_not_wr hW]
    rcases h with h | h
    · left
      intro t' h1 h2
      rcases Nat.lt_succ_iff_lt_or_eq.1 h2 with h2 | h2
      · exact h t' h1 h2
      · exact h2 ▸ hW
    · exact Or.inr h

lemma iterInv (t : ℕ) (p : P) : E.IterInv t p := by
  induction t generalizing p with
  | zero =>
    intro _ _
    refine ⟨0, le_rfl, rfl, fun i hi => ?_, fun i _ => Or.inl fun t' h1 h2 => by omega⟩
    simp [st_zero] at hi
  | succ t ih =>
    intro hd hc
    by_cases hq : p = E.σ t ∧ (E.st t p).dec = none
    · obtain ⟨hq, hd0⟩ := hq
      have hst := E.st_succ_self hq.symm hd0
      by_cases hlt : (E.st t p).idx.val + 1 < N
      · rw [after_of_lt _ _ hlt] at hst
        rw [hst] at hc
        simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not, not_not] at hc
        obtain ⟨hc1, hc2⟩ := hc
        obtain ⟨s, hs, hsU, h1, h2⟩ := ih p hd0 hc1
        rw [E.st_me] at hc2
        have hU : (E.st (t + 1) p).U = (E.st t p).U := by rw [hst]; funext j; simp [hc2]
        have hidx : (E.st (t + 1) p).idx = ⟨(E.st t p).idx.val + 1, hlt⟩ := by rw [hst]
        refine ⟨s, by omega, by rw [hU, hsU], fun i hi => ?_, fun i hi => ?_⟩
        · rw [hU]
          rw [hidx, Fin.lt_def] at hi
          rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | hi
          · exact h1 i (Fin.lt_def.2 hi)
          · have hi' : i = (E.st t p).idx := Fin.ext hi
            subst hi'
            rcases h2 _ le_rfl with h2 | h2
            · rw [← E.mem_eq_of_noWr hs h2, hc2]
            · exact absurd (by rw [hc2]) h2
        · rw [hidx, Fin.le_def] at hi
          have hi' : (E.st t p).idx ≤ i := Fin.le_def.2 (by simp at hi; omega)
          refine E.noWr_extend (h2 i hi') (fun hW hσ => ?_)
          have := hW.2
          rw [hσ] at this
          simp only at hi
          rw [← this] at hi
          omega
      · refine ⟨t + 1, le_rfl, rfl, fun i hi => ?_, fun i _ => Or.inl fun t' h1 h2 => by omega⟩
        rw [hst, after_idx_of_not_lt _ _ hlt, Fin.lt_def] at hi
        simp at hi
    · have hst := E.st_succ_of_not_active hq
      rw [hst] at hd hc ⊢
      obtain ⟨s, hs, hsU, h1, h2⟩ := ih p hd hc
      refine ⟨s, by omega, hsU, h1, fun i hi => E.noWr_extend (h2 i hi) (fun hW hσ => ?_)⟩
      exact hq ⟨hσ.symm, hσ ▸ hW.1⟩

/-- Observation 2: if `q` completes a lap at time `t` with lap counter `V` (the swap of the last
object returns `⟨V, q⟩`, and so did all swaps of the iteration), then some configuration at a
time `s ≤ t` (the start of the iteration) is `⟨V, q⟩`-total, and no process swaps the last object
during `[s, t)`. -/
theorem obs2 {t : ℕ} {q : P} (h : E.CompLap t q) :
    ∃ s ≤ t, E.Total s (E.st t q).U q ∧ ∀ t', s ≤ t' → t' < t → ¬ E.Wr t' (E.st t q).idx := by
  obtain ⟨_, hd, hidx, hc, hmem⟩ := h
  obtain ⟨s, hs, hsU, h1, h2⟩ := E.iterInv t q hd hc
  have hnw : ∀ t', s ≤ t' → t' < t → ¬ E.Wr t' (E.st t q).idx := by
    rcases h2 _ le_rfl with h2 | h2
    · exact h2
    · exact absurd (by rw [hmem]) h2
  refine ⟨s, hs, ⟨fun i => ?_, hsU⟩, hnw⟩
  by_cases hi : i < (E.st t q).idx
  · exact h1 i hi
  · have : i = (E.st t q).idx := Fin.ext (by rw [Fin.lt_def] at hi; have := i.isLt; omega)
    subst this
    rw [← E.mem_eq_of_noWr hs hnw, hmem]

/-! ### Observation 1 -/

/-- Some process or some object has a lap counter whose `y`-th component is at least `ℓ`. -/
def Big (t : ℕ) (y : Fin m) (ℓ : ℕ) : Prop :=
  (∃ q, ℓ ≤ (E.st t q).U y) ∨ (∃ i, ℓ ≤ ((E.cfg t).mem i).1 y)

/-- Observation 1: if the `y`-th component of some lap counter is `≥ ℓ ≥ 2` at time `t`, then
before `t` some process completed a lap with lap counter `V`, `y = lead V` (so `V y` is maximal)
and `V y + 1 = ℓ` (so it incremented component `y` from `ℓ - 1` to `ℓ` on line 20). -/
theorem obs1 {t : ℕ} {y : Fin m} {ℓ : ℕ} (hℓ : 2 ≤ ℓ) (h : E.Big t y ℓ) :
    ∃ t' < t, E.CompLap t' (E.σ t') ∧ lead (E.st t' (E.σ t')).U = y ∧
      (E.st t' (E.σ t')).U y + 1 = ℓ := by
  induction t with
  | zero =>
    exfalso
    rcases h with ⟨q, hq⟩ | ⟨i, hi⟩
    · rw [st_zero] at hq
      simp only [initU] at hq
      split_ifs at hq <;> omega
    · rw [cfg_zero_mem] at hi
      simp at hi
      omega
  | succ t ih =>
    suffices H : E.Big t y ℓ ∨ (E.CompLap t (E.σ t) ∧ lead (E.st t (E.σ t)).U = y ∧
        (E.st t (E.σ t)).U y + 1 = ℓ) by
      rcases H with H | H
      · obtain ⟨t', ht', H⟩ := ih H
        exact ⟨t', by omega, H⟩
      · exact ⟨t, by omega, H⟩
    rcases h with ⟨q, hq⟩ | ⟨i, hi⟩
    · by_cases hact : q = E.σ t ∧ (E.st t q).dec = none
      · obtain ⟨hσ, hd⟩ := hact
        rw [E.st_succ_self hσ.symm hd] at hq
        rcases after_U (E.st t q) ((E.cfg t).mem (E.st t q).idx) y with h' | h'
        · rcases le_max_iff.1 (hq.trans h') with h'' | h''
          · exact Or.inl (Or.inl ⟨q, h''⟩)
          · exact Or.inl (Or.inr ⟨_, h''⟩)
        · obtain ⟨hlt, hc, hr, hy, hU⟩ := h'
          by_cases hle : ℓ ≤ (E.st t q).U y
          · exact Or.inl (Or.inl ⟨q, hle⟩)
          · right
            subst hσ
            refine ⟨⟨rfl, hd, by have := (E.st t (E.σ t)).idx.isLt; omega, hc, ?_⟩, hy.symm,
              by omega⟩
            rw [hr, E.st_me]
      · rw [E.st_succ_of_not_active hact] at hq
        exact Or.inl (Or.inl ⟨q, hq⟩)
    · by_cases hW : E.Wr t i
      · rw [E.mem_succ_of_wr hW] at hi
        exact Or.inl (Or.inl ⟨_, hi⟩)
      · rw [E.mem_succ_of_not_wr hW] at hi
        exact Or.inl (Or.inr ⟨i, hi⟩)

end Sched

end ConsensusFromSwap.Alg1.Agree
