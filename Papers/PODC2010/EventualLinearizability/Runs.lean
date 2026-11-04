import Papers.PODC2010.EventualLinearizability.ImplModel
import Mathlib.Tactic.Linarith

/-!
# Runs of implementations on top of a consistency layer: general lemmas

General facts about the runs of `ImplModel.lean`, used in the proof of Theorem 2.

* One step (`Cfg.step`): what it changes (`step_loc_of_ne`, …, `opsOf_step_hist`), the log
  only grows by appending entries stamped with the current time (`step_log`), the items of the
  log are unique (`WFLog`, `wfLog_step`), and two configurations that agree on the local part
  of the acting process evolve in the same way (`step_congr`, used for simulation arguments).
* Runs: monotonicity of the log and of the history, time stamps (`log_filter`: the log at an
  earlier time is recovered from the current log), deliveries (`dlv_induction`), the
  submission times of `layerRun` (`sub_of_mem`, `mem_of_sub`).
* **Round-robin layer** (`rrAct`, `RRTail`): from time `T` on, the adversary cycles through the
  processes of a list `ps`; in round `k` (times `T + 2nk + 1, …, T + 2n(k+1)`, `n = |ps|`) every
  process of `ps` gets a delivery of the *snapshot* of the log at the start of the round (all
  items submitted so far, in submission order) followed by a tick. If deliveries before `T`
  are reasonable (`RRTail.pre`), the layer run satisfies **Eventual Consensus**
  (`RRTail.eventualConsensus`), the processes of `ps` tick infinitely often (`RRTail.fair`),
  and the other processes take no step after `T`.
-/

namespace Podc.EventualLinearizability.Runs

open Podc.EventualLinearizability Cslib.SharedMemory.HerlihyWing

variable {P Op Res Msg : Type} [DecidableEq P] {I : Impl P Op Res Msg}

/-! ### One step -/

/-- The log entries appended when process `i`, having submitted `n` items, submits `ms` at
time `t`. -/
def newEntries (i : P) (n t : ℕ) (ms : List Msg) : List (Item P Msg × ℕ) :=
  (ms.zipIdx n).map fun mk => ((i, mk.2, mk.1), t)

/-- The identity of a log entry: submitter and index of the submission. -/
def key (e : Item P Msg × ℕ) : P × ℕ := (e.1.1, e.1.2.1)

omit [DecidableEq P] in
lemma mem_newEntries {i : P} {n t : ℕ} {ms : List Msg} {e : Item P Msg × ℕ}
    (h : e ∈ newEntries i n t ms) :
    e.1.1 = i ∧ n ≤ e.1.2.1 ∧ e.1.2.1 < n + ms.length ∧ e.2 = t := by
  obtain ⟨⟨m, k⟩, hmk, rfl⟩ := List.mem_map.1 h
  obtain ⟨h1, h2, -⟩ := List.mem_zipIdx hmk
  exact ⟨rfl, h1, h2, rfl⟩

omit [DecidableEq P] in
lemma nodup_newEntries (i : P) (n t : ℕ) (ms : List Msg) :
    ((newEntries i n t ms).map key).Nodup := by
  have : (newEntries i n t ms).map key = (List.range' n ms.length).map (Prod.mk i) := by
    rw [← List.zipIdx_map_snd n ms, List.map_map]
    simp [newEntries, key, Function.comp_def]
  rw [this]
  exact (List.nodup_range' ..).map (Prod.mk_right_injective i)

/-- Well-formedness of the log: indices of submissions are below the submission counters, and
entries have distinct identities. -/
def WFLog (log : List (Item P Msg × ℕ)) (nsub : P → ℕ) : Prop :=
  (∀ e ∈ log, e.1.2.1 < nsub e.1.1) ∧ (log.map key).Nodup

lemma wfLog_apply {C : Cfg I} (h : WFLog C.log C.nsub) (t : ℕ) (i : P)
    (out : I.State × List Msg × Option Res) (pre : History P Unit Op Res) :
    WFLog (C.apply t i out pre).log (C.apply t i out pre).nsub := by
  obtain ⟨h1, h2⟩ := h
  have hlog : (C.apply t i out pre).log = C.log ++ newEntries i (C.nsub i) t out.2.1 := rfl
  have hnsub : (C.apply t i out pre).nsub = Function.update C.nsub i (C.nsub i + out.2.1.length) :=
    rfl
  have hle : ∀ j, C.nsub j ≤ Function.update C.nsub i (C.nsub i + out.2.1.length) j := by
    intro j
    by_cases hj : j = i
    · subst hj; simp
    · simp [Function.update_of_ne hj]
  rw [hlog, hnsub]
  refine ⟨fun e he => ?_, ?_⟩
  · rcases List.mem_append.1 he with he | he
    · exact lt_of_lt_of_le (h1 e he) (hle _)
    · obtain ⟨rfl, -, h3, -⟩ := mem_newEntries he
      simpa using h3
  · rw [List.map_append, List.nodup_append]
    refine ⟨h2, nodup_newEntries .., ?_⟩
    intro a ha b hb hab
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 ha
    obtain ⟨f, hf, rfl⟩ := List.mem_map.1 hb
    obtain ⟨hf1, hf2, -, -⟩ := mem_newEntries hf
    have := h1 e he
    simp only [key, Prod.mk.injEq] at hab
    rw [hab.1, hf1, hab.2] at this
    omega

lemma wfLog_step {C : Cfg I} (h : WFLog C.log C.nsub) (t : ℕ) (act : Act P Op Msg) :
    WFLog (C.step t act).log (C.step t act).nsub := by
  cases act with
  | idle => exact h
  | invoke i op => exact wfLog_apply h t i _ _
  | deliver i s => exact wfLog_apply h t i _ []
  | tick i => exact wfLog_apply h t i _ []

lemma step_log (C : Cfg I) (t : ℕ) (act : Act P Op Msg) :
    ∃ new, (C.step t act).log = C.log ++ new ∧ ∀ e ∈ new, e.2 = t := by
  cases act with
  | idle => exact ⟨[], by simp [Cfg.step]⟩
  | invoke i op =>
    exact ⟨newEntries i (C.nsub i) t _, rfl, fun e he => (mem_newEntries he).2.2.2⟩
  | deliver i s =>
    exact ⟨newEntries i (C.nsub i) t _, rfl, fun e he => (mem_newEntries he).2.2.2⟩
  | tick i =>
    exact ⟨newEntries i (C.nsub i) t _, rfl, fun e he => (mem_newEntries he).2.2.2⟩

/-- The operations invoked by an action. -/
def invOps (act : Act P Op Msg) (p : P) : List Op :=
  match act with
  | .invoke i op => if i = p then [op] else []
  | _ => []

lemma opsOf_res_map (i p : P) (x : Unit) (r : Option Res) :
    opsOf ((r.map fun r => (Event.res i () r : Event P Unit Op Res)).toList) p x = [] := by
  cases r <;> rfl

lemma opsOf_step_hist (C : Cfg I) (t : ℕ) (act : Act P Op Msg) (p : P) (x : Unit) :
    opsOf (C.step t act).hist p x = opsOf C.hist p x ++ invOps act p := by
  cases act with
  | idle => simp [Cfg.step, invOps]
  | invoke i op =>
    simp only [Cfg.step, Cfg.apply, opsOf_append, opsOf_res_map, invOps, List.append_nil,
      List.append_cancel_left_eq]
    by_cases h : i = p <;> simp [opsOf, h]
  | deliver i s => simp [Cfg.step, Cfg.apply, opsOf_res_map, invOps]
  | tick i => simp [Cfg.step, Cfg.apply, opsOf_res_map, invOps]

lemma step_loc_of_ne {C : Cfg I} {t : ℕ} {act : Act P Op Msg} {j : P} (h : act.proc ≠ some j) :
    (C.step t act).loc j = C.loc j := by
  cases act with
  | idle => rfl
  | invoke i op =>
    have : j ≠ i := fun e => h (by simp [Act.proc, e])
    simp [Cfg.step, Cfg.apply, Function.update_of_ne this]
  | deliver i s =>
    have : j ≠ i := fun e => h (by simp [Act.proc, e])
    simp [Cfg.step, Cfg.apply, Function.update_of_ne this]
  | tick i =>
    have : j ≠ i := fun e => h (by simp [Act.proc, e])
    simp [Cfg.step, Cfg.apply, Function.update_of_ne this]

lemma step_nsub_of_ne {C : Cfg I} {t : ℕ} {act : Act P Op Msg} {j : P}
    (h : act.proc ≠ some j) : (C.step t act).nsub j = C.nsub j := by
  cases act with
  | idle => rfl
  | invoke i op =>
    have : j ≠ i := fun e => h (by simp [Act.proc, e])
    simp [Cfg.step, Cfg.apply, Function.update_of_ne this]
  | deliver i s =>
    have : j ≠ i := fun e => h (by simp [Act.proc, e])
    simp [Cfg.step, Cfg.apply, Function.update_of_ne this]
  | tick i =>
    have : j ≠ i := fun e => h (by simp [Act.proc, e])
    simp [Cfg.step, Cfg.apply, Function.update_of_ne this]

lemma step_dlv_of_ne {C : Cfg I} {t : ℕ} {act : Act P Op Msg} {j : P}
    (h : ∀ s, act ≠ .deliver j s) : (C.step t act).dlv j = C.dlv j := by
  cases act with
  | idle => rfl
  | invoke i op => rfl
  | deliver i s =>
    have : j ≠ i := fun e => h s (by rw [e])
    simp [Cfg.step, Cfg.apply, Function.update_of_ne this]
  | tick i => rfl

lemma step_dlv_deliver (C : Cfg I) (t : ℕ) (i : P) (s : List (Item P Msg)) :
    (C.step t (.deliver i s)).dlv i = s := by
  simp [Cfg.step]

lemma restrictP_step_hist_of_ne {C : Cfg I} {t : ℕ} {act : Act P Op Msg} {j : P}
    (h : act.proc ≠ some j) : restrictP (C.step t act).hist j = restrictP C.hist j := by
  cases act with
  | idle => rfl
  | invoke i op =>
    have : i ≠ j := fun e => h (by simp [Act.proc, e])
    cases hr : (I.onInvoke i (C.loc i) op).2.2 <;>
      simp [Cfg.step, Cfg.apply, hr, restrictP_cons, this]
  | deliver i s =>
    have : i ≠ j := fun e => h (by simp [Act.proc, e])
    cases hr : (I.onDeliver i (C.loc i) s).2.2 <;>
      simp [Cfg.step, Cfg.apply, hr, restrictP_cons, this]
  | tick i =>
    have : i ≠ j := fun e => h (by simp [Act.proc, e])
    cases hr : (I.onTick i (C.loc i)).2.2 <;>
      simp [Cfg.step, Cfg.apply, hr, restrictP_cons, this]

/-- Two configurations that agree on the local part of process `i` evolve in the same way under
an action of `i`: same local part afterwards, same events appended to the history, same entries
appended to the log. -/
lemma step_congr {C D : Cfg I} {i : P} {t : ℕ} {act : Act P Op Msg}
    (hact : act.proc = none ∨ act.proc = some i) (hloc : C.loc i = D.loc i)
    (hnsub : C.nsub i = D.nsub i) (hdlv : C.dlv i = D.dlv i) :
    (C.step t act).loc i = (D.step t act).loc i ∧ (C.step t act).nsub i = (D.step t act).nsub i ∧
    (C.step t act).dlv i = (D.step t act).dlv i ∧
    (∃ δ, (C.step t act).hist = C.hist ++ δ ∧ (D.step t act).hist = D.hist ++ δ) ∧
    (∃ new, (C.step t act).log = C.log ++ new ∧ (D.step t act).log = D.log ++ new) := by
  cases act with
  | idle => exact ⟨hloc, hnsub, hdlv, ⟨[], by simp [Cfg.step]⟩, ⟨[], by simp [Cfg.step]⟩⟩
  | invoke j op =>
    obtain rfl : j = i := by simpa [Act.proc] using hact
    refine ⟨by simp [Cfg.step, Cfg.apply, hloc], by simp [Cfg.step, Cfg.apply, hloc, hnsub],
      hdlv, ⟨_, by simp [Cfg.step, Cfg.apply, hloc, List.append_assoc]; rfl⟩,
      ⟨_, by simp [Cfg.step, Cfg.apply, hloc, hnsub]; rfl⟩⟩
  | deliver j s =>
    obtain rfl : j = i := by simpa [Act.proc] using hact
    refine ⟨by simp [Cfg.step, Cfg.apply, hloc], by simp [Cfg.step, Cfg.apply, hloc, hnsub],
      by simp [Cfg.step], ⟨_, by simp [Cfg.step, Cfg.apply, hloc]; rfl⟩,
      ⟨_, by simp [Cfg.step, Cfg.apply, hloc, hnsub]; rfl⟩⟩
  | tick j =>
    obtain rfl : j = i := by simpa [Act.proc] using hact
    refine ⟨by simp [Cfg.step, Cfg.apply, hloc], by simp [Cfg.step, Cfg.apply, hloc, hnsub],
      hdlv, ⟨_, by simp [Cfg.step, Cfg.apply, hloc]; rfl⟩,
      ⟨_, by simp [Cfg.step, Cfg.apply, hloc, hnsub]; rfl⟩⟩

/-! ### Runs -/

section Run

variable (adv : Adversary I)

lemma run_succ (t : ℕ) : run I adv (t + 1) = (run I adv t).step (t + 1) (actAt I adv t) := rfl

lemma wfLog_run (t : ℕ) : WFLog (run I adv t).log (run I adv t).nsub := by
  induction t with
  | zero => exact ⟨by simp [run, Cfg.init], by simp [run, Cfg.init]⟩
  | succ t ih => exact wfLog_step ih ..

/-- The items of the log are unique. -/
lemma nodup_log_items (t : ℕ) : ((run I adv t).log.map Prod.fst).Nodup := by
  have h := (wfLog_run adv t).2
  have : (run I adv t).log.map key = ((run I adv t).log.map Prod.fst).map
      (fun it : Item P Msg => (it.1, it.2.1)) := by simp [key, Function.comp_def]
  rw [this] at h
  exact h.of_map _

lemma log_succ (t : ℕ) : ∃ new, (run I adv (t + 1)).log = (run I adv t).log ++ new ∧
    ∀ e ∈ new, e.2 = t + 1 := step_log ..

lemma log_prefix {s t : ℕ} (h : s ≤ t) : (run I adv s).log <+: (run I adv t).log := by
  induction t, h using Nat.le_induction with
  | base => exact List.prefix_refl _
  | succ t _ ih =>
    obtain ⟨new, hnew, -⟩ := log_succ adv t
    rw [hnew]; exact ih.trans (List.prefix_append _ _)

lemma stamp_le {t : ℕ} {e : Item P Msg × ℕ} (h : e ∈ (run I adv t).log) : e.2 ≤ t := by
  induction t with
  | zero => simp [run, Cfg.init] at h
  | succ t ih =>
    obtain ⟨new, hnew, hst⟩ := log_succ adv t
    rw [hnew] at h
    rcases List.mem_append.1 h with h | h
    · exact (ih h).trans (Nat.le_succ t)
    · exact (hst e h).le

/-- The log at an earlier time `s` consists of the entries stamped at most `s`. -/
lemma log_filter {s t : ℕ} (h : s ≤ t) :
    (run I adv t).log.filter (fun e => decide (e.2 ≤ s)) = (run I adv s).log := by
  induction t, h using Nat.le_induction with
  | base => exact List.filter_eq_self.2 fun e he => by simpa using stamp_le adv he
  | succ t hst ih =>
    obtain ⟨new, hnew, hnst⟩ := log_succ adv t
    rw [hnew, List.filter_append, ih, List.filter_eq_nil_iff.2, List.append_nil]
    intro e he; have := hnst e he; simp; omega

lemma items_mono {s t : ℕ} (h : s ≤ t) {o : Item P Msg}
    (ho : o ∈ (run I adv s).log.map Prod.fst) : o ∈ (run I adv t).log.map Prod.fst :=
  ((log_prefix adv h).map Prod.fst).subset ho

lemma hist_succ (t : ℕ) : ∃ δ, hist I adv (t + 1) = hist I adv t ++ δ := by
  cases h : actAt I adv t with
  | idle => exact ⟨[], by simp [hist, run_succ, h, Cfg.step]⟩
  | invoke i op =>
    exact ⟨_, by simp only [hist, run_succ, h, Cfg.step, Cfg.apply, List.append_assoc]; rfl⟩
  | deliver i s =>
    exact ⟨_, by simp only [hist, run_succ, h, Cfg.step, Cfg.apply, List.append_assoc]; rfl⟩
  | tick i =>
    exact ⟨_, by simp only [hist, run_succ, h, Cfg.step, Cfg.apply, List.append_assoc]; rfl⟩

lemma hist_prefix {s t : ℕ} (h : s ≤ t) : hist I adv s <+: hist I adv t := by
  induction t, h using Nat.le_induction with
  | base => exact List.prefix_refl _
  | succ t _ ih =>
    obtain ⟨δ, hδ⟩ := hist_succ adv t
    rw [hδ]; exact ih.trans (List.prefix_append _ _)

lemma completed_mono {s t : ℕ} (h : s ≤ t) {a : OpId P Unit} (ha : Completed (hist I adv s) a) :
    Completed (hist I adv t) a := ha.of_prefix (hist_prefix adv h)

lemma opsOf_hist_succ (t : ℕ) (p : P) (x : Unit) :
    opsOf (hist I adv (t + 1)) p x = opsOf (hist I adv t) p x ++ invOps (actAt I adv t) p :=
  opsOf_step_hist ..

/-- Without invocations between `s` and `t`, no operation is invoked. -/
lemma opsOf_hist_const {s t : ℕ} (h : s ≤ t)
    (hno : ∀ t', s ≤ t' → t' < t → ∀ i op, actAt I adv t' ≠ .invoke i op) (p : P) (x : Unit) :
    opsOf (hist I adv t) p x = opsOf (hist I adv s) p x := by
  induction t, h using Nat.le_induction with
  | base => rfl
  | succ t hst ih =>
    rw [opsOf_hist_succ, ih (fun t' h1 h2 => hno t' h1 (by omega))]
    have : invOps (actAt I adv t) p = [] := by
      cases hc : actAt I adv t with
      | invoke i op => exact absurd hc (hno t hst (by omega) i op)
      | _ => rfl
    simp [this]

/-- A process that has not acted before `t` is in its initial state and has no events. -/
lemma not_acted {j : P} {t : ℕ} (h : ∀ t' < t, (actAt I adv t').proc ≠ some j) :
    (run I adv t).loc j = I.init j ∧ (run I adv t).nsub j = 0 ∧ (run I adv t).dlv j = [] ∧
      restrictP (hist I adv t) j = [] := by
  induction t with
  | zero => exact ⟨rfl, rfl, rfl, rfl⟩
  | succ t ih =>
    obtain ⟨h1, h2, h3, h4⟩ := ih fun t' ht' => h t' (by omega)
    have hj := h t (by omega)
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [run_succ, step_loc_of_ne hj, h1]
    · rw [run_succ, step_nsub_of_ne hj, h2]
    · rw [run_succ, step_dlv_of_ne (fun s hs => hj (by simp [hs, Act.proc])), h3]
    · rw [hist, run_succ, restrictP_step_hist_of_ne hj]; exact h4

lemma opsOf_eq_nil_of_restrictP {H : History P Unit Op Res} {j : P} (h : restrictP H j = [])
    (x : Unit) : opsOf H j x = [] := by
  have := opsOf_restrictP H j j x
  simpa [h] using this.symm

lemma ressOf_eq_nil_of_restrictP {H : History P Unit Op Res} {j : P} (h : restrictP H j = [])
    (x : Unit) : ressOf H j x = [] := by
  have := ressOf_restrictP H j j x
  simpa [h] using this.symm

lemma run_eq_init {t : ℕ} (h : ∀ t' < t, actAt I adv t' = .idle) : run I adv t = Cfg.init I := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [run_succ, h t (by omega), ih fun t' ht' => h t' (by omega)]; rfl

lemma dlv_succ_deliver {t : ℕ} {i : P} {s : List (Item P Msg)}
    (h : actAt I adv t = .deliver i s) : (run I adv (t + 1)).dlv i = s := by
  rw [run_succ, h, step_dlv_deliver]

lemma dlv_succ_of_ne {t : ℕ} {i : P} (h : ∀ s, actAt I adv t ≠ .deliver i s) :
    (run I adv (t + 1)).dlv i = (run I adv t).dlv i := by
  rw [run_succ, step_dlv_of_ne h]

/-- Induction principle for the last delivered sequence. -/
lemma dlv_induction {i : P} (Q : List (Item P Msg) → Prop) {t₀ : ℕ}
    (h₀ : Q ((run I adv t₀).dlv i))
    (hstep : ∀ t ≥ t₀, ∀ s, actAt I adv t = .deliver i s → Q s) :
    ∀ t ≥ t₀, Q ((run I adv t).dlv i) := by
  intro t ht
  induction t, ht using Nat.le_induction with
  | base => exact h₀
  | succ t ht ih =>
    by_cases hd : ∃ s, actAt I adv t = .deliver i s
    · obtain ⟨s, hs⟩ := hd
      rw [dlv_succ_deliver adv hs]; exact hstep t ht s hs
    · push Not at hd
      rw [dlv_succ_of_ne adv hd]; exact ih

/-! ### Submission times in `layerRun` -/

lemma sub_of_mem {correct : Set P} {t : ℕ} {o : Item P Msg}
    (h : o ∈ (run I adv t).log.map Prod.fst) :
    ∃ t' ≤ t, (layerRun I adv correct).sub o = some (o.1, t') := by
  classical
  obtain ⟨⟨o', s⟩, hmem, rfl⟩ := List.mem_map.1 h
  have hex : ∃ s t, ((o', s) : Item P Msg × ℕ) ∈ (run I adv t).log := ⟨s, t, hmem⟩
  refine ⟨Nat.find hex, (Nat.find_min' hex ⟨t, hmem⟩).trans (stamp_le adv hmem), ?_⟩
  simp [layerRun, hex]

lemma mem_of_sub {correct : Set P} {o : Item P Msg} {j : P} {t' : ℕ}
    (h : (layerRun I adv correct).sub o = some (j, t')) :
    j = o.1 ∧ o ∈ (run I adv t').log.map Prod.fst := by
  classical
  simp only [layerRun] at h
  split_ifs at h with hex
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, hfind⟩ := h
  refine ⟨rfl, ?_⟩
  obtain ⟨t, ht⟩ := Nat.find_spec hex
  rw [hfind] at ht
  have hst : t' ≤ t := stamp_le adv ht
  rw [← log_filter adv hst]
  exact List.mem_map.2 ⟨_, List.mem_filter.2 ⟨ht, by simp⟩, rfl⟩

end Run

/-! ### Round-robin consistency layer -/

/-- The snapshot of the log at time `s`: the items stamped at most `s`, in submission order. -/
def snap (C : Cfg I) (s : ℕ) : List (Item P Msg) :=
  (C.log.filter fun e => decide (e.2 ≤ s)).map Prod.fst

/-- The items of the log at time `s`. -/
abbrev items (adv : Adversary I) (s : ℕ) : List (Item P Msg) := (run I adv s).log.map Prod.fst

lemma snap_run (adv : Adversary I) {s t : ℕ} (h : s ≤ t) : snap (run I adv t) s = items adv s := by
  simp only [snap, log_filter adv h]

/-- Start of the round-robin round containing step `t`. -/
def rrStart (ps : List P) (T t : ℕ) : ℕ := T + 2 * ps.length * ((t - T) / (2 * ps.length))

/-- The round-robin adversary from time `T` on: in round `k` (steps `T + 2nk + j`,
`j < 2n`, `n = |ps|`), step `2m` delivers to `ps[m]` the snapshot of the log at the start of the
round, and step `2m + 1` is a tick of `ps[m]`. -/
def rrAct (ps : List P) (T t : ℕ) (C : Cfg I) : Act P Op Msg :=
  match ps[(t - T) % (2 * ps.length) / 2]? with
  | none => .idle
  | some i =>
    if (t - T) % (2 * ps.length) % 2 = 0 then .deliver i (snap C (rrStart ps T t)) else .tick i

section RR

variable {ps : List P} {T : ℕ}

omit [DecidableEq P] in
lemma rrStart_le {t : ℕ} (h : T ≤ t) : rrStart ps T t ≤ t := by
  have := Nat.div_mul_le_self (t - T) (2 * ps.length)
  unfold rrStart; rw [Nat.mul_comm (2 * ps.length)]; omega

omit [DecidableEq P] in
lemma le_rrStart (t : ℕ) : T ≤ rrStart ps T t := Nat.le_add_right _ _

omit [DecidableEq P] in
lemma rrStart_mono {t t' : ℕ} (h : t ≤ t') : rrStart ps T t ≤ rrStart ps T t' := by
  unfold rrStart
  have : (t - T) / (2 * ps.length) ≤ (t' - T) / (2 * ps.length) := Nat.div_le_div_right (by omega)
  have := Nat.mul_le_mul_left (2 * ps.length) this
  omega

omit [DecidableEq P] in
lemma rrStart_round {k j : ℕ} (hj : j < 2 * ps.length) :
    rrStart ps T (T + 2 * ps.length * k + j) = T + 2 * ps.length * k := by
  unfold rrStart
  have hpos : 0 < 2 * ps.length := by omega
  rw [show T + 2 * ps.length * k + j - T = 2 * ps.length * k + j by omega,
    Nat.mul_add_div hpos, Nat.div_eq_of_lt hj, Nat.add_zero]

omit [DecidableEq P] in
lemma rrAct_deliver {t : ℕ} {C : Cfg I} {i : P} {s : List (Item P Msg)}
    (h : rrAct ps T t C = .deliver i s) : i ∈ ps ∧ s = snap C (rrStart ps T t) := by
  unfold rrAct at h
  split at h
  · cases h
  · rename_i j hj
    split_ifs at h
    cases h
    exact ⟨List.mem_of_getElem? hj, rfl⟩

omit [DecidableEq P] in
lemma rrAct_proc {t : ℕ} {C : Cfg I} {i : P} (h : (rrAct ps T t C).proc = some i) : i ∈ ps := by
  unfold rrAct at h
  split at h
  · cases h
  · rename_i j hj
    split_ifs at h <;>
    · simp only [Act.proc, Option.some.injEq] at h
      subst h; exact List.mem_of_getElem? hj

omit [DecidableEq P] in
lemma rrAct_ne_invoke (t : ℕ) (C : Cfg I) (i : P) (op : Op) : rrAct ps T t C ≠ .invoke i op := by
  unfold rrAct
  split
  · simp
  · split_ifs <;> simp

omit [DecidableEq P] in
lemma rrAct_at_deliver {idx : ℕ} {i : P} (hidx : ps[idx]? = some i) (k : ℕ) (C : Cfg I) :
    rrAct ps T (T + 2 * ps.length * k + 2 * idx) C =
      .deliver i (snap C (T + 2 * ps.length * k)) := by
  have hlt : idx < ps.length := (List.getElem?_eq_some_iff.1 hidx).1
  have hpos : 0 < 2 * ps.length := by omega
  have h1 : (T + 2 * ps.length * k + 2 * idx - T) % (2 * ps.length) = 2 * idx := by
    rw [show T + 2 * ps.length * k + 2 * idx - T = 2 * ps.length * k + 2 * idx by omega,
      Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
  unfold rrAct
  rw [h1, show 2 * idx / 2 = idx by omega, hidx]
  dsimp only
  rw [ite_eq_left (by omega), rrStart_round (by omega)]

omit [DecidableEq P] in
lemma rrAct_at_tick {idx : ℕ} {i : P} (hidx : ps[idx]? = some i) (k : ℕ) (C : Cfg I) :
    rrAct ps T (T + 2 * ps.length * k + (2 * idx + 1)) C = .tick i := by
  have hlt : idx < ps.length := (List.getElem?_eq_some_iff.1 hidx).1
  have hpos : 0 < 2 * ps.length := by omega
  have h1 : (T + 2 * ps.length * k + (2 * idx + 1) - T) % (2 * ps.length) = 2 * idx + 1 := by
    rw [show T + 2 * ps.length * k + (2 * idx + 1) - T = 2 * ps.length * k + (2 * idx + 1) by
      omega, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
  unfold rrAct
  rw [h1, show (2 * idx + 1) / 2 = idx by omega, hidx]
  dsimp only
  rw [ite_eq_right (by omega)]

end RR

/-- A delivery of `s` to `p_i` at step `t` is *good*: `s` has no duplicates, consists of
submitted items, and contains the previously delivered sequence. -/
def GoodDeliv (adv : Adversary I) (t : ℕ) (i : P) (s : List (Item P Msg)) : Prop :=
  s.Nodup ∧ (∀ o ∈ s, o ∈ items adv t) ∧ ∀ o ∈ (run I adv t).dlv i, o ∈ s

/-- The adversary follows the round-robin layer for the processes `ps` from time `T` on, and
makes only good deliveries before. -/
structure RRTail (adv : Adversary I) (ps : List P) (T : ℕ) : Prop where
  ne : ps ≠ []
  tail : ∀ t ≥ T, actAt I adv t = rrAct ps T t (run I adv t)
  pre : ∀ t < T, ∀ i s, actAt I adv t = .deliver i s → GoodDeliv adv t i s

namespace RRTail

variable {adv : Adversary I} {ps : List P} {T : ℕ}

lemma length_pos (h : RRTail adv ps T) : 0 < ps.length := List.length_pos_iff.2 h.ne

lemma rrStart_self (h : RRTail adv ps T) : rrStart ps T T = T := by
  simpa using rrStart_round (ps := ps) (T := T) (k := 0) (j := 0) (by have := h.length_pos; omega)

lemma deliver_tail (h : RRTail adv ps T) {t : ℕ} (ht : T ≤ t) {i : P} {s : List (Item P Msg)}
    (hd : actAt I adv t = .deliver i s) : i ∈ ps ∧ s = items adv (rrStart ps T t) := by
  rw [h.tail t ht] at hd
  obtain ⟨hi, rfl⟩ := rrAct_deliver hd
  exact ⟨hi, snap_run adv (rrStart_le ht)⟩

/-- Delivered sequences consist of submitted items. -/
lemma dlv_sub_items (h : RRTail adv ps T) :
    ∀ t i, ∀ o ∈ (run I adv t).dlv i, o ∈ items adv t := by
  intro t
  induction t with
  | zero => intro i o ho; simp [run, Cfg.init] at ho
  | succ t ih =>
    intro i o ho
    by_cases hd : ∃ s, actAt I adv t = .deliver i s
    · obtain ⟨s, hs⟩ := hd
      rw [dlv_succ_deliver adv hs] at ho
      refine items_mono adv (Nat.le_succ t) ?_
      by_cases ht : t < T
      · exact (h.pre t ht i s hs).2.1 o ho
      · obtain ⟨-, rfl⟩ := h.deliver_tail (by omega) hs
        exact items_mono adv (rrStart_le (by omega)) ho
    · push Not at hd
      rw [dlv_succ_of_ne adv hd] at ho
      exact items_mono adv (Nat.le_succ t) (ih i o ho)

/-- From time `T` on, delivered sequences consist of items submitted before the current round. -/
lemma dlv_sub_start (h : RRTail adv ps T) :
    ∀ t ≥ T, ∀ i, ∀ o ∈ (run I adv t).dlv i, o ∈ items adv (rrStart ps T t) := by
  intro t ht
  induction t, ht using Nat.le_induction with
  | base =>
    intro i o ho
    rw [h.rrStart_self]; exact h.dlv_sub_items T i o ho
  | succ t ht ih =>
    intro i o ho
    by_cases hd : ∃ s, actAt I adv t = .deliver i s
    · obtain ⟨s, hs⟩ := hd
      rw [dlv_succ_deliver adv hs] at ho
      obtain ⟨-, rfl⟩ := h.deliver_tail ht hs
      exact items_mono adv (rrStart_mono (Nat.le_succ t)) ho
    · push Not at hd
      rw [dlv_succ_of_ne adv hd] at ho
      exact items_mono adv (rrStart_mono (Nat.le_succ t)) (ih i o ho)

/-- All deliveries are good. -/
lemma goodDeliv (h : RRTail adv ps T) {t : ℕ} {i : P} {s : List (Item P Msg)}
    (hd : actAt I adv t = .deliver i s) : GoodDeliv adv t i s := by
  by_cases ht : t < T
  · exact h.pre t ht i s hd
  · obtain ⟨-, rfl⟩ := h.deliver_tail (by omega) hd
    exact ⟨nodup_log_items adv _, fun o ho => items_mono adv (rrStart_le (by omega)) ho,
      h.dlv_sub_start t (by omega) i⟩

/-- The processes of `ps` tick infinitely often. -/
lemma fair (h : RRTail adv ps T) {i : P} (hi : i ∈ ps) (t : ℕ) :
    ∃ t' ≥ t, actAt I adv t' = .tick i := by
  obtain ⟨idx, hidx⟩ := List.mem_iff_getElem?.1 hi
  have hn := h.length_pos
  refine ⟨T + 2 * ps.length * t + (2 * idx + 1), by nlinarith, ?_⟩
  rw [h.tail _ (by omega), rrAct_at_tick hidx]

/-- The processes outside `ps` take no step from time `T` on. -/
lemma proc_ne (h : RRTail adv ps T) {i : P} (hi : i ∉ ps) {t : ℕ} (ht : T ≤ t) :
    (actAt I adv t).proc ≠ some i := by
  rw [h.tail t ht]; intro h'; exact hi (rrAct_proc h')

/-- No invocation from time `T` on. -/
lemma ne_invoke (h : RRTail adv ps T) {t : ℕ} (ht : T ≤ t) (i : P) (op : Op) :
    actAt I adv t ≠ .invoke i op := by
  rw [h.tail t ht]; exact rrAct_ne_invoke t (run I adv t) i op

/-- After round `k`, a process of `ps` holds the snapshot of the log at a round start `≥` the
start of round `k` and `≤` the current round start. -/
lemma dlv_round (h : RRTail adv ps T) {i : P} (hi : i ∈ ps) (k : ℕ) :
    ∀ t ≥ T + 2 * ps.length * (k + 1), ∃ s, T + 2 * ps.length * k ≤ s ∧
      s ≤ rrStart ps T t ∧ (run I adv t).dlv i = items adv s := by
  obtain ⟨idx, hidx⟩ := List.mem_iff_getElem?.1 hi
  have hlt : idx < ps.length := (List.getElem?_eq_some_iff.1 hidx).1
  have hd : actAt I adv (T + 2 * ps.length * k + 2 * idx) =
      .deliver i (items adv (T + 2 * ps.length * k)) := by
    rw [h.tail _ (by omega), rrAct_at_deliver hidx, snap_run adv (by omega)]
  have hstart : rrStart ps T (T + 2 * ps.length * k + 2 * idx) = T + 2 * ps.length * k :=
    rrStart_round (by omega)
  have key : ∀ t ≥ T + 2 * ps.length * k + 2 * idx + 1, ∃ s, T + 2 * ps.length * k ≤ s ∧
      s ≤ rrStart ps T t ∧ (run I adv t).dlv i = items adv s := by
    intro t ht
    induction t, ht using Nat.le_induction with
    | base =>
      refine ⟨_, le_rfl, ?_, dlv_succ_deliver adv hd⟩
      exact hstart.symm.trans_le (rrStart_mono (by omega))
    | succ t ht ih =>
      by_cases hd' : ∃ s, actAt I adv t = .deliver i s
      · obtain ⟨s, hs⟩ := hd'
        obtain ⟨-, rfl⟩ := h.deliver_tail (by omega) hs
        refine ⟨_, ?_, rrStart_mono (Nat.le_succ t), dlv_succ_deliver adv hs⟩
        exact hstart.symm.trans_le (rrStart_mono (by omega))
      · push Not at hd'
        obtain ⟨s, h1, h2, h3⟩ := ih
        exact ⟨s, h1, h2.trans (rrStart_mono (Nat.le_succ t)), (dlv_succ_of_ne adv hd').trans h3⟩
  intro t ht
  exact key t (by nlinarith)

/-- **The round-robin layer satisfies Eventual Consensus** (for any set of correct processes
contained in `ps`), with stability from the end of the first round on. -/
theorem eventualConsensus (h : RRTail adv ps T) {correct : Set P}
    (hc : ∀ i ∈ correct, i ∈ ps) : (layerRun I adv correct).EventualConsensus := by
  have hn := h.length_pos
  -- the common prefix: the snapshot of the start of the last completed round
  let Pf : ℕ → List (Item P Msg) := fun t =>
    match (t - T) / (2 * ps.length) with
    | 0 => []
    | k + 1 => items adv (T + 2 * ps.length * k)
  have hq : ∀ t k, (t - T) / (2 * ps.length) = k + 1 → T + 2 * ps.length * (k + 1) ≤ t := by
    intro t k hk
    have := Nat.div_mul_le_self (t - T) (2 * ps.length)
    rw [hk, Nat.mul_comm] at this
    have : T ≤ t := by
      by_contra hlt
      rw [show t - T = 0 by omega, Nat.zero_div] at hk
      omega
    omega
  refine ⟨⟨fun i => rfl, ?_, ?_, Pf, ?_, ?_, ?_⟩, T + 2 * ps.length, ?_⟩
  · -- Nontriviality
    intro i t
    refine ⟨fun o ho => ?_, ?_⟩
    · obtain ⟨t', ht', hs⟩ := sub_of_mem adv (correct := correct) (h.dlv_sub_items t i o ho)
      exact ⟨_, _, hs, ht'⟩
    · exact dlv_induction adv (i := i) List.Nodup (t₀ := 0) List.nodup_nil
        (fun t _ s hs => (h.goodDeliv hs).1) t (Nat.zero_le _)
  · -- Set stability
    intro i t t' htt' o ho
    induction t', htt' using Nat.le_induction with
    | base => exact ho
    | succ t' _ ih =>
      show o ∈ (run I adv (t' + 1)).dlv i
      by_cases hd : ∃ s, actAt I adv t' = .deliver i s
      · obtain ⟨s, hs⟩ := hd
        rw [dlv_succ_deliver adv hs]; exact (h.goodDeliv hs).2.2 o ih
      · push Not at hd
        rw [dlv_succ_of_ne adv hd]; exact ih
  · -- (C1)
    intro i hi t t' htt'
    show Pf t <+: (run I adv t').dlv i
    simp only [Pf]
    split
    · exact List.nil_prefix
    · rename_i k hk
      have := hq t k hk
      obtain ⟨s, hs1, -, hs3⟩ := h.dlv_round (hc i hi) k t' (by omega)
      rw [hs3]; exact (log_prefix adv hs1).map Prod.fst
  · -- (C2)
    intro t t' htt'
    have hmono : (t - T) / (2 * ps.length) ≤ (t' - T) / (2 * ps.length) :=
      Nat.div_le_div_right (by omega)
    simp only [Pf]
    split
    · exact List.nil_prefix
    · rename_i k hk
      split
      · rename_i hk'; omega
      · rename_i k' hk'
        have : k ≤ k' := by omega
        exact (log_prefix adv (by nlinarith)).map Prod.fst
  · -- (C3)
    intro o j t' hsub _
    obtain ⟨-, ho⟩ := mem_of_sub adv hsub
    refine ⟨T + 2 * ps.length * (t' + 1), by nlinarith, ?_⟩
    have : (T + 2 * ps.length * (t' + 1) - T) / (2 * ps.length) = t' + 1 := by
      rw [Nat.add_sub_cancel_left, Nat.mul_div_cancel_left _ (by omega)]
    show o ∈ Pf (T + 2 * ps.length * (t' + 1))
    simp only [Pf, this]
    exact items_mono adv (by nlinarith) ho
  · -- Eventual stability
    intro i t' t'' h1 h2
    show (run I adv t').dlv i <+: (run I adv t'').dlv i
    by_cases hi : i ∈ ps
    · obtain ⟨s', -, hs'2, hs'3⟩ := h.dlv_round hi 0 t' (by simpa using h1)
      obtain ⟨s'', hs'', e⟩ := dlv_induction adv (i := i) (fun x => ∃ s ≥ s', x = items adv s)
        (t₀ := t') ⟨s', le_rfl, hs'3⟩ (fun t ht s hs => by
          obtain ⟨-, rfl⟩ := h.deliver_tail (by omega) hs
          exact ⟨_, hs'2.trans (rrStart_mono ht), rfl⟩) t'' h2
      rw [hs'3, e]; exact (log_prefix adv hs'').map Prod.fst
    · have := dlv_induction adv (i := i) (fun x => x = (run I adv t').dlv i) (t₀ := t') rfl
        (fun t ht s hs => absurd (h.deliver_tail (by omega) hs).1 hi) t'' h2
      rw [this]

end RRTail

end Podc.EventualLinearizability.Runs
