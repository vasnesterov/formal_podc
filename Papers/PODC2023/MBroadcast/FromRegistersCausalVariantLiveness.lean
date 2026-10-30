import Papers.PODC2023.MBroadcast.FromRegistersCausalVariant
import Papers.PODC2023.MBroadcast.FromRegistersPhases

/-!
# Liveness of the causal variant

Same notion of execution, correct process and fairness as for Algorithm 2
(`FromRegistersLiveness.lean`). The processing of a register stops at a message of the current
`mbroadcast` of the reader; such a message was mbroadcast after the read message, so the first
`catch_up` started after a message is in a register delivers it.
-/

namespace Podc.MBroadcast.FromRegisters.Causal

open Function

variable {n : ℕ} {M : Type} [DecidableEq M]

/-! ## One-step lemmas -/

section StepLemmas

variable {c c' : Cfg n M}

lemma tick_log_prefix (c : Cfg n M) (p : Fin n) : c.log <+: (tick c p).log := by
  unfold tick
  split
  · exact List.prefix_rfl
  · split
    · split
      · exact List.prefix_rfl
      · exact List.prefix_append _ _
    · exact List.prefix_append _ _

lemma tick_crashed (c : Cfg n M) (p : Fin n) : (tick c p).crashed = c.crashed := by
  unfold tick
  split
  · rfl
  · split
    · split <;> rfl
    · rfl

lemma tick_phase_other (c : Cfg n M) {p r : Fin n} (h : r ≠ p) :
    (tick c p).phase r = c.phase r := by
  unfold tick
  split
  · simp [startCU, update_of_ne h]
  · split
    · split
      · simp [skipSelf, update_of_ne h]
      · simp [readReg, update_of_ne h]
    · simp [finish, update_of_ne h]

lemma tick_phase_self (c : Cfg n M) (r : Fin n) :
    (tick c r).phase r = tickPhase n (c.phase r) := by
  unfold tick
  split
  · next h => simp [startCU, tickPhase, h]
  · next o j h =>
    split
    · next hj =>
      split
      · simp [skipSelf, tickPhase, h, hj]
      · simp [readReg, tickPhase, h, hj]
    · next hj => simp [finish, tickPhase, h, hj]

lemma tick_end {r : Fin n} {o : Option M} (h : c.phase r = .catchUp o n) :
    tick c r = finish c r o := by
  simp [tick, h]

lemma tick_read {r q : Fin n} {o : Option M} (h : c.phase r = .catchUp o q.val) (hqr : q ≠ r) :
    tick c r = readReg c r q o q.val := by
  simp [tick, h, hqr]

lemma step_log_prefix {a : Act n M} (hs : step c a = some c') : c.log <+: c'.log := by
  cases a with
  | invoke p m =>
    simp only [step] at hs; split_ifs at hs; cases hs; exact List.prefix_append _ _
  | tick p => simp only [step] at hs; split_ifs at hs; cases hs; exact tick_log_prefix c p
  | crash p => simp only [step, Option.some.injEq] at hs; subst hs; exact List.prefix_rfl

lemma step_phase {a : Act n M} {r : Fin n} (hs : step c a = some c') (ha : a ≠ .tick r) :
    c'.phase r = c.phase r ∨ (c.phase r = .idle ∧ ∃ m, c'.phase r = .catchUp (some m) 0) := by
  cases a with
  | invoke p m =>
    simp only [step] at hs; split_ifs at hs with hc; cases hs
    by_cases hp : r = p
    · subst hp; exact Or.inr ⟨hc.2.1, m, by simp⟩
    · exact Or.inl (by simp [update_of_ne hp])
  | tick p =>
    simp only [step] at hs; split_ifs at hs; cases hs
    have : r ≠ p := fun h => ha (by rw [h])
    exact Or.inl (tick_phase_other c this)
  | crash p => simp only [step, Option.some.injEq] at hs; subst hs; exact Or.inl rfl

/-- A process enters the `catch_up` of `mbroadcast(m)` only by invoking it, with a fresh `m`. -/
lemma step_fresh {a : Act n M} {r : Fin n} {m : M} (hs : step c a = some c')
    (h0 : c.phase r = .idle) (h1 : c'.phase r = .catchUp (some m) 0) : Ev.bc r m ∉ c.log := by
  cases a with
  | invoke p m' =>
    simp only [step] at hs; split_ifs at hs with hc; cases hs
    by_cases hp : r = p
    · subst hp
      simp only [update_self, Phase.catchUp.injEq, Option.some.injEq, and_true] at h1
      subst h1; exact hc.2.2
    · simp only [update_of_ne hp] at h1; rw [h0] at h1; cases h1
  | tick p =>
    simp only [step] at hs; split_ifs at hs; cases hs
    by_cases hp : r = p
    · subst hp; rw [tick_phase_self, h0] at h1; simp [tickPhase] at h1
    · rw [tick_phase_other c hp, h0] at h1; cases h1
  | crash p =>
    simp only [step, Option.some.injEq] at hs; subst hs; rw [h0] at h1; cases h1

end StepLemmas

/-- Reading `SENT[q]` mdelivers the message of an entry if the histories up to this entry
contain no undelivered message of the reader. -/
lemma Inv.read_delivers {c : Cfg n M} (h : Inv c) {r q : Fin n} (hqr : q ≠ r) {e : Entry n M}
    (he : e ∈ c.sent q) (hno : ∀ z ∈ e.2, z.1 = r → z ∈ c.hist r) :
    (q, e.1) ∈ go r (c.hist r) (flat q (c.sent q)) := by
  obtain ⟨A, B, hAB⟩ := List.append_of_mem he
  have hflat : flat q (c.sent q) = (flat q A ++ (e.2 ++ [(q, e.1)])) ++ flat q B := by
    rw [hAB]; simp [flat]
  rw [hflat]
  refine go_nonblock _ _ _ ?_ _ (by simp)
  intro z hz hzr
  simp only [List.mem_append, List.mem_singleton] at hz
  rcases hz with hz | hz | rfl
  · simp only [flat, List.mem_flatMap, List.mem_append, List.mem_singleton] at hz
    obtain ⟨e', he', hz | rfl⟩ := hz
    · have hpw := h.chain q
      rw [hAB, List.pairwise_append] at hpw
      exact hno z ((hpw.2.2 e' he' e (by simp)).subset hz) hzr
    · exact absurd hzr hqr
  · exact hno z hz hzr
  · exact absurd hzr hqr

/-! ## Executions -/

/-- An infinite execution of the causal variant. -/
structure Execution (n : ℕ) (M : Type) [DecidableEq M] where
  cfg : ℕ → Cfg n M
  act : ℕ → Act n M
  start : cfg 0 = init
  valid : ∀ k, step (cfg k) (act k) = some (cfg (k + 1))

namespace Execution

variable (e : Execution n M)

/-- A correct process never crashes. -/
def Correct (p : Fin n) : Prop := ∀ k, (e.cfg k).crashed p = false

/-- Fairness: every correct process takes infinitely many local steps. -/
def Fair : Prop := ∀ p, e.Correct p → ∀ k, ∃ k' ≥ k, e.act k' = .tick p

variable {e}

lemma reachable (k : ℕ) : Reachable (e.cfg k) := by
  induction k with
  | zero => rw [e.start]; exact .init
  | succ k ih => exact .step ih (e.valid k)

lemma inv (k : ℕ) : Inv (e.cfg k) := (reachable k).inv

lemma log_prefix {k k' : ℕ} (h : k ≤ k') : (e.cfg k).log <+: (e.cfg k').log := by
  induction h with
  | refl => exact List.prefix_rfl
  | step _ ih => exact ih.trans (step_log_prefix (e.valid _))

lemma cfg_succ_tick {k : ℕ} {r : Fin n} (h : e.act k = .tick r) :
    e.cfg (k + 1) = tick (e.cfg k) r := by
  have := e.valid k
  rw [h] at this
  simp only [step] at this
  split_ifs at this
  exact (Option.some.inj this).symm

/-- The control skeleton of the execution. -/
def skel (e : Execution n M) : Skeleton n M where
  phase k := (e.cfg k).phase
  act := e.act
  other k r ha := step_phase (e.valid k) ha
  tick k r ha := by
    show (e.cfg (k + 1)).phase r = _; rw [cfg_succ_tick ha]; exact tick_phase_self _ r
  jle k r o j h := (inv k).jle r o j h

lemma ticks (hf : e.Fair) {r : Fin n} (hr : e.Correct r) : e.skel.Ticks r := hf r hr

end Execution

open Execution

variable {e : Execution n M}

-- CSLib candidate (list lemma)
lemma getElem?_of_prefix {α : Type} {l1 l2 : List α} (h : l1 <+: l2) {i : ℕ}
    (hi : i < l1.length) : l2[i]? = l1[i]? := by
  obtain ⟨t, rfl⟩ := h; exact List.getElem?_append_left hi

/-- **Local termination** of the causal variant. -/
theorem localTermination (hf : e.Fair) {p : Fin n} (hp : e.Correct p) {m : M} {k : ℕ}
    (h : Ev.bc p m ∈ (e.cfg k).log) : ∃ k', Ev.dl p p m ∈ (e.cfg k').log := by
  have hi := inv (e := e) k
  rcases hi.own p m h with h1 | ⟨j, hph⟩
  · rw [hi.hist p, mem_hdl] at h1; exact ⟨k, h1⟩
  · obtain ⟨k', -, ht, h'⟩ := Skeleton.reach_end (ticks hf hp) _ rfl (hi.jle p _ j hph) hph
    refine ⟨k' + 1, ?_⟩
    rw [cfg_succ_tick ht, tick_end h']; simp [finish, dlEvs]

/-- **Global CF-termination** of the causal variant: if a process mdelivers `m` from `q`, every
correct process eventually mdelivers `m` from `q`. -/
theorem globalCFTermination (hf : e.Fair) {p q r : Fin n} (hr : e.Correct r) {m : M} {k : ℕ}
    (h : Ev.dl p q m ∈ (e.cfg k).log) : ∃ k', Ev.dl r q m ∈ (e.cfg k').log := by
  have hbc : Ev.bc q m ∈ (e.cfg k).log := validity_bc_mem (inv k).valid h
  by_cases hqr : q = r
  · subst hqr; exact localTermination hf hr hbc
  obtain ⟨k', hk', o, ht, hph, hfresh⟩ := Skeleton.eventually_index (ticks hf hr) q.isLt k
  have hi := inv (e := e) k'
  have hpre := log_prefix (e := e) hk'
  set c := e.cfg k' with hc
  have hph' : c.phase r = .catchUp o q.val := hph
  obtain ⟨en, hen, hen1⟩ := hi.entryEx q m (hpre.subset hbc)
  obtain ⟨be, hbe, hbe'⟩ := hi.entry q en hen
  rw [hen1] at hbe
  -- the entry of `m` was written before `k`
  have hbek : be < (e.cfg k).log.length := by
    obtain ⟨b0, hb0⟩ := List.mem_iff_getElem?.1 hbc
    have hb0l : b0 < (e.cfg k).log.length := by
      by_contra hc'; rw [List.getElem?_eq_none (by omega)] at hb0; cases hb0
    have := eq_of_count_le_one (hi.uniq q m) (by rw [getElem?_of_prefix hpre hb0l]; exact hb0) hbe
    omega
  have hno : ∀ z ∈ en.2, z.1 = r → z ∈ c.hist r := by
    rintro ⟨z1, y⟩ hz hzr
    simp only at hzr; subst z1
    rw [hbe', mem_hdl] at hz
    obtain ⟨i, hi', hiz⟩ := exists_lt_of_mem_take hz
    have hv := hi.valid i q r y hiz
    rcases hi.own r y (List.mem_of_mem_take hv) with h1 | ⟨j'', h1⟩
    · exact h1
    · exfalso
      rw [hph'] at h1; simp only [Phase.catchUp.injEq] at h1; obtain ⟨rfl, -⟩ := h1
      obtain ⟨k2, hk2, hk2', h2, h3⟩ := hfresh y rfl
      apply step_fresh (e.valid k2) h2 h3
      -- `bc r y` is in the trace at time `k ≤ k2`
      obtain ⟨i', hi'i, hi'e⟩ := exists_lt_of_mem_take hv
      have hil : i < be := hi'
      have hik : i' < (e.cfg k).log.length := by omega
      have hpre2 := log_prefix (e := e) hk2
      have hpre3 := log_prefix (e := e) (show k2 ≤ k' by omega)
      have : (e.cfg k2).log[i']? = some (Ev.bc r y) := by
        have hik2 : i' < (e.cfg k2).log.length := by
          have := hpre2.length_le; omega
        rw [← getElem?_of_prefix hpre3 hik2]; exact hi'e
      exact List.mem_of_getElem? this
  have hdel := hi.read_delivers hqr hen hno
  rw [hen1] at hdel
  refine ⟨k' + 1, ?_⟩
  have hi1 := inv (e := e) (k' + 1)
  rw [← mem_hdl (z := (q, m)), ← hi1.hist r, cfg_succ_tick ht, ← hc, tick_read hph' hqr]
  simpa [readReg] using hdel

/-- **Global CS-termination** of the causal variant. -/
theorem globalCSTermination (hf : e.Fair) {p r : Fin n} (hp : e.Correct p) (hr : e.Correct r)
    {m : M} {k : ℕ} (h : Ev.bc p m ∈ (e.cfg k).log) : ∃ k', Ev.dl r p m ∈ (e.cfg k').log := by
  obtain ⟨k', h'⟩ := localTermination hf hp h
  exact globalCFTermination hf hr h'

/-! ## Non-vacuity: a fair execution with a broadcast -/

section Example

variable (hn : 0 < n) (m : M)

/-- Process `0` invokes `mbroadcast(m)`, then all processes tick in round-robin order. -/
def exCfg : ℕ → Cfg n M
  | 0 => init
  | 1 => { (init : Cfg n M) with
      sent := update (init : Cfg n M).sent ⟨0, hn⟩ [(m, [])]
      phase := update (init : Cfg n M).phase ⟨0, hn⟩ (.catchUp (some m) 0)
      log := [.bc ⟨0, hn⟩ m] }
  | k + 2 => tick (exCfg (k + 1)) ⟨k % n, Nat.mod_lt _ hn⟩

/-- The actions of `exCfg`. -/
def exAct : ℕ → Act n M
  | 0 => .invoke ⟨0, hn⟩ m
  | k + 1 => .tick ⟨k % n, Nat.mod_lt _ hn⟩

lemma exCfg_crashed : ∀ k, (exCfg hn m k).crashed = fun _ => false
  | 0 => rfl
  | 1 => rfl
  | k + 2 => by rw [exCfg, tick_crashed, exCfg_crashed (k + 1)]

/-- A fair execution without crashes in which process `0` mbroadcasts `m`. -/
def exampleExec : Execution n M where
  cfg := exCfg hn m
  act := exAct hn m
  start := rfl
  valid := by
    intro k
    match k with
    | 0 => simp [step, exAct, exCfg, init]
    | k + 1 => simp [step, exAct, exCfg, exCfg_crashed]

lemma exampleExec_correct (p : Fin n) : (exampleExec hn m).Correct p := by
  intro k; simp [exampleExec, exCfg_crashed]

lemma exampleExec_fair : (exampleExec hn m).Fair := by
  intro p _ k
  refine ⟨n * k + p.val + 1, ?_, ?_⟩
  · have := Nat.le_mul_of_pos_left k hn; omega
  · simp only [exampleExec, exAct]
    congr 1; ext; simp [Nat.mod_eq_of_lt p.isLt]

/-- In `exampleExec`, every process eventually mdelivers `m` from process `0`. -/
theorem exampleExec_delivers (p : Fin n) :
    ∃ k, Ev.dl p ⟨0, hn⟩ m ∈ ((exampleExec hn m).cfg k).log :=
  globalCSTermination (exampleExec_fair hn m) (exampleExec_correct hn m _)
    (exampleExec_correct hn m p) (k := 1) (by simp [exampleExec, exCfg])

end Example

end Podc.MBroadcast.FromRegisters.Causal
