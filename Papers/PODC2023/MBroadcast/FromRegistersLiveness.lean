import Papers.PODC2023.MBroadcast.FromRegistersPhases

/-!
# Algorithm 2: liveness (full version, Appendix A.1)

An *execution* is an infinite sequence of configurations `cfg` and actions `act` starting from
the initial configuration, each action being enabled (`step (cfg k) (act k) = some (cfg (k+1))`).
A process is *correct* if it never crashes. The execution is *fair* if every correct process takes
infinitely many local steps (`Act.tick`); since `tick p` is always enabled for an alive process,
this is weak fairness. In particular every correct process executes `catch_up` infinitely often
("periodically do catch_up()").

* `localTermination`: a correct process that has mbroadcast `m` eventually mdelivers `m` itself
  (i.e. `mbroadcast(m)` returns).
* `globalCFTermination`: if some process mdelivers `m` from `q`, every correct process eventually
  mdelivers `m` from `q`.
* `globalCSTermination`: if a correct process mbroadcasts `m`, every correct process eventually
  mdelivers `m`.
* `exampleExec`: fair executions in which a message is mbroadcast exist (the hypotheses of the
  theorems are not vacuous).
-/

namespace Podc.MBroadcast.FromRegisters

open Function

variable {n : ℕ} {M : Type} [DecidableEq M]

set_option linter.unusedSectionVars false

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

lemma tick_end {r : Fin n} {o : Option M} (h : c.phase r = .catchUp o n) :
    tick c r = finish c r o := by
  simp [tick, h]

lemma tick_read {r q : Fin n} {o : Option M} (h : c.phase r = .catchUp o q.val) (hqr : q ≠ r) :
    tick c r = readReg c r q o q.val := by
  simp [tick, h, hqr]

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

lemma step_log_prefix {a : Act n M} (hs : step c a = some c') : c.log <+: c'.log := by
  cases a with
  | invoke p m =>
    simp only [step] at hs; split_ifs at hs; cases hs; exact List.prefix_append _ _
  | tick p => simp only [step] at hs; split_ifs at hs; cases hs; exact tick_log_prefix c p
  | crash p => simp only [step, Option.some.injEq] at hs; subst hs; exact List.prefix_rfl

/-- Only `tick r` and `invoke r m` change the control position of `r`; `invoke` only from
`idle`. -/
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

end StepLemmas

/-! ## Executions -/

/-- An infinite execution of Algorithm 2. -/
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

/-- After reading `SENT[q]`, `r` has mdelivered every message mbroadcast by `q` so far. -/
lemma read_effect {r q : Fin n} (hqr : q ≠ r) {k : ℕ} {o : Option M} (ht : e.act k = .tick r)
    (hph : (e.cfg k).phase r = .catchUp o q.val) {m : M} (hm : Ev.bc q m ∈ (e.cfg k).log) :
    Ev.dl r q m ∈ (e.cfg (k + 1)).log := by
  have hi := inv (e := e) (k + 1)
  have hc : e.cfg (k + 1) = readReg (e.cfg k) r q o q.val := by
    rw [cfg_succ_tick ht, tick_read hph hqr]
  rw [← mem_dls, hi.deliv r q (Ne.symm hqr), hc]
  simp only [readReg, update_self, List.take_length]
  rw [(inv k).sent q, mem_bcs]; exact hm

end Execution

open Execution

variable {e : Execution n M}

/-- **Local termination** (full version, Appendix A.1): if a correct process `p` invokes
`mbroadcast(m)`, it eventually mdelivers `m` (i.e. the invocation returns). -/
theorem localTermination (hf : e.Fair) {p : Fin n} (hp : e.Correct p) {m : M} {k : ℕ}
    (h : Ev.bc p m ∈ (e.cfg k).log) : ∃ k', Ev.dl p p m ∈ (e.cfg k').log := by
  have hi := inv (e := e) k
  have hm : m ∈ dls (e.cfg k).log p p ++ ((e.cfg k).phase p).pending := by
    rw [hi.own p, hi.sent p, mem_bcs]; exact h
  rcases List.mem_append.1 hm with hm | hm
  · exact ⟨k, mem_dls.1 hm⟩
  · cases hph : (e.cfg k).phase p with
    | idle => rw [hph] at hm; simp at hm
    | catchUp o j =>
      rw [hph] at hm
      simp only [Phase.pending_catchUp, Option.mem_toList] at hm
      subst hm
      obtain ⟨k', -, ht, h'⟩ := Skeleton.reach_end (ticks hf hp) _ rfl (hi.jle p _ j hph) hph
      refine ⟨k' + 1, ?_⟩
      rw [cfg_succ_tick ht, tick_end h']; simp [finish]

/-- **Global CF-termination** (full version, Appendix A.1): if a process mdelivers `m` from `q`,
every correct process eventually mdelivers `m` from `q`. -/
theorem globalCFTermination (hf : e.Fair) {p q r : Fin n} (hr : e.Correct r) {m : M} {k : ℕ}
    (h : Ev.dl p q m ∈ (e.cfg k).log) : ∃ k', Ev.dl r q m ∈ (e.cfg k').log := by
  have hi := inv (e := e) k
  have hbc : Ev.bc q m ∈ (e.cfg k).log := by
    rw [← mem_bcs]; exact (hi.pre.prefix p q).subset (mem_dls.2 h)
  by_cases hqr : q = r
  · subst hqr; exact localTermination hf hr hbc
  · obtain ⟨k', hk', o, ht, hph, -⟩ := Skeleton.eventually_index (ticks hf hr) q.isLt k
    exact ⟨k' + 1, read_effect hqr ht hph ((log_prefix hk').subset hbc)⟩

/-- **Global CS-termination** (full version, Appendix A.1): if a correct process mbroadcasts `m`,
every correct process eventually mdelivers `m`. -/
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
      sent := update (init : Cfg n M).sent ⟨0, hn⟩ [m]
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

end Podc.MBroadcast.FromRegisters
