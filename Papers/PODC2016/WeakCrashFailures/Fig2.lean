import Papers.PODC2016.WeakCrashFailures.Failures
import Cslib.Foundations.Data.Nat.Descent

/-!
# Section 4: k-set consensus with `ℓ + k − 2` crash `(n − ℓ)`-failures (Fig. 2)

G. Taubenfeld, *Computing in the presence of weak crash failures*, PODC 2016; full version
*Weak Failures: Definitions, Algorithms and Impossibility Results*, §4 (Fig. 2, Lemmas 5–8,
Theorems 4–6).

## Model

* `n` processes `Fin n`, process `p` has input `x p`.
* `Flag` is one single-writer atomic snapshot object: `Flag.update(p, 1)` is one step and
  `Flag.scan` is one step. Since the flag of a process is only ever set to `1`, its state is the
  set `flag` of the processes that have set their flag.
* `decision : Option V` is a multi-writer atomic register (initially `⊥ = none`).
* `EX[1]` (one-shot mutual exclusion) and `EX[2]` (one-shot `(k − 1)`-exclusion) are modelled by
  their specification. Their state is the set `ent g` of processes that have entered the critical
  section of `EX[g]`. *Safety* is built into the step relation: an `enter` step succeeds only while
  fewer than `cap g` processes have entered (in Fig. 2 nobody ever leaves the critical section: an
  entrant writes `decision` and terminates). *Liveness* (deadlock-freedom, Appendix A) is a
  hypothesis `DF g e` on executions: if strictly fewer than `cap g` processes are delayed forever in
  `EX[g]`, and some process is trying (and not delayed), then some process eventually enters.
* Line 7 runs two threads in parallel: the entry code of `EX[group]` and a checker that reads
  `decision`. Steps are events `(p, a)`; while `p` is trying, `a = rd` is a read of `decision`,
  `a = ex` is an entry-code step that does not enter, and `a = enter` is an attempt to enter.
  Outside line 7 the action component is ignored.
* Executions are infinite event sequences `e : ℕ → Fin n × Act` run from the initial
  configuration; their schedule is `sched e t = (e t).1`. A process is correct iff it takes
  infinitely many steps (terminated processes keep taking no-op steps: participation is required).
  `Fair e`: every correct process takes infinitely many steps of each thread.
-/

namespace Podc.WeakCrashFailures.Fig2

open Cslib.SWMR Podc.WeakCrashFailures

/-- The two exclusion objects: `one` is `EX[1]` (mutual exclusion), `two` is `EX[2]`
(`(k − 1)`-exclusion). -/
inductive Grp | one | two
  deriving DecidableEq

/-- The capacity of `EX[g]`: `EX[1]` admits one process, `EX[2]` admits `k − 1`. -/
def cap (k : ℕ) : Grp → ℕ
  | .one => 1
  | .two => k - 1

/-- Program counter of a process. `start`: before line 1; `scan`: in the repeat loop (lines 2–5);
`trying g`: participating in `EX[g]` (line 7); `cs`: entered the critical section of its group,
about to write `decision` (line 10); `done v`: decided `v` and terminated. -/
inductive PC (V : Type) | start | scan | trying (g : Grp) | cs | done (v : V)

/-- The process has exited the repeat loop. -/
def PC.exited {V : Type} : PC V → Bool
  | .start => false
  | .scan => false
  | _ => true

/-- The action component of an event (only relevant at line 7). -/
inductive Act | rd | ex | enter
  deriving DecidableEq

/-- A configuration of Fig. 2. -/
structure Config (n : ℕ) (V : Type) where
  /-- program counters -/
  pc : Fin n → PC V
  /-- the local variable `counter` (meaningful once the process exited the repeat loop) -/
  counter : Fin n → ℕ
  /-- the processes whose `Flag` component is `1` -/
  flag : Finset (Fin n)
  /-- the register `decision` -/
  decision : Option V
  /-- the processes that entered the critical section of `EX[g]` -/
  ent : Grp → Finset (Fin n)

/-- The exit threshold of the repeat loop, `n − ℓ − k + 2` (exact whenever `ℓ + k ≤ n + 2`). -/
def thr (n ℓ k : ℕ) : ℕ := n + 2 - (ℓ + k)

/-- Line 6: the group chosen with counter value `c`. -/
def grp (n ℓ c : ℕ) : Grp := if c ≤ n - ℓ then .two else .one

variable {n : ℕ} (ℓ k : ℕ) {V : Type} (x : Fin n → V)

/-- The initial configuration. -/
def init (n : ℕ) (V : Type) : Config n V where
  pc := fun _ => .start
  counter := fun _ => 0
  flag := ∅
  decision := none
  ent := fun _ => ∅

/-- One step of Fig. 2 for the event `ev = (p, a)`. -/
def step (C : Config n V) (ev : Fin n × Act) : Config n V :=
  match C.pc ev.1, ev.2 with
  | .start, _ => { C with pc := Function.update C.pc ev.1 .scan, flag := insert ev.1 C.flag }
  | .scan, _ =>
      if thr n ℓ k ≤ C.flag.card then
        { C with pc := Function.update C.pc ev.1 (.trying (grp n ℓ C.flag.card)),
                 counter := Function.update C.counter ev.1 C.flag.card }
      else C
  | .trying _, .rd =>
      match C.decision with
      | some v => { C with pc := Function.update C.pc ev.1 (.done v) }
      | none => C
  | .trying _, .ex => C
  | .trying g, .enter =>
      if (C.ent g).card < cap k g then
        { C with pc := Function.update C.pc ev.1 .cs,
                 ent := Function.update C.ent g (insert ev.1 (C.ent g)) }
      else C
  | .cs, _ =>
      { C with pc := Function.update C.pc ev.1 (.done (x ev.1)), decision := some (x ev.1) }
  | .done _, _ => C

/-- Inversion of `step`: the possible effects of an event `(p, a)`. -/
lemma step_cases (C : Config n V) (p : Fin n) (a : Act) :
    step ℓ k x C (p, a) = C ∨
    (C.pc p = .start ∧
      step ℓ k x C (p, a) = { C with pc := Function.update C.pc p .scan,
                                       flag := insert p C.flag }) ∨
    (C.pc p = .scan ∧ thr n ℓ k ≤ C.flag.card ∧
      step ℓ k x C (p, a) = { C with pc := Function.update C.pc p (.trying (grp n ℓ C.flag.card)),
                                       counter := Function.update C.counter p C.flag.card }) ∨
    (∃ g v, C.pc p = .trying g ∧ C.decision = some v ∧
      step ℓ k x C (p, a) = { C with pc := Function.update C.pc p (.done v) }) ∨
    (∃ g, C.pc p = .trying g ∧ (C.ent g).card < cap k g ∧ a = .enter ∧
      step ℓ k x C (p, a) = { C with pc := Function.update C.pc p .cs,
                                       ent := Function.update C.ent g (insert p (C.ent g)) }) ∨
    (C.pc p = .cs ∧
      step ℓ k x C (p, a) = { C with pc := Function.update C.pc p (.done (x p)),
                                       decision := some (x p) }) := by
  unfold step
  cases h : C.pc p with
  | start => simp
  | scan => by_cases hc : thr n ℓ k ≤ C.flag.card <;> simp [hc]
  | trying g =>
    cases a with
    | rd => cases C.decision <;> simp
    | ex => simp
    | enter => by_cases hc : (C.ent g).card < cap k g <;> simp [hc]
  | cs => simp
  | done v => simp


/-! ### Reachable configurations and their invariants -/

/-- Configurations reachable from the initial one by finitely many events. -/
inductive Reachable : Config n V → Prop
  | init : Reachable (init n V)
  | step {C : Config n V} (ev : Fin n × Act) : Reachable C → Reachable (step ℓ k x C ev)

/-- The set `S_m` of processes that exited the repeat loop with `counter ≤ m` (Lemma 5). -/
def lowSet (C : Config n V) (m : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun p => (C.pc p).exited ∧ C.counter p ≤ m

/-- The invariant of Fig. 2 (all clauses are ghost-free statements about one configuration). -/
structure Inv (C : Config n V) : Prop where
  flag_iff : ∀ p, p ∈ C.flag ↔ C.pc p ≠ .start
  trying_grp : ∀ p g, C.pc p = .trying g → grp n ℓ (C.counter p) = g
  counter_le : ∀ p, (C.pc p).exited → C.counter p ≤ C.flag.card
  thr_le : ∀ p, (C.pc p).exited → thr n ℓ k ≤ C.counter p
  lowSet_card : ∀ m, (lowSet C m).card ≤ m
  ent_card : ∀ g, (C.ent g).card ≤ cap k g
  ent_pc : ∀ g p, p ∈ C.ent g → C.pc p = .cs ∨ ∃ v, C.pc p = .done v
  cs_ent : ∀ p, C.pc p = .cs → ∃ g, p ∈ C.ent g
  dec_val : ∀ v, C.decision = some v → ∃ g, ∃ q ∈ C.ent g, x q = v
  done_val : ∀ p v, C.pc p = .done v → ∃ g, ∃ q ∈ C.ent g, x q = v
  done_dec : ∀ p v, C.pc p = .done v → C.decision.isSome

lemma inv_init : Inv ℓ k x (init n V) where
  flag_iff := by simp [init]
  trying_grp := by simp [init]
  counter_le := by simp [init, PC.exited]
  thr_le := by simp [init, PC.exited]
  lowSet_card := by simp [lowSet, init, PC.exited]
  ent_card := by simp [init]
  ent_pc := by simp [init]
  cs_ent := by simp [init]
  dec_val := by simp [init]
  done_val := by simp [init]
  done_dec := by simp [init]

namespace Inv

variable {ℓ k x}

lemma lowSet_eq_of_exited {C D : Config n V} (hpc : ∀ q, (D.pc q).exited = (C.pc q).exited)
    (hc : ∀ q, (C.pc q).exited → D.counter q = C.counter q) (m : ℕ) :
    lowSet D m = lowSet C m := by
  ext q
  simp only [lowSet, Finset.mem_filter, Finset.mem_univ, true_and, hpc]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, by rwa [← hc q h1]⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, by rwa [hc q h1]⟩

lemma lowSet_subset_flag {C : Config n V} (hI : Inv ℓ k x C) (m : ℕ) : lowSet C m ⊆ C.flag := by
  intro q hq
  simp only [lowSet, Finset.mem_filter, Finset.mem_univ, true_and] at hq
  refine (hI.flag_iff q).2 fun h => ?_
  simp [h, PC.exited] at hq

/-- The counting argument of Lemma 5: if every member of `lowSet D m` is in `lowSet C m` or is a
flagged process that saw at most `m` flags, then `lowSet D m` still has at most `m` members. -/
lemma lowSet_card_le_of {C D : Config n V} (hI : Inv ℓ k x C) (m : ℕ)
    (h : ∀ q ∈ lowSet D m, q ∈ lowSet C m ∨ (q ∈ C.flag ∧ C.flag.card ≤ m)) :
    (lowSet D m).card ≤ m := by
  by_cases hex : ∃ q ∈ lowSet D m, q ∉ lowSet C m
  · obtain ⟨q, hq, hqC⟩ := hex
    have hfl : C.flag.card ≤ m := ((h q hq).resolve_left hqC).2
    refine le_trans (Finset.card_le_card fun r hr => ?_) hfl
    rcases h r hr with h' | h'
    · exact hI.lowSet_subset_flag m h'
    · exact h'.1
  · push Not at hex
    exact (Finset.card_le_card hex).trans (hI.lowSet_card m)

lemma not_mem_ent_of_pc {C : Config n V} (hI : Inv ℓ k x C) {p : Fin n} {g : Grp}
    (h1 : C.pc p ≠ .cs) (h2 : ∀ v, C.pc p ≠ .done v) : p ∉ C.ent g := by
  intro hp
  rcases hI.ent_pc g p hp with h | ⟨v, h⟩
  · exact h1 h
  · exact h2 v h

lemma step_start {C : Config n V} (hI : Inv ℓ k x C) {p : Fin n} (hp : C.pc p = .start) :
    Inv ℓ k x { C with pc := Function.update C.pc p .scan, flag := insert p C.flag } := by
  have hpe : ∀ g, p ∉ C.ent g := fun g => hI.not_mem_ent_of_pc (by simp [hp]) (by simp [hp])
  constructor
  · intro q
    by_cases hq : q = p
    · subst hq; simp
    · simp [hq, hI.flag_iff q]
  · intro q g
    by_cases hq : q = p
    · subst hq; simp
    · simpa [Function.update_of_ne hq] using hI.trying_grp q g
  · intro q
    by_cases hq : q = p
    · subst hq; simp [PC.exited]
    · simp only [Function.update_of_ne hq]
      intro h
      exact (hI.counter_le q h).trans (Finset.card_le_card (Finset.subset_insert _ _))
  · intro q
    by_cases hq : q = p
    · subst hq; simp [PC.exited]
    · simpa [Function.update_of_ne hq] using hI.thr_le q
  · intro m
    rw [lowSet_eq_of_exited (C := C) ?_ ?_ m]
    · exact hI.lowSet_card m
    · intro q
      by_cases hq : q = p
      · subst hq; simp [hp, PC.exited]
      · simp [Function.update_of_ne hq]
    · intro q _; rfl
  · exact hI.ent_card
  · intro g q hq'
    have hq : q ≠ p := by rintro rfl; exact hpe g hq'
    simpa [Function.update_of_ne hq] using hI.ent_pc g q hq'
  · intro q
    by_cases hq : q = p
    · subst hq; simp
    · simpa [Function.update_of_ne hq] using hI.cs_ent q
  · exact hI.dec_val
  · intro q v
    by_cases hq : q = p
    · subst hq; simp
    · simpa [Function.update_of_ne hq] using hI.done_val q v
  · intro q v
    by_cases hq : q = p
    · subst hq; simp
    · simpa [Function.update_of_ne hq] using hI.done_dec q v

lemma step_scan {C : Config n V} (hI : Inv ℓ k x C) {p : Fin n} (hp : C.pc p = .scan)
    (hthr : thr n ℓ k ≤ C.flag.card) :
    Inv ℓ k x { C with pc := Function.update C.pc p (.trying (grp n ℓ C.flag.card)),
                       counter := Function.update C.counter p C.flag.card } := by
  have hpe : ∀ g, p ∉ C.ent g := fun g => hI.not_mem_ent_of_pc (by simp [hp]) (by simp [hp])
  have hpf : p ∈ C.flag := (hI.flag_iff p).2 (by simp [hp])
  constructor
  · intro q
    by_cases hq : q = p
    · subst hq; simp [hpf]
    · simpa [Function.update_of_ne hq] using hI.flag_iff q
  · intro q g
    by_cases hq : q = p
    · subst hq; simp
    · simpa [Function.update_of_ne hq] using hI.trying_grp q g
  · intro q
    by_cases hq : q = p
    · subst hq; simp
    · simpa [Function.update_of_ne hq] using hI.counter_le q
  · intro q
    by_cases hq : q = p
    · subst hq; simp [hthr]
    · simpa [Function.update_of_ne hq] using hI.thr_le q
  · intro m
    refine hI.lowSet_card_le_of m fun q hq => ?_
    simp only [lowSet, Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
    by_cases hqp : q = p
    · subst hqp; simp at hq; exact Or.inr ⟨hpf, hq.2⟩
    · simp only [Function.update_of_ne hqp] at hq; exact Or.inl hq
  · exact hI.ent_card
  · intro g q hq'
    have hq : q ≠ p := by rintro rfl; exact hpe g hq'
    simpa [Function.update_of_ne hq] using hI.ent_pc g q hq'
  · intro q
    by_cases hq : q = p
    · subst hq; simp
    · simpa [Function.update_of_ne hq] using hI.cs_ent q
  · exact hI.dec_val
  · intro q v
    by_cases hq : q = p
    · subst hq; simp
    · simpa [Function.update_of_ne hq] using hI.done_val q v
  · intro q v
    by_cases hq : q = p
    · subst hq; simp
    · simpa [Function.update_of_ne hq] using hI.done_dec q v

lemma step_read {C : Config n V} (hI : Inv ℓ k x C) {p : Fin n} {g : Grp} {v : V}
    (hp : C.pc p = .trying g) (hv : C.decision = some v) :
    Inv ℓ k x { C with pc := Function.update C.pc p (.done v) } := by
  have hpe : ∀ g, p ∉ C.ent g := fun g => hI.not_mem_ent_of_pc (by simp [hp]) (by simp [hp])
  have hpf : p ∈ C.flag := (hI.flag_iff p).2 (by simp [hp])
  constructor
  · intro q
    by_cases hq : q = p
    · subst hq; simp [hpf]
    · simpa [Function.update_of_ne hq] using hI.flag_iff q
  · intro q g
    by_cases hq : q = p
    · subst hq; simp
    · simpa [Function.update_of_ne hq] using hI.trying_grp q g
  · intro q
    by_cases hq : q = p
    · subst hq; intro _; simpa using hI.counter_le q (by simp [hp, PC.exited])
    · simpa [Function.update_of_ne hq] using hI.counter_le q
  · intro q
    by_cases hq : q = p
    · subst hq; intro _; simpa using hI.thr_le q (by simp [hp, PC.exited])
    · simpa [Function.update_of_ne hq] using hI.thr_le q
  · intro m
    rw [lowSet_eq_of_exited (C := C) ?_ ?_ m]
    · exact hI.lowSet_card m
    · intro q
      by_cases hq : q = p
      · subst hq; simp [hp, PC.exited]
      · simp [Function.update_of_ne hq]
    · intro q _; rfl
  · exact hI.ent_card
  · intro g q hq'
    have hq : q ≠ p := by rintro rfl; exact hpe g hq'
    simpa [Function.update_of_ne hq] using hI.ent_pc g q hq'
  · intro q
    by_cases hq : q = p
    · subst hq; simp
    · simpa [Function.update_of_ne hq] using hI.cs_ent q
  · exact hI.dec_val
  · intro q w
    by_cases hq : q = p
    · subst hq; simp only [Function.update_self, PC.done.injEq]
      rintro rfl; exact hI.dec_val _ hv
    · simpa [Function.update_of_ne hq] using hI.done_val q w
  · intro q w
    by_cases hq : q = p
    · subst hq; simp [hv]
    · simpa [Function.update_of_ne hq] using hI.done_dec q w

lemma step_enter {C : Config n V} (hI : Inv ℓ k x C) {p : Fin n} {g : Grp}
    (hp : C.pc p = .trying g) (hc : (C.ent g).card < cap k g) :
    Inv ℓ k x { C with pc := Function.update C.pc p .cs,
                       ent := Function.update C.ent g (insert p (C.ent g)) } := by
  have hpe : ∀ g, p ∉ C.ent g := fun g => hI.not_mem_ent_of_pc (by simp [hp]) (by simp [hp])
  have hpf : p ∈ C.flag := (hI.flag_iff p).2 (by simp [hp])
  have hmono : ∀ g', C.ent g' ⊆ Function.update C.ent g (insert p (C.ent g)) g' := by
    intro g'
    by_cases hg : g' = g
    · subst hg; simp
    · simp [Function.update_of_ne hg]
  constructor
  · intro q
    by_cases hq : q = p
    · subst hq; simp [hpf]
    · simpa [Function.update_of_ne hq] using hI.flag_iff q
  · intro q g
    by_cases hq : q = p
    · subst hq; simp
    · simpa [Function.update_of_ne hq] using hI.trying_grp q g
  · intro q
    by_cases hq : q = p
    · subst hq; intro _; simpa using hI.counter_le q (by simp [hp, PC.exited])
    · simpa [Function.update_of_ne hq] using hI.counter_le q
  · intro q
    by_cases hq : q = p
    · subst hq; intro _; simpa using hI.thr_le q (by simp [hp, PC.exited])
    · simpa [Function.update_of_ne hq] using hI.thr_le q
  · intro m
    rw [lowSet_eq_of_exited (C := C) ?_ ?_ m]
    · exact hI.lowSet_card m
    · intro q
      by_cases hq : q = p
      · subst hq; simp [hp, PC.exited]
      · simp [Function.update_of_ne hq]
    · intro q _; rfl
  · intro g'
    by_cases hg : g' = g
    · subst hg; simp only [Function.update_self]
      exact (Finset.card_insert_le _ _).trans hc
    · simpa [Function.update_of_ne hg] using hI.ent_card g'
  · intro g' q hq'
    by_cases hq : q = p
    · subst hq; simp
    · have : q ∈ C.ent g' := by
        by_cases hg : g' = g
        · subst hg; simpa [hq] using hq'
        · simpa [Function.update_of_ne hg] using hq'
      simpa [Function.update_of_ne hq] using hI.ent_pc g' q this
  · intro q
    by_cases hq : q = p
    · subst hq; intro _; exact ⟨g, by simp⟩
    · simp only [Function.update_of_ne hq]
      intro h
      obtain ⟨g', hg'⟩ := hI.cs_ent q h
      exact ⟨g', hmono g' hg'⟩
  · intro v hv
    obtain ⟨g', q, hq, hqv⟩ := hI.dec_val v hv
    exact ⟨g', q, hmono g' hq, hqv⟩
  · intro q w
    by_cases hq : q = p
    · subst hq; simp
    · simp only [Function.update_of_ne hq]
      intro h
      obtain ⟨g', r, hr, hrv⟩ := hI.done_val q w h
      exact ⟨g', r, hmono g' hr, hrv⟩
  · intro q w
    by_cases hq : q = p
    · subst hq; simp
    · simpa [Function.update_of_ne hq] using hI.done_dec q w

lemma step_cs {C : Config n V} (hI : Inv ℓ k x C) {p : Fin n} (hp : C.pc p = .cs) :
    Inv ℓ k x { C with pc := Function.update C.pc p (.done (x p)), decision := some (x p) } := by
  have hpf : p ∈ C.flag := (hI.flag_iff p).2 (by simp [hp])
  constructor
  · intro q
    by_cases hq : q = p
    · subst hq; simp [hpf]
    · simpa [Function.update_of_ne hq] using hI.flag_iff q
  · intro q g
    by_cases hq : q = p
    · subst hq; simp
    · simpa [Function.update_of_ne hq] using hI.trying_grp q g
  · intro q
    by_cases hq : q = p
    · subst hq; intro _; simpa using hI.counter_le q (by simp [hp, PC.exited])
    · simpa [Function.update_of_ne hq] using hI.counter_le q
  · intro q
    by_cases hq : q = p
    · subst hq; intro _; simpa using hI.thr_le q (by simp [hp, PC.exited])
    · simpa [Function.update_of_ne hq] using hI.thr_le q
  · intro m
    rw [lowSet_eq_of_exited (C := C) ?_ ?_ m]
    · exact hI.lowSet_card m
    · intro q
      by_cases hq : q = p
      · subst hq; simp [hp, PC.exited]
      · simp [Function.update_of_ne hq]
    · intro q _; rfl
  · exact hI.ent_card
  · intro g q hq'
    by_cases hq : q = p
    · subst hq; simp
    · simpa [Function.update_of_ne hq] using hI.ent_pc g q hq'
  · intro q
    by_cases hq : q = p
    · subst hq; simp
    · simpa [Function.update_of_ne hq] using hI.cs_ent q
  · intro v hv
    simp only [Option.some.injEq] at hv
    subst hv
    obtain ⟨g, hg⟩ := hI.cs_ent p hp
    exact ⟨g, p, hg, rfl⟩
  · intro q w
    by_cases hq : q = p
    · subst hq; simp only [Function.update_self, PC.done.injEq]
      rintro rfl
      obtain ⟨g, hg⟩ := hI.cs_ent q hp
      exact ⟨g, q, hg, rfl⟩
    · simpa [Function.update_of_ne hq] using hI.done_val q w
  · intro q w _
    simp

/-- The invariant is preserved by every step. -/
lemma step {C : Config n V} (hI : Inv ℓ k x C) (ev : Fin n × Act) : Inv ℓ k x (Fig2.step ℓ k x C ev) := by
  obtain ⟨p, a⟩ := ev
  rcases step_cases ℓ k x C p a with h | ⟨hp, h⟩ | ⟨hp, hthr, h⟩ | ⟨g, v, hp, hv, h⟩ |
      ⟨g, hp, hc, -, h⟩ | ⟨hp, h⟩ <;> rw [h]
  · exact hI
  · exact hI.step_start hp
  · exact hI.step_scan hp hthr
  · exact hI.step_read hp hv
  · exact hI.step_enter hp hc
  · exact hI.step_cs hp

end Inv

lemma Reachable.inv {C : Config n V} (h : Reachable ℓ k x C) : Inv ℓ k x C := by
  induction h with
  | init => exact inv_init ℓ k x
  | step ev _ ih => exact ih.step ev

/-! ### Local effects of a step -/

section StepLemmas

variable {ℓ k x}

/-- How a step changes the program counter of a process `q`. -/
lemma step_pc (C : Config n V) (p : Fin n) (a : Act) (q : Fin n) :
    (Fig2.step ℓ k x C (p, a)).pc q = C.pc q ∨
    (q = p ∧ C.pc p = .start ∧ (Fig2.step ℓ k x C (p, a)).pc p = .scan) ∨
    (q = p ∧ C.pc p = .scan ∧ thr n ℓ k ≤ C.flag.card ∧
      (Fig2.step ℓ k x C (p, a)).pc p = .trying (grp n ℓ C.flag.card) ∧
      (Fig2.step ℓ k x C (p, a)).counter p = C.flag.card) ∨
    (q = p ∧ ∃ g v, C.pc p = .trying g ∧ C.decision = some v ∧
      (Fig2.step ℓ k x C (p, a)).pc p = .done v) ∨
    (q = p ∧ ∃ g, C.pc p = .trying g ∧ a = .enter ∧ (Fig2.step ℓ k x C (p, a)).pc p = .cs) ∨
    (q = p ∧ C.pc p = .cs ∧ (Fig2.step ℓ k x C (p, a)).pc p = .done (x p)) := by
  by_cases hq : q = p
  · subst hq
    rcases step_cases ℓ k x C q a with h | ⟨hp, h⟩ | ⟨hp, hthr, h⟩ | ⟨g, v, hp, hv, h⟩ |
      ⟨g, hp, hc, ha, h⟩ | ⟨hp, h⟩ <;> rw [h]
    · exact Or.inl rfl
    · exact Or.inr (Or.inl ⟨rfl, hp, by simp⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨rfl, hp, hthr, by simp, by simp⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, g, v, hp, hv, by simp⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, g, hp, ha, by simp⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, hp, by simp⟩))))
  · left
    rcases step_cases ℓ k x C p a with h | ⟨hp, h⟩ | ⟨hp, hthr, h⟩ | ⟨g, v, hp, hv, h⟩ |
      ⟨g, hp, hc, ha, h⟩ | ⟨hp, h⟩ <;> rw [h] <;> simp [Function.update_of_ne hq]

lemma step_pc_of_ne (C : Config n V) {p q : Fin n} (a : Act) (hq : q ≠ p) :
    (Fig2.step ℓ k x C (p, a)).pc q = C.pc q := by
  rcases step_pc (ℓ := ℓ) (k := k) (x := x) C p a q with h | h | h | h | h | h
  · exact h
  all_goals exact absurd h.1 hq

lemma step_counter (C : Config n V) (p : Fin n) (a : Act) (q : Fin n)
    (hq : (C.pc q).exited) : (Fig2.step ℓ k x C (p, a)).counter q = C.counter q := by
  rcases step_cases ℓ k x C p a with h | ⟨hp, h⟩ | ⟨hp, hthr, h⟩ | ⟨g, v, hp, hv, h⟩ |
      ⟨g, hp, hc, ha, h⟩ | ⟨hp, h⟩ <;> rw [h]
  case inr.inr.inl =>
    have : q ≠ p := by rintro rfl; simp [hp, PC.exited] at hq
    simp [Function.update_of_ne this]

lemma step_decision (C : Config n V) (p : Fin n) (a : Act) :
    (Fig2.step ℓ k x C (p, a)).decision = C.decision ∨
    (Fig2.step ℓ k x C (p, a)).decision = some (x p) := by
  rcases step_cases ℓ k x C p a with h | ⟨hp, h⟩ | ⟨hp, hthr, h⟩ | ⟨g, v, hp, hv, h⟩ |
      ⟨g, hp, hc, ha, h⟩ | ⟨hp, h⟩ <;> rw [h] <;> simp

lemma step_ent_subset (C : Config n V) (p : Fin n) (a : Act) (g : Grp) :
    C.ent g ⊆ (Fig2.step ℓ k x C (p, a)).ent g := by
  rcases step_cases ℓ k x C p a with h | ⟨hp, h⟩ | ⟨hp, hthr, h⟩ | ⟨g', v, hp, hv, h⟩ |
      ⟨g', hp, hc, ha, h⟩ | ⟨hp, h⟩ <;> rw [h]
  case inr.inr.inr.inr.inl =>
    by_cases hg : g = g'
    · subst hg; simp
    · simp [Function.update_of_ne hg]

lemma Inv.step_flag {C : Config n V} (hI : Inv ℓ k x C) (p : Fin n) (a : Act) :
    (Fig2.step ℓ k x C (p, a)).flag = insert p C.flag := by
  by_cases hp0 : C.pc p = .start
  · simp [Fig2.step, hp0]
  · rw [Finset.insert_eq_of_mem ((hI.flag_iff p).2 hp0)]
    rcases step_cases ℓ k x C p a with h | ⟨hp, h⟩ | ⟨hp, hthr, h⟩ | ⟨g, v, hp, hv, h⟩ |
        ⟨g, hp, hc, ha, h⟩ | ⟨hp, h⟩ <;> rw [h]
    exact absurd hp hp0

lemma step_scan_exit (C : Config n V) {p : Fin n} (a : Act) (hp : C.pc p = .scan)
    (h : thr n ℓ k ≤ C.flag.card) :
    (Fig2.step ℓ k x C (p, a)).pc p = .trying (grp n ℓ C.flag.card) := by
  simp [Fig2.step, hp, h]

lemma step_cs_decision (C : Config n V) {p : Fin n} (a : Act) (hp : C.pc p = .cs) :
    (Fig2.step ℓ k x C (p, a)).decision = some (x p) := by
  simp [Fig2.step, hp]

lemma step_read_done (C : Config n V) {p : Fin n} {w : V} (hp : (C.pc p).exited)
    (hw : C.decision = some w) : ∃ v, (Fig2.step ℓ k x C (p, .rd)).pc p = .done v := by
  cases h : C.pc p with
  | start => simp [h, PC.exited] at hp
  | scan => simp [h, PC.exited] at hp
  | trying g => exact ⟨w, by simp [Fig2.step, h, hw]⟩
  | cs => exact ⟨x p, by simp [Fig2.step, h]⟩
  | done v => exact ⟨v, by simp [Fig2.step, h]⟩

lemma step_enter_mem (C : Config n V) {p : Fin n} {a : Act} {g : Grp} (hp : C.pc p = .trying g)
    (hcs : (Fig2.step ℓ k x C (p, a)).pc p = .cs) : p ∈ (Fig2.step ℓ k x C (p, a)).ent g := by
  rcases step_cases ℓ k x C p a with h | ⟨hp', h⟩ | ⟨hp', hthr, h⟩ | ⟨g', v, hp', hv, h⟩ |
      ⟨g', hp', hc, ha, h⟩ | ⟨hp', h⟩ <;> rw [h] at hcs ⊢
  · rw [hp] at hcs; cases hcs
  · simp at hcs
  · simp at hcs
  · simp at hcs
  · rw [hp] at hp'; cases hp'; simp
  · rw [hp] at hp'; cases hp'

lemma step_ent_mem (C : Config n V) {p : Fin n} {a : Act} {g : Grp} {r : Fin n}
    (hr : r ∈ (Fig2.step ℓ k x C (p, a)).ent g) : r ∈ C.ent g ∨ (r = p ∧ C.pc p = .trying g) := by
  rcases step_cases ℓ k x C p a with h | ⟨hp', h⟩ | ⟨hp', hthr, h⟩ | ⟨g', v, hp', hv, h⟩ |
      ⟨g', hp', hc, ha, h⟩ | ⟨hp', h⟩ <;> rw [h] at hr
  case inr.inr.inr.inr.inl =>
    by_cases hg : g = g'
    · subst hg
      simp only [Function.update_self, Finset.mem_insert] at hr
      rcases hr with rfl | hr
      · exact Or.inr ⟨rfl, hp'⟩
      · exact Or.inl hr
    · simp only [Function.update_of_ne hg] at hr
      exact Or.inl hr
  all_goals exact Or.inl hr

end StepLemmas

/-! ### Theorem 6: k-agreement and validity -/

/-- The values decided in configuration `C`. -/
def decided (C : Config n V) : Set V := {v | ∃ p, C.pc p = .done v}

lemma Inv.decided_subset {C : Config n V} (hI : Inv ℓ k x C) [DecidableEq V] :
    decided C ⊆ ↑((C.ent .one ∪ C.ent .two).image x) := by
  rintro v ⟨p, hp⟩
  obtain ⟨g, q, hq, rfl⟩ := hI.done_val p v hp
  refine Finset.mem_coe.2 (Finset.mem_image_of_mem x ?_)
  cases g
  · exact Finset.mem_union_left _ hq
  · exact Finset.mem_union_right _ hq

/-- **Theorem 6** of [Taubenfeld PODC'16, full version] (k-agreement & validity): in every
reachable configuration of Fig. 2 (for `k ≥ 1`) at most `k` different values are decided, and each
decided value is the input of a participating process (one whose `Flag` is set, i.e. that has
taken a step). -/
theorem theorem6 (hk : 1 ≤ k) {C : Config n V} (hC : Reachable ℓ k x C) :
    (decided C).ncard ≤ k ∧ ∀ v ∈ decided C, ∃ q ∈ C.flag, x q = v := by
  classical
  have hI := hC.inv
  refine ⟨?_, ?_⟩
  · calc (decided C).ncard ≤ (↑((C.ent .one ∪ C.ent .two).image x) : Set V).ncard :=
          Set.ncard_le_ncard (hI.decided_subset) (Finset.finite_toSet _)
      _ = ((C.ent .one ∪ C.ent .two).image x).card := Set.ncard_coe_finset _
      _ ≤ (C.ent .one ∪ C.ent .two).card := Finset.card_image_le
      _ ≤ (C.ent .one).card + (C.ent .two).card := Finset.card_union_le _ _
      _ ≤ cap k .one + cap k .two := Nat.add_le_add (hI.ent_card _) (hI.ent_card _)
      _ = k := by simp [cap]; omega
  · rintro v ⟨p, hp⟩
    obtain ⟨g, q, hq, rfl⟩ := hI.done_val p v hp
    refine ⟨q, (hI.flag_iff q).2 ?_, rfl⟩
    rcases hI.ent_pc g q hq with h | ⟨w, h⟩ <;> simp [h]

/-! ### Executions -/

/-- The configuration after the first `t` events of `e`. -/
def exec (e : ℕ → Fin n × Act) : ℕ → Config n V
  | 0 => init n V
  | t + 1 => Fig2.step ℓ k x (exec e t) (e t)

/-- The schedule of an event sequence. -/
def sched (e : ℕ → Fin n × Act) : ℕ → Fin n := fun t => (e t).1

variable {ℓ k x}

lemma reachable_exec (e : ℕ → Fin n × Act) (t : ℕ) : Reachable ℓ k x (exec ℓ k x e t) := by
  induction t with
  | zero => exact .init
  | succ t ih => exact .step _ ih

lemma inv_exec (e : ℕ → Fin n × Act) (t : ℕ) : Inv ℓ k x (exec ℓ k x e t) :=
  (reachable_exec e t).inv

section Exec

variable {e : ℕ → Fin n × Act}

/-- The `Flag` object holds exactly the processes that have taken a step. -/
lemma flag_exec (e : ℕ → Fin n × Act) (t : ℕ) :
    (exec ℓ k x e t).flag = started (sched e) t := by
  induction t with
  | zero => simp [exec, init, started, pre]
  | succ t ih =>
    rw [started_succ, ← ih]
    show (Fig2.step ℓ k x (exec ℓ k x e t) ((e t).1, (e t).2)).flag = _
    exact (inv_exec e t).step_flag _ _

/-- The number of set flags is the point contention. -/
lemma card_flag_exec (e : ℕ → Fin n × Act) (t : ℕ) :
    (exec ℓ k x e t).flag.card = contention (sched e) t := by
  rw [flag_exec]; rfl

lemma exec_succ (e : ℕ → Fin n × Act) (t : ℕ) :
    exec ℓ k x e (t + 1) = Fig2.step ℓ k x (exec ℓ k x e t) ((e t).1, (e t).2) := rfl

lemma pc_succ_of_ne {t : ℕ} {p : Fin n} (h : sched e t ≠ p) :
    (exec ℓ k x e (t + 1)).pc p = (exec ℓ k x e t).pc p := by
  rw [exec_succ]; exact step_pc_of_ne _ _ (Ne.symm h)

lemma exited_succ {t : ℕ} {p : Fin n} (h : ((exec ℓ k x e t).pc p).exited) :
    ((exec ℓ k x e (t + 1)).pc p).exited ∧
      (exec ℓ k x e (t + 1)).counter p = (exec ℓ k x e t).counter p := by
  rw [exec_succ]
  refine ⟨?_, step_counter _ _ _ _ h⟩
  rcases step_pc (ℓ := ℓ) (k := k) (x := x) (exec ℓ k x e t) (e t).1 (e t).2 p with
    h' | ⟨rfl, h1, h2⟩ | ⟨rfl, h1, -, h2, -⟩ | ⟨rfl, g, v, h1, -, h2⟩ | ⟨rfl, g, h1, -, h2⟩ |
    ⟨rfl, h1, h2⟩
  · rwa [h']
  · simp [h1, PC.exited] at h
  · simp [h1, PC.exited] at h
  all_goals simp [h2, PC.exited]

lemma exited_mono {t t' : ℕ} {p : Fin n} (h : ((exec ℓ k x e t).pc p).exited) (ht : t ≤ t') :
    ((exec ℓ k x e t').pc p).exited ∧
      (exec ℓ k x e t').counter p = (exec ℓ k x e t).counter p := by
  induction t', ht using Nat.le_induction with
  | base => exact ⟨h, rfl⟩
  | succ t' _ ih => exact ⟨(exited_succ ih.1).1, (exited_succ ih.1).2.trans ih.2⟩

lemma decision_mono {t t' : ℕ} (h : (exec ℓ k x e t).decision.isSome) (ht : t ≤ t') :
    (exec ℓ k x e t').decision.isSome := by
  induction t', ht using Nat.le_induction with
  | base => exact h
  | succ t' _ ih =>
    rw [exec_succ]
    rcases step_decision (ℓ := ℓ) (k := k) (x := x) (exec ℓ k x e t') (e t').1 (e t').2 with
      h' | h' <;> rw [h'] <;> simp [ih]

lemma ent_mono {t t' : ℕ} (g : Grp) (ht : t ≤ t') :
    (exec ℓ k x e t).ent g ⊆ (exec ℓ k x e t').ent g := by
  induction t', ht using Nat.le_induction with
  | base => exact subset_rfl
  | succ t' _ ih => exact ih.trans (step_ent_subset _ _ _ _)

lemma trying_succ {t : ℕ} {p : Fin n} {g : Grp} (h : (exec ℓ k x e t).pc p = .trying g) :
    (exec ℓ k x e (t + 1)).pc p = .trying g ∨ (exec ℓ k x e (t + 1)).pc p = .cs ∨
      ∃ v, (exec ℓ k x e (t + 1)).pc p = .done v := by
  rw [exec_succ]
  rcases step_pc (ℓ := ℓ) (k := k) (x := x) (exec ℓ k x e t) (e t).1 (e t).2 p with
    h' | ⟨rfl, h1, h2⟩ | ⟨rfl, h1, -, h2, -⟩ | ⟨rfl, g', v, h1, -, h2⟩ | ⟨rfl, g', h1, -, h2⟩ |
    ⟨rfl, h1, h2⟩
  · exact Or.inl (h'.trans h)
  · rw [h] at h1; cases h1
  · rw [h] at h1; cases h1
  · exact Or.inr (Or.inr ⟨v, h2⟩)
  · exact Or.inr (Or.inl h2)
  · rw [h] at h1; cases h1

/-- Lemma 5 of [Taubenfeld PODC'16, full version]: in every reachable configuration, for every
`m`, at most `m` processes have exited the repeat loop with `counter ≤ m`. -/
theorem lemma5 {C : Config n V} (hC : Reachable ℓ k x C) (m : ℕ) : (lowSet C m).card ≤ m :=
  hC.inv.lowSet_card m

variable (ℓ k x) in
/-- The processes that ever participate in `EX[g]`. -/
noncomputable def everTrying (e : ℕ → Fin n × Act) (g : Grp) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun p => ∃ t, (exec ℓ k x e t).pc p = .trying g

variable (ℓ k x) in
lemma mem_everTrying {g : Grp} {p : Fin n} :
    p ∈ everTrying ℓ k x e g ↔ ∃ t, (exec ℓ k x e t).pc p = .trying g := by
  classical
  simp [everTrying]

/-- Lemma 6 of [Taubenfeld PODC'16, full version]: at most `n − ℓ` processes ever participate in
`EX[2]` (so at least `ℓ` processes never do). -/
theorem lemma6 (e : ℕ → Fin n × Act) : (everTrying ℓ k x e .two).card ≤ n - ℓ := by
  have hev : ∀ p, ∃ T, ∀ m ≥ T, p ∈ everTrying ℓ k x e .two →
      p ∈ lowSet (exec ℓ k x e m) (n - ℓ) := by
    intro p
    by_cases hp : p ∈ everTrying ℓ k x e .two
    · obtain ⟨t, ht⟩ := (mem_everTrying ℓ k x).1 hp
      refine ⟨t, fun m hm _ => ?_⟩
      have hex : ((exec ℓ k x e t).pc p).exited := by simp [ht, PC.exited]
      have hg := (inv_exec e t).trying_grp p _ ht
      have hc : (exec ℓ k x e t).counter p ≤ n - ℓ := by
        unfold grp at hg; split_ifs at hg with h; exact h
      obtain ⟨h1, h2⟩ := exited_mono hex hm
      simp only [lowSet, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨h1, h2 ▸ hc⟩
    · exact ⟨0, fun _ _ h => absurd h hp⟩
  obtain ⟨T, -, hT⟩ := Nat.eventually_forall_of_finite hev 0
  exact (Finset.card_le_card fun p hp => hT T le_rfl p hp).trans ((inv_exec e T).lowSet_card _)

/-- A process in `EX[1]` has taken a step at a time when the point contention exceeded `n − ℓ`
(it saw more than `n − ℓ` flags when it left the repeat loop). -/
lemma exists_step_of_trying_one {t : ℕ} {p : Fin n} (h : (exec ℓ k x e t).pc p = .trying .one) :
    ∃ s < t, sched e s = p ∧ n - ℓ < contention (sched e) (s + 1) := by
  induction t with
  | zero => simp [exec, init] at h
  | succ t ih =>
    by_cases h0 : (exec ℓ k x e t).pc p = .trying .one
    · obtain ⟨s, hs, h1, h2⟩ := ih h0
      exact ⟨s, by omega, h1, h2⟩
    · rw [exec_succ] at h
      rcases step_pc (ℓ := ℓ) (k := k) (x := x) (exec ℓ k x e t) (e t).1 (e t).2 p with
        h' | ⟨rfl, h1, h2⟩ | ⟨rfl, h1, -, h2, -⟩ | ⟨rfl, g', v, h1, -, h2⟩ | ⟨rfl, g', h1, -, h2⟩ |
        ⟨rfl, h1, h2⟩
      · exact absurd (h'.symm.trans h) h0
      · rw [h2] at h; cases h
      · rw [h2] at h
        have hg : grp n ℓ (exec ℓ k x e t).flag.card = .one := PC.trying.inj h
        unfold grp at hg
        split_ifs at hg with hc
        refine ⟨t, by omega, rfl, ?_⟩
        rw [card_flag_exec] at hc
        exact lt_of_lt_of_le (by omega) (contention_mono _ (Nat.le_succ t))
      · rw [h2] at h; cases h
      · rw [h2] at h; cases h
      · rw [h2] at h; cases h

/-- Lemma 7 of [Taubenfeld PODC'16, full version]: if all failures are `(n − ℓ)`-failures, a
process that participates in `EX[1]` is correct. -/
theorem lemma7 {f : ℕ} (hadm : WeakAdmissible (n - ℓ) f (sched e)) {t : ℕ} {p : Fin n}
    (h : (exec ℓ k x e t).pc p = .trying .one) : InfOften (sched e) p := by
  by_contra hf
  obtain ⟨s, -, hs, hc⟩ := exists_step_of_trying_one h
  have := (hadm.2 p hf).contention_le_of_step hs
  omega

end Exec

/-! ### Fairness, the liveness specification of the exclusion objects, and termination -/

/-- Fairness of the two parallel threads of line 7: every correct process takes infinitely many
`decision`-reading steps and infinitely many other steps. -/
def Fair (e : ℕ → Fin n × Act) : Prop :=
  ∀ p, InfOften (sched e) p →
    (∀ N, ∃ t ≥ N, e t = (p, .rd)) ∧ (∀ N, ∃ t ≥ N, (e t).1 = p ∧ (e t).2 ≠ .rd)

variable (ℓ k x) in
/-- The processes that are *delayed forever* in the entry code of `EX[g]`: they participate in
`EX[g]` at some time but take only finitely many entry-code steps while trying (they crashed,
abandoned `EX[g]` after reading `decision`, or entered the critical section and stay there). -/
def Del (e : ℕ → Fin n × Act) (g : Grp) : Set (Fin n) :=
  {p | (∃ t, (exec ℓ k x e t).pc p = .trying g) ∧
    {t | (e t).1 = p ∧ (e t).2 ≠ .rd ∧ (exec ℓ k x e t).pc p = .trying g}.Finite}

variable (ℓ k x) in
/-- Deadlock-freedom of `EX[g]` (Appendix A, `cap g`-deadlock-freedom): if strictly fewer than
`cap g` processes are delayed forever, then whenever some (non-delayed) process is trying, some
process eventually enters the critical section. -/
def DF (e : ℕ → Fin n × Act) (g : Grp) : Prop :=
  (Del ℓ k x e g).ncard < cap k g →
    ∀ t p, (exec ℓ k x e t).pc p = .trying g → p ∉ Del ℓ k x e g →
      ∃ t' ≥ t, ∃ q, (exec ℓ k x e t').pc q = .trying g ∧ (exec ℓ k x e (t' + 1)).pc q = .cs

section Termination

variable {e : ℕ → Fin n × Act}

/-- All correct processes have taken a step by some time `T`. -/
lemma exists_started_correct (σ : ℕ → Fin n) :
    ∃ T, ∀ q, InfOften σ q → q ∈ started σ T := by
  have h : ∀ q, ∃ T, ∀ m ≥ T, InfOften σ q → q ∈ started σ m := by
    intro q
    by_cases hq : InfOften σ q
    · obtain ⟨s, -, hs⟩ := hq 0
      exact ⟨s + 1, fun m hm _ => mem_started.2 ⟨s, by omega, hs⟩⟩
    · exact ⟨0, fun _ _ h => absurd h hq⟩
  obtain ⟨T, -, hT⟩ := Nat.eventually_forall_of_finite h 0
  exact ⟨T, fun q hq => hT T le_rfl q hq⟩

/-- Many correct processes means large contention. -/
lemma contention_ge (σ : ℕ → Fin n) {T : ℕ} (hT : ∀ q, InfOften σ q → q ∈ started σ T) :
    n - (Faulty σ).ncard ≤ contention σ T := by
  have h1 := Set.ncard_add_ncard_compl (Faulty σ)
  have h2 : (Faulty σ)ᶜ ⊆ ↑(started σ T) := fun q hq => by
    simp only [Set.mem_compl_iff, Faulty, Set.mem_ofPred_eq, not_not] at hq
    exact hT q hq
  have h3 := Set.ncard_le_ncard h2 (Finset.finite_toSet _)
  rw [Set.ncard_coe_finset] at h3
  simp only [Nat.card_eq_fintype_card, Fintype.card_fin] at h1
  unfold contention
  omega

/-- Termination of the repeat loop (first paragraph of the proof of Theorem 5): with at most
`ℓ + k − 2` faulty processes, every correct process exits the repeat loop. -/
lemma exits_loop (hℓk : 2 ≤ ℓ + k) (hf : (Faulty (sched e)).ncard ≤ ℓ + k - 2) {p : Fin n}
    (hp : InfOften (sched e) p) : ∃ t, ((exec ℓ k x e t).pc p).exited := by
  obtain ⟨T, hT⟩ := exists_started_correct (sched e)
  have hcT := contention_ge (sched e) hT
  by_contra hne
  push Not at hne
  obtain ⟨s, hs, hsp⟩ := hp T
  have hpf : p ∈ (exec ℓ k x e s).flag := by
    rw [flag_exec]; exact started_mono _ hs (hT p hp)
  have hscan : (exec ℓ k x e s).pc p = .scan := by
    have h1 := ((inv_exec e s).flag_iff p).1 hpf
    have h2 := hne s
    revert h1 h2
    cases (exec ℓ k x e s).pc p <;> simp [PC.exited]
  have hthr : thr n ℓ k ≤ (exec ℓ k x e s).flag.card := by
    rw [card_flag_exec]
    have := contention_mono (sched e) hs
    unfold thr; omega
  have := hne (s + 1)
  rw [exec_succ, show (e s).1 = p from hsp, step_scan_exit _ _ hscan hthr] at this
  simp [PC.exited] at this

/-- Second paragraph of the proof of Theorem 5: once `decision` has been written, every correct
process eventually decides. -/
lemma decides_of_decision (hfair : Fair e) (hℓk : 2 ≤ ℓ + k)
    (hf : (Faulty (sched e)).ncard ≤ ℓ + k - 2) {p : Fin n} (hp : InfOften (sched e) p) {t₁ : ℕ}
    (h₁ : (exec ℓ k x e t₁).decision.isSome) : ∃ t v, (exec ℓ k x e t).pc p = .done v := by
  obtain ⟨t₀, h₀⟩ := exits_loop hℓk hf hp
  obtain ⟨s, hs, hes⟩ := (hfair p hp).1 (max t₀ t₁)
  have hex := (exited_mono h₀ (le_of_max_le_left hs)).1
  obtain ⟨w, hw⟩ := Option.isSome_iff_exists.1 (decision_mono h₁ (le_of_max_le_right hs))
  obtain ⟨v, hv⟩ := step_read_done (ℓ := ℓ) (k := k) (x := x) _ hex hw
  refine ⟨s + 1, v, ?_⟩
  rw [exec_succ, show ((e s).1, (e s).2) = (p, Act.rd) by rw [hes]]
  exact hv

/-- A correct process in the critical section eventually writes `decision`. -/
lemma decision_of_cs {p : Fin n} (hp : InfOften (sched e) p) {t : ℕ}
    (h : (exec ℓ k x e t).pc p = .cs) : ∃ t', (exec ℓ k x e t').decision.isSome := by
  have key : ∀ s ≥ t, (exec ℓ k x e s).pc p = .cs ∨ (exec ℓ k x e s).decision.isSome := by
    intro s hs
    induction s, hs using Nat.le_induction with
    | base => exact Or.inl h
    | succ s _ ih =>
      rcases ih with ih | ih
      · by_cases hps : sched e s = p
        · right
          rw [exec_succ, show (e s).1 = p from hps,
            step_cs_decision (ℓ := ℓ) (k := k) (x := x) _ _ ih]
          rfl
        · left; rw [pc_succ_of_ne hps]; exact ih
      · exact Or.inr (decision_mono ih (Nat.le_succ s))
  obtain ⟨s, hs, hsp⟩ := hp t
  rcases key s hs with h' | h'
  · refine ⟨s + 1, ?_⟩
    rw [exec_succ, show (e s).1 = p from hsp, step_cs_decision (ℓ := ℓ) (k := k) (x := x) _ _ h']
    rfl
  · exact ⟨s, h'⟩

/-- If `decision` is never written, a correct process that participates in `EX[g]` keeps trying
forever. -/
lemma trying_forever (hD : ∀ t, (exec ℓ k x e t).decision = none) {p : Fin n}
    (hp : InfOften (sched e) p) {t : ℕ} {g : Grp} (h : (exec ℓ k x e t).pc p = .trying g) :
    ∀ s ≥ t, (exec ℓ k x e s).pc p = .trying g := by
  intro s hs
  induction s, hs using Nat.le_induction with
  | base => exact h
  | succ s _ ih =>
    rcases trying_succ ih with h' | h' | ⟨v, h'⟩
    · exact h'
    · obtain ⟨t', ht'⟩ := decision_of_cs hp h'
      simp [hD t'] at ht'
    · have := (inv_exec e (s + 1)).done_dec p v h'
      simp [hD (s + 1)] at this

/-- If `decision` is never written, a correct process that participates in `EX[g]` is not
delayed forever in `EX[g]`. -/
lemma not_mem_del (hfair : Fair e) (hD : ∀ t, (exec ℓ k x e t).decision = none) {p : Fin n}
    (hp : InfOften (sched e) p) {t : ℕ} {g : Grp} (h : (exec ℓ k x e t).pc p = .trying g) :
    p ∉ Del ℓ k x e g := by
  rintro ⟨-, hfin⟩
  apply Set.infinite_of_forall_exists_gt _ hfin
  intro a
  obtain ⟨s, hs, h1, h2⟩ := (hfair p hp).2 (max (a + 1) t)
  exact ⟨s, ⟨h1, h2, trying_forever hD hp h s (le_of_max_le_right hs)⟩,
    by have := le_of_max_le_left hs; omega⟩

/-- Entering the critical section of `EX[g]` adds a new member to `ent g`. -/
lemma card_ent_lt_of_enter {t : ℕ} {q : Fin n} {g : Grp} (h1 : (exec ℓ k x e t).pc q = .trying g)
    (h2 : (exec ℓ k x e (t + 1)).pc q = .cs) :
    ((exec ℓ k x e t).ent g).card < ((exec ℓ k x e (t + 1)).ent g).card := by
  have hq : sched e t = q := by
    by_contra hne
    rw [pc_succ_of_ne hne, h1] at h2
    cases h2
  have hnot : q ∉ (exec ℓ k x e t).ent g :=
    (inv_exec e t).not_mem_ent_of_pc (by simp [h1]) (by simp [h1])
  have hmem : q ∈ (exec ℓ k x e (t + 1)).ent g := by
    rw [exec_succ, show (e t).1 = q from hq] at h2 ⊢
    exact step_enter_mem _ h1 h2
  exact Finset.card_lt_card
    ⟨ent_mono g (Nat.le_succ t), fun hsub => hnot (hsub hmem)⟩

/-- The heart of the proof of Theorem 5: if `decision` is never written, a correct process that
participates in `EX[g]` contradicts deadlock-freedom of `EX[g]` as soon as fewer than `cap g`
processes are delayed forever (entries would happen infinitely often, but each process enters at
most once). -/
lemma no_progress (hfair : Fair e) (hD : ∀ t, (exec ℓ k x e t).decision = none) {p : Fin n}
    (hp : InfOften (sched e) p) {t : ℕ} {g : Grp} (h : (exec ℓ k x e t).pc p = .trying g)
    (hdel : (Del ℓ k x e g).ncard < cap k g) (hDF : DF ℓ k x e g) : False := by
  obtain ⟨T, hT, hc⟩ := Nat.eventually_const_of_le_succ (f := fun m => ((exec ℓ k x e m).ent g).card)
    (N := t) (B := n) (fun m _ => (Finset.card_le_univ _).trans (by simp))
    (fun m _ => Finset.card_le_card (ent_mono g (Nat.le_succ m)))
  obtain ⟨t', ht', q, hq1, hq2⟩ := hDF hdel T p (trying_forever hD hp h T hT)
    (not_mem_del hfair hD hp h)
  have := card_ent_lt_of_enter hq1 hq2
  have e1 := hc t' ht'
  have e2 := hc (t' + 1) (by omega)
  omega

/-- **Theorem 5** of [Taubenfeld PODC'16, full version] (termination), under a weaker hypothesis
than the paper: only `2 ≤ ℓ + k` (the paper assumes `ℓ ≥ 1`, `k ≥ 1` and `n ≥ 2ℓ + k − 2`).
In every fair execution with at most `ℓ + k − 2` crash `(n − ℓ)`-failures in which the exclusion
objects are deadlock-free, every correct process eventually decides. -/
theorem theorem5 (hℓk : 2 ≤ ℓ + k) (hfair : Fair e) (hDF1 : DF ℓ k x e .one)
    (hDF2 : DF ℓ k x e .two) (hadm : WeakAdmissible (n - ℓ) (ℓ + k - 2) (sched e)) {p : Fin n}
    (hp : InfOften (sched e) p) : ∃ t v, (exec ℓ k x e t).pc p = .done v := by
  by_cases hdec : ∃ t, (exec ℓ k x e t).decision.isSome
  · obtain ⟨t₁, h₁⟩ := hdec
    exact decides_of_decision hfair hℓk hadm.1 hp h₁
  exfalso
  have hD : ∀ t, (exec ℓ k x e t).decision = none := by
    intro t; push Not at hdec; simpa using hdec t
  -- every correct process eventually participates in some `EX[g]`
  have htry : ∀ q, InfOften (sched e) q → ∃ t g, (exec ℓ k x e t).pc q = .trying g := by
    intro q hq
    obtain ⟨t, ht⟩ := exits_loop (x := x) hℓk hadm.1 hq
    refine ⟨t, ?_⟩
    cases hpc : (exec ℓ k x e t).pc q with
    | start => simp [hpc, PC.exited] at ht
    | scan => simp [hpc, PC.exited] at ht
    | trying g => exact ⟨g, rfl⟩
    | cs =>
      obtain ⟨t', ht'⟩ := decision_of_cs hq hpc
      simp [hD t'] at ht'
    | done v =>
      have := (inv_exec e t).done_dec q v hpc
      simp [hD t] at this
  by_cases h1 : ∃ t q, (exec ℓ k x e t).pc q = .trying .one
  · -- some process participates in `EX[1]`: it is correct (Lemma 7) and nobody is delayed
    obtain ⟨t, q, hq⟩ := h1
    have hdel : Del ℓ k x e .one = ∅ := by
      ext r
      simp only [Set.mem_empty_iff_false, iff_false]
      intro hr
      obtain ⟨t', ht'⟩ := hr.1
      exact not_mem_del hfair hD (lemma7 hadm ht') ht' hr
    exact no_progress hfair hD (lemma7 hadm hq) hq (by simp [hdel, cap]) hDF1
  · push Not at h1
    obtain ⟨t, g, hg⟩ := htry p hp
    have hg2 : g = .two := by
      cases g
      · exact absurd hg (h1 t p)
      · rfl
    subst hg2
    set G := everTrying ℓ k x e .two with hG
    have hpG : p ∈ G := (mem_everTrying ℓ k x).2 ⟨t, hg⟩
    have hGcard := lemma6 (ℓ := ℓ) (k := k) (x := x) e
    rw [← hG] at hGcard
    have hGpos : 1 ≤ G.card := Finset.card_pos.2 ⟨p, hpG⟩
    -- processes outside `G` are faulty
    have hcompl : (↑G : Set (Fin n))ᶜ ⊆ Faulty (sched e) := by
      intro r hr hcorr
      obtain ⟨t', g', ht'⟩ := htry r hcorr
      cases g'
      · exact h1 t' r ht'
      · exact hr ((mem_everTrying ℓ k x).2 ⟨t', ht'⟩)
    -- the processes delayed forever in `EX[2]` are faulty members of `G`
    have hdelsub : Del ℓ k x e .two ⊆ Faulty (sched e) ∩ ↑G := by
      intro r hr
      obtain ⟨t', ht'⟩ := hr.1
      refine ⟨fun hcorr => not_mem_del hfair hD hcorr ht' hr, ?_⟩
      exact Finset.mem_coe.2 ((mem_everTrying ℓ k x).2 ⟨t', ht'⟩)
    have hsplit := Set.ncard_inter_add_ncard_sdiff_eq_ncard (Faulty (sched e)) (↑G : Set (Fin n))
    have hdiff : Faulty (sched e) \ ↑G = (↑G : Set (Fin n))ᶜ := by
      ext r
      simp only [Set.mem_sdiff, Set.mem_compl_iff]
      exact ⟨fun h => h.2, fun h => ⟨hcompl h, h⟩⟩
    rw [hdiff] at hsplit
    have hGc := Set.ncard_add_ncard_compl (↑G : Set (Fin n))
    rw [Set.ncard_coe_finset] at hGc
    simp only [Nat.card_eq_fintype_card, Fintype.card_fin] at hGc
    have hle := Set.ncard_le_ncard hdelsub
    have hF := hadm.1
    refine no_progress hfair hD hp hg ?_ hDF2
    simp only [cap]
    omega

/-- Lemma 8 of [Taubenfeld PODC'16, full version]: under the hypotheses of Theorem 4 there is a
correct process. (Not needed for our proof of Theorem 5.) -/
theorem lemma8 (hℓ : 1 ≤ ℓ) (hk : 1 ≤ k) (hn : 2 * ℓ + k - 2 ≤ n)
    (hadm : WeakAdmissible (n - ℓ) (ℓ + k - 2) (sched e)) : ∃ p, InfOften (sched e) p := by
  by_contra h
  push Not at h
  have huniv : Faulty (sched e) = Set.univ := Set.eq_univ_of_forall h
  have := hadm.1
  rw [huniv, Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin] at this
  omega

end Termination

/-! ### Theorem 4 -/

/-- **Theorem 4** of [Taubenfeld PODC'16, full version], with the weaker hypotheses `1 ≤ k` and
`2 ≤ ℓ + k` (instead of `ℓ ≥ 1`, `k ≥ 1`, `n ≥ 2ℓ + k − 2`): the algorithm of Fig. 2, with any
exclusion objects meeting their specification, solves k-set consensus tolerating `ℓ + k − 2` crash
`(n − ℓ)`-failures.
* *k-agreement and validity*: at any time of any execution at most `k` values are decided, each the
  input of a participating process;
* *termination*: in every fair execution with deadlock-free exclusion objects and at most
  `ℓ + k − 2` faulty processes, all of them `(n − ℓ)`-failures, every correct process decides. -/
theorem theorem4' (hk : 1 ≤ k) (hℓk : 2 ≤ ℓ + k) (x : Fin n → V) :
    (∀ (e : ℕ → Fin n × Act) t, (decided (exec ℓ k x e t)).ncard ≤ k ∧
      ∀ v ∈ decided (exec ℓ k x e t), ∃ q ∈ started (sched e) t, x q = v) ∧
    (∀ e : ℕ → Fin n × Act, Fair e → DF ℓ k x e .one → DF ℓ k x e .two →
      WeakAdmissible (n - ℓ) (ℓ + k - 2) (sched e) →
      ∀ p, InfOften (sched e) p → ∃ t v, (exec ℓ k x e t).pc p = .done v) := by
  refine ⟨fun e t => ?_, fun e hfair h1 h2 hadm p hp => theorem5 hℓk hfair h1 h2 hadm hp⟩
  have h := theorem6 ℓ k x hk (reachable_exec e t)
  rw [flag_exec] at h
  exact h

/-- **Theorem 4** of [Taubenfeld PODC'16, full version], with the paper's hypotheses
`ℓ ≥ 1`, `k ≥ 1`, `n ≥ 2ℓ + k − 2` (the last one is not needed, see `theorem4'`). -/
theorem theorem4 (hℓ : 1 ≤ ℓ) (hk : 1 ≤ k) (_hn : 2 * ℓ + k - 2 ≤ n) (x : Fin n → V) :
    (∀ (e : ℕ → Fin n × Act) t, (decided (exec ℓ k x e t)).ncard ≤ k ∧
      ∀ v ∈ decided (exec ℓ k x e t), ∃ q ∈ started (sched e) t, x q = v) ∧
    (∀ e : ℕ → Fin n × Act, Fair e → DF ℓ k x e .one → DF ℓ k x e .two →
      WeakAdmissible (n - ℓ) (ℓ + k - 2) (sched e) →
      ∀ p, InfOften (sched e) p → ∃ t v, (exec ℓ k x e t).pc p = .done v) :=
  theorem4' hk (by omega) x

/-! ### Non-vacuity of the hypotheses -/

section NonVacuity

variable {e : ℕ → Fin n × Act}

lemma exists_trying_of_mem_ent {t : ℕ} {g : Grp} {r : Fin n}
    (hr : r ∈ (exec ℓ k x e t).ent g) : ∃ s < t, (exec ℓ k x e s).pc r = .trying g := by
  induction t with
  | zero => simp [exec, init] at hr
  | succ t ih =>
    rw [exec_succ] at hr
    rcases step_ent_mem _ hr with h | ⟨rfl, h⟩
    · obtain ⟨s, hs, h'⟩ := ih h
      exact ⟨s, by omega, h'⟩
    · exact ⟨t, by omega, h⟩

/-- Processes that entered the critical section of `EX[g]` are delayed forever in `EX[g]`. -/
lemma ent_subset_del (t : ℕ) (g : Grp) :
    ↑((exec ℓ k x e t).ent g) ⊆ Del ℓ k x e g := by
  intro r hr
  rw [Finset.mem_coe] at hr
  refine ⟨(exists_trying_of_mem_ent hr).elim fun s h => ⟨s, h.2⟩, ?_⟩
  refine (Set.finite_lt_nat t).subset fun s hs => ?_
  obtain ⟨-, -, hs⟩ := hs
  by_contra hst
  have hr' := ent_mono g (Nat.le_of_not_lt hst) hr
  rcases (inv_exec e s).ent_pc g r hr' with h | ⟨v, h⟩ <;> rw [h] at hs <;> cases hs

/-- *Eager* exclusion objects meet the specification: if no event is an entry-code step that
declines to enter (every non-read step of a trying process attempts to enter), then both
exclusion objects are deadlock-free in the sense of `DF`. -/
theorem df_of_eager (heager : ∀ t, (e t).2 ≠ .ex) (g : Grp) : DF ℓ k x e g := by
  intro hdel t p hp hpD
  have hinf : {s | (e s).1 = p ∧ (e s).2 ≠ .rd ∧ (exec ℓ k x e s).pc p = .trying g}.Infinite :=
    fun hfin => hpD ⟨⟨t, hp⟩, hfin⟩
  obtain ⟨t', ⟨h1, h2, h3⟩, ht'⟩ := hinf.exists_gt t
  have ha : (e t').2 = .enter := by
    have := heager t'
    cases h : (e t').2 <;> simp_all
  have hev : e t' = (p, .enter) := Prod.ext h1 ha
  by_cases hc : ((exec ℓ k x e t').ent g).card < cap k g
  · refine ⟨t', ht'.le, p, h3, ?_⟩
    rw [exec_succ, show ((e t').1, (e t').2) = (p, Act.enter) by rw [hev]]
    simp [Fig2.step, h3, hc]
  · exfalso
    have := Set.ncard_le_ncard (ent_subset_del (ℓ := ℓ) (k := k) (x := x) (e := e) t' g)
      (Set.toFinite _)
    rw [Set.ncard_coe_finset] at this
    omega

/-- A round-robin execution (no failures): at time `t` process `(t / 2) mod n` reads `decision`
(`t` even) or tries to enter (`t` odd). -/
def roundRobin (hn : 0 < n) (t : ℕ) : Fin n × Act :=
  (⟨t / 2 % n, Nat.mod_lt _ hn⟩, if t % 2 = 0 then .rd else .enter)

lemma roundRobin_hits (hn : 0 < n) (p : Fin n) (N : ℕ) (b : ℕ) (hb : b < 2) :
    ∃ t ≥ N, (roundRobin hn t).1 = p ∧ t % 2 = b := by
  refine ⟨2 * (n * N + p.val) + b, ?_, ?_, ?_⟩
  · have : N ≤ n * N := Nat.le_mul_of_pos_left N hn
    omega
  · ext
    simp only [roundRobin]
    have h2 : (2 * (n * N + p.val) + b) / 2 = n * N + p.val := by omega
    rw [h2, Nat.mul_add_mod, Nat.mod_eq_of_lt p.isLt]
  · omega

/-- The hypotheses of Theorem 5 are satisfiable (for every `n ≥ 1`, `ℓ`, `k`): the round-robin
execution is fair, has no faulty process, and its exclusion objects are deadlock-free. -/
theorem roundRobin_hyps (hn : 0 < n) :
    Fair (roundRobin hn) ∧ DF ℓ k x (roundRobin hn) .one ∧ DF ℓ k x (roundRobin hn) .two ∧
      WeakAdmissible (n - ℓ) (ℓ + k - 2) (sched (roundRobin hn)) ∧
      ∀ p, InfOften (sched (roundRobin hn)) p := by
  have heager : ∀ t, (roundRobin hn t).2 ≠ .ex := by
    intro t; simp only [roundRobin]; split_ifs <;> simp
  have hinf : ∀ p, InfOften (sched (roundRobin hn)) p := by
    intro p N
    obtain ⟨t, ht, h1, -⟩ := roundRobin_hits hn p N 0 (by omega)
    exact ⟨t, ht, h1⟩
  have hfaulty : Faulty (sched (roundRobin hn)) = ∅ := by
    ext p; simp [Faulty, hinf p]
  refine ⟨fun p _ => ⟨fun N => ?_, fun N => ?_⟩, df_of_eager heager _, df_of_eager heager _,
    ⟨by simp [hfaulty], by simp [hfaulty]⟩, hinf⟩
  · obtain ⟨t, ht, h1, h2⟩ := roundRobin_hits hn p N 0 (by omega)
    refine ⟨t, ht, ?_⟩
    rw [← h1]; simp [roundRobin, h2]
  · obtain ⟨t, ht, h1, h2⟩ := roundRobin_hits hn p N 1 (by omega)
    refine ⟨t, ht, h1, ?_⟩
    simp [roundRobin, h2]

end NonVacuity

end Podc.WeakCrashFailures.Fig2
