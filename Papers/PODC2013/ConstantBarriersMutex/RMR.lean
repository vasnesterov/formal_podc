import Papers.PODC2013.ConstantBarriersMutex.InvDefs

/-!
# The cache-coherent RMR cost model and barrier counting (Section 3 of the paper)

The paper (Section 3): "Each write to a shared variable incurs an RMR. A read by process `p` of a
shared variable `v` incurs an RMR if (1) it is the first read of `v` by `p`, or (2) it is
preceded by a write of another process to `v` that was performed after `p`'s previous read of
`v`."

We model this with a ghost *cache* computed along a run (`Run.cache`); the configurations of
`Model.lean` are unchanged.

* `c p v = true` means that `p` holds a valid copy of `v`. Initially no copy is valid.
* A read by `p` of `v` that is served from `p`'s own store buffer (TSO store forwarding) costs
  nothing and does not touch the cache. A read served from memory costs one RMR iff `p` has no
  valid copy, and afterwards `p` has a valid copy.
* Every *performed* write to `v` by a process `q` (the adversary flushing `q`'s buffer, a barrier
  step of `q` performing a buffered write, the writes a CAS of `q` performs first, and a
  successful CAS of `q` itself) invalidates the copies of `v` of all processes other than `q`
  (rule (2): only writes of *another* process count, so `q`'s own writes neither invalidate nor
  validate its copy). A failed CAS writes nothing and invalidates nothing.
* Every *issued* write costs one RMR (charged when it is issued, i.e. to the passage that issues
  it), and every CAS costs one RMR. Performing a buffered write costs nothing more.

`Cfg.perf s e` is the list of writes performed by the event `e` (`mem_next`: the memory after
`e` is the memory before updated by `perf`). Statement 35's `foreach`, the `enqueue`/`dequeue`
of `promQ` and `exits ← exits + 1` are modelled as in `Model.lean`: each step performs at most
one read and issues at most one write.
-/

-- The case analyses below use generic tactic combinators; some branches do not need every
-- simp lemma or tactic.
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false

namespace Podc.ConstantBarriersMutex

open Finset

variable {h : ℕ}

/-- Shared variables (cache lines). -/
inductive Var (h : ℕ) where
  | node (i : ℕ)
  | promQ
  | apply (q : Proc h)
  | signal (q : Proc h)
  | inPromQ (q : Proc h)
  | lock
  | exits
  deriving DecidableEq

/-- The variable written by a write. -/
def W.var : W h → Var h
  | .node i _ => .node i
  | .promQ _ => .promQ
  | .apply q _ => .apply q
  | .signal q _ => .signal q
  | .inPromQ q _ => .inPromQ q
  | .lock _ => .lock
  | .exits _ => .exits

/-- The process taking the event. -/
def Ev.actor : Ev h → Proc h
  | .step p => p
  | .flush p => p

/-- The writes *performed* (made visible in memory) by an event, in order. -/
def Cfg.perf (s : Cfg h) : Ev h → List (W h)
  | .flush p => (s.buf p).take 1
  | .step p =>
    match s.pc p with
    | .e22 | .x50 _ => (s.buf p).take 1
    | .e23 | .e26 => s.buf p ++ (if (s.view p).lock = none then [.lock (some p)] else [])
    | _ => []

/-- The shared variable read by the next step of `p`, if any. -/
def Cfg.rdVar (s : Cfg h) (p : Proc h) : Option (Var h) :=
  match s.pc p with
  | .e24 | .e25a _ | .x32 => some .exits
  | .e25b _ => some .lock
  | .e27 => some (.signal p)
  | .x34 l j _ => some (.node (target (anc p l) j))
  | .x35 _ (q :: _) => some (.apply q)
  | .x36 _ q _ => some (.inPromQ q)
  | .x37 _ _ _ | .x42 | .x45 => some .promQ
  | _ => none

/-- The number of writes issued or CAS operations performed by the next step of `p` (`0` or
`1`). -/
def Cfg.wcost (s : Cfg h) (p : Proc h) : ℕ :=
  match s.pc p with
  | .rem | .e18 | .e19 _ | .e23 | .e26 | .x31 | .x32 | .x37 _ _ _ | .x38 _ _ _ | .x43
  | .x46 _ | .x47 _ | .x48 _ => 1
  | .x45 => if (s.view p).promQ = [] then 0 else 1
  | _ => 0

/-- A read of `v` by `p` is served from `p`'s own store buffer. -/
def Cfg.fromBuf (s : Cfg h) (p : Proc h) (v : Var h) : Prop := ∃ w ∈ s.buf p, w.var = v

instance (s : Cfg h) (p : Proc h) (v : Var h) : Decidable (s.fromBuf p v) := by
  unfold Cfg.fromBuf; infer_instance

/-- Cache states: `c p v = true` iff `p` holds a valid copy of `v`. -/
abbrev Cache (h : ℕ) := Proc h → Var h → Bool

/-- The cache after the event `e` in configuration `s`: a read from memory validates the reader's
copy; a write performed by `q` invalidates the copies of all processes other than `q`. -/
def Cache.upd (c : Cache h) (s : Cfg h) (e : Ev h) : Cache h := fun q v =>
  if e = .step q ∧ s.rdVar q = some v ∧ ¬ s.fromBuf q v then true
  else if e.actor ≠ q ∧ ∃ w ∈ s.perf e, w.var = v then false
  else c q v

/-- The RMR cost of the read of the next step of `p`: one iff it is served from memory and `p`
has no valid copy. -/
def Cfg.rcost (s : Cfg h) (c : Cache h) (p : Proc h) : ℕ :=
  match s.rdVar p with
  | some v => if ¬ s.fromBuf p v ∧ c p v = false then 1 else 0
  | none => 0

/-- The number of RMRs incurred by `p` in the event `e` (from configuration `s`, cache `c`). -/
def evCost (c : Cache h) (s : Cfg h) (e : Ev h) (p : Proc h) : ℕ :=
  if e = .step p then s.wcost p + s.rcost c p else 0

/-- The cache state along a run (initially empty). -/
def Run.cache (r : Run h) : ℕ → Cache h
  | 0 => fun _ _ => false
  | t + 1 => (r.cache t).upd (r.s t) (r.ev t)

/-- The RMRs incurred by `p` in the event at time `t`. -/
def Run.cost (r : Run h) (p : Proc h) (t : ℕ) : ℕ := evCost (r.cache t) (r.s t) (r.ev t) p

/-- The number of RMRs incurred by `p` in the events at times `t₁, …, t₂ − 1`. -/
def Run.rmr (r : Run h) (p : Proc h) (t₁ t₂ : ℕ) : ℕ := ∑ t ∈ Ico t₁ t₂, r.cost p t

/-- The next step of `p` completes a barrier (statement 22 or 50): its store buffer is empty. -/
def Cfg.BarrierDone (s : Cfg h) (p : Proc h) : Prop :=
  (s.pc p = .e22 ∨ ∃ o, s.pc p = .x50 o) ∧ s.buf p = []

instance (s : Cfg h) (p : Proc h) : Decidable (s.BarrierDone p) := by
  unfold Cfg.BarrierDone; infer_instance

/-- The number of barriers completed by `p` in the events at times `t₁, …, t₂ − 1`. -/
def Run.barriers (r : Run h) (p : Proc h) (t₁ t₂ : ℕ) : ℕ :=
  ((Ico t₁ t₂).filter (fun t => r.ev t = .step p ∧ (r.s t).BarrierDone p)).card

/-- `p` is not in the remainder section at any time strictly between `t₁` and `t₂`: the events
at times `t₁, …, t₂ − 1` belong to (a part of) a single passage of `p` (at most the event at time
`t₁` is a step of `p` in the remainder section, i.e. the start of the passage). -/
def Run.WithinPassage (r : Run h) (p : Proc h) (t₁ t₂ : ℕ) : Prop :=
  ∀ t, t₁ < t → t < t₂ → (r.s t).pc p ≠ .rem

/-! ### Semantics of events -/

lemma Cfg.mem_next_perf (s : Cfg h) (e : Ev h) : (s.next e).mem = s.mem.view (s.perf e) := by
  cases e with
  | flush p =>
    simp only [Cfg.next, Cfg.perf, Cfg.flush]
    split <;> rename_i hb <;> simp [hb]
  | step p =>
    simp only [Cfg.next, Cfg.perf, Cfg.stepProc]
    split <;> rename_i hpc <;> simp only [hpc]
    all_goals first
      | rfl
      | (simp only [Cfg.barrier]; split <;> rename_i hb
         · simp [hb]
         · simp only [Cfg.flush]; split <;> rename_i hb' <;> simp_all)
      | (simp only [Cfg.cas, Cfg.view]; split <;> rename_i hl <;> simp [hl, Mem.write])
      | (split <;> rfl)

lemma Cfg.pc_next_of_ne_actor (s : Cfg h) (e : Ev h) {q : Proc h} (hq : e.actor ≠ q) :
    (s.next e).pc q = s.pc q := by
  have hq' : q ≠ e.actor := Ne.symm hq
  cases e with
  | flush p => simp [Cfg.next]
  | step p =>
    simp only [Ev.actor] at hq'
    simp only [Cfg.next, Cfg.stepProc]
    split <;> (try simp [Cfg.barrier, Cfg.cas, Function.update_of_ne hq']) <;> (try split) <;>
      (try split) <;> (try simp [Function.update_of_ne hq'])

lemma Cfg.buf_next_of_ne_actor (s : Cfg h) (e : Ev h) {q : Proc h} (hq : e.actor ≠ q) :
    (s.next e).buf q = s.buf q := by
  have hq' : q ≠ e.actor := Ne.symm hq
  cases e with
  | flush p =>
    simp only [Ev.actor] at hq'
    simp only [Cfg.next, Cfg.flush]; split <;> simp [Function.update_of_ne hq']
  | step p =>
    simp only [Ev.actor] at hq'
    simp only [Cfg.next, Cfg.stepProc]
    split <;> (try simp [Cfg.barrier, Cfg.cas, Cfg.flush, Function.update_of_ne hq']) <;> (try split) <;>
      (try split) <;> (try split) <;> (try simp [Function.update_of_ne hq'])

/-- An event changes `ent` only when its actor enters the critical section from the entry
section. -/
lemma Cfg.ent_next_cases (s : Cfg h) (e : Ev h) :
    (s.next e).ent = s.ent ∨ ((s.next e).ent = s.ent + 1 ∧ (s.pc e.actor).Entry ∧
      (s.next e).pc e.actor = .cs) := by
  cases e with
  | flush p => simp [Cfg.next]
  | step p =>
    simp only [Cfg.next, Ev.actor]
    rcases hpc : s.pc p <;> simp [Cfg.stepProc, hpc, Cfg.barrier, PC.Entry] <;>
      (try split) <;> (try split) <;> simp_all [Cfg.cas]
    all_goals (split <;> simp)

/-- A process leaves the entry section only by entering the critical section. -/
lemma Cfg.entry_next_cases (s : Cfg h) (e : Ev h) (he : (s.pc e.actor).Entry) :
    ((s.next e).pc e.actor).Entry ∨ (s.next e).ent = s.ent + 1 := by
  cases e with
  | flush p => simp_all [Cfg.next, Ev.actor]
  | step p =>
    simp only [Cfg.next, Ev.actor] at he ⊢
    rcases hpc : s.pc p <;> simp [hpc, PC.Entry] at he <;>
      simp only [Cfg.stepProc, hpc, Cfg.barrier, Cfg.cas] <;> (try split_ifs) <;> simp [PC.Entry, hpc]

end Podc.ConstantBarriersMutex
