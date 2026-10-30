import Papers.PODC2023.MBroadcast.FromRegistersTrace

/-!
# Algorithm 2: MBroadcast on top of atomic SWMR registers (full version, Section 5.1)

The brief announcement states (end of Section 5) that MBroadcast can be implemented on top of
atomic read/write registers, for any number of crashes. The algorithm is given in the full
version (DISC 2023, Algorithm 2, proof in Appendix A.1):

```
shared: SENT[1..n], SWMR registers, SENT[i] = list of messages mbroadcast by pᵢ (initially empty)
local: deliveredᵢ[1..n] (counters, initially 0)
operation mbroadcast(m):  (1) SENT[i] ← SENT[i] ⊕ m; (2) catch_up(); (3) mdelivery of m from pᵢ
periodically do catch_up().
internal uninterruptible routine catch_up():
 (4) for j from 1 to i − 1 and then from i + 1 to n do
 (5)   msg_j ← SENT[j];
 (6)   for k from deliveredᵢ[j] to |msg_j| − 1 do mdelivery of msg_j[k + 1] from p_j end for;
 (7)   deliveredᵢ[j] ← |msg_j|
```

## Model

* `n` asynchronous processes `Fin n` (the loop order "1..i−1, then i+1..n" is the increasing
  order skipping `i`); messages of any type `M` with decidable equality.
* `n` **atomic** SWMR registers `sent : Fin n → List M`; one register access is one atomic step.
  Any number of processes may crash (`Act.crash`, at any time; a crashed process takes no
  further step).
* A configuration also holds the local counters `delivered`, the control position of each process
  (`Phase.idle`, or `Phase.catchUp own j`: inside `catch_up`, the next register to read is `j`,
  and `own = some m` iff this `catch_up` is the one of line 2 of `mbroadcast(m)`), and the
  **MBroadcast trace** `log` of the `bc`/`dl` events, in real-time order. The safety theorems are
  stated on `log` with the definitions of `Spec.lean`.
* Atomic steps (`step`):
  - `invoke p m`: invocation of `mbroadcast(m)` together with line 1 (one atomic write of
    `SENT[p]`, which `p` knows locally since it is its only writer); appends `bc p m`. It is
    enabled only when `p` is idle (no `catch_up` runs: the routine is uninterruptible, and an
    invocation has no effect before line 1, so this loses no behaviour), and only if `p` has not
    already mbroadcast `m` (the paper's assumption that all messages are different, per sender).
  - `tick p`: the next local step of `p`. When idle: start a periodic `catch_up`. In
    `catchUp own j` with `j < n`: if `j = p`, skip it; otherwise one atomic read of `SENT[j]`
    (line 5) together with the local lines 6–7, which append the `dl p j _` events of the messages
    not yet mdelivered, in order. In `catchUp own n`: the loop is over; if `own = some m`, line 3
    (`dl p p m`, i.e. `mbroadcast(m)` returns). Executing the local lines 6–7 in the same atomic
    step as the read only fixes how the local steps of `p` interleave with steps of other processes,
    which is irrelevant for the abstraction (they touch only the local state of `p`).
  - `crash p`.
* The register accesses themselves are not logged: the theorems only need the MBroadcast events
  (the write of line 1 coincides with the `bc` event).
* The full version assumes only *regular* registers; we model atomic ones (as in the brief
  announcement's claim).

## Results

* `safe`, `fifoOrdering` (this file): every reachable configuration (any number of crashes)
  satisfies unique broadcasts, Validity, No-duplication, Mutual ordering and FIFO ordering.
  Mutual ordering follows the proof of Appendix A.1, via the trace invariant `MOInv`
  (`FromRegistersTrace.lean`) and the invariant `Inv.cu`.
* `localTermination`, `globalCFTermination`, `globalCSTermination`
  (`FromRegistersLiveness.lean`): under weak fairness, for correct processes.
* `not_causalOrdering` (`FromRegistersCausal.lean`): Algorithm 2 is not causal.
* `Causal.safe`, `Causal.causalOrdering`, `Causal.fifoOrdering`, `Causal.globalCFTermination`, …
  (`FromRegistersCausalVariant*.lean`): a variant (ours) implementing causal-MBroadcast.
-/

namespace Podc.MBroadcast.FromRegisters

/-- Control position of a process. -/
inductive Phase (M : Type) where
  /-- Not inside `catch_up` (and not inside `mbroadcast`). -/
  | idle
  /-- Inside `catch_up`, the next register to read is `SENT[j]`; `own = some m` iff this is the
  `catch_up` of line 2 of `mbroadcast(m)`. -/
  | catchUp (own : Option M) (j : ℕ)
  deriving DecidableEq

/-- The own message of the current `mbroadcast` (not yet mdelivered by its sender). -/
def Phase.pending {M : Type} : Phase M → List M
  | .catchUp (some m) _ => [m]
  | _ => []

@[simp] lemma Phase.pending_idle {M : Type} : (Phase.idle : Phase M).pending = [] := rfl

@[simp] lemma Phase.pending_catchUp {M : Type} (o : Option M) (j : ℕ) :
    (Phase.catchUp o j).pending = o.toList := by
  cases o <;> rfl

/-- Configurations of Algorithm 2. -/
structure Cfg (n : ℕ) (M : Type) where
  /-- The shared registers `SENT[1..n]`. -/
  sent : Fin n → List M
  /-- The local counters: `delivered p q` is `delivered_p[q]`. -/
  delivered : Fin n → Fin n → ℕ
  /-- The control position of each process. -/
  phase : Fin n → Phase M
  /-- The crashed processes. -/
  crashed : Fin n → Bool
  /-- The MBroadcast trace. -/
  log : List (Ev (Fin n) M)

/-- Atomic steps. -/
inductive Act (n : ℕ) (M : Type) where
  /-- `p` invokes `mbroadcast(m)` and executes line 1. -/
  | invoke (p : Fin n) (m : M)
  /-- The next local step of `p` (start of a periodic `catch_up`, one iteration of the loop of
  `catch_up`, or the end of `catch_up`). -/
  | tick (p : Fin n)
  /-- `p` crashes. -/
  | crash (p : Fin n)

variable {n : ℕ} {M : Type} [DecidableEq M]

set_option linter.unusedSectionVars false

open Function

/-- The initial configuration. -/
def init : Cfg n M := ⟨fun _ => [], fun _ _ => 0, fun _ => .idle, fun _ => false, []⟩

/-- `p` starts a periodic `catch_up`. -/
def startCU (c : Cfg n M) (p : Fin n) : Cfg n M :=
  { c with phase := update c.phase p (.catchUp none 0) }

/-- `p` skips its own register in the loop of line 4. -/
def skipSelf (c : Cfg n M) (p : Fin n) (own : Option M) (j : ℕ) : Cfg n M :=
  { c with phase := update c.phase p (.catchUp own (j + 1)) }

/-- Lines 5–7 for `SENT[q]` (`q = j`): one atomic read, the mdeliveries of the new messages, and
the update of the counter. -/
def readReg (c : Cfg n M) (p q : Fin n) (own : Option M) (j : ℕ) : Cfg n M :=
  { c with
    phase := update c.phase p (.catchUp own (j + 1))
    delivered := update c.delivered p (update (c.delivered p) q (c.sent q).length)
    log := c.log ++ ((c.sent q).drop (c.delivered p q)).map (Ev.dl p q) }

/-- End of `catch_up`; line 3 if this is the `catch_up` of `mbroadcast(m)`. -/
def finish (c : Cfg n M) (p : Fin n) (own : Option M) : Cfg n M :=
  { c with
    phase := update c.phase p .idle
    log := c.log ++ own.toList.map (Ev.dl p p) }

/-- The next local step of `p`. -/
def tick (c : Cfg n M) (p : Fin n) : Cfg n M :=
  match c.phase p with
  | .idle => startCU c p
  | .catchUp own j =>
    if hj : j < n then
      if (⟨j, hj⟩ : Fin n) = p then skipSelf c p own j else readReg c p ⟨j, hj⟩ own j
    else finish c p own

/-- One atomic step (`none`: the action is not enabled). -/
def step (c : Cfg n M) : Act n M → Option (Cfg n M)
  | .invoke p m =>
    if c.crashed p = false ∧ c.phase p = .idle ∧ Ev.bc p m ∉ c.log then
      some { c with
        sent := update c.sent p (c.sent p ++ [m])
        phase := update c.phase p (.catchUp (some m) 0)
        log := c.log ++ [.bc p m] }
    else none
  | .tick p => if c.crashed p = false then some (tick c p) else none
  | .crash p => some { c with crashed := update c.crashed p true }

/-- Reachable configurations. -/
inductive Reachable : Cfg n M → Prop
  | init : Reachable init
  | step {c c' : Cfg n M} {a : Act n M} : Reachable c → step c a = some c' → Reachable c'

/-! ## The invariant -/

/-- The inductive invariant of Algorithm 2. -/
structure Inv (c : Cfg n M) : Prop where
  /-- Trace invariant: mdeliveries from `p` follow the mbroadcasts of `p` (all prefixes). -/
  pre : PrefixInv c.log
  /-- All mbroadcast messages are different (per sender). -/
  uniq : UniqueBc c.log
  /-- Trace invariant for mutual ordering. -/
  mo : MOInv c.log
  /-- `SENT[p]` is the list of the messages mbroadcast by `p`. -/
  sent : ∀ p, c.sent p = bcs c.log p
  /-- The counters are bounded by the length of the registers. -/
  dle : ∀ q p, c.delivered q p ≤ (c.sent p).length
  /-- `q` has mdelivered from `p ≠ q` exactly the first `delivered_q[p]` messages of `SENT[p]`. -/
  deliv : ∀ q p, q ≠ p → dls c.log q p = (c.sent p).take (c.delivered q p)
  /-- `p` has mdelivered all its own messages, except the one of its current `mbroadcast`. -/
  own : ∀ p, dls c.log p p ++ (c.phase p).pending = c.sent p
  /-- The loop index is at most `n`. -/
  jle : ∀ p o j, c.phase p = .catchUp o j → j ≤ n
  /-- During the `catch_up` of `mbroadcast(m)`, `p` has mdelivered from every process already
  read every message mbroadcast before `m`. -/
  cu : ∀ p m j, c.phase p = .catchUp (some m) j → ∃ b, c.log[b]? = some (.bc p m) ∧
    ∀ q : Fin n, q.val < j → q ≠ p → ∀ m', .bc q m' ∈ c.log.take b → .dl p q m' ∈ c.log

lemma inv_init : Inv (init : Cfg n M) where
  pre := PrefixInv.nil
  uniq := by intro p m; simp [init]
  mo := MOInv.nil
  sent := by intro p; simp [init]
  dle := by intro q p; simp [init]
  deliv := by intro q p _; simp [init]
  own := by intro p; simp [init]
  jle := by intro p o j h; simp [init] at h
  cu := by intro p m j h; simp [init] at h

/-! ## Preservation of the invariant -/

section Preservation

variable {c : Cfg n M}

lemma cu_append {tr : List (Ev (Fin n) M)} (L : List (Ev (Fin n) M)) {p : Fin n} {m : M} {j : ℕ}
    (h : ∃ b, tr[b]? = some (.bc p m) ∧ ∀ q : Fin n, q.val < j → q ≠ p → ∀ m',
      .bc q m' ∈ tr.take b → .dl p q m' ∈ tr) :
    ∃ b, (tr ++ L)[b]? = some (.bc p m) ∧ ∀ q : Fin n, q.val < j → q ≠ p → ∀ m',
      .bc q m' ∈ (tr ++ L).take b → .dl p q m' ∈ tr ++ L := by
  obtain ⟨b, hb, hb'⟩ := h
  have hbl : b < tr.length := by
    by_contra hc; rw [List.getElem?_eq_none (by omega)] at hb; cases hb
  refine ⟨b, by rw [List.getElem?_append_left hbl]; exact hb, ?_⟩
  intro q hq hqp m' hm'
  rw [List.take_append_of_le_length hbl.le] at hm'
  exact List.mem_append_left _ (hb' q hq hqp m' hm')

lemma uniqueBc_append_map_dl {tr : List (Ev (Fin n) M)} (h : UniqueBc tr) (q p : Fin n)
    (L : List M) : UniqueBc (tr ++ L.map (Ev.dl q p)) := by
  intro p' m'
  have h0 : (L.map (Ev.dl q p)).count (Ev.bc p' m') = 0 := List.count_eq_zero.2 (by simp)
  rw [List.count_append, h0]
  exact h p' m'

lemma Inv.after_invoke (h : Inv c) {p : Fin n} {m : M} (hidle : c.phase p = .idle)
    (hnot : Ev.bc p m ∉ c.log) :
    Inv { c with
        sent := update c.sent p (c.sent p ++ [m])
        phase := update c.phase p (.catchUp (some m) 0)
        log := c.log ++ [.bc p m] } where
  pre := h.pre.snoc (by intro q p x he; cases he)
  uniq := by
    intro p' m'
    rw [List.count_append]
    by_cases hh : Ev.bc p' m' = Ev.bc p m
    · rw [hh, List.count_eq_zero.2 hnot]; simp
    · have hh' : ¬ (p = p' ∧ m = m') := fun ⟨h1, h2⟩ => hh (by rw [h1, h2])
      rw [List.count_singleton]; simpa [hh'] using h.uniq p' m'
  mo := h.mo.append (by intro p m hm; simp at hm)
  sent := by
    intro p'
    by_cases hp : p' = p
    · subst hp; simp [h.sent]
    · simp [update_of_ne hp, h.sent, Ne.symm hp]
  dle := by
    intro q p'
    by_cases hp : p' = p
    · subst hp; simp only [update_self, List.length_append]; have := h.dle q p'; omega
    · simp only [update_of_ne hp]; exact h.dle q p'
  deliv := by
    intro q p' hq
    simp only [dls_append, dls_cons_bc, dls_nil, List.append_nil]
    by_cases hp : p' = p
    · subst hp; simp only [update_self]
      rw [List.take_append_of_le_length (h.dle q p')]; exact h.deliv q p' hq
    · simp only [update_of_ne hp]; exact h.deliv q p' hq
  own := by
    intro p'
    simp only [dls_append, dls_cons_bc, dls_nil, List.append_nil]
    by_cases hp : p' = p
    · subst hp; have := h.own p'; simp only [hidle, Phase.pending_idle, List.append_nil] at this
      simp [this]
    · simp only [update_of_ne hp]; exact h.own p'
  jle := by
    intro p' o j hph
    by_cases hp : p' = p
    · subst hp; simp only [update_self, Phase.catchUp.injEq] at hph; omega
    · simp only [update_of_ne hp] at hph; exact h.jle p' o j hph
  cu := by
    intro p' m' j hph
    by_cases hp : p' = p
    · subst hp; simp only [update_self, Phase.catchUp.injEq, Option.some.injEq] at hph
      obtain ⟨rfl, rfl⟩ := hph
      exact ⟨c.log.length, by simp, fun q hq => absurd hq (by omega)⟩
    · simp only [update_of_ne hp] at hph; exact cu_append _ (h.cu p' m' j hph)

lemma Inv.after_startCU (h : Inv c) {p : Fin n} (hidle : c.phase p = .idle) :
    Inv (startCU c p) where
  pre := h.pre
  uniq := h.uniq
  mo := h.mo
  sent := h.sent
  dle := h.dle
  deliv := h.deliv
  own := by
    intro p'
    by_cases hp : p' = p
    · subst hp; have := h.own p'; simp only [hidle, Phase.pending_idle] at this
      simpa [startCU] using this
    · simp only [startCU, update_of_ne hp]; exact h.own p'
  jle := by
    intro p' o j hph
    by_cases hp : p' = p
    · subst hp; simp only [startCU, update_self, Phase.catchUp.injEq] at hph; omega
    · simp only [startCU, update_of_ne hp] at hph; exact h.jle p' o j hph
  cu := by
    intro p' m' j hph
    by_cases hp : p' = p
    · subst hp; simp [startCU] at hph
    · simp only [startCU, update_of_ne hp] at hph; exact h.cu p' m' j hph

lemma Inv.after_skipSelf (h : Inv c) {p : Fin n} {own : Option M} {j : ℕ}
    (hph : c.phase p = .catchUp own j) (hj : j < n) (hjp : (⟨j, hj⟩ : Fin n) = p) :
    Inv (skipSelf c p own j) where
  pre := h.pre
  uniq := h.uniq
  mo := h.mo
  sent := h.sent
  dle := h.dle
  deliv := h.deliv
  own := by
    intro p'
    by_cases hp : p' = p
    · subst hp; have := h.own p'; rw [hph] at this
      simpa [skipSelf] using this
    · simp only [skipSelf, update_of_ne hp]; exact h.own p'
  jle := by
    intro p' o j' hph'
    by_cases hp : p' = p
    · subst hp; simp only [skipSelf, update_self, Phase.catchUp.injEq] at hph'; omega
    · simp only [skipSelf, update_of_ne hp] at hph'; exact h.jle p' o j' hph'
  cu := by
    intro p' m' j' hph'
    by_cases hp : p' = p
    · subst hp
      simp only [skipSelf, update_self, Phase.catchUp.injEq] at hph'
      obtain ⟨rfl, rfl⟩ := hph'
      obtain ⟨b, hb, hb'⟩ := h.cu p' m' j hph
      refine ⟨b, hb, fun q hq hqp => hb' q ?_ hqp⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hq with hq | hq
      · exact hq
      · exact absurd (hjp ▸ Fin.ext hq) hqp
    · simp only [skipSelf, update_of_ne hp] at hph'; exact h.cu p' m' j' hph'

lemma Inv.after_readReg (h : Inv c) {p q : Fin n} {own : Option M} {j : ℕ}
    (hph : c.phase p = .catchUp own j) (hqj : q.val = j) (hqp : q ≠ p) :
    Inv (readReg c p q own j) where
  pre := by
    refine h.pre.append_map_dl ?_
    rw [h.deliv p q (Ne.symm hqp), List.take_append_drop, h.sent q]
  uniq := uniqueBc_append_map_dl h.uniq p q _
  mo := h.mo.append (by
    intro p' m hm
    simp only [List.mem_map, Ev.dl.injEq] at hm
    obtain ⟨_, _, rfl, rfl, _⟩ := hm
    exact absurd rfl hqp)
  sent := by
    intro p'; simp only [readReg, bcs_append, bcs_map_dl, List.append_nil]; exact h.sent p'
  dle := by
    intro q' p'
    simp only [readReg]
    by_cases h1 : q' = p
    · subst h1
      by_cases h2 : p' = q
      · subst h2; simp
      · simp only [update_self, update_of_ne h2]; exact h.dle _ _
    · simp only [update_of_ne h1]; exact h.dle _ _
  deliv := by
    intro q' p' hq'
    simp only [readReg, dls_append, dls_map_dl, update_apply]
    by_cases hh : p = q' ∧ q = p'
    · obtain ⟨rfl, rfl⟩ := hh
      simp only [and_self, ite_true]
      rw [h.deliv p q (Ne.symm hqp), List.take_append_drop]; simp
    · rw [ite_eq_right hh, List.append_nil, h.deliv q' p' hq']
      by_cases h1 : q' = p
      · subst h1
        have h2 : p' ≠ q := fun h2 => hh ⟨rfl, h2.symm⟩
        simp [h2]
      · simp [h1]
  own := by
    intro p'
    simp only [readReg, dls_append, dls_map_dl]
    have hh : ¬ (p = p' ∧ q = p') := fun ⟨h1, h2⟩ => hqp (h2.trans h1.symm)
    rw [ite_eq_right hh, List.append_nil]
    by_cases hp : p' = p
    · subst hp; have := h.own p'; rw [hph] at this
      simpa using this
    · simp only [update_of_ne hp]; exact h.own p'
  jle := by
    intro p' o j' hph'
    by_cases hp : p' = p
    · subst hp; simp only [readReg, update_self, Phase.catchUp.injEq] at hph'
      have := q.isLt; omega
    · simp only [readReg, update_of_ne hp] at hph'; exact h.jle p' o j' hph'
  cu := by
    intro p' m' j' hph'
    by_cases hp : p' = p
    · subst hp
      simp only [readReg, update_self, Phase.catchUp.injEq] at hph'
      obtain ⟨rfl, rfl⟩ := hph'
      obtain ⟨b, hb, hb'⟩ := cu_append (((c.sent q).drop (c.delivered p' q)).map (Ev.dl p' q))
        (h.cu p' m' j hph)
      refine ⟨b, hb, fun q' hq hq'p m'' hm => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hq with hq | hq
      · exact hb' q' hq hq'p m'' hm
      · have hq'q : q' = q := Fin.ext (hq.trans hqj.symm)
        subst hq'q
        simp only [readReg] at hm ⊢
        rw [← mem_dls]
        simp only [dls_append, dls_map_dl, and_self, ite_true]
        rw [h.deliv p' q' hq'p.symm, List.take_append_drop, h.sent q', mem_bcs]
        have hbl : b < c.log.length := by
          by_contra hc
          rw [List.getElem?_append_right (by omega)] at hb
          have := List.mem_of_getElem? hb
          simp only [List.mem_map] at this
          obtain ⟨_, _, h⟩ := this; cases h
        rw [List.take_append_of_le_length hbl.le] at hm
        exact List.mem_of_mem_take hm
    · simp only [readReg, update_of_ne hp] at hph'
      exact cu_append _ (h.cu p' m' j' hph')

lemma Inv.after_finish (h : Inv c) {p : Fin n} {own : Option M} {j : ℕ}
    (hph : c.phase p = .catchUp own j) (hj : n ≤ j) :
    Inv (finish c p own) where
  pre := by
    refine h.pre.append_map_dl ?_
    have := h.own p; rw [hph] at this
    rw [h.sent p] at this
    cases own <;> simp_all
  uniq := uniqueBc_append_map_dl h.uniq p p _
  mo := h.mo.append (by
    intro p' m hm
    simp only [List.mem_map, Option.mem_toList, Ev.dl.injEq] at hm
    obtain ⟨m0, hm0, rfl, -, rfl⟩ := hm
    subst hm0
    obtain ⟨b, hb, hb'⟩ := h.cu p m0 j hph
    exact ⟨b, hb, fun q hq => hb' q (by have := q.isLt; omega) hq⟩)
  sent := by intro p'; simp [finish, h.sent]
  dle := h.dle
  deliv := by
    intro q' p' hq'
    simp only [finish, dls_append, dls_map_dl]
    have hh : ¬ (p = q' ∧ p = p') := fun ⟨h1, h2⟩ => hq' (h1.symm.trans h2)
    rw [ite_eq_right hh, List.append_nil]; exact h.deliv q' p' hq'
  own := by
    intro p'
    simp only [finish, dls_append, dls_map_dl]
    by_cases hp : p' = p
    · subst hp; have := h.own p'; rw [hph] at this
      cases own <;> simpa using this
    · have hh : ¬ (p = p' ∧ p = p') := fun ⟨h1, _⟩ => hp h1.symm
      rw [ite_eq_right hh, List.append_nil, update_of_ne hp]; exact h.own p'
  jle := by
    intro p' o j' hph'
    by_cases hp : p' = p
    · subst hp; simp [finish] at hph'
    · simp only [finish, update_of_ne hp] at hph'; exact h.jle p' o j' hph'
  cu := by
    intro p' m' j' hph'
    by_cases hp : p' = p
    · subst hp; simp [finish] at hph'
    · simp only [finish, update_of_ne hp] at hph'; exact cu_append _ (h.cu p' m' j' hph')

lemma Inv.after_tick (h : Inv c) (p : Fin n) : Inv (tick c p) := by
  unfold FromRegisters.tick
  split
  · next hidle => exact h.after_startCU hidle
  · next own j hph =>
    split
    · next hj =>
      split
      · next hjp => exact h.after_skipSelf hph hj hjp
      · next hjp => exact h.after_readReg hph rfl hjp
    · next hj => exact h.after_finish hph (by omega)

lemma Inv.after_step (h : Inv c) {a : Act n M} {c' : Cfg n M} (hs : step c a = some c') : Inv c' := by
  cases a with
  | invoke p m =>
    simp only [FromRegisters.step] at hs
    split_ifs at hs with hc
    cases hs; exact h.after_invoke hc.2.1 hc.2.2
  | tick p =>
    simp only [FromRegisters.step] at hs
    split_ifs at hs; cases hs; exact h.after_tick p
  | crash p =>
    simp only [FromRegisters.step, Option.some.injEq] at hs; subst hs
    exact ⟨h.pre, h.uniq, h.mo, h.sent, h.dle, h.deliv, h.own, h.jle, h.cu⟩

lemma Reachable.inv {c : Cfg n M} (h : Reachable c) : Inv c := by
  induction h with
  | init => exact inv_init
  | step _ hs ih => exact ih.after_step hs

end Preservation

/-! ## Safety -/

/-- **Safety of Algorithm 2** (full version, Theorem 2 / Appendix A.1, safety part; with atomic
registers and any number of crashes): in every reachable configuration, the MBroadcast trace
satisfies unique broadcasts, Validity, No-duplication and Mutual ordering, i.e. the algorithm
implements MBroadcast. -/
theorem safe {c : Cfg n M} (h : Reachable c) : UniqueBc c.log ∧ Safe c.log := by
  have hi := h.inv
  exact ⟨hi.uniq, hi.pre.validity, hi.pre.noDup hi.uniq, hi.mo.mutualOrdering⟩

/-- **FIFO ordering** of Algorithm 2: the algorithm implements fifo-MBroadcast. -/
theorem fifoOrdering {c : Cfg n M} (h : Reachable c) : FifoOrdering c.log :=
  h.inv.pre.fifo h.inv.uniq

end Podc.MBroadcast.FromRegisters
