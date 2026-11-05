import Mathlib

/-!
# The Signal object of [JJJ19], Section 2 (Theorem 1)

P. Jayanti, S. Jayanti, A. Joshi, *A Recoverable Mutex Algorithm with Sub-logarithmic RMR on Both CC
and DSM*, PODC 2019 (arXiv 1904.02124v2), Section 2.1, Figure 2, Theorem 1, proof in Appendix D.

## Model

Asynchronous shared memory, processes of an arbitrary type `P` (with decidable equality), one shared
access per step, no crashes (Section 2 of the paper does not mention crashes). An execution is
determined by an arbitrary *schedule* `σ : ℕ → Action P`: at each time the environment either lets an
idle process invoke `set()` or `wait()`, or lets some process execute the next line of its current
operation (`Action.step`). There are no fairness assumptions.

Shared memory: `Bit`, `GoAddr`, and the boolean cells created by `new Boolean` (line 5). A cell is a
pair `(q, k)`: the `k`-th cell allocated by process `q`; it lives in `q`'s memory partition (DSM).

Line 3 is a local test and is merged with line 2; line 5 (`new Boolean`) is a local step.

The abstract `State` of the Signal object (Figure 1) is a ghost field `Config.state`; it is set to `1`
(`true`) exactly at the linearization point of the first effective `set()`, which is the first event
that is either the completion of some `set()` or a `wait()` reading `Bit = 1` at line 8 (this is the
linearization of Appendix D). Theorem 1 (i) shows that this point always lies inside a pending
`set()` execution that has already performed line 1, so it is a legitimate linearization point.

A second ghost field `Config.cache` records which processes hold a valid cached copy of each boolean
cell; it is only used to count RMRs on a CC machine.
-/

namespace Podc.RMESubLogBoth.Signal

variable {P : Type} [DecidableEq P]

/-- A boolean cell created by `new Boolean`: `(q, k)` is the `k`-th cell allocated by `q`, residing
in `q`'s memory partition. -/
abbrev Cell (P : Type) := P × ℕ

/-- Program counter: the next line to execute. -/
inductive PC (P : Type) where
  /-- Not executing any operation. -/
  | idle
  /-- In `set()`, about to execute line 1 (`Bit ← 1`). -/
  | s1
  /-- In `set()`, about to execute lines 2–3 (`addr ← GoAddr; if addr ≠ NIL`). -/
  | s2
  /-- In `set()`, about to execute line 4 (`*addr ← true`) with `addr = a`. -/
  | s4 (a : Cell P)
  /-- In `wait()`, about to execute line 5 (`go ← new Boolean`). -/
  | w5
  /-- In `wait()`, about to execute line 6 (`*go ← false`). -/
  | w6 (g : Cell P)
  /-- In `wait()`, about to execute line 7 (`GoAddr ← go`). -/
  | w7 (g : Cell P)
  /-- In `wait()`, about to execute line 8 (`if Bit == 0`). -/
  | w8 (g : Cell P)
  /-- In `wait()`, spinning at line 9 (`wait till *go == true`). -/
  | w9 (g : Cell P)
  deriving DecidableEq

namespace PC

/-- The process is executing `set()`. -/
def InSet : PC P → Prop
  | s1 | s2 | s4 _ => True
  | _ => False

/-- The process is executing `set()` and has already performed line 1. -/
def PastLine1 : PC P → Prop
  | s2 | s4 _ => True
  | _ => False

/-- The process is executing `wait()`. -/
def InWait : PC P → Prop
  | w5 | w6 _ | w7 _ | w8 _ | w9 _ => True
  | _ => False

/-- The cell allocated by the current `wait()` (after line 5). -/
def cell : PC P → Option (Cell P)
  | w6 g | w7 g | w8 g | w9 g => some g
  | _ => none

instance : DecidablePred (InSet (P := P)) := fun x => by cases x <;> unfold InSet <;> infer_instance
instance : DecidablePred (InWait (P := P)) := fun x => by cases x <;> unfold InWait <;> infer_instance

end PC

/-- A configuration of the system. -/
structure Config (P : Type) where
  /-- Shared variable `Bit`. -/
  bit : Bool
  /-- Shared variable `GoAddr` (`none` = `NIL`). -/
  goAddr : Option (Cell P)
  /-- Contents of the boolean cells. -/
  go : Cell P → Bool
  /-- Program counters. -/
  pc : P → PC P
  /-- Number of cells allocated so far by each process. -/
  cnt : P → ℕ
  /-- Ghost: the abstract state `X.State` of the Signal object (Figure 1). -/
  state : Bool
  /-- Ghost (CC accounting): `cache q g` iff `q` holds a valid cached copy of cell `g`. -/
  cache : P → Cell P → Bool

/-- Initial configuration: `Bit = 0`, `GoAddr = NIL`, all processes idle, `State = 0`. -/
def init : Config P where
  bit := false
  goAddr := none
  go := fun _ => false
  pc := fun _ => .idle
  cnt := fun _ => 0
  state := false
  cache := fun _ _ => false

/-- Actions chosen by the environment (scheduler). -/
inductive Action (P : Type) where
  /-- Process `p` invokes `set()` (no effect unless `p` is idle). -/
  | invokeSet (p : P)
  /-- Process `p` invokes `wait()` (no effect unless `p` is idle). -/
  | invokeWait (p : P)
  /-- Process `p` executes one line of its current operation (no effect if `p` is idle). -/
  | step (p : P)
  deriving DecidableEq

namespace Config

/-- Update the program counter of `p`. -/
def setPc (c : Config P) (p : P) (x : PC P) : Config P := { c with pc := Function.update c.pc p x }

@[simp] theorem setPc_pc (c : Config P) (p : P) (x : PC P) :
    (c.setPc p x).pc = Function.update c.pc p x := rfl
@[simp] theorem setPc_bit (c : Config P) (p : P) (x : PC P) : (c.setPc p x).bit = c.bit := rfl
@[simp] theorem setPc_goAddr (c : Config P) (p : P) (x : PC P) :
    (c.setPc p x).goAddr = c.goAddr := rfl
@[simp] theorem setPc_go (c : Config P) (p : P) (x : PC P) : (c.setPc p x).go = c.go := rfl
@[simp] theorem setPc_cnt (c : Config P) (p : P) (x : PC P) : (c.setPc p x).cnt = c.cnt := rfl
@[simp] theorem setPc_state (c : Config P) (p : P) (x : PC P) :
    (c.setPc p x).state = c.state := rfl
@[simp] theorem setPc_cache (c : Config P) (p : P) (x : PC P) :
    (c.setPc p x).cache = c.cache := rfl

/-- Cache effect of a write of cell `g` by `p`: `p` holds the only valid copy. -/
def writeCache (c : Config P) (p : P) (g : Cell P) : P → Cell P → Bool :=
  fun q h => if h = g then decide (q = p) else c.cache q h

/-- Cache effect of a read of cell `g` by `p`. -/
def readCache (c : Config P) (p : P) (g : Cell P) : P → Cell P → Bool :=
  fun q h => if q = p ∧ h = g then true else c.cache q h

end Config

open Config

/-- One step of process `p` (Figure 2): execute the line its program counter points to. -/
def stepProc (c : Config P) (p : P) : Config P :=
  match c.pc p with
  | .idle => c
  -- line 1: Bit ← 1
  | .s1 => { c.setPc p .s2 with bit := true }
  -- lines 2–3: addr ← GoAddr; if addr ≠ NIL (otherwise `set()` returns: linearization point if
  -- `State` was still 0)
  | .s2 =>
    match c.goAddr with
    | none => { c.setPc p .idle with state := true }
    | some a => c.setPc p (.s4 a)
  -- line 4: *addr ← true; `set()` returns
  | .s4 a =>
    { c.setPc p .idle with
      go := Function.update c.go a true
      state := true
      cache := c.writeCache p a }
  -- line 5: go ← new Boolean (local allocation in p's partition)
  | .w5 => { c.setPc p (.w6 (p, c.cnt p)) with cnt := Function.update c.cnt p (c.cnt p + 1) }
  -- line 6: *go ← false
  | .w6 g =>
    { c.setPc p (.w7 g) with
      go := Function.update c.go g false
      cache := c.writeCache p g }
  -- line 7: GoAddr ← go
  | .w7 g => { c.setPc p (.w8 g) with goAddr := some g }
  -- line 8: if Bit == 0 then (go to line 9) else return
  | .w8 g => if c.bit then { c.setPc p .idle with state := true } else c.setPc p (.w9 g)
  -- line 9: one read of *go; return if it is true
  | .w9 g => if c.go g then { c.setPc p .idle with cache := c.readCache p g }
              else { c with cache := c.readCache p g }

/-- Effect of one action of the schedule. -/
def stepAct : Action P → Config P → Config P
  | .invokeSet p, c => if c.pc p = .idle then c.setPc p .s1 else c
  | .invokeWait p, c => if c.pc p = .idle then c.setPc p .w5 else c
  | .step p, c => stepProc c p

/-- The execution determined by the schedule `σ`: `exec σ t` is the configuration after `t` events. -/
def exec (σ : ℕ → Action P) : ℕ → Config P
  | 0 => init
  | t + 1 => stepAct (σ t) (exec σ t)

/-- At most one process is executing `wait()` (no two executions of `wait()` are concurrent). -/
def AtMostOneWaiter (c : Config P) : Prop :=
  ∀ p q, (c.pc p).InWait → (c.pc q).InWait → p = q

/-- The hypothesis of Theorem 1: in the execution of `σ`, no two executions of `wait()` overlap. -/
def NoConcurrentWaits (σ : ℕ → Action P) : Prop := ∀ t, AtMostOneWaiter (exec σ t)

/-! ## The invariant -/

/-- The part of the invariant about one process `q` whose program counter is `x`
(it only mentions the shared/ghost variables of `c`, not the program counters). -/
def LocalInv (c : Config P) (q : P) : PC P → Prop
  | .idle | .s1 | .w5 => True
  | .s2 => c.bit = true
  | .s4 a => c.bit = true ∧ a.2 < c.cnt a.1
  | .w6 g => g.1 = q ∧ g.2 < c.cnt q ∧ c.goAddr ≠ some g
  | .w7 g => g.1 = q ∧ g.2 < c.cnt q ∧ c.goAddr ≠ some g ∧ c.go g = false ∧ c.cache q g = true
  | .w8 g => g.1 = q ∧ g.2 < c.cnt q ∧ c.goAddr = some g ∧ (c.go g = true → c.bit = true) ∧
      (c.cache q g = false → c.go g = true)
  | .w9 g => g.1 = q ∧ g.2 < c.cnt q ∧ c.goAddr = some g ∧ c.go g = c.state ∧
      (c.cache q g = false → c.go g = true)

/-- The part of the invariant about two processes with program counters `x` and `y`. -/
def PairInv : PC P → PC P → Prop
  | .w6 g, .s4 a => a ≠ g
  | .w7 g, .s4 a => a ≠ g
  | .w9 g, .s4 a => a = g
  | _, _ => True

/-- Inductive invariant of the implementation (under the no-concurrent-waits hypothesis). -/
structure Inv (c : Config P) : Prop where
  state_bit : c.state = true → c.bit = true
  bit_past : c.bit = true → c.state = false → ∃ q, (c.pc q).PastLine1
  fresh_addr : ∀ r, c.goAddr = some r → r.2 < c.cnt r.1
  local_ : ∀ q, LocalInv c q (c.pc q)
  pair : ∀ q q', PairInv (c.pc q) (c.pc q')

omit [DecidableEq P] in
theorem inv_init : Inv (init : Config P) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp [init, LocalInv, PairInv]

omit [DecidableEq P] in
theorem pairInv_self (x : PC P) : PairInv x x := by
  cases x <;> simp [PairInv]

/-- Frame lemma: a step of `p` that changes `p`'s program counter to `x'`. -/
theorem Inv.of_update {c c' : Config P} {p : P} {x' : PC P} (hI : Inv c)
    (hpc : c'.pc = Function.update c.pc p x')
    (hsb : c'.state = true → c'.bit = true)
    (hbp : c'.bit = true → c'.state = false → ∃ q, (c'.pc q).PastLine1)
    (hfa : ∀ r, c'.goAddr = some r → r.2 < c'.cnt r.1)
    (hself : LocalInv c' p x')
    (hother : ∀ q, q ≠ p → LocalInv c' q (c.pc q))
    (hp1 : ∀ q, q ≠ p → PairInv x' (c.pc q)) (hp2 : ∀ q, q ≠ p → PairInv (c.pc q) x') :
    Inv c' := by
  refine ⟨hsb, hbp, hfa, fun q => ?_, fun q q' => ?_⟩
  · rw [hpc]
    by_cases hq : q = p
    · subst hq; simpa using hself
    · simpa [Function.update_of_ne hq] using hother q hq
  · rw [hpc]
    by_cases hq : q = p <;> by_cases hq' : q' = p
    · subst hq hq'; simpa using pairInv_self x'
    · subst hq; simpa [Function.update_of_ne hq'] using hp1 q' hq'
    · subst hq'; simpa [Function.update_of_ne hq] using hp2 q hq
    · simpa [Function.update_of_ne hq, Function.update_of_ne hq'] using hI.pair q q'

omit [DecidableEq P] in
/-- In a configuration where `p` is waiting and there are no concurrent waits, no other process is
waiting. -/
theorem not_inWait_of_ne {c : Config P} (h1 : AtMostOneWaiter c) {p q : P} (hp : (c.pc p).InWait)
    (hq : q ≠ p) : ¬ (c.pc q).InWait := fun h => hq (h1 q p h hp)

omit [DecidableEq P] in
theorem pairInv_left_true {x y : PC P} (hx : x = .idle ∨ x = .s1 ∨ x = .s2 ∨ x = .w5 ∨
    (∃ g, x = .w8 g) ∨ (∃ a, x = .s4 a)) : PairInv x y := by
  rcases hx with rfl | rfl | rfl | rfl | ⟨g, rfl⟩ | ⟨a, rfl⟩ <;> cases y <;> simp [PairInv]

omit [DecidableEq P] in
theorem pairInv_right_true {x y : PC P} (hy : ¬ ∃ a, y = .s4 a) : PairInv x y := by
  cases x <;> cases y <;> simp_all [PairInv]

/-- The witness for `bit_past` is unaffected by a step of a process `p` that was not past line 1. -/
theorem bitPast_of_update {c : Config P} {p : P} {x' : PC P} (hp : ¬ (c.pc p).PastLine1)
    {q : P} (hq : (c.pc q).PastLine1) : (Function.update c.pc p x' q).PastLine1 := by
  have : q ≠ p := by rintro rfl; exact hp hq
  simpa [Function.update_of_ne this] using hq

theorem inv_invoke {c : Config P} (hI : Inv c) {p : P} (hp : c.pc p = .idle) {x : PC P}
    (hx : x = .s1 ∨ x = .w5) : Inv (c.setPc p x) := by
  apply hI.of_update (p := p) (x' := x) rfl
  · exact hI.state_bit
  · intro hb hs
    obtain ⟨q, hq⟩ := hI.bit_past hb hs
    exact ⟨q, bitPast_of_update (by simp [hp, PC.PastLine1]) hq⟩
  · exact hI.fresh_addr
  · rcases hx with rfl | rfl <;> trivial
  · exact fun q _ => hI.local_ q
  · intro q _; exact pairInv_left_true (by rcases hx with rfl | rfl <;> simp)
  · intro q _; exact pairInv_right_true (by rcases hx with rfl | rfl <;> simp)

theorem inv_s1 {c : Config P} (hI : Inv c) {p : P} (_hp : c.pc p = .s1) :
    Inv { c.setPc p .s2 with bit := true } := by
  apply hI.of_update (p := p) (x' := .s2) rfl
  · simp
  · intro _ _; exact ⟨p, by simp [setPc, PC.PastLine1]⟩
  · exact hI.fresh_addr
  · simp [LocalInv]
  · intro q _
    have h := hI.local_ q
    cases hc : c.pc q <;> simp only [hc, LocalInv, setPc_cnt, setPc_goAddr, setPc_go, setPc_state,
      setPc_cache] at h ⊢ <;> grind
  · intro q _; exact pairInv_left_true (by simp)
  · intro q _; exact pairInv_right_true (by simp)

theorem inv_s2_none {c : Config P} (hI : Inv c) {p : P} (hp : c.pc p = .s2)
    (ha : c.goAddr = none) : Inv { c.setPc p .idle with state := true } := by
  apply hI.of_update (p := p) (x' := .idle) rfl
  · intro _; have := hI.local_ p; simpa [hp, LocalInv] using this
  · simp
  · exact hI.fresh_addr
  · simp [LocalInv]
  · intro q _
    have h := hI.local_ q
    cases hc : c.pc q <;> simp only [hc, LocalInv, setPc_cnt, setPc_goAddr, setPc_go,
      setPc_cache, setPc_bit] at h ⊢ <;> grind
  · intro q _; exact pairInv_left_true (by simp)
  · intro q _; exact pairInv_right_true (by simp)

theorem inv_s2_some {c : Config P} (hI : Inv c) {p : P} (hp : c.pc p = .s2) {a : Cell P}
    (ha : c.goAddr = some a) : Inv (c.setPc p (.s4 a)) := by
  apply hI.of_update (p := p) (x' := .s4 a) rfl
  · exact hI.state_bit
  · intro _ _; exact ⟨p, by simp [setPc, PC.PastLine1]⟩
  · exact hI.fresh_addr
  · have := hI.local_ p
    simp only [hp, LocalInv] at this
    exact ⟨this, hI.fresh_addr a ha⟩
  · exact fun q _ => hI.local_ q
  · intro q _; exact pairInv_left_true (by simp)
  · intro q _
    have h := hI.local_ q
    cases hc : c.pc q <;> simp_all [LocalInv, PairInv]

theorem inv_s4 {c : Config P} (hI : Inv c) {p : P} {a : Cell P} (hp : c.pc p = .s4 a) :
    Inv { c.setPc p .idle with go := Function.update c.go a true, state := true,
                               cache := c.writeCache p a } := by
  have hb : c.bit = true := by have := hI.local_ p; simp only [hp, LocalInv] at this; exact this.1
  apply hI.of_update (p := p) (x' := .idle) rfl
  · intro _; exact hb
  · simp
  · exact hI.fresh_addr
  · simp [LocalInv]
  · intro q hq
    have h := hI.local_ q
    have hpair := hI.pair q p
    rw [hp] at hpair
    cases hc : c.pc q <;> simp_all [LocalInv, PairInv, writeCache, Function.update_apply]
    all_goals grind
  · intro q _; exact pairInv_left_true (by simp)
  · intro q _; exact pairInv_right_true (by simp)

theorem inv_w5 {c : Config P} (hI : Inv c) {p : P} (hp : c.pc p = .w5) :
    Inv { c.setPc p (.w6 (p, c.cnt p)) with cnt := Function.update c.cnt p (c.cnt p + 1) } := by
  have hmono : ∀ q, c.cnt q ≤ Function.update c.cnt p (c.cnt p + 1) q := by
    intro q; by_cases hq : q = p
    · subst hq; simp
    · simp [Function.update_of_ne hq]
  apply hI.of_update (p := p) (x' := .w6 (p, c.cnt p)) rfl
  · exact hI.state_bit
  · intro hb hs
    obtain ⟨q, hq⟩ := hI.bit_past hb hs
    exact ⟨q, bitPast_of_update (by simp [hp, PC.PastLine1]) hq⟩
  · intro r hr; exact lt_of_lt_of_le (hI.fresh_addr r hr) (hmono _)
  · refine ⟨rfl, by simp, ?_⟩
    intro h
    have := hI.fresh_addr _ h
    simp at this
  · intro q _
    have h := hI.local_ q
    have hm := hmono
    cases hc : c.pc q <;> simp only [hc, LocalInv, setPc_goAddr, setPc_go, setPc_state,
      setPc_cache, setPc_bit] at h ⊢ <;> grind
  · intro q _
    have h := hI.local_ q
    cases hc : c.pc q <;> simp only [hc, LocalInv, PairInv] at h ⊢
    rintro rfl
    simp at h
  · intro q _; exact pairInv_right_true (by simp)

theorem inv_w6 {c : Config P} (hI : Inv c) (h1 : AtMostOneWaiter c) {p : P} {g : Cell P}
    (hp : c.pc p = .w6 g) :
    Inv { c.setPc p (.w7 g) with go := Function.update c.go g false,
                                 cache := c.writeCache p g } := by
  have hl := hI.local_ p
  simp only [hp, LocalInv] at hl
  apply hI.of_update (p := p) (x' := .w7 g) rfl
  · exact hI.state_bit
  · intro hb hs
    obtain ⟨q, hq⟩ := hI.bit_past hb hs
    exact ⟨q, bitPast_of_update (by simp [hp, PC.PastLine1]) hq⟩
  · exact hI.fresh_addr
  · simp [LocalInv, writeCache, hl]
  · intro q hq
    have h := hI.local_ q
    have hw := not_inWait_of_ne h1 (by simp [hp, PC.InWait]) hq
    cases hc : c.pc q <;> simp_all [LocalInv, PC.InWait]
  · intro q hq
    have h := hI.pair p q
    rw [hp] at h
    cases hc : c.pc q <;> simp_all [PairInv]
  · intro q _; exact pairInv_right_true (by simp)

theorem inv_w7 {c : Config P} (hI : Inv c) (h1 : AtMostOneWaiter c) {p : P} {g : Cell P}
    (hp : c.pc p = .w7 g) : Inv { c.setPc p (.w8 g) with goAddr := some g } := by
  have hl := hI.local_ p
  simp only [hp, LocalInv] at hl
  apply hI.of_update (p := p) (x' := .w8 g) rfl
  · exact hI.state_bit
  · intro hb hs
    obtain ⟨q, hq⟩ := hI.bit_past hb hs
    exact ⟨q, bitPast_of_update (by simp [hp, PC.PastLine1]) hq⟩
  · intro r hr
    simp only [Option.some.injEq] at hr
    subst hr
    rw [hl.1]; exact hl.2.1
  · simp [LocalInv, hl]
  · intro q hq
    have h := hI.local_ q
    have hw := not_inWait_of_ne h1 (by simp [hp, PC.InWait]) hq
    cases hc : c.pc q <;> simp_all [LocalInv, PC.InWait]
  · intro q _; exact pairInv_left_true (by simp)
  · intro q _; exact pairInv_right_true (by simp)

theorem inv_w8_true {c : Config P} (hI : Inv c) (h1 : AtMostOneWaiter c) {p : P} {g : Cell P}
    (hp : c.pc p = .w8 g) (hb : c.bit = true) :
    Inv { c.setPc p .idle with state := true } := by
  apply hI.of_update (p := p) (x' := .idle) rfl
  · intro _; exact hb
  · simp
  · exact hI.fresh_addr
  · simp [LocalInv]
  · intro q hq
    have h := hI.local_ q
    have hw := not_inWait_of_ne h1 (by simp [hp, PC.InWait]) hq
    cases hc : c.pc q <;> simp_all [LocalInv, PC.InWait]
  · intro q _; exact pairInv_left_true (by simp)
  · intro q _; exact pairInv_right_true (by simp)

theorem inv_w8_false {c : Config P} (hI : Inv c) {p : P} {g : Cell P}
    (hp : c.pc p = .w8 g) (hb : c.bit = false) : Inv (c.setPc p (.w9 g)) := by
  have hl := hI.local_ p
  simp only [hp, LocalInv] at hl
  have hs : c.state = false := by
    cases h : c.state
    · rfl
    · simpa [hb] using hI.state_bit h
  have hg : c.go g = false := by
    cases h : c.go g
    · rfl
    · simpa [hb] using hl.2.2.2.1 h
  apply hI.of_update (p := p) (x' := .w9 g) rfl
  · exact hI.state_bit
  · simp [hb]
  · exact hI.fresh_addr
  · simp only [LocalInv, setPc_cnt, setPc_goAddr, setPc_go, setPc_state, setPc_cache]
    exact ⟨hl.1, hl.2.1, hl.2.2.1, by rw [hg, hs], hl.2.2.2.2⟩
  · exact fun q _ => hI.local_ q
  · intro q _
    have h := hI.local_ q
    cases hc : c.pc q <;> simp_all [LocalInv, PairInv]
  · intro q _; exact pairInv_right_true (by simp)

theorem inv_w9_true {c : Config P} (hI : Inv c) (h1 : AtMostOneWaiter c) {p : P} {g : Cell P}
    (hp : c.pc p = .w9 g) : Inv { c.setPc p .idle with cache := c.readCache p g } := by
  apply hI.of_update (p := p) (x' := .idle) rfl
  · exact hI.state_bit
  · intro hb hs
    obtain ⟨q, hq⟩ := hI.bit_past hb hs
    exact ⟨q, bitPast_of_update (by simp [hp, PC.PastLine1]) hq⟩
  · exact hI.fresh_addr
  · simp [LocalInv]
  · intro q hq
    have h := hI.local_ q
    have hw := not_inWait_of_ne h1 (by simp [hp, PC.InWait]) hq
    cases hc : c.pc q <;> simp_all [LocalInv, PC.InWait]
  · intro q _; exact pairInv_left_true (by simp)
  · intro q _; exact pairInv_right_true (by simp)

theorem inv_w9_false {c : Config P} (hI : Inv c) (h1 : AtMostOneWaiter c) {p : P} {g : Cell P}
    (hp : c.pc p = .w9 g) : Inv { c with cache := c.readCache p g } := by
  have hl := hI.local_ p
  simp only [hp, LocalInv] at hl
  have hpc : ({ c with cache := c.readCache p g } : Config P).pc = Function.update c.pc p (.w9 g) := by
    simp [← hp]
  apply hI.of_update (p := p) (x' := .w9 g) hpc
  · exact hI.state_bit
  · exact hI.bit_past
  · exact hI.fresh_addr
  · simp [LocalInv, readCache, hl]
  · intro q hq
    have h := hI.local_ q
    have hw := not_inWait_of_ne h1 (by simp [hp, PC.InWait]) hq
    cases hc : c.pc q <;> simp_all [LocalInv, PC.InWait]
  · intro q _; simpa [hp] using hI.pair p q
  · intro q _; simpa [hp] using hI.pair q p

/-- The invariant is preserved by every action, as long as at most one process is waiting. -/
theorem Inv.step {c : Config P} (hI : Inv c) (h1 : AtMostOneWaiter c) (a : Action P) :
    Inv (stepAct a c) := by
  rcases a with p | p | p
  · simp only [stepAct]; split_ifs with hp
    · exact inv_invoke hI hp (.inl rfl)
    · exact hI
  · simp only [stepAct]; split_ifs with hp
    · exact inv_invoke hI hp (.inr rfl)
    · exact hI
  · simp only [stepAct, stepProc]
    cases hp : c.pc p with
    | idle => exact hI
    | s1 => exact inv_s1 hI hp
    | s2 =>
      cases ha : c.goAddr with
      | none => exact inv_s2_none hI hp ha
      | some a => exact inv_s2_some hI hp ha
    | s4 a => exact inv_s4 hI hp
    | w5 => exact inv_w5 hI hp
    | w6 g => exact inv_w6 hI h1 hp
    | w7 g => exact inv_w7 hI h1 hp
    | w8 g =>
      cases hb : c.bit
      · exact inv_w8_false hI hp hb
      · exact inv_w8_true hI h1 hp hb
    | w9 g =>
      dsimp only
      split_ifs
      · exact inv_w9_true hI h1 hp
      · exact inv_w9_false hI h1 hp

/-- The invariant holds in every configuration of an execution without concurrent waits. -/
theorem inv_exec {σ : ℕ → Action P} (hσ : NoConcurrentWaits σ) (t : ℕ) : Inv (exec σ t) := by
  induction t with
  | zero => exact inv_init
  | succ t ih => exact ih.step (hσ t) (σ t)

/-! ## Basic facts about steps -/

theorem stepProc_pc_of_ne (c : Config P) {p q : P} (hq : q ≠ p) :
    (stepProc c p).pc q = c.pc q := by
  unfold stepProc
  split
  · rfl
  all_goals (try split) <;> simp [Function.update_of_ne hq]

/-- An action other than a step of `q` does not change the program counter of a busy process `q`. -/
theorem stepAct_pc_of_ne (c : Config P) {a : Action P} {q : P} (ha : a ≠ .step q)
    (hq : c.pc q ≠ .idle) : (stepAct a c).pc q = c.pc q := by
  rcases a with p | p | p <;> simp only [stepAct]
  · split_ifs with h
    · have : q ≠ p := by rintro rfl; exact hq h
      simp [Function.update_of_ne this]
    · rfl
  · split_ifs with h
    · have : q ≠ p := by rintro rfl; exact hq h
      simp [Function.update_of_ne this]
    · rfl
  · exact stepProc_pc_of_ne c (fun h => ha (h ▸ rfl))

omit [DecidableEq P] in
theorem PC.ne_idle_of_inSet {x : PC P} (h : x.InSet) : x ≠ .idle := by
  rintro rfl; exact h

omit [DecidableEq P] in
theorem PC.ne_idle_of_inWait {x : PC P} (h : x.InWait) : x ≠ .idle := by
  rintro rfl; exact h

/-- The abstract state never goes back from `1` to `0`. -/
theorem stepAct_state (c : Config P) (a : Action P) (h : c.state = true) :
    (stepAct a c).state = true := by
  rcases a with p | p | p <;> simp only [stepAct]
  · split_ifs <;> simpa
  · split_ifs <;> simpa
  · unfold stepProc
    split
    · exact h
    all_goals (try split) <;> simp [h]

/-- Where the abstract state changes from `0` to `1`, some process is executing `set()` after its
line 1. -/
theorem stepAct_flip (c : Config P) (hI : Inv c) (a : Action P) (h0 : c.state = false)
    (h1 : (stepAct a c).state = true) : ∃ q, (c.pc q).PastLine1 := by
  rcases a with p | p | p <;> simp only [stepAct] at h1
  · split_ifs at h1 <;> simp_all
  · split_ifs at h1 <;> simp_all
  · revert h1
    unfold stepProc
    cases hp : c.pc p with
    | s2 => exact fun _ => ⟨p, by simp [hp, PC.PastLine1]⟩
    | s4 a => exact fun _ => ⟨p, by simp [hp, PC.PastLine1]⟩
    | w8 g =>
      dsimp only
      split_ifs with hb
      · exact fun _ => hI.bit_past hb h0
      · simp [h0]
    | w9 g =>
      dsimp only
      split_ifs <;> simp [h0]
    | _ => simp [h0, setPc]

/-! ## Counting steps -/

/-- The number of steps of process `p` among the events `t, t+1, …, t+k-1` of the schedule. -/
def ownSteps (σ : ℕ → Action P) (p : P) (t k : ℕ) : ℕ :=
  ((Finset.range k).filter (fun i => σ (t + i) = Action.step p)).card

/-- The number of steps of process `p` among the events `t, …, t+k-1` that are RMRs according to the
cost model `rmr` (`rmr c p` = whether the next step of `p` in configuration `c` is an RMR). -/
def rmrSteps (rmr : Config P → P → Bool) (σ : ℕ → Action P) (p : P) (t k : ℕ) : ℕ :=
  ((Finset.range k).filter (fun i => σ (t + i) = Action.step p ∧ rmr (exec σ (t + i)) p = true)).card

omit [DecidableEq P] in
/-- Potential-function argument: if every "good" event with `Q` decreases the potential `B` by at
least one, and other good events do not increase it, then the number of `Q`-events in a window of
good events is bounded by the initial potential. -/
theorem card_le_of_potential {Q good : ℕ → Prop} [DecidablePred Q] (B : ℕ → ℕ) {t k : ℕ}
    (hB : ∀ j, good j → (if Q j then 1 else 0) + B (j + 1) ≤ B j) (hk : ∀ i < k, good (t + i)) :
    ((Finset.range k).filter (fun i => Q (t + i))).card + B (t + k) ≤ B t := by
  induction k with
  | zero => simp
  | succ k ih =>
    have ih := ih (fun i hi => hk i (by omega))
    have hs := hB (t + k) (hk k (by omega))
    rw [Finset.range_add_one, Finset.filter_insert]
    have hnot : k ∉ (Finset.range k).filter (fun i => Q (t + i)) := by simp
    split_ifs at hs ⊢ with hq
    · rw [Finset.card_insert_of_notMem hnot]
      rw [show t + (k + 1) = t + k + 1 by omega]
      omega
    · rw [show t + (k + 1) = t + k + 1 by omega]
      omega

/-- The program counter of `p` after a step of `p`. -/
def nextPc (c : Config P) (p : P) : PC P :=
  match c.pc p with
  | .idle => .idle
  | .s1 => .s2
  | .s2 => match c.goAddr with
    | none => .idle
    | some a => .s4 a
  | .s4 _ => .idle
  | .w5 => .w6 (p, c.cnt p)
  | .w6 g => .w7 g
  | .w7 g => .w8 g
  | .w8 g => if c.bit then .idle else .w9 g
  | .w9 g => if c.go g then .idle else .w9 g

theorem stepProc_pc_self (c : Config P) (p : P) : (stepProc c p).pc p = nextPc c p := by
  unfold stepProc nextPc
  split
  · simp_all
  all_goals (try split) <;> simp_all

/-! ## Potentials -/

/-- Remaining number of own steps of an execution of `set()`. -/
def setRank : PC P → ℕ
  | .s1 => 3
  | .s2 => 2
  | .s4 _ => 1
  | _ => 0

/-- Remaining number of own steps of an execution of `wait()`, once `State = 1`. -/
def waitRank : PC P → ℕ
  | .w5 => 4
  | .w6 _ => 3
  | .w7 _ => 2
  | .w8 _ | .w9 _ => 1
  | _ => 0

/-- Remaining DSM RMR budget of an execution of `wait()`. -/
def dsmBudget : PC P → ℕ
  | .w5 | .w6 _ | .w7 _ => 2
  | .w8 _ => 1
  | _ => 0

/-- Remaining CC RMR budget of an execution of `wait()`. -/
def ccBudget : PC P → ℕ
  | .w5 | .w6 _ => 4
  | .w7 _ => 3
  | .w8 _ => 2
  | .w9 _ => 1
  | _ => 0

/-! ## Cost models for RMRs -/

/-- DSM cost model: the next step of `p` in configuration `c` is an RMR iff it accesses a location
outside `p`'s memory partition. Cell `(q, k)` lives in `q`'s partition; `Bit` and `GoAddr` are
conservatively counted as remote for every process. Line 5 (`new Boolean`) is local. -/
def rmrDSM (c : Config P) (p : P) : Bool :=
  match c.pc p with
  | .idle | .w5 => false
  | .s1 | .s2 | .w7 _ | .w8 _ => true
  | .s4 a => decide (a.1 ≠ p)
  | .w6 g | .w9 g => decide (g.1 ≠ p)

/-- CC cost model: every access to `Bit`/`GoAddr` and every write is (conservatively) an RMR; a read
of a cell at line 9 is an RMR iff `p` holds no valid cached copy of it (writes invalidate the copies
of all other processes; the writer and readers obtain a valid copy). -/
def rmrCC (c : Config P) (p : P) : Bool :=
  match c.pc p with
  | .idle | .w5 => false
  | .w9 g => !(c.cache p g)
  | _ => true

theorem set_step (c : Config P) (a : Action P) (p : P) (h : (c.pc p).InSet) :
    (if a = .step p then 1 else 0) + setRank ((stepAct a c).pc p) ≤ setRank (c.pc p) := by
  by_cases ha : a = .step p
  · subst ha
    simp only [↓reduceIte, stepAct, stepProc_pc_self, nextPc]
    cases hp : c.pc p <;> simp [hp, PC.InSet] at h ⊢ <;> (try cases c.goAddr) <;> simp [setRank]
  · simp only [ha, ↓reduceIte, stepAct_pc_of_ne c ha (PC.ne_idle_of_inSet h)]; simp

theorem wait_step {c : Config P} (hI : Inv c) (a : Action P) (p : P) (h : (c.pc p).InWait)
    (hs : c.state = true) :
    (if a = .step p then 1 else 0) + waitRank ((stepAct a c).pc p) ≤ waitRank (c.pc p) := by
  by_cases ha : a = .step p
  · subst ha
    have hl := hI.local_ p
    have hb := hI.state_bit hs
    simp only [↓reduceIte, stepAct, stepProc_pc_self, nextPc]
    cases hp : c.pc p <;> simp [hp, PC.InWait, LocalInv] at h hl ⊢ <;> simp_all [waitRank]
  · simp only [ha, ↓reduceIte, stepAct_pc_of_ne c ha (PC.ne_idle_of_inWait h)]; simp

theorem wait_step_dsm {c : Config P} (hI : Inv c) (a : Action P) (p : P) (h : (c.pc p).InWait) :
    (if a = .step p ∧ rmrDSM c p = true then 1 else 0) + dsmBudget ((stepAct a c).pc p) ≤
      dsmBudget (c.pc p) := by
  by_cases ha : a = .step p
  · subst ha
    have hl := hI.local_ p
    simp only [true_and, stepAct, stepProc_pc_self, nextPc, rmrDSM]
    cases hp : c.pc p <;> simp [hp, PC.InWait, LocalInv] at h hl ⊢ <;>
      (try split_ifs) <;> simp_all [dsmBudget]
  · simp only [ha, false_and, ↓reduceIte, stepAct_pc_of_ne c ha (PC.ne_idle_of_inWait h)]; simp

theorem wait_step_cc {c : Config P} (hI : Inv c) (a : Action P) (p : P) (h : (c.pc p).InWait) :
    (if a = .step p ∧ rmrCC c p = true then 1 else 0) + ccBudget ((stepAct a c).pc p) ≤
      ccBudget (c.pc p) := by
  by_cases ha : a = .step p
  · subst ha
    have hl := hI.local_ p
    simp only [true_and, stepAct, stepProc_pc_self, nextPc, rmrCC]
    cases hp : c.pc p <;> simp [hp, PC.InWait, LocalInv] at h hl ⊢ <;>
      (try split_ifs) <;> simp_all [ccBudget]
  · simp only [ha, false_and, ↓reduceIte, stepAct_pc_of_ne c ha (PC.ne_idle_of_inWait h)]; simp

/-! ## Theorem 1 -/

/-- Initially `X.State = 0`. -/
theorem state_exec_zero (σ : ℕ → Action P) : (exec σ 0).state = false := rfl

/-- `X.State` never changes from `1` back to `0`. -/
theorem state_mono (σ : ℕ → Action P) {t u : ℕ} (htu : t ≤ u) (h : (exec σ t).state = true) :
    (exec σ u).state = true := by
  induction u, htu using Nat.le_induction with
  | base => exact h
  | succ u _ ih => exact stepAct_state _ _ ih

/-- **Theorem 1 (i) of [JJJ19]** (`set()` is linearizable), first half: the single event at which
`X.State` changes from `0` to `1` happens while some process `q` is executing `set()` and has
already performed its line 1; this event is the linearization point of `q`'s `set()`. -/
theorem theorem1_i_linearization_point {σ : ℕ → Action P} (hσ : NoConcurrentWaits σ) (t : ℕ)
    (h0 : (exec σ t).state = false) (h1 : (exec σ (t + 1)).state = true) :
    ∃ q, ((exec σ t).pc q).PastLine1 :=
  stepAct_flip _ (inv_exec hσ t) (σ t) h0 h1

/-- **Theorem 1 (i) of [JJJ19]**, second half: when an execution of `set()` completes, `X.State`
is `1`. Hence every completed `set()` other than the one linearized at the `0 → 1` change can be
linearized (as a no-op) at its completion. (This holds for every schedule.) -/
theorem theorem1_i_set_completes (σ : ℕ → Action P) (p : P) (t : ℕ)
    (h : ((exec σ t).pc p).InSet) (h' : ¬ ((exec σ (t + 1)).pc p).InSet) :
    (exec σ (t + 1)).state = true := by
  simp only [exec] at h' ⊢
  set c := exec σ t
  by_cases ha : σ t = .step p
  · rw [ha] at h' ⊢
    simp only [stepAct] at h' ⊢
    unfold stepProc at h' ⊢
    cases hp : c.pc p <;> simp [hp, PC.InSet] at h h' ⊢
    · cases hg : c.goAddr <;> simp_all
  · exact absurd (by rwa [stepAct_pc_of_ne c ha (PC.ne_idle_of_inSet h)]) h'

/-- **Theorem 1 (ii) of [JJJ19]**: when an execution of `wait()` returns, `X.State` is `1`. -/
theorem theorem1_ii {σ : ℕ → Action P} (hσ : NoConcurrentWaits σ) (p : P) (t : ℕ)
    (h : ((exec σ t).pc p).InWait) (h' : ¬ ((exec σ (t + 1)).pc p).InWait) :
    (exec σ (t + 1)).state = true := by
  have hI := inv_exec hσ t
  simp only [exec] at h' ⊢
  set c := exec σ t
  by_cases ha : σ t = .step p
  · rw [ha] at h' ⊢
    have hl := hI.local_ p
    simp only [stepAct] at h' ⊢
    unfold stepProc at h' ⊢
    cases hp : c.pc p <;> simp [hp, PC.InWait, LocalInv] at h h' hl ⊢
    · split_ifs at h' ⊢ <;> simp_all
    · split_ifs at h' ⊢ with hg <;> simp_all
  · exact absurd (by rwa [stepAct_pc_of_ne c ha (PC.ne_idle_of_inWait h)]) h'

/-- **Theorem 1 (iii) of [JJJ19]**: an execution of `set()` completes within 3 of its own steps:
while `p` stays inside one execution of `set()`, it takes at most 3 steps. (This holds for every
schedule.) -/
theorem theorem1_iii (σ : ℕ → Action P) (p : P) (t k : ℕ)
    (h : ∀ i < k, ((exec σ (t + i)).pc p).InSet) : ownSteps σ p t k ≤ 3 := by
  have := card_le_of_potential (Q := fun j => σ j = .step p)
    (good := fun j => ((exec σ j).pc p).InSet) (fun j => setRank ((exec σ j).pc p))
    (fun j hj => set_step (exec σ j) (σ j) p hj) h
  have hb : setRank ((exec σ t).pc p) ≤ 3 := by
    cases (exec σ t).pc p <;> simp [setRank]
  unfold ownSteps; omega

/-- **Theorem 1 (iv) of [JJJ19]**: once `X.State = 1`, any execution of `wait()` by `p` completes
within 4 of `p`'s own steps: if `State = 1` at time `t`, then while `p` stays inside one execution
of `wait()` from time `t` on, it takes at most 4 steps. -/
theorem theorem1_iv {σ : ℕ → Action P} (hσ : NoConcurrentWaits σ) (p : P) (t k : ℕ)
    (hs : (exec σ t).state = true) (h : ∀ i < k, ((exec σ (t + i)).pc p).InWait) :
    ownSteps σ p t k ≤ 4 := by
  have := card_le_of_potential (Q := fun j => σ j = .step p)
    (good := fun j => ((exec σ j).pc p).InWait ∧ (exec σ j).state = true)
    (fun j => waitRank ((exec σ j).pc p))
    (fun j hj => wait_step (inv_exec hσ j) (σ j) p hj.1 hj.2)
    (fun i hi => ⟨h i hi, state_mono σ (by omega) hs⟩)
  have : waitRank ((exec σ t).pc p) ≤ 4 := by
    cases (exec σ t).pc p <;> simp [waitRank]
  unfold ownSteps; omega

/-- **Theorem 1 (v) of [JJJ19]**, `set()`: an execution of `set()` performs at most 3 shared-memory
accesses, hence at most 3 RMRs in any cost model (in particular `rmrDSM` and `rmrCC`). -/
theorem theorem1_v_set (rmr : Config P → P → Bool) (σ : ℕ → Action P) (p : P) (t k : ℕ)
    (h : ∀ i < k, ((exec σ (t + i)).pc p).InSet) : rmrSteps rmr σ p t k ≤ 3 := by
  refine le_trans ?_ (theorem1_iii σ p t k h)
  unfold rmrSteps ownSteps
  exact Finset.card_le_card (Finset.monotone_filter_right _ fun _ _ h => h.1)

/-- **Theorem 1 (v) of [JJJ19]**, `wait()` on a DSM machine: an execution of `wait()` incurs at most
2 RMRs (lines 7 and 8; the cell `go` lives in the waiter's partition, so line 9 spins locally). -/
theorem theorem1_v_wait_dsm {σ : ℕ → Action P} (hσ : NoConcurrentWaits σ) (p : P) (t k : ℕ)
    (h : ∀ i < k, ((exec σ (t + i)).pc p).InWait) : rmrSteps rmrDSM σ p t k ≤ 2 := by
  have := card_le_of_potential (Q := fun j => σ j = .step p ∧ rmrDSM (exec σ j) p = true)
    (good := fun j => ((exec σ j).pc p).InWait)
    (fun j => dsmBudget ((exec σ j).pc p))
    (fun j hj => wait_step_dsm (inv_exec hσ j) (σ j) p hj) h
  have : dsmBudget ((exec σ t).pc p) ≤ 2 := by
    cases (exec σ t).pc p <;> simp [dsmBudget]
  unfold rmrSteps; omega

/-- **Theorem 1 (v) of [JJJ19]**, `wait()` on a CC machine: an execution of `wait()` incurs at most
4 RMRs (lines 6, 7, 8, and at most one cache miss at line 9). -/
theorem theorem1_v_wait_cc {σ : ℕ → Action P} (hσ : NoConcurrentWaits σ) (p : P) (t k : ℕ)
    (h : ∀ i < k, ((exec σ (t + i)).pc p).InWait) : rmrSteps rmrCC σ p t k ≤ 4 := by
  have := card_le_of_potential (Q := fun j => σ j = .step p ∧ rmrCC (exec σ j) p = true)
    (good := fun j => ((exec σ j).pc p).InWait)
    (fun j => ccBudget ((exec σ j).pc p))
    (fun j hj => wait_step_cc (inv_exec hσ j) (σ j) p hj) h
  have : ccBudget ((exec σ t).pc p) ≤ 4 := by
    cases (exec σ t).pc p <;> simp [ccBudget]
  unfold rmrSteps; omega

/-! ## Non-vacuity of the hypothesis -/

/-- A process can only enter `wait()` through an `invokeWait` action. -/
theorem enter_wait (c : Config P) (a : Action P) (q : P) (h : ¬ (c.pc q).InWait)
    (h' : ((stepAct a c).pc q).InWait) : a = .invokeWait q := by
  rcases a with p | p | p
  · simp only [stepAct] at h'
    split_ifs at h' with hp
    · by_cases hq : q = p
      · subst hq; simp [PC.InWait] at h'
      · simp [Function.update_of_ne hq] at h'; exact absurd h' h
    · exact absurd h' h
  · by_cases hq : q = p
    · rw [hq]
    · simp only [stepAct] at h'
      split_ifs at h' <;> simp_all
  · by_cases hq : q = p
    · subst hq
      simp only [stepAct, stepProc_pc_self, nextPc] at h'
      cases hc : c.pc q <;> simp [hc, PC.InWait] at h h'
      cases hg : c.goAddr <;> simp_all
    · simp only [stepAct, stepProc_pc_of_ne c hq] at h'; exact absurd h' h

/-- A sufficient condition for the hypothesis of Theorem 1: only one process ever invokes
`wait()` (as in the main algorithm, where only the owner of a queue node waits on its signals). -/
theorem noConcurrentWaits_of_single_waiter (σ : ℕ → Action P) (w : P)
    (hw : ∀ i q, σ i = .invokeWait q → q = w) : NoConcurrentWaits σ := by
  have key : ∀ t q, ((exec σ t).pc q).InWait → q = w := by
    intro t
    induction t with
    | zero => intro q h; simp [exec, init, PC.InWait] at h
    | succ t ih =>
      intro q h
      by_cases h0 : ((exec σ t).pc q).InWait
      · exact ih q h0
      · exact hw t q (enter_wait _ _ q h0 h)
  intro t p q hp hq
  rw [key t p hp, key t q hq]

/-- A concrete run (Case 2 of the proof in Appendix D): process `0` invokes `wait()`, finds
`Bit = 0` and spins; then process `1` performs `set()`, which wakes `0` up through `GoAddr`. -/
def exampleSchedule : ℕ → Action (Fin 2) := fun i =>
  [Action.invokeWait 0, .step 0, .step 0, .step 0, .step 0, .invokeSet 1, .step 1, .step 1,
    .step 1, .step 0].getD i (.step 0)

theorem exampleSchedule_noConcurrentWaits : NoConcurrentWaits exampleSchedule :=
  noConcurrentWaits_of_single_waiter _ 0 (by
    intro i q h
    unfold exampleSchedule at h
    rcases lt_or_ge i 10 with hi | hi
    · interval_cases i <;> simp_all
    · rw [List.getD_eq_default _ _ (by simpa using hi)] at h; cases h)

/-- In the example run, process `0` spins at line 9 at time 9 and its `wait()` has returned at
time 10, with `X.State = 1`. -/
example : (exec exampleSchedule 9).pc 0 = .w9 (0, 0) ∧ (exec exampleSchedule 10).pc 0 = .idle ∧
    (exec exampleSchedule 10).state = true := by
  decide

/-! ## Side check: crashes (the recoverable model of Section 1.1)

Section 2 does not mention crashes, but the Signal object is used inside a recoverable algorithm
(Section 1.1: a crash resets the local state and the program counter of the crashed process to its
Remainder section; shared variables survive). We extend the model by crash steps and exhibit the
following execution, with two processes `W = 0` and `S = 1`, which respects the hypothesis that no two
executions of `wait()` are concurrent:

1. `W` invokes `wait()`, executes lines 5–8, reads `Bit = 0` and starts spinning at line 9;
2. `S` invokes `set()`, executes line 1 (`Bit ← 1`) and crashes;
3. `W` takes `k` further steps, for arbitrary `k`: it keeps spinning at line 9, with `Bit = 1`
   (`crash_spin`);
4. `W` crashes, invokes `wait()` again, and this new `wait()` returns after 4 steps, having read
   `Bit = 1` at line 8 (`crash_rewait`).

The second `wait()` returns, so in any linearization `S`'s (only) `set()` must take effect before
that. If a crashed operation must take effect before the crash or not at all (strict
linearizability), it takes effect before step 3, so `W`'s first `wait()` takes `k` steps after
`X.State = 1` without completing — for every `k`, contradicting Theorem 1 (iv). Under weaker notions
that let `S`'s interrupted `set()` take effect later (e.g. just before `W`'s second `wait()`, as `S`
never invokes another operation), this run is no counterexample. In the main algorithm of the paper
an interrupted `set()` is re-executed after recovery, so this does not affect the main theorem. -/

/-- Actions of the extended model with crashes. -/
inductive CAction (P : Type) where
  /-- A normal action. -/
  | act (a : Action P)
  /-- A crash of `p`: its program counter (and local state) is reset; shared memory survives. -/
  | crash (p : P)

/-- Effect of an action of the extended model. -/
def cstep : CAction P → Config P → Config P
  | .act a, c => stepAct a c
  | .crash p, c => c.setPc p .idle

/-- The configuration after the prefix "`W = 0` executes lines 5–8 and spins; `S = 1` executes line
1 of `set()` and crashes". -/
def crashPrefix : Config (Fin 2) :=
  [CAction.act (.invokeWait 0), .act (.step 0), .act (.step 0), .act (.step 0), .act (.step 0),
    .act (.invokeSet 1), .act (.step 1), .crash 1].foldl (fun c a => cstep a c) init

theorem crashPrefix_spec : crashPrefix.pc 0 = .w9 (0, 0) ∧ crashPrefix.pc 1 = .idle ∧
    crashPrefix.bit = true ∧ crashPrefix.go (0, 0) = false := by
  decide

/-- A step of a process spinning at line 9 on a cell that is `false` changes nothing but the cache. -/
theorem spin_step (c : Config P) (p : P) (g : Cell P) (hp : c.pc p = .w9 g) (hg : c.go g = false) :
    (stepAct (.step p) c).pc = c.pc ∧ (stepAct (.step p) c).bit = c.bit ∧
      (stepAct (.step p) c).go = c.go := by
  simp [stepAct, stepProc, hp, hg]

/-- Side check, part 1: after the crash prefix, `W` spins at line 9 forever if only `W` takes steps:
after any number `k` of further steps of `W`, `W` is still inside its first `wait()` (at line 9),
`S` is idle, and `Bit = 1`. -/
theorem crash_spin (k : ℕ) :
    let c := (cstep (.act (.step 0)))^[k] crashPrefix
    c.pc 0 = .w9 (0, 0) ∧ c.pc 1 = .idle ∧ c.bit = true ∧ c.go (0, 0) = false := by
  induction k with
  | zero => exact crashPrefix_spec
  | succ k ih =>
    simp only [Function.iterate_succ_apply']
    obtain ⟨h0, h1, hb, hg⟩ := ih
    obtain ⟨e1, e2, e3⟩ := spin_step _ 0 (0, 0) h0 hg
    simp only [cstep]
    exact ⟨by rw [e1, h0], by rw [e1, h1], by rw [e2, hb], by rw [e3, hg]⟩

/-- Side check, part 2: if, in a configuration with `Bit = 1`, process `p` crashes and then invokes
`wait()`, its new `wait()` returns after 4 steps, the last of which reads `Bit = 1` at line 8. -/
theorem crash_rewait (c : Config P) (p : P) (hb : c.bit = true) :
    let d := (cstep (.act (.step p)))^[3] (cstep (.act (.invokeWait p)) (cstep (.crash p) c))
    d.pc p = .w8 (p, c.cnt p) ∧ d.bit = true ∧ (cstep (.act (.step p)) d).pc p = .idle := by
  simp [cstep, stepAct, stepProc, setPc, hb]

end Podc.RMESubLogBoth.Signal
