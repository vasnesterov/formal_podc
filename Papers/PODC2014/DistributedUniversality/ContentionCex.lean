import Papers.PODC2014.DistributedUniversality.Model

/-!
# Figure 2 is not contention-aware (Theorem 2)

Theorem 2 of [Raynal–Stainer–Taubenfeld, PODC 2014] claims that the algorithm of Figure 2 is a
non-blocking *contention-aware* `(k,1)`-universal construction: "when a process invokes an operation
on a contention-aware universal construction, it must be able to complete its operation by accessing
only read/write registers in the absence of contention" (Section 4.1), contention being interval
contention (Introduction), and the execution of an operation starting when its issuer makes it
public (Section 3).

Line N2 treats an `adopt` received at line N1 as evidence of contention.  But `AC[2r-1][m]` is a
one-shot object per round number: an `adopt` can be caused by *stale* proposals left in the same
round number by processes that have since completed their operations and stopped.  A process that
then runs completely alone, but is behind in rounds, gets `adopt` and invokes the `k`-SC object.

* `theorem_2_not_contention_aware`: a concrete execution (`n = 3`, `k = 1`) of Figure 2 where this
  happens; the adopt-commit responses satisfy even the strong reading of the no-conflict property.
* `theorem_2_not_contention_aware_sequential`: with the weak reading of adopt-commit (satisfied by
  the standard implementation), even a fully sequential execution (`n = 2`) invokes `kSC[1]`.
* `fig2_solo_from_init_no_sc`: what is true — in an execution from the initial state in which only
  one process ever takes steps, no SC object (and no `AC[2r][-]`) is ever accessed.
-/

namespace Podc.DistributedUniversality.ContentionCex

open Podc.DistributedUniversality

variable {n k : ℕ}

/-- Every step increments the ghost clock by one. -/
theorem stepFn_time {M : Mode} {s s' : St n k} {a : Act n k} (h : stepFn M s a = some s') :
    s'.time = s.time + 1 := by
  rcases a with i | ⟨i, t, v⟩ | ⟨i, d⟩ <;> simp only [stepFn] at h <;>
    split at h <;> (try split at h) <;> (try split at h) <;> (try split at h) <;>
      (try split at h) <;> simp_all <;> (try subst h) <;> rfl

/-- The ghost clock counts the steps of a run (time = index in the run). -/
theorem run_time {M : Mode} {s s' : St n k} {as : List (Act n k)} (h : run M s as = some s') :
    s'.time = s.time + as.length := by
  induction as generalizing s with
  | nil => simp [run] at h; subst h; rfl
  | cons a as ih =>
    simp only [run, Option.bind_eq_some_iff] at h
    obtain ⟨s₁, h₁, h₂⟩ := h
    rw [ih h₂, stepFn_time h₁]; simp; omega

/-- Invariant: a process has not invoked any base object of a round later than its current round,
and a process that has not started has round `0`. -/
def RoundInv (s : St n k) : Prop :=
  ∀ q, ((s.loc q).pc = .init → (s.loc q).r = 0) ∧
    ∀ r, (s.loc q).r < r → (∀ b y, s.acI r b y q = none) ∧ s.scI r q = none

/-- The first line of a round is not the initialization line. -/
theorem startPC_ne_init (M : Mode) : startPC M ≠ .init := by
  unfold startPC; split <;> simp

/-- Line N2 does not go back to the initialization line. -/
theorem afterN1_ne_init (l : Loc n k) : afterN1 l ≠ .init := by
  unfold afterN1; split <;> simp

/-- Line N2: with only `commit` tags, the process proceeds to line 5. -/
theorem afterN1_of_all (l : Loc n k) (h : ∀ m, l.tag m = true) : afterN1 l = .collect 0 := by
  unfold afterN1; simp [h]

/-- `RoundInv` holds initially. -/
theorem roundInv_init : RoundInv (init : St n k) := by
  intro q; simp [init, initLoc]

/-- `RoundInv` is preserved by every step. -/
theorem roundInv_step {M : Mode} {s s' : St n k} {a : Act n k} (hs : RoundInv s)
    (h : stepFn M s a = some s') : RoundInv s' := by
  rcases a with i | ⟨i, t, v⟩ | ⟨i, d⟩ <;> simp only [stepFn] at h <;>
    split at h <;> (try split at h) <;> (try split at h) <;> (try split at h) <;>
      (try split at h) <;> simp only [Option.some.injEq, reduceCtorEq] at h <;> subst h <;>
      intro q <;> by_cases hq : q = i <;> (try subst hq) <;> have hq' := hs q <;>
      simp_all [RoundInv, startPC_ne_init, afterN1_ne_init] <;> (try split) <;> (try simp_all) <;>
      intro r hr <;> first
        | omega
        | exact (hs q).2 r (by omega)
        | exact (hs q).2 r (by have := (hs q).1 (by assumption); omega)

/-- `RoundInv` is preserved by runs. -/
theorem run_roundInv {M : Mode} {s s' : St n k} {as : List (Act n k)} (hs : RoundInv s)
    (h : run M s as = some s') : RoundInv s' := by
  induction as generalizing s with
  | nil => simp [run] at h; subst h; exact hs
  | cons a as ih =>
    simp only [run, Option.bind_eq_some_iff] at h
    obtain ⟨s₁, h₁, h₂⟩ := h
    exact ih (roundInv_step hs h₁) h₂

/-- The program counter of a process running solo in Figure 2 never reaches lines 2M–4M; at line
N1 all objects already treated in the current round got the tag `commit`. -/
def SoloPC (l : Loc n k) : Prop :=
  match l.pc with
  | .scInv | .scResp | .acInv _ | .acResp _ => False
  | .n1Inv m | .n1Resp m => ∀ y : Fin k, y.val < m → l.tag y = true
  | _ => True

/-- Invariant of a solo run of process `i` from the initial state. -/
def SoloInv (i : Fin n) (s : St n k) : Prop :=
  SoloPC (s.loc i) ∧ (∀ r j, s.scI r j = none) ∧ (∀ r y j, s.acI r true y j = none) ∧
    (∀ r y q, q ≠ i → s.acI r false y q = none)

/-- `SoloInv` holds initially. -/
theorem soloInv_init (i : Fin n) : SoloInv i (init : St n k) := by
  simp [SoloInv, SoloPC, init, initLoc]

/-- `SoloInv i` is preserved by the steps of process `i` (Figure 2): the no-conflicting-values
property forces `commit` at line N1, since nobody else invoked `AC[2r-1][m]`. -/
theorem soloInv_step {M : Mode} (hca : M.ca = true) {i : Fin n} {s s' : St n k} {a : Act n k}
    (hs : SoloInv i s) (ha : a.proc = i) (h : stepFn M s a = some s') : SoloInv i s' := by
  rcases a with j | ⟨j, t, v⟩ | ⟨j, d⟩ <;> simp only [Act.proc] at ha <;> subst ha <;>
    simp only [stepFn] at h <;>
    split at h <;> (try split at h) <;> (try split at h) <;> (try split at h) <;>
      (try split at h) <;> simp only [Option.some.injEq, reduceCtorEq] at h <;> subst h <;>
      simp_all [SoloInv, SoloPC, startPC]
  any_goals (split_ifs <;> trivial)
  all_goals
    rename_i _ m hm _ hac hk
    have ht : t = true := (hac.2.2.2.1 (fun q hq w hw => by
      rw [hs.2.2.2 _ _ q hq] at hw; cases hw)).1
    have htag : ∀ y : Fin k, y.val < m + 1 → Function.update (s.loc j).tag ⟨m, hm⟩ t y = true := by
      intro y hy
      rw [Function.update_apply]
      split
      · exact ht
      · exact hs.1 y (by rename_i hne; exact lt_of_le_of_ne (by omega) (fun h => hne (Fin.ext h)))
    first
      | (intro y hy; exact htag y (by omega))
      | (rw [afterN1_of_all _ (fun y => htag y (by omega))]; trivial)

/-- Runs compose. -/
theorem run_append {M : Mode} {s : St n k} (as bs : List (Act n k)) :
    run M s (as ++ bs) = (run M s as).bind (fun s' => run M s' bs) := by
  induction as generalizing s with
  | nil => simp [run]
  | cons a as ih =>
    simp only [List.cons_append, run, ih]
    cases stepFn M s a <;> simp

/-- `SoloInv i` is preserved by runs of process `i` alone. -/
theorem run_soloInv {M : Mode} (hca : M.ca = true) {i : Fin n} {s s' : St n k}
    {as : List (Act n k)} (hs : SoloInv i s) (has : ∀ a ∈ as, a.proc = i)
    (h : run M s as = some s') : SoloInv i s' := by
  induction as generalizing s with
  | nil => simp [run] at h; subst h; exact hs
  | cons a as ih =>
    simp only [run, Option.bind_eq_some_iff] at h
    obtain ⟨s₁, h₁, h₂⟩ := h
    exact ih (soloInv_step hca hs (has a (by simp)) h₁) (fun b hb => has b (by simp [hb])) h₂

end Podc.DistributedUniversality.ContentionCex


namespace Podc.DistributedUniversality

open ContentionCex

/-- **Contention-awareness of Figure 2, solo-from-the-start version (true).** In the
contention-aware construction (Figure 2), in any execution from the initial state in which only
one process `i` takes steps, no process ever invokes a `k`-SC (or `(k,ℓ)`-SC) object (line 2M),
nor an adopt-commit object `AC[2r][-]` (lines 3M–4M): since nobody else ever invokes
`AC[2r-1][m]`, the no-conflicting-values property forces `commit` at line N1, so the test of line N2
is always false. This is the part of the proof of Theorem 2 ("if a process executes alone, the
k-simultaneous consensus object is not used") that is correct. -/
theorem fig2_solo_from_init_no_sc {M : Mode} (hca : M.ca = true) (i : Fin n)
    {as : List (Act n k)} (hsolo : ∀ a ∈ as, a.proc = i) {s : St n k}
    (h : run M init as = some s) :
    (∀ r j, s.scI r j = none) ∧ ∀ r y j, s.acI r true y j = none := by
  have := run_soloInv hca (soloInv_init i) hsolo h
  exact ⟨this.2.1, this.2.2.1⟩

end Podc.DistributedUniversality

namespace Podc.DistributedUniversality.ContentionCex

open Podc.DistributedUniversality

/-- Figure 2 with `k`-SC objects (`ℓ = 1`), no helping, strong reading of adopt-commit. -/
def M : Mode := { ℓ := 1, ca := true, help := false, strongAC := true }

/-- The `s`-th operation of process `i` on the single object. -/
abbrev o (i : Fin 3) (s : ℕ) : Op 3 := (i, s)

/-- The decision of `SC[1]`: object `0`, operation `(1, 0)`. -/
def d1 : Fin 1 → Option (Op 3) := fun _ => some (o 1 0)

/-- `c` local steps of process `i`. -/
def g (i : Fin 3) (c : ℕ) : List (Act 3 1) := List.replicate c (.go i)

/-- First part: processes 1 and 2 run round 1 concurrently (both get `adopt` at line N1, go
through `SC[1]`, which decides `(1,0)`); process 1 completes its first operation in round 1,
process 2 in round 2; then both stop. -/
def pre : List (Act 3 1) :=
  [.go 1, .go 2, .go 1, .go 2, .ac 1 false (o 1 0), .ac 2 false (o 2 0), .go 1, .go 2,
   .sc 1 d1, .sc 2 d1, .go 1, .go 2, .ac 1 true (o 1 0), .ac 2 true (o 1 0)] ++
  g 1 6 ++ g 2 6 ++ [.go 2, .ac 2 true (o 2 0)] ++ g 2 6

/-- Second part: process 0 runs alone.  At line N1 of round 1 it meets the stale proposals
`(1,0)` and `(2,0)` of processes 1 and 2 in `AC[1][0]` and gets `adopt`, hence invokes `SC[1]`. -/
def solo : List (Act 3 1) :=
  [.go 0, .go 0, .ac 0 false (o 0 0), .go 0, .sc 0 d1, .go 0, .ac 0 true (o 1 0)] ++ g 0 6 ++
  [.go 0, .ac 0 true (o 2 0)] ++ g 0 6 ++ [.go 0, .ac 0 true (o 0 0)] ++ g 0 6

/-- The state when process 0 starts (time `t₀ = 34`). -/
def s0 : St 3 1 := (run M init pre).get (by decide)

/-- The final state (time `63`). -/
def sF : St 3 1 := (run M s0 solo).get (by decide)

/-- The first part of the execution leads to `s0`. -/
theorem run_pre : run M init pre = some s0 := by simp [s0]

/-- The second part of the execution leads from `s0` to `sF`. -/
theorem run_solo : run M s0 solo = some sF := by simp [sF]

/-- Process 0 starts at time `t₀ = 34`. -/
theorem s0_time : s0.time = 34 := by decide

/-- Property (3) of the counterexample, for rounds `< 5`. -/
theorem sF_bounded :
    (∀ r < 5, ∀ b y q, ∀ o ∈ sF.acI r b y q, o.1 ≠ 0 → ∃ t ∈ sF.retAt o.1 y o.2, t < s0.time) ∧
    (∀ r < 5, ∀ q, ∀ f ∈ sF.scI r q, ∀ y, (f y).1 ≠ 0 →
      ∃ t ∈ sF.retAt (f y).1 y (f y).2, t < s0.time) := by
  decide

/-- The whole execution. -/
theorem run_all : run M init (pre ++ solo) = some sF := by
  rw [run_append, run_pre, Option.bind_some, run_solo]

/-- At time `t₀`, process 0 has not started. -/
theorem s0_r0 : (s0.loc 0).r = 0 := by decide

/-- All processes are in rounds `< 5` at the end. -/
theorem sF_rounds : ∀ q : Fin 3, (sF.loc q).r < 5 := by decide

end Podc.DistributedUniversality.ContentionCex

namespace Podc.DistributedUniversality

open ContentionCex

/-- **Theorem 2 of [Raynal–Stainer–Taubenfeld, PODC 2014] is false as stated: Figure 2 is not
contention-aware.** (Section 4.1: "When a process invokes an operation on a contention-aware
universal construction, it must be able to complete its operation by accessing only read/write
registers in the absence of contention"; the execution of an operation starts when its issuer makes
it public and ends when it is returned.)

Execution of Figure 2 (`n = 3`, `k = 1`, `k`-SC objects, no helping, adopt-commit objects
satisfying even the strong reading of the no-conflict property): processes 1 and 2 run round 1
concurrently, both complete their first operation (`retAt`) and stop taking steps.  Then process 0
runs alone, from time `t₀` on.  Its first operation `(0,0)` is invoked at `t₀` and returned at some
`t₁`; every operation of another process that was ever proposed to a base object (adopt-commit or
SC) was returned before `t₀`, so no other operation is in progress during `[t₀, t₁]`. Yet process 0
receives `adopt` at line N1 (`AC[1][0]` still holds the stale proposals of round 1) and invokes the
`k`-SC object `SC[1]` (line 2M) during this contention-free operation.

(In the model, a process fetches its next operation with `next()` right after returning the
previous one; the next operations `(1,1)`, `(2,1)` of processes 1 and 2 are thus fetched before
`t₀`, but they are never proposed to any base object — processes 1 and 2 take no step after `t₀` —
so they are not in execution in the sense of the paper. The run is equally a run in which
processes 1 and 2 crash right after returning.) -/
theorem theorem_2_not_contention_aware :
    ∃ s₀ s : St 3 1, run M init pre = some s₀ ∧ run M s₀ solo = some s ∧
      run M init (pre ++ solo) = some s ∧
      -- (1) process 0's first operation on object 0 is invoked at `t₀` and returned at `t₁`
      s.invAt 0 0 0 = some s₀.time ∧ (∃ t₁, s.retAt 0 0 0 = some t₁ ∧ t₁ < s.time) ∧
      -- (2) all actions from time `t₀` on are by process 0 (time = index in the run)
      s₀.time = pre.length ∧ s.time = s₀.time + solo.length ∧ (∀ a ∈ solo, a.proc = 0) ∧
      -- (3) all operations of other processes ever proposed were returned before `t₀`
      (∀ r b y q, ∀ op ∈ s.acI r b y q, op.1 ≠ 0 →
        ∃ t ∈ s.retAt op.1 y op.2, t < s₀.time) ∧
      (∀ r q, ∀ f ∈ s.scI r q, ∀ y, (f y).1 ≠ 0 →
        ∃ t ∈ s.retAt (f y).1 y (f y).2, t < s₀.time) ∧
      -- (4) process 0 had not made anything public at `t₀` …
      (∀ r b y, s₀.acI r b y 0 = none) ∧ (∀ r, s₀.scI r 0 = none) ∧
      -- … it gets `adopt` at line N1 of round 1 and accesses the `k`-SC object `SC[1]`
      s.acR 1 false 0 0 = some (false, (0, 0)) ∧ s.scI 1 0 ≠ none := by
  have hinv := run_roundInv (M := M) roundInv_init run_all
  have hinv0 := run_roundInv (M := M) roundInv_init run_pre
  refine ⟨s0, sF, run_pre, run_solo, run_all, by decide, ⟨62, by decide, by decide⟩, by decide,
    by rw [run_time run_solo], by decide, ?_, ?_, ?_, ?_, by decide, by decide⟩
  · intro r b y q op hop h0
    by_cases hr : r < 5
    · exact sF_bounded.1 r hr b y q op hop h0
    · have hr' : (sF.loc q).r < r := lt_of_lt_of_le (sF_rounds q) (by omega)
      rw [((hinv q).2 r hr').1 b y] at hop; cases hop
  · intro r q f hf y h0
    by_cases hr : r < 5
    · exact sF_bounded.2 r hr q f hf y h0
    · have hr' : (sF.loc q).r < r := lt_of_lt_of_le (sF_rounds q) (by omega)
      rw [((hinv q).2 r hr').2] at hf; cases hf
  · intro r b y
    rcases Nat.eq_zero_or_pos r with rfl | hr
    · revert b y; decide
    · exact ((hinv0 0).2 r (by rw [s0_r0]; exact hr)).1 b y
  · intro r
    rcases Nat.eq_zero_or_pos r with rfl | hr
    · decide
    · exact ((hinv0 0).2 r (by rw [s0_r0]; exact hr)).2

end Podc.DistributedUniversality

namespace Podc.DistributedUniversality.ContentionCex

open Podc.DistributedUniversality

/-- Figure 2 with `k`-SC objects, no helping, weak (standard) reading of adopt-commit. -/
def Mw : Mode := { ℓ := 1, ca := true, help := false, strongAC := false }

/-- A fully sequential execution (`n = 2`, `k = 1`): process 1 runs its first operation alone
(commit at line N1, return at line 31) and stops; then process 0 runs alone. -/
def seqRun : List (Act 2 1) :=
  [.go 1, .go 1, .ac 1 true (1, 0)] ++ List.replicate 5 (.go 1) ++
  [.go 0, .go 0, .ac 0 false (1, 0), .go 0, .sc 0 (fun _ => some (1, 0))]

end Podc.DistributedUniversality.ContentionCex

namespace Podc.DistributedUniversality

open ContentionCex

/-- **Theorem 2 fails even in a sequential execution (weak reading of adopt-commit).** With the
no-conflict property in its weak reading (the one satisfied by the standard register
implementation, `ACImpl.adopt_after_solo_commit`), process 1 completes its first operation alone
(invoked at time `0`, returned at time `7`); afterwards process 0 invokes its first operation (time
`8`) and runs alone, gets `(adopt, (1,0))` at line N1 of round 1 and invokes `kSC[1]`. No two
operations that were ever proposed overlap in time. Under the strong reading this run is not
allowed (process 0 must commit), which is why `theorem_2_not_contention_aware` uses a concurrent
prefix. -/
theorem theorem_2_not_contention_aware_sequential :
    ∃ s : St 2 1, run Mw init seqRun = some s ∧
      s.invAt 1 0 0 = some 0 ∧ s.retAt 1 0 0 = some 7 ∧ s.invAt 0 0 0 = some 8 ∧
      (∀ a ∈ seqRun.drop 8, a.proc = 0) ∧
      s.acR 1 false 0 0 = some (false, (1, 0)) ∧ s.scI 1 0 ≠ none ∧
      run { Mw with strongAC := true } init seqRun = none :=
  ⟨_, rfl, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

end Podc.DistributedUniversality
