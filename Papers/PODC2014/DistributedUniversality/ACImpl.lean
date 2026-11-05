import Papers.PODC2014.DistributedUniversality.Model

/-!
# The standard register-based adopt-commit object returns `adopt` on stale proposals

Evidence that the `adopt` responses used in `theorem_2_not_contention_aware` are what a standard
read/write implementation of adopt-commit (Gafni's two-phase algorithm, as cited by the paper)
actually returns.

Each process `i` with input `v` executes, one shared-memory access per step:
1. `AA[i] := v`; read `AA[0], …, AA[n-1]`;
2. `BB[i] := (commit, v)` if it saw no value `≠ v` in `AA`, else `(adopt, v)`;
   read `BB[0], …, BB[n-1]`;
3. return `(commit, w)` if all the `BB` entries it read are `(commit, w)`; otherwise `(adopt, w)`
   if it read some `(commit, w)`; otherwise `(adopt, v)`.

On the invocation schedule of `AC[1][0]` (line N1, round 1, object 0) in the counterexample
(processes 1 and 2 concurrently, then process 0 alone, long after), all three processes return
`(adopt, own value)`.
-/

namespace Podc.DistributedUniversality.ACImpl

/-- Local state of a process of the adopt-commit implementation. -/
structure L (n : ℕ) (V : Type) where
  /-- program counter: `0` write `AA`, `1..n` read `AA`, `n+1` write `BB`, `n+2..2n+1` read
  `BB`, `2n+2` return, `2n+3` done -/
  pc : ℕ
  /-- input value -/
  v : V
  /-- saw a value different from `v` in `AA` -/
  other : Bool
  /-- the `BB` entries read so far -/
  seen : List (Bool × V)
  /-- the response `(commit?, value)` -/
  res : Option (Bool × V)

/-- Global state: the registers `AA`, `BB` and the local states. -/
structure S (n : ℕ) (V : Type) where
  AA : Fin n → Option V
  BB : Fin n → Option (Bool × V)
  loc : Fin n → L n V

variable {n : ℕ} {V : Type} [DecidableEq V]

/-- The response computed from the `BB` entries read (phase 3). -/
def decideRes (v : V) (seen : List (Bool × V)) : Bool × V :=
  match seen.find? (fun e => e.1) with
  | some (_, w) => if seen.all (fun e => e.1 && decide (e.2 = w)) then (true, w) else (false, w)
  | none => (false, v)

/-- One step of process `i` (`none` if it has returned). -/
def step (s : S n V) (i : Fin n) : Option (S n V) :=
  let l := s.loc i
  let upd (l' : L n V) : Fin n → L n V := Function.update s.loc i l'
  if h0 : l.pc = 0 then
    some { s with AA := Function.update s.AA i (some l.v), loc := upd { l with pc := 1 } }
  else if h : l.pc ≤ n then
    let q : Fin n := ⟨l.pc - 1, by omega⟩
    let o := match s.AA q with
      | some w => decide (w ≠ l.v)
      | none => false
    some { s with loc := upd { l with pc := l.pc + 1, other := l.other || o } }
  else if h1 : l.pc = n + 1 then
    some { s with BB := Function.update s.BB i (some (!l.other, l.v)),
                  loc := upd { l with pc := l.pc + 1 } }
  else if h : l.pc ≤ 2 * n + 1 then
    let q : Fin n := ⟨l.pc - n - 2, by omega⟩
    some { s with loc := upd { l with pc := l.pc + 1, seen := l.seen ++ (s.BB q).toList } }
  else if l.pc = 2 * n + 2 then
    some { s with loc := upd { l with pc := l.pc + 1, res := some (decideRes l.v l.seen) } }
  else none

/-- Run a schedule (list of process identities). -/
def runS (s : S n V) : List (Fin n) → Option (S n V)
  | [] => some s
  | i :: is => (step s i).bind (fun s' => runS s' is)

/-- Initial state with inputs `inp`. -/
def initS (inp : Fin n → V) : S n V where
  AA := fun _ => none
  BB := fun _ => none
  loc := fun i => { pc := 0, v := inp i, other := false, seen := [], res := none }

/-- The inputs to `AC[1][0]` in the counterexample: process `i` proposes its operation `(i, 0)`. -/
def inp : Fin 3 → Op 3 := fun i => (i, 0)

/-- The schedule of `AC[1][0]` in the counterexample: processes 1 and 2 write `AA` concurrently and
complete; much later process 0 runs alone (9 steps each). -/
def sched : List (Fin 3) :=
  [1, 2] ++ List.replicate 8 1 ++ List.replicate 8 2 ++ List.replicate 9 0

/-- **The standard adopt-commit implementation returns `(adopt, own value)` to all three processes**
on the schedule of `AC[1][0]` in `theorem_2_not_contention_aware`; in particular process 0, which
runs alone, gets `adopt` because of the stale entries of processes 1 and 2. -/
theorem adopt_on_stale :
    ∃ s, runS (initS inp) sched = some s ∧
      ∀ i : Fin 3, (s.loc i).res = some (false, (i, 0)) := by
  exact ⟨_, rfl, by decide⟩

/-- Sanity check: a process running alone from the initial state commits its own value. -/
theorem solo_commits :
    ∃ s, runS (initS inp) (List.replicate 9 0) = some s ∧ (s.loc 0).res = some (true, (0, 0)) :=
  ⟨_, rfl, by decide⟩

/-- **A sequential schedule**: process `1` runs `propose` alone and commits; afterwards process `0`
runs alone and, seeing the stale conflicting entry of process `1`, gets `(adopt, (1,0))`.  This is
the schedule of `AC[1][0]` in `theorem_2_not_contention_aware_sequential`.  (It also shows that the
standard implementation does not satisfy the *strong* reading of the no-conflict property.) -/
theorem adopt_after_solo_commit :
    ∃ s, runS (initS (n := 2) (fun i => ((i : Fin 2), 0)))
        (List.replicate 7 1 ++ List.replicate 7 0) = some s ∧
      (s.loc 1).res = some (true, (1, 0)) ∧ (s.loc 0).res = some (false, (1, 0)) :=
  ⟨_, rfl, by decide⟩

end Podc.DistributedUniversality.ACImpl
