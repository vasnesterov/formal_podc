import Papers.PODC2023.BoundedTimestamping.Machine

/-!
# The MTS algorithm is not linearizable

**Main result (refutes Corollary 10 / Lemma 8, hence Theorem 1 for this algorithm).** For
`n = 3` processes and `κ = 4` (the smallest `κ` with "a complete `helpMoveTS()` call requires at
most `n · κ` steps": a call takes up to `2n + 4 = 10` steps), the algorithm of Figures 1–2 has a
*sequential* execution (every operation runs solo, from invocation to response) whose responses
violate the MTS specification.

The script (`script3`):
1. process `0` performs 371 `updateTS()` (`Counter` reaches `δ = 371`, cluster 1 becomes
   active; `TS[0] = (0, 370)`);
2. process `1` performs 62 `updateTS()`; after the 60th the cluster-1 invalidation phase is over,
   the last two run in the move phase, and the `helpMoveTS` of process `1` moves `TS[2]`
   (the `≪`-dominant old entry, index `⊥`) to cluster 1;
3. process `2` calls `isEarlier(0, 1)`; its `κ = 4` `helpMoveTS` steps are `TS[2].LL()`,
   `Counter.read()` (move phase), `TS[0].LL()` (cluster 0, index 370), `TS[1].LL()`: the
   coroutine stops between line 61 and line 62 of a `helpMoveTS()` call;
4. process `0` performs two `updateTS()`: `TS[0] = (1, 63)`, and its flag is back to the value
   process `2` saw;
5. process `2` calls `isEarlier(0, 2)`: line 35 performs `TS[0].LL()`, which *renews process
   `2`'s link* on `TS[0]`; the `helpMoveTS` steps in line 39 then execute lines 62, 65
   (`TS[0].VL()` succeeds — it validates the new link, not the one of line 61), 66 and the `SC`
   of line 73, which writes `(1, -1)` into `TS[0]` from the stale local copy: process `0`'s
   latest timestamp is now dominated by process `1`'s;
6. process `2` calls `isEarlier(1, 0)` and gets `false`, although the latest `updateTS()` of
   `1` precedes both latest `updateTS()` calls of `0` (the specification answers `true`).

The cause: `helpMoveTS()` is executed `κ` steps at a time across several operations of the same
process, and these operations perform their own `LL()`s on the same `TS` entries; with one link
per process and object (the paper's LL/SC definition, Section 3), the `VL()`s of line 65 no
longer certify that the local copies of line 61 are current. Giving `helpMoveTS` its own link
(e.g. `2n` LL/SC "identities") removes this execution.

The execution has 438 operations and 6392 base-object steps; it is evaluated by the kernel
(`script3_result`), and `valid_of_runScript` turns the evaluation into a valid execution of
`alg 3 4`.
-/

set_option linter.unusedSectionVars false

namespace Cslib.SharedMemory.BoundedTS

open Cslib.SharedMemory

/-- The schedule of the counterexample (each operation runs solo to completion). -/
def script3 : List (Fin 3 × MOp 3) :=
  List.replicate 371 (0, .upd 0) ++ List.replicate 62 (1, .upd 1) ++
  [(2, .ie 0 1), (0, .upd 0), (0, .upd 0), (2, .ie 0 2), (2, .ie 1 0)]

/-- Kernel evaluation of the script: it completes, and its responses are illegal for the MTS
specification. -/
theorem script3_result : (runScript 3 4 1000 (initMS 3) script3).map
    (fun x => legalFromB (A := mtsObj 3) [] (x.2.map fun s => (s.2.1, s.2.2.1))) = some false := by
  decide +kernel

/-- The last response of the script: `isEarlier(1, 0)` returns `false`. -/
theorem script3_last : (runScript 3 4 1000 (initMS 3) script3).map
    (fun x => (x.2.getLast?.map fun s => (s.1, s.2.1, s.2.2.1))) =
      some (some (2, .ie 1 0, some false)) := by
  decide +kernel

/-- **The algorithm of Figures 1–2 is not linearizable** (for `n = 3`, `κ = 4`): this refutes
Lemma 8 and Corollary 10 of [BJW23], and with them Theorem 1 as proved by this algorithm. -/
theorem alg_not_linearizable : ¬ (alg 3 4).Linearizable := by
  have h := script3_result
  cases hr : runScript 3 4 1000 (initMS 3) script3 with
  | none => simp [hr] at h
  | some x =>
    obtain ⟨s, H⟩ := x
    simp only [hr, Option.map_some, Option.some.injEq] at h
    refine Impl.not_linearizable_of_seqExec _ (valid_of_runScript 3 4 hr) ?_
    rw [← legalFromB_eq_true_iff, h]
    simp

/-! ## Lemma 6 is false

Lemma 6 claims that an `SC()` executed in line 73 does not affect the dominance order of any
entries of the `TS` array. In the run above, process `2`'s `SC()` of line 73 (during its
`isEarlier(0, 2)`) changes `TS[0]` from `(1, 63)` to `(1, -1)`, while `TS[1] = (1, 61)`:
before the step `TS[1] ≪ TS[0]`, after it `TS[0] ≪ TS[1]`. -/

/-- Labels: the script up to process `0`'s second update, then `isEarlier(0, 2)` of process `2`
up to its `SC()` of line 73. -/
def lemma6Exec : Option (List (Label (Fin 3) (mtsObj 3)) × MState 3) := do
  let (s, H) ← runScript 3 4 1000 (initMS 3) (script3.take 436)
  let s ← cstep 3 4 s (Label.inv (2 : Fin 3) (MOp.ie 0 2 : (mtsObj 3).Op))
  let (s, k) ← tausUntilMove s 1000
  return (seqExec H ++ [Label.inv (2 : Fin 3) (MOp.ie 0 2 : (mtsObj 3).Op)] ++ List.replicate k (.tau 2), s)
where
  /-- Internal steps of process `2` until it is about to execute line 73. -/
  tausUntilMove : MState 3 → ℕ → Option (MState 3 × ℕ)
    | _, 0 => none
    | s, f + 1 =>
      let l := s.loc.getD 2 (locInit 3)
      if (match l.pc with | .K _ => true | _ => false) && l.mv.pc == MPC.m73 then some (s, 0) else
      match cstep 3 4 s (.tau 2) with
      | some s' => (tausUntilMove s' f).map (fun x => (x.1, x.2 + 1))
      | none => none

/-- The labels of `lemma6Exec`. -/
def lemma6Labels : List (Label (Fin 3) (mtsObj 3)) := (lemma6Exec.map Prod.fst).getD []

/-- The facts about the step of line 73, as a `Bool`. -/
def check6 : Option (MState 3) → Bool
  | none => false
  | some s =>
    let l := s.loc.getD 2 (locInit 3)
    (match l.pc with | .K _ => true | _ => false) && l.mv.pc == MPC.m73 &&
    less (s.getMem (.TS 1)).1 (s.getMem (.TS 0)).1 1 0 &&
    match cstep 3 4 s (.tau 2) with
    | none => false
    | some s' => less (s'.getMem (.TS 0)).1 (s'.getMem (.TS 1)).1 0 1

theorem lemma6Check_eq : check6 (crun 3 4 (initMS 3) lemma6Labels) = true := by decide +kernel

/-- **Lemma 6 of [BJW23] is false.** In a valid execution of `alg 3 4`, process `2` is about to
execute the `SC()` of line 73 (inside a `helpActiveCluster()` call, `PC.K _`) while
`TS[1] ≪ TS[0]`; the step succeeds and afterwards `TS[0] ≪ TS[1]`. (With Lemma 6, also
Lemma 9 fails in this execution: the dominance order of `TS[0]`, `TS[1]` no longer matches the
order of the latest `updateTS()` calls of `0` and `1`.) -/
theorem lemma6_false : ∃ α C C', (alg 3 4).run α = some C ∧ (alg 3 4).step C (.tau 2) = some C' ∧
    (∃ k, (C.loc 2).pc = .K k) ∧ (C.loc 2).mv.pc = .m73 ∧
    less (C.mem (.TS 1)).1 (C.mem (.TS 0)).1 1 0 = true ∧
    less (C'.mem (.TS 0)).1 (C'.mem (.TS 1)).1 0 1 = true := by
  have h := lemma6Check_eq
  generalize hr : crun 3 4 (initMS 3) lemma6Labels = o at h
  cases o with
  | none => simp [check6] at h
  | some s =>
    simp only [check6] at h
    have hw : s.WF := crun_wf 3 4 (initMS_wf 3) hr
    cases hs : cstep 3 4 s (.tau 2) with
    | none => simp [hs] at h
    | some s' =>
      simp only [hs, Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨⟨⟨hK, hm⟩, h1⟩, h2⟩ := h
      refine ⟨lemma6Labels, toCfg 3 s, toCfg 3 s', ?_, ?_, ?_, hm, h1, h2⟩
      · rw [Impl.run, ← toCfg_initMS 3 4, runFrom_toCfg 3 4 (initMS_wf 3), hr]; rfl
      · rw [step_toCfg 3 4 hw, hs]; rfl
      · obtain ⟨k, hk⟩ : ∃ k, (s.loc.getD 2 (locInit 3)).pc = PC.K k := by
          revert hK
          generalize (s.loc.getD 2 (locInit 3)).pc = pc
          cases pc <;> simp
        exact ⟨k, hk⟩

end Cslib.SharedMemory.BoundedTS

namespace Cslib.SharedMemory.BoundedTS

/-! ## `isEarlier(x, x)` -/

/-- A concurrent execution with an `isEarlier(1, 1)` returning `true`: process `1` updates;
process `2` invokes `isEarlier(1, 1)` and runs until it has executed line 44 (`TS[1].LL()`);
process `1` performs another complete `updateTS()`; process `2` executes line 45 (`TS[1].LL()`,
the new value) and line 46 (`TS[1].VL()`, which validates the link of line 45) and returns
`xTS ≪ yTS = true` for two different values of the *same* entry. -/
def selfExec : List (Label (Fin 3) (mtsObj 3)) :=
  seqExec [((1 : Fin 3), MOp.upd 1, (none : Option Bool), 20)] ++ [Label.inv (2 : Fin 3) (MOp.ie 1 1 : (mtsObj 3).Op)] ++
    List.replicate 15 (.tau 2) ++ seqExec [((1 : Fin 3), MOp.upd 1, (none : Option Bool), 16)] ++
    List.replicate 3 (.tau 2) ++ [Label.ret (2 : Fin 3) (some true : (mtsObj 3).Resp)]

theorem selfExec_run : (crun 3 4 (initMS 3) selfExec).isSome = true := by decide +kernel

/-- `isEarlier(x, x)` can return `true` (the specification always answers `false`), so the
algorithm is not linearizable even if one disregards the `helpMoveTS` problem: the
"snapshot" of lines 44–46 is not a snapshot when `x = y` (Observation 56 implicitly assumes
`x ≠ y`). -/
theorem alg_not_linearizable_self : ¬ (alg 3 4).Linearizable := by
  obtain ⟨s, hs⟩ := Option.isSome_iff_exists.1 selfExec_run
  refine Impl.not_linearizable_of_resp _ (valid_of_crun 3 4 hs) (x := (2, 0)) (o := .ie 1 1)
    (r := some true) (by decide +kernel) (by decide +kernel) ?_
  intro q; simp

end Cslib.SharedMemory.BoundedTS
