import Papers.PODC2019.RDMAAgreement.PMP.Exec

/-!
# Minimality of `p1`'s first ballot is needed (even with the repaired line 21)

The model `Step` fixes the ballot of `p1`'s first attempt (which skips phase 1) to `1`, smaller
than every other ballot. The paper only says "propNr = a higher value than any proposal number
seen before"; `p1` has seen nothing before its first attempt, so it could pick any value.
`StepAnyFirst` adds this freedom (`startFirstAny`: any fresh ballot `b`); with it agreement fails
even for the repaired algorithm.

Run with `n = 2` (`p1 = 0` input `false`, `q = 1` input `true`) and `m = 3` memories:
1. `q` (ballot 5) acquires memories 1, 2, phase 1 reads nothing, writes `(5,5,true)` on 1, 2 and
   **decides `true`**.
2. `p1`'s first attempt with ballot 100 (no phase 1, no `getPermission`): its line-35 write on
   memory 0 succeeds (it still holds the initial permission), on memory 1 it fails: abort.
3. `q` starts ballot 200 on memories 0, 1: memory 0 shows `p1`'s `(100,100,false)` and `q`'s
   `(200,5,true)`, memory 1 shows `(200,5,true)`; no `minProp > 200`, the highest `accProp` is 100:
   `q` adopts `false`, writes `(200,200,false)` on 0, 1 and **decides `false`**.
-/

namespace Podc.RDMAAgreement.PMP

open Function

variable {P M V : Type*} [DecidableEq P] [DecidableEq M] [Fintype M]

/-- `Step`, plus: `p1`'s first attempt may use any fresh ballot. -/
inductive StepAnyFirst (p1 : P) (inp : P → V) (var : Variant) :
    State P M V → State P M V → Prop
  | step {s s' : State P M V} (h : Step p1 inp var s s') : StepAnyFirst p1 inp var s s'
  | startFirstAny (s : State P M V) (q : P) (b : ℕ) (hq : q = p1) (hs : (s.pr q).started = false)
      (hact : (s.pr q).active = false) (hb : b ∉ s.used) (hlt : (s.pr q).bal < b) :
      StepAnyFirst p1 inp var s
        { s with
          pr := update s.pr q
            { s.pr q with
              active := true, started := true, noPh1 := true, bal := b,
              curVal := inp q, curMax := 0, p2s := false, ready := ∅, done := ∅,
              pc := fun _ => .ph2 }
          used := insert b s.used
          p2val := update s.p2val b (some (inp q)) }

/-- Reachable states when `p1`'s first ballot is arbitrary. -/
def ReachableAnyFirst (p1 : P) (inp : P → V) (var : Variant) (s : State P M V) : Prop :=
  Relation.ReflTransGen (StepAnyFirst p1 inp var) (initState p1 inp) s

section Exec2

variable [Fintype P]

/-- Extra actions: arbitrary first ballot; read delivery adopting/keeping the value of slot `r`. -/
inductive Act2 (P M : Type*)
  | base (a : Act P M)
  | startFirstAny (q : P) (b : ℕ)
  | dlvRd (q : P) (m : M) (r : P)

/-- `o`'s ballot is at most `a`. -/
def accLeB (o : Option (ℕ × V)) (a : ℕ) : Bool :=
  match o with
  | none => true
  | some (a', _) => decide (a' ≤ a)

theorem accLeB_spec {o : Option (ℕ × V)} {a : ℕ} (h : accLeB o a = true) {a' : ℕ} {y' : V}
    (h' : o = some (a', y')) : a' ≤ a := by
  subst h'; simpa [accLeB] using h

def exec2 (p1 : P) (inp : P → V) (var : Variant) :
    Act2 P M → State P M V → Option (State P M V)
  | .base a, s => exec p1 inp var a s
  | .startFirstAny q b, s =>
    if q = p1 ∧ (s.pr q).started = false ∧ (s.pr q).active = false ∧ b ∉ s.used ∧
        (s.pr q).bal < b then
      some { s with
          pr := update s.pr q
            { s.pr q with
              active := true, started := true, noPh1 := true, bal := b,
              curVal := inp q, curMax := 0, p2s := false, ready := ∅, done := ∅,
              pc := fun _ => .ph2 }
          used := insert b s.used
          p2val := update s.p2val b (some (inp q)) }
    else none
  | .dlvRd q m r, s =>
    match (s.pr q).pc m, (s.pr q).link m with
    | .wRd, .resp (.snap f) =>
      match (f r).acc with
      | some (a, y) =>
        if (∀ r', (f r').mp ≤ (s.pr q).bal) ∧ (∀ r', accLeB (f r').acc a = true) then
          if a ≤ (s.pr q).curMax then
            some { s with
              pr := update s.pr q
                { (s.pr q).setT m .barrier .idle with ready := insert m (s.pr q).ready } }
          else if (s.pr q).p2s = false then
            some { s with
              pr := update s.pr q
                { (s.pr q).setT m .barrier .idle with
                  ready := insert m (s.pr q).ready, curVal := y, curMax := a } }
          else none
        else none
      | none => none
    | _, _ => none

def run2 (p1 : P) (inp : P → V) (var : Variant) :
    List (Act2 P M) → State P M V → Option (State P M V)
  | [], s => some s
  | a :: as, s => (exec2 p1 inp var a s).bind (run2 p1 inp var as)

theorem exec2_sound (p1 : P) (inp : P → V) (var : Variant) (a : Act2 P M) (s s' : State P M V)
    (h : exec2 p1 inp var a s = some s') : StepAnyFirst p1 inp var s s' := by
  cases a with
  | base a => exact .step (exec_sound p1 inp var a s s' h)
  | startFirstAny q b =>
    simp only [exec2] at h
    split_ifs at h with hc
    obtain ⟨h1, h2, h3, h4, h5⟩ := hc
    cases h; exact .startFirstAny s q b h1 h2 h3 h4 h5
  | dlvRd q m r =>
    simp only [exec2] at h
    split at h <;> try simp only [reduceCtorEq] at h
    rename_i f hpc hl
    split at h <;> try simp only [reduceCtorEq] at h
    rename_i a y hr
    split_ifs at h with h1 h2 h3 <;> try simp only [reduceCtorEq] at h
    all_goals obtain ⟨hmp, hmax⟩ := h1
    all_goals have hmax' : ∀ r' a' y', (f r').acc = some (a', y') → a' ≤ a :=
      fun r' _ _ h' => accLeB_spec (hmax r') h'
    · cases h; exact .step (Step.dlvRdKeep s q m f r a y hpc hl hmp hr hmax' h2)
    · cases h; exact .step (Step.dlvRdAdopt s q m f r a y hpc hl hmp hr hmax' (by omega) h3)

theorem run2_sound (p1 : P) (inp : P → V) (var : Variant) :
    ∀ (as : List (Act2 P M)) (s s' : State P M V), run2 p1 inp var as s = some s' →
      Relation.ReflTransGen (StepAnyFirst p1 inp var) s s'
  | [], s, s', h => by cases h; exact .refl
  | a :: as, s, s', h => by
    simp only [run2, Option.bind_eq_some_iff] at h
    obtain ⟨t, ht, h⟩ := h
    exact .head (exec2_sound p1 inp var a s t ht) (run2_sound p1 inp var as t s' h)

end Exec2

namespace FirstBallot

/-- Inputs: `p1 = 0` proposes `false`, `q = 1` proposes `true`. -/
def inp (p : Fin 2) : Bool := decide (p = 1)

open Act in
/-- Phase 1 of thread `m` of `q` up to the barrier (no value read). -/
def ph1None (q : Fin 2) (m : Fin 3) : List (Act2 (Fin 2) (Fin 3)) :=
  [.base (invPerm q m), .base (eff q m), .base (dlv q m), .base (eff q m), .base (dlv q m),
   .base (eff q m), .base (dlv q m)]

open Act in
/-- Phase 1 of thread `m` of `q` up to the read response. -/
def ph1Read (q : Fin 2) (m : Fin 3) : List (Act2 (Fin 2) (Fin 3)) :=
  [.base (invPerm q m), .base (eff q m), .base (dlv q m), .base (eff q m), .base (dlv q m),
   .base (eff q m)]

open Act in
def schedule : List (Act2 (Fin 2) (Fin 3)) :=
  -- 1. q decides `true` with ballot 5 on memories 1, 2
  [.base (startNext 1 5)] ++ ph1None 1 1 ++ ph1None 1 2 ++
  [.base (pass 1 1), .base (pass 1 2), .base (eff 1 1), .base (dlv 1 1), .base (eff 1 2),
   .base (dlv 1 2)] ++
  -- 2. p1's first attempt with ballot 100: succeeds on memory 0, fails on memory 1
  [.startFirstAny 0 100, .base (issue 0 0), .base (eff 0 0), .base (dlv 0 0),
   .base (issue 0 1), .base (eff 0 1), .base (dlv 0 1)] ++
  -- 3. q, ballot 200, adopts `false` from memory 0 and decides it
  [.base (startNext 1 200)] ++ ph1Read 1 0 ++ [.dlvRd 1 0 0] ++ ph1Read 1 1 ++ [.dlvRd 1 1 1] ++
  [.base (pass 1 0), .base (pass 1 1), .base (eff 1 0), .base (dlv 1 0), .base (eff 1 1),
   .base (dlv 1 1)]

theorem finalDecs :
    (run2 (0 : Fin 2) inp .repaired schedule (initState 0 inp)).map State.decs =
      some [false, true] := by
  decide +kernel

end FirstBallot

open FirstBallot in
/-- If `p1`'s first attempt (which skips phase 1) may use an arbitrary fresh ballot instead of
the smallest one, agreement fails **even for the repaired algorithm**: `q` decides `true`, later
`q` decides `false` (n = 2, m = 3). -/
theorem first_ballot_not_minimal_false :
    ∃ s : State (Fin 2) (Fin 3) Bool, ReachableAnyFirst (0 : Fin 2) FirstBallot.inp .repaired s ∧
      true ∈ s.decs ∧ false ∈ s.decs := by
  have h := FirstBallot.finalDecs
  simp only [Option.map_eq_some_iff] at h
  obtain ⟨s, hs, hd⟩ := h
  exact ⟨s, run2_sound _ _ _ _ _ _ hs, by simp [hd], by simp [hd]⟩

end Podc.RDMAAgreement.PMP
